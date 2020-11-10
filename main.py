from __future__ import division

import sys
import math
import random
import time

from collections import deque
from pyglet import image
from pyglet.gl import *
from pyglet.graphics import TextureGroup
from pyglet.window import key, mouse

TICKS_PER_SEC = 60  # 每秒60游戏刻

# 用于简化块加载的扇区大小
SECTOR_SIZE = 16

WALKING_SPEED = 5
FLYING_SPEED = 15

GRAVITY = 20.0
MAX_JUMP_HEIGHT = 1.0   # 方块的高度
#    推导起跳速度的计算公式
#    v_t = v_0 - a * t,v_t = 0
#    得到t = v_0 / a 到达最高点的时间
#    使用t 和 AX_JUMP_HEIGHT 计算v_0 (jump speed)
#    MAX_JUMP_HEIGHT =  v_0 * t - (a * t^2) / 2 => v_0 = sqrt(2 * a * MAX_JUMP_HEIGHT)
JUMP_SPEED = math.sqrt(2 * GRAVITY * MAX_JUMP_HEIGHT)
TERMINAL_VELOCITY = 50

PLAYER_HEIGHT = 2  # 玩家身高

# 只有在python2中才有xrange和range，python3中没有xrange,在py2中，range得到的是一个列表
xrange = range

def cube_vertices(x, y, z, n):
    """
        返回立方体在x，y，z位置的顶点坐标，边长为2*n
        (x,y,z)表示立方体中心坐标，n为偏移量
    """
    return [
        x-n,y+n,z-n, x-n,y+n,z+n, x+n,y+n,z+n, x+n,y+n,z-n,  # top
        x-n,y-n,z-n, x+n,y-n,z-n, x+n,y-n,z+n, x-n,y-n,z+n,  # bottom
        x-n,y-n,z-n, x-n,y-n,z+n, x-n,y+n,z+n, x-n,y+n,z-n,  # left
        x+n,y-n,z+n, x+n,y-n,z-n, x+n,y+n,z-n, x+n,y+n,z+n,  # right
        x-n,y-n,z+n, x+n,y-n,z+n, x+n,y+n,z+n, x-n,y+n,z+n,  # front
        x+n,y-n,z-n, x-n,y-n,z-n, x-n,y+n,z-n, x+n,y+n,z-n,  # back
    ]


def tex_coord(x, y, n=4):
    """
        返回纹理正方形的边界顶点
    """
    m = 1.0 / n
    dx = x * m
    dy = y * m
    return dx, dy, dx + m, dy, dx + m, dy + m, dx, dy + m


def tex_coords(top, bottom, side):
    """
        返回顶部、底部和侧面的纹理方块列表
    """
    top = tex_coord(*top)
    bottom = tex_coord(*bottom)
    side = tex_coord(*side)
    result = []
    result.extend(top)
    result.extend(bottom)
    result.extend(side * 4)
    return result


TEXTURE_PATH = 'texture.png'
# 计算草块,沙块,砖块,石块,TNT,红石块,合金欢树6个面的纹理贴图坐标(用一个list保存)
GRASS = tex_coords((1, 0), (0, 1), (0, 0))
TNT = tex_coords((1, 2), (2, 2), (0, 2))
SAND = tex_coords((1, 1), (1, 1), (1, 1))
BRICK = tex_coords((2, 0), (2, 0), (2, 0))
STONE = tex_coords((2, 1), (2, 1), (2, 1))
RED_STONE = tex_coords((3, 0), (3, 0), (3, 0))
ACACIA_LEAVE = tex_coords((3, 2), (3, 2), (3, 2))
ACACIA_LOG = tex_coords((2, 3), (2, 3), (3, 3))
ACACIA_PLANKS = tex_coords((3, 1), (3, 1), (3, 1))

# 当前位置向6个方向移动1个单位要用到的增量坐标
FACES = [
    ( 0, 1, 0),
    ( 0,-1, 0),
    (-1, 0, 0),
    ( 1, 0, 0),
    ( 0, 0, 1),
    ( 0, 0,-1),
]


def normalize(position):
    """ 接受任意精度的“position”，并返回包含该位置的块

    Parameters
    ----------
    position : tuple of len 3

    Returns
    -------
    block_position : tuple of ints of len 3

    """
    x, y, z = position
    x, y, z = (int(round(x)), int(round(y)), int(round(z))) #四舍五入
    return (x, y, z)


def sectorize(position):
    """
        返回表示给定位置扇区的元组
    Parameters
    ----------
    position : tuple of len 3

    Returns
    -------
    sector : tuple of len 3

    """
    x, y, z = normalize(position)
    x, y, z = x // SECTOR_SIZE, y // SECTOR_SIZE, z // SECTOR_SIZE
    return (x, 0, z)


class Model(object):

    def __init__(self):

        # 批量一起渲染
        self.batch = pyglet.graphics.Batch()

        # 载入纹理贴图
        self.group = TextureGroup(image.load(TEXTURE_PATH).get_texture())

        # 定义当前世界上的所有块
        # 字典：键为坐标，键值为纹理，所有已经存在的方块均有
        self.world = {}

        # 字典：键为坐标，键值为纹理，所有存在并且已经显示的方块均有
        self.shown = {}

        # 字典：键为坐标，键值为a pyglet `VertexList`，VertexList被批量渲染
        # VertexList创建一个顶点列表(其中每个帧位置数据预期都将变化，但是颜色数据预计将保持相对恒定)
        self._shown = {}

        # 字典：键为扇区坐标，键值为扇区方块位置列表
        self.sectors = {}

        # 用于存储事件的队列
        # _show_block() 和 _hide_block() 调用
        self.queue = deque()
        # 画出游戏地图
        self._initialize()

    def _initialize(self):
        """ 初始化世界，放置所有方块

        """
        n = 80  # 地图大小
        s = 1  # 步长
        y = 0  # 初始化y值，注意y为垂直于地面高度
        for x in xrange(-n, n + 1, s):
            for z in xrange(-n, n + 1, s):
                # 地基和草坪
                self.add_block((x, y - 2, z), GRASS, immediate=False)
                self.add_block((x, y - 3, z), STONE, immediate=False)
                if x in (-n, n) or z in (-n, n):
                    # 世界边界围墙
                    for dy in xrange(-2, 3):
                        self.add_block((x, y + dy, z), STONE, immediate=False)

        # 随机生成山丘
        o = n - 10  # 避免建筑撞墙
        for _ in xrange(120):
            a = random.randint(-o, o)  # 山丘x位置
            b = random.randint(-o, o)  # 山丘z位置
            c = -1  # 山丘地基高度
            h = random.randint(1, 6)  # 山丘高度
            s = random.randint(4, 8)  # 山丘边长
            d = 1  # 逐层减小山丘边长
            t = random.choice([GRASS, SAND, BRICK])     # 山丘类型
            for y in xrange(c, c + h):    # 高度
                for x in xrange(a - s, a + s + 1):
                    for z in xrange(b - s, b + s + 1):
                        if (x - a) ** 2 + (z - b) ** 2 > (s + 1) ** 2:  # s>2时去除边角方块使其看起来更圆
                            continue
                        if (x - 0) ** 2 + (z - 0) ** 2 < 5 ** 2:  # 地图中心半径4区块范围内不生成山丘
                            continue
                        self.add_block((x, y, z), t, immediate=False)
                s -= d  # 减少侧面长度使山逐渐变小
                
        # 随机生成树
        temp = []
        for _ in range(500):
            x = random.randint(-o, o)  # 树x位置
            z = random.randint(-o, o)  # 树z位置
            h = random.randint(5, 8)  # 树高度
            for c in range(10):
                if (x,c,z) not in self.world:continue
                if self.world[(x,c,z)] != GRASS:continue  # 只在草方块上生成
                if not self.exposed((x,c,z)):continue  # 只在暴露在外的草方块上生成
                y = c + 1 # base of the tree
                for dy in xrange(y, y + h):
                    self.add_block((x, dy, z), ACACIA_LOG, immediate=False)
                temp.append((x,dy,z))
        # 生成树叶
        k = random.randint(1, 3)
        for x,y,z in temp:
            for dy in xrange(0, k + 1): # 高度
                for dx in xrange(-k, k + 1):
                    for dz in xrange(-k, k + 1):
                        if (dx) ** 2 + (dz) ** 2 + (dy) ** 2 > (k + 1) ** 2:continue  # 去除边角方块使其看起来更圆
                        self.add_block((x + dx, y + dy, z + dz), ACACIA_LEAVE, immediate=False)
            
            
        
    def hit_test(self, position, vector, max_distance=8):   # 方块更新检测BUD
        """
        从当前位置进行视线搜索。如果一个块与之相交，则返回它，同时返回先前在视线中的块。如果没有找到块，返回None
        返回key,previous：key是鼠标可操作的块(中心坐标)，根据人所在位置和方向向量求出，
        previous是与key处立方体相邻的空位置的中心坐标。
        Parameters
        ----------
        position : 三个元素
            (x, y, z) 视线位置
        vector : 三个元素
            视线向量
        max_distance : int
            可以寻找几个元素长度

        """
        m = 8
        x, y, z = position
        dx, dy, dz = vector
        previous = None
        for _ in xrange(max_distance * m):
            key = normalize((x, y, z))
            if key != previous and key in self.world:
                return key, previous
            previous = key
            x, y, z = x + dx / m, y + dy / m, z + dz / m
        return None, None

    def exposed(self, position):
        """
            判断方块是否被其他方块包围，没有被包围时返回True
        """
        x, y, z = position
        for dx, dy, dz in FACES:
            if (x + dx, y + dy, z + dz) not in self.world:
                return True
        return False

    def add_block(self, position, texture, immediate=True):
        """ 添加模块，有纹理与位置信息

        Parameters
        ----------
        position : 三个元素
            (x, y, z)
        texture : 三个元素
            `tex_coords()` 得到模块纹理
        immediate : bool
            是否立即绘制方块。

        """
        if position in self.world:
            self.remove_block(position, immediate)
        self.world[position] = texture  # 添加相应的位置和纹理
        self.sectors.setdefault(sectorize(position), []).append(position)
        if immediate:
            if self.exposed(position):
                self.show_block(position)
            self.check_neighbors(position)
            self.check_block_status(position)

    def remove_block(self, position, immediate=True):
        """ 移除对应位置模块

        Parameters
        ----------
        position : tuple of len 3
            位置(x, y, z)
        immediate : bool
            是否在视野中立即移除

        """
        del self.world[position]  # 把world中的position,texture对删除
        self.sectors[sectorize(position)].remove(position)  # 把区域中相应的position删除
        if immediate:
            if position in self.shown:
                self.hide_block(position)
            self.check_neighbors(position)
        # 删除一个立方体后，要检查它周围6个邻接的位置,是否有因此暴露出来的立方体，有的话要把它绘制出来

    def tnt_boom(self, position, immediate=True):
        """ 移除选定位置周围的模块，tnt炸药

        Parameters
        ----------
        position : tuple of len 3
            位置(x, y, z)
        immediate : bool
            是否在视野中立即移除

        """
        k = 1
        op = list(position)
        opx = op[0]
        opy = op[1]
        opz = op[2]
        for dx in xrange(-k,k+1):
            for dy in xrange(-k,k+1):
                for dz in xrange(-k,k+1):
                    pos = (opx+dx,opy+dy,opz+dz)
                    if pos not in self.world:
                        continue
                    if self.world[pos] == STONE:continue
                    if self.world[pos] == TNT:temp = pos    # 如果TNT爆炸范围内存在其他TNT，则记录下位置
                    else:temp = None
                    del self.world[pos]  # 把world中的position,texture对删除
                    self.sectors[sectorize(pos)].remove(pos)    # 把区域中相应的position删除
                    if immediate:
                        if pos in self.shown:
                            self.hide_block(pos)
                        self.check_neighbors(pos)
                    if temp is not None:self.tnt_boom(temp)     # 引爆其他TNT
                
                        
    def check_block_status(self, position):     # 检查是否有红石块和TNT相邻，如果有，引爆TNT
        x, y, z = position
        texture = self.world[position]
        if not self.exposed(position):return
        if texture != RED_STONE and texture != TNT:return
        for dx, dy, dz in FACES:
            key = (x + dx, y + dy, z + dz)
            if key not in self.world:
                continue
            if texture == RED_STONE:
                if self.world[key] == TNT:
                    self.tnt_boom(key)
            elif texture == TNT:
                if self.world[key] == RED_STONE:
                    self.tnt_boom(key)
        
    def check_neighbors(self, position):
        """
        检查“position”周围的所有块，确保它们的视觉状态是最新的。即隐藏未公开的块，并确保显示所有公开的块。
        在添加或删除块后使用
        """
        x, y, z = position
        for dx, dy, dz in FACES:
            key = (x + dx, y + dy, z + dz)
            if key not in self.world:
                continue
            if self.exposed(key):
                if key not in self.shown:   # 如果有方块暴露在外且没有在显示列表中
                    self.show_block(key)
            else:    # 如果没有暴露在外，而又在显示列表中，则立即隐藏它
                if key in self.shown:
                    self.hide_block(key)

    def show_block(self, position, immediate=True):
        """
        在给定的“位置”显示块。此时假定块已使用add_block（）添加
        Parameters
        ----------
        position : tuple of len 3
            位置(x, y, z)
        immediate : bool
            是否立即显示

        """
        texture = self.world[position]  # 取出纹理(其实是6个面的纹理坐标信息)
        self.shown[position] = texture  # 保存入shown字典中
        if immediate:
            self._show_block(position, texture)  # 立即显示
        else:
            self._enqueue(self._show_block, position, texture)  # 排队等待

    def _show_block(self, position, texture):
        """ 使用`show_block()`

        Parameters
        ----------
        position : tuple of len 3
            位置(x, y, z)
        texture : list of len 3
            纹理，用`tex_coords()`函数实现

        """
        x, y, z = position
        vertex_data = cube_vertices(x, y, z, 0.5)
        texture_data = list(texture)
        # create vertex list
        # FIXME Maybe `add_indexed()` should be used instead
        self._shown[position] = self.batch.add(24, GL_QUADS, self.group,
            ('v3f/static', vertex_data),
            ('t2f/static', texture_data))

    def hide_block(self, position, immediate=True):
        """ 隐藏给定位置的模块，但并不从world中移除

        Parameters
        ----------
        position : tuple of len 3
            位置(x, y, z)
        immediate : bool
            是否立即从视野中移除

        """
        self.shown.pop(position)   # 将要隐藏的立方体中心坐标从显示列表中移除
        if immediate:
            self._hide_block(position)
        else:
            self._enqueue(self._hide_block, position)

    def _hide_block(self, position):
        """ 使用'hide_block()` 方法

        """
        self._shown.pop(position).delete()  # 从_shown中弹出该位置并删除

    def show_sector(self, sector):
        """ 确保给定扇区中应显示的所有块都绘制到画布上
        
        """
        for position in self.sectors.get(sector, []):
            if position not in self.shown and self.exposed(position):   # 如果区域内的立方体位置没在显示列表且是显露在外的
                self.show_block(position, False)    # 显示立方体

    def hide_sector(self, sector):
        """ 确保给定扇区中应隐藏的所有块都已从画布中移除

        """
        for position in self.sectors.get(sector, []):
            if position in self.shown:
                self.hide_block(position, False)

    def change_sectors(self, before, after):
        """
            从“before”扇区移到“after”扇区。扇区是世界上一个相邻的x，y亚区域。扇区用于加速世界渲染

        """
        before_set = set()
        after_set = set()
        pad = 4
        for dx in xrange(-pad, pad + 1):
            for dy in [0]:  # xrange(-pad, pad + 1):
                for dz in xrange(-pad, pad + 1):
                    if dx ** 2 + dy ** 2 + dz ** 2 > (pad + 1) ** 2:
                        continue
                    if before:
                        x, y, z = before
                        before_set.add((x + dx, y + dy, z + dz))
                    if after:
                        x, y, z = after
                        after_set.add((x + dx, y + dy, z + dz))
        show = after_set - before_set
        hide = before_set - after_set
        for sector in show:
            self.show_sector(sector)
        for sector in hide:
            self.hide_sector(sector)

    def _enqueue(self, func, *args):
        """ 添加进事件队列

        """
        self.queue.append((func, args))

    def _dequeue(self):
        """ 先进先出，处理队头事件

        """
        func, args = self.queue.popleft()
        func(*args)

    def process_queue(self):
        """
        处理整个队列，同时定期休息。这使游戏循环平稳运行。队列包含对_show_block（）和_hide_block（）的调用，
        因此如果add_block（）或remove_block（）被调用且immediate=False，则应调用此方法

        """
        start = time.perf_counter()     # 该函数有两个功能，在第一次调用的时候，返回的是程序运行的实际时间；
                                        # 以第二次之后的调用，返回的是自第一次调用后,到这次调用的时间间隔
        while self.queue and time.perf_counter() - start < 1.0 / TICKS_PER_SEC:     # queue非空执行1/60秒的时间来处理队列中的事件
            self._dequeue()

    def process_entire_queue(self):     # 处理事件队列中的所有事件
        """ Process the entire queue with no breaks.不间断地处理整个队列。

        """
        while self.queue:
            self._dequeue()


class Window(pyglet.window.Window):

    def __init__(self, *args, **kwargs):
        super(Window, self).__init__(*args, **kwargs)
        # *args,化序列为位置参数：(1,2) -> func(1,2)
        # **kwargs,化字典为关键字参数：{'a':1,'b':2} -> func(a=1,b=2)
        # 初始时，鼠标事件没有绑定到游戏窗口
        self.exclusive = False

        # 飞行的重力不起作用而速度增加
        self.flying = False

        # Strafe 是朝着面对的方向横向移动
        self.strafe = [0, 0]  # [z, x]，z表示前后运动，1向后，x表示左右运动，1向右

        # 目前位置(x, y, z) . 注意，y为垂直于地面的轴
        self.position = (0, 0, 0)  # 开始位置在地图中间

        # 第一个元素是球员在x-z平面（地平面）的旋转，从z轴向下测量。第二个是从地平面向上的旋转角度。旋转以度为单位。
        # 垂直面旋转范围从-90（直向下看）到90（直向上看）。水平旋转范围是无限的
        self.rotation = (0, 0)
        # rotation(水平角x，俯仰角y)
        # 水平角是方向射线xoz上的投影与z轴负半轴的夹角，俯仰角是方向射线与xoz平面的夹角，初始面向-z方向，视线水平
        
        # 玩家当前在哪个扇区
        self.sector = None

        # reticle表示游戏窗口中间的那个十字，四个点绘制成两条直线
        self.reticle = None

        self.dy = 0  # y（向上）方向的速度。

        # 玩家可以放置的方块列表。按数字键循环。
        self.inventory = [BRICK, GRASS, SAND, TNT, RED_STONE, ACACIA_LEAVE, ACACIA_LOG, ACACIA_PLANKS]

        # 当前用户可以放置的方块
        self.block = self.inventory[0]

        # 可用数字键列表
        self.num_keys = [
            key._1, key._2, key._3, key._4, key._5,
            key._6, key._7, key._8, key._9, key._0]

        # 处理世界的模型的实例
        self.model = Model()

        # 游戏窗口左上角的label参数设置
        self.label = pyglet.text.Label('', font_name='Arial', font_size=18,
            x=10, y=self.height - 10, anchor_x='left', anchor_y='top',
            color=(0, 0, 0, 255))   # ( 字体名，字体大小，水平位置，竖直位置，居左，居上，字体颜色)
        # `update()`方法调用
        # TICKS_PER_SEC. 主游戏事件循环。
        pyglet.clock.schedule_interval(self.update, 1.0 / TICKS_PER_SEC)    # 每秒刷新60次

    def set_exclusive_mouse(self, exclusive):   # 设置鼠标事件是否绑定到游戏窗口
        """ 如果“exclusive”为True，则游戏将捕获鼠标；如果为False，则游戏将忽略鼠标

        """
        super(Window, self).set_exclusive_mouse(exclusive)
        self.exclusive = exclusive

    def get_sight_vector(self):     # 根据前进方向rotation来决定移动1单位距离时，各轴分量移动多少
        """
        返回当前视线向量，指示玩家正在寻找的方向
        """
        x, y = self.rotation
        # y的范围是-90到90，或者是-pi/2到pi/2，所以m的范围是0到1，在平行于地面向前看时是1，在垂直向上或向下看时是0
        m = math.cos(math.radians(y))  # m=cos(y),m=1,y=0,视线水平，m=1,y=pi/2,-pi/2,视线垂直向上或向下
        # dy的范围-1到1
        # dy=1视线向上，dy=-1，视线向下
        dy = math.sin(math.radians(y)) # dy=sin(y)
        dx = math.cos(math.radians(x - 90)) * m     # dx=cos(y)sin(x)
        dz = math.sin(math.radians(x - 90)) * m     # dz=-cos(y)cos(x)
        return (dx, dy, dz)

    def get_motion_vector(self):    # 计算运动时三个轴的位移增量
        """ 返回当前的运动矢量，指示玩家的速度

        Returns
        -------
        vector : tuple of len 3
            分别包含x、y和z上的速度的元组

        """
        if any(self.strafe):    # 只要strafe中有一项为真(不为0)，就执行
            x, y = self.rotation 
            strafe = math.degrees(math.atan2(*self.strafe))     # atan2是反正切函数，返回弧度，y在前，x在后 arctan(z/x)
            y_angle = math.radians(y)
            x_angle = math.radians(x + strafe)
            if self.flying:  # 如果允许飞，那么运动时会考虑垂直方向即y轴方向的运动
                m = math.cos(y_angle)   # m=cos(y_angle)=cos(y)
                dy = math.sin(y_angle)   # dy=sin(y_angle)=sin(y)
                if self.strafe[1]:
                    # 左右移动
                    dy = 0.0
                    m = 1
                if self.strafe[0] > 0: 
                    # z>0向后移动
                    dy *= -1   # dy = -dy
                # 上下飞行时，有左右的偏移
                dx = math.cos(x_angle) * m  # dx=cos(x_angle)*cos(y_angle)
                dz = math.sin(x_angle) * m  # dz=sin(x_angle)*cos(y_angle)
            else:
                dy = 0.0  # 不允许飞行
                dx = math.cos(x_angle)   # dx=cos(x_angle)
                dz = math.sin(x_angle)   # dz=sin(x_angle)
        else:  # strafe为空时不移动
            dy = 0.0
            dx = 0.0
            dz = 0.0
        return (dx, dy, dz)

    def update(self, dt):
        """ 每pyglet时钟重复调用此方法，即1/60s

        Parameters
        ----------
        dt : float
            上次调用后时间的变化。

        """
        self.model.process_queue()  # 用1/60的时间来处理队列中的事件，不一定要处理完
        sector = sectorize(self.position)
        if sector != self.sector:   # 如果position的sector与当前sector不一样，则替换
            self.model.change_sectors(self.sector, sector)
            if self.sector is None:     # 如果sector为空，处理队列中的所有事件
                self.model.process_entire_queue()
            self.sector = sector    # 更新sector
        m = 8
        dt = min(dt, 0.2)
        for _ in xrange(m):
            self._update(dt / m)

    def _update(self, dt):
        """ `update()`方法，实现大多数运动逻辑以及重力和碰撞检测
        Parameters
        ----------
        dt : float
            上次调用后时间的变化。

        """
        # walking
        speed = FLYING_SPEED if self.flying else WALKING_SPEED  # 如果能飞，速度15；否则为5
        d = dt * speed  # dt刻走过的距离
        dx, dy, dz = self.get_motion_vector()
        # 在空间中的新位置，不考虑重力
        dx, dy, dz = dx * d, dy * d, dz * d
        # gravity 如果不能飞，则使其在y方向上符合重力规律
        if not self.flying:
            # 更新速度
            # 如果在下落，撞地前一直加速
            # 如果在跳，下落前一直减速
            self.dy -= dt * GRAVITY  # dy=dy-dt*g
            self.dy = max(self.dy, -TERMINAL_VELOCITY)  # 不能超过最大下落速度
            dy += self.dy * dt  # dy=dy*dt
        # 碰撞
        x, y, z = self.position
        x, y, z = self.collide((x + dx, y + dy, z + dz), PLAYER_HEIGHT)     # 碰撞检测后应该移动到的位置
        self.position = (x, y, z)   # 更新位置

    def collide(self, position, height):
        """
        检查给定“位置”和“高度”的玩家是否与世界上的任何方块发生碰撞
        Parameters
        ----------
        position : tuple of len 3
            位置(x, y, z)
        height : int or float
            高度

        Returns
        -------
        position : tuple of len 3
            碰撞后位置

        """
        # 需要将与周围块的某个维度重叠的程度计算为碰撞。
        # 如果为0，则完全接触地形将被视为碰撞。
        # 如果.49，你沉到地上，好像穿过高高的草地。
        # 如果>=0.5，你会掉到地上
        pad = 0.25
        p = list(position)  # 将元组变为list
        np = normalize(position)
        for face in FACES:  # 检查周围6个面的立方体
            for i in xrange(3):  # (x,y,z)中每一维单独检测
                if not face[i]:  # 如果为0，过
                    continue
                # 和这个维度有多少重叠
                d = (p[i] - np[i]) * face[i]
                if d < pad:  # 如果小于0.25，过
                    continue
                for dy in xrange(height):  # 检测每个高度
                    op = list(np)
                    op[1] -= dy     # 判断当前及往下是否有方块
                    op[i] += face[i]    # 判断周围六个面是否有方块
                    if tuple(op) not in self.model.world:    # 如果周围无方块，则可以移动
                        continue
                    p[i] -= (d - pad) * face[i]     # 计算出正确的位置
                    if face == (0, -1, 0) or face == (0, 1, 0):
                        # 与地面或天花板相撞,停止上升或下降
                        self.dy = 0
                    break
        return tuple(p)  # 返回的p是碰撞检测后应该移动到的位置

    def on_mouse_press(self, x, y, button, modifiers):
        """ 按下鼠标按钮时调用

        Parameters
        ----------
        x, y : int
            鼠标单击的坐标。如果鼠标被捕获，则始终位于屏幕中心
        button : int
           1为左击，4为右击
        modifiers : int
            表示单击鼠标按钮时按下的任何修改键的数字

        """
        if self.exclusive:   # 如果“exclusive”为True，则游戏将捕获鼠标；如果为False，则游戏将忽略鼠标
            vector = self.get_sight_vector()    # 视线角度向量
            block, previous = self.model.hit_test(self.position, vector)
            print(block)
            print(previous)
            texture = self.model.world[block]
            np = list(previous)
            if (button == mouse.RIGHT) or \
                    ((button == mouse.LEFT) and (modifiers & key.MOD_CTRL)): #右击
                # ON OSX, control + left click = right click.
                if previous:    # 如果先前有方块，则可以放置方块
                    self.model.add_block(previous, self.block)
                            
            elif button == pyglet.window.mouse.LEFT and block:  # 左击并且有方块
                if texture != STONE:    # 如果block不是石块，就移除它
                    self.model.remove_block(block)
        else:   # 否则设置“exclusive”为True
            self.set_exclusive_mouse(True)

    def on_mouse_motion(self, x, y, dx, dy):
        """  鼠标移动事件，处理视角的变化，变化幅度由参数m控制
             该函数将这个位移转换成了水平角x和俯仰角y的变化
             dx,dy表示鼠标从上一位置移动到当前位置x，y轴上的位移
        Parameters
        ----------
        x, y : int
            鼠标移动事件，处理视角的变化，鼠标总是在中心
        dx, dy : float
            dx,dy表示鼠标从上一位置移动到当前位置x，y轴上的位移

        """
        if self.exclusive:
            m = 0.15
            x, y = self.rotation
            x, y = x + dx * m, y + dy * m
            y = max(-90, min(90, y))  # y不能超过正负pi/2
            self.rotation = (x, y)

    def on_key_press(self, symbol, modifiers):
        """ 当玩家按下一个键时调用
            按下键盘事件，长按W，S，A，D键将不断改变坐标
        Parameters
        ----------
        symbol : int
            按下按键的值
        modifiers : int
            按下修饰按键的值

        """
        if symbol == key.W:  # 前进
            self.strafe[0] -= 1
        elif symbol == key.S:   # 后退
            self.strafe[0] += 1
        elif symbol == key.A:   # 向左
            self.strafe[1] -= 1
        elif symbol == key.D:   # 向右
            self.strafe[1] += 1
        elif symbol == key.SPACE:   # 跳跃
            if self.dy == 0:
                self.dy = JUMP_SPEED
        elif symbol == key.ESCAPE:  # 退出，将“exclusive”置为False
            self.set_exclusive_mouse(False)
        elif symbol == key.TAB:     # 按下TAB切换飞行
            self.flying = not self.flying
        elif symbol in self.num_keys:
            index = (symbol - self.num_keys[0]) % len(self.inventory)   # 0~9模5循环
            self.block = self.inventory[index]

    def on_key_release(self, symbol, modifiers):
        """ 当玩家释放按键时调用
            释放按键事件

        Parameters
        ----------
        symbol : int
            按下按键的值
        modifiers : int
            按下修饰按键的值
        按键释放时，各方向退回一个单位
        """
        if symbol == key.W:
            self.strafe[0] += 1
        elif symbol == key.S:
            self.strafe[0] -= 1
        elif symbol == key.A:
            self.strafe[1] += 1
        elif symbol == key.D:
            self.strafe[1] -= 1

    def on_resize(self, width, height):  # 窗口大小变化响应事件
        """
        当窗口调整为新的“width”和“height”时调用`
        """
        # label的纵坐标
        self.label.y = height - 10
        # reticle更新，包含四个点，绘制成两条直线
        if self.reticle:
            self.reticle.delete()
        x, y = self.width // 2, self.height // 2
        n = 10
        self.reticle = pyglet.graphics.vertex_list(4,
            ('v2i', (x - n, y, x + n, y, x, y - n, x, y + n))
        )

    def set_2d(self):
        """ 配置OpenGL以在2d中绘制

        """
        width, height = self.get_size()
        glDisable(GL_DEPTH_TEST)
        viewport = self.get_viewport_size()
        glViewport(0, 0, max(1, viewport[0]), max(1, viewport[1]))
        glMatrixMode(GL_PROJECTION)
        glLoadIdentity()
        glOrtho(0, max(1, width), 0, max(1, height), -1, 1)
        glMatrixMode(GL_MODELVIEW)
        glLoadIdentity()

    def set_3d(self):
        """ 配置OpenGL以在3d中绘制

        """
        width, height = self.get_size()
        glEnable(GL_DEPTH_TEST)
        viewport = self.get_viewport_size()
        glViewport(0, 0, max(1, viewport[0]), max(1, viewport[1]))
        glMatrixMode(GL_PROJECTION)
        glLoadIdentity()
        gluPerspective(65.0, width / float(height), 0.1, 60.0)
        glMatrixMode(GL_MODELVIEW)
        glLoadIdentity()
        x, y = self.rotation
        glRotatef(x, 0, 1, 0)
        glRotatef(-y, math.cos(math.radians(x)), 0, math.sin(math.radians(x)))
        x, y, z = self.position
        glTranslatef(-x, -y, -z)

    def on_draw(self):
        """ 调用pyglet绘制窗口
            重写Window的on_draw函数
            当窗口需要被重绘时，事件循环(EventLoop)就会调度该事件
        """
        self.clear()
        self.set_3d()   # 进入3d模式
        glColor3d(1, 1, 1)
        self.model.batch.draw()     # 将batch中保存的顶点列表绘制出来
        self.draw_focused_block()   # 绘制鼠标focus的立方体的线框
        self.set_2d()   # 进入2d模式
        self.draw_label()   # 进入2d模式
        self.draw_reticle()     # 绘制窗口中间的十字

    def draw_focused_block(self):
        """ 围绕当前位于十字准线下的块绘制黑色边。

        """
        vector = self.get_sight_vector()
        block = self.model.hit_test(self.position, vector)[0]
        if block:
            x, y, z = block
            vertex_data = cube_vertices(x, y, z, 0.51)
            glColor3d(0, 0, 0)
            glPolygonMode(GL_FRONT_AND_BACK, GL_LINE)
            pyglet.graphics.draw(24, GL_QUADS, ('v3f/static', vertex_data))
            glPolygonMode(GL_FRONT_AND_BACK, GL_FILL)

    def draw_label(self):
        """ 在画面左上角显示标签
            帧率，当前位置坐标，显示的方块数及总共的方块数

        """
        x, y, z = self.position
        self.label.text = '%02d (%.2f, %.2f, %.2f) %d / %d' % (
            pyglet.clock.get_fps(), x, y, z,
            len(self.model._shown), len(self.model.world))
        self.label.draw()   # 绘制label的text

    def draw_reticle(self):     # 绘制游戏窗口中间的十字，一条横线加一条竖线
        """ 在屏幕中央画十字准线

        """
        glColor3d(0, 0, 0)
        self.reticle.draw(GL_LINES)


def setup_fog():
    """
        设置雾效果
    """
    # 启用雾。“雾”将雾颜色与每个光栅化像素片段的后纹理颜色混合
    glEnable(GL_FOG)
    # 雾颜色
    glFogfv(GL_FOG_COLOR, (GLfloat * 4)(0.5, 0.69, 1.0, 1))
    # 不关心速度与品质
    glHint(GL_FOG_HINT, GL_DONT_CARE)
    # 指定用于雾颜色计算混合因子的公式
    glFogi(GL_FOG_MODE, GL_LINEAR)
    # 多远或多近雾开始或结束
    # 多稠密
    glFogf(GL_FOG_START, 20.0)
    glFogf(GL_FOG_END, 60.0)


def setup():
    """ 基本OpenGL配置

    """
    # 设定天空颜色 "clear"
    glClearColor(0.5, 0.69, 1.0, 1)
    # 对背面镶嵌面启用消隐（而不是渲染）（对视野不可见的面）
    glEnable(GL_CULL_FACE)
    # 将“纹理缩小/放大”功能设置为距指定纹理坐标最近（曼哈顿距离最近）的GL_NEAREST。
    # “GL_NEAREST”通常比GL_LINEAR快，它可以生成边缘更清晰的纹理图像，因为纹理元素之间的过渡不是那么平滑
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST)
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST)
    setup_fog()  # 设置雾效果


def main():
    window = Window(width=800, height=600, caption='Pyglet', resizable=True)
    # 隐藏鼠标光标并防止鼠标离开窗口
    window.set_exclusive_mouse(True)
    setup()
    pyglet.app.run()


if __name__ == '__main__':
    main()
