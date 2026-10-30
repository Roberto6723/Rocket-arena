#!/usr/bin/env python3
"""Fox Rocket Arena: HTTP + authoritative multiplayer WebSocket server.

Install: python3 -m pip install -r requirements.txt
Run:     python3 multiplayer_server.py
Friends connect to the same host via :8000 (LAN or a publicly deployed server).
"""
from __future__ import annotations

import asyncio
import json
import math
import os
import random
import re
import secrets
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from aiohttp import WSMsgType, web

BASE = Path(__file__).resolve().parent
PORT = int(os.environ.get('PORT', '8000'))
FW, FL, GW, GH, ROOF, BALL_R = 825.0, 1320.0, 260.0, 195.0, 540.0, 42.0
TICK_RATE = 30
BROADCAST_RATE = 15
AI_NAMES = ('FOX', 'REX', 'ACE', 'NOVA', 'JET', 'BOLT')
AI_CARS = ('fox', 'viper', 'comet', 'titan', 'viper', 'comet')
DEFAULT_COLORS = ('#f45b17', '#218bfa')
ROOMS: dict[str, 'Room'] = {}
PRESENCE: set[web.WebSocketResponse] = set()
MAX_HUMANS = 120

def human_count():
    return sum(len(r.members) for r in ROOMS.values())

def players_online():
    return human_count() + len(PRESENCE)



def clamp(value: float, a: float, b: float) -> float:
    return max(a, min(value, b))


def angle_diff(a: float, b: float) -> float:
    return math.atan2(math.sin(a-b), math.cos(a-b))


def safe_name(value: Any) -> str:
    name = re.sub(r'[\x00-\x1f\x7f<>]', '', str(value or 'PLAYER')).strip()
    return name[:16] or 'PLAYER'


def safe_color(value: Any, fallback: str) -> str:
    return value if isinstance(value, str) and re.fullmatch(r'#[0-9a-fA-F]{6}', value) else fallback


def safe_style(value: Any) -> str:
    return value if value in ('fox', 'viper', 'titan', 'comet') else 'fox'


@dataclass
class Car:
    slot: int
    x: float = 0
    y: float = 0
    z: float = 0
    vx: float = 0
    vy: float = 0
    vz: float = 0
    yaw: float = 0
    pitch: float = 0
    roll: float = 0
    boost: float = 100
    jumps: int = 0
    airtime: float = 0
    human: 'Client | None' = None
    control: dict = field(default_factory=dict)
    ai_jump_cooldown: float = 0
    on_wall: bool = False

    @property
    def team(self):
        return self.slot % 2

    @property
    def name(self):
        return self.human.name if self.human else AI_NAMES[self.slot]

    @property
    def style(self):
        return self.human.style if self.human else AI_CARS[self.slot]

    @property
    def color(self):
        return self.human.color if self.human else DEFAULT_COLORS[self.team]

    @property
    def explosion(self):
        return self.human.explosion if self.human else ('#ff741c' if self.team == 0 else '#25a5ff')

    def kickoff(self, size: int) -> None:
        # Symmetrical kickoff formation for 1v1, 2v2 and 3v3.
        lane = self.slot // 2
        x = (0, -240, 270)[lane] * (1 if self.team == 0 else -1)
        self.x, self.z = x, (0.63 + lane * 0.07) * FL * (1 if self.team == 0 else -1)
        self.y = self.vx = self.vy = self.vz = self.pitch = self.roll = 0
        self.yaw = 0 if self.team == 0 else math.pi
        self.boost = 100
        self.jumps = 0
        self.airtime = 0
        self.on_wall = False
        self.control.clear()
        self.ai_jump_cooldown = 0

    def payload(self) -> dict:
        return {'slot': self.slot, 'team': self.team, 'name': self.name,
                'human': self.human is not None, 'style': self.style,
                'color': self.color, 'x': round(self.x, 2), 'y': round(self.y, 2),
                'z': round(self.z, 2), 'vx': round(self.vx, 2), 'vy': round(self.vy, 2),
                'vz': round(self.vz, 2), 'yaw': round(self.yaw, 4),
                'pitch': round(self.pitch, 4), 'roll': round(self.roll, 4),
                'boost': round(self.boost, 1), 'ground': self.y < 1 and not self.on_wall, 'onWall': self.on_wall,
                'boosting': bool(self.control.get('boost') or self.control.get('auto')) and self.boost > 0}


@dataclass(eq=False)
class Client:
    socket: web.WebSocketResponse
    name: str
    style: str
    color: str
    explosion: str
    room: 'Room | None' = None
    slot: int = -1


class Room:
    def __init__(self, code: str, size: int, private: bool):
        self.code, self.size, self.private = code, size, private
        self.cars = [Car(i) for i in range(size*2)]
        self.members: set[Client] = set()
        self.ball = {'x': 0., 'y': BALL_R, 'z': 0., 'vx': 0., 'vy': 0., 'vz': 0.}
        self.score = [0, 0]
        self.seconds = 180.
        self.phase = 'play'
        self.phase_left = 0.
        self.last_touch: tuple[str, int, str] | None = None
        self.goal_id = 0
        self.goal_event: dict | None = None
        self.accumulator = 0
        self.shots = [0, 0]
        self.ot_shots = [0, 0]
        self.overtime = False
        self.winner = None
        self.win_reason = ''
        self.pending_winner = None
        self.last_shot_touch = None
        self.last_broadcast = 0
        self.created = time.monotonic()
        self.reset_positions()

    def available(self) -> bool:
        return len(self.members) < self.size*2 and self.phase=='play' and self.seconds>15

    def assign(self, client: Client) -> int:
        # Allocate alternating teams to keep matches balanced as friends arrive.
        empty = [car for car in self.cars if car.human is None]
        team0 = sum(car.human is not None for car in self.cars if car.team == 0)
        team1 = sum(car.human is not None for car in self.cars if car.team == 1)
        preferred = 0 if team0 <= team1 else 1
        car = next((c for c in empty if c.team == preferred), empty[0])
        car.human, client.room, client.slot = client, self, car.slot
        self.members.add(client)
        return car.slot

    def release(self, client: Client) -> None:
        if client.slot >= 0 and self.cars[client.slot].human is client:
            self.cars[client.slot].human = None
            self.cars[client.slot].control.clear()
        self.members.discard(client)
        client.room, client.slot = None, -1

    def reset_positions(self) -> None:
        for car in self.cars:
            car.kickoff(self.size)
        self.ball.update(x=0., y=BALL_R, z=0., vx=0., vy=0., vz=0.)
        self.last_touch = None

    def snapshot(self) -> dict:
        return {'type': 'state', 'room': self.code, 'mode': self.size,
                'overtime': self.overtime, 'shots': self.shots[:],
                'winner': self.winner, 'winReason': self.win_reason,
                'onlinePlayers': players_online(),
                'phase': self.phase, 'phaseLeft': round(self.phase_left, 2),
                'time': round(self.seconds, 1), 'score': self.score[:],
                'goalId': self.goal_id, 'goal': self.goal_event,
                'cars': [c.payload() for c in self.cars],
                'ball': {k: round(v, 2) for k, v in self.ball.items()}}

    async def send_all(self, packet: dict):
        if not self.members:
            return
        data = json.dumps(packet, separators=(',', ':'))
        clients = list(self.members)
        results = await asyncio.gather(*(cl.socket.send_str(data) for cl in clients if not cl.socket.closed), return_exceptions=True)
        # send failures are cleaned up in the WebSocket handler.
        return results

    def ai_input(self, car: Car, dt: float) -> dict:
        b = self.ball
        ahead = clamp(math.hypot(b['x']-car.x, b['z']-car.z)/390, .08, .55)
        target_x = clamp(b['x'] + b['vx'] * ahead, -FW+45, FW-45)
        target_z = clamp(b['z'] + b['vz'] * ahead, -FL+55, FL-55)
        # One player chases, others offset/cover the goal.
        if car.slot >= 2 and car.slot % 4 == 3:
            target_x = clamp(target_x * .7, -GW-70, GW+70)
            danger = (target_z > 0) if car.team == 0 else (target_z < 0)
            if not danger:
                target_z = (FL-240) * (1 if car.team == 0 else -1)
        elif car.slot >= 2 and car.slot % 4 == 2:
            target_x = clamp(target_x + (110 if car.team else -110), -FW+55, FW-55)
        else:
            attack_z = -FL if car.team == 0 else FL
            vx, vz = -target_x, attack_z-target_z
            length = math.hypot(vx, vz) or 1
            target_x -= 65 * vx / length
            target_z -= 65 * vz / length
        wanted = math.atan2(target_x - car.x, -(target_z - car.z))
        turn = angle_diff(wanted, car.yaw)
        distance = math.hypot(target_x - car.x, target_z - car.z)
        control = {'up': True, 'left': turn < -.09, 'right': turn > .09,
                   'boost': abs(turn) < .25 and distance > 200 and car.boost > 22}
        car.ai_jump_cooldown = max(0, car.ai_jump_cooldown-dt)
        if car.y < 1 and car.ai_jump_cooldown <= 0 and distance < 95 and b['y'] > 62:
            control['jump'] = True
            car.ai_jump_cooldown = 1.5
        return control

    def update_car(self, car: Car, dt: float) -> None:
        ctrl = car.control if car.human else self.ai_input(car, dt)
        up, down = bool(ctrl.get('up')), bool(ctrl.get('down'))
        throttle = clamp(float(ctrl.get('throttle',int(up)-int(down))), -1, 1)
        steer = clamp(float(ctrl.get('steer',int(bool(ctrl.get('right')))-int(bool(ctrl.get('left'))))), -1, 1)
        air = car.y > 1 and not car.on_wall
        launching = bool(ctrl.get('auto'))
        if ctrl.pop('jump', False) or launching and not air:
            if not air:
                car.y = max(car.y, 3)
                car.on_wall = False
                car.vy = max(car.vy, 320)
                car.jumps, car.airtime = 1, 0
                if launching:
                    car.pitch = max(car.pitch, .68)
            elif car.jumps == 1 and car.airtime < 1.55:
                car.jumps = 2
                car.vy = max(car.vy + 300, 370)
        air = car.y > 1 and not car.on_wall
        boosting = (bool(ctrl.get('boost')) or launching) and car.boost > 0
        if air:
            car.airtime += dt
            car.yaw += steer*2.5*dt
            car.pitch = clamp(car.pitch-throttle*2.35*dt, -math.pi*.49, math.pi*.49)
            car.roll += (int(bool(ctrl.get('rollRight')))-int(bool(ctrl.get('rollLeft'))))*4.1*dt
            if launching:
                car.pitch += (1.04-car.pitch)*min(1,dt*4.5)
            fx = math.sin(car.yaw)*math.cos(car.pitch)
            fz = -math.cos(car.yaw)*math.cos(car.pitch)
            fy = math.sin(car.pitch)
            if boosting:
                car.vx += fx * 1480*dt
                car.vz += fz * 1480*dt
                car.vy += fy * 1480*dt
            car.vy -= 520*dt
            decay = math.exp(-.12*dt)
            car.vx *= decay; car.vy *= decay; car.vz *= decay
            speed = math.sqrt(car.vx**2+car.vy**2+car.vz**2)
            maximum = 850 if boosting else 650
            if speed > maximum:
                fact = maximum/speed
                car.vx *= fact; car.vy *= fact; car.vz *= fact
            car.x += car.vx*dt; car.y += car.vy*dt; car.z += car.vz*dt
            if abs(car.x) > FW-18:
                car.x = math.copysign(FW-18,car.x); car.vx *= -.35
            if abs(car.z) > FL-19:
                car.z = math.copysign(FL-19,car.z); car.vz *= -.35
            if car.y > ROOF-40:
                car.y = ROOF-40; car.vy = min(0,car.vy)
            if car.y <= 0:
                car.y=car.vy=car.pitch=car.roll=0
                car.on_wall=False
                car.jumps=0
                if math.hypot(car.vx,car.vz)>10:
                    car.yaw = math.atan2(car.vx,-car.vz)
        else:
            speed = math.hypot(car.vx,car.vz)
            car.yaw += steer * 3.15*dt*(.76+.24*min(1,speed/150))*(-.85 if throttle<0 else 1)
            dx,dz = math.sin(car.yaw),-math.cos(car.yaw)
            accel = 850 if throttle>0 and boosting else 510 if throttle>0 else -390 if throttle<0 else 0
            car.vx += dx*accel*dt; car.vz += dz*accel*dt
            friction = math.exp(-1.55*dt)
            car.vx *= friction; car.vz *= friction
            forward = car.vx*dx + car.vz*dz
            grip = 1-math.exp(-8*dt)
            car.vx += (dx*forward-car.vx)*grip
            car.vz += (dz*forward-car.vz)*grip
            speed = math.hypot(car.vx,car.vz)
            maximum = 435 if boosting else 295
            if speed > maximum:
                car.vx *= maximum/speed; car.vz *= maximum/speed
            car.x += car.vx*dt; car.z += car.vz*dt
            car.x=clamp(car.x,-FW+18,FW-18)
            car.z=clamp(car.z,-FL+18,FL-18)
            # The floor smoothly rises into the rounded arena walls.
            sx=max(0,abs(car.x)-(FW-110))
            sz=max(0,abs(car.z)-(FL-110))
            climb=max(sx,sz)
            if climb > 0:
                car.on_wall=True
                car.y=110-math.sqrt(max(0,110*110-climb*climb))
                car.pitch=math.asin(clamp(climb/110,0,.99))
            else:
                car.on_wall=False
                car.y=0;car.pitch=car.roll=0
        car.boost = clamp(car.boost + (-39 if boosting else 12 if car.y<1 else 0)*dt, 0, 100)
        if car.human:
            # Clear transient jump but retain held driving controls.
            car.control.pop('jump', None)

    def update_ball(self, dt: float):
        b=self.ball
        b['vy'] -= 460*dt
        b['x'] += b['vx']*dt; b['y'] += b['vy']*dt; b['z'] += b['vz']*dt
        b['vx'] *= math.exp(-.2*dt); b['vz'] *= math.exp(-.2*dt)
        for c in self.cars:
            dx,dy,dz=b['x']-c.x,b['y']-(c.y+16),b['z']-c.z
            d=math.sqrt(dx*dx+dy*dy+dz*dz)
            min_dist=BALL_R+32
            if d >= min_dist:
                continue
            if d < .001:
                dx,dy,dz,d=0,1,0,1
            nx,ny,nz=dx/d,dy/d,dz/d
            closing=max(0,(c.vx-b['vx'])*nx+(c.vy-b['vy'])*ny+(c.vz-b['vz'])*nz)
            airborne=c.y>1
            impulse=(145+.65*closing) if airborne else (230+.88*closing)
            if c.control.get('boost'): impulse+=65 if airborne else 105
            b['vx']=nx*impulse+c.vx*.45
            b['vy']=ny*impulse+c.vy*.45+20
            b['vz']=nz*impulse+c.vz*.45
            b['x']=c.x+nx*(min_dist+.5)
            b['y']=c.y+16+ny*(min_dist+.5)
            b['z']=c.z+nz*(min_dist+.5)
            self.last_touch=(c.name,c.team,c.explosion)
            # Count each meaningful offensive shot once per car touch.
            heading_to_enemy = b['vz'] < -95 if c.team == 0 else b['vz'] > 95
            in_shooting_lane = abs(b['x'] + b['vx'] * .8) < GW + 155
            if heading_to_enemy and in_shooting_lane:
                self.shots[c.team] += 1
                if self.overtime: self.ot_shots[c.team] += 1
        if abs(b['z']) > FL-BALL_R and abs(b['x'])<GW-BALL_R-3 and b['y']+BALL_R<GH-3:
            self.goal(0 if b['z']<0 else 1)
            return
        if b['y']<BALL_R:
            b['y']=BALL_R;b['vy']=abs(b['vy'])*.55
            if b['vy']<18: b['vy']=0
            b['vx']*=math.exp(-.55*dt);b['vz']*=math.exp(-.55*dt)
        # Wall + corner support. The ball can roll up the base of a wall.
        for key,limit in [('x',FW),('z',FL)]:
            if key=='z' and abs(b['x'])<GW+5 and b['y']+BALL_R<GH-4:
                continue
            bound=limit-BALL_R
            if abs(b[key])>bound:
                b[key]=math.copysign(bound,b[key]);b['v'+key]*=-.68
            ramp=max(0,abs(b[key])-(limit-110))
            if 0<ramp<110-BALL_R:
                floor=110-math.sqrt((110-BALL_R)**2-ramp**2)
                if b['y']<floor:
                    b['y']=floor;b['vy']=max(0,b['vy'])*.35
        if b['y']>ROOF-BALL_R-8:
            b['y']=ROOF-BALL_R-8;b['vy']=-abs(b['vy'])*.65

    def goal(self, team: int):
        if self.phase != 'play':return
        self.score[team]+=1
        self.goal_id+=1
        if self.last_touch:
            name,touch_team,explosion=self.last_touch
            scorer=(name+' SCORES!') if touch_team==team else (name+' OWN GOAL!')
        else:
            scorer=('ORANGE' if team==0 else 'BLUE')+' SCORES!'
            explosion='#ff741c' if team==0 else '#25a5ff'
        self.goal_event={'id':self.goal_id,'team':team,'scorer':scorer,'explosion':explosion,
                         'x':self.ball['x'],'y':self.ball['y'],'z':self.ball['z']}
        self.phase='goal'
        if self.overtime: self.pending_winner=team
        # Clients show explosion and replay before the next kickoff or final screen.
        self.phase_left=19.5
        for c in self.cars: c.vx=c.vy=c.vz=0

    def finish(self, team: int, reason: str):
        self.winner=team
        self.win_reason=reason
        self.phase='finished'
        self.phase_left=0
        self.pending_winner=None

    def tick(self,dt):
        if self.phase!='play':
            self.phase_left-=dt
            if self.phase_left<=0:
                if self.phase=='goal':
                    if self.pending_winner is not None:
                        self.finish(self.pending_winner, 'OVERTIME GOLDEN GOAL')
                    else:
                        self.reset_positions();self.phase='play';self.goal_event=None
                elif self.phase=='finished':
                    # Keep results visible; a future new room handles the next match.
                    self.phase_left=0
                self.phase_left=0
            return
        self.seconds=max(0,self.seconds-dt)
        if self.seconds<=0:
            if not self.overtime:
                if self.score[0]==self.score[1]:
                    self.overtime=True;self.seconds=90
                else:
                    self.finish(0 if self.score[0]>self.score[1] else 1, 'FINAL SCORE')
            else:
                if self.shots[0]!=self.shots[1]:
                    self.finish(0 if self.shots[0]>self.shots[1] else 1,'OVERTIME · MOST SHOTS')
                elif self.ot_shots[0]!=self.ot_shots[1]:
                    self.finish(0 if self.ot_shots[0]>self.ot_shots[1] else 1,'OVERTIME · MOST OT SHOTS')
                else:
                    self.finish(random.randint(0,1),'OVERTIME · SHOTS TIED · COIN TOSS')
            return
        for car in self.cars: self.update_car(car,dt)
        # Gentle car-to-car shoves.
        for i,a in enumerate(self.cars):
            for other in self.cars[i+1:]:
                dx,dz=other.x-a.x,other.z-a.z
                dist=math.hypot(dx,dz)
                if dist>=39 or abs(a.y-other.y)>30:continue
                nx,nz=(dx/dist,dz/dist) if dist>.001 else (1,0)
                shift=(39-dist)*.5
                a.x-=nx*shift;a.z-=nz*shift
                other.x+=nx*shift;other.z+=nz*shift
        self.update_ball(dt)
        for c in self.cars:
            for px in (-430,-215,0,215,430):
                if abs(c.x-px)<25 and (abs(c.z-670)<25 or abs(c.z+670)<25) and c.y<24:
                    c.boost=min(100,c.boost+25*dt)


async def game_loop(app: web.Application):
    interval=1/TICK_RATE
    last=time.monotonic()
    while True:
        now=time.monotonic();dt=min(.1,now-last);last=now
        for room in list(ROOMS.values()):
            if not room.members:
                ROOMS.pop(room.code,None)
                continue
            room.accumulator+=dt
            while room.accumulator>=interval:
                room.tick(interval)
                room.accumulator-=interval
            if now-room.last_broadcast>=1/BROADCAST_RATE:
                room.last_broadcast=now
                await room.send_all(room.snapshot())
        await asyncio.sleep(max(0,interval*.5))


async def index(request):
    return web.FileResponse(BASE/'index.html')


async def ws_handler(request):
    ws=web.WebSocketResponse(heartbeat=20,max_msg_size=2048)
    await ws.prepare(request)
    client=None
    try:
        first=await asyncio.wait_for(ws.receive(),10)
        if first.type!=WSMsgType.TEXT: return ws
        try:data=json.loads(first.data)
        except (ValueError,TypeError): return ws
        if data.get('type')!='join':return ws
        mode=data.get('mode',1)
        if type(mode) is not int or mode not in (1,2,3):
            await ws.send_json({'type':'error','message':'Choose 1v1, 2v2 or 3v3.'})
            return ws
        if players_online() >= MAX_HUMANS:
            await ws.send_json({'type':'error','message':'The server is full. Try again later.'})
            return ws
        client=Client(ws,safe_name(data.get('name')),
                      safe_style(data.get('style')),
                      safe_color(data.get('color'),DEFAULT_COLORS[0]),
                      safe_color(data.get('explosion'),'#ff741c'))
        requested=str(data.get('code') or '').upper().strip()
        if requested and not re.fullmatch(r'[A-Z0-9]{3,8}',requested):
            await ws.send_json({'type':'error','message':'Room code must be 3–8 letters or numbers.'})
            return ws
        if requested:
            room=ROOMS.get(requested)
            if room is None:
                room=Room(requested,mode,True);ROOMS[requested]=room
            elif room.size!=mode:
                await ws.send_json({'type':'error','message':'This room uses a different game mode.'})
                return ws
            elif not room.available():
                await ws.send_json({'type':'error','message':'This room is full.'})
                return ws
        else:
            # Join an occupied global room before starting a new AI-filled room.
            candidates=[r for r in ROOMS.values() if not r.private and r.size==mode and r.available()]
            room=max(candidates,key=lambda r:(len(r.members),r.seconds)) if candidates else None
            if room is None:
                code=secrets.token_hex(3).upper()
                while code in ROOMS:code=secrets.token_hex(3).upper()
                room=Room(code,mode,False);ROOMS[code]=room
        slot=room.assign(client)
        await ws.send_json({'type':'welcome','room':room.code,'mode':mode,'slot':slot,
                            'state':room.snapshot()})
        async for msg in ws:
            if msg.type==WSMsgType.TEXT:
                try:data=json.loads(msg.data)
                except (ValueError,TypeError):continue
                if not isinstance(data,dict):continue
                if data.get('type')=='input' and client.room is room:
                    control=room.cars[slot].control
                    for key in ('up','down','left','right','boost','auto','rollLeft','rollRight'):
                        control[key]=bool(data.get(key))
                    for key in ('throttle','steer'):
                        raw=data.get(key)
                        if isinstance(raw,(float,int)) and math.isfinite(raw):
                            control[key]=clamp(float(raw),-1,1)
                    if data.get('jump'):control['jump']=True
                elif data.get('type')=='ping':await ws.send_json({'type':'pong'})
            elif msg.type in (WSMsgType.ERROR,WSMsgType.CLOSE):break
    except asyncio.TimeoutError:
        pass
    finally:
        if client and client.room:
            client.room.release(client)
        if not ws.closed:await ws.close()
    return ws


async def status(request):
    response=web.json_response({
        'onlinePlayers':players_online(),
        'inMatches':human_count(),
        'inLobby':len(PRESENCE),
        'activeMatches':len(ROOMS),
        'waitingForPlayers':sum(r.size*2-len(r.members) for r in ROOMS.values()),
        'server':'Fox Rocket Arena Public Matchmaking',
    },headers={'Access-Control-Allow-Origin':'*','Cache-Control':'no-store'})
    return response


async def presence_handler(request):
    ws=web.WebSocketResponse(heartbeat=20,max_msg_size=2048)
    await ws.prepare(request)
    PRESENCE.add(ws)
    try:
        async for message in ws:
            if message.type==WSMsgType.ERROR:break
    finally:
        PRESENCE.discard(ws)
    return ws


async def health(request):
    return web.json_response({'ok':True})


async def server_context(app):
    task=asyncio.create_task(game_loop(app))
    yield
    task.cancel()
    try:await task
    except asyncio.CancelledError:pass


app=web.Application()
app.router.add_get('/',index)
app.router.add_get('/index.html',index)
app.router.add_get('/ws',ws_handler)
app.router.add_get('/status',status)
app.router.add_get('/presence',presence_handler)
app.router.add_get('/health',health)
app.cleanup_ctx.append(server_context)

if __name__=='__main__':
    print(f'Fox Rocket Arena ONLINE — http://localhost:{PORT}')
    print('Public matchmaking uses /ws, online player counter uses /status')
    web.run_app(app,host='0.0.0.0',port=PORT,access_log=None)
