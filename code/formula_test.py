import random
from fractions import Fraction as F
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def br(u,v,w): return dot(u,cross(v,w))
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def sub(u,v): return tuple(x-y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)
def rnd(n=4):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(31)
badP=badQ=badR=0; tested=0
for _ in range(3000):
    O,A,B,C=rnd(),rnd(),rnd(),rnd()
    al,be,ga,de,ep,ze=[random.randint(-4,4) for _ in range(6)]
    Ap=add(smul(al,A),smul(be,O)); Bp=add(smul(ga,B),smul(de,O)); Cp=add(smul(ep,C),smul(ze,O))
    t=br(A,B,O); u=br(B,C,O); v=br(A,C,O)
    P=cross(cross(A,B),cross(Ap,Bp)); Q=cross(cross(B,C),cross(Bp,Cp)); R=cross(cross(C,A),cross(Cp,Ap))
    Pc=smul(t, sub(smul(al*de,A), smul(be*ga,B)))
    Qc=smul(u, sub(smul(ga*ze,B), smul(de*ep,C)))
    Rc=smul(v*ga*be, sub(A,C))
    tested+=1
    if P!=Pc: badP+=1
    if Q!=Qc: badQ+=1
    if R!=Rc: badR+=1
print("tested",tested,"badP",badP,"badQ",badQ,"badR",badR)
