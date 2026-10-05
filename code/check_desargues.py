import random
from fractions import Fraction as F

def cross(u,v):
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def det(u,v,w):
    return u[0]*(v[1]*w[2]-v[2]*w[1]) - u[1]*(v[0]*w[2]-v[2]*w[0]) + u[2]*(v[0]*w[1]-v[1]*w[0])
def sub(u,v): return tuple(x-y for x,y in zip(u,v))
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)

def rnd():
    while True:
        u=tuple(random.randint(-6,6) for _ in range(3))
        if u!=(0,0,0): return u

def check(sep=False):
    # perspective config: A' = al*A + oa*O, etc.
    O=rnd()
    while True:
        A,B,C=rnd(),rnd(),rnd()
        if det(A,B,C)!=0: break
    al,be,ga=rnd()[0],rnd()[1],rnd()[2]
    oa,ob,oc=rnd()[0],rnd()[1],rnd()[2]
    if sep:
        A2,B2,C2=rnd(),rnd(),rnd()   # negative control: no perspective
    else:
        A2=add(smul(al,A),smul(oa,O))
        B2=add(smul(be,B),smul(ob,O))
        C2=add(smul(ga,C),smul(oc,O))
    x=cross(cross(A,B),cross(A2,B2))
    y=cross(cross(B,C),cross(B2,C2))
    z=cross(cross(C,A),cross(C2,A2))
    return det(x,y,z), (x,y,z)

random.seed(7)
good=0
for _ in range(3000):
    d,_=check(False)
    if d==0: good+=1
print("perspective: det==0 in", good, "/3000")
bad=0; nz=0
for _ in range(3000):
    d,p=check(True)
    if p[0]!=(0,0,0) and p[1]!=(0,0,0) and p[2]!=(0,0,0):
        nz+=1
        if d!=0: bad+=1
print("NEG CONTROL non-perspective: nonzero-genuine configs", nz, "of which det!=0:", bad)

# explicit non-vacuity example over Q
O=(0,0,1); A=(1,0,0); B=(0,1,0); C=(1,1,1)
A2=add(smul(2,A),smul(3,O)); B2=add(smul(5,B),smul(-1,O)); C2=add(smul(4,C),smul(7,O))
x=cross(cross(A,B),cross(A2,B2)); y=cross(cross(B,C),cross(B2,C2)); z=cross(cross(C,A),cross(C2,A2))
print("example O,A,B,C,A',B',C' =",O,A,B,C,A2,B2,C2)
print("x,y,z =",x,y,"\n",z,"det=",det(x,y,z))
