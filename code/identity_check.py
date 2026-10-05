import random
from fractions import Fraction as F
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def det3(u,v,w): return u[0]*(v[1]*w[2]-v[2]*w[1]) - u[1]*(v[0]*w[2]-v[2]*w[0]) + u[2]*(v[0]*w[1]-v[1]*w[0])
def br(u,v,w): return dot(u,cross(v,w))
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def sub(u,v): return tuple(x-y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)
def rnd(n=4):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(99)

fails={'I0':0,'I1':0,'I2':0,'I3':0,'I4':0}
N=1500
for _ in range(N):
    a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    l1=cross(a,ap); l2=cross(b,bp); l3=cross(c,cp)
    lhs=br(P,Q,R)
    rhs=br(a,b,c)*br(ap,bp,cp)*br(l1,l2,l3)
    if lhs!=rhs: fails['I1']+=1
    # I0: P = br(a,ap,bp)*b - br(b,ap,bp)*a
    if P!=sub(smul(br(a,ap,bp),b), smul(br(b,ap,bp),a)): fails['I0']+=1
    # I2: P = br(a,b,bp)*ap - br(a,b,ap)*bp
    if P!=sub(smul(br(a,b,bp),ap), smul(br(a,b,ap),bp)): fails['I2']+=1
    # I3: [PQR] = [abc]*( a1a2a3 + b1b2b3 ) with
    a1=br(a,ap,bp); b1=-br(b,ap,bp); a2=br(b,bp,cp); b2=-br(c,bp,cp); a3=br(c,cp,ap); b3=-br(a,cp,ap)
    if br(P,Q,R)!=br(a,b,c)*(a1*a2*a3+b1*b2*b3): fails['I3']+=1
    # I4: a1a2a3+b1b2b3 = [a'b'c']*[l1 l2 l3]
    if a1*a2*a3+b1*b2*b3 != br(ap,bp,cp)*br(l1,l2,l3): fails['I4']+=1
print("N=",N,"fails:",fails)
# extra: no division/neg issues, and check det3 sign for l's: br(l1,l2,l3) = det3(l1,l2,l3)
a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
print("sanity:", br(cross(a,ap),cross(b,bp),cross(c,cp))==det3(cross(a,ap),cross(b,bp),cross(c,cp)))
