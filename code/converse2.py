import random, itertools
from fractions import Fraction as F
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def det3(u,v,w): return u[0]*(v[1]*w[2]-v[2]*w[1]) - u[1]*(v[0]*w[2]-v[2]*w[0]) + u[2]*(v[0]*w[1]-v[1]*w[0])
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)
def rnd(n=3):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(5)

def cfg():
    while True:
        a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
        if det3(a,b,c)!=0 and det3(ap,bp,cp)!=0: return a,b,c,ap,bp,cp

# 1) Test converse with strong hypotheses
ok=0; bad=0; bad_ex=None
for _ in range(200000):
    a,b,c,ap,bp,cp=cfg()
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    if P==(0,0,0) or Q==(0,0,0) or R==(0,0,0): continue
    if cross(P,Q)==(0,0,0) or cross(Q,R)==(0,0,0): continue   # P,Q,R distinct
    if det3(P,Q,R)!=0: continue
    conc=det3(cross(a,ap),cross(b,bp),cross(c,cp))
    n=len(str(conc))
    if conc==0: ok+=1
    else:
        bad+=1
        if bad_ex is None: bad_ex=(a,b,c,ap,bp,cp,P,Q,R,conc)
print("converse strong hyps: ok",ok,"bad",bad)
if bad_ex: print("bad example:",bad_ex)

# 2) relation between d1=det(AxA',BxB',CxC') and d2=detPQR
from math import prod
cnt=0
for _ in range(3000):
    a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
    if det3(a,b,c)==0 or det3(ap,bp,cp)==0: continue
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    d1=det3(cross(a,ap),cross(b,bp),cross(c,cp)); d2=det3(P,Q,R)
    if d1==0 or d2==0: continue
    cnt+=1
    if cnt<=6:
        print("d1",d1,"d2",d2,"detABC",det3(a,b,c),"detA'B'C'",det3(ap,bp,cp),"ratio d1/d2",F(d1,d2))
print("pairs with both nonzero:",cnt)
