import random
from fractions import Fraction as F
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def det3(u,v,w): return u[0]*(v[1]*w[2]-v[2]*w[1]) - u[1]*(v[0]*w[2]-v[2]*w[0]) + u[2]*(v[0]*w[1]-v[1]*w[0])
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)
def rnd(n=5):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(23)
bad=0; tested=0; ex=None
for _ in range(200000):
    a,b,c,ap,bp=rnd(),rnd(),rnd(),rnd(),rnd()
    if det3(a,b,c)==0 or det3(ap,bp,c) is None: pass
    if det3(a,b,c)==0: continue
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,None if False else 1)) if False else None
    Q=cross(cross(b,c),cross(bp,None)) if False else None
    # need cp; we construct it below, so recompute
    l=cross(P,cross(a,b))  # placeholder
    # line l through P and Q requires Q; instead pick cp via construction:
    # l = P x Q; but Q depends on cp. Use different approach: choose l through P and a random direction, then solve.
    l=rnd()  # arbitrary line l through P? we need P on l: choose l with P in it: l = P x m for random m
    m=rnd()
    l=cross(P,m)
    if l==(0,0,0): continue
    R0=cross(l,cross(c,a))
    if R0==(0,0,0): continue
    cp=add(smul(random.randint(1,4),ap), smul(random.randint(1,4),R0))
    Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    if P==(0,0,0) or Q==(0,0,0) or R==(0,0,0): continue
    if det3(P,Q,R)!=0: continue
    if det3(ap,bp,cp)==0: continue   # triangle A'B'C' nondegenerate
    if det3(cross(a,ap),cross(b,bp),cross(c,cp))==0: continue  # already concurrent -> skip
    # also require nondegeneracy: P,Q distinct as points
    if cross(P,Q)==(0,0,0): continue
    tested+=1
    bad+=1
    if ex is None: ex=(a,b,c,ap,bp,cp,P,Q,R)
print("constructed non-perspective collinear configs (nondegen):",bad,"of",tested)
if ex: print("example:",ex)
