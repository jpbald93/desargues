import random
from fractions import Fraction as F

def cross(u,v):
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def det3(u,v,w):
    return u[0]*(v[1]*w[2]-v[2]*w[1]) - u[1]*(v[0]*w[2]-v[2]*w[0]) + u[2]*(v[0]*w[1]-v[1]*w[0])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def sub(u,v): return tuple(x-y for x,y in zip(u,v))
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)
def smul3(s,u): return tuple(s*x for x in u)
def rnd(n=6): 
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u

random.seed(11)

# (A) identity: cross (cross u v) (cross w z) = det3 u v z * w - det3 u v w * z
bad=0
for _ in range(2000):
    u,v,w,z=[rnd() for _ in range(4)]
    lhs=cross(cross(u,v),cross(w,z))
    rhs=sub(smul(det3(u,v,z),w), smul(det3(u,v,w),z))
    if lhs!=rhs: bad+=1
print("A cross_cross identity fails:",bad,"/2000")

# (B) direct theorem after substitution a'=al*a+oa*o etc, ALL degeneracies allowed (a=b, c=0? no nonzero)
bad=0; zero=0
for _ in range(4000):
    o,a,b,c=[rnd() for _ in range(4)]
    al,be,ga,de,ep,ze=[random.randint(-4,4) for _ in range(6)]
    ap=add(smul(al,a),smul(be,o)); bp=add(smul(ga,b),smul(de,o)); cp=add(smul(ep,c),smul(ze,o))
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    if det3(P,Q,R)!=0: bad+=1
print("B substituted identity fails (all degeneracies):",bad,"/4000")

# (C) direct statement w/ hypotheses hoa/hob/hoc (cross o a != 0 etc) - random search for counterexample
bad=0; tried=0
for _ in range(40000):
    o,a,b,c=[rnd(4) for _ in range(4)]
    if cross(o,a)==(0,0,0) or cross(o,b)==(0,0,0) or cross(o,c)==(0,0,0): continue
    if det3(a,b,c)==0: pass  # allow degenerate triangle
    # pick a' in span{o,a} with random coeffs
    ap=add(smul(random.randint(-4,4),a),smul(random.randint(-4,4),o))
    bp=add(smul(random.randint(-4,4),b),smul(random.randint(-4,4),o))
    cp=add(smul(random.randint(-4,4),c),smul(random.randint(-4,4),o))
    tried+=1
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    if det3(P,Q,R)!=0: bad+=1
print("C direct hyp-version fails:",bad,"/",tried)

# (D) show hypothesis "cross o a != 0" is needed: find config w/ cross o a = 0 and det!=0
found=0
for _ in range(200000):
    o,a,b,c=[rnd(4) for _ in range(4)]
    if cross(o,a)!=(0,0,0): continue
    # a parallel o; then det3 o a a' = 0 for all a'
    ap,bp,cp=[rnd(3) for _ in range(3)]
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    if det3(P,Q,R)!=0:
        found+=1
        if found==1: print("D counterexample w/ a||o:",o,a,b,c,ap,bp,cp,det3(P,Q,R))
    if found>=3: break
print("D degenerate-a counterexamples found:",found)

# (E) converse check: build configs with P,Q,R collinear generically
# construction: choose a,b,c,a',b',o; P=(a x b) x (a' x b'); Q=(b x c) x (b' x c'); then solve for c' with R=(c x a) x (c' x a') || P x Q
def solve_cp(a,b,c,ap,bp,o):
    # random b' first
    P=cross(cross(a,b),cross(ap,bp))
    # need c' : R=(c x a) x (c' x a') in span{P}
    # pick random c'
    for _ in range(200):
        cp=rnd(4)
        Q=cross(cross(b,c),cross(bp,cp))
        return P,Q
    return None
# simpler: use duality identity directly: hypothesis det(P,Q,R)=0 with O*=PxQ, config (O*, A*=bxc, ...) satisfies direct hypotheses automatically
tested=0; bad=0
for _ in range(3000):
    a,b,c,ap,bp,cp=[rnd(4) for _ in range(6)]
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    if det3(P,Q,R)!=0: continue   # only collinear cases (rare)
    tested+=1
    if det3(cross(a,ap),cross(b,bp),cross(c,cp))!=0: bad+=1
print("E converse (random collinear hits):",tested,"bad:",bad)

# (F) converse via dual construction: pick a,b,c,ap,bp,cp AND force det(P,Q,R)=0 by replacing cp? 
# Instead: verify the dual-substitution claim numerically at the identity level:
# det3 (cross(c,cp) ) (cross(a,ap)) (cross(b,bp)) == det3 of direct-theorem-output with dual inputs, up to nonzero scalars
bad=0
for _ in range(2000):
    o_,a_,b_,c_,ap_,bp_,cp_= [rnd(4) for _ in range(7)]
    # treat (P,Q,R) = (o_ cross a_, ...)? simpler: check the algebra identity
    # cross (cross (bxc) (cxa)) (cross (b'xc') (c'xa')) = (det3 b c a * det3 b' c' a') * cross c c'
    lhs=cross(cross(cross(b_,c_),cross(c_,a_)),cross(cross(bp_,cp_),cross(cp_,ap_)))
    rhs=smul(det3(b_,c_,a_)*det3(bp_,cp_,ap_), cross(c_,cp_))
    if lhs!=rhs: bad+=1
print("F dual-side identity fails:",bad,"/2000")

# also: cross (cross (axb) (bxc)) (cross (a'xb') (b'xc')) = ... * cross b b' ?
bad=0
for _ in range(1000):
    a_,b_,c_,ap_,bp_,cp_=[rnd(4) for _ in range(6)]
    lhs=cross(cross(cross(a_,b_),cross(b_,c_)),cross(cross(ap_,bp_),cross(bp_,cp_)))
    rhs=smul(det3(a_,b_,c_)*det3(ap_,bp_,cp_), cross(b_,bp_))
    if lhs!=rhs: bad+=1
print("F2 fails:",bad,"/1000")
