import itertools, random
p=5
def cross(u,v): return ((u[1]*v[2]-u[2]*v[1])%p,(u[2]*v[0]-u[0]*v[2])%p,(u[0]*v[1]-u[1]*v[0])%p)
def dot(u,v): return (u[0]*v[0]+u[1]*v[1]+u[2]*v[2])%p
def br(u,v,w): return dot(u,cross(v,w))
def add(u,v): return tuple((x+y)%p for x,y in zip(u,v))
def smul(s,u): return tuple((s*x)%p for x in u)
vecs=[v for v in itertools.product(range(p),repeat=3) if v!=(0,0,0)]
random.seed(1234)

# Degenerate target: A x O = 0 (O,A same projective point or O on... ) with br conditions
print("--- degenerate A x O = 0 ---")
tested=0; bad=0; ex=None
for _ in range(400000):
    O=random.choice(vecs)
    A=random.choice([v for v in vecs if cross(v,O)==(0,0,0)])
    Ap=random.choice(vecs)          # br(O,A,Ap)=0 automatically
    B=random.choice(vecs)
    if cross(B,O)==(0,0,0):  continue
    gam,de=random.randrange(p),random.randrange(p)
    Bp=add(smul(gam,B),smul(de,O))
    C=random.choice(vecs)
    if cross(C,O)==(0,0,0): continue
    ep,ze=random.randrange(p),random.randrange(p)
    Cp=add(smul(ep,C),smul(ze,O))
    if Bp==(0,0,0) or Cp==(0,0,0): continue
    P=cross(cross(A,B),cross(Ap,Bp)); Q=cross(cross(B,C),cross(Bp,Cp)); R=cross(cross(C,A),cross(Cp,Ap))
    tested+=1
    if br(P,Q,R)!=0:
        bad+=1
        if ex is None: ex=(O,A,Ap,B,Bp,C,Cp,P,Q,R)
print("tested",tested,"counterexamples",bad, "ex",ex)

print("--- degenerate B x O = 0 only ---")
tested=0; bad=0; ex=None
for _ in range(300000):
    O=random.choice(vecs)
    A=random.choice(vecs)
    if cross(A,O)==(0,0,0): continue
    al,be=random.randrange(p),random.randrange(p)
    Ap=add(smul(al,A),smul(be,O))
    B=random.choice([v for v in vecs if cross(v,O)==(0,0,0)])
    Bp=random.choice(vecs)
    C=random.choice(vecs)
    if cross(C,O)==(0,0,0): continue
    ep,ze=random.randrange(p),random.randrange(p)
    Cp=add(smul(ep,C),smul(ze,O))
    if Ap==(0,0,0) or Bp==(0,0,0) or Cp==(0,0,0): continue
    P=cross(cross(A,B),cross(Ap,Bp)); Q=cross(cross(B,C),cross(Bp,Cp)); R=cross(cross(C,A),cross(Cp,Ap))
    tested+=1
    if br(P,Q,R)!=0:
        bad+=1
        if ex is None: ex=(O,A,Ap,B,Bp,C,Cp,P,Q,R)
print("tested",tested,"counterexamples",bad,"ex",ex)
