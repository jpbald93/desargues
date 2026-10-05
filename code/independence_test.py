import random
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def br(u,v,w): return dot(u,cross(v,w))
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def sub(u,v): return tuple(x-y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)
def rnd(n=5):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(2026)

# T1: br-hypothesis form WITHOUT independence hypotheses:
# for each pair (X,X'): if X x O != 0 pick X' in span{X,O}; else X' arbitrary.
bad=0; ex=None; tested=0
for _ in range(200000):
    O=rnd(); A=rnd(); B=rnd(); C=rnd()
    def pick(X):
        c=cross(X,O)
        if c!=(0,0,0):
            return add(smul(random.randint(-4,4),X), smul(random.randint(-4,4),O))
        return rnd(4)
    Ap=pick(A); Bp=pick(B); Cp=pick(C)
    if Ap==(0,0,0) or Bp==(0,0,0) or Cp==(0,0,0): continue
    assert br(O,A,Ap)==0 and br(O,B,Bp)==0 and br(O,C,Cp)==0
    P=cross(cross(A,B),cross(Ap,Bp)); Q=cross(cross(B,C),cross(Bp,Cp)); R=cross(cross(C,A),cross(Cp,Ap))
    tested+=1
    if br(P,Q,R)!=0:
        bad+=1
        if ex is None: ex=(O,A,B,C,Ap,Bp,Cp,br(P,Q,R), cross(O,A)==(0,0,0), cross(O,B)==(0,0,0), cross(O,C)==(0,0,0))
print("T1 br-hyp form (no independence): tested",tested,"counterexamples",bad)
if ex: print("  example:",ex)

# T2: same but require all three O x X != 0 (should be 0 counterexamples)
bad=0; tested=0
for _ in range(100000):
    O=rnd(); A=rnd(); B=rnd(); C=rnd()
    if cross(O,A)==(0,0,0) or cross(O,B)==(0,0,0) or cross(O,C)==(0,0,0): continue
    Ap=add(smul(random.randint(-4,4),A),smul(random.randint(-4,4),O))
    Bp=add(smul(random.randint(-4,4),B),smul(random.randint(-4,4),O))
    Cp=add(smul(random.randint(-4,4),C),smul(random.randint(-4,4),O))
    P=cross(cross(A,B),cross(Ap,Bp)); Q=cross(cross(B,C),cross(Bp,Cp)); R=cross(cross(C,A),cross(Cp,Ap))
    tested+=1
    if br(P,Q,R)!=0: bad+=1
print("T2 with independence: tested",tested,"counterexamples",bad)
