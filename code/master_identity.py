import random
from fractions import Fraction as F
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def br(u,v,w): return dot(u,cross(v,w))
def add(u,v): return tuple(x+y for x,y in zip(u,v))
def smul(s,u): return tuple(s*x for x in u)
def rnd(n=5):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(777)
fails=0; tested=0
for _ in range(4000):
    a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    lhs=br(P,Q,R)
    rhs=br(a,b,c)*br(ap,bp,cp)*br(cross(a,ap),cross(b,bp),cross(c,cp))
    tested+=1
    if lhs!=rhs: fails+=1
print("master identity fails",fails,"/",tested)
# concurrency vanishing for concurrent lines through O
fails=0
for _ in range(3000):
    O=rnd(); A=rnd(); B=rnd(); C=rnd()
    if br(cross(A,O),cross(B,O),cross(C,O))!=0: fails+=1
print("concurrent-lines vanishing fails",fails,"/3000")
# parametrized: A'=al A+be O etc.
fails=0
for _ in range(3000):
    O,A,B,C=rnd(),rnd(),rnd(),rnd()
    al,be,ga,de,ep,ze=[random.randint(-4,4) for _ in range(6)]
    Ap=add(smul(al,A),smul(be,O)); Bp=add(smul(ga,B),smul(de,O)); Cp=add(smul(ep,C),smul(ze,O))
    P=cross(cross(A,B),cross(Ap,Bp)); Q=cross(cross(B,C),cross(Bp,Cp)); R=cross(cross(C,A),cross(Cp,Ap))
    if br(P,Q,R)!=0: fails+=1
print("param form fails",fails,"/3000")
# P lies in span{A,B}: br(P, A, B) == 0 ?
fails=0
for _ in range(2000):
    O,A,B,C=rnd(),rnd(),rnd(),rnd()
    al,be,ga,de,ep,ze=[random.randint(-4,4) for _ in range(6)]
    Ap=add(smul(al,A),smul(be,O)); Bp=add(smul(ga,B),smul(de,O)); Cp=add(smul(ep,C),smul(ze,O))
    P=cross(cross(A,B),cross(Ap,Bp)); Q=cross(cross(B,C),cross(Bp,Cp)); R=cross(cross(C,A),cross(Cp,Ap))
    if br(P,A,B)!=0 or br(Q,B,C)!=0 or br(R,C,A)!=0: fails+=1
print("P in span{A,B} fails",fails,"/2000")
