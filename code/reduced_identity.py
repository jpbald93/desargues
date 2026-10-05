import random
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def br(u,v,w): return dot(u,cross(v,w))
def rnd(n=5):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(4242)
f1=f2=f3=f4=0
for _ in range(3000):
    a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    # form check
    if P != tuple(br(a,b,bp)*x - br(a,b,ap)*y for x,y in zip(ap,bp)): f1+=1
    if Q != tuple(br(b,c,cp)*x - br(b,c,bp)*y for x,y in zip(bp,cp)): f2+=1
    if R != tuple(br(c,a,ap)*x - br(c,a,cp)*y for x,y in zip(cp,ap)): f3+=1
    p1,p2=br(a,b,bp),-br(a,b,ap); q1,q2=br(b,c,cp),-br(b,c,bp); r1,r2=br(c,a,ap),-br(c,a,cp)
    lhs=br(P,Q,R); rhs=(p1*q1*r1+p2*q2*r2)*br(ap,bp,cp)
    if lhs!=rhs: f4+=1
print("P form fails",f1,"Q",f2,"R",f3,"det-expansion fails",f4)
# and the reduced algebraic identity:
f5=0
for _ in range(2000):
    a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
    p1,p2=br(a,b,bp),-br(a,b,ap); q1,q2=br(b,c,cp),-br(b,c,bp); r1,r2=br(c,a,ap),-br(c,a,cp)
    if p1*q1*r1+p2*q2*r2 != br(a,b,c)*br(cross(a,ap),cross(b,bp),cross(c,cp)): f5+=1
print("reduced identity fails",f5)
