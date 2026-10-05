import random
from fractions import Fraction as F
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def br(u,v,w): return dot(u,cross(v,w))
def matvec(M,v): return tuple(sum(M[i][j]*v[j] for j in range(3)) for i in range(3))
def det3m(M): return M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])-M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])+M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0])
def inv(M):
    d=det3m(M)
    c=[[ (M[(j+1)%3][(i+1)%3]*M[(j+2)%3][(i+2)%3]-M[(j+1)%3][(i+2)%3]*M[(j+2)%3][(i+1)%3]) for j in range(3)] for i in range(3)]
    # adjugate transpose = cofactor matrix; inverse = adj/d
    return [[F(c[i][j],d) for j in range(3)] for i in range(3)]
def rnd(n=4):
    while True:
        u=tuple(random.randint(-n,n) for _ in range(3))
        if u!=(0,0,0): return u
random.seed(3)
G=[[1,2,0],[0,1,3],[2,0,1]]
dG=det3m(G)
for trial in range(3):
    a,b,c,ap,bp,cp=[rnd() for _ in range(6)]
    P=cross(cross(a,b),cross(ap,bp)); Q=cross(cross(b,c),cross(bp,cp)); R=cross(cross(c,a),cross(cp,ap))
    l1=cross(a,ap); l2=cross(b,bp); l3=cross(c,cp)
    X=br(P,Q,R); Y=br(a,b,c)*br(ap,bp,cp)*br(l1,l2,l3)
    print("identity holds:", X==Y, "X nonzero:", X!=0)
    ga,gb,gc,gap,gbp,gcp=[matvec(G,v) for v in (a,b,c,ap,bp,cp)]
    P2=cross(cross(ga,gb),cross(gap,gbp)); Q2=cross(cross(gb,gc),cross(gbp,gcp)); R2=cross(cross(gc,ga),cross(gcp,gap))
    L2=cross(ga,gap); L22=cross(gb,gbp); L23=cross(gc,gcp)
    X2=br(P2,Q2,R2); Y2=br(ga,gb,gc)*br(gap,gbp,gcp)*br(L2,L22,L23)
    wp4=tuple(dG**4 * z for z in P)   # placeholder
    print("identity holds after g:", X2==Y2)
    print("X2/(det^4 X) =", F(X2, dG**4 * X) if X else None, "  Y2/(det^6 Y) =", F(Y2, dG**6 * Y) if Y else None)
