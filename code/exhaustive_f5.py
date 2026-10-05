import itertools, random
p=5
def cross(u,v): return ((u[1]*v[2]-u[2]*v[1])%p,(u[2]*v[0]-u[0]*v[2])%p,(u[0]*v[1]-u[1]*v[0])%p)
def dot(u,v): return (u[0]*v[0]+u[1]*v[1]+u[2]*v[2])%p
def br(u,v,w): return dot(u,cross(v,w))
vecs=[v for v in itertools.product(range(p),repeat=3) if v!=(0,0,0)]
random.seed(4)
def test_configs(sampler):
    bad=0; tested=0; ex=None
    for _ in range(sampler):
        O,A,B,C,A2,B2=[random.choice(vecs) for _ in range(6)]
        # require br(O,A,A2)=0 and br(O,B,B2)=0 else skip
        if br(O,A,A2)!=0 or br(O,B,B2)!=0: continue
        for C2 in vecs:
            if br(O,C,C2)!=0: continue
            P=cross(cross(A,B),cross(A2,B2)); Q=cross(cross(B,C),cross(B2,C2)); R=cross(cross(C,A),cross(C2,A2))
            tested+=1
            if br(P,Q,R)!=0:
                bad+=1
                if ex is None: ex=(O,A,B,C,A2,B2,C2,P,Q,R)
    return tested,bad,ex

for name,trials in [("F5 random",300),("F5 more",1500)]:
    t,b,ex=test_configs(trials)
    print(name,"tested",t,"counterexamples",b, "ex", ex)
