import sys
p=int(sys.argv[1]); N=int(sys.argv[2]); mode=sys.argv[3]; path=sys.argv[4]
c=2
while pow(c,(p-1)//2,p)!=p-1: c+=1
zeta=pow(c,(p-1)//N,p); pts=[pow(zeta,i,p) for i in range(N)]
def ev(S,x):
    a=1
    for s in S: a=a*(x-pts[s])%p
    return a
def poly(S):
    co=[1]
    for s in S:
        n=[0]*(len(co)+1)
        for i,a in enumerate(co):
            n[i+1]=(n[i+1]+a)%p; n[i]=(n[i]-a*pts[s])%p
        co=n
    return co
def collinear(a,b,c):
    u=[(x-y)%p for x,y in zip(a,b)]; v=[(x-y)%p for x,y in zip(c,b)]
    i=next((i for i,x in enumerate(u) if x),None)
    if i is None or v[i]==0: return False
    f=v[i]*pow(u[i],p-2,p)%p
    return all((x*f-y)%p==0 for x,y in zip(u,v))
bits=lambda m:[i for i in range(N) if m>>i&1]
sym=lambda S: all((x+N//2)%N in S for x in S)
nh=0; good=[]
for line in open(path):
    if not line.startswith("HIT"): continue
    nh+=1
    f=line.split(); T,A,C=[bits(int(x[2:],16)) for x in f[1:4]]
    r=[ev(A,pts[t])*pow(ev(C,pts[t]),p-2,p)%p for t in T]
    if len(set(r))!=1: continue
    if mode=="pencil" and not collinear(poly(A),poly(T),poly(C)): continue
    good.append((T,A,C))
print(f"{path}: fingerprint hits {nh}, exact {mode} solutions {len(good)}")
print("all A and C antipodally symmetric:", all(sym(set(A)) and sym(set(C)) for _,A,C in good))
for g in good[:40]: print(" ",g)
