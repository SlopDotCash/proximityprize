import math
def order(a,p):
    o=1; x=a%p
    while x!=1: x=x*a%p; o+=1
    return o
def run(n,p,K):
    # find subgroup of order n
    g=None
    for c in range(2,p):
        if order(c,p)==(p-1): g=c; break
    h=pow(g,(p-1)//n,p); H=[]
    x=1
    for _ in range(n): H.append(x); x=x*h%p
    arc=lambda v: K*v//p
    R={}
    for d in H:
        R[d]=sum(1 for v in range(1,p) if arc(d*v%p)==arc(v))
    # grand identity check on a few b
    tot=0
    for b in range(1,p):
        tot+=sum(1 for x in H for y in H if arc(b*x%p)==arc(b*y%p))
    lhs=tot; rhs=n*sum(R.values())
    print(f"n={n} p={p} K={K}: identity {lhs}=={rhs}: {lhs==rhs}; R(1)={R[1]} (p-1={p-1})")
    Rn1=[R[d] for d in H if d!=1]
    print(f"  R on mu_n\\1: max={max(Rn1)} mean={sum(Rn1)/len(Rn1):.1f} vs p/K={p/K:.1f}  max/[p/K]={max(Rn1)/(p/K):.2f}")
for (n,p,K) in [(8,257,8),(8,257,16),(16,257,8),(16,769,16),(32,1153,16)]:
    run(n,p,K)
