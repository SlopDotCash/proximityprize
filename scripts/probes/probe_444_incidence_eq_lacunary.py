import itertools
from sympy import isprime, primitive_root
def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e
def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r
def interp(xs,ys,p):
    k=len(xs); c=[0]*k
    for i in range(k):
        num=[1]; den=1
        for j in range(k):
            if j==i: continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=(den*((xs[i]-xs[j])%p))%p
        sc=(ys[i]*pow(den,p-2,p))%p
        for t in range(len(num)): c[t]=(c[t]+sc*num[t])%p
    return tuple(c)
def peval(c,x,p):
    r=0
    for a in reversed(c): r=(r*x+a)%p
    return r
def esym(roots,p,upto):
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]
# Compare: (A) far-line incidence #bad-gamma for word x^a (direction x^a + gamma), vs (B) lacunary count
# #{size-s subsets S: first c=s-k power sums vanish}.  Claim: bad-gamma involves the SAME conditions.
def badgamma(n,p,a,k,s):
    elts=subgroup(n,p)
    bad=set()
    # for each size-s subset S, x^a interpolated by deg<k poly? then gamma determined
    for S in itertools.combinations(range(n),s):
        xs=[elts[i] for i in S]; ys=[pow(elts[i],a,p) for i in S]
        # interpolant of x^a on S (deg < s); check if it's actually deg < k (top coeffs zero)
        c=interp(xs,ys,p)
        if all(c[j]==0 for j in range(k,len(c))):  # deg < k
            # gamma: word x^a+gamma agrees with codeword (interpolant)+gamma... gamma is free; the agreement
            # is on S regardless of gamma (shift). bad gamma exists. Count distinct interp (codewords).
            bad.add(c[:k])
    return len(bad)
def lacunary(n,p,s,c):
    elts=subgroup(n,p)
    return sum(1 for S in itertools.combinations(range(n),s) if all(v==0 for v in esym([elts[i] for i in S],p,c)))
print("### R-a CHECK: bad-gamma (x^a direction) =?= lacunary count (c=s-k)  [a=s] ###",flush=True)
for n in [16]:
    p=65537; 
    for (k,s) in [(2,4),(2,5),(4,6),(4,7)]:
        a=s  # a=s case
        bg=badgamma(n,p,a,k,s)
        lac=lacunary(n,p,s,s-k)
        print(f"  n={n} a={a} k={k} s={s} c={s-k}: bad-gamma(distinct codewords)={bg}  lacunary(c=s-k)={lac}  match={bg==lac}",flush=True)
