import itertools
from sympy import isprime, primitive_root
from math import comb, sqrt
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
def Lword(elts,k,s,p,exps,coeffs=None):
    n=len(elts)
    if coeffs is None: coeffs=[1]*len(exps)
    u=[sum(coeffs[i]*pow(x,exps[i],p) for i in range(len(exps)))%p for x in elts]
    seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[u[i] for i in T]; c=interp(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==u[i])
        if ag>=s: seen.add(c)
    return len(seen)
def worst_Lstar(n,k,s,p):
    elts=subgroup(n,p); best=0; bw=None
    # scan all weight-2 words (the proven worst family); skip correlated n/2
    for a in range(1,n):
        for b in range(0,a):
            if a==n//2 or b==n//2: continue
            L=Lword(elts,k,s,p,(a,b))
            if L>best: best=L; bw=(a,b)
    return best,bw
def find_p(n,beta=4.0):
    t=int(n**beta); base=t-(t%n)+1; p=base
    while True:
        if isprime(p) and (p-1)%n==0 and (p-1)//n>=2: return p
        p+=n
print("### COMPLETE L*(n,rho,eta) TABLE — hunting for an exact closed-form law ###",flush=True)
print(" n  rho     k   eta     s   c=s-k  L*   word     | 1/eta  2^(c0/eta)? log2(L*)/(1/eta)",flush=True)
for n in [16,32]:
    p=find_p(n)
    for rho in [0.25,0.125,0.0625]:
        k=max(1,round(rho*n))
        if comb(n,k)>4_000_000: continue
        # sweep eta over the window interior
        import math
        johnson_eta = math.sqrt(rho)-rho
        for eta in [round(0.5*johnson_eta,4), round(0.75*johnson_eta,4), round(0.9*johnson_eta,4)]:
            s=round((rho+eta)*n); s=max(s,k+1)
            if s>n: continue
            c=s-k
            L,w=worst_Lstar(n,k,s,p)
            l2 = (math.log2(L)/(1/eta)) if L>1 and eta>0 else 0
            print(f"{n:3d} {rho:.4f}  {k:2d}  {eta:.4f}  {s:3d}  {c:3d}   {L:3d}  x^{w[0] if w else '-'}+x^{w[1] if w else '-'}   | {1/eta:.2f}  {l2:.3f}",flush=True)
