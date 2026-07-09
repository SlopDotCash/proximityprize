import itertools, math
from sympy import primitive_root, isprime
def find_p(n,beta=4.0):
    t=int(n**beta); p=t-(t%n)+1
    while True:
        if isprime(p) and (p-1)%n==0 and (p-1)//n>=2: return p
        p+=n
def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e,g,z
def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r
def interp_coeffs(xs,ys,p):
    # coefficients (low->high) of the deg<|xs| interpolant through (xs,ys)
    m=len(xs); c=[0]*m
    for i in range(m):
        num=[1]; den=1
        for j in range(m):
            if j==i: continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=(den*((xs[i]-xs[j])%p))%p
        sc=(ys[i]*pow(den,p-2,p))%p
        for t in range(len(num)): c[t]=(c[t]+sc*num[t])%p
    return c
def bad_gammas_deep(n,p,a,b,k,s):
    # direction x^a+gamma x^b; bad gamma <=> exists s-subset T with deg<k interp of (x^a+gamma x^b)|_T
    # interp coeffs are linear in gamma: c_a[t] + gamma*c_b[t]. Need coeffs[k..s-1]=0 (c=s-k conditions).
    elts,g,z=subgroup(n,p); bad=set()
    for T in itertools.combinations(elts,s):
        ca=interp_coeffs(list(T),[pow(t,a,p) for t in T],p)
        cb=interp_coeffs(list(T),[pow(t,b,p) for t in T],p)
        # solve c_a[j]+gamma c_b[j]=0 for j in k..s-1, consistent gamma
        gam=None; ok=True
        for j in range(k,s):
            if cb[j]%p!=0:
                gj=(-ca[j]*pow(cb[j],p-2,p))%p
                if gam is None: gam=gj
                elif gam!=gj: ok=False; break
            else:
                if ca[j]%p!=0: ok=False; break  # 0+gamma*0 != -ca[j]
        if ok and gam is not None: bad.add(gam)
    return bad
def orbit_ct(bad,n,p,absorb,g,z):
    mul=pow(z,absorb%n,p); seen=set(); no=0
    for gam in bad:
        if gam in seen or gam==0: continue
        no+=1; cur=gam
        while cur not in seen and cur!=0: seen.add(cur); cur=(cur*mul)%p
    return no
print("### O_P (gamma-orbits) at increasing agreement c for d=2 direction, find O_P=1 (n=16) ###",flush=True)
n=16; p=find_p(n); k=4; elts,g,z=subgroup(n,p)
for (a,b) in [(9,7),(11,9),(7,5)]:  # d=2 (a-b=2)
    print(f" direction x^{a}+g*x^{b} (d=2):",flush=True)
    for c in [1,2,3,4]:
        s=k+c
        if s>=n: break
        from math import comb
        if comb(n,s)>2_000_000: break
        bad=bad_gammas_deep(n,p,a,b,k,s)
        nz=sum(1 for x in bad if x!=0); has0=(0 in bad)
        no=orbit_ct(bad,n,p,a-b,g,z)
        tag=" <== O_P=1" if no==1 else ""
        print(f"   c={c} s={s} (delta={1-s/n:.3f}): #bad={len(bad)} (nz={nz},gamma0={has0}) O_P={no}{tag}",flush=True)
