import itertools
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
    return e
def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r
def interp_coeffs(xs,ys,p):
    m=len(xs); c=[0]*m
    for i in range(m):
        num=[1]; den=1
        for j in range(m):
            if j==i: continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=(den*((xs[i]-xs[j])%p))%p
        sc=(ys[i]*pow(den,p-2,p))%p
        for t in range(len(num)): c[t]=(c[t]+sc*num[t])%p
    return c
# binding x^a+g x^b, find the bad T (size s) and check antipodal symmetry
n=16; p=find_p(n); k=4; a,b=9,7; c=3; s=k+c
elts=subgroup(n,p); neg={x:(p-x)%p for x in elts}
sym=0; nonsym=0; bad_gammas=set()
for T in itertools.combinations(elts,s):
    ca=interp_coeffs(list(T),[pow(t,a,p) for t in T],p)
    cb=interp_coeffs(list(T),[pow(t,b,p) for t in T],p)
    gam=None; ok=True
    for j in range(k,s):
        if cb[j]%p!=0:
            gj=(-ca[j]*pow(cb[j],p-2,p))%p
            if gam is None: gam=gj
            elif gam!=gj: ok=False; break
        elif ca[j]%p!=0: ok=False; break
    if ok and gam is not None and gam!=0:
        bad_gammas.add(gam)
        Ts=set(T); is_sym=all(neg[x] in Ts for x in T)
        if is_sym: sym+=1
        else: nonsym+=1
print(f"### Binding x^{a}+g*x^{b} (n={n},k={k},c={c},s={s}): bad-T symmetry ###",flush=True)
print(f"  nonzero-bad-T: antipodal-SYMMETRIC={sym}, NON-symmetric={nonsym}",flush=True)
print(f"  #distinct nonzero bad-gamma={len(bad_gammas)} (= n/2 * O_P; O_P={len(bad_gammas)//(n//2)})",flush=True)
print(f"  => bad T are {'ALL NON-symmetric (single-fibre descent needed)' if sym==0 else 'mixed/symmetric'}",flush=True)
