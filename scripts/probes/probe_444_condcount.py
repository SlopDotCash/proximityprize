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
def listsize(n,p,D,k,s):
    elts=subgroup(n,p); u=[(pow(x,D,p)+1)%p for x in elts]; seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[u[i] for i in T]; c=interp(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==u[i])
        if ag>=s: seen.add(c)
    return len(seen)
print("### CONDITION-COUNT c=D-k vs LIST SIZE vs norm-ceiling p<=D^(n/2c)  (n=32,k=2; budget qeps*~n=32) ###",flush=True)
n=32; k=2
p=None
from math import comb
for D in [4,6,8,12,16,24]:
    s=D  # agreement = D (all roots of f-u in mu_n)
    c=D-k
    # window prime ~ n^4
    pp=None
    base=n**4 - (n**4)%n +1
    q=base
    while True:
        if isprime(q) and (q-1)%n==0 and (q-1)//n>=2: pp=q; break
        q+=n
    L=listsize(n,pp,D,k,s)
    ceil=D**(n/(2*c)) if c>0 else float('inf')
    print(f"   D={D:2d} c={c:2d} s={s:2d}: list={L:4d}  norm-ceiling p<=D^(n/2c)={ceil:.3g}  (prize p~2^158; clean iff p>ceiling: {'CLEAN' if 2**158>ceil else 'WALL(vacuous)'})",flush=True)
