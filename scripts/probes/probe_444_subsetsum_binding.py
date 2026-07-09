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
# direction x^{k+1} + gamma*x^k, s=k+1 agreement, c=1. bad gamma: exists (k+1)-subset T where
# x^{k+1}+gamma*x^k interpolated by deg<k poly => order-(k+1) divided difference of (x^{k+1}+gamma x^k) on T = 0.
# DD_{k+1}(f) = leading coeff of interp of f on T (k+1 pts) for the deg-k interpolant... = coefficient.
# Actually: f on k+1 points has a unique deg<=k interpolant; it's deg<k iff the X^k coeff = 0.
# X^k coeff of interp of f on T(size k+1) = sum_t f(t)/prod_{u!=t}(t-u) = DD. Set = 0 => gamma = -DD(x^{k+1})/DD(x^k).
def bad_gammas(n,p,k):
    elts=subgroup(n,p); bad=set()
    for T in itertools.combinations(elts,k+1):
        # DD of x^{k+1} and x^k on T
        dd_a=0; dd_b=0
        for t in T:
            den=1
            for u in T:
                if u!=t: den=(den*((t-u)%p))%p
            inv=pow(den,p-2,p)
            dd_a=(dd_a + pow(t,k+1,p)*inv)%p
            dd_b=(dd_b + pow(t,k,p)*inv)%p
        if dd_b!=0:
            bad.add((-dd_a*pow(dd_b,p-2,p))%p)
        # dd_b==0 => no finite gamma (degenerate); skip
    return len(bad)
def distinct_sums(n,p,k):
    elts=subgroup(n,p)
    return len(set(sum(T)%p for T in itertools.combinations(elts,k+1)))
print("### CHECK: #bad-gamma (x^{k+1}+g x^k, c=1) =?= #distinct (k+1)-subset sums of mu_n ###",flush=True)
for n in [16]:
    for k in [2,3,4]:
        for p in [find_p for find_p in [65537]]:
            bg=bad_gammas(n,p,k); ds=distinct_sums(n,p,k)
            print(f"  n={n} k={k} p={p}: #bad-gamma={bg}  #distinct-(k+1)-sums={ds}  match={bg==ds}  budget=n={n}",flush=True)
