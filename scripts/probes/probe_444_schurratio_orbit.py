import itertools, math
from sympy import primitive_root
def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e,g,z
def bad_gammas(n,p,a,b,k):
    # direction x^a + gamma x^b, agreement s=k+1 (c=1): gamma = -DD(x^a)/DD(x^b) over (k+1)-subsets
    elts,_,_=subgroup(n,p); bad=set()
    for T in itertools.combinations(elts,k+1):
        da=db=0
        for t in T:
            den=1
            for u in T:
                if u!=t: den=(den*((t-u)%p))%p
            inv=pow(den,p-2,p)
            da=(da+pow(t,a,p)*inv)%p; db=(db+pow(t,b,p)*inv)%p
        if db!=0: bad.add((-da*pow(db,p-2,p))%p)
    return bad
def count_orbits(n,p,bad,absorb):
    # dilation orbit: gamma ~ z^{a-b} * gamma where z generates mu_n; orbit size = n/gcd(a-b,n)
    elts,g,z=subgroup(n,p); mul=pow(z,absorb%n,p)
    seen=set(); norb=0
    for gam in bad:
        if gam in seen: continue
        norb+=1; cur=gam
        while cur not in seen:
            seen.add(cur); cur=(cur*mul)%p
    return norb
print("### ORBIT DECOMP: #bad-gamma = #orbits * (n/gcd(a-b,n))?  (Schur-ratio dilation eigenvalue g^{a-b}) ###",flush=True)
n=16; p=65537; k=2
for (a,b) in [(3,2),(5,3),(6,4),(9,7),(9,1)]:
    d=math.gcd(abs(a-b),n); orbsize=n//d
    bad=bad_gammas(n,p,a,b,k); nb=len(bad)
    norb=count_orbits(n,p,bad,a-b)
    print(f"  dir x^{a}+g*x^{b}: a-b={a-b} d=gcd={d} orbit-size={orbsize}: #bad={nb}  #orbits={norb}  check {nb}=={norb}*{orbsize}? {nb==norb*orbsize}",flush=True)
