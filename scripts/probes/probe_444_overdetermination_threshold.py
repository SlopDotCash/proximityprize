# Test 5 fresh closed-intent conjectures for the floor (defect bound), with full confidence.
import itertools, cmath, math
from sympy import isprime, primitive_root, totient
def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e
def esym(roots,p,upto):
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]

print("=== C-NEW-1: defect count = 0 when c >= s/2 (over-determined kills it)? ===",flush=True)
# Conjecture: if the number of vanishing conditions c >= s/2, NO non-coset defect exists (the system
# is so over-determined that only cosets survive even mod p). If true + c=eta*n >= s/2=(rho+eta)n/2
# i.e. eta >= rho (achievable in window for rho<=eta), this would bound the floor for eta>=rho.
n=32
for p in [97,193,257,449,641]:
    if (p-1)%n: continue
    elts=subgroup(n,p)
    for sz in [6,8]:
        for c in [sz//2, sz//2+1, sz-1]:
            g=primitive_root(p); 
            # cosets
            cos=set()
            for d in set(pow(x,sz,p) for x in elts):
                rs=frozenset(x for x in elts if pow(x,sz,p)==d)
                if len(rs)==sz: cos.add(rs)
            defects=sum(1 for T in itertools.combinations(elts,sz)
                        if all(v==0 for v in esym(T,p,c)) and frozenset(T) not in cos)
            print(f"  p={p} s={sz} c={c} (c/s={c/sz:.2f}): defects={defects}",flush=True)
    break
