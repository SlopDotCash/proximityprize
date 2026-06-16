import itertools
from sympy import isprime, primitive_root
from math import comb
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
print("### DEFECT COUNT vs RANDOM MODEL C(n,s)/p^c (does structure inflate above random?) ###",flush=True)
n=32
for (p,sz,c) in [(97,6,2),(97,8,2),(193,6,2),(257,8,2),(97,6,3),(193,8,3)]:
    if (p-1)%n: continue
    elts=subgroup(n,p)
    cnt=sum(1 for T in itertools.combinations(elts,sz) if all(v==0 for v in esym(T,p,c)))
    rand=comb(n,sz)/p**c
    print(f"  n={n} p={p} s={sz} c={c}: actual={cnt}  random=C(n,s)/p^c={rand:.3g}  ratio={cnt/rand if rand>0 else float('inf'):.1f}x",flush=True)
