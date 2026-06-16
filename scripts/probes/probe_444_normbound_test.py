import itertools
from sympy import isprime, primitive_root
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
def cosets(n,p,sz):
    elts=subgroup(n,p); cs=set()
    for d in set(pow(x,sz,p) for x in elts):
        rs=frozenset(x for x in elts if pow(x,sz,p)==d)
        if len(rs)==sz: cs.add(rs)
    return cs
print("### NORM-BOUND DECISIVE TEST: do ALL defects satisfy p <= s^{n/(2c)} ? (violation => floor REFUTED) ###",flush=True)
# search n=32, sizes 6,8,10, c=2,3, over primes p=1 mod n, find max defect-prime vs ceiling s^{n/(2c)}
n=32
for sz in [6,8,10]:
    for c in [2,3]:
        ceil = sz**(n/(2*c))   # s^{n/(2c)}
        maxdef=0; ndef=0; violation=None
        p=33
        checked=0
        while p < min(ceil*4, 300000) and checked<60:
            if p%n==1 and isprime(p):
                checked+=1
                elts=subgroup(n,p); cos=cosets(n,p,sz)
                found=False
                # sample subsets (full enum if feasible)
                from math import comb
                if comb(n,sz)<=300000:
                    it=itertools.combinations(elts,sz)
                else:
                    import random; random.seed(p); it=(tuple(random.sample(elts,sz)) for _ in range(200000))
                for T in it:
                    if all(v==0 for v in esym(T,p,c)) and frozenset(T) not in cos:
                        found=True; break
                if found:
                    ndef+=1; maxdef=max(maxdef,p)
                    if p>ceil and violation is None: violation=p
            p+=n
        tag = f"  *** VIOLATION at p={violation} > ceil ***" if violation else ("  (no defect found)" if ndef==0 else "  OK (all defects <= ceil)")
        print(f"  sz={sz} c={c}: ceiling s^(n/2c)={ceil:.4g}  #defect-primes={ndef}  max-defect-prime={maxdef}{tag}",flush=True)
