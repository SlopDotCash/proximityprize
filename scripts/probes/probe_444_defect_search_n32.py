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
def defects(n,p,sz,c):
    elts=subgroup(n,p)
    g=primitive_root(p); mu_sz=set(pow(g,(p-1)//(n//sz)*i,p) for i in range(n//sz)) if False else None
    # cosets of mu_{sz}: root-sets of x^{sz}=d for d in mu_{n/sz}
    coset=set()
    for d in set(pow(x,sz,p) for x in elts):
        rs=frozenset(x for x in elts if pow(x,sz,p)==d)
        if len(rs)==sz: coset.add(rs)
    tot=0; dfc=0; ex=None
    for T in itertools.combinations(elts,sz):
        if all(v==0 for v in esym(T,p,c)):
            tot+=1
            if frozenset(T) not in coset:
                dfc+=1
                if ex is None: ex=T
    return tot,len(coset),dfc,ex
n=32; sz=4; c=2; ceil=sz**(n//(2*c))
print(f"### DEFECT SEARCH n={n} size={sz} c={c}: norm ceiling p<={ceil}. Do non-coset defects appear below it? ###",flush=True)
found_below=False; checked=0
for p in range(33, 70000):
    if p%n==1 and isprime(p):
        tot,nc,dfc,ex=defects(n,p,sz,c)
        rel = "<=ceil" if p<=ceil else ">ceil "
        if dfc>0 or p>ceil and dfc>0:
            print(f"   p={p:6d} ({rel}): lacunary={tot} cosets={nc} DEFECTS={dfc}  ex={ex}",flush=True)
        checked+=1
        if dfc>0 and p<=ceil: found_below=True
        # only print non-defect summary occasionally
        if checked%20==0 or (p>ceil and dfc==0):
            pass
        if p>ceil and checked>40: 
            print(f"   ...(checked {checked} primes up to {p}; defects-below-ceiling found: {found_below})",flush=True)
            break
