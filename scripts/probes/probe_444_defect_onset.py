import itertools
from sympy import isprime, primitive_root
def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e
def elem_sym(roots,p,upto):
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]
def count_defects(n,p):
    elts=subgroup(n,p); sz=n//4; tcap=n//8
    g=primitive_root(p); mu4=set(pow(g,(p-1)//4*i,p) for i in range(4))
    # binomial cosets: root-sets of x^{n/4}=c, c in mu4
    cosets=set()
    for c in mu4:
        rs=frozenset(x for x in elts if pow(x,sz,p)==c)
        if len(rs)==sz: cosets.add(rs)
    total=0; defects=0; defex=None
    for T in itertools.combinations(elts,sz):
        if all(e==0 for e in elem_sym(T,p,tcap)):
            total+=1
            if frozenset(T) not in cosets:
                defects+=1
                if defex is None: defex=T
    return total,len(cosets),defects,defex
print("### DEFECT ONSET (n=16): non-coset T (size 4, e1=e2=0 mod p) — bound says only p<=n^4/256=256 ###",flush=True)
n=16; bound=n**4//256
print(f"   predicted defect ceiling p <= {bound}",flush=True)
cnt=0
for p in range(17, 1200):
    if p%n==1 and isprime(p):
        tot,nc,dc,ex=count_defects(n,p)
        flag = "  <-- DEFECT" if dc>0 else ""
        print(f"   p={p:5d} ({'<=bound' if p<=bound else '>bound '}): total_lacunary={tot} cosets={nc} DEFECTS={dc}{flag}",flush=True)
        cnt+=1
        if cnt>=20: break
