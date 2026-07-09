#!/usr/bin/env python3
"""
probe_444_defect_witness_inspect.py  (#444 Verify-2, witness inspection)

Inspect the actual defect witnesses found, to classify them:
  - Is T antipodal (T = -T)?  (the EXCLUDED correlated x^{n/2}=+-1 case)
  - Is T a union of cosets / a coset of a sub-subgroup?  (structured, not a 'true' Lam-Leung defect)
  - What is the actual char-0 sum beta_T = sum_{x in T} zeta^idx(x)?  (=0 over C => coset by Lam-Leung;
    !=0 over C => the genuine non-coset defect the Action-Orbit bound addresses)
The Action-Orbit norm argument applies to T with beta_T != 0 over C (genuine non-coset). A T that is
antipodal or has beta_T=0 over C is NOT a counterexample to the ceiling.
"""
import itertools, cmath, math
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def subgroup_idx(n,p):
    """Return list of (value, index) for mu_n: value=zeta^i, index=i."""
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    out=[]; x=1
    for i in range(n): out.append((x,i)); x=(x*zeta)%p
    return out

def elem_sym(roots,p,upto):
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]

def beta_char0(idxs, n):
    """beta_T = sum over T of exp(2pi i * idx / n)  (the char-0 root-of-unity sum)."""
    z = 2j*math.pi/n
    return sum(cmath.exp(z*i) for i in idxs)

def classify(n, p, s, c):
    elts=subgroup_idx(n,p)
    val=[v for v,_ in elts]; idx={v:i for v,i in elts}
    found=[]
    for T in itertools.combinations(val, s):
        if all(e==0 for e in elem_sym(T,p,c)):
            Tidx=[idx[x] for x in T]
            antipodal = all(((i+n//2)%n) in set(Tidx) for i in Tidx)  # T = -T means idx+n/2 also in T
            b0 = beta_char0(Tidx, n)
            # is it a single coset of mu_s? (binomial)
            is_coset=False
            if n % s == 0:
                vals=set(pow(x,s,p) for x in T)
                if len(vals)==1:
                    cst=vals.pop()
                    full=[x for x in val if pow(x,s,p)==cst]
                    if len(full)==s and set(full)==set(T): is_coset=True
            found.append((sorted(Tidx), antipodal, abs(b0), is_coset))
    return found

if __name__=="__main__":
    cases = [(16,8,2),(16,8,3),(24,6,2),(24,7,2),(24,8,2),(24,8,3),(24,9,2)]
    for (n,s,c) in cases:
        p=find_window_prime(n,4.0)
        fs=classify(n,p,s,c)
        print(f"=== n={n} p={p} s={s} c={c}:  {len(fs)} lacunary subset(s) ===", flush=True)
        for Tidx, antip, absb0, iscos in fs:
            kind = "COSET" if iscos else ("ANTIPODAL(T=-T)" if antip else "NON-COSET-genuine?")
            print(f"   idx={Tidx}  antipodal={antip}  |beta_T(char0)|={absb0:.4f}  coset={iscos}  -> {kind}", flush=True)
        print(flush=True)
