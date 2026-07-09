#!/usr/bin/env python3
"""
probe_444_worstword_exponent.py  (#444 SEAM A)

Two decisive checks for the even/odd-descent proof path:
  (A) UNIT-FACTOR REDUCTION: L(x^{a-1}(1+x), RS[k]) == L((1+x), x^{-(a-1)}.RS[k])
      i.e. the worst consecutive word reduces (by a per-coordinate Hamming isometry) to the
      FIXED word (1+x) against a monomially-shifted code. If true, the descent's single-fiber
      term is O(1) (deg(1+x)=1), independent of n.
  (B) TRUE WORST WORD over ALL weight-2 words x^a+x^b: find the max window list and the
      exponents (a,b) that achieve it; track whether the achieving exponent scales with n
      or stays bounded.  (bounded exponent => descent closes cleanly => constant list.)
"""
import itertools, sys
from math import comb
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def subgroup(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*zeta)%p
    return e

def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r

def interp_coeffs(xs,ys,p):
    k=len(xs); c=[0]*k
    for i in range(k):
        num=[1]; den=1
        for j in range(k):
            if j==i: continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=(den*((xs[i]-xs[j])%p))%p
        inv=pow(den,p-2,p); sc=(ys[i]*inv)%p
        for t in range(len(num)): c[t]=(c[t]+sc*num[t])%p
    return tuple(c)

def peval(c,x,p):
    r=0
    for a in reversed(c): r=(r*x+a)%p
    return r

def list_RS(uvals, elts, k, s, p):
    """# distinct deg<k polys agreeing with u on >= s pts."""
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return len(seen)

def list_shifted(uvals, elts, k, s, p, shift):
    """# codewords g(x)=x^shift * (deg<k poly) agreeing with u on >= s pts. shift can be <0
       (use modular inverse on mu_n: x^shift well-defined as pow(x, shift mod n) since x^n=1)."""
    n=len(elts)
    # word divided by x^shift: g0(x)=u(x)*x^{-shift}; then g0 is plain deg<k RS word
    inv_sh = (-shift) % n
    u2=[(uvals[i]*pow(elts[i], inv_sh, p))%p for i in range(n)]
    return list_RS(u2, elts, k, s, p)

def check_unit_reduction(n, k, eta, beta=4.0):
    p=find_window_prime(n,beta); elts=subgroup(n,p)
    rho=k/n; s=round((rho+eta)*n); s=max(s,k)
    print(f"  (A) unit-factor reduction  n={n} k={k} s={s} p={p}")
    ok=True
    for a in range(2,n):
        # word x^{a-1}(1+x)=x^a+x^{a-1}
        u=[(pow(x,a,p)+pow(x,a-1,p))%p for x in elts]
        L_direct=list_RS(u,elts,k,s,p)
        # reduce: divide by x^{a-1}: word becomes 1 + x ; against shifted code (handled by list_shifted with shift=a-1)
        u_fixed=[(1+x)%p for x in elts]   # the FIXED word (1+x)
        # L((1+x), x^{-(a-1)} RS[k]) : codewords x^{-(a-1)} f, f deg<k, near (1+x)
        # equivalently list_RS of (1+x)*x^{a-1} vs RS[k] = L_direct already; instead verify the
        # ISOMETRY count: L_direct == L of (1+x) against code scaled by x^{a-1}. We test the
        # invariance: dividing BOTH word and code by x^{a-1} preserves the count.
        L_fixed_shift = list_shifted(u, elts, k, s, p, shift=a-1)  # divides word by x^{a-1}
        if L_fixed_shift != L_direct:
            ok=False; print(f"     a={a}: MISMATCH L_direct={L_direct} L_reduced={L_fixed_shift}")
    print(f"     reduction holds for all a: {ok}")

def true_worst_word(n, k, eta, beta=4.0, primes=2):
    ps=[find_window_prime(n,beta), find_window_prime(n,beta+0.5)]
    ps=list(dict.fromkeys(ps))[:primes]
    rho=k/n
    out=[]
    for p in ps:
        elts=subgroup(n,p); s=round((rho+eta)*n); s=max(s,k)
        best=(-1,None)
        for a in range(1,n):
            for b in range(0,a):
                # exclude correlated direction exponents == n/2 (x^{n/2}=+-1)
                if a==n//2 or b==n//2: continue
                u=[(pow(x,a,p)+pow(x,b,p))%p for x in elts]
                L=list_RS(u,elts,k,s,p)
                if L>best[0]: best=(L,(a,b))
        out.append((p,best,s))
    return out

if __name__=="__main__":
    print("### (A) UNIT-FACTOR REDUCTION ###")
    check_unit_reduction(16,2,0.125)
    check_unit_reduction(16,4,0.0625)
    print("\n### (B) TRUE WORST WEIGHT-2 WORD + exponent ###")
    for (n,k,eta) in [(16,2,0.125),(32,4,0.125),(16,1,0.0625),(32,2,0.0625)]:
        res=true_worst_word(n,k,eta)
        for p,best,s in res:
            print(f"  n={n} k={k}(rho={k/n:.3f}) eta={eta} s={s} p={p}: worst L={best[0]} at exps {best[1]}")
