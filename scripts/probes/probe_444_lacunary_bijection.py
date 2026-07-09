#!/usr/bin/env python3
"""
probe_444_lacunary_bijection.py  (#444 SEAM A, list-decoding side)

ADVERSARIAL VERIFICATION of the capstone claim (even monomial-plus-constant word u = x^a + 1,
a even, a|n clean case, binding radius s = gcd(a,n) = a):

  - deg<k window-list members  <->  lacunary subsets T of mu_n with |T|=a and the prefix of
    elementary symmetric functions vanishing (the precise prefix depends on k; see below);
  - member is CONSTANT  <=>  T is a mu_d-coset (d=gcd(a,n)=a);
  - a NON-CONSTANT member EXISTS  <=>  a NON-COSET lacunary subset (char-p DEFECT) EXISTS;
  - hence "L = n/a exactly (only constants)"  <=>  "defect = 0".

For k=2 (linear) f=alpha*x+beta:  f agrees with x^a+1 on T (|T|=a)  <=>
   prod_{t in T}(x-t) = x^a - alpha*x + (1-beta),
i.e. coeff(x^j)=0 for 2<=j<=a-1  (lacunary: e_1=..=e_{a-2}=0), and
     alpha = -coeff(x^1),  beta = 1 - coeff(x^0).
Non-constant <=> alpha != 0 <=> coeff(x^1)!=0 <=> e_{a-1}(T) != 0  (defect signature).

For general deg<k member f, agreement of degree-(k-1) poly with x^a+1 on the full set T (|T|=a):
   x^a + 1 - f(x) = prod_{t in T}(x - t) * (unit)   [both sides monic deg a, when k-1 < a]
   so   prod_{t in T}(x-t) = x^a - (f(x) - 1).
   Since deg f <= k-1 < a, this forces coeff(x^j)=0 for k <= j <= a-1 (lacunary prefix
   e_1..e_{a-k}=0), and the low coeffs x^0..x^{k-1} encode f. CONSTANT member = deg-0 f = beta,
   which forces coeff(x^j)=0 for 1<=j<=a-1, i.e. e_1=..=e_{a-1}=0 (T is a mu_a-coset).

Run: python3 scripts/probes/probe_444_lacunary_bijection.py
"""
import itertools, sys
from sympy import isprime, primitive_root

# ----- reused decoder primitives (verbatim from probe_444_worstword_exponent.py) -----
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

def list_RS_members(uvals, elts, k, s, p):
    """Return the FULL set of distinct deg<k coeff-tuples agreeing with u on >= s pts."""
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return seen

# ----- prod_{t in T}(x - t) coefficients (low->high) -----
def prod_coeffs(subset_vals, p):
    poly=[1]
    for t in subset_vals:
        poly = poly_mul(poly, [(-t)%p, 1], p)   # (x - t)
    return poly   # poly[i] = coeff of x^i, length m+1, poly[m]=1

def is_coset_idx(subset_idx, n, d):
    """subset (indices into the cyclic subgroup) is a multiplicative coset of the order-d
       subgroup mu_d iff it equals {i0 + (n/d)*j mod n : j} for some i0."""
    step=n//d; s=set(subset_idx)
    if len(s)!=d: return False
    for i0 in range(n):
        if set((i0+step*j)%n for j in range(d))==s: return True
    return False

# ============================================================================================
# TASK 1: coefficient-matching algebra, k=2 (linear), a=n/4, several n  (DIRECT, member-driven)
# ============================================================================================
def task1(ns=(16,32,64,128)):
    print("="*100); print("TASK 1: k=2 coeff-matching algebra, u=x^a+1, a=n/4, binding s=a")
    print("="*100)
    allok=True
    for n in ns:
        a=n//4; k=2; s=a; p=find_window_prime(n); elts=subgroup(n,p)
        uvals=[(pow(x,a,p)+1)%p for x in elts]
        members=list_RS_members(uvals,elts,k,s,p)
        nbad=0
        for c in members:   # c=(beta,alpha) low->high, deg<2
            beta,alpha = (c+(0,0))[0],(c+(0,0))[1]
            Tidx=[i for i in range(n) if peval(c,elts[i],p)==uvals[i]]
            if len(Tidx)!=a:           # binding radius is exactly a here
                # member agrees on != a pts; allowed if >a? For a|n & u=x^a+1, agreement is exactly a.
                nbad+=1; allok=False
                print(f"   n={n}: member c={c} agrees on {len(Tidx)} != a={a}")
                continue
            Tvals=[elts[i] for i in Tidx]
            poly=prod_coeffs(Tvals,p)   # prod (x-t), len a+1
            # claim: poly == x^a - alpha x + (1-beta)
            target=[0]*(a+1); target[a]=1; target[1]=(-alpha)%p; target[0]=(1-beta)%p
            if poly!=target:
                nbad+=1; allok=False
                print(f"   n={n}: ALGEBRA FAIL c={c} poly={poly} target={target}")
            # lacunary prefix e_1..e_{a-2}=0 <=> coeff x^2..x^{a-1}=0
            lac=all(poly[j]==0 for j in range(2,a))
            if not lac:
                nbad+=1; allok=False
                print(f"   n={n}: non-lacunary T for member c={c} poly={poly}")
        nconst=sum(1 for c in members if (c+(0,0))[1]==0)
        print(f"  n={n} a={a} p={p}: |window-list|={len(members)}  #const(alpha=0)={nconst} "
              f"#nonconst={len(members)-nconst}  algebra_ok={'YES' if nbad==0 else 'NO'}")
    print(f"  TASK1 overall: {'HOLDS' if allok else 'FAILED'}\n")
    return allok

# ============================================================================================
# Independent lacunary-subset enumerator (size a, vanishing symmetric prefix) for k=2.
#   k=2 lacunary condition: coeff(x^j)=0 for 2<=j<=a-1 of prod_{t in T}(x-t).
# For n=16 (a=4) brute C(16,4)=1820 trivial. For n=32 (a=8) C(32,8)=10.5M too slow in Python,
# so we enumerate by an incremental prefix-pruned DFS on the partial product coefficients.
# ============================================================================================
def enum_lacunary_k2(n, a, elts, p):
    """All size-a subsets T (as sorted index tuples) of mu_n whose prod(x-t) has zero coeffs
       at x^2..x^{a-1}.  Prefix-pruned DFS: build prod incrementally; once the product has degree
       m, its coeffs x^2..x^{m-1} are fixed for the FINAL deg-a poly ONLY in the sense that adding
       more linear factors changes higher coeffs but the constraint set spans the middle — so we
       cannot prune purely on partial coeffs in general. We therefore prune by symmetry (fix the
       smallest index to 0..n/a-1 reps is NOT valid since condition isn't dilation-only). Use
       full combinations for a<=4; meet-in-the-middle for larger a."""
    res=[]
    if a<=5:
        for Tidx in itertools.combinations(range(n),a):
            poly=prod_coeffs([elts[i] for i in Tidx],p)
            if all(poly[j]==0 for j in range(2,a)):
                res.append(Tidx)
        return res
    # meet-in-the-middle for a in {6,8,...}: not needed for our n in {16,32}? n=32 -> a=8.
    # We'll implement a generic but pruned DFS using the fact that the FULL set of constraints is
    # symmetric; enumerate combinations but with an early multiply-and-store. Still O(C(n,a)) worst.
    # For n=32,a=8 we instead use a smarter route in task2 (see enum_lacunary_via_resultant).
    raise NotImplementedError

if __name__=="__main__":
    task1()
