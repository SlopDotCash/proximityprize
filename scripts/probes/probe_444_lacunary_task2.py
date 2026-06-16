#!/usr/bin/env python3
"""
probe_444_lacunary_task2.py  (#444 SEAM A)  -- TASKS 2 & 3

Bijection + equivalence check for u=x^a+1, k=2, binding radius s=a, a=n/4.

Independent objects:
  MEMBERS  = window-list members (deg<2 polys agreeing with u on >= s pts), via the decoder.
  LACUNARY = size-a subsets T of mu_n with prod_{t in T}(x-t) = x^a - alpha x + c  (alpha,c in F_p),
             enumerated INDEPENDENTLY (not via members) by the two routes below.

Bijection map:  member f=alpha*x+beta  <->  T = agreement set {x: f(x)=u(x)}.
  CONSTANT member (alpha=0)  <->  T = {x : x^a = beta-1} = a mu_a-coset.
  NON-CONSTANT member        <->  T a NON-COSET lacunary subset (DEFECT).

Equivalence under test:  #non-constant-members == #non-coset-lacunary-subsets  (EXACTLY),
and  (L == n/a, only constants)  <=>  (no non-coset lacunary subset = defect 0).

Independent lacunary enumeration:
  Route C (constants / cosets): T_gamma = {x in mu_n : x^a = gamma} for gamma in mu_{n/a}.
    There are exactly n/a such cosets (gamma ranges over the image of x->x^a = mu_{n/a}).
  Route D (defects): brute over all size-a subsets for small (n=16); for n=32 use a pruned DFS that
    fixes one element index to 0 (every lacunary T can be multiplicatively rotated; but rotation
    does NOT preserve lacunarity in general, so we DON'T quotient -- we brute n=16 fully and for
    n=32 we enumerate the (alpha,c)-parametrization: a lacunary T is the root set of x^a-alpha x+c,
    so enumerate candidate (alpha,c) where ALL a roots lie in mu_n. We get candidate c from products
    of a-subsets is circular; instead: x^a-alpha x+c splits over mu_n  <=>  every root rho satisfies
    rho^a = alpha*rho - c AND rho^n = 1. Enumerate alpha in F_p is p-large. So for n=32 we BRUTE the
    members side fully (cheap) and CROSS-CHECK with route C for the constant count, and separately
    confirm task1 already proved the prod-coeff identity is exact, so members<->lacunary is a proven
    bijection; the only open numeric is whether DEFECT subsets exist => done by prime sweep in task3.
"""
import itertools, sys
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def all_window_primes(n, beta=4.0, idx_min=2, count=40):
    """First `count` prize-shaped primes p ~ n^beta with (p-1)/n >= idx_min."""
    target=int(n**beta); p=target-(target%n)+1; out=[]
    while len(out)<count:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: out.append(p)
        p+=n
    return out

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
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return seen

def prod_coeffs(subset_vals, p):
    poly=[1]
    for t in subset_vals: poly=poly_mul(poly,[(-t)%p,1],p)
    return poly

def is_coset_idx(subset_idx, n, d):
    step=n//d; s=set(subset_idx)
    if len(s)!=d: return False
    for i0 in range(n):
        if set((i0+step*j)%n for j in range(d))==s: return True
    return False

# ---- Independent lacunary enumeration ----
def cosets_route_C(n, a, elts, p):
    """T_gamma = {x in mu_n : x^a = gamma}, gamma in image(x->x^a)=mu_{n/a}. n/a cosets, each size a
       (since a|n). Returns list of sorted index-tuples."""
    img={}  # gamma -> list of indices x with x^a=gamma
    for i,x in enumerate(elts):
        g=pow(x,a,p); img.setdefault(g,[]).append(i)
    return [tuple(sorted(v)) for v in img.values()]

def lacunary_brute(n, a, elts, p):
    """ALL size-a subsets T with prod(x-t)=x^a - alpha x + c (coeff x^2..x^{a-1} = 0).
       Brute over C(n,a). Tractable for n=16 (a=4, 1820)."""
    res=[]
    for Tidx in itertools.combinations(range(n),a):
        poly=prod_coeffs([elts[i] for i in Tidx],p)
        if all(poly[j]==0 for j in range(2,a)):
            res.append(tuple(sorted(Tidx)))
    return res

def analyze_one(n, p, verbose=True, brute=False):
    """For word u=x^a+1 (a=n/4), k=2, s=a at prime p: window-list members, classification,
       coset counts. If brute, also independently enumerate lacunary subsets and check bijection."""
    a=n//4; k=2; s=a; elts=subgroup(n,p)
    uvals=[(pow(x,a,p)+1)%p for x in elts]
    members=list_RS_members(uvals,elts,k,s,p)
    # classify members
    mem_const=[]; mem_nonconst=[]; mem_T={}
    algebra_ok=True; bind_ok=True
    for c in members:
        beta,alpha=(c+(0,0))[0],(c+(0,0))[1]
        Tidx=tuple(sorted(i for i in range(n) if peval(c,elts[i],p)==uvals[i]))
        mem_T[c]=Tidx
        if len(Tidx)!=a: bind_ok=False
        poly=prod_coeffs([elts[i] for i in Tidx],p) if len(Tidx)==a else None
        if poly is not None:
            target=[0]*(a+1); target[a]=1; target[1]=(-alpha)%p; target[0]=(1-beta)%p
            if poly!=target: algebra_ok=False
        if alpha==0: mem_const.append(c)
        else: mem_nonconst.append(c)
    # T-side classification (coset vs non-coset) of the members' agreement sets
    nc_const=sum(1 for c in members if is_coset_idx(mem_T[c],n,a))
    # consistency: constant member <=> coset T ?
    const_iff_coset=all((((c+(0,0))[1]==0)==is_coset_idx(mem_T[c],n,a)) for c in members)
    row=dict(n=n,p=p,a=a,L=len(members),nconst=len(mem_const),nnonconst=len(mem_nonconst),
             ncosetT=nc_const,const_iff_coset=const_iff_coset,algebra_ok=algebra_ok,bind_ok=bind_ok)
    if brute:
        # independent enumeration
        lac=lacunary_brute(n,a,elts,p)
        cosets=set(cosets_route_C(n,a,elts,p))
        lac_coset=[T for T in lac if T in cosets]
        lac_noncoset=[T for T in lac if T not in cosets]
        # also cross-check route-C cosets really satisfy lacunary
        cosets_are_lac=all(all(prod_coeffs([elts[i] for i in T],p)[j]==0 for j in range(2,a))
                           for T in cosets)
        # bijection: set of member-agreement-sets == set of lacunary subsets ?
        memTset=set(mem_T.values())
        bij = (memTset==set(lac))
        row.update(dict(nlac=len(lac),nlac_coset=len(lac_coset),nlac_noncoset=len(lac_noncoset),
                        cosets_count=len(cosets),cosets_are_lac=cosets_are_lac,
                        bijection=bij,
                        nonconst_eq_noncoset=(len(mem_nonconst)==len(lac_noncoset)),
                        Leq_n_over_a_iff_defect0=((len(members)==n//a)==(len(lac_noncoset)==0))))
    return row

if __name__=="__main__":
    print("="*100); print("TASK 2: bijection + equivalence at n=16 (full brute lacunary)")
    print("="*100)
    for n in [16]:
        p=find_window_prime(n)
        r=analyze_one(n,p,brute=True)
        print(f"  n={n} p={p} a={r['a']}:")
        for kk in ['L','nconst','nnonconst','ncosetT','const_iff_coset','algebra_ok','bind_ok',
                   'nlac','nlac_coset','nlac_noncoset','cosets_count','cosets_are_lac',
                   'bijection','nonconst_eq_noncoset','Leq_n_over_a_iff_defect0']:
            print(f"      {kk:<26}= {r[kk]}")

    print("\n"+"="*100); print("TASK 2b: n=16 PRIME SWEEP (find any DEFECT prime) + bijection each")
    print("="*100)
    defects16=[]
    for p in all_window_primes(16, beta=4.0, count=60):
        r=analyze_one(16,p,brute=True)
        flag = "DEFECT" if r['nnonconst']>0 else ""
        ok = r['bijection'] and r['const_iff_coset'] and r['algebra_ok'] and r['bind_ok'] and \
             r['nonconst_eq_noncoset'] and r['Leq_n_over_a_iff_defect0'] and r['cosets_are_lac']
        if r['nnonconst']>0: defects16.append((p,r))
        print(f"  p={p:<10} L={r['L']:<3} nconst={r['nconst']:<3} nnonconst={r['nnonconst']:<3} "
              f"nlac={r['nlac']:<3} noncosetLac={r['nlac_noncoset']:<3} bij={r['bijection']} "
              f"nc==nclac={r['nonconst_eq_noncoset']} Leq<=>def0={r['Leq_n_over_a_iff_defect0']} "
              f"allOK={ok} {flag}")
    print(f"\n  n=16: #defect primes among 60 = {len(defects16)}")
