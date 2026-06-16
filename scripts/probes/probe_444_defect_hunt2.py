#!/usr/bin/env python3
"""
probe_444_defect_hunt2.py  (#444 SEAM A, TASK 3 cont.)

Findings so far:
  - a=2: lacunary condition "coeff x^2..x^{a-1}=0" is EMPTY (range 2..1) so EVERY pair is "lacunary";
    112/120 are non-coset. The equivalence is non-vacuous but trivial there.
  - a=n/4=4 (n=16) and a=8: NO non-coset lacunary subset over hundreds of primes.

This script does two things:
  (1) VERIFY the bijection AT an a=2 defect prime (where non-constant members DO exist): confirm
      member<->lacunary bijection, const<->coset, #nonconst==#noncoset, L==n/a <=> defect0.
      This makes the equivalence non-vacuous: there IS a non-constant member and it DOES correspond
      to a non-coset lacunary subset.
  (2) HUNT HARD for a defect at a>=3 (a=4 various n; a=4 with index up to several thousand; a=3
      with n=12; a=4 n=16 sweeping 2000 primes) to determine whether defects at the *non-trivial*
      lacunary order are merely rare or provably absent in the clean a|n 2-power regime.
"""
import itertools
from sympy import isprime, primitive_root, nextprime

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

def list_RS_members(uvals, elts, k, s, p):
    n=len(elts); seen=set()
    for T in itertools.combinations(range(n),k):
        xs=[elts[i] for i in T]; ys=[uvals[i] for i in T]
        c=interp_coeffs(xs,ys,p)
        if c in seen: continue
        ag=sum(1 for i in range(n) if peval(c,elts[i],p)==uvals[i])
        if ag>=s: seen.add(c)
    return seen

def primes_idx(n, count, idx_min=2, pmin=0):
    out=[]; pp=n+1
    while len(out)<count:
        if pp>pmin and isprime(pp) and (pp-1)%n==0 and (pp-1)//n>=idx_min: out.append(pp)
        pp+=n
    return out

# ---- (1) Full bijection check at an a=2 defect prime ----
def full_bijection_check(n, a, p):
    """word u=x^a+1, k=2, binding s=a. Build members & lacunary independently; check everything.
       NOTE: at binding radius s=a, members may agree on MORE than a points only if a-subset roots
       coincide; for a|n & u=x^a+1 the constant members agree on exactly a. Non-constant members
       (if any) agree on exactly a too (their T is a size-a lacunary set). We set s=a."""
    elts=subgroup(n,p); k=2; s=a
    uvals=[(pow(x,a,p)+1)%p for x in elts]
    members=list_RS_members(uvals,elts,k,s,p)
    mem_T={}
    for c in members:
        mem_T[c]=tuple(sorted(i for i in range(n) if peval(c,elts[i],p)==uvals[i]))
    nconst=sum(1 for c in members if (c+(0,0))[1]==0)
    nnonconst=len(members)-nconst
    const_iff_coset=all((((c+(0,0))[1]==0)==is_coset_idx(mem_T[c],n,a)) for c in members)
    # independent lacunary (brute) -- size a with coeff x^2..x^{a-1}=0
    lac=[]
    for Tidx in itertools.combinations(range(n),a):
        poly=prod_coeffs([elts[i] for i in Tidx],p)
        if all(poly[j]==0 for j in range(2,a)): lac.append(tuple(sorted(Tidx)))
    lacset=set(lac); cosets=set();
    img={}
    for i,x in enumerate(elts): img.setdefault(pow(x,a,p),[]).append(i)
    cosets=set(tuple(sorted(v)) for v in img.values())
    lac_noncoset=[T for T in lac if T not in cosets]
    bij = set(mem_T.values())==lacset
    return dict(n=n,a=a,p=p,L=len(members),nconst=nconst,nnonconst=nnonconst,
                const_iff_coset=const_iff_coset,nlac=len(lac),
                nlac_noncoset=len(lac_noncoset),cosets=len(cosets),bijection=bij,
                nonconst_eq_noncoset=(nnonconst==len(lac_noncoset)),
                Leq=(len(members)==n//a),defect0=(len(lac_noncoset)==0),
                Leq_iff_def0=((len(members)==n//a)==(len(lac_noncoset)==0)))

# ---- (2) hard defect hunt at a>=3 via lacunary brute ----
def lac_noncoset_count(n, a, p):
    elts=subgroup(n,p)
    img={}
    for i,x in enumerate(elts): img.setdefault(pow(x,a,p),[]).append(i)
    cosets=set(tuple(sorted(v)) for v in img.values())
    cnt=0; ex=None
    for Tidx in itertools.combinations(range(n),a):
        poly=prod_coeffs([elts[i] for i in Tidx],p)
        if all(poly[j]==0 for j in range(2,a)):
            T=tuple(sorted(Tidx))
            if T not in cosets:
                cnt+=1
                if ex is None: ex=(T,poly)
    return cnt,ex

if __name__=="__main__":
    print("="*100)
    print("(1) NON-VACUOUS bijection check at a=2 DEFECT primes (n=8 a=2, n=16 a=2)")
    print("="*100)
    for (n,a) in [(8,2),(16,2)]:
        for p in primes_idx(n,4,idx_min=2,pmin=8):
            r=full_bijection_check(n,a,p)
            ok = r['bijection'] and r['const_iff_coset'] and r['nonconst_eq_noncoset'] and r['Leq_iff_def0']
            print(f"  n={n} a={a} p={p}: L={r['L']} nconst={r['nconst']} nnonconst={r['nnonconst']} "
                  f"nlac={r['nlac']} noncosetLac={r['nlac_noncoset']} bij={r['bijection']} "
                  f"const<=>coset={r['const_iff_coset']} nc==nclac={r['nonconst_eq_noncoset']} "
                  f"L=n/a:{r['Leq']} defect0:{r['defect0']} L<=>def0={r['Leq_iff_def0']} ALLOK={ok}")

    print("\n"+"="*100)
    print("(2) HARD defect hunt at NON-trivial lacunary order a>=3 (clean a|n)")
    print("="*100)
    # a=4 n=16 over 2000 primes (indices up to huge); a=4 n=32; a=3 n=12; a=4 n=20; a=4 n=24
    cases=[(16,4,300),(32,4,40),(12,3,300),(20,4,200),(24,4,150),(16,4,1)]  # last reuses below
    for (n,a,cnt) in [(16,4,400),(12,3,400),(20,4,150),(24,4,120),(28,4,120),(36,4,80)]:
        tot=0; firstex=None
        for p in primes_idx(n,cnt,idx_min=2,pmin=8):
            c,ex=lac_noncoset_count(n,a,p)
            tot+=c
            if c>0 and firstex is None: firstex=(p,ex)
        if tot==0:
            print(f"  n={n} a={a}: 0 non-coset lacunary over {cnt} primes (defect NEVER occurs).")
        else:
            print(f"  n={n} a={a}: TOTAL non-coset lacunary={tot}; FIRST defect at {firstex}")
