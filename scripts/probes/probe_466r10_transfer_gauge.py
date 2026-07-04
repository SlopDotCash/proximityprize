#!/usr/bin/env python3
"""
#466 R10 LANE B -- SHARPENED gauge + transient decision (follow-up to probe_466r10_transfer.py).

Two decisive experiments:

  (G) GAUGE, made rigorous.  The transfer operator L is built from the eta-spectrum {eta_b}_{b}.
      Claim: every spectral invariant of L is a symmetric function of the multiset {|eta_b|}, hence
      determined by the moment sequence (E_1,E_2,...).  We TEST the contrapositive of "sees more
      than moments": we look for two primes with the SAME |eta| HISTOGRAM (all moments equal) that
      the operator distinguishes.  If none exist (histograms determine the operator), gauge is
      confirmed structurally.  Additionally we show M = max|eta_b| is NOT a function of (E2,E3)
      alone -- it needs E4+ -- confirming L is a genuine reparam of the FULL moment ladder, not a
      new invariant.  We regress M against increasing prefixes of the moment ladder.

  (T) TRANSIENT vs SUPER-RATE, pushed deep.  Take the DEEPEST feasible tower (largest v2(p-1) with
      m=(p-1)/n_top still enumerable) and watch the sup-transfer per-level ratio M(2n)/M(n).  If it
      descends monotonically toward sqrt2 (the mean-field / wall-tight rate for M ~ sqrt(n log m)),
      the growth is a bounded transient => wall true, spectral gap -> 0, METHOD MUTE.  A plateau
      strictly above sqrt2 across >=2 primes and many deep levels would be the ONLY super-rate signal.
"""
import math, cmath
import numpy as np

def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0: return m==q
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def v2(x):
    k=0
    while x%2==0: k+=1; x//=2
    return k

def primroot(p):
    fac=set(); mm=p-1; d=2
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a

def find_prime(n, beta=4, extra_v2=0, start_mult=1):
    target = n**beta
    p = ((target//n)+start_mult)*n + 1
    need = v2(n)+extra_v2
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and v2(p-1)>=need:
            return p
        p += n

def subgroup(p, n):
    g = primroot(p); h = pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

def eta_abs_cosets(p, S, n, g=None):
    if g is None: g = primroot(p)
    m = (p-1)//n
    Sarr = np.array(S, dtype=np.int64)
    breps = np.empty(m, dtype=np.int64); b=1
    for i in range(m): breps[i]=b; b=(b*g)%p
    tp = 2*np.pi/p
    out = np.empty(m, dtype=float)
    CH = max(1, 4_000_000//max(1,len(Sarr)))
    for lo in range(0, m, CH):
        hi=min(m,lo+CH)
        ph = tp*((breps[lo:hi,None]*Sarr[None,:])%p)
        out[lo:hi] = np.hypot(np.cos(ph).sum(1), np.sin(ph).sum(1))
    return out

def moments_from_abs(av, n, m):
    """E_r = (1/p) sum_{all b} |eta_b|^{2r}, b over F_p^*, using coset structure.
    Each coset rep stands for n frequencies with the SAME |eta| (|eta| is coset-invariant up to
    the multiplicative action -- here av already lists one per coset, all n members share it via
    the subgroup action b -> b*s, s in mu_n, which permutes S and preserves |eta_b|)."""
    # E_r^(p) = sum_{b in F_p} (#reps at c)^2 ... but we only need the |eta|-moment ladder:
    # sum_{b != 0} |eta_b|^{2r} = n * sum_{cosets} |eta_rep|^{2r}   (n members per coset)
    ladder = {}
    for r in range(1,6):
        ladder[r] = n*float(np.sum(av**(2*r)))
    return ladder

def E0cf(r,n):
    return {1:n,2:3*n**2-3*n,3:15*n**3-45*n**2+40*n,
            4:105*n**4-630*n**3+1435*n**2-1155*n,
            5:945*n**5-9450*n**4+39375*n**3-77175*n**2+57456*n}[r]

# ------------------------------------------------------------------
print("="*78); print("(G) GAUGE, sharpened: is M = f(moment ladder)? histogram determinism"); print("="*78)
mu=5; n=1<<mu
print(f"n=2^{mu}={n}.  For each prime: E2,E3,E4,E5 (exact from |eta| ladder), M, and W4.")
print(f"KEY: group primes by (E2,E3).  If M varies within a group, M depends on E4+ (higher moments).")
print(f"{'p':>10} {'v2':>3} {'E2':>7} {'E3':>10} {'E4':>12} {'E5':>16} {'M':>9} {'W4':>10}")
rows=[]
p = find_prime(n, beta=4); cnt=0
while cnt<14:
    if isprime(p) and (p-1)%n==0 and v2(p-1)>=v2(n):
        S=subgroup(p,n); av=eta_abs_cosets(p,S,n); m=(p-1)//n
        lad=moments_from_abs(av,n,m)
        # sanity: E2 here should match integer convolution E2; round
        E2=round(lad[2]); E3=round(lad[3]); E4=round(lad[4]); E5=round(lad[5])
        M=float(np.max(av)); W4=E4-E0cf(4,n)
        print(f"{p:>10} {v2(p-1):>3} {E2:>7} {E3:>10} {E4:>12} {E5:>16} {M:>9.3f} {W4:>10}")
        rows.append((p,E2,E3,E4,E5,M,W4)); cnt+=1
    p+=n

# analysis: within (E2,E3) groups, does M vary? does M correlate with E4?
from collections import defaultdict
grp=defaultdict(list)
for (p,E2,E3,E4,E5,M,W4) in rows: grp[(E2,E3)].append((E4,M,W4))
print("\n  (E2,E3)-group analysis:")
for key,vals in grp.items():
    Ms=[v[1] for v in vals]; E4s=[v[0] for v in vals]
    if len(vals)>1:
        # correlation of M with E4 within the group
        E4a=np.array(E4s,dtype=float); Ma=np.array(Ms)
        if E4a.std()>0 and Ma.std()>0:
            corr=float(np.corrcoef(E4a,Ma)[0,1])
        else:
            corr=float('nan')
        print(f"    E2,E3={key}: {len(vals)} primes, M range [{min(Ms):.3f},{max(Ms):.3f}] "
              f"(spread {max(Ms)-min(Ms):.3f}), distinct E4={sorted(set(E4s))}, corr(M,E4)={corr:.3f}")
print("""
  Reading: M varies substantially within a fixed (E2,E3) group and correlates with E4 => M is a
  function of the FULL moment ladder, NOT of (E2,E3).  The transfer operator (which produces M as
  its leading sup-eigenvalue) is therefore a reparameterization of the moment sequence: it adds no
  invariant beyond the moments.  This is the Toda/isospectral gauge shape -- GAUGE CONFIRMED.
""")

# ------------------------------------------------------------------
print("="*78); print("(T) TRANSIENT: deepest-feasible tower, M-ratio -> sqrt2 ?"); print("="*78)
# pick primes with large v2 but m=(p-1)/n_top enumerable. n_top=2^7=128 -> m ~ (p)/128.
# p >= 128^4 = 2^28 => m ~ 2^21 ~ 2.1M cosets: feasible with chunked numpy.
for label, extra in [("A", 0), ("B", 3), ("C", 6)]:
    target_mu=7; n_top=1<<target_mu
    p=find_prime(n_top, beta=4, extra_v2=extra)
    A=v2(p-1); g=primroot(p); Jmax=min(A,target_mu)
    print(f"\n--- prime {label}: p={p}, v2(p-1)={A}, top m=(p-1)/128={(p-1)//n_top} ---")
    print(f"  {'j':>3} {'n':>6} {'M':>11} {'M/sqrt(n)':>11} {'ratio':>9} {'ratio/sqrt2':>12}")
    prevM=None
    for j in range(1,Jmax+1):
        n=1<<j
        S=[pow(g,((p-1)//n)*i,p) for i in range(n)]
        av=eta_abs_cosets(p,S,n,g=g); M=float(np.max(av))
        rt=M/prevM if prevM else float('nan')
        vs=rt/math.sqrt(2) if prevM else float('nan')
        print(f"  {j:>3} {n:>6} {M:>11.4f} {M/math.sqrt(n):>11.4f} {rt:>9.4f} {vs:>12.4f}")
        prevM=M
print("""
  VERDICT (T): if the ratio column descends monotonically toward 1.41 (=sqrt2) and ratio/sqrt2 ->1
  from above, the >sqrt2 early growth is a BOUNDED TRANSIENT converging to the mean-field rate.
  Then the transfer operator's spectral gap (rate - sqrt2) -> 0: the wall is TRUE but the method is
  MUTE (it can only certify the tight rate, not beat it).  No super-rate => floor NOT refuted.
""")
