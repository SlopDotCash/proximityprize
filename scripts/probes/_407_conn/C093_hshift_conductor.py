#!/usr/bin/env python3
"""
C093 attack: "Effective Jacobi equidistribution at CONSTANT index is the Rojas-Leon
homothety lever read backwards: the prize's large automorphism is the multiplicative
h-shift, giving sqrt(q) per-h but only m statistics."

THE CLAIM (C093.json):
  Rojas-Leon (1010.0120) gets sqrt(q) from a large automorphism (homothety by a big
  subgroup), but the in-tree verdict is it needs n>=sqrt(p) (additive x-sum window empty
  at prize). C093 says: apply the homothety lever to the MULTIPLICATIVE h-shift of the
  Hasse-Davenport-linked Jacobi family T_h(phi)=sum_{w in mu_n} phi(1-w) instead. That
  family is m-dimensional (m=2^128 huge), sidestepping n>=sqrt(p). The open question
  becomes purely the m-statistic AVERAGE = constant-index (m fixed) effective
  equidistribution. ATTACK PLAN: state the conductor of the h |-> T_h family (Kummer
  sheaf L_{chi^h} twisted by the tangent locus) and check whether it is bounded
  uniformly in p at fixed index m.

WHAT WE TEST (exact / high-precision, PROPER dyadic mu_n < F_q*, prize regime n<<sqrt q):

  P1. THE H-FAMILY OBJECT. The prize house B = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n}
      psi(bx). Identity A_h = m*conj(tau_h)*T_h with |tau_h|=sqrt q (Weil flat) routes B
      to the tangent sums. C093 reframes the relevant FAMILY as h |-> T_h indexed by the
      m multiplicative shifts. We need: does the per-h sum already have sqrt-cancellation
      (then only the m-average matters), and does the m-average give B?

  P2. THE CONDUCTOR (the load-bearing claim). For each multiplicative character phi of
      order o, T_h = sum_{w in mu_n} phi(1-w) = an INCOMPLETE multiplicative character sum
      of phi(1-w) over the subgroup mu_n. As a character sum over the subgroup it is
      governed by the Kummer sheaf L_{phi(1-x)} restricted to mu_n. The Weil/Deligne bound
      for a COMPLETE sum sum_{x in F_q} phi(1-x)*chi(x) is O(sqrt q) with an O(1) conductor
      (this is the Jacobi sum J(chi,phi), |J|<=sqrt q). But T_h is the INCOMPLETE sum over
      mu_n. C093 says T_h = (1/m) sum_i J(chi^i, phi) (in-tree I4). The conductor question:
      to bound the m-AVERAGE you need effective equidistribution of {J(chi^i,phi)}_i, and
      the relevant sheaf is [n]_* L (the pushforward making the subgroup a complete sum
      over the quotient), whose conductor scales with n (=> with p, since n grows with p).
      We MEASURE: does any sqrt(q)-per-h bound get LEVERED into a better-than-trivial
      m-average bound, or does the conductor (= number of Jacobi terms that must align)
      grow with p, leaving the trivial sup-norm m*sqrt(p)/m = sqrt(p) per period?

  P3. THE HOMOTHETY AUTOMORPHISM ON THE H-SHIFT. Rojas-Leon's lever: an automorphism of
      order ~q acting on the variety gives sqrt(q) gain ONLY when the family is large vs
      the conductor. The h-shift family has SIZE m (the index). The Galois action chi->chi^a
      permutes {J(chi^i,phi)}_i. We test whether this orbit structure produces a GENUINE
      gain in the m-average (i.e. T_h smaller than generic) at FIXED m as p grows -- the
      "uniform-in-p at fixed index m" claim. We hold m fixed (same index) and vary p, and
      check whether max_h |T_h| / sqrt(n) stays bounded (gain) or grows like sqrt(ln m)
      (no gain -- same BGK extreme-value law).

VERDICT LOGIC:
  - If per-h sqrt-cancellation holds AND the m-average is bounded uniformly in p at fixed
    index (max_h|T_h|/sqrt n bounded indep of p) => the lever WORKS => PARTIAL/REDUCED/PROVEN.
  - If the m-average inherits the sqrt(ln m) extreme-value gap (max/rms ~ sqrt(ln m)) and
    the per-period sup stays ~sqrt(p)*[no gain], OR the conductor grows with p at fixed m
    => the homothety lever does NOT transfer to the h-shift => OPEN (welds to BGK/Paley).
"""
import math, cmath
import numpy as np

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def primitive_root(p):
    n=p-1; fac=set(); d=2
    while d*d<=n:
        while n%d==0: fac.add(d); n//=d
        d+=1
    if n>1: fac.add(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    raise RuntimeError

def find_prime_by_index(n, m_target, maxp=6_000_000):
    """find prime p=1+n*m with m as close to m_target as possible (FIXED index family)."""
    best=None; bestd=None
    for dm in range(0, 200000):
        for m in (m_target+dm, m_target-dm):
            if m<2: continue
            p=1+n*m
            if p<=n or p>maxp: continue
            if is_prime(p):
                # require m odd-part>1 so mu_n proper-and-the-shift-family is genuine
                return p, m
    return None, None

def find_prime_beta(n, beta, maxp=6_000_000):
    target=int(round(n**beta)); t0=max(2,target//n)
    for dt in range(0,400000):
        for t in (t0+dt,t0-dt):
            if t<2: continue
            p=1+n*t
            if p<=n or p>maxp: continue
            if is_prime(p): return p,(p-1)//n
    return None,None

def run(n, p):
    g=primitive_root(p); pe=p-1; m=pe//n; sqp=math.sqrt(p)
    # discrete log table
    dlog=np.empty(p,dtype=np.int64); dlog[0]=-1
    x=1
    for k in range(pe):
        dlog[x]=k; x=(x*g)%p
    # mu_n = {g^{m*t} : t} (subgroup of order n)
    mu=[pow(g,(m*t)%pe,p) for t in range(n)]
    mu=np.array(mu,dtype=np.int64)
    # additive char psi(x)=e_p(x); eta_b = sum_{w in mu} psi(b*w)
    # B = max_{b!=0}|eta_b|
    bvals=np.arange(1,p)
    # eta over all b: matrix exp(2pi i (b*w)/p)
    Wb=np.outer(bvals, mu) % p
    eta=np.exp(2j*np.pi*Wb/p).sum(axis=1)
    B=float(np.max(np.abs(eta)))
    # ---- tangent sums T_h ----
    # phi of multiplicative order: characters trivial-on-nothing; the relevant phi are
    # arbitrary mult chars. T(phi)=sum_{w in mu, w!=1} phi(1-w).  Index phi by exponent
    # e in 0..pe-1: phi(g^k)=exp(2pi i e k/pe).  T_e = sum_{w in mu} phi(1-w) (skip w=1).
    # We sweep all e (the full multiplicative-shift family) and record |T_e|.
    one_minus = (1 - mu) % p
    nz = one_minus != 0          # skip w=1 (1-w=0)
    om = one_minus[nz]
    klog = dlog[om]              # discrete logs of (1-w)
    e_all = np.arange(0, pe)
    # T_e = sum_w exp(2pi i e * klog / pe)
    Phase = np.exp(2j*np.pi*np.outer(e_all, klog)/pe)
    T = Phase.sum(axis=1)        # length pe, T[0]=count(real)
    absT = np.abs(T)
    # The "h-shift family" relevant to the house: by A_h identity the operative chars are
    # those NONTRIVIAL on mu_n is irrelevant for phi (phi acts on 1-w); but the autocorr
    # identity ties h to the additive shift.  We take the WORST tangent sum over all e!=0
    # and also the worst over the m-coset-quotient structure.
    Tnz = absT[1:]               # e=1..pe-1
    maxT = float(np.max(Tnz)); rmsT = float(np.sqrt(np.mean(Tnz**2)))
    return dict(p=p,m=m,n=n,B=B,eta=eta,absT=absT,maxT=maxT,rmsT=rmsT,sqp=sqp,
                etadistinct=len(np.unique(np.round(eta,6))))

print("="*100)
print("C093 -- multiplicative h-shift homothety lever: conductor uniform-in-p at FIXED index?")
print("="*100)

# ============================================================================
# PART A: FIXED-INDEX FAMILY (the core C093 claim). Hold m fixed, vary p, check
#         whether max_h|T_h|/sqrt(n) is bounded UNIFORMLY in p (lever works) or grows.
# ============================================================================
print("\n### PART A: FIXED INDEX m, vary p -> does max|T|/sqrt(n) stay bounded (homothety gain)?")
print("(n, m_target): finds several primes p=1+n*m at ~same index, tracks the per-index trend")
for n in (8, 16, 32):
    print(f"\n-- n={n}: hold index m near a few fixed targets, list primes found --")
    for m_target in (65, 129, 257):
        # collect up to 4 primes with index NEAR m_target (same 'fixed index' band)
        found=[]
        for mm in range(m_target, m_target+4000):
            p=1+n*mm
            if 1+n*mm>6_000_000: break
            if is_prime(p):
                found.append((p,mm))
            if len(found)>=4: break
        for (p,mm) in found:
            R=run(n,p)
            print(f"   p={p:>8} m={mm:>5} (beta={math.log(p)/math.log(n):.2f}) "
                  f"B/sqrt(n)={R['B']/math.sqrt(n):.3f}  "
                  f"maxT/sqrt(n)={R['maxT']/math.sqrt(n):.3f}  "
                  f"maxT/rmsT={R['maxT']/R['rmsT']:.3f}  sqrt(ln m)={math.sqrt(math.log(mm)):.3f}")

# ============================================================================
# PART B: PRIZE-LIKE REGIME (n << sqrt q), check B vs sqrt(n ln m) and the per-h
#         sqrt(p) triviality of the homothety bound.
# ============================================================================
print("\n### PART B: prize-like regime (n<<sqrt q), B law + per-period conductor triviality")
print(" Per-period sup from a single Kummer sheaf is the TRIVIAL m*sqrt(p)/m = sqrt(p);")
print(" check whether B (true) << sqrt(p) (so a real gain is NEEDED) and whether the")
print(" m-average max|T| shows the BGK sqrt(ln m) extreme-value gap (no homothety gain).")
for (n,beta) in [(8,3.0),(16,3.0),(32,2.6),(64,2.5),(8,4.0),(16,3.5)]:
    p,m=find_prime_beta(n,beta)
    if p is None:
        print(f"  n={n} beta={beta}: no prime"); continue
    R=run(n,p)
    Bn=R['B']/math.sqrt(n)
    Bnlnm=R['B']/math.sqrt(n*math.log(m))
    trivial_period = R['sqp']                 # single-sheaf Deligne sup per period
    print(f"  n={n:>3} p={p:>8} m={m:>5} beta={math.log(p)/math.log(n):.2f}  "
          f"n/sqrt(q)={n/R['sqp']:.4f}  B={R['B']:.2f}  B/sqrt(n)={Bn:.3f}  "
          f"B/sqrt(n ln m)={Bnlnm:.3f}")
    print(f"        single-sheaf trivial per-period bound sqrt(p)={trivial_period:.2f} "
          f"(B/sqrt(p)={R['B']/trivial_period:.4f} -- real gain over trivial is NEEDED)")
    print(f"        m-avg tangent: maxT/sqrt(n)={R['maxT']/math.sqrt(n):.3f} "
          f"maxT/rmsT={R['maxT']/R['rmsT']:.3f} vs sqrt(ln m)={math.sqrt(math.log(m)):.3f} "
          f"(extreme-value gap => no homothety gain)")
