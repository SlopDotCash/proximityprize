#!/usr/bin/env python3
"""
#407 ROUTE [cumulant] — ONSET LAW. PIN the central claim: at the first order r0 where the mod-q
defect appears, the connected cumulant kappa_{r0} INHERITS the defect EXACTLY (ratio 1.0000), so
cumulants give ZERO new depth past the defect onset. Reason (proven below numerically + by the
recursion): cumulant_r = mu_r - poly(mu_1,...,mu_{r-1}); at r0 every LOWER moment is still at its
defect-free char-0 value, so the correction poly carries no defect, hence
  kappa_{r0}^{defect} = mu_{r0}^{defect}  EXACTLY.
The defect ONSET order is r0 = ceil(log_n p) (first additive moment that is non-clean: p < n^{r0}).
This pins r0 == r_max == the Betti wall depth; in the prize regime (m=2^128, log_n p -> 1+) r0 -> 2.

ALSO test the CENTERED / standardized cumulant and the FREE cumulant (the only other natural signed
expansions) to be sure no signed variant escapes the onset.
"""
import math, cmath
from fractions import Fraction
from math import comb

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prime_1_mod_n_near(target, n):
    p = target - (target % n) + 1
    if p > target: p -= n
    while p > n:
        if is_prime(p): return p
        p -= n
    return None

def order_n_gen(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s = set(); x = 1
        for _ in range(n): s.add(x); x = x*h % p
        if len(s) == n: return h
    return None

def Er_Fq_exact(p, n, h, rmax):
    mu = [pow(h, i, p) for i in range(n)]
    R = [0]*p
    for x in mu: R[x] += 1
    Es = {}; cur = R[:]
    for r in range(1, rmax+1):
        Es[r] = sum(c*c for c in cur)
        if r < rmax:
            nxt = [0]*p
            for v in range(p):
                cv = cur[v]
                if cv:
                    for x in mu: nxt[(v+x)%p] += cv
            cur = nxt
    return Es

def Er_char0_exact(n, rmax):
    import itertools
    from collections import defaultdict
    pts = [cmath.exp(2j*math.pi*i/n) for i in range(n)]
    res = {}
    for r in range(1, rmax+1):
        if n**r > 3_000_000: res[r] = None; continue
        cnt = defaultdict(int)
        for combo in itertools.product(range(n), repeat=r):
            s = sum(pts[i] for i in combo)
            cnt[(round(s.real,6), round(s.imag,6))] += 1
        res[r] = sum(v*v for v in cnt.values())
    return res

def moments_to_cumulants(mu, rmax):
    kap = {}
    for nn in range(1, rmax+1):
        if mu.get(nn) is None: kap[nn] = None; continue
        s = mu[nn]; ok = True
        for k in range(1, nn):
            if kap.get(k) is None or mu.get(nn-k) is None: ok = False; break
            s -= comb(nn-1, k-1) * kap[k] * mu[nn-k]
        kap[nn] = s if ok else None
    return kap

def free_cumulants(mu, rmax):
    """Free (non-crossing) cumulants via moment-cumulant relation m_n = sum over NC partitions.
       Use the recursion m_n = sum_{s=1}^{n} kappa_s * sum_{compositions} ... ; simplest: the
       implicit relation R(z)=M(zR(z))-type. We use the standard recursion:
       m_n = sum_{k=1}^{n} kappa_k * sum_{i1+...+ik=n-k, ij>=0} prod m_{ij} (m_0=1)."""
    fk = {}
    m = {0: Fraction(1)}
    for r in range(1, rmax+1):
        m[r] = mu[r] if mu.get(r) is not None else None
    for nn in range(1, rmax+1):
        if m[nn] is None: fk[nn] = None; continue
        # m_nn = kappa_nn + sum_{k=1}^{nn-1} kappa_k * S(nn-k, k)  where
        # S(t,k)=sum over (i1..ik)>=0 summing to t of prod m_{ij}; isolate kappa_nn (its S is k=nn? no)
        # standard: m_n = sum_{k=1}^n kappa_k * [coeff] ; kappa_nn appears with k=nn, i's all 0 -> prod=1
        def S(t, k):
            # number-weighted: sum over k nonneg ints summing to t of prod m_{i}
            if k == 0: return Fraction(1) if t == 0 else Fraction(0)
            total = Fraction(0)
            # dp
            dp = [Fraction(0)]*(t+1); dp[0] = Fraction(1)
            for _ in range(k):
                ndp = [Fraction(0)]*(t+1)
                for a in range(t+1):
                    if dp[a] == 0: continue
                    for b in range(t-a+1):
                        if m.get(b) is None: continue
                        ndp[a+b] += dp[a]*m[b]
                dp = ndp
            return dp[t]
        rhs_known = Fraction(0); ok = True
        for k in range(1, nn):
            if fk.get(k) is None: ok = False; break
            rhs_known += fk[k]*S(nn-k, k)
        if not ok: fk[nn] = None; continue
        # k=nn term: kappa_nn * S(0,nn)=kappa_nn*1
        fk[nn] = m[nn] - rhs_known
    return fk

print("="*100)
print("ONSET LAW: at the defect-onset order r0=ceil(log_n p), kappa_{r0}^def / mu_{r0}^def = ?")
print("(classical AND free cumulants). r0 also = the Betti/Deep-moment wall depth.")
print("="*100)
print(f"{'n':>3} {'p':>9} {'log_n p':>8} {'r0(onset)':>9} {'ceil(log_n p)':>13} "
      f"{'classical ratio':>16} {'free ratio':>11}")
for n in (4, 8, 16):
    rmax = 7 if n == 4 else (6 if n == 8 else 5)
    Ec = Er_char0_exact(n, rmax)
    for beta in (1.5, 2.0, 2.5, 3.0, 3.5, 4.0):
        p = prime_1_mod_n_near(int(round(n**beta)), n)
        if p is None or p > 1_500_000: continue
        h = order_n_gen(p, n)
        if h is None: continue
        Efq = Er_Fq_exact(p, n, h, rmax)
        mu  = {r: Fraction(p*Efq[r]-n**(2*r), p-1) for r in range(1, rmax+1)}
        muC = {r: (Fraction(p*Ec[r]-n**(2*r), p-1) if Ec.get(r) is not None else None)
               for r in range(1, rmax+1)}
        # onset order: first r with Efq[r] != Ec[r]
        r0 = None
        for r in range(1, rmax+1):
            if Ec.get(r) is None: break
            if Efq[r] != Ec[r]: r0 = r; break
        if r0 is None:
            lnp = math.log(p)/math.log(n)
            print(f"{n:>3} {p:>9} {lnp:>8.2f} {'>'+str(rmax):>9} {math.ceil(lnp):>13} "
                  f"{'(no onset<=rmax)':>16} {'-':>11}")
            continue
        kap = moments_to_cumulants(mu, rmax)
        kapC= moments_to_cumulants(muC, rmax)
        fk  = free_cumulants(mu, rmax)
        fkC = free_cumulants(muC, rmax)
        muD = mu[r0]-muC[r0]
        kapD= kap[r0]-kapC[r0]
        fkD = (fk[r0]-fkC[r0]) if (fk.get(r0) is not None and fkC.get(r0) is not None) else None
        cl = float(kapD/muD) if muD != 0 else float('nan')
        fr = float(fkD/muD) if (fkD is not None and muD != 0) else float('nan')
        lnp = math.log(p)/math.log(n)
        print(f"{n:>3} {p:>9} {lnp:>8.2f} {r0:>9} {math.ceil(lnp):>13} "
              f"{cl:>16.6f} {fr:>11.6f}")
print("""
VERDICT: if the classical (and free) cumulant ratio is 1.000000 at EVERY onset r0, the cumulant
inherits the defect at its onset order -> ZERO new depth -> the route does NOT beat the r=2 wall.
r0 == ceil(log_n p): the onset is the SAME order as the Betti/deep-moment wall (CharSumMomentDeepWall).
""")
