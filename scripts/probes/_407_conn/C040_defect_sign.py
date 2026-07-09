#!/usr/bin/env python3
"""
C040 attack: "The cumulant IS the char-p energy DEFECT and the defect is NEGATIVE".

CLAIM (from C040.json):
  (1) identity  n*sum_b |eta_b|^{2r} = q*E_r - n^{2r}  (off-diagonal cumulant; b=0 term n^{2r} cancels).
      [NOTE: this is the Parseval-moment identity. Standard form is sum_{b in F_q} |eta_b|^{2r} = q*E_r,
       and the b=0 term is |eta_0|^{2r} = n^{2r}, so sum_{b!=0} |eta_b|^{2r} = q*E_r - n^{2r}. The "n*"
       prefactor in the json is a typo/artifact; we test the standard identity.]
  (2) char-p DEFECT  D_r := E_r^{Fq} - E_r^{C}  is NEGATIVE in regime (n=16,r=5: E_5=5.17e8 < E_5^C=9.91e8).
  (3) hence the "cumulant" kappa_r := q*E_r - n^{2r}, divided by the Gaussian baseline q*(2r-1)!!*n^r,
      stays <= 1 WITH MARGIN (kappa_r <= 1), dissolving the W-anomaly.

THE TEST that matters for the prize: is the defect negative (and the normalized cumulant <= 1) ACROSS
the prize regime -- PROPER subgroup mu_n, LARGE prime, n << sqrt(q), beta ~ 4-5 -- or only at the small
prime where it was measured? (The #400 trap: full-group / small-prime tests give false positives.)

EXACT integer arithmetic throughout (E_r^{Fq} via r-fold convolution counts; E_r^{C} via exact
Gaussian-integer / unit-circle sum counts using sympy exact roots-of-unity coordinates is overkill;
we use exact integer char-0 energy via the known structure when feasible, else rounded brute for the
real/imag keys with high precision but report the EXACT Fq side and the relation kappa_r vs baseline).
"""
import math, itertools, cmath
from fractions import Fraction
from collections import defaultdict

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def primes_1_mod_n(n, lo, hi, count):
    """Return up to `count` primes p == 1 mod n in [lo, hi], spread out."""
    out = []
    start = lo - (lo % n) + 1
    if start < lo: start += n
    p = start
    while p <= hi and len(out) < count:
        if is_prime(p): out.append(p)
        p += n
    return out

def order_n_gen(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s = set(); x = 1
        for _ in range(n): s.add(x); x = x*h % p
        if len(s) == n: return h
    return None

def dfac2(r):  # (2r-1)!!
    x = 1
    for i in range(1, r+1): x *= (2*i-1)
    return x

def Er_Fq_exact(p, n, h, rmax):
    """EXACT integer E_r(mu_n) in F_p for r=1..rmax via r-fold convolution counts."""
    mu = [pow(h, i, p) for i in range(n)]
    R = [0]*p
    for x in mu: R[x] += 1
    Es = {}
    cur = R[:]
    for r in range(1, rmax+1):
        Es[r] = sum(c*c for c in cur)
        if r < rmax:
            nxt = [0]*p
            for v in range(p):
                cv = cur[v]
                if cv:
                    for x in mu:
                        nxt[(v + x) % p] += cv
            cur = nxt
    return Es

def Er_char0_exact(n, rmax, cap=4_000_000):
    """char-0 additive energy of the n-th roots of unity (exact integer count)."""
    pts = [cmath.exp(2j*math.pi*i/n) for i in range(n)]
    res = {}
    for r in range(1, rmax+1):
        if n**r > cap:
            res[r] = None; continue
        cnt = defaultdict(int)
        for combo in itertools.product(range(n), repeat=r):
            s = sum(pts[i] for i in combo)
            key = (round(s.real, 7), round(s.imag, 7))
            cnt[key] += 1
        res[r] = sum(v*v for v in cnt.values())
    return res

print("="*120)
print("C040: defect sign & normalized cumulant across the PRIZE regime (proper subgroup, large prime, n<<sqrt q)")
print("="*120)

# We test n in {8,16,32} (n=16 is where the json measured). For each n we scan beta and several primes
# per beta band, so we can see the sign of the defect as a function of how 'large' q is relative to n^?.
for n in (8, 16, 32):
    rmax = 6 if n == 8 else (5 if n == 16 else 4)
    Ec = Er_char0_exact(n, rmax)
    print(f"\n{'#'*110}\nn = {n}   (char-0 energies E_r^C: " +
          ", ".join(f"r{r}={Ec[r]}" for r in range(1,rmax+1) if Ec.get(r) is not None) + ")")
    print(f"  rule of thumb (CharSumMomentDeepWall): char-0 value valid only for r <= r_max ~ 2*log_n(p)-3")
    print(f"  {'beta':>5} {'p':>12} {'log_n p':>8} | " +
          " ".join(f"D{r}sgn" for r in range(1,rmax+1)) + " || " +
          " ".join(f"kap{r}/base" for r in range(1,rmax+1)))
    for beta in (2.0, 3.0, 4.0, 4.5, 5.0):
        target = int(round(n**beta))
        # pick a few primes near n^beta (spread the band to avoid a single accidental prime)
        ps = primes_1_mod_n(n, max(target - 50*n, n+1), target + 400*n, 2)
        for p in ps:
            if p > 6_000_000:   # convolution table size guard
                continue
            h = order_n_gen(p, n)
            if h is None: continue
            Efq = Er_Fq_exact(p, n, h, rmax)
            lnp = math.log(p)/math.log(n)
            rmax_valid = 2*lnp - 3
            dsign = []
            kapbase = []
            for r in range(1, rmax+1):
                if Ec.get(r) is None:
                    dsign.append("  ?  "); kapbase.append("   ?   "); continue
                D = Efq[r] - Ec[r]            # exact integer defect
                sgn = "-" if D < 0 else ("0" if D == 0 else "+")
                dsign.append(f" {sgn} ")
                # normalized cumulant kappa_r = q*E_r - n^{2r}  over baseline q*(2r-1)!!*n^r
                kap = Fraction(p*Efq[r] - n**(2*r))
                base = Fraction(p) * dfac2(r) * n**r
                kapbase.append(f"{float(kap/base):7.4f}")
            flag = ""
            # mark whether r-range exceeds the validity cap
            print(f"  {beta:>5.1f} {p:>12} {lnp:>8.3f} | " +
                  " ".join(dsign) + " || " + " ".join(kapbase) +
                  f"   (r_max~{rmax_valid:.1f})")
print("""
KEY READ:
- D{r}sgn = sign of E_r^{Fq} - E_r^{C}. C040 claims '-' (defect negative) in regime.
- kap{r}/base = (q*E_r - n^{2r}) / (q*(2r-1)!!*n^r). C040 claims this stays <= 1 WITH MARGIN.
- Compare to r_max~2 log_n p - 3: the wall predicts kap{r}/base BLOWS UP once r > r_max.
- PRIZE-RELEVANT rows are beta>=4 with the LARGEST primes (n<<sqrt q). Watch the sign flip & the >1 blowup.
""")
