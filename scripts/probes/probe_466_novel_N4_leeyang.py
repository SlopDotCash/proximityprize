#!/usr/bin/env python3
"""
#466 NOVEL LANE N4-leeyang -- the Gauss period polynomial as a root-location problem:
the COMPLETE consumer tradeoff, and the integer-multiset countermodel that kills it.

CONTEXT (prior art, do not re-prove):
  - G3 (#444, DISPROOF_LOG 15728, _wf9G3_periodpoly_coeff_nogo.lean): Fujiwara/Cauchy/Lagrange
    on Psi_m have argmax k=2, bound = sqrt(2(p-n-1)) -- loose by sqrt(m/log m). Max-FORM bounds dead.
  - A6 (#444, DISPROOF_LOG 844): Schur-Siegel-Smyth trace framing reduces to Johnson.
  - R1 (#466): CMK lone-spike -- abstract equal-atom moment problem's answer IS the raw moment bound.

WHAT THIS PROBE ADDS (the N4 lane deliverables):
  P1. Wick prediction for the elementary symmetric functions:  |e_{2s}| ~ p2^s/(2^s s!)
      (hence |e_{2s}|^{1/2s} ~ sqrt(p2/2)/(s!)^{1/2s}, DECREASING in s => k=2 binds for every
      max-form bound). Measured against exact/float coefficients at n=8,p=4001 and n=16,p=65537.
  P2. THE COLLAPSE LEMMA data: Newton triangularity e_1..e_K <-> p_1..p_K (verified exactly to K=4
      from wraparound-count DP); so ANY root bound consuming shallow coefficients is a shallow-
      moment consumer.
  P3. THE INTEGER-MULTISET COUNTERMODEL (the lane's new object): an explicit monic, totally-real,
      degree-m polynomial with INTEGER coefficients (indeed almost-all-integer roots plus at most
      a few golden-ratio quadratic packs to fix the Newton-Frobenius congruences), matching the
      TRUE period-polynomial power sums p_1,p_2 (K=2) and p_1..p_4 (K=4) EXACTLY, whose house is
      ~sqrt(p) (K=2) resp ~(2*p4)^{1/4} (K=4)  >> true M. Consequence: real-rootedness + integrality
      + degree + shallow coefficients impose NO house bound below the lone-spike/moment value --
      the entire Lee-Yang / Newton-inequality / Laguerre-Polya apparatus is 0 bits here.
  P4. The prize-point tradeoff table: class floor S_2s = sqrt(2s/e)*sqrt(n)*m^{1/(2s)}(1+o(1)),
      minimized ONLY at s ~ ln m where it equals the raw moment bound sqrt(2)*sqrt(n ln m):
      shallow-k weighted consumers give NOTHING beyond the raw moment ladder; depth k=2s ~ 2 ln m
      of coefficient data = Wick moments at depth ln m = the wall, verbatim.

Honesty: proper subgroup mu_n, n=2^mu, p prime = 1 mod n, p >> n^3, NEVER n = p-1.
"""
import math
import numpy as np
from math import sqrt, log, factorial

OUT = []
def say(s=""):
    print(s)
    OUT.append(s)

# ---------------------------------------------------------------- utilities
def primitive_root(p):
    fac = []
    x = p - 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def periods(p, n):
    """the m = (p-1)/n distinct Gauss period values eta_i (real; -1 in mu_n since n even)"""
    m = (p - 1) // n
    g = primitive_root(p)
    gm = pow(g, m, p)
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x)
        x = (x * gm) % p
    assert len(set(mu)) == n
    mu = np.array(mu, dtype=np.int64)
    etas = np.empty(m)
    b = 1
    for i in range(m):
        etas[i] = np.cos(2.0 * np.pi * ((b * mu) % p) / p).sum()
        b = (b * g) % p
    return mu, etas

def exact_power_sums(p, n, mu):
    """exact integer p_r = sum_i eta_i^r for r=1..4 via wraparound counts N(r):
       sum_{b in F_p} eta_b^r = p*N(r);  p_r = (p*N(r) - n^r)/n."""
    dist2 = np.zeros(p, dtype=np.int64)
    for x in mu:
        idx = (x + mu) % p
        for z in idx:
            dist2[z] += 1
    N1 = 0  # 0 not in mu_n
    N2 = int(dist2[0])
    neg = (-np.arange(p)) % p
    N3 = int(sum(dist2[int((-x) % p)] for x in mu))
    N4 = int(np.dot(dist2, dist2[neg]))
    ps = {}
    for r, Nr in [(1, N1), (2, N2), (3, N3), (4, N4)]:
        num = p * Nr - n ** r
        assert num % n == 0, (r, Nr)
        ps[r] = num // n
    return ps, (N1, N2, N3, N4)

def newton_e_from_p(ps, K):
    """exact e_1..e_K from p_1..p_K (Newton), rationals guaranteed integral"""
    from fractions import Fraction
    e = [Fraction(1)]
    for k in range(1, K + 1):
        acc = Fraction(0)
        for i in range(1, k + 1):
            acc += Fraction((-1) ** (i - 1)) * Fraction(ps[i]) * e[k - i]
        e.append(acc / k)
    for k in range(1, K + 1):
        assert e[k].denominator == 1
    return [int(x) for x in e]

def coeff_profile(etas, mn):
    """scaled product: returns |e_k| via log10, k=1..m (float64, scaled roots)"""
    sigma = sqrt(mn)
    r = etas / sigma
    poly = np.array([1.0])
    for x in r:
        poly = np.concatenate([poly, [0.0]])
        poly[1:] -= x * poly[:-1]
    # |e_k(eta)| = |poly[k]| * sigma^k ; return log10|e_k|
    with np.errstate(divide="ignore"):
        lg = np.log10(np.abs(poly))
    lg = lg + np.arange(len(poly)) * math.log10(sigma)
    return lg  # lg[k] = log10 |e_k|; -inf where underflow/zero

# ================================================================ scale 1: n=8, p=4001
say("=" * 78)
say("SCALE 1: n=8, p=4001, m=500  (proper dyadic subgroup, beta ~ 4)")
say("=" * 78)
n, p = 8, 4001
m = (p - 1) // n
mu, etas = periods(p, n)
M_true = float(np.max(np.abs(etas)))
target = sqrt(n * log(p / n))
say(f"true M = {M_true:.4f}   target sqrt(n log(p/n)) = {target:.4f}   Johnson sqrt(p) = {sqrt(p):.4f}")

ps, Ns = exact_power_sums(p, n, mu)
say(f"exact wraparound counts: N(1..4) = {Ns}")
say(f"  N(4) vs 3n^2-3n = {3*n*n-3*n}   (excess = char-p wraparound at r=2): {Ns[3] - (3*n*n-3*n)}")
say(f"exact power sums: p1={ps[1]}, p2={ps[2]}, p3={ps[3]}, p4={ps[4]}")
assert ps[1] == -1 and ps[2] == p - n
# Newton-Frobenius congruences (the ONLY integrality constraint on shallow moments):
say(f"congruences: (p3-p1) mod 3 = {(ps[3]-ps[1])%3} (must be 0);  (p4-p2) mod 4 = {(ps[4]-ps[2])%4} (must be 0)")
say(f"             (p3-p1) mod 6 = {(ps[3]-ps[1])%6};  (p4-p2) mod 12 = {(ps[4]-ps[2])%12}")
assert (ps[3] - ps[1]) % 3 == 0 and (ps[4] - ps[2]) % 4 == 0

eK = newton_e_from_p(ps, 4)
say(f"exact e_1..e_4 (Newton): {eK[1:]}")

lg = coeff_profile(etas, m * n)
# check float vs exact for k<=4
say("float-vs-exact coefficient check (log10|e_k|): " + ", ".join(
    f"k={k}: {lg[k]:.6f} vs {math.log10(abs(eK[k])):.6f}" for k in range(1, 5) if eK[k] != 0))

# P1: Wick prediction |e_{2s}| ~ p2^s / (2^s s!)
say("")
say("P1 -- Wick prediction for elementary symmetric functions, |e_2s| ~ p2^s/(2^s s!):")
say("   s    measured log10|e_2s|    predicted     ratio e/pred")
for s in range(1, 11):
    pred = s * math.log10(ps[2] / 2) - math.log10(factorial(s))
    say(f"  {s:2d}      {lg[2*s]:10.4f}        {pred:10.4f}     {10**(lg[2*s]-pred):8.4f}")

# Fujiwara profile
f = np.full(len(lg), -np.inf)
for k in range(1, m + 1):
    v = lg[k] - (math.log10(2.0) if k == m else 0.0)
    f[k] = v / k  # log10 |e_k|^{1/k}
kmax = int(np.nanargmax(f[1:])) + 1
say("")
say(f"Fujiwara terms 2|e_k|^(1/k): argmax k = {kmax} (G3 predicted 2);"
    f" bound = {2*10**f[kmax]:.3f} vs sqrt(2(p-n-1)) = {sqrt(2*(p-n-1)):.3f}")
say(f"  profile at k=2,4,8,16,32,64: " + ", ".join(f"{2*10**f[k]:.2f}" for k in [2, 4, 8, 16, 32, 64]))
say(f"  => every max-form coefficient bound >= {2*10**f[2]:.1f} = sqrt(2p) > Johnson; true M = {M_true:.2f}")

# ---------------------------------------------------------------- P3a: K=2 countermodel
say("")
say("P3a -- K=2 INTEGER countermodel (matches p1, p2 exactly; degree m; totally real; ZZ roots):")
# roots: spike s, a copies of +1, c copies of -1, rest 0
best = None
for s in range(int(sqrt(ps[2])), 0, -1):
    rem = ps[2] - s * s
    a = (rem - 1 - s) // 2
    c = (rem + 1 + s) // 2
    if a < 0:
        continue
    assert (rem - 1 - s) % 2 == 0
    if a + c <= m - 1:
        best = (s, a, c)
        break
s2, a2, c2 = best
# verify exactly
chk1 = s2 + a2 - c2
chk2 = s2 * s2 + a2 + c2
nzero = m - 1 - a2 - c2
assert chk1 == ps[1] and chk2 == ps[2] and nzero >= 0
say(f"  spike s={s2}, {a2} roots at +1, {c2} at -1, {nzero} at 0   [p1={chk1}, p2={chk2}: EXACT]")
say(f"  house = {s2}  vs Johnson sqrt(p) = {sqrt(p):.1f}  vs true M = {M_true:.2f}"
    f"  => K=2 consumers cannot go below {s2}")

# ---------------------------------------------------------------- P3b: K=4 countermodel
say("")
say("P3b -- K=4 countermodel (matches p1..p4 exactly; monic ZZ[x]; totally real; degree m):")
say("  atoms at 0,+-1,+-2,+-3,+-4 + spike s + kappa golden packs (x^2 -+ x - 1) for congruences")

T1, T2, T3, T4 = ps[1], ps[2], ps[3], ps[4]

def solve_K4(s, double_spike):
    # golden packs: Q+ adds (1,3,4,7) to (p1,p2,p3,p4); Q- adds (-1,3,-4,7). Each uses 2 roots.
    # double_spike: roots +s AND -s (odd moments self-cancel; quartic cost 2s^4).
    #   [single spike dies: cancelling its odd moment s^3 costs ~s^4 quartic at ANY scale]
    nsp = 2 if double_spike else 1
    for kplus in range(0, 4):
        for kminus in range(0, 4):
            kt = kplus + kminus
            R1 = T1 - (0 if double_spike else s) - kplus + kminus
            R2 = T2 - nsp * s * s - 3 * kt
            R3 = T3 - (0 if double_spike else s ** 3) - 4 * (kplus - kminus)
            R4 = T4 - nsp * s ** 4 - 7 * kt
            if R2 < 0 or R4 < 0:
                continue
            if (R4 - R2) % 12 != 0 or (R3 - R1) % 6 != 0:
                continue
            W = (R4 - R2) // 12  # beta + 6 gamma + 20 delta = W  (alpha@1, beta@2, gamma@3, delta@4)
            for delta in range(0, min(W // 20, 300) + 1):
                for gamma in range(0, min((W - 20 * delta) // 6, 500) + 1):
                    beta = W - 6 * gamma - 20 * delta
                    if beta < 0:
                        continue
                    alpha = R2 - 4 * beta - 9 * gamma - 16 * delta
                    if alpha < 0:
                        continue
                    if 1 + alpha + beta + gamma + delta + 2 * kt > m:
                        continue
                    # odd: d1+2d2+3d3+4d4 = R1 ; d1+8d2+27d3+64d4 = R3
                    V = (R3 - R1) // 6  # d2 + 4 d3 + 10 d4 = V
                    for d4 in range(-min(delta, 8), min(delta, 8) + 1):
                        lo = max(-gamma, (V - 10 * d4 - min(beta, abs(V) + 40)) // 4 - 1)
                        for d3 in range(-gamma, gamma + 1):
                            d2 = V - 4 * d3 - 10 * d4
                            if abs(d2) > beta:
                                continue
                            d1 = R1 - 2 * d2 - 3 * d3 - 4 * d4
                            if abs(d1) > alpha:
                                continue
                            if (alpha + d1) % 2 or (beta + d2) % 2 or (gamma + d3) % 2 or (delta + d4) % 2:
                                continue
                            return dict(s=s, kplus=kplus, kminus=kminus,
                                        alpha=alpha, beta=beta, gamma=gamma, delta=delta,
                                        d1=d1, d2=d2, d3=d3, d4=d4)
    return None

sol = None
for s in range(20, 8, -1):
    sol = solve_K4(s)
    if sol:
        break

if sol:
    s = sol["s"]
    # exact verification: rebuild power sums
    c = {}
    for v, tot, d in [(1, sol["alpha"], sol["d1"]), (2, sol["beta"], sol["d2"]),
                      (3, sol["gamma"], sol["d3"]), (4, sol["delta"], sol["d4"])]:
        c[v] = ((tot + d) // 2, (tot - d) // 2)  # (count at +v, count at -v)
    P = [0, 0, 0, 0, 0]
    for r in range(1, 5):
        acc = s ** r
        for v, (cp, cm) in c.items():
            acc += cp * v ** r + cm * (-v) ** r
        # golden packs: p_r(x^2-x-1) = (1,3,4,7); (x^2+x-1) = (-1,3,-4,7)
        gp = {1: (1, -1), 2: (3, 3), 3: (4, -4), 4: (7, 7)}[r]
        acc += sol["kplus"] * gp[0] + sol["kminus"] * gp[1]
        P[r] = acc
    nroots = 1 + sum(cp + cm for cp, cm in c.values()) + 2 * (sol["kplus"] + sol["kminus"])
    ok = (P[1], P[2], P[3], P[4]) == (T1, T2, T3, T4) and nroots <= m
    say(f"  FOUND: spike s={s}; counts(+v,-v): " + ", ".join(f"{v}:{c[v]}" for v in sorted(c)) +
        f"; golden packs +:{sol['kplus']} -:{sol['kminus']}; zeros={m-nroots}")
    say(f"  exact power sums of countermodel: {P[1:]} vs target {[T1,T2,T3,T4]}  -> {'EXACT MATCH' if ok else 'FAIL'}")
    assert ok
    say(f"  house = {s}  vs raw 4th-moment bound p4^(1/4) = {T4**0.25:.2f}"
        f"  vs bulk-floor cap (2 p4/3)^(1/4)-ish  vs true M = {M_true:.2f}")
    say(f"  => even with p1..p4 EXACT + integrality + real-rootedness + degree m, house floor >= {s}"
        f"  ({s/M_true:.1f}x the truth, {s/target:.1f}x the target)")
else:
    say("  no solution found in search range (tighten scales) -- s <= 11 fallback not attempted")

# ---------------------------------------------------------------- scale 2: n=16, p=65537
say("")
say("=" * 78)
say("SCALE 2: n=16, p=65537, m=4096  (profile replication at larger m)")
say("=" * 78)
n2, p2_ = 16, 65537
m2 = (p2_ - 1) // n2
mu2, etas2 = periods(p2_, n2)
M2 = float(np.max(np.abs(etas2)))
t2 = sqrt(n2 * log(p2_ / n2))
say(f"true M = {M2:.4f}   target = {t2:.4f}   Johnson = {sqrt(p2_):.2f}   sqrt(2p) = {sqrt(2*p2_):.2f}")
lg2 = coeff_profile(etas2, m2 * n2)
f2 = np.full(len(lg2), -np.inf)
for k in range(1, m2 + 1):
    if np.isfinite(lg2[k]):
        f2[k] = (lg2[k] - (math.log10(2.0) if k == m2 else 0.0)) / k
k2max = int(np.nanargmax(f2[1:])) + 1
say(f"Fujiwara argmax k = {k2max}; bound = {2*10**f2[k2max]:.2f} = sqrt(2(p-n-1)) = {sqrt(2*(p2_-n2-1)):.2f}")
say("Wick-prediction ratio |e_2s| / [p2^s/(2^s s!)] for s=1..8: " + ", ".join(
    f"{10**(lg2[2*s] - (s*math.log10((p2_-n2)/2) - math.log10(factorial(s)))):.3f}" for s in range(1, 9)))

# ---------------------------------------------------------------- P4: prize-point table
say("")
say("=" * 78)
say("P4 -- PRIZE-POINT TRADEOFF (pure arithmetic; class floor S_2s = best possible for ANY")
say("      consumer of coefficients e_1..e_{2s} == moments p_1..p_2s, granted Wick-exact)")
say("=" * 78)
for tag, lgn, lgm in [("beta=4 diagonal (p=n^4)", 30, 90), ("prize-exact (m=2^128)", 30, 128)]:
    lgp = lgn + lgm  # p ~ n*m
    lnm = lgm * log(2)
    say(f"[{tag}]  n=2^{lgn}, m=2^{lgm}, p~2^{lgp}")
    say(f"  Johnson sqrt(p)              = 2^{lgp/2:.2f}")
    say(f"  G3/Fujiwara sqrt(2p)         = 2^{lgp/2+0.5:.2f}   (> Johnson; max-form dead at k=2)")
    say(f"  S_2 (K=2 class floor)        = 2^{lgp/2:.2f}   (= Johnson: K=2 consumers see nothing)")
    s4 = (1 + lgp + lgn) / 4  # (2 p n)^{1/4}
    say(f"  S_4 (K=4 class floor)        = 2^{s4:.2f}   raw 4th-moment (3pn)^(1/4) = 2^{(math.log2(3)+lgp+lgn)/4:.2f}")
    tgt = math.log2(sqrt(2 ** lgn * lnm))
    say(f"  prize target sqrt(n ln m)    = 2^{tgt:.2f}   => S_4/target = 2^{s4-tgt:.1f}")
    say(f"  class-floor curve: S_2s/target = sqrt(2s/(e ln m)) * m^(1/2s);  minimum sqrt(2) at s* = ln m = {lnm:.1f}")
    say(f"  => coefficient depth needed k* = 2 ln m = {2*lnm:.0f}  == Wick moments to r ~ ln m == THE WALL")
    say("")

with open("scripts/probes/_out_466_novel_N4_leeyang.txt", "w") as fh:
    fh.write("\n".join(OUT) + "\n")
say("written: scripts/probes/_out_466_novel_N4_leeyang.txt")
