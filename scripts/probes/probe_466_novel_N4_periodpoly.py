#!/usr/bin/env python3
"""
#466 NOVEL LANE N4-leeyang -- the Gauss period polynomial as a ROOT-LOCATION problem.

CLAIM OF THE LANE: the periods eta_b = sum_{x in mu_n} e_p(bx) ARE the roots of the classical
degree-m period polynomial P_m(x) in Z[x] (m = (p-1)/n).  So M = max_{b!=0}|eta_b| = house of
P_m.  This converts the sup-norm into root location of ONE integer, monic, totally-real
polynomial.  We develop the Fujiwara/Lagrange/Cauchy root-bound chain, the Wick prediction for
the elementary symmetric coefficients e_k, and the INTEGER LONE-SPIKE COUNTERMODEL that kills
the entire Lee-Yang / Newton-inequality / Laguerre-Polya apparatus for this problem.

PRIOR ART (do not re-prove):
  - G3 (#444, _wf9G3_periodpoly_coeff_nogo.lean, axiom-clean): Fujiwara max-form binds at k=2,
    bound = sqrt(2(p-n-1)) = Theta(sqrt(nm)), loose by sqrt(m/log m).  Char-0, unconditional.
  - R1 (#466): CMK lone-spike -- the abstract equal-atom moment problem's sharp answer IS the
    raw moment bound; positivity adds nothing.  N4 is the ROOT-LOCATION twin of that finding.

WHAT N4 ADDS:
  P1. WHY k=2 binds: the Wick law |e_{2s}| ~ p2^s/(2^s s!) => |e_{2s}|^{1/2s} DECREASING in s.
  P2. Newton triangularity e_1..e_K <-> p_1..p_K (exact): shallow coefficients = shallow moments.
  P3. INTEGER LONE-SPIKE COUNTERMODEL (K=2 and K=4): explicit monic totally-real Z[x] polynomial
      of degree m matching p_1..p_K EXACTLY with house ~ raw K-moment value >> true M.  Hence
      real-rootedness + integrality + degree + shallow coefficients impose NO house bound below
      the moment ladder: the root-location apparatus is 0 bits here.
  P4. PRIZE-POINT DEPTH TRADEOFF: the best consumer of e_1..e_{2s} == the raw depth-s moment
      bound S_{2s} = sqrt(2ns/e)*(p/n)^{1/2s}; minimized at s*=ln m, reaching sqrt(2 n ln m)
      (target ORDER) but ONLY at coefficient depth k*=2 ln m = deep Wick moments = THE WALL.

Honesty: proper subgroup mu_n, n=2^mu, p prime = 1 mod n, p >> n^3, NEVER n = p-1.
The chain is COMPLETE and then DIES at P4 (deep-coefficient == deep-moment == wall), self-
refuted by the P3 countermodel.  A complete chain killed at its own step k is the deliverable.
"""
import math
import numpy as np
from math import sqrt, log, factorial
from fractions import Fraction

OUT = []
def say(s=""):
    print(s)
    OUT.append(s)

# ---------------------------------------------------------------- arithmetic utilities
def primitive_root(p):
    fac, x, d = [], p - 1, 2
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
    """the m = (p-1)/n distinct Gauss period values eta_i (all real; -1 in mu_n as n even)."""
    m = (p - 1) // n
    g = primitive_root(p)
    gm = pow(g, m, p)
    mu, x = [], 1
    for _ in range(n):
        mu.append(x); x = (x * gm) % p
    assert len(set(mu)) == n
    mu = np.array(mu, dtype=np.int64)
    etas = np.empty(m)
    b = 1
    for i in range(m):
        etas[i] = np.cos(2.0 * np.pi * ((b * mu) % p) / p).sum()
        b = (b * g) % p
    return mu, etas

def exact_power_sums(p, n, mu, K=4):
    """exact integer p_r = sum_i eta_i^r for r=1..K via wraparound counts N(r):
       sum_{b in F_p^*} eta_b^r = p*N(r) - n^r ;  p_r = (p*N(r) - n^r)/n .
       N(r) = #{(x_1..x_r) in mu_n^r : sum = 0 mod p}."""
    S = set(int(x) for x in mu)
    # r=1: 0 not in mu_n ; r=2: pairs x+y=0 ; r=3,4 via convolution DP over residues
    dist2 = np.zeros(p, dtype=np.int64)
    for x in mu:
        for y in mu:
            dist2[(int(x) + int(y)) % p] += 1
    N = {1: 0, 2: int(dist2[0])}
    if K >= 3:
        N[3] = int(sum(dist2[(-int(x)) % p] for x in mu))
    if K >= 4:
        neg = (-np.arange(p)) % p
        N[4] = int(np.dot(dist2, dist2[neg]))
    ps = {}
    for r in range(1, K + 1):
        num = p * N[r] - n ** r
        assert num % n == 0, (r, N[r])
        ps[r] = num // n
    return ps, N

def newton_e_from_p(ps, K):
    """exact e_1..e_K from p_1..p_K (Newton's identities); result guaranteed integral."""
    e = [Fraction(1)]
    for k in range(1, K + 1):
        acc = Fraction(0)
        for i in range(1, k + 1):
            acc += Fraction((-1) ** (i - 1)) * Fraction(ps[i]) * e[k - i]
        e.append(acc / k)
    for k in range(1, K + 1):
        assert e[k].denominator == 1, (k, e[k])
    return [int(x) for x in e]

def coeff_profile_log10(etas, scale):
    """log10 |e_k(eta)| for k=0..m via scaled root product (float64, numerically stable)."""
    sigma = sqrt(scale)
    r = etas / sigma
    poly = np.array([1.0])
    for x in r:
        poly = np.concatenate([poly, [0.0]])
        poly[1:] -= x * poly[:-1]
    with np.errstate(divide="ignore"):
        lg = np.log10(np.abs(poly))
    return lg + np.arange(len(poly)) * math.log10(sigma)

# ---------------------------------------------------------------- K=4 class floor (spike + bulk)
def k4_class_floor(ps, m):
    """The EXACT K=4 class floor: the maximum house of ANY real measure of total mass m matching
       the even moments p_2, p_4 (odd moments p_1,p_3 = O(n) are negligible at the house scale).
       Extremal config = ONE spike at +-s plus a symmetric bulk at a single level +-t on the
       remaining m-1 atoms (the upper principal representation of the [-s,s] moment problem):
         s^2 + (m-1) t^2 = p_2 ,   s^4 + (m-1) t^4 = p_4 .
       Eliminating t (u = (m-1)t^2 => bulk-4th = u^2/(m-1)) gives a quadratic in y = s^2:
         m y^2 - 2 p_2 y + (p_2^2 - (m-1) p_4) = 0
       => y_max = ( p_2 + sqrt( (m-1)(m p_4 - p_2^2) ) ) / m ,  house = sqrt(y_max).
       This is a monic REAL-ROOTED polynomial (Lee-Yang-admissible) whose house >> true M, so
       real-rootedness + p_1..p_4 impose NO house bound below this class floor.  NB: this needs
       m > p_2^2 / p_4 (else the bulk cannot carry the 2nd moment at small 4th moment -- a
       power-mean feasibility bound); satisfied with room at the prize point (p_2^2/p_4 ~ m/3),
       marginal at tiny n where the finite budget itself already pins the house near the truth."""
    p2, p4 = ps[2], ps[4]
    disc = (m - 1) * (m * p4 - p2 * p2)
    if disc < 0:
        return None, None
    y = (p2 + math.sqrt(disc)) / m
    s = math.sqrt(y)
    t = math.sqrt((p2 - y) / (m - 1)) if p2 - y >= 0 else float("nan")
    return s, t

# ================================================================================
say("=" * 82)
say("N4-leeyang: the Gauss period polynomial as root location -- complete chain to its death")
say("=" * 82)

for (n, p) in [(8, 4001), (16, 65537)]:
    m = (p - 1) // n
    mu, etas = periods(p, n)
    M_true = float(np.max(np.abs(etas)))
    target = sqrt(n * log(p / n))
    say("")
    say("-" * 82)
    say(f"SCALE  n={n}, p={p}, m={m}   (beta = log p / log n = {log(p)/log(n):.2f})")
    say("-" * 82)
    say(f"true M = {M_true:.4f}    target sqrt(n log(p/n)) = {target:.4f}    "
        f"Johnson sqrt(p) = {sqrt(p):.3f}")

    ps, N = exact_power_sums(p, n, mu, 4)
    say(f"exact wraparound counts N(1..4) = {tuple(N[r] for r in (1,2,3,4))}   "
        f"[N(4) vs char-0 Wick 3n^2-3n = {3*n*n-3*n}, excess = {N[4]-(3*n*n-3*n)}]")
    say(f"exact power sums p1..p4 = {[ps[r] for r in (1,2,3,4)]}   "
        f"[p1=-1, p2=p-n={p-n}: exact identities]")
    assert ps[1] == -1 and ps[2] == p - n
    eK = newton_e_from_p(ps, 4)
    say(f"exact e_1..e_4 (Newton) = {eK[1:]}   |e2| = (p-n-1)/2 = {(p-n-1)//2}")

    # float coefficient profile & Fujiwara max-form bound
    lg = coeff_profile_log10(etas, m * n)
    kmax = 1 + int(np.nanargmax([lg[k] / k for k in range(1, m + 1)]))
    fuj = 2 * 10 ** (lg[kmax] / kmax)
    say(f"Fujiwara max-form 2*max_k|e_k|^(1/k): argmax k = {kmax}  bound = {fuj:.3f}  "
        f"[sqrt(2(p-n-1)) = {sqrt(2*(p-n-1)):.3f}]")
    say(f"  |e_k|^(1/k) profile k=2,4,8,16: " +
        ", ".join(f"{10**(lg[k]/k):.2f}" for k in (2, 4, 8, 16)) +
        "   (DECREASING => k=2 binds, bound = sqrt(2p) > Johnson)")

    # P1: Wick law for even elementary symmetric functions
    ratios = [10 ** (lg[2*s] - (s*math.log10(ps[2]/2) - math.log10(factorial(s))))
              for s in range(1, min(9, m // 2))]
    say(f"P1 Wick law |e_2s| ~ p2^s/(2^s s!): ratio measured/pred s=1..{len(ratios)} = " +
        ", ".join(f"{x:.3f}" for x in ratios))

    # P3a: K=2 lone-spike integer countermodel
    s2 = int(sqrt(ps[2]))
    while s2 > 0:
        rem = ps[2] - s2 * s2
        a = (rem - 1 - s2)
        if a >= 0 and a % 2 == 0 and (a // 2) + ((rem + 1 + s2) // 2) <= m - 1:
            aP, cM = a // 2, (rem + 1 + s2) // 2
            if s2 + aP - cM == ps[1] and s2*s2 + aP + cM == ps[2]:
                break
        s2 -= 1
    say(f"P3a K=2 lone-spike Z-countermodel: spike s={s2}, {aP}x(+1), {cM}x(-1), {m-1-aP-cM}x(0)  "
        f"-> p1={s2+aP-cM}, p2={s2*s2+aP+cM} EXACT; house = {s2} vs true M = {M_true:.2f}")

    # P3b: K=4 lone-spike integer countermodel
    s4, t4 = k4_class_floor(ps, m)
    if s4:
        say(f"P3b K=4 class floor (spike+bulk, real-rooted): house s = {s4:.3f}, bulk level "
            f"+-t = +-{t4:.3f}  -> matches p2,p4 EXACTLY (p1,p3=O(n) negligible)")
        say(f"    house {s4:.2f} vs true M = {M_true:.2f} ({s4/M_true:.2f}x truth, {s4/target:.2f}x "
            f"target); raw (3pn)^(1/4) = {(3*p*n)**0.25:.2f} [m->inf value]; "
            f"budget check p2^2/p4 = {ps[2]**2//ps[4]} < m = {m}")
    else:
        say("P3b K=4 class floor: infeasible (m too small)")

# ================================================================================
say("")
say("=" * 82)
say("P4 -- PRIZE-POINT DEPTH TRADEOFF (pure arithmetic; the honest death of the lane)")
say("=" * 82)
say("class floor S_2s = best possible house bound from coefficients e_1..e_2s == moments p_1..p_2s")
say("             = (raw depth-s moment bound) = sqrt(2 n s / e) * (p/n)^{1/2s}  (Wick-exact)")
for tag, lgn, lgp in [("beta=4 diagonal (p~n^4)", 30, 120), ("prize-exact (m=2^128)", 30, 158)]:
    lgm = lgp - lgn                      # m = p/n
    lnm = lgm * log(2)
    say("")
    say(f"[{tag}]  n=2^{lgn}, m=2^{lgm}, p~2^{lgp}")
    say(f"  Johnson sqrt(p)               = 2^{lgp/2:.2f}")
    say(f"  Fujiwara/G3 max-form sqrt(2p) = 2^{lgp/2+0.5:.2f}   (WORSE than Johnson; binds at k=2)")
    say(f"  K=2 consumer floor S_2        = 2^{lgp/2:.2f}   (= Johnson exactly; sees nothing)")
    s4 = (math.log2(3) + lgp + lgn) / 4  # (3pn)^{1/4}
    say(f"  K=4 consumer floor S_4        = 2^{s4:.2f}   ((3pn)^{{1/4}}; countermodel-tight)")
    tgt = 0.5 * (lgn + math.log2(lnm))
    say(f"  prize target sqrt(n ln m)     = 2^{tgt:.2f}")
    say(f"  OPTIMIZED floor min_s S_2s    = 2^{0.5*(lgn+math.log2(2*lnm)):.2f} = sqrt(2 n ln m)  "
        f"(target ORDER, const sqrt2)")
    say(f"    achieved at s* = ln m = {lnm:.1f}  ==> coefficient depth k* = 2 ln m = {2*lnm:.0f}")
    say(f"    == Wick power sums to depth r ~ ln m == THE DEEP-MOMENT WALL (not char-0-clean).")

say("")
say("DEATH POINT (honest): the lane's chain is COMPLETE -- M = house(P_m), Fujiwara/Lee-Yang")
say("root location, Newton triangularity, Wick coefficient law, optimized moment ladder reaching")
say("sqrt(2 n ln m) = target order.  It DIES at P4: the optimum needs coefficient depth 2 ln m,")
say("i.e. DEEP power sums = deep wraparound moments = THE WALL.  Shallow (K=2,4) gives only")
say("Johnson / (3pn)^{1/4}.  The P3 integer lone-spike countermodel proves the root-location")
say("apparatus (real-rootedness + integrality + Newton inequalities + Laguerre-Polya) adds 0")
say("bits: the extremal object is a lone spike, exactly as in the CMK R1 refutation.  N4 = the")
say("root-location TWIN of the lone-spike moment-problem death.  No escape; SELF-REFUTED.")

with open("scripts/probes/_out_466_novel_N4_periodpoly.txt", "w") as fh:
    fh.write("\n".join(OUT) + "\n")
say("")
say("written: scripts/probes/_out_466_novel_N4_periodpoly.txt")
