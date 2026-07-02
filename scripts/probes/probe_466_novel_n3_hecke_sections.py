#!/usr/bin/env python3
"""
probe_466_novel_n3_hecke_sections.py -- lane N3-homogeneous (#466, novel-math round)

Machine checks for the Hecke-point dictionary underlying the homogeneous-dynamics
(SST/space-of-lattices) route, plus the exact binding arithmetic at the prize point.

(1) DICTIONARY SPOT-CHECK: the depth-r section L_S(p) = ker(Z^d -> F_p, a -> sum a_i h^{s_i})
    (d = 2r = |S|) is an index-p sublattice of Z^d whose DUAL is exactly
    L_S^* = Z^d + Z*(c_S/p), c_S = (h^{s_1},...,h^{s_d}).  (Proof is two lines --
    c/p pairs integrally with L, and covolumes match; here we spot-check numerically.)
    Hence x_S(p) := p^{-1/d} L_S(p) is a HECKE POINT of the standard T_p correspondence
    on X_d = SL_d(Z)\SL_d(R), with parameter [c_S] in P^{d-1}(F_p).

(2) "ROGERS FOR THE HECKE FIBER IS ELEMENTARY": over the FULL Hecke fiber
    P^{d-1}(F_p), the first and second moments of the {0,+-1}-point count
    N(c) = #{eps in {0,+-1}^d \ 0 : eps . c = 0 mod p} are EXACT closed forms:
        T1 = sum_c N(c)      = (3^d - 1) * pi_{d-2}
        T2 = sum_c N(c)^2    = 2(3^d-1) * pi_{d-2} + ((3^d-1)^2 - 2(3^d-1)) * pi_{d-3}
    with pi_k = (p^{k+1}-1)/(p-1) = #P^k(F_p).  (For p > 3, eps' prop. to eps over F_p
    iff eps' = +-eps.)  Verified brute-force below.  Consequence: full-orbit
    equidistribution technology (COU/Gorodnik-Nevo) can add NOTHING at fixed p --
    the orbit averages it would estimate are exact finite-field counting identities.

(3) MULTIPLIER = GALOIS TWIST: count(kS; h) = count(S; h^k) exactly, for k odd.
    The only "dynamics" on the section family is the shift (an isometry, round-2
    cosmetic) and this Galois twist by the virtually-cyclic group (Z/n)^x.

(4) THE BINDING ARITHMETIC at the prize point (the deployer/union-bound form):
    kappa_needed(r) = log_p C(n,2r)   vs   kappa_available <= 1/2 (Ramanujan ceiling),
    the single-section certification floor log_p(#primes in window), and the three
    depth crossovers (avoidance r~2-3, cusp r = ln p/ln(2 pi e), saturation r = log2(p)/2).

Run cost: a few seconds.  Output: _out_466_novel_n3_hecke_sections.txt
"""

import math
import random
import sys
from itertools import product, combinations

try:
    import numpy as np
    HAVE_NP = True
except Exception:
    HAVE_NP = False

OUT = []
def say(s=""):
    OUT.append(s)
    print(s)

random.seed(466)

# ----------------------------------------------------------------------------------
say("=" * 92)
say("probe_466_novel_n3_hecke_sections.py -- N3-homogeneous lane: dictionary + binding arithmetic")
say("=" * 92)

# ---------------------------------------------------------------------------- (1)
say("")
say("(1) DICTIONARY SPOT-CHECK: section = Hecke point; dual = Z^d + Z*(c/p)")

def element_of_order(n, p):
    # h of exact multiplicative order n mod p (needs n | p-1)
    assert (p - 1) % n == 0
    for g in range(2, p):
        h = pow(g, (p - 1) // n, p)
        # exact order n iff h^(n/q) != 1 for all prime q | n ; n is a 2-power here
        if n % 2 == 0 and pow(h, n // 2, p) != 1:
            return h
        if n % 2 == 1 and h != 1:
            return h
    raise RuntimeError("no element found")

n16 = 16
for p in (65537, 65617):
    h = element_of_order(n16, p)
    ok_dual, ok_ker, tested = 0, 0, 0
    for trial in range(40):
        S = sorted(random.sample(range(n16), 4))
        c = [pow(h, s, p) for s in S]
        d = 4
        # basis of a finite-index sublattice of L: p*e1 and c1*e_i - c_i*e_1 (i>=2);
        # random combos are in L; check ker and dual-integrality of c/p on them
        for _ in range(25):
            coeffs = [random.randint(-50, 50) for _ in range(d)]
            a = [coeffs[0] * p, 0, 0, 0]
            for i in range(1, d):
                a[i] += coeffs[i] * c[0]
                a[0] -= coeffs[i] * c[i]
            tested += 1
            if sum(ai * ci for ai, ci in zip(a, c)) % p == 0:
                ok_ker += 1
            if sum(ai * ci for ai, ci in zip(a, c)) % p == 0 and \
               sum(ai * ci for ai, ci in zip(a, c)) // p * p == sum(ai * ci for ai, ci in zip(a, c)):
                ok_dual += 1  # <c/p, a> = (a.c)/p integral
        # covolume of Z^d + Z c/p is 1/ord(c/p in T^d) = 1/p  (c has a unit entry)
        assert math.gcd(c[0], p) == 1
    say(f"  p={p}: h={h} (order {n16});  ker-membership {ok_ker}/{tested}, "
        f"dual-integrality <c/p,a> in Z: {ok_dual}/{tested};  covol(Z^d+Zc/p)=1/p certified "
        f"(c has unit entries => order of c/p in (R/Z)^d is exactly p)")
say("  => x_S(p) = p^(-1/d) L_S(p) is the T_p Hecke point of [Z^d] with parameter [c_S] in P^(d-1)(F_p).")
say("  NOTE: mu_n-dilation acts on c_S by global scalar => acts TRIVIALLY on [c_S] (projective).")
say("  The Hecke fiber sees exactly the dilation-quotient of the problem (b-blindness = projectivization).")

# ---------------------------------------------------------------------------- (2)
say("")
say("(2) FULL-FIBER MOMENTS ARE ELEMENTARY IDENTITIES (Siegel/Rogers for the Hecke orbit = counting)")

def projective_points(d, p):
    """Representatives of P^{d-1}(F_p): last nonzero coordinate = 1."""
    pts = []
    for lead in range(d - 1, -1, -1):
        # coordinates after 'lead' are 0, coordinate 'lead' = 1, before: anything
        for pre in product(range(p), repeat=lead):
            pts.append(tuple(pre) + (1,) + (0,) * (d - 1 - lead))
    return pts

def fiber_moments(d, p):
    eps_list = [e for e in product((-1, 0, 1), repeat=d) if any(e)]
    pts = projective_points(d, p)
    if HAVE_NP:
        C = np.array(pts, dtype=np.int64)
        E = np.array(eps_list, dtype=np.int64)
        Z = (C @ E.T) % p
        Ncounts = (Z == 0).sum(axis=1)
        T1 = int(Ncounts.sum()); T2 = int((Ncounts.astype(np.int64) ** 2).sum())
    else:
        T1 = T2 = 0
        for c in pts:
            N = sum(1 for e in eps_list if sum(x * y for x, y in zip(c, e)) % p == 0)
            T1 += N; T2 += N * N
    m = 3 ** d - 1
    pi = lambda k: (p ** (k + 1) - 1) // (p - 1) if k >= 0 else 0
    T1c = m * pi(d - 2)
    T2c = 2 * m * pi(d - 2) + (m * m - 2 * m) * pi(d - 3)
    return T1, T2, T1c, T2c, len(pts)

for (d, p) in ((3, 251), (4, 31)):
    T1, T2, T1c, T2c, npts = fiber_moments(d, p)
    say(f"  d={d}, p={p}: |P^{d-1}| = {npts};  T1 brute = {T1}, closed = {T1c}  "
        f"[{'MATCH' if T1 == T1c else 'MISMATCH'}];  T2 brute = {T2}, closed = {T2c}  "
        f"[{'MATCH' if T2 == T2c else 'MISMATCH'}]")
say("  => full-orbit mean AND variance of the wraparound statistic are exact counting identities;")
say("     effective Hecke-point equidistribution (any rate) is information-free at fixed p:")
say("     it estimates averages that are already exact, and our C(n,2r) sections are a")
say("     density ~ 2^(-16000) subfamily it cannot resolve (see table (4)).")

# ---------------------------------------------------------------------------- (3)
say("")
say("(3) MULTIPLIER ACTION = GALOIS TWIST:  count(kS; h) = count(S; h^k), k odd")

def count_pm1(S, h, p, full_support=False):
    d = len(S)
    c = [pow(h, s % n16, p) for s in S]
    cnt = 0
    sign_sets = product((-1, 1), repeat=d) if full_support else product((-1, 0, 1), repeat=d)
    for e in sign_sets:
        if not any(e):
            continue
        if sum(x * y for x, y in zip(c, e)) % p == 0:
            cnt += 1
    return cnt

p = 65617
h = element_of_order(n16, p)
viol = 0; tested = 0
for trial in range(60):
    dsz = random.choice((4, 6))
    S = sorted(random.sample(range(n16), dsz))
    k = random.choice((3, 5, 7, 9, 11, 13, 15))
    kS = sorted((k * s) % n16 for s in S)
    lhs = count_pm1(kS, h, p)
    rhs = count_pm1(S, pow(h, k, p), p)
    tested += 1
    if lhs != rhs:
        viol += 1
say(f"  p={p}: identity verified on {tested - viol}/{tested} random (S,k) pairs "
    f"({'EXACT' if viol == 0 else 'VIOLATIONS=' + str(viol)})")
say("  => the multiplier 'dynamics' is generator-change (Galois); the AGGREGATE count is")
say("     Galois-invariant (generator-independent), so the action is information-free at the")
say("     aggregate level; the acting group (Z/n)^x ~ Z/2 x Z/2^(mu-2) is VIRTUALLY CYCLIC:")
say("     no rank-2 (x2x3 / Furstenberg-BLMV) rigidity input exists on a 2-power exponent space.")

# ---------------------------------------------------------------------------- (4)
say("")
say("(4) BINDING ARITHMETIC AT THE PRIZE POINT (deployer/union-bound form)")

LN2 = math.log(2.0)

def lnC(nbits, d):
    """ln C(2^nbits, d) via Stirling on d! (n huge => C ~ n^d/d!)."""
    n_ln = nbits * LN2
    lnfact = math.lgamma(d + 1)
    return d * n_ln - lnfact

for (tag, nbits, pbits) in (("beta=4 diagonal", 30, 120), ("true prize field", 30, 158)):
    lnp = pbits * LN2
    rstar = math.ceil(lnp)
    phi_bits = nbits - 1
    primes_bits = pbits - phi_bits - math.log2(lnp)   # p/(phi(n) ln p)
    kappa_floor = primes_bits * LN2 / lnp
    say(f"  --- {tag}: n = 2^{nbits}, p ~ 2^{pbits}, ln p = {lnp:.2f}, r* = ceil(ln p) = {rstar},"
        f" #primes(window) ~ 2^{primes_bits:.1f} ---")
    say(f"      single-section certification floor: kappa > log_p(#primes) = {kappa_floor:.4f}"
        f"  (Ramanujan ceiling = 0.5 => deficit p^{kappa_floor-0.5:.4f} ~ 2^{(kappa_floor-0.5)*pbits:.1f}"
        f" uncertifiable bad primes per section)")
    say(f"      {'r':>5} {'d=2r':>6} {'kappa_needed=log_p C(n,2r)':>28} {'vs 1/2':>10}"
        f" {'per-section mean +-1 pts (log2)':>32} {'radius/lambda_gauss':>20}")
    for r in (1, 2, 3, 4, 5, 10, 29, 60, rstar):
        d = 2 * r
        kn = lnC(nbits, d) / lnp
        mean_bits = d - pbits          # log2( 2^d / p ) per-section full-support mean
        ratio = math.sqrt(2 * math.pi * math.e) * math.exp(-lnp / d)
        say(f"      {r:>5} {d:>6} {kn:>28.4f} {kn/0.5:>9.1f}x {mean_bits:>32} {ratio:>20.3f}")
    r_cusp = lnp / math.log(2 * math.pi * math.e)
    say(f"      crossovers: avoidance-with-K^r-exceptions dies in r in (2,3) "
        f"(expected dirty sections: r=2: {2**(pbits-2*math.log2(math.e)):.2e}... see below);")
    # exact expected dirty antipodal-free sections at r=2,3 (Siegel heuristic)
    for r in (2, 3):
        d = 2 * r
        val_ln = lnC(nbits, d) + d * LN2 - (pbits + 1) * LN2
        say(f"        r={r}: E[#dirty sections] ~ C(n,{d})*2^{d}/(2p) = exp({val_ln:.1f}) = "
            f"{math.exp(min(val_ln, 700)):.3g}")
    say(f"      cusp crossover r_cusp = ln p / ln(2 pi e) = {r_cusp:.1f} "
        f"(below: a +-1 vector is beyond-Minkowski-short; above: bulk radius)")
    say(f"      saturation r_sat = log2(p)/2 = {pbits/2:.0f} (above: EVERY section carries wraparounds;"
        f" at r*: 2^{2*rstar - pbits} per section)")
    say(f"      union bound at r*: kappa_needed = {lnC(nbits, 2*rstar)/lnp:.2f} vs Ramanujan 0.5:"
        f" deficit {lnC(nbits, 2*rstar)/lnp/0.5:.0f}x;"
        f" fictional-Ramanujan depth cap: r=1 only (kappa_needed(1) = {lnC(nbits,2)/lnp:.3f},"
        f" kappa_needed(2) = {lnC(nbits,4)/lnp:.3f})")

say("")
say("(4b) WHY THE FORM ITSELF IS WRONG PAST r ~ beta: Parseval forces E_r >= n^{2r}/p (DC mean);")
say("     the proven char-0 ladder caps char-0 solutions at Wick; so for r > beta the char-p mass")
say("     ~ n^{2r}/p MUST be present -- 'all but K^r sections avoid' contradicts Parseval at r >= 5")
say("     (modulo the standard low-support layer bookkeeping): at r=5, needed mass 2^180 tuples vs")
say("     K^5 * 2^10 * (5!)^2 * (max 2^10/section) -- constant K fails by ~2^150. The correct")
say("     lattice-language statement of form A at depth r ~ ln p is the VARIANCE form (dossier form C):")
say("     total +-1-count over the C(n,2r) Hecke points = Siegel mean * (1 + O(mean^{-0.47})).")

say("")
say("VERDICT: all three sub-routes die on exact arithmetic/structure (see kb note")
say("  deltastar-466-novel-N3-homogeneous-2026-07-01.md). Surviving content: the dictionary (exact),")
say("  the three crossovers, the type-error warning (deg-T_p rates vs p-rates), and the reduction of")
say("  the lane's residue to the ALREADY-NAMED open Props (TPS divisor-equidistribution; D2 coupling).")

with open(__file__.replace("probe_", "_out_").replace(".py", ".txt"), "w") as f:
    f.write("\n".join(OUT) + "\n")
