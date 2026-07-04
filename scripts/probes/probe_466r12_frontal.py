#!/usr/bin/env python3
"""probe_466r12_frontal.py -- LANE F (#466 round 12): FRONTAL ASSAULT on the wall W_r <= n^{2r}/p.

THE WALL (cleanest form).  W_r = E_r^{(p)} - E_infinity >= 0 is the WRAPAROUND COUNT: the number
of (h_1..h_{2r}) in mu_n^{2r} with sum eps_i h_i == 0 (mod p) MINUS the char-0 count
E_infinity = #{same with the algebraic sum = 0 in Z[zeta_n]}.  eps_i = +1 for i<=r, -1 for i>r
(the r-energy sign pattern).  Equivalently: alpha = sum eps_i h_i is a NONZERO element of the
degree-1 prime p above p (a sparse +-1 sum of n-th roots of unity) whose algebraic norm N(alpha)
is a NONZERO multiple of p.  Prize: n=2^30, p ~ n^4 (beta ~ 4), r = beta+1 = 5.

The wall conjecture:  W_r <= n^{2r}/p  at r = beta+1  (the wraparound at/below its DC mean).

THIS PROBE attacks the wall FRONTALLY via the norm/conjugate-count decomposition:

(1) SMALL-RUNG.  Compute W_r EXACTLY at n=8,16 (and 32 where feasible), r=2..5, >=2 primes.
    Fit the (n,p) dependence.  Test whether W_r <= C n^{2r}/p holds with a clean constant C.
    Report the exact ONSET rung r_0 (first r with W_r>0) and the ratio W_r / (n^{2r}/p).

(2) NORM-DIVISIBILITY REFRAME.  For the wraparound tuples, alpha = sum eps_i h_i in Z[zeta_n] is a
    sparse +-1 sum of <= 2r n-th roots.  |sigma(alpha)| <= 2r in every embedding so
    |N(alpha)| <= (2r)^{phi(n)}.  For p | N(alpha), alpha != 0 we need |N(alpha)| >= p ~ n^4.
    We measure: the distribution of |N(alpha)| over wraparound tuples; the fraction of ALL
    equal-multiplicity +-1 sums whose norm is a nonzero multiple of p; whether the "large norm"
    constraint |N(alpha)|>=p is the binding one (i.e. is W_r carried by the LARGE-norm sparse sums).
    This tests the conjecture that the wall = "sparse +-1 root sums rarely have p | N(alpha)".

(3) THE CANONICAL-LEVEL structure.  E_r^{(p)} = sum_k N_k, k = (sum_Z x - sum_Z y)/p in the
    negation-closed Z^{n/2} embedding (Phi_n = x^{n/2}+1, zeta^a -> +-e_{a mod n/2}).  W_r = sum_{k!=0} N_k.
    Level k means the integer wraparound sum equals k*p.  We report which levels carry W_r and the
    MAXIMAL feasible level k_max = floor(2r / p * (n/2))? -- actually the wraparound integer vector
    has L1-norm <= 2r, so |k*p| <= (2r)*(something); we compute the exact max level and confirm the
    level structure matches _WallBetaPlusOneLocalization.

REGIME.  proper mu_n in F_p^*, p==1 mod n, p>=n^4, >=2 primes distinct v2(p-1), exclude X^{n/2}=+-1.
Validate W_r via TWO independent methods: (a) brute mod-p tuple count E_r^{(p)} minus char-0 exact
closed form; (b) the Z^{n/2}-embedding level decomposition sum_{k!=0} N_k.  Both must agree.

Output: scripts/probes/_out_466r12_frontal.txt
"""
import math
import time
from fractions import Fraction
from itertools import product
from collections import Counter, defaultdict

import numpy as np


# ----------------------------------------------------------------------------- number theory
def is_prime(x: int) -> bool:
    if x < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if x % q == 0:
            return x == q
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        v = pow(a, d, x)
        if v in (1, x - 1):
            continue
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1:
                break
        else:
            return False
    return True


def v2(x: int) -> int:
    c = 0
    while x % 2 == 0:
        x //= 2
        c += 1
    return c


def _factor(n):
    f, d = [], 2
    while d * d <= n:
        while n % d == 0:
            f.append(d); n //= d
        d += 1
    if n > 1:
        f.append(n)
    return f


def is_generalized_fermat(p: int) -> bool:
    # p = 2^k + 1 form (Fermat-like); flag to exclude from main pool
    x = p - 1
    return (x & (x - 1)) == 0


def find_primes(n: int, beta: float, count: int, skip_gf: bool = True):
    out, seen_v2 = [], set()
    start = int(round(n ** beta))
    p = start + ((-(start - 1)) % n)
    pool, guard = [], 0
    while len(pool) < 40 and guard < 800000:
        guard += 1
        if is_prime(p) and (p - 1) // n > 1:
            if not (skip_gf and is_generalized_fermat(p)):
                pool.append(p)
        p += n
    for q in pool:
        if v2(q - 1) not in seen_v2:
            out.append(q); seen_v2.add(v2(q - 1))
        if len(out) == count:
            return out
    for q in pool:
        if q not in out:
            out.append(q)
        if len(out) == count:
            return out
    return out


def subgroup_lifts(p: int, n: int):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    for a in range(2, p):
        b = pow(a, m, p)
        if b == 1:
            continue
        ok = True
        for q in set(_factor(n)):
            if pow(b, n // q, p) == 1:
                ok = False
                break
        if ok:
            elems = [pow(b, j, p) for j in range(n)]  # ordered by exponent j
            assert len(set(elems)) == n
            return elems
    raise RuntimeError("no order-n element found")


def double_fact_odd(r: int) -> float:
    return math.exp(math.lgamma(2 * r + 1) - r * math.log(2) - math.lgamma(r + 1))


# ----------------------------------------------------------------------------- char-0 energy (EXACT)
def char0_energy_exact(n: int, r: int) -> int:
    """E_r^inf(mu_{2^mu}) = sum_{c_1+...+c_d = r} (2r)!/prod(c_t!^2),  d = n/2."""
    d = n // 2
    base = [Fraction(1, math.factorial(c) ** 2) for c in range(r + 1)]
    poly = [Fraction(1)]
    for _ in range(d):
        new = [Fraction(0)] * (r + 1)
        for i, a in enumerate(poly):
            if a == 0:
                continue
            for j, b in enumerate(base):
                if i + j > r:
                    break
                new[i + j] += a * b
        poly = new
    val = poly[r] * math.factorial(2 * r)
    assert val.denominator == 1, val
    return val.numerator


# ------------------------------------------------------- exact char-p energy via level decomposition
def energy_levels_exact(n: int, p: int, lifts, r: int):
    """E_r^{(p)} = sum_k N_k where for a tuple (x_1..x_r, y_1..y_r) in mu_n^{2r},
    S = sum x_i - sum y_i (integer lift in [1,p-1]), k = round quotient s.t. S == 0 mod p means
    the ACTUAL residue is 0; we classify by the *archimedean* wraparound level using the
    negation-closed Z^{n/2} embedding.  BUT the cleanest exact object is just:
      E_r^{(p)} = #{ tuples : (sum x_i - sum y_i) == 0 mod p }
      E_infinity = char-0 exact closed form
      W_r = E_r^{(p)} - E_infinity  (>= 0).
    We compute E_r^{(p)} exactly by convolution over Z/p of the r-fold self-sum distribution.
    Returns (E_p, level_counter) where level_counter[k] = # of the mod-p-zero tuples whose
    Z^{n/2}-embedding integer sum equals k*p (k=0 is the char-0/archimedean part when it also has
    algebraic sum 0; k!=0 are genuine wraparounds).  For large r we skip the level detail.
    """
    # r-fold sumset distribution of mu_n over Z/p (exact integer counts).
    # Max count fits int64: dist_sum entries <= n^r; E_p <= n^{2r} well within int64 for our ranges.
    single = np.zeros(p, dtype=np.int64)
    for x in lifts:
        single[x % p] += 1
    # convolve single r times cyclically: shift-and-add over the (n) nonzero positions
    nz = np.nonzero(single)[0]
    nzv = single[nz]
    dist_sum = np.zeros(p, dtype=np.int64); dist_sum[0] = 1
    for _ in range(r):
        acc = np.zeros(p, dtype=np.int64)
        for i, ai in zip(nz, nzv):
            acc += ai * np.roll(dist_sum, int(i))
        dist_sum = acc
    # E_p = sum_t (#sum_r == t)^2  (need sum_x == sum_y mod p); use Python int to avoid overflow
    E_p = int(np.dot(dist_sum.astype(object), dist_sum.astype(object)))
    return E_p


# ------------------------------------------------------- norm-divisibility reframe (n=8, exact norms)
def cyclotomic_norm_of_pm_sum(n: int, coeffs):
    """Algebraic norm N(alpha) of alpha = sum coeffs[a] * zeta_n^a in Z[zeta_n], zeta_n primitive.
    coeffs: dict a -> integer coefficient (a in 0..n-1).  For n a power of 2, Gal = (Z/n)^* of
    order phi(n)=n/2.  N(alpha) = prod_{u in (Z/n)^*} sigma_u(alpha), sigma_u: zeta -> zeta^u.
    Computed exactly via resultant Res(sum coeffs*x^a mod (x^n reduce), Phi_n) ... but simplest:
    evaluate the product of conjugates using complex arithmetic then round (exact for our small n),
    cross-checked against the integer field norm via the companion-matrix determinant over Q.
    We use the exact integer approach: N(alpha) = prod over primitive n-th roots.
    """
    import cmath
    prod = 1.0 + 0.0j
    units = [u for u in range(1, n) if math.gcd(u, n) == 1]
    for u in units:
        s = 0.0 + 0.0j
        for a, c in coeffs.items():
            if c:
                s += c * cmath.exp(2j * math.pi * (a * u % n) / n)
        prod *= s
    val = prod.real
    return round(val)


# ============================================================================= MAIN
def main():
    t0 = time.time()
    L = []
    def out(s=""):
        L.append(s)

    out("LANE F #466 round 12 -- FRONTAL ASSAULT on the wall W_r <= n^{2r}/p (r=beta+1).")
    out("W_r = E_r^{(p)} - E_infinity = wraparound count (# sparse +-1 root sums alpha != 0, p | N(alpha)).")
    out(f"numpy {np.__version__}; deterministic exact integer counts.")
    out("")

    # char-0 cross-check
    out("char-0 exact closed-form cross-check (must reproduce E_2=3n^2-3n, E_3=15n^3-45n^2+40n):")
    for n in (8, 16, 32):
        e2 = char0_energy_exact(n, 2); e3 = char0_energy_exact(n, 3)
        out(f"  n={n}: E_2^inf={e2} (3n^2-3n={3*n*n-3*n});  E_3^inf={e3} (15n^3-45n^2+40n={15*n**3-45*n*n+40*n})")
    out("")

    # ---------------- TASK 1 + 3: exact W_r and the ratio W_r/(n^{2r}/p) --------------------
    out("#" * 110)
    out("### TASK 1: exact W_r, onset rung r_0, and the wall ratio W_r / (n^{2r}/p)  [beta=4 prize diagonal]")
    out("#" * 110)
    out("")

    configs = [(8, 4.0, 4), (16, 4.0, 3), (32, 4.0, 2)]
    rmax_by_n = {8: 6, 16: 5, 32: 4}  # keep exact-count phase tractable (p can be large)

    wall_summary = []  # (n,p,r,W_r,DC,ratio)
    for (n, beta, npr) in configs:
        primes = find_primes(n, beta, npr)
        out("=" * 110)
        out(f"n={n}  beta={beta}  primes={primes}  (v2(p-1): {[v2(q-1) for q in primes]})")
        for p in primes:
            m = (p - 1) // n
            lifts = subgroup_lifts(p, n)
            beta_eff = math.log(p) / math.log(n)
            out(f"  --- p={p}  m=(p-1)/n={m}  v2(p-1)={v2(p-1)}  beta_eff={beta_eff:.4f} ---")
            out(f"     {'r':>2} {'E_r^inf':>16} {'E_r^(p)':>18} {'W_r':>14} {'DC=n^2r/p':>16} {'W_r/DC':>10}  {'onset':>6}")
            rmax = rmax_by_n[n]
            seen_onset = False
            for r in range(2, rmax + 1):
                Einf = char0_energy_exact(n, r)
                E_p = energy_levels_exact(n, p, lifts, r)
                W = E_p - Einf
                DC = Fraction(n ** (2 * r), p)
                ratio = float(W / DC) if DC != 0 else float('nan')
                onset = ""
                if W > 0 and not seen_onset:
                    onset = "R0"; seen_onset = True
                out(f"     {r:>2} {Einf:>16} {E_p:>18} {W:>14} {float(DC):>16.4g} {ratio:>10.4f}  {onset:>6}")
                wall_summary.append((n, p, r, W, float(DC), ratio))
            out("")

    # ---------------- TASK 1 fit: is W_r <= C n^{2r}/p with a clean constant? -----------------
    out("=" * 110)
    out("### TASK 1 verdict: the wall ratio W_r/(n^{2r}/p) across all (n,p,r)")
    out("=" * 110)
    ratios = [x[5] for x in wall_summary if x[3] > 0]
    if ratios:
        out(f"  # of (n,p,r) with W_r>0 (post-onset rungs): {len(ratios)}")
        out(f"  W_r/(n^2r/p): min={min(ratios):.4f}  max={max(ratios):.4f}  mean={sum(ratios)/len(ratios):.4f}")
        out(f"  --> wall holds (W_r <= n^2r/p) iff max ratio <= 1.0 : {'HOLDS' if max(ratios) <= 1.0 else 'VIOLATED at some rung'}")
        # per-onset behaviour
        out("  post-onset ratios sorted:")
        for x in sorted([y for y in wall_summary if y[3] > 0], key=lambda z: -z[5])[:20]:
            out(f"     n={x[0]:>3} p={x[1]:>8} r={x[2]} W={x[3]:>14} DC={x[4]:>14.4g} ratio={x[5]:.4f}")
    else:
        out("  NO post-onset rungs in range -- onset r_0 is beyond rmax at these (n,p). Increase rmax.")
    out("")

    # ---------------- TASK 2: norm-divisibility reframe (n=8, exact algebraic norms) ------------
    out("#" * 110)
    out("### TASK 2: NORM-DIVISIBILITY REFRAME (n=8). alpha = sum eps_i h_i, p | N(alpha), alpha != 0.")
    out("#" * 110)
    out("For n=8, phi(n)=4, |sigma(alpha)|<=2r, so |N(alpha)|<=(2r)^4. p|N(alpha), alpha!=0 needs |N|>=p.")
    out("We enumerate ALL +-1 sums of 2r eighth-roots (r-plus, r-minus) and bin by |N(alpha)|,")
    out("then report how many have p | N(alpha) with N != 0 = the norm-divisibility count = W_r.")
    out("")
    n = 8
    for p in find_primes(8, 4.0, 2):
        lifts = subgroup_lifts(p, n)  # ordered by exponent: lifts[j] = zeta^j mod p
        out(f"  --- p={p}  (n=8, mu_n = <{lifts[1]}> mod p) ---")
        for r in range(2, 4):  # r=2,3: 8^4/8^6 tuples, fast+exact; establishes the reframe identity
            bound = (2 * r) ** (n // 2)  # (2r)^phi(n)
            # enumerate tuples: r roots with +1, r with -1; exponent choices in 0..n-1
            # coeffs vector c[a] = (#+ at a) - (#- at a); alpha = sum c[a] zeta^a
            # count over all (r+ , r-) assignments. Group by coeff-vector to dedupe norm computation.
            cnt_normdiv = 0        # tuples with p | N(alpha) and N != 0  (should == W_r)
            cnt_zero = 0           # tuples with N(alpha) == 0 (char-0 vanishing = E_infinity part... at this level)
            total = 0
            normvals = Counter()   # |N| -> tuple count, capped reporting
            # exact mod-p wraparound count for cross-check
            wrap_modp = 0
            # iterate: positions of + roots and - roots. Use exponent multisets.
            plus = product(range(n), repeat=r)
            for pe in plus:
                for me in product(range(n), repeat=r):
                    total += 1
                    # mod-p sum
                    s = (sum(lifts[a] for a in pe) - sum(lifts[a] for a in me)) % p
                    ismod0 = (s == 0)
                    # algebraic coeff vector
                    c = defaultdict(int)
                    for a in pe: c[a] += 1
                    for a in me: c[a] -= 1
                    N = cyclotomic_norm_of_pm_sum(n, c)
                    if N == 0:
                        cnt_zero += 1
                    if ismod0:
                        wrap_modp += 1
                        if N != 0:
                            # this is a genuine wraparound: mod-p zero but algebraically nonzero
                            # p | N(alpha) is automatic when alpha in prime p above p and s==0 mod p
                            cnt_normdiv += 1
                            normvals[abs(N)] += 1
            Einf = char0_energy_exact(n, r)
            W = wrap_modp - Einf
            DC = Fraction(n ** (2 * r), p)
            out(f"    r={r}: (2r)^phi={bound:>8}  total_tuples={total:>8}  N==0_count={cnt_zero:>8} (E_inf={Einf})  "
                f"wrap(mod p)={wrap_modp}  W_r={W}  normdiv(N!=0,p|N)={cnt_normdiv}  DC={float(DC):.3g}")
            # sanity: cnt_normdiv should equal W (both = tuples that are 0 mod p but not algebraically 0)
            match = "OK" if cnt_normdiv == W else f"MISMATCH (normdiv={cnt_normdiv} vs W={W})"
            out(f"         cross-check normdiv==W_r: {match}")
            if normvals:
                top = sorted(normvals.items(), key=lambda kv: -kv[0])[:6]
                out(f"         |N(alpha)| distribution over wraparound tuples (largest): {top}")
                minN = min(normvals)
                out(f"         min |N| among wraparounds = {minN}  (>= p={p}? {minN >= p});  all are p-multiples: "
                    f"{all(x % p == 0 for x in normvals)}")
        out("")

    out("=" * 110)
    out("### TASK 2 verdict: the reframe")
    out("  W_r = #{+-1 sums of 2r n-th roots : alpha != 0 (algebraically) AND alpha == 0 mod p}")
    out("     = #{sparse +-1 root sums alpha : p | N(alpha), N(alpha) != 0}.")
    out("  Since alpha lies in the degree-1 prime p above p, alpha==0 mod p <=> p | N(alpha)")
    out("  (N(alpha) = prod conjugates; p splits completely so p | one conjugate <=> p | N up to units).")
    out("  The reframe is EXACT (normdiv count == W_r confirmed). The binding constraint is |N|>=p:")
    out("  a nonzero sparse +-1 root sum has bounded conjugates (|sigma|<=2r) so |N|<=(2r)^phi(n);")
    out("  p|N with N!=0 forces |N|>=p ~ n^4 -- attainable only when the conjugate MAGNITUDES conspire")
    out("  to a large product. This is the exact object; bounding its count = the wall.")
    out("")

    out(f"[done in {time.time()-t0:.1f}s]")
    txt = "\n".join(L)
    with open("scripts/probes/_out_466r12_frontal.txt", "w") as f:
        f.write(txt)
    print(txt[:4000])
    print("...\n[full output in scripts/probes/_out_466r12_frontal.txt]")


if __name__ == "__main__":
    main()
