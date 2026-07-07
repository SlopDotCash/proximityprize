#!/usr/bin/env python3
"""probe_466_e2w4_orbit_census.py -- LANE W8 TASK B (issue #466): the e2BadScalarSet
full G-orbit census (the #464 landable leftover).

OBJECT.  For G = mu_n < F_p^* (proper subgroup, p = 1 mod n, p >= n^4):
    e2BadScalarSet(G, 4) = { -1/e1(S) : S in C(G,4), e2(S) = 0, e1(S) != 0 }
(exactly the Lean `E2DilationDirectCount.e2BadScalarSet` with
`e2 = (e1^2 - p2)/2`, `e1 = sum`, `p2 = sum of squares`).  The width-4 machinery
(`E2W4CyclotomicNonCollision.lean`) proved TWO-orbit refuters via the product
family quadT x t = {x, -x, x t, x/t} (bad scalar alpha = -(x(t+1/t))^{-1}); the
full census -- how many G-ORBITS the whole width-4 bad-scalar image decomposes
into as n grows -- was never computed.  This probe computes it EXACTLY.

METHOD.
  * All C(n,4) subsets of mu_n, vectorized mod p.  bad iff e2 = 0, e1 != 0.
  * alpha = -1/e1 is a bijection of e1, and alpha*mu_n = beta*mu_n iff
    alpha^n = beta^n (mu_n = full n-torsion since n | p-1).  So
        #distinct alpha  = #distinct e1 (mod p)   and
        K := #G-orbits   = #distinct e1^n (mod p).
  * Internal check (Lean theorem `e2BadScalarSet_card_eq_orbit_mul`, free
    action): #e2BadScalarSet = K * n exactly.
  * CHAR-0 GROUND TRUTH for the subset census: e2(S) = sum_{i<j} zeta^{a_i+a_j}
    in Z[zeta_n]; vanishing checked EXACTLY by reduction mod Phi_n(x) (integer
    arithmetic, no floats).  Char-p counts are accepted as the char-0 census
    only when (i) both generic primes agree and (ii) the char-p bad-subset
    count equals the char-0 bad-subset count (else the prime is flagged BAD).
  * Product-form sub-census: the product family's orbit labels are
    (-1)^n / c^n with c = t + 1/t, t in mu_n; K_prod = #distinct labels,
    compared against the combinatorial model Kmodel = n/4 - 1
    (`E2W4CyclotomicNonCollision` Part-2 commentary) and `_OPSingleOrbit`'s
    O_P = n/8 - 1.  K_extra = K_total - K_prod counts NON-product orbits
    (Lam-Leung 3+3 families can only occur when 3 | n; flagged).
  * Growth fit: least-squares slope of log K vs log n, cross-checked against
    the `_DstarGrowthLaw` reading (O_P(n,r) = Theta(n^{r-1}), D* = n*O_P):
    for the width-4 (r = 4) variety this predicts K = Theta(n^3) IF the full
    moment-variety dimension count applies, Theta(n) if only 1-parameter
    families (product form) exist.  The probe decides.

REGIME DISCIPLINE (#400 trap): p prime, p = 1 mod n, p >= n^4, mu_n PROPER,
never n = p-1, 2 generic primes per n, generalized-Fermat / power-of-two-m
primes flagged.

Run:  python scripts/probes/probe_466_e2w4_orbit_census.py
"""

import sys
import math
from itertools import combinations

import numpy as np

# ----------------------------------------------------------------------------
# number theory helpers
# ----------------------------------------------------------------------------

_MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factorize(n: int):
    fs = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        fs[n] = fs.get(n, 0) + 1
    return fs


def primitive_root(p: int) -> int:
    fac = list(factorize(p - 1).keys())
    g = 2
    while True:
        if all(pow(g, (p - 1) // r, p) != 1 for r in fac):
            return g
        g += 1


def is_generalized_fermat(p: int) -> bool:
    """p = a^{2^j} + 1 with 2^j >= 2 (includes Fermat primes)."""
    for e in (2, 4, 8, 16, 32):
        a = round((p - 1) ** (1.0 / e))
        for aa in (a - 1, a, a + 1):
            if aa >= 2 and aa ** e + 1 == p:
                return True
    return False


def prime_flags(p: int, n: int):
    flags = []
    if is_generalized_fermat(p):
        flags.append("GENERALIZED-FERMAT")
    m = (p - 1) // n
    if m & (m - 1) == 0:
        flags.append("m=2^k (X^{n/2}-correlated tower)")
    return flags


def primes_for(n: int, count: int):
    """First `count` NON-generalized-Fermat primes p >= n^4, p = 1 mod n."""
    out = []
    p = n ** 4
    p += (1 - p) % n
    while len(out) < count:
        if is_prime(p) and not is_generalized_fermat(p):
            out.append(p)
        p += n
    return out


# ----------------------------------------------------------------------------
# cyclotomic char-0 machinery (exact integer arithmetic)
# ----------------------------------------------------------------------------

def poly_divexact(num, den):
    """Exact division of integer polynomial lists (ascending coeffs)."""
    num = list(num)
    dd = len(den) - 1
    q = [0] * (len(num) - dd)
    for i in range(len(num) - 1, dd - 1, -1):
        c = num[i]
        if c == 0:
            continue
        assert c % den[-1] == 0
        f = c // den[-1]
        q[i - dd] = f
        for j, dc in enumerate(den):
            num[i - dd + j] -= f * dc
    assert all(v == 0 for v in num), "non-exact poly division"
    return q


_CYCLO_CACHE = {}


def cyclotomic(n: int):
    """Coefficients (ascending) of Phi_n(x), exact integers."""
    if n in _CYCLO_CACHE:
        return _CYCLO_CACHE[n]
    poly = [-1] + [0] * (n - 1) + [1]          # x^n - 1
    for d in range(1, n):
        if n % d == 0:
            poly = poly_divexact(poly, cyclotomic(d))
    _CYCLO_CACHE[n] = poly
    return poly


def reduction_table(n: int) -> np.ndarray:
    """M[k] = coefficient vector of x^k mod Phi_n(x), k = 0..n-1 (ints)."""
    phi = cyclotomic(n)
    deg = len(phi) - 1
    assert phi[-1] == 1
    M = np.zeros((n, deg), dtype=np.int64)
    cur = np.zeros(deg + 1, dtype=np.int64)
    cur[0] = 1
    for k in range(n):
        M[k] = cur[:deg]
        nxt = np.zeros(deg + 1, dtype=np.int64)
        nxt[1:] = cur[:deg]
        # reduce degree-deg term
        lead = cur[deg - 1]  # after shift, coefficient of x^deg is cur[deg-1]
        if lead != 0:
            for j in range(deg):
                nxt[j] -= lead * phi[j]
            nxt[deg] = 0
        else:
            nxt[deg] = 0
        cur = nxt
    return M


def char0_counts(n: int, quads: np.ndarray):
    """Exact char-0 census via Phi_n reduction (integer arithmetic).
    Returns (#{S : e2 = 0 in Z[zeta_n]}, #{S : e2 = 0 AND e1 = 0})."""
    M = reduction_table(n)
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    acc2 = np.zeros((quads.shape[0], M.shape[1]), dtype=np.int64)
    for (i, j) in pairs:
        acc2 += M[(quads[:, i] + quads[:, j]) % n]
    e2zero = (acc2 == 0).all(axis=1)
    del acc2
    acc1 = np.zeros((quads.shape[0], M.shape[1]), dtype=np.int64)
    for i in range(4):
        acc1 += M[quads[:, i] % n]
    e1zero = (acc1 == 0).all(axis=1)
    return int(e2zero.sum()), int((e2zero & e1zero).sum())


# ----------------------------------------------------------------------------
# char-p census
# ----------------------------------------------------------------------------

def modpow_vec(base: np.ndarray, e: int, p: int) -> np.ndarray:
    """base^e mod p, vectorized (values < p < 2^26 so int64-safe)."""
    r = np.ones_like(base)
    b = base % p
    while e > 0:
        if e & 1:
            r = (r * b) % p
        b = (b * b) % p
        e >>= 1
    return r


def census(n: int, p: int, quads: np.ndarray):
    m = (p - 1) // n
    g = primitive_root(p)
    h = pow(g, m, p)
    X = np.empty(n, dtype=np.int64)
    x = 1
    for k in range(n):
        X[k] = x
        x = x * h % p
    assert x == 1 and len(set(X.tolist())) == n, "mu_n enumeration broken"

    E = X[quads]                                   # (Q,4)
    e1 = E.sum(axis=1) % p
    p2 = (E * E % p).sum(axis=1) % p
    inv2 = pow(2, p - 2, p)
    e2 = ((e1 * e1 - p2) % p) * inv2 % p

    bad = (e2 == 0) & (e1 != 0)
    bad_e1zero = int(((e2 == 0) & (e1 == 0)).sum())
    nbad = int(bad.sum())

    e1bad = e1[bad]
    distinct_alpha = len(np.unique(e1bad))         # alpha = -1/e1 bijective
    labels = modpow_vec(e1bad, n, p)               # orbit label ~ e1^n
    K = len(np.unique(labels))

    # free-action check (Lean: #set = K * #G)
    free_ok = (distinct_alpha == K * n)

    # product-form sub-census (needs -1 in mu_n, i.e. n even):
    # quadT x t = {x,-x,xt,x/t}; e1 = x(t+1/t); label in the e1^n convention
    # is e1^n = c^n (x^n = 1), c = t + 1/t.
    prod_labels_e1 = set()
    if n % 2 == 0:
        for t in X.tolist():
            if t == 1 or t == p - 1:        # degenerate quadT (t^2 = 1)
                continue
            tinv = pow(int(t), p - 2, p)
            c = (t + tinv) % p
            if c == 0:
                continue
            prod_labels_e1.add(pow(int(c), n, p))
    K_prod = len(prod_labels_e1)
    all_labels = set(int(v) for v in np.unique(labels))
    prod_inside = prod_labels_e1 <= all_labels
    K_extra = K - len(all_labels & prod_labels_e1)

    # representatives of NON-product orbits (exponent quadruples)
    extra_reps = []
    if K_extra > 0:
        seen = set()
        bad_idx = np.nonzero(bad)[0]
        for bi, lab in zip(bad_idx.tolist(), labels.tolist()):
            if lab not in prod_labels_e1 and lab not in seen:
                seen.add(lab)
                extra_reps.append(tuple(quads[bi].tolist()))
                if len(extra_reps) >= 6:
                    break

    return dict(p=p, m=m, nbad=nbad, bad_e1zero=bad_e1zero,
                distinct_alpha=distinct_alpha, K=K, free_ok=free_ok,
                K_prod=K_prod, prod_inside=prod_inside, K_extra=K_extra,
                extra_reps=extra_reps, flags=prime_flags(p, n))


# ----------------------------------------------------------------------------
# driver
# ----------------------------------------------------------------------------

def char0_rep_check(n: int, rep):
    """Exact char-0 (e2 == 0?, e1 == 0?) for one exponent quadruple, via Phi_n."""
    M = reduction_table(n)
    deg = M.shape[1]
    acc2 = np.zeros(deg, dtype=np.int64)
    for i in range(4):
        for j in range(i + 1, 4):
            acc2 += M[(rep[i] + rep[j]) % n]
    acc1 = np.zeros(deg, dtype=np.int64)
    for i in range(4):
        acc1 += M[rep[i] % n]
    return bool((acc2 == 0).all()), bool((acc1 == 0).all())


def main():
    ns = [8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64]
    if len(sys.argv) > 1:
        ns = [int(a) for a in sys.argv[1:]]
    rows = []
    print("probe_466_e2w4_orbit_census -- width-4 e2BadScalarSet full G-orbit census")
    print(f"numpy {np.__version__}")
    for n in ns:
        quads = np.array(list(combinations(range(n), 4)), dtype=np.int64)
        c0_bad_all, c0_bad_e10 = char0_counts(n, quads)
        c0_bad = c0_bad_all - c0_bad_e10               # e2=0 & e1!=0 (char 0)
        runs = []
        for p in primes_for(n, 2):
            r = census(n, p, quads)
            runs.append(r)
        agree = (runs[0]["nbad"] == runs[1]["nbad"]
                 and runs[0]["K"] == runs[1]["K"]
                 and runs[0]["distinct_alpha"] == runs[1]["distinct_alpha"])
        char0_match = all(r["nbad"] == c0_bad for r in runs)
        kmodel = n // 4 - 1
        opmodel = n // 8 - 1
        rows.append((n, c0_bad, runs, agree, char0_match, kmodel, opmodel))
        f0 = ",".join(runs[0]["flags"]) or "-"
        f1 = ",".join(runs[1]["flags"]) or "-"
        print(f"\nn={n:3d}  C(n,4)={len(quads)}  char0: #bad(e2=0,e1!=0)={c0_bad} "
              f"(+{c0_bad_e10} with e1=0)")
        for r in runs:
            print(f"  p={r['p']:>10d} (m={r['m']}, flags={','.join(r['flags']) or '-'}): "
                  f"#bad={r['nbad']}  #alpha={r['distinct_alpha']}  "
                  f"K_orbits={r['K']}  free_action={'OK' if r['free_ok'] else 'FAIL'}  "
                  f"K_prod={r['K_prod']}(inside={r['prod_inside']})  K_extra={r['K_extra']}")
            for rep in r["extra_reps"]:
                z2, z1 = char0_rep_check(n, rep)
                print(f"      non-product orbit rep (exponents mod {n}): {rep}  "
                      f"char0-exact: e2==0 {z2}  e1==0 {z1}")
        v = "AGREE" if agree else "**PRIME-DISAGREE**"
        c = "char0-MATCH" if char0_match else "**CHAR-P EXCESS (bad prime?)**"
        print(f"  cross-prime: {v}; {c};  Kmodel=n/4-1={kmodel}  O_P-model=n/8-1={opmodel}  "
              f"3|n={'yes' if n % 3 == 0 else 'no'}")
        sys.stdout.flush()

    # ------------------------------------------------------------------
    # growth fit (use runs[0] K where cross-prime agrees and char0 matches)
    # ------------------------------------------------------------------
    print("\n" + "=" * 78)
    print("GROWTH TABLE (validated rows only)")
    print(f"{'n':>4s} {'#bad':>8s} {'K':>7s} {'K_prod':>7s} {'K_extra':>8s} "
          f"{'n/4-1':>6s} {'n/8-1':>6s} {'K/(n/4-1)':>10s} {'bad/n^3':>9s}")
    xs, ys, ybad = [], [], []
    for (n, c0_bad, runs, agree, char0_match, kmodel, opmodel) in rows:
        if not (agree and char0_match):
            print(f"{n:>4d}  -- excluded (disagreement) --")
            continue
        K = runs[0]["K"]
        print(f"{n:>4d} {runs[0]['nbad']:>8d} {K:>7d} {runs[0]['K_prod']:>7d} "
              f"{runs[0]['K_extra']:>8d} {kmodel:>6d} {opmodel:>6d} "
              f"{K / max(kmodel, 1):>10.3f} {runs[0]['nbad'] / n**3:>9.5f}")
        if K > 0:
            xs.append(math.log(n))
            ys.append(math.log(K))
            ybad.append(math.log(runs[0]["nbad"]))
    if len(xs) >= 3:
        xs_a, ys_a, yb_a = np.array(xs), np.array(ys), np.array(ybad)
        # fit on the top octave (largest half of n) to reduce small-n bias
        half = len(xs) // 2
        sK = np.polyfit(xs_a[half:], ys_a[half:], 1)[0]
        sB = np.polyfit(xs_a[half:], yb_a[half:], 1)[0]
        sK_all = np.polyfit(xs_a, ys_a, 1)[0]
        sB_all = np.polyfit(xs_a, yb_a, 1)[0]
        print(f"\nlog-log slope of K:    all-n {sK_all:+.3f}   top-half {sK:+.3f}")
        print(f"log-log slope of #bad: all-n {sB_all:+.3f}   top-half {sB:+.3f}")
        print("\nREADINGS: K bounded  -> slope ~ 0;   K = Theta(n) (product-only) -> ~1;")
        print("          K = Theta(n^2) (full moment-variety, D*-law analogue) -> ~2.")
    print("\nDone.")


if __name__ == "__main__":
    main()
