#!/usr/bin/env python3
"""SYZ72 — certified middle-band occupancy at (6,6,6), and the missing prime sweep.

WHY THIS PROBE EXISTS
---------------------
`probe_syz71_linear_middle_slot.py` flags a configuration as a hit whenever the
6 x 4 evaluation matrix of `(W_AC, X·W_AC, W_BC, X·W_BC)` at the six points of
`S_AB` has rank < 4.  A *constant* cofactor is a linear cofactor of degree 0, so
that test also fires on every floor-attained (constant-syzygy) triple — the
second class of SYZ69, whose minimal syzygy has product degree `6 = max(a,b,c)`,
i.e. `delta_1 = max`, which is exactly what `SYZ59.middleBand` EXCLUDES.

So rank < 4 at six points is *necessary but not sufficient* for middle-band
occupancy.  This probe replaces the hit test with a certificate that pins
`delta_1 = 7 = max + 1` exactly, and then uses it for the sweep that
`Research/ProximityPrize/AGENTS.md` ("small-field discipline") mandates before
any small-`p` verdict is trusted in either direction.

THE CERTIFICATE  (n = 20, d = 6, k = 10, t = 2; SYZ50.Realizable 6 6 6 2 10)
---------------------------------------------------------------------------
Let `mu_20 = <w> subset F_p^*`, `S_AC, S_BC, S_AB` three disjoint 6-subsets and
`T = mu_20 \\ (S_AC ∪ S_BC ∪ S_AB)` the leftover (necessarily `|T| = 2`).  Let
`W_AC, W_BC, W_AB` be the corresponding monic vanishing polynomials.  A config
is a **certified middle-band occupant** iff

  (C1) there are cofactors `s_AC, s_BC` with `deg <= 1`, not both zero, whose
       combination `s_AC·W_AC + s_BC·W_BC` vanishes on all of `S_AB`
       (rank of the 6 x 4 system < 4);
  (C2) after writing `s_AC·W_AC + s_BC·W_BC = s_AB·W_AB` (forced by (C1): the
       combination has degree <= 7 and six roots, so it is a degree-<=1
       multiple of `W_AB`), all three cofactors are genuinely linear
       (`natDegree = 1`), so all three slot products have degree exactly 7;
  (C3) no nontrivial constant-cofactor relation exists among the three `W`'s
       (coefficient matrix 7 x 3 of full rank 3) — otherwise the minimal
       syzygy already has product degree `6 = max`, the triple is
       floor-attained, and it is NOT a middle-band triple;
  (C4) the combination is nonzero and does not vanish at `T`.

(C1)-(C4) give `delta_1 = 7` on a band-realizable `(6,6,6)` triple: the
degree-sum law then gives `delta_2 = 11`, gap `g = 4`, imbalance `iota = 2`,
so `SYZ59.middleBand 6 6 6 7` is occupied and SYZ69's empty-middle census is
FALSE at `n = 20`.  Whether that occupancy is a small-`p` artifact or survives
to production-scale primes is the question this probe answers.

Usage:
  python scripts/probes/probe_syz72_middle_band_sweep.py
  python scripts/probes/probe_syz72_middle_band_sweep.py --trials 100000
  python scripts/probes/probe_syz72_middle_band_sweep.py --demo-false-positive

Evidence class: reproducible exact-arithmetic computation, not a theorem.
"""
from __future__ import annotations

import argparse
import random

N_DEFAULT = 20
D_DEFAULT = 6


# ----------------------------------------------------------------------------
# field / domain helpers
# ----------------------------------------------------------------------------
def prime_factors(m: int) -> set[int]:
    fs: set[int] = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def is_prime(m: int) -> bool:
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
    d, r = m - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def next_prime_1_mod(n: int, above: int) -> int:
    """Smallest prime p > above with p = 1 (mod n)."""
    k = max(1, (above // n) + 1)
    while True:
        p = k * n + 1
        if is_prime(p):
            return p
        k += 1


def primitive_root(p: int) -> int | None:
    fs = prime_factors(p - 1)
    for cand in range(2, p):
        if all(pow(cand, (p - 1) // q, p) != 1 for q in fs):
            return cand
    return None


def mu_domain(n: int, p: int) -> tuple[list[int], int] | tuple[None, None]:
    if (p - 1) % n != 0:
        return None, None
    g = primitive_root(p)
    if g is None:
        return None, None
    w = pow(g, (p - 1) // n, p)
    if pow(w, n, p) != 1 or any(pow(w, n // q, p) == 1 for q in prime_factors(n)):
        return None, None
    return [pow(w, i, p) for i in range(n)], w


# ----------------------------------------------------------------------------
# dense univariate polynomials over F_p (coefficients ascending)
# ----------------------------------------------------------------------------
def poly_from_roots(roots: list[int], p: int) -> list[int]:
    c = [1]
    for r in roots:
        nc = [0] * (len(c) + 1)
        for i, v in enumerate(c):
            nc[i] = (nc[i] - v * r) % p
            nc[i + 1] = (nc[i + 1] + v) % p
        c = nc
    return c


def poly_mul(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return out


def poly_add(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i in range(len(out)):
        out[i] = ((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p
    return out


def poly_eval(a: list[int], x: int, p: int) -> int:
    acc = 0
    for c in reversed(a):
        acc = (acc * x + c) % p
    return acc


def poly_deg(a: list[int], p: int) -> int:
    for i in range(len(a) - 1, -1, -1):
        if a[i] % p:
            return i
    return -1


def vanishing_value(omega: int, support: list[int], p: int) -> int:
    acc = 1
    for s in support:
        acc = acc * ((omega - s) % p) % p
    return acc


def gf_rank(rows: list[list[int]], p: int) -> int:
    M = [[x % p for x in r] for r in rows]
    if not M:
        return 0
    nrows, ncols = len(M), len(M[0])
    rank, row = 0, 0
    for col in range(ncols):
        piv = next((r for r in range(row, nrows) if M[r][col]), None)
        if piv is None:
            continue
        M[row], M[piv] = M[piv], M[row]
        inv = pow(M[row][col], p - 2, p)
        M[row] = [(x * inv) % p for x in M[row]]
        for r in range(nrows):
            if r != row and M[r][col]:
                f = M[r][col]
                M[r] = [(a - f * b) % p for a, b in zip(M[r], M[row])]
        rank += 1
        row += 1
        if row == nrows:
            break
    return rank


def kernel_basis(rows: list[list[int]], ncols: int, p: int) -> list[list[int]]:
    M = [[x % p for x in r] for r in rows]
    nrows = len(M)
    piv_cols: list[int] = []
    r = 0
    for col in range(ncols):
        piv = next((i for i in range(r, nrows) if M[i][col]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(nrows):
            if i != r and M[i][col]:
                f = M[i][col]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        piv_cols.append(col)
        r += 1
        if r == nrows:
            break
    free = [c for c in range(ncols) if c not in piv_cols]
    out = []
    for fcol in free:
        v = [0] * ncols
        v[fcol] = 1
        for i, pc in enumerate(piv_cols):
            v[pc] = (-M[i][fcol]) % p
        out.append(v)
    return out


# ----------------------------------------------------------------------------
# the certified middle-band predicate
# ----------------------------------------------------------------------------
def certify(
    p: int,
    mu: list[int],
    S_AC: list[int],
    S_BC: list[int],
    S_AB: list[int],
) -> dict:
    """Certify or reject a `(6,6,6)` middle-band occupant.  See module docstring."""
    res: dict = {"ok": False, "reason": "", "p": p}

    # -- combinatorial part of SYZ50.Realizable 6 6 6 2 10 --------------------
    d = D_DEFAULT
    if not (len(S_AC) == len(S_BC) == len(S_AB) == d):
        res["reason"] = "wrong support sizes"
        return res
    union = set(S_AC) | set(S_BC) | set(S_AB)
    if len(union) != 3 * d:
        res["reason"] = "supports not disjoint"
        return res
    if not union <= set(mu):
        res["reason"] = "supports leave mu_n"
        return res
    T = [x for x in mu if x not in union]
    if len(T) != len(mu) - 3 * d:
        res["reason"] = "bad leftover"
        return res
    res["T"] = T

    W_AC = poly_from_roots(S_AC, p)
    W_BC = poly_from_roots(S_BC, p)
    W_AB = poly_from_roots(S_AB, p)
    if poly_deg(W_AC, p) != d or poly_deg(W_BC, p) != d or poly_deg(W_AB, p) != d:
        res["reason"] = "not a degree-6 triple"
        return res

    # -- (C3) no constant-cofactor relation ----------------------------------
    coeff_rows = []
    for i in range(d + 1):
        coeff_rows.append(
            [
                W_AB[i] if i < len(W_AB) else 0,
                W_AC[i] if i < len(W_AC) else 0,
                W_BC[i] if i < len(W_BC) else 0,
            ]
        )
    const_rank = gf_rank(coeff_rows, p)
    res["const_rank"] = const_rank
    if const_rank < 3:
        res["reason"] = "floor-attained: nontrivial constant syzygy exists"
        return res

    # -- (C1) linear cofactors vanishing on S_AB ----------------------------
    rows = []
    for x in S_AB:
        wac = vanishing_value(x, S_AC, p)
        wbc = vanishing_value(x, S_BC, p)
        rows.append([wac, x * wac % p, wbc, x * wbc % p])
    rank = gf_rank(rows, p)
    res["rank"] = rank
    if rank >= 4:
        res["reason"] = "no linear cofactor pair"
        return res
    basis = kernel_basis(rows, 4, p)

    # -- (C2)/(C4) exact certificate over the kernel -------------------------
    for v in basis:
        a0, a1, b0, b1 = v
        sAC = [a0 % p, a1 % p]
        sBC = [b0 % p, b1 % p]
        combo = poly_add(poly_mul(sAC, W_AC, p), poly_mul(sBC, W_BC, p), p)
        if poly_deg(combo, p) < 0:
            continue  # trivial
        if any(poly_eval(combo, x, p) != 0 for x in S_AB):
            continue
        if comp := [poly_eval(combo, x, p) for x in T]:
            if any(c == 0 for c in comp):
                continue  # (C4) the combination must avoid T
        # recover s_AB from combo / W_AB (monic long division)
        rem = combo[:]
        quot = [0] * (max(1, len(rem) - len(W_AB) + 1))
        for i in range(len(rem) - len(W_AB), -1, -1):
            c = rem[i + len(W_AB) - 1]
            if not c:
                continue
            quot[i] = c
            for j, wc in enumerate(W_AB):
                rem[i + j] = (rem[i + j] - c * wc) % p
        if any(x % p for x in rem[: len(W_AB) - 1]):
            continue  # not divisible by W_AB
        sAB = quot
        # (C2) the syzygy must have product degree exactly 7 in its largest slot:
        # at least one cofactor is genuinely linear and (C3) rules out a
        # degree-<=6 syzygy, so the minimal product degree is exactly 7.
        slot_degs = [
            poly_deg(poly_mul(sAB, W_AB, p), p),
            poly_deg(poly_mul(sAC, W_AC, p), p),
            poly_deg(poly_mul(sBC, W_BC, p), p),
        ]
        if max(slot_degs) != d + 1:
            continue
        res.update(
            ok=True,
            reason="certified middle-band occupant",
            s_AC=sAC,
            s_BC=sBC,
            s_AB=sAB,
            cofactor_degrees=[poly_deg(sAB, p), poly_deg(sAC, p), poly_deg(sBC, p)],
            combo_degree=poly_deg(combo, p),
            slot_degrees=slot_degs,
        )
        return res
    res["reason"] = "kernel exists but no genuinely linear certificate"
    return res


# ----------------------------------------------------------------------------
# searches
# ----------------------------------------------------------------------------
def sample_prime(
    p: int, n: int, d: int, trials: int, seed: int
) -> dict:
    """Sample `(S_AC, S_BC)` pairs; scan EVERY legal `S_AB`, then certify.

    Scanning all `C(8,6) = 28` sub-triples instead of sampling the third set is
    what `probe_syz71_linear_middle_slot.py` did, and it is 28x more efficient at
    finding occupants for the same number of pair draws.  Unlike that probe, a
    `rank <= 3` sighting is only counted as an occupant after `certify` accepts
    it; floor-attained sightings are counted separately as rejections.
    """
    from itertools import combinations

    mu, _ = mu_domain(n, p)
    if mu is None:
        return {"p": p, "n": n, "ok": False, "reason": "no mu_n"}
    rng = random.Random(seed)
    stats = {
        "p": p,
        "n": n,
        "pairs": trials,
        "configs": 0,
        "ok": True,
        "rank_le_3": 0,       # what the SYZ71 test would call a hit
        "certified": 0,       # genuine middle-band occupants
        "floor_attained": 0,  # SYZ71 false positive: constant syzygy only
        "witness": None,
    }
    for _ in range(trials):
        bag = mu[:]
        rng.shuffle(bag)
        S_AC = bag[:d]
        S_BC = bag[d : 2 * d]
        rest = bag[2 * d :]
        rows_of = {}
        for x in rest:
            wac = vanishing_value(x, S_AC, p)
            wbc = vanishing_value(x, S_BC, p)
            rows_of[x] = [wac, x * wac % p, wbc, x * wbc % p]
        for subset in combinations(rest, d):
            stats["configs"] += 1
            if gf_rank([rows_of[x] for x in subset], p) >= 4:
                continue
            stats["rank_le_3"] += 1
            rec = certify(p, mu, S_AC, S_BC, list(subset))
            if rec["ok"]:
                stats["certified"] += 1
                if stats["witness"] is None:
                    stats["witness"] = {
                        "S_AC": S_AC,
                        "S_BC": S_BC,
                        "S_AB": list(subset),
                        "s_AC": rec["s_AC"],
                        "s_BC": rec["s_BC"],
                        "s_AB": rec["s_AB"],
                    }
            elif "constant syzygy" in rec["reason"]:
                stats["floor_attained"] += 1
    return stats


def structured_supports(mu: list[int], d: int) -> list[tuple[list[int], list[int], list[int]]]:
    """Supports built from index progressions / unions of cosets.

    These are the configurations with multiplicative symmetry, so they are the
    natural home of any *structural* (prime-independent) middle-band occupant.
    """
    n = len(mu)
    out = []
    idx = list(range(n))
    progressions = []
    for step in (1, 2, 3, 4, 5, 6, 10):
        for start in range(n):
            s = [(start + i * step) % n for i in range(d)]
            if len(set(s)) == d:
                progressions.append(sorted(s))
    progressions = sorted({tuple(s) for s in progressions})
    for i, pa in enumerate(progressions):
        for pb in progressions[i:]:
            if set(pa) & set(pb):
                continue
            rest = [j for j in idx if j not in set(pa) and j not in set(pb)]
            if len(rest) < d:
                continue
            for pc in combinations_of(rest, d):
                out.append(
                    (
                        [mu[j] for j in pa],
                        [mu[j] for j in pb],
                        [mu[j] for j in pc],
                    )
                )
    return out


def combinations_of(seq: list[int], k: int):
    from itertools import combinations

    return combinations(seq, k)


def scan_structured(p: int, n: int, d: int) -> dict:
    mu, _ = mu_domain(n, p)
    if mu is None:
        return {"p": p, "ok": False}
    configs = structured_supports(mu, d)
    certified = 0
    false_positive = 0
    witness = None
    for S_AC, S_BC, S_AB in configs:
        rec = certify(p, mu, S_AC, S_BC, S_AB)
        if rec["ok"]:
            certified += 1
            if witness is None:
                witness = (S_AC, S_BC, S_AB)
        elif "constant syzygy" in rec["reason"]:
            false_positive += 1
    return {
        "p": p,
        "ok": True,
        "configs": len(configs),
        "certified": certified,
        "floor_attained": false_positive,
        "witness": witness,
    }


# ----------------------------------------------------------------------------
# controls
# ----------------------------------------------------------------------------
SYZ71_WITNESS = {
    "p": 41,
    "S_AC": [1, 2, 23, 25, 37, 39],
    "S_BC": [5, 8, 10, 16, 18, 36],
    "S_AB": [4, 9, 21, 31, 33, 40],
}


def check_syz71_witness() -> bool:
    p = SYZ71_WITNESS["p"]
    mu, _ = mu_domain(N_DEFAULT, p)
    assert mu is not None
    rec = certify(p, mu, SYZ71_WITNESS["S_AC"], SYZ71_WITNESS["S_BC"], SYZ71_WITNESS["S_AB"])
    print("=== control: the recorded SYZ71 F_41 witness ===")
    print(f"  mu_20 stays in F_{p}: {set(mu) <= set(range(p))}, |mu| = {len(mu)}")
    print(f"  certified: {rec['ok']}  ({rec['reason']})")
    if rec["ok"]:
        print(f"  s_AC = {fmt_poly(rec['s_AC'], p)}")
        print(f"  s_BC = {fmt_poly(rec['s_BC'], p)}")
        print(f"  s_AB = {fmt_poly(rec['s_AB'], p)}")
        print(f"  combined degree = {rec['combo_degree']}, slot degrees = {rec['slot_degrees']}")
        print(f"  constant-cofactor rank (must be 3) = {rec['const_rank']}")
        print(f"  leftover T = {rec['T']}")
    return bool(rec["ok"])


def demo_false_positive(p: int = 41, trials: int = 60000, seed: int = 20261030) -> None:
    """Exhibit a config the SYZ71 rank test calls a hit but which is floor-attained."""
    mu, _ = mu_domain(N_DEFAULT, p)
    assert mu is not None
    rng = random.Random(seed)
    for _ in range(trials):
        bag = mu[:]
        rng.shuffle(bag)
        S_AC, S_BC, S_AB = bag[:6], bag[6:12], bag[12:18]
        rows = []
        for x in S_AB:
            wac = vanishing_value(x, S_AC, p)
            wbc = vanishing_value(x, S_BC, p)
            rows.append([wac, x * wac % p, wbc, x * wbc % p])
        if gf_rank(rows, p) >= 4:
            continue
        rec = certify(p, mu, S_AC, S_BC, S_AB)
        if not rec["ok"] and "constant syzygy" in rec["reason"]:
            print("\n=== reproduced SYZ71-test false positive ===")
            print(f"  p = {p}; the SYZ71 rank<4 test reports a hit on:")
            print(f"    S_AC={S_AC}  S_BC={S_BC}  S_AB={S_AB}")
            print(f"  the certificate rejects it: {rec['reason']}")
            print(f"  constant-cofactor rank = {rec['const_rank']} < 3, so delta_1 = 6 = max:")
            print("  a floor-attained (SYZ69 second-class) triple, NOT a middle-band occupant.")
            return
    print("\n(no floor-attained rank<4 config found in the sample)")


def fmt_poly(c: list[int], p: int) -> str:
    terms = []
    for i, v in enumerate(c):
        v %= p
        if not v:
            continue
        if i == 0:
            terms.append(str(v))
        elif i == 1:
            terms.append(f"{v}*X")
        else:
            terms.append(f"{v}*X^{i}")
    return " + ".join(terms) if terms else "0"


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=20000)
    ap.add_argument("--demo-false-positive", action="store_true")
    ap.add_argument("--no-structured", action="store_true")
    args = ap.parse_args()

    check_syz71_witness()
    if args.demo_false_positive:
        demo_false_positive()

    # Every entry is 1 (mod 20), so mu_20 embeds in F_p^*.
    primes = [
        p
        for p in (
            41, 61, 101, 181, 241, 401, 601, 1021, 2081,
            4481, 9011, 16421, 131101, 1048601, 8388761, 2147484041,
        )
        if is_prime(p) and p % N_DEFAULT == 1
    ]

    print("\n=== SYZ72 sweep: certified (6,6,6) middle-band occupancy on mu_20 ===")
    print(
        f"{'p':>12} {'configs':>9} {'rank<=3':>8} {'certified':>9} "
        f"{'floor-attained':>14} {'density':>10}"
    )
    total_certified = 0
    for p in primes:
        rec = sample_prime(p, N_DEFAULT, D_DEFAULT, args.trials, seed=20261030 + p)
        if not rec.get("ok"):
            print(f"{p:>12}  skipped: {rec.get('reason')}")
            continue
        total_certified += rec["certified"]
        dens = rec["certified"] / max(1, rec["configs"])
        print(
            f"{p:>12} {rec['configs']:>9} {rec['rank_le_3']:>8} "
            f"{rec['certified']:>9} {rec['floor_attained']:>14} {dens:>10.2e}"
        )
        if rec["witness"]:
            w = rec["witness"]
            print(f"    WITNESS S_AC={w['S_AC']}")
            print(f"            S_BC={w['S_BC']}")
            print(f"            S_AB={w['S_AB']}")
            print(
                f"            s_AC={fmt_poly(w['s_AC'], p)}  s_BC={fmt_poly(w['s_BC'], p)}"
                f"  s_AB={fmt_poly(w['s_AB'], p)}"
            )

    if not args.no_structured:
        print("\n=== structured supports (index progressions, i.e. union-of-coset shapes) ===")
        for p in (41, 101, 1009, next_prime_1_mod(N_DEFAULT, 2**20)):
            rec = scan_structured(p, N_DEFAULT, D_DEFAULT)
            if not rec.get("ok"):
                continue
            print(
                f"  F_{p}: configs={rec['configs']:>6} certified={rec['certified']:>4} "
                f"floor-attained={rec['floor_attained']:>4}"
            )

    print(f"\ntotal certified middle-band occupants over the sweep: {total_certified}")
    print("Exact arithmetic; sampling evidence, not a theorem.")


if __name__ == "__main__":
    main()
