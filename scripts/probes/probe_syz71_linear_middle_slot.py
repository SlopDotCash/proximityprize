#!/usr/bin/env python3
"""SYZ71 — does the first open middle slot (6,6,6) at product-degree 7 exist on-domain?

A linear-cofactor syzygy of three degree-6 vanishing polynomials is the SYZ70
first middle slot: product-degree 7 = 6 + 1.  On mu_n this is a 6 x 4
homogeneous linear system (two linear cofactors, four unknown coefficients).

Band-realizable at rate 1/2 first occurs at n = 20, k = 10, t = 2
(SYZ50: n >= 3d + 1 = 19, even n, t = 2 fills the domain).

This probe searches mu_20 (and nearby admissible n) for a 6-point set on which
the evaluation matrix of (W_AC, X W_AC, W_BC, X W_BC) has rank < 4.  A hit is
an on-domain linear-middle witness.  A miss is computational evidence, not a
proof.

Usage: python scripts/probes/probe_syz71_linear_middle_slot.py
"""
from __future__ import annotations

import random
from itertools import combinations


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


def primitive_root(mod: int) -> int | None:
    for cand in range(2, mod):
        if all(pow(cand, (mod - 1) // pr, mod) != 1 for pr in prime_factors(mod - 1)):
            return cand
    return None


def mu_domain(n: int, mod: int) -> tuple[list[int], int] | tuple[None, None]:
    if (mod - 1) % n != 0:
        return None, None
    g = primitive_root(mod)
    if g is None:
        return None, None
    w = pow(g, (mod - 1) // n, mod)
    return [pow(w, i, mod) for i in range(n)], w


def vanishing_eval(omega: int, support: list[int], mod: int) -> int:
    acc = 1
    for s in support:
        acc = (acc * ((omega - s) % mod)) % mod
    return acc


def gf_rank(rows: list[list[int]], p: int) -> int:
    M = [row[:] for row in rows]
    nrows = len(M)
    if nrows == 0:
        return 0
    ncols = len(M[0])
    rank = 0
    row = 0
    for col in range(ncols):
        piv = None
        for r in range(row, nrows):
            if M[r][col] % p:
                piv = r
                break
        if piv is None:
            continue
        M[row], M[piv] = M[piv], M[row]
        inv = pow(M[row][col], p - 2, p)
        M[row] = [(x * inv) % p for x in M[row]]
        for r in range(nrows):
            if r != row and M[r][col] % p:
                f = M[r][col]
                M[r] = [(a - f * b) % p for a, b in zip(M[r], M[row])]
        rank += 1
        row += 1
        if row == nrows:
            break
    return rank


def remaining_rows(pts: list[int], S_AC: list[int], S_BC: list[int], mod: int):
    excl = set(S_AC) | set(S_BC)
    rows = []
    omegas = []
    for omega in pts:
        if omega in excl:
            continue
        wac = vanishing_eval(omega, S_AC, mod)
        wbc = vanishing_eval(omega, S_BC, mod)
        rows.append(
            [wac, (omega * wac) % mod, wbc, (omega * wbc) % mod]
        )
        omegas.append(omega)
    return omegas, rows


def search_pair(pts: list[int], S_AC: list[int], S_BC: list[int], mod: int, d: int):
    omegas, rows = remaining_rows(pts, S_AC, S_BC, mod)
    if len(omegas) < d:
        return None
    for idxs in combinations(range(len(omegas)), d):
        block = [rows[i] for i in idxs]
        if gf_rank(block, mod) < 4:
            return [omegas[i] for i in idxs]
    return None


def random_disjoint(pts: list[int], d: int, rng: random.Random):
    bag = pts[:]
    rng.shuffle(bag)
    return bag[:d], bag[d : 2 * d]


def scan(mod: int, n: int, d: int, trials: int, seed: int) -> dict:
    pts, _ = mu_domain(n, mod)
    if pts is None:
        return {"mod": mod, "n": n, "ok": False, "reason": "no mu_n"}
    rng = random.Random(seed)
    hits = []
    for i in range(trials):
        S_AC, S_BC = random_disjoint(pts, d, rng)
        found = search_pair(pts, S_AC, S_BC, mod, d)
        if found is not None:
            hits.append((S_AC, S_BC, found))
            break
    return {
        "mod": mod,
        "n": n,
        "d": d,
        "ok": True,
        "trials": trials,
        "hits": len(hits),
        "witness": hits[0] if hits else None,
    }


def coset_pairs(pts: list[int], w: int, n: int, d: int, mod: int):
    """Structured: two disjoint d-sets as unions of short geometric progressions."""
    out = []
    if d % 2 == 0:
        half = d // 2
        if n % half == 0:
            step = n // half
            # two residue classes of a subgroup of index step
            for shift_a in range(min(step, 8)):
                for shift_b in range(shift_a + 1, min(step, 8)):
                    ac = [pts[(shift_a + j * step) % n] for j in range(half)]
                    # pad with another progression if needed — skip, size is half
                    if len(ac) == d:
                        bc = [pts[(shift_b + j * step) % n] for j in range(d)]
                        if len(set(ac) & set(bc)) == 0:
                            out.append((ac, bc))
    # arithmetic (index) progressions
    for start_a in range(n):
        for step in (1, 2, 3):
            ac_idx = [(start_a + i * step) % n for i in range(d)]
            if len(set(ac_idx)) < d:
                continue
            rem = [i for i in range(n) if i not in set(ac_idx)]
            if len(rem) < d:
                continue
            bc_idx = rem[:d]
            out.append(([pts[i] for i in ac_idx], [pts[i] for i in bc_idx]))
            if len(out) > 40:
                return out
    return out


def scan_structured(mod: int, n: int, d: int) -> dict:
    pts, w = mu_domain(n, mod)
    if pts is None or w is None:
        return {"mod": mod, "n": n, "ok": False}
    hits = 0
    witness = None
    pairs = coset_pairs(pts, w, n, d, mod)
    for S_AC, S_BC in pairs:
        found = search_pair(pts, S_AC, S_BC, mod, d)
        if found is not None:
            hits += 1
            witness = (S_AC, S_BC, found)
            break
    return {
        "mod": mod,
        "n": n,
        "structured_pairs": len(pairs),
        "hits": hits,
        "witness": witness,
    }


def main() -> None:
    configs = [
        # first band-realizable (6,6,6): n=20, k=10, t=2
        (41, 20, 6, 4000),
        (61, 20, 6, 4000),
        (101, 20, 6, 4000),
        # slightly larger domains, still rate-1/2 compatible
        (67, 22, 6, 2500),
        (89, 22, 6, 2500),
        (73, 24, 6, 2500),
        (97, 32, 6, 2000),
    ]
    print("=== SYZ71 linear-middle slot search (d=6, product-degree 7) ===")
    any_hit = False
    for mod, n, d, trials in configs:
        rec = scan(mod, n, d, trials, seed=20260815 + n + mod)
        print(
            f"  random  F_{mod} mu_{n}: trials={rec.get('trials')} "
            f"hits={rec.get('hits')} ok={rec.get('ok')}"
        )
        if rec.get("witness"):
            any_hit = True
            S_AC, S_BC, S_AB = rec["witness"]
            print(f"    WITNESS S_AC={S_AC}")
            print(f"            S_BC={S_BC}")
            print(f"            S_AB={S_AB}")
        rec2 = scan_structured(mod, n, d)
        print(
            f"  struct  F_{mod} mu_{n}: pairs={rec2.get('structured_pairs')} "
            f"hits={rec2.get('hits')}"
        )
        if rec2.get("witness"):
            any_hit = True
            print(f"    STRUCTURED WITNESS {rec2['witness'][:2]}")

    # sanity: recover a SYZ50-style CONSTANT level-set at (4,4,4) on mu_14 < F_29
    print("\n=== sanity: constant (4,4,4) level-set on mu_14 ⊂ F_29 should exist ===")
    pts, _ = mu_domain(14, 29)
    assert pts is not None
    rng = random.Random(0)
    const_hits = 0
    for _ in range(2000):
        ac, bc = random_disjoint(pts, 4, rng)
        excl = set(ac) | set(bc)
        levels: dict[int, list[int]] = {}
        for omega in pts:
            if omega in excl:
                continue
            num = vanishing_eval(omega, bc, 29)
            den = vanishing_eval(omega, ac, 29)
            if den == 0:
                continue
            lam = (num * pow(den, 27, 29)) % 29
            levels.setdefault(lam, []).append(omega)
        if any(len(v) >= 4 for v in levels.values()):
            const_hits += 1
            break
    print(f"  constant level-set hit within 2000 trials: {const_hits > 0}")
    print("\nLINEAR-MIDDLE HIT:" if any_hit else "\nNO LINEAR-MIDDLE HIT in the scanned sample.")
    print("This is computational evidence, not a theorem.")


if __name__ == "__main__":
    main()
