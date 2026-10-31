#!/usr/bin/env python3
"""G280 probe: does the sponsor subset-correlation cone contain the antipode -R_r? (#466)

Frontier context.  Fable G276/G279 retired every polarity-invariant (even) certificate
via the exact involution
    B(w, -r) = -B(w, r),   E(-r) = E(r),
where B is the centered covariance and every available datum (norms, energies, |Gram|,
operator ceilings) is even in the profile.  Fable's ONE surviving escape hatch is a
"sponsor-specific quadratic certificate on the narrow cone of actual subset-correlation
profiles", explicitly caveated: it is only alive "because that cone need not contain -r".

This probe DECIDES that caveat structurally.  Two distinct antipode notions:

(Q1) COORDINATE antipode.  Is R_r even as a function on F_p, i.e. R_r(-x) = R_r(x)?
     The centered vector is r_x := p*R_r(x) - SR.  If R_r is coordinate-even then r is a
     symmetric vector but that is NOT Fable's -r (which negates VALUES, not permutes
     coordinates).  We record the exact symmetry class of R_r.

(Q2) VALUE antipode / cone membership.  Fable's involution sends the centered profile
     vector r = (r_x) to -r = (-r_x).  The realizable centered sponsor profiles at a fixed
     (n,p) are the vectors r^{(s)} := p*R_r(x) - SR for the finitely many admissible rank
     pairs / sponsor data.  We test whether -r (Fable's involuted vector) coincides with
     ANY realizable centered profile at the same prime -- across ranks, across the
     coordinate-antipode reindexing x->-x, and across the multiplicative dilations
     x -> a*x for a in G that act on the sponsor (the natural symmetry group of the
     subgroup covariance).  If -r IS realizable, the same involution kills the
     sponsor-specific certificate too.  If -r is NOT found, that is a finite absence on the
     tested carrier only (see SCOPE), not a proof that the cone is antipode-free.

SCOPE (audit 2026-10-28, L103).  The exact tested carrier is: the listed (n, p) cells and
their listed ranks r; the realizable set consists of the centered profiles of those ranks,
their coordinate antipodes x -> -x, and their dilations x -> a*x for a in G only (NOT general
field dilations a in F_p^* outside G); the shift check additionally composes with translations
x -> x + b.  Absence of a pairwise antipode in these finite orbits does not show that the
convex/conic closure of ALL realizable profiles is antipode-free, and does not by itself
supply a useful separating normal.

Conventions match G269 EXACTLY (double-shift sponsor, dp_r*dp_{r-1}).  Pure int, no floats.
SystemExit(1) on any internal inconsistency.
"""
from __future__ import annotations
from math import comb


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def prime_factors(n: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fac = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise ValueError(f"no primitive root mod {p}")


def subgroup(p: int, n: int) -> list[int]:
    root = primitive_root(p)
    z = pow(root, (p - 1) // n, p)
    out: list[int] = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * z % p
    assert x == 1 and len(set(out)) == n
    return out


def W_hist(G: list[int], p: int) -> list[int]:
    """W_G(x) = #{(y,z) in G^2 : 2y - z = x}."""
    W = [0] * p
    for y in G:
        two_y = (2 * y) % p
        for z in G:
            W[(two_y - z) % p] += 1
    return W


def dp(G: list[int], k: int, p: int) -> list[int]:
    """dp_k(x) = #{A subset G, |A|=k : sum A = x mod p}. Exact subset-sum DP."""
    # counts[s] over subsets of chosen size; do size-tracked DP
    # f[j][s] = number of j-subsets summing to s
    n = len(G)
    # Use list of dicts keyed by size -> array over residues
    cur = [[0] * p for _ in range(k + 1)]
    cur[0][0] = 1
    for g in G:
        for j in range(k, 0, -1):
            row_prev = cur[j - 1]
            row_cur = cur[j]
            if any(row_prev):
                for s in range(p):
                    v = row_prev[s]
                    if v:
                        row_cur[(s + g) % p] += v
    return cur[k]


def conv(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * p
    for i in range(p):
        ai = a[i]
        if ai:
            for j in range(p):
                bj = b[j]
                if bj:
                    out[(i + j) % p] += ai * bj
    return out


def R_profile(G: list[int], r: int, p: int) -> list[int]:
    """R_r = dp_r * dp_{r-1}."""
    return conv(dp(G, r, p), dp(G, r - 1, p), p)


def centered(R: list[int], p: int) -> list[int]:
    SR = sum(R)
    return [p * R[x] - SR for x in range(p)]


def dilate(vec: list[int], a: int, p: int) -> list[int]:
    """Reindex coordinate x -> a*x: new[a*x] = vec[x], i.e. new[t] = vec[a^{-1} t]."""
    ainv = pow(a, p - 2, p)
    return [vec[(ainv * t) % p] for t in range(p)]


def coord_antipode(vec: list[int], p: int) -> list[int]:
    """x -> -x reindex."""
    return [vec[(-t) % p] for t in range(p)]


def main() -> None:
    # Sponsor cells (match the G269/G278 census family).
    cells = [
        (8, 113, [3, 4]),
        (8, 2969, [3, 4]),
        (16, 97, [5, 6]),
        (16, 433, [5, 6]),
        (16, 257, [5, 6]),
        (16, 977, [5]),
        (16, 1153, [5]),
    ]
    for (n, p, ranks) in cells:
        assert is_prime(p), p
        assert (p - 1) % n == 0, (n, p)

    print("=" * 78)
    print("G280: sponsor cone antipode probe (#466)")
    print("=" * 78)

    q1_even = 0
    q1_total = 0
    q2_hits = 0   # -r realizable by some sponsor symmetry
    q2_total = 0
    q2_records = []

    for (n, p, ranks) in cells:
        G = subgroup(p, n)
        # Precompute realizable centered profiles at this prime, tagged.
        realizable = {}  # tag -> tuple(vec)
        cent = {}
        for r in ranks:
            R = R_profile(G, r, p)
            c = centered(R, p)
            cent[r] = c
            realizable[f"r{r}"] = tuple(c)
            # coordinate-antipode and dilation orbit are the sponsor's symmetry group
            realizable[f"r{r}_anti"] = tuple(coord_antipode(c, p))
            for a in G:
                realizable[f"r{r}_dil{a}"] = tuple(dilate(c, a, p))
                realizable[f"r{r}_dil{a}_anti"] = tuple(coord_antipode(dilate(c, a, p), p))

        for r in ranks:
            c = cent[r]
            R = R_profile(G, r, p)
            # ---- Q1: coordinate evenness of R_r ----
            q1_total += 1
            is_even = all(R[x] == R[(-x) % p] for x in range(p))
            if is_even:
                q1_even += 1
            # ---- Q2: is -c (Fable value-antipode) a realizable centered profile? ----
            q2_total += 1
            neg = tuple(-v for v in c)
            hit_tag = None
            for tag, vec in realizable.items():
                if vec == neg:
                    hit_tag = tag
                    break
            if hit_tag is not None:
                q2_hits += 1
            # Also record: is -c reachable after composing with a translation x -> x + b?
            # Together with the dilations by a in G above this tests x -> a*x + b for a in G
            # only (not the full affine group of F_p: no dilations outside G).
            found_shift = None
            if hit_tag is None:
                cset = None
                for b in range(p):
                    shifted = tuple(c[(t - b) % p] for t in range(p))
                    # compare -shifted against realizable? equivalently shift the target
                    negshift = tuple(-v for v in shifted)
                    # check membership among realizable (already dilation+antipode closed)
                    # cheap: build set once
                    if cset is None:
                        cset = set(realizable.values())
                    if negshift in cset:
                        found_shift = b
                        break
            q2_records.append((n, p, r, is_even, hit_tag, found_shift))
            print(f"  cell n={n:>2} p={p:>5} r={r}: R_r coord-even={is_even}  "
                  f"-c realizable(dihedral+dilation)={hit_tag}  affine-shift-hit={found_shift}")

    print("-" * 78)
    print(f"Q1 coordinate-even R_r:            {q1_even}/{q1_total} cells")
    print(f"Q2 -c in sponsor symmetry orbit:   {q2_hits}/{q2_total} cells")
    print("-" * 78)

    # ---- Structural interpretation asserts ----
    # Claim A (to verify): R_r is NEVER coordinate-even at genuine wraparound cells
    #   (n=16 sponsors).  Evenness would make the centered profile a symmetric vector.
    # Claim B: -c is NOT found in the tested carrier (G-dilation orbit, antipode, and
    #   translations composed with them) at the recorded cells.  This is a finite absence; it
    #   does not prove the conic/convex closure of all realizable profiles is antipode-free.

    # We assert the empirical finding as hard invariants so drift fails the gate.
    any_neg_realizable = any(tag is not None for (_, _, _, _, tag, _) in q2_records)
    any_shift_hit = any(sh is not None for (*_, sh) in q2_records)
    print(f"any -c realizable across all cells: {any_neg_realizable}  "
          f"any translated -c hit: {any_shift_hit}")

    # ---- HARD ASSERTIONS (SystemExit(1) on drift) ----
    # (A1) -1 in G forces R_r coordinate-even at EVERY recorded cell.
    if q1_even != q1_total:
        raise SystemExit(f"FAIL A1: R_r not coord-even in all cells ({q1_even}/{q1_total})")
    # (A2) On the tested carrier, -c is never hit by G-dilation / antipode / translation at
    #      any recorded cell (both the orbit check AND the translation check are enforced).
    if q2_hits != 0 or any_neg_realizable or any_shift_hit:
        raise SystemExit(f"FAIL A2: -c hit in {q2_hits} cells (orbit) or by a translation "
                         f"(shift hit={any_shift_hit}) on the tested carrier")

    # (A3) EXACT-INTEGER real-Fourier / signed-inner-product certificate.
    #   -1 in G => both W_G and R_r coord-even => B = p*<W,R> - SW*SR equals the
    #   frequency-pair signed sum with NO magnitude positivity.  Verified float-free:
    #   B takes BOTH signs, and B is exactly reproduced by the coordinate-even folded
    #   pairing  B = p*[W(0)R(0) + 2*sum_{x=1..(p-1)/2} W(x)R(x)] - SW*SR.
    signs = set()
    for (n, p, ranks) in cells:
        G = subgroup(p, n)
        W = W_hist(G, p)
        if not all(W[x] == W[(-x) % p] for x in range(p)):
            raise SystemExit(f"FAIL A3: W_G not coord-even at n={n} p={p}")
        SW = sum(W)
        for r in ranks:
            R = R_profile(G, r, p)
            SR = sum(R)
            B_direct = p * sum(W[x] * R[x] for x in range(p)) - SW * SR
            half = (p - 1) // 2
            folded = W[0] * R[0] + 2 * sum(W[x] * R[x] for x in range(1, half + 1))
            B_folded = p * folded - SW * SR
            if B_folded != B_direct:
                raise SystemExit(
                    f"FAIL A3: folded != direct at n={n} p={p} r={r} "
                    f"({B_folded} != {B_direct})")
            signs.add(1 if B_direct > 0 else (-1 if B_direct < 0 else 0))
    if 1 not in signs or -1 not in signs:
        raise SystemExit(f"FAIL A3: B did not exhibit both signs across sponsors: {signs}")
    print(f"A1 coord-even: PASS  A2 no antipode in tested carrier: PASS  "
          f"A3 real signed-inner-product both signs: PASS (signs={sorted(signs)})")

    # Emit machine-readable summary
    import json
    summary = {
        "q1_even": q1_even, "q1_total": q1_total,
        "q2_hits": q2_hits, "q2_total": q2_total,
        "any_neg_realizable": any_neg_realizable,
        "any_shift_hit": any_shift_hit,
        "tested_carrier": "listed ranks; x->-x; x->a*x for a in G; translations x->x+b",
        "records": [
            {"n": n, "p": p, "r": r, "coord_even": ev, "neg_realizable_tag": tag,
             "shift_hit": sh}
            for (n, p, r, ev, tag, sh) in q2_records
        ],
    }
    print("JSON " + json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
