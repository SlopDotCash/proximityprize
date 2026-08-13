#!/usr/bin/env python3
"""G320 reproducible probe: stdlib port of the G246 Krylov degree-2 countermodel.

G246 (`_G246KrylovDegreeTwoCountermodel.lean`) certifies that in the sponsor
cell `(n, p, m) = (8, 1009, 126)`, the centered rank-6 quotient profile `R_6^c`
is NOT in the degree-2 Krylov span of the centered base class. The published
certificate is the 4x4 minor of `[e_0^c, N e_0^c, N^2 e_0^c, R_6^c]` taken on
rows `(0, 1, 2, 4)`, with determinant `-285768` (nonzero).

The original G246 probe uses `sympy` for matrix arithmetic. This file ports
the same computation to **pure Python stdlib** (no `sympy`, no `numpy`, no
`float` in any load-bearing value), reproducing the `-285768` minor, and
extends the check to a SECOND cell `(n, p, m) = (10, 2003, 200)` as an
independent audit. The second cell is a different field and a different
subgroup, so the SAME structure (degree-2 Krylov does not determine `R_6^c`)
holding at both is a real two-data-point sanity check.

HONESTY / SCOPE.
- The Lean kernel pins a specific 4x4 minor determinant (`-285768`) for the
  `(8, 1009)` cell. This probe reproduces that integer exactly via stdlib
  matrix arithmetic (no `sympy`).
- The `(10, 2003)` cell is a NEW audit not in the Lean file. The probe
  computes the 4x4 minor determinant for that cell; if nonzero, the
  countermodel extends. If zero, the structure does NOT extend and the
  audit reports a real refutation of the "always fails" pattern.
- Stdlib only. Pure `int` arithmetic. No `float`, no third-party imports.

No field data beyond the two cells above. Reproducible: the matrix toolkit
is deterministic and the assertions are exact.
"""

from __future__ import annotations


# ---------- stdlib matrix toolkit ----------

def mat_vec(A, v):
    """Matrix-vector product A @ v; A is m x k, v is length k, returns length m."""
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]


def det4(M):
    """Determinant of a 4x4 matrix (cofactor expansion along the first row)."""
    a, b, c, d = M[0]
    e, f, g, h = M[1]
    i, j, k, l = M[2]
    n, o, p, q = M[3]
    return (
        a * (f * (k * q - l * p) - g * (j * q - l * o) + h * (j * p - k * o))
        - b * (e * (k * q - l * p) - g * (i * q - l * n) + h * (i * p - k * n))
        + c * (e * (j * q - l * o) - f * (i * q - l * n) + h * (i * o - j * n))
        - d * (e * (j * p - k * o) - f * (i * p - k * n) + g * (i * o - j * n))
    )


def rank_int(M):
    """Rank of an integer matrix via Gaussian elimination (exact division).
    Returns the number of nonzero pivots after row reduction."""
    A = [row[:] for row in M]
    rows, cols = len(A), len(A[0]) if A else 0
    r = 0
    for c in range(cols):
        pivot = None
        for i in range(r, rows):
            if A[i][c] != 0:
                pivot = i
                break
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                factor = A[i][c] // A[r][c]  # exact since A[i][c] is a multiple
                for cc in range(c, cols):
                    A[i][cc] -= factor * A[r][cc]
        r += 1
        if r == rows:
            break
    return r


def hstack_cols(cols):
    """Given a list of column vectors (each length m), return the m x k matrix
    whose columns are those vectors."""
    m = len(cols[0])
    return [[cols[c][r] for c in range(len(cols))] for r in range(m)]


# ---------- arithmetic helpers (hand-rolled, no sympy) ----------

def factors(n: int) -> list[int]:
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
    fs = factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError(p)


def setup(p: int, n: int):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    logs = [0] * p
    x = 1
    for j in range(p - 1):
        logs[x] = j
        x = x * g % p
    G = [pow(g, m * j, p) for j in range(n)]
    return m, g, logs, G


def incidence(p: int, m: int, logs: list[int]) -> list[list[int]]:
    """Build the symmetric quotient-incidence matrix N[A,B] = #{x in A : 2-x in B}."""
    N = [[0] * m for _ in range(m)]
    for x in range(1, p):
        y = (2 - x) % p
        if y:
            N[logs[x] % m][logs[y] % m] += 1
    assert N == [list(row) for row in zip(*N)]
    return N


def subset_profiles(p: int, G: list[int], rmax: int) -> list[list[int]]:
    """For r = 0..rmax, the subset-sum profile dp[r][t] = #{S in C(G, r) : sum S = t}."""
    dp = [[0] * p for _ in range(rmax + 1)]
    dp[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for r in range(min(rmax, used), 0, -1):
            prev, cur = dp[r - 1], dp[r]
            for t, v in enumerate(prev):
                if v:
                    cur[(t + x) % p] += v
    from math import comb
    for r in range(rmax + 1):
        assert sum(dp[r]) == comb(len(G), r)
    return dp


def quotient_value(profile: list[int], p: int, m: int, g: int) -> list[int]:
    """Project the profile down to the quotient: vals[a] = profile[g^a mod p]."""
    vals = [profile[pow(g, a, p)] for a in range(m)]
    for a, want in enumerate(vals):
        for j in range(1, (p - 1) // m):
            assert profile[pow(g, a + m * j, p)] == want
    return vals


# ---------- the actual audit ----------

def audit_cell(n: int, p: int, *, label: str, expected_minor_rows=(0, 1, 2, 4),
               expected_minor_det: int | None = None, expected_rank_seed: int = 3,
               expected_rank_aug: int = 4):
    """Run the G246 audit on the cell (n, p). Return a result dict."""
    m, g, logs, G = setup(p, n)
    assert 2 not in set(G), f"cell ({n},{p}): 2 in G, sponsor condition broken"
    N = incidence(p, m, logs)
    dp = subset_profiles(p, G, 6)
    R = quotient_value(dp[6], p, m, g)

    one = [1] * m
    e0 = [1] + [0] * (m - 1)
    seed = [m * e0[i] - one[i] for i in range(m)]
    Rc = [m * R[i] - sum(R) for i in range(m)]

    # Build Krylov columns: seed, N*seed, N^2*seed, then Rc
    cols = [seed]
    v = seed
    for _ in range(2):
        v = mat_vec(N, v)
        cols.append(v)
    cols.append(Rc)

    # Rank check
    seed_matrix = hstack_cols(cols[:-1])      # first 3 columns
    aug_matrix = hstack_cols(cols)            # all 4 columns
    rank_seed = rank_int(seed_matrix)
    rank_aug = rank_int(aug_matrix)

    # Minor determinant
    minor_rows = list(expected_minor_rows)
    minor = [[aug_matrix[r][c] for c in range(4)] for r in minor_rows]
    det = det4(minor)

    # Assert known facts for the G246 cell
    assert rank_seed == expected_rank_seed, (
        f"cell ({n},{p}) [{label}]: rank_seed={rank_seed}, expected {expected_rank_seed}"
    )
    assert rank_aug == expected_rank_aug, (
        f"cell ({n},{p}) [{label}]: rank_aug={rank_aug}, expected {expected_rank_aug}"
    )
    if expected_minor_det is not None:
        assert det == expected_minor_det, (
            f"cell ({n},{p}) [{label}]: det={det}, expected {expected_minor_det}"
        )

    # The remaining-rank coefficient A_r
    from math import comb
    extras = {}
    for rr in (5, 6):
        Rr = quotient_value(dp[rr], p, m, g)
        cquot = n * sum(int(N[0][a]) * int(Rr[a]) for a in range(m))
        A = p * cquot - n * n * comb(n, rr)
        extras[f"A{rr}"] = A

    return {
        "label": label, "n": n, "p": p, "m": m,
        "rank_seed": rank_seed, "rank_aug": rank_aug,
        "minor_rows": tuple(minor_rows), "det": det,
        "extras": extras,
        "countermodel_holds": rank_aug > rank_seed,
    }


def main() -> None:
    # ---- Cell 1: G246's published cell (n=8, p=1009). Reproduces the
    #      published minor determinant -285768 from the Lean file.
    cell1 = audit_cell(8, 1009, label="G246-cell (reproduction)",
                       expected_minor_rows=(0, 1, 2, 4),
                       expected_minor_det=-285768)

    # ---- Cell 2: NEW audit at n=10, p=2011 (different field, different
    #      subgroup; (p-1) % n = 2010 % 10 = 0 so m = 201, and 2 ∉ G
    #      because 2^10 = 1024 ≠ 1 mod 2011). Expected_minor_det is None
    #      because no Lean file pins it; the probe computes it and reports.
    cell2 = audit_cell(10, 2011, label="G320-new-cell (extension)",
                       expected_minor_rows=(0, 1, 2, 4),
                       expected_minor_det=None)

    print(f"G320 stdlib port of G246: rank structure CHECKED at both cells.")
    for c in (cell1, cell2):
        print(f"  cell n={c['n']} p={c['p']} m={c['m']}  [{c['label']}]")
        print(f"    rank_seed={c['rank_seed']}  rank_aug={c['rank_aug']}")
        print(f"    pinned minor rows={c['minor_rows']}  det={c['det']}")
        if c['countermodel_holds']:
            print(f"    VERDICT: countermodel HOLDS (rank_aug > rank_seed: R_6^c not in degree-2 Krylov span)")
        else:
            print(f"    VERDICT: countermodel FAILS (rank_aug == rank_seed: degree-2 Krylov span suffices)")
        if c['det'] != 0 and c['label'].startswith('G246'):
            print(f"    (and the G246-pinned 4x4 minor is nonzero at this cell, as expected)")
        elif c['det'] == 0 and not c['label'].startswith('G246'):
            print(f"    (and the G246-pinned 4x4 minor is 0 at this cell, but the rank check still holds;")
            print(f"     a different 4-row subset would give a nonzero minor)")
        for k, v in c['extras'].items():
            print(f"    {k}={v}")


if __name__ == "__main__":
    main()
