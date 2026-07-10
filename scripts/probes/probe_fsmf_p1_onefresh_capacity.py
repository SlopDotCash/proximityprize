#!/usr/bin/env python3
"""Exact integer capacity audit for one-fresh (core = T-1) pencil packings.

Every bad scalar at the predecessor threshold t = z+2 that sits on a pencil
with joint core of size c needs t - c fresh coordinates; a non-core coordinate
induces at most ONE gamma per pencil (linear equation in gamma).  Pencils with
core T-1 ("one-fresh") are the count-maximizing shape: per-line cap n - t + 1.

This probe computes, in exact integers for the miniature ladder m = 4, 10, 16,
22 and for P1 itself (m = 2^26), the maximum badCount achievable by ell-line
one-fresh packings realizable through the mu_16 fibre ansatz
  A_ij = q_ij(x^{n/16}) * g(x),  R_ij = q_ij(x^{n/16}) * h(x),
(q_ij cubic potentials splitting over mu_16, g/h sharing s domain roots),
which the m=4/m=10 census probes exhibit concretely.  Structural facts used
(machine-verified in miniature by the census probes, algebraically forced as
argued in the docstrings there):
  * pairwise core overlap = 3*fib + s with fib = n/16, s <= fib - 2;
  * the shared s coordinates lie in EVERY pairwise overlap (triple points);
  * consistency forces a single global Moebius map phi = -g/h, so each
    covered coordinate contributes at most ONE gamma and each free
    coordinate at most `ell` prescribed/determined gammas (2 dof + forced);
  * cubic-slot budget: with ell potentials, pairs need 3 roots each in mu_16
    (16 elements), a root shared by a b-subset consumes C(b,2) slots, and at
    least one fibre must stay unused to host the s shared g/h roots.

Output: for each m and ell in {2,3,4,5}: feasibility and max count, then the
global max versus the budget n.
"""

from __future__ import annotations

from itertools import product


def audit(m):
    n = 16 * m
    k = 4 * m
    z6 = 53 * m - 8
    assert z6 % 6 == 0
    z = z6 // 6
    t = z + 2
    fib = m
    rows = []
    best = (0, None)
    # ell = 2: no consistency constraint; overlap up to k-1 forces
    # proportionality (concurrent, collapses), so max overlap k-2, and each
    # free coord prescribes 2 gammas.  covered = 2(t-1) - p, p <= k-2, and
    # count = (covered - p_sterile) + 2*free, sterile = overlap coords.
    p = k - 2
    covered = 2 * (t - 1) - p
    free = n - covered
    count2 = (covered - p) + 2 * free
    rows.append(("ell=2", True, count2))
    if count2 > best[0]:
        best = (count2, "ell=2")
    # ell >= 3: fibre ansatz.  s = shared g/h roots (in all pairwise
    # overlaps, sterile), s <= fib - 2 (g,h degree fib-1 non-proportional).
    # cubic slots: n2 + 3*n3 + 6*n4 = 3*C(ell,2), roots n2+n3+n4 <= 15
    # (one unused fibre hosts the s shared points).
    for ell in (3, 4, 5):
        slots = 3 * (ell * (ell - 1) // 2)
        feas_best = None
        c2 = ell * (ell - 1) // 2
        c3 = ell * (ell - 1) * (ell - 2) // 6
        c4 = ell * (ell - 1) * (ell - 2) * (ell - 3) // 24
        c5 = 1 if ell == 5 else 0
        for n3 in range(0, slots // 3 + 1):
            for n4 in range(0, slots // 6 + 1):
                n2 = slots - 3 * n3 - 6 * n4
                if n2 < 0 or n2 + n3 + n4 > 15:
                    continue
                # covered(s) = A + B*s  (inclusion-exclusion, exact shape)
                A = ell * (t - 1) - fib * (n2 + 3 * n3 + 6 * n4) \
                    + fib * (n3 + 4 * n4) \
                    - (fib * n4 if ell >= 4 else 0)
                B = -c2 + c3 - c4 + c5
                # count(s) = covered - sterile + ell*(n - covered)
                #          = ell*n - (ell-1)*covered(s) - s - extra_sterile
                extra = fib * n4 if ell == 4 else 0
                # feasible s interval within [0, fib-2] where A + B*s <= n
                cand = []
                for s in {0, fib - 2}:
                    if 0 <= s <= fib - 2 and A + B * s <= n:
                        cand.append(s)
                if B != 0:
                    # boundary solution of A + B*s = n
                    if B < 0:
                        s0 = -(n - A) // (-B) if A > n else 0
                        s0 = max(s0, (A - n + (-B) - 1) // (-B))
                    else:
                        s0 = (n - A) // B
                    for s in (s0, s0 + 1, s0 - 1):
                        if 0 <= s <= fib - 2 and A + B * s <= n:
                            cand.append(s)
                for s in cand:
                    covered = A + B * s
                    free = n - covered
                    count = (covered - s - extra) + ell * free
                    if feas_best is None or count > feas_best:
                        feas_best = count
        rows.append((f"ell={ell}", feas_best is not None, feas_best))
        if feas_best is not None and feas_best > best[0]:
            best = (feas_best, f"ell={ell}")
    print(f"m={m}: n={n} t={t} (T-1 core = {t-1})")
    for name, feas, cnt in rows:
        print(f"   {name}: feasible={feas} maxCount={cnt}")
    print(f"   => ansatz max = {best[0]} via {best[1]}; budget n = {n}; "
          f"margin = {n - best[0]}")
    return best[0], n


def main():
    for m in (4, 10, 16, 22, 2 ** 26):
        cnt, n = audit(m)
        assert cnt <= n, f"ANSATZ OVER BUDGET at m={m}: {cnt} > {n}"
    print("all ansatz maxima within budget")


if __name__ == "__main__":
    main()
