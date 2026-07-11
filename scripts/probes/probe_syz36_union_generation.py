#!/usr/bin/env python3
"""SYZ36 — union-generation for band triples of shortened RS duals.

For an MDS/RS code RS[n,k] with evaluation domain `dom`, and three cores
C_A, C_B, C_C in the "band" (sizes s in (2n/3, 3n/4), pairwise overlaps in
[2s-n, k-1], so pairwise dual intersections vanish), we test the
UNION-GENERATION gate

    finrank( A ⊔ B ⊔ C )  ==  finrank( D_{C_A ∪ C_B ∪ C_C} )  ==  |U| - k

where A_i = { v ∈ F^n : supp(v) ⊆ C_i, v ⊥ RS[n,k] } is the shortened dual on
core C_i (finrank |C_i| - k).  Equivalently (SYZ25 duality) the local-to-global
polynomial rigidity: every p on U that is deg<k on each core is globally deg<k.

We ALSO compute the univariate-syzygy law behind the cocycle reduction:

    cocycle  q_AB = q_AC - q_BC ,  deg q_XY <= k-1 ,  q_XY vanishes on C_X∩C_Y.
    factor V_T (triple T = C_A∩C_B∩C_C), W_XY pairwise coprime:
        W_AB r_AB - W_AC r_AC + W_BC r_BC = 0 , deg r_XY <= k-1 - m_XY.

The µ-basis theory (Cox–Sederberg–Chen): the syzygy module of a coprime
univariate triple is FREE of rank 2 with generator degrees µ1 ≤ µ2 summing to
the parametrization degree.  We compute the minimal degree of a NONTRIVIAL
in-budget syzygy of (W_AB, -W_AC, W_BC) and compare against the budget.

Outputs, per (field, domain-type):
  * # band triples, # generation failures (deficiency d>0)
  * whether every band triple generates (the gate)
  * the syzygy-degree margin distribution.

Deterministic; no external deps beyond stdlib.  Fields are prime GF(p).
"""

import itertools
from itertools import combinations

# ---------- prime field linear algebra ----------

def inv(a, p):
    return pow(a % p, p - 2, p)

def rank_mod(rows, ncols, p):
    """Rank of a matrix (list of row lists) over GF(p)."""
    M = [row[:] for row in rows]
    r = 0
    nrows = len(M)
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if M[i][c] % p != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        ic = inv(M[r][c], p)
        M[r] = [(x * ic) % p for x in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] % p != 0:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(ncols)]
        r += 1
        if r == nrows:
            break
    return r

def nullspace_mod(rows, ncols, p):
    """Basis of the right null space of the matrix (rows) over GF(p)."""
    M = [row[:] for row in rows]
    nrows = len(M)
    pivcol = {}
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nrows):
            if M[i][c] % p != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        ic = inv(M[r][c], p)
        M[r] = [(x * ic) % p for x in M[r]]
        for i in range(nrows):
            if i != r and M[i][c] % p != 0:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % p for j in range(ncols)]
        pivcol[c] = r
        r += 1
        if r == nrows:
            break
    free = [c for c in range(ncols) if c not in pivcol]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for c, rr in pivcol.items():
            v[c] = (-M[rr][fc]) % p
        basis.append(v)
    return basis

# ---------- RS dual / shortened-core spaces ----------

def vandermonde(dom, k, p):
    """k x n generator of RS[n,k]: rows d=0..k-1, cols alpha^d."""
    return [[pow(a, d, p) for a in dom] for d in range(k)]

def core_dual_basis(dom, k, p, core):
    """Basis of { v ∈ F^n : supp(v) ⊆ core, G v = 0 }, embedded in F^n.
    Solve on the core coordinates: G_core * w = 0, then zero-extend."""
    n = len(dom)
    Gc = [[pow(dom[j], d, p) for j in core] for d in range(k)]  # k x |core|
    ns = nullspace_mod(Gc, len(core), p)  # vectors indexed by core positions
    out = []
    for w in ns:
        v = [0] * n
        for idx, j in enumerate(core):
            v[j] = w[idx]
        out.append(v)
    return out

def union_generation_deficiency(dom, k, p, cores):
    """d = (|U| - k) - finrank(⨆ A_i)."""
    U = sorted(set().union(*[set(c) for c in cores]))
    target = len(U) - k
    allrows = []
    for c in cores:
        allrows.extend(core_dual_basis(dom, k, p, c))
    rk = rank_mod(allrows, len(dom), p) if allrows else 0
    return target - rk, target, rk

# ---------- univariate polynomial arithmetic over GF(p) ----------

def poly_from_roots(roots, p):
    """Monic polynomial with given roots (list of field elements), low->high."""
    poly = [1]
    for r in roots:
        # multiply by (x - r)
        new = [0] * (len(poly) + 1)
        for i, c in enumerate(poly):
            new[i] = (new[i] - c * r) % p
            new[i + 1] = (new[i + 1] + c) % p
        poly = new
    return poly

def pdeg(a):
    d = len(a) - 1
    while d > 0 and a[d] == 0:
        d -= 1
    return d if any(a) else -1

def pmul(a, b, p):
    if not a or not b:
        return [0]
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    return r

def inbudget_syzygy_dim(WAB, WAC, WBC, bAB, bAC, bBC, p):
    """Dimension of the space of (r_AB,r_AC,r_BC) with
        W_AB r_AB - W_AC r_AC + W_BC r_BC = 0,
    and deg r_AB<=bAB, deg r_AC<=bAC, deg r_BC<=bBC (per-component budgets).
    Budgets < 0 mean that component is forced 0."""
    dAB, dAC, dBC = pdeg(WAB), pdeg(WAC), pdeg(WBC)
    # variable blocks
    nAB = bAB + 1 if bAB >= 0 else 0
    nAC = bAC + 1 if bAC >= 0 else 0
    nBC = bBC + 1 if bBC >= 0 else 0
    nvar = nAB + nAC + nBC
    if nvar == 0:
        return 0
    eqdeg = max((dAB + bAB) if nAB else -1,
                (dAC + bAC) if nAC else -1,
                (dBC + bBC) if nBC else -1)
    if eqdeg < 0:
        return 0
    rows = []
    for e in range(eqdeg + 1):
        row = [0] * nvar
        for i in range(nAB):
            j = e - i
            if 0 <= j <= dAB:
                row[i] = (row[i] + WAB[j]) % p
        for i in range(nAC):
            j = e - i
            if 0 <= j <= dAC:
                row[nAB + i] = (row[nAB + i] - WAC[j]) % p
        for i in range(nBC):
            j = e - i
            if 0 <= j <= dBC:
                row[nAB + nAC + i] = (row[nAB + nAC + i] + WBC[j]) % p
        rows.append(row)
    return nvar - rank_mod(rows, nvar, p)

# ---------- domains ----------

def roots_of_unity(n, p):
    """n-th roots of unity in GF(p) if n | p-1, else None."""
    if (p - 1) % n != 0:
        return None
    g = None
    for cand in range(2, p):
        if pow(cand, p - 1, p) == 1:
            # find generator of order n
            w = pow(cand, (p - 1) // n, p)
            # check order exactly n
            order_ok = all(pow(w, d, p) != 1 for d in range(1, n))
            if order_ok:
                g = w
                break
    if g is None:
        return None
    return [pow(g, i, p) for i in range(n)]

# ---------- band-triple enumeration ----------

def band_triples(n, k, dom_indices):
    """Yield (C_A,C_B,C_C) with sizes s in (2n/3,3n/4), pairwise overlaps
    in [2s-n, k-1].  Use size s = common value.  Small n only."""
    slo = 2 * n // 3 + 1
    shi = (3 * n - 1) // 4  # strictly < 3n/4
    for s in range(slo, shi + 1):
        # pairwise overlap window
        omin = max(2 * s - n, 0)
        omax = k - 1
        if omin > omax:
            continue
        # enumerate a modest number of triples for this s
        pts = list(dom_indices)
        if s <= k:  # genuine band: cores strictly bigger than k (nontrivial duals)
            continue
        # to keep it tractable, fix C_A as first s points
        CA = frozenset(pts[:s])
        cnt = 0
        for CB in combinations(pts, s):
            CBs = frozenset(CB)
            if CBs == CA:
                continue
            oAB = len(CA & CBs)
            if not (omin <= oAB <= omax):
                continue
            for CC in combinations(pts, s):
                CCs = frozenset(CC)
                if CCs == CA or CCs == CBs:
                    continue
                oAC = len(CA & CCs)
                oBC = len(CBs & CCs)
                if not (omin <= oAC <= omax and omin <= oBC <= omax):
                    continue
                if len(CA | CBs | CCs) > n:
                    continue
                yield (sorted(CA), sorted(CBs), sorted(CCs))
                cnt += 1
                if cnt >= 400:
                    return

def analyze(p, n, k, dom, dom_name):
    fails = 0
    total = 0
    margins = []
    fail_examples = []
    for cores in band_triples(n, k, list(range(n))):
        total += 1
        d, target, rk = union_generation_deficiency(dom, k, p, cores)
        if d != 0:
            fails += 1
            if len(fail_examples) < 3:
                fail_examples.append((cores, d, target, rk))
        # syzygy law on this config (per-component budgets b_XY = k-1-m_XY)
        CA, CB, CC = [set(c) for c in cores]
        T = CA & CB & CC
        WAB = poly_from_roots([dom[i] for i in sorted((CA & CB) - T)], p)
        WAC = poly_from_roots([dom[i] for i in sorted((CA & CC) - T)], p)
        WBC = poly_from_roots([dom[i] for i in sorted((CB & CC) - T)], p)
        mAB, mAC, mBC = len(CA & CB), len(CA & CC), len(CB & CC)
        bAB, bAC, bBC = k - 1 - mAB, k - 1 - mAC, k - 1 - mBC
        syzdim = inbudget_syzygy_dim(WAB, WAC, WBC, bAB, bAC, bBC, p)
        margins.append((d, syzdim, mAB, mAC, mBC, len(T)))
    return total, fails, margins, fail_examples

def main():
    configs = [
        (n, k) for n in range(6, 15) for k in range(2, n)
        if 2 * n // 3 + 1 <= (3 * n - 1) // 4
    ]
    print("SYZ36 union-generation probe (band triples of shortened RS duals)")
    print("=" * 70)
    for p in (31, 101, 65537):
        for (n, k) in configs:
            # need band nonempty and pairwise overlap window nonempty
            slo = 2 * n // 3 + 1
            shi = (3 * n - 1) // 4
            ok_s = any(max(2*s-n,0) <= k-1 for s in range(slo, shi+1))
            if not ok_s:
                continue
            for dom_name, dom in (("gen", list(range(1, n + 1))),
                                  ("roots", roots_of_unity(n, p))):
                if dom is None:
                    continue
                if len(set(dom)) < n:
                    continue
                total, fails, margins, ex = analyze(p, n, k, dom, dom_name)
                if total == 0:
                    continue
                tag = f"p={p} n={n} k={k} dom={dom_name:5s}"
                verdict = "GENERATES" if fails == 0 else f"FAILS x{fails}"
                # law check: does deficiency d equal in-budget syzygy dim?
                mism = sum(1 for m in margins if m[0] != m[1])
                print(f"{tag}: {total:4d} triples  {verdict:14s}  "
                      f"d==syzdim mismatches={mism}/{total}")
                for (cores, d, target, rk) in ex:
                    print(f"      FAIL d={d} target={target} rank={rk} cores={cores}")

if __name__ == "__main__":
    main()
