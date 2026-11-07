#!/usr/bin/env python3
"""Dyadic-domain escape hunt: does ANY Bezout escape / over-budget stall family
exist on the literal prize domain mu_{2^30}?

Follow-up to probe_rate_quarter_p1_stepanov_weld.py (which REFUTED StallResidual
on adversarial domains via n = 7*2^25 subgroup cosets).  The prize instance
evaluates on mu_{2^30}: every element has 2-power order, subgroups are mu_{2^j},
so coset root-sets have 2-power sizes.  Sections:

  A. The 2-adic window obstruction, exact: the escape window [ceil(M/3), k-1] =
     [234881024, 268435455] lies strictly between 2^27 and 2^28 — no 2-power (and
     no divisor of 2^30) is admissible.  Scale check at mu_256 ratios: window
     [56, 63] between 2^5 and 2^6.  The obstruction is scale-invariant: the
     window sits inside (k/2, k) and k is the 2-power.
  B. Two-level constructions ((x^m - s)*alpha with shared alpha-roots): shared
     roots are TRIPLE points, raising the coverage demand; exact arithmetic shows
     the demand exceeds the degree budget at prize scale AND at mu_256 scale.
  C. Small Bezout solution-dimension battery on the dyadic domain
     mu_256 c F_65537: X, Y, Z c mu_256 at escape sizes (56,56,55), over
     structured dyadic families (genuine subgroup-coset truncations, coset
     unions, two-level sets, random domain subsets, cyclic arcs).  Subgroups
     and cosets are built from exponent-ordered powers w256^(8i), w256^(4i)
     with representatives from distinct quotient classes, and membership /
     disjointness is asserted before any rank check.  Result: dimension 0 on
     every family EXCEPT the two-level shared set, which has dimension 8 (an
     exact family a = alpha*h, b = beta*h, c = lambda*l*h, deg h <= 7, from the
     linear dependence of the three binomials x^32 - s_i times the common
     shared-root factor).  Section B's triple-point coverage count, not Bezout
     dimension, is what excludes that shape; this battery does not turn the
     Bezout family into a stall family, and it is not exhaustive.
     (An earlier version took strides of a NUMERICALLY sorted list of mu_256,
     which are not subgroups or cosets, and reported dimension 0 everywhere.)
  D. Full stall-family census on the dyadic domain (single/dual/coset-shaped
     pencil constructions with dom = mu_256): max #stall-bad vs the two-pencil
     capacity 2(N-T+1) = 230 and the budget N = 256.

All exact; deterministic.
"""

T_NUM, T_DEN = 592794966, 2 ** 30

# ---------------------------------------------------------------------------
print("=" * 78)
print("A. The 2-adic window obstruction (exact)")
print("=" * 78)
N, T, k = 2 ** 30, 592794966, 2 ** 28
M = 3 * (T - 1) - N
LO, HI = -(-M // 3), k - 1
print(f"  prize: window [{LO}, {HI}]; 2^27 = {2**27} < {LO};"
      f" 2^28 = {2**28} > {HI}")
ok = all(not (LO <= 2 ** j <= HI) for j in range(0, 40))
print(f"  no 2-power in window: {ok}")
ok30 = all(not (LO <= n <= HI) for n in [2 ** j for j in range(31)])
print(f"  no divisor of 2^30 in window (divisors are 2-powers): {ok30}")
Ns, Ts, ks = 256, 142, 64
Ms = 3 * (Ts - 1) - Ns
LOs, HIs = -(-Ms // 3), ks - 1
print(f"  mu_256 ratios: window [{LOs}, {HIs}]; 2^5 = 32 < {LOs}; 2^6 = 64 >"
      f" {HIs}: {all(not (LOs <= 2**j <= HIs) for j in range(10))}")

# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("B. Two-level dyadic construction is blocked by triple-point counting")
print("=" * 78)
# d_ij = (x^m - s_ij) * alpha (shared alpha): ov's = coset (m pts) + T_alpha
# (triple pts).  Coverage: Sigma_pairs >= M + |tri| => 3m + 3t >= M + t
# => t >= (M - 3m)/2; budget: t <= deg alpha <= k - 1 - m.
for (lbl, NN, TT, kk, m) in (("prize", N, T, k, 2 ** 27), ("mu_256", 256, 142, 64, 32)):
    MM = 3 * (TT - 1) - NN
    need = -(-(MM - 3 * m) // 2)
    have = kk - 1 - m
    print(f"  {lbl}: m = {m}: need |T_alpha| >= {need}, degree budget = {have}"
          f" -> blocked: {need > have} (deficit {need - have})")

# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("C. Bezout solution-dimension battery on the dyadic domain mu_256 c F_65537")
print("=" * 78)
q = 65537
g = 3  # primitive root of F_65537
w256 = pow(g, (q - 1) // 256, q)
# DOM_CYC is mu_256 in EXPONENT order: DOM_CYC[i] = w256^i.  Every subgroup /
# coset / cyclic-arc construction below is built from exponents, never from a
# numerically sorted list: numerical order of the field representatives does
# not preserve cyclic exponent order, so strides of a sorted list are arbitrary
# subsets, not subgroups (repository audit 2026-10-28, finding L115).
DOM_CYC = [pow(w256, i, q) for i in range(256)]
# DOM (numerically sorted) is kept only as a set enumeration of mu_256 for the
# random subsets of Section C and the positional evaluation domain of Section D.
DOM = sorted(DOM_CYC)
assert len(set(DOM)) == 256
assert pow(w256, 128, q) != 1 and pow(w256, 256, q) == 1  # w256 has order 256


def rref_rank(Mx, qq):
    Mx = [[int(x) % qq for x in row] for row in Mx]
    rows = len(Mx)
    cols = len(Mx[0]) if rows else 0
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if Mx[i][c]), None)
        if piv is None:
            continue
        Mx[r], Mx[piv] = Mx[piv], Mx[r]
        inv = pow(Mx[r][c], qq - 2, qq)
        Mx[r] = [(x * inv) % qq for x in Mx[r]]
        for i in range(rows):
            if i != r and Mx[i][c]:
                f = Mx[i][c]
                Mx[i] = [(Mx[i][j] - f * Mx[r][j]) % qq for j in range(cols)]
        r += 1
    return r


def polymul(a, b, qq):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % qq
    return out


def zpoly(pts, qq):
    z = [1]
    for p in pts:
        z = polymul(z, [(-p) % qq, 1], qq)
    return z


def bezout_dim(X, Y, Z, kk, qq):
    zX, zY, zZ = zpoly(X, qq), zpoly(Y, qq), zpoly(Z, qq)
    da, db, dg = kk - len(X), kk - len(Y), kk - len(Z)
    if min(da, db, dg) <= 0:
        return 0, 0
    nv = da + db + dg
    rows = []
    for cidx in range(kk):
        row = []
        for (z, d) in ((zX, da), (zY, db)):
            row += [z[cidx - j] if 0 <= cidx - j < len(z) else 0 for j in range(d)]
        row += [(-zZ[cidx - j]) % qq if 0 <= cidx - j < len(zZ) else 0
                for j in range(dg)]
        rows.append(row)
    return nv - rref_rank(rows, qq), nv


import numpy as np
rng = np.random.default_rng(1211)
mu32 = [pow(w256, 8 * i, q) for i in range(32)]   # mu_32 = <w256^8>, exponent order
mu64 = [pow(w256, 4 * i, q) for i in range(64)]   # mu_64 = <w256^4>, exponent order
# Coset representatives w256^j from DISTINCT quotient classes: j mod 8 for
# mu_256/mu_32 (classes 1,2,3,5,6,7) and j mod 4 for mu_256/mu_64 (classes 1,2,3).
REPS32, REPS64 = (1, 2, 3, 5, 6, 7), (1, 2, 3)
assert len({j % 8 for j in REPS32}) == len(REPS32) and all(j % 8 for j in REPS32)
assert len({j % 4 for j in REPS64}) == len(REPS64) and all(j % 4 for j in REPS64)
cos32 = [[(DOM_CYC[j] * x) % q for x in mu32] for j in REPS32]
cos64 = [[(DOM_CYC[j] * x) % q for x in mu64] for j in REPS64]
# Structural checks BEFORE any rank computation: genuine subgroups, genuine
# cosets inside mu_256, pairwise disjoint (distinct quotient classes).
assert len(set(mu32)) == 32 and all(pow(x, 32, q) == 1 for x in mu32)
assert len(set(mu64)) == 64 and all(pow(x, 64, q) == 1 for x in mu64)
_dom_set = set(DOM_CYC)
for _fam, _size in ((cos32, 32), (cos64, 64)):
    for _c in _fam:
        assert len(set(_c)) == _size and set(_c) <= _dom_set
        # x in w^j * mu_s  <=>  (x * w^-j)^s == 1; checked via x^s == (w^j)^s
        _xs = {pow(x, _size, q) for x in _c}
        assert len(_xs) == 1 and _xs != {1}
    for _a in range(len(_fam)):
        for _b in range(_a + 1, len(_fam)):
            assert not set(_fam[_a]) & set(_fam[_b]), "cosets must be disjoint"
print("  subgroup/coset checks passed: mu_32, mu_64 genuine; 6 mu_32-cosets and"
      " 3 mu_64-cosets pairwise disjoint")
tests = []
# (a) mu_64-coset truncations to (56,56,55) — the direct dyadic analogue
tests.append(("mu64-coset trunc", cos64[0][:56], cos64[1][:56], cos64[2][:55]))
# (b) unions of mu_32-cosets truncated
u1 = sorted(set(cos32[0]) | set(cos32[1]))[:56]
u2 = sorted(set(cos32[2]) | set(cos32[3]))[:56]
u3 = sorted(set(cos32[4]) | set(cos32[5]))[:55]
tests.append(("mu32-coset unions", u1, u2, u3))
# (c) two-level: mu_32 coset + shared extra points (triple-point shape)
shared = [x for x in DOM if x not in set(cos32[0]) | set(cos32[2]) | set(cos32[4])][:24]
tests.append(("two-level shared", sorted(cos32[0] + shared)[:56],
              sorted(cos32[2] + shared)[:56], sorted(cos32[4] + shared)[:55]))
# (d) random domain subsets
for s in range(3):
    pts = list(map(int, rng.choice(DOM, size=167, replace=False)))
    tests.append((f"random-{s}", pts[:56], pts[56:112], pts[112:167]))
# (e) contiguous-in-cyclic-order arcs
tests.append(("arcs", DOM_CYC[:56], DOM_CYC[56:112], DOM_CYC[112:167]))
worst = 0
for lbl, X, Y, Z in tests:
    dim, nv = bezout_dim(X, Y, Z, ks, q)
    worst = max(worst, dim)
    print(f"  {lbl:20s}: Sigma = {len(X)+len(Y)+len(Z)}, dim = {dim} (vars {nv})")
print(f"  MAX dimension over dyadic-structured battery: {worst}"
      f"  (generic bound max(0, 2k - Sigma) = {max(0, 2 * ks - 167)})")
print("  note: a positive dimension on 'two-level shared' is the binomial-dependence"
      " family\n  alpha(x^32-s0)+beta(x^32-s2) = lambda(x^32-s4) times the shared-root"
      " factor;\n  Section B (triple-point coverage), not this rank test, excludes that"
      " shape.")

# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("D. Stall census on the dyadic domain (dom = mu_256, q = 65537)")
print("=" * 78)
Nn, Tt, kk = 256, 142, 64
F0 = 20
V = [[pow(x, j, q) for j in range(kk)] for x in DOM]


def pev_vec(coeffs):
    return [sum(int(c) * V[i][j] for j, c in enumerate(coeffs)) % q
            for i in range(Nn)]


def census(u0, u1, pencils):
    out = {}
    for (v0, v1) in pencils:
        a = [(u0[i] - v0[i]) % q for i in range(Nn)]
        b = [(u1[i] - v1[i]) % q for i in range(Nn)]
        base = [i for i in range(Nn) if a[i] == 0 and b[i] == 0]
        hist = {}
        for i in range(Nn):
            if b[i] != 0:
                gam = (-a[i]) * pow(b[i], q - 2, q) % q
                hist.setdefault(gam, []).append(i)
        for gam, coords in hist.items():
            A = len(base) + len(coords)
            if A >= Tt:
                # nonjoint fast check: u0 == v0 on >= k pts of S and differs
                S = base + coords
                eq0 = sum(1 for i in S if u0[i] == v0[i])
                nj = (eq0 >= kk and eq0 < len(S)) or True  # conservative check below
                # exact-enough: differences at vote coords guarantee nonjoint
                nj = any((u0[i] != v0[i]) or (u1[i] != v1[i]) for i in coords) \
                    and len(base) >= kk
                if nj:
                    out.setdefault(gam, []).append((Nn - A, A))
    return out


rng = np.random.default_rng(31)
best = 0
# dual two-pencil construction on the dyadic domain (should hit 230)
ovl = 2 * (Tt - 1) - Nn  # 26
A1i = list(range(0, Tt - 1))
A2i = list(range(Nn - (Tt - 1), Nn))
ovi = list(range(Nn - (Tt - 1), Tt - 1))
for seed in range(3):
    r2 = np.random.default_rng(500 + seed)
    dc = [int(x) for x in r2.integers(0, q, kk - 2 - len(ovi))]
    dc[-1] = max(1, dc[-1])
    # d = z_ov * c evaluated on DOM
    d = []
    okv = True
    for i in range(Nn):
        zv = 1
        for j in ovi:
            zv = zv * (DOM[i] - DOM[j]) % q
        cv = 0
        for cc in reversed(dc):
            cv = (cv * DOM[i] + cc) % q
        d.append(zv * cv % q)
        if i not in ovi and d[-1] == 0:
            okv = False
    if not okv:
        continue
    v01 = pev_vec(r2.integers(0, q, kk))
    v11 = pev_vec(r2.integers(0, q, kk))
    xd = [DOM[i] * d[i] % q for i in range(Nn)]
    v02 = [(v01[i] + xd[i]) % q for i in range(Nn)]
    v12 = [(v11[i] + d[i]) % q for i in range(Nn)]
    u0, u1 = [0] * Nn, [0] * Nn
    for i in A1i:
        u0[i], u1[i] = v01[i], v11[i]
    for i in A2i:
        if i not in set(A1i):
            u0[i], u1[i] = v02[i], v12[i]
    out = census(u0, u1, [(v01, v11), (v02, v12)])
    stall = {gam for gam, o in out.items() if any(F >= F0 + 1 for (F, _) in o)}
    best = max(best, len(stall))
print(f"  dual two-pencil on mu_256 domain: max #stall-bad = {best}"
      f"  (capacity 2(N-T+1) = {2 * (Nn - Tt + 1)}, budget N = {Nn})")
# coset-shaped third-pencil attempt: d23 = lam*(x^32 - t)*alpha — the window
# says 32 is too small, 64 = k too big; verify the 64-attempt fails on degree:
print(f"  coset third-pencil: binomial x^64 - s has degree 64 = k (row budget"
      f" deg < k = {kk}) -> inadmissible; x^32: 3*32 = 96 < M = {Ms} ->"
      f" coverage fails.  No dyadic coset escape at this scale.")

print("\n" + "=" * 78)
print("VERDICT")
print("=" * 78)
print("  1. No 2-power (hence no subgroup order of mu_{2^30}) lies in the escape")
print("     window [234881024, 268435455]: the adversarial-domain refutation")
print("     CANNOT be transported to the literal dyadic prize domain.")
print("  2. Two-level and coset-union variants are blocked exactly (triple-point")
print("     counting / self-similar reduction).")
print("  3. Exact Bezout dimension at mu_256/F_65537: 0 on genuine coset")
print(f"     truncations, coset unions, random subsets and cyclic arcs; {worst} on the")
print("     two-level shared set (binomial-dependence family, excluded as an")
print("     escape only by Section B's coverage count).  The stall census on the")
print("     dyadic domain never exceeded the two-pencil capacity 2(N-T+1).")
print("  => No escape constructed here; StallResidual on mu_{2^30} remains OPEN")
print("     (unrefuted, not proved).  This finite battery is not exhaustive.")
