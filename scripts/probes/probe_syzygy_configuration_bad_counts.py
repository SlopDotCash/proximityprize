#!/usr/bin/env python3
"""G88 syzygy-configuration hunt: can rank-deficient stacks beat the generic
planting cap / the wall budget in the LARGE-FIELD regime?

Follow-up (issues #466/#505/#507) to
  * G85: `scripts/probes/probe_rate_half_predecessor_count_largefield.py` +
    `docs/kb/deltastar-466-g85-wall-hypothesis-largefield-probe-2026-07-10.md`
    (generic planting law r_max = 2(n-k)/(t-k) - 1; large-field cells all
    CONSISTENT with the wall budget n), and
  * G87: `Frontier/_G87McaEventSyndromeBridge.lean` (Lean theorem: at production
    shape any stack with >= 64 bad scalars forces a SYZYGY -- a nontrivial
    linear dependence among the per-witness blocks of t-k constraint
    functionals on the 2(n-k)-dim syndrome-pair space).

The single residual after G87: can SYZYGY configurations carry many bad
scalars?  This probe hunts, at the faithful small cells

    n = 32, k = 16, t = 18   (m = t-k = 2, syndrome dim 2(n-k) = 32,
                              generic cap r_max = 15, wall budget = n = 32)
    n = 64, k = 32, t = 34   (m = 2, dim 64, cap 31, budget 64)

in the large-field regime (p far above the G85 collapse threshold
p_count = C(n,t)/n, where generic stacks are certified clean), for stacks
whose bad-scalar count EXCEEDS the generic cap -- and, decisively, the BUDGET.

The syzygy channel (exact linear algebra)
-----------------------------------------
A witness (S, c, gamma) contributes the m = t-k parity functionals of S,
gamma-folded: rows  ell_j (x) (1, gamma)  in F^n (x) F^2 = F^{2n}.  For a
FIXED subset S and r >= 2 DISTINCT gammas the second tensor factor
span{(1,gamma_i)} saturates at dimension 2, so the whole block has rank at
most 2m -- a maximal structural syzygy.  Concretely, two distinct gammas
through the same S force  ell_j(u0) = ell_j(u1) = 0  for all j: BOTH u0|S and
u1|S must be codeword restrictions ("degenerate subset", the a = b = 0 case
of G85's affine-in-gamma reduction).

On a degenerate subset S the parity checks pass for EVERY gamma, but badness
is decided by the pairJoint clause: with v0, v1 the unique codewords agreeing
with u0, u1 on S and d_i := u_i - v_i (zero on S), the line u0 + gamma*u1
agrees with the codeword w = v0 + gamma*v1 on
    A = S  \\cup  { x : d0(x) + gamma*d1(x) = 0 }.
If A = S then v0, v1 joint-agree on A and gamma is NOT bad.  If some x not in
S has d1(x) != 0, then the single scalar  gamma_x = -d0(x)/d1(x)  picks up the
extra agreement point x, |A| >= t+1, and pairJoint FAILS on A (the codeword
agreeing with u0 on >= t+1 > k points of A is forced to be v0, which misses x
whenever d0(x) != 0; symmetrically v1 when d0(x) = 0 since then gamma_x = 0
and d1(x) != 0 breaks the u1 side).  So EACH degenerate subset donates up to
n - t bad scalars, at a rank cost of only 2m rows.

Stacking D degenerate subsets costs 2mD rank out of 2(n-k); as long as
2mD < 2(n-k) (D <= (n-k)/m - 1 generically) a non-codeword-pair stack exists,
predicting up to

    D_max * (n - t)  =  7 * 14  =  98   bad scalars at n = 32  (budget 32!)
                     = 15 * 30  = 450   at n = 64               (budget 64!)

This probe CONSTRUCTS those stacks, enumerates the candidate scalars exactly
(the per-subset candidate set {-d0(x)/d1(x)} is complete for badness via that
subset's codeword pencil), FULLY verifies every candidate against the literal
mcaEvent definition (interpolate w, agreement set, NOT pairJoint), and
recounts every over-cap/over-budget witness on an independent second
interpolation path.  All arithmetic exact (Python bigints), deterministic
seeds.

Families searched (per the brief):
  A. sharedS-degenerate-D : D shared/degenerate subsets (the syzygy channel).
  B. zero-set stacks      : u1 with a large zero set (row collapse attempt).
  C. coset-supported      : u0, u1 supported on an index-2 subgroup coset.
  D. structured (S_i, gamma_i) rank scan without a stack: shared subsets,
     t-1-overlap chains, arithmetic gamma progressions, gammas in a
     multiplicative subgroup -- measuring which configurations are rank
     deficient at all (only shared-S is, and it degenerates into family A).
  E. mixed: D degenerate subsets + generic planted witnesses on the residual
     rank budget (checks additivity of the two channels).

For every stack we also record the RANK of the full gamma-folded witness-row
system of the certified witnesses, so the (rank deficit |-> bad count) law is
measured, not guessed.
"""

import math
import random
import sys

MASTER_SEED = 466_88

# ------------------------------------------------------------------ primality

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(x):
    if x < 2:
        return False
    for q in _MR_BASES:
        if x % q == 0:
            return x == q
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
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


def next_prime_1_mod(n, target):
    p = target + ((1 - target) % n)
    while not is_prime(p):
        p += n
    return p


# --------------------------------------------------------------------- domain

class Domain:
    def __init__(self, n, k, t, p):
        self.n, self.k, self.t, self.p = n, k, t, p
        for a in range(2, 1000):
            g = pow(a, (p - 1) // n, p)
            if pow(g, n // 2, p) != 1 and pow(g, n, p) == 1:
                self.g = g
                break
        else:
            raise RuntimeError("no order-n subgroup generator")
        self.xs = [pow(self.g, i, p) for i in range(n)]


def batch_inverse(vals, p):
    pref, acc = [], 1
    for v in vals:
        pref.append(acc)
        acc = acc * v % p
    inv_acc = pow(acc, p - 2, p)
    out = [0] * len(vals)
    for i in range(len(vals) - 1, -1, -1):
        out[i] = pref[i] * inv_acc % p
        inv_acc = inv_acc * vals[i] % p
    return out


def grs_check_rows(dom, S):
    """(c_i, c_i*x_i) parity rows of RS_k restricted to the t-subset S (t=k+2)."""
    p, xs = dom.p, dom.xs
    pts = [xs[i] for i in S]
    prods = []
    for i, xi in enumerate(pts):
        acc = 1
        for l, xl in enumerate(pts):
            if l != i:
                acc = acc * (xi - xl) % p
        prods.append(acc)
    c = batch_inverse(prods, p)
    return c, [ci * xi % p for ci, xi in zip(c, pts)]


def interp_full(dom, idxs, vals):
    """Full-domain evaluations of the degree<k polynomial through k points."""
    p, xs, n, k = dom.p, dom.xs, dom.n, dom.k
    pts = [xs[i] for i in idxs]
    wden = []
    for j, xj in enumerate(pts):
        acc = 1
        for l, xl in enumerate(pts):
            if l != j:
                acc = acc * (xj - xl) % p
        wden.append(acc)
    wgt = batch_inverse(wden, p)
    idxset = dict(zip(idxs, vals))
    need, pos = [], []
    for r in range(n):
        if r not in idxset:
            for xj in pts:
                need.append((xs[r] - xj) % p)
            pos.append(r)
    invs = batch_inverse(need, p) if need else []
    out = [0] * n
    for i, v in idxset.items():
        out[i] = v % p
    for m, r in enumerate(pos):
        x = xs[r]
        Z = 1
        for xj in pts:
            Z = Z * (x - xj) % p
        acc = 0
        base = m * k
        for j in range(k):
            acc += wgt[j] * vals[j] % p * invs[base + j]
        out[r] = Z * (acc % p) % p
    return out


def agrees_with_code_on(dom, u, A):
    w = interp_full(dom, A[: dom.k], [u[i] for i in A[: dom.k]])
    return all(w[i] == u[i] for i in A)


def verify_bad(dom, u0, u1, gamma, S, alt=False):
    """Literal mcaEvent verification of candidate gamma via subset S.
    alt=True is the independent recount path (different interpolation nodes)."""
    p, n, t, k = dom.p, dom.n, dom.t, dom.k
    line = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
    nodes = list(S[-k:]) if alt else list(S[:k])
    w = interp_full(dom, nodes, [line[i] for i in nodes])
    if any(w[i] != line[i] for i in S):
        return False
    A = [i for i in range(n) if w[i] == line[i]]
    if len(A) < t:
        return False
    if alt:
        A = A[::-1]
    return not (agrees_with_code_on(dom, u0, A) and agrees_with_code_on(dom, u1, A))


# ------------------------------------------------------------ exact nullspace

def nullspace_mod_p(rows, ncols, p):
    mat = [list(r) for r in rows]
    pivots, prow = [], 0
    for col in range(ncols):
        sel = None
        for r in range(prow, len(mat)):
            if mat[r][col] % p:
                sel = r
                break
        if sel is None:
            continue
        mat[prow], mat[sel] = mat[sel], mat[prow]
        inv = pow(mat[prow][col], p - 2, p)
        mat[prow] = [v * inv % p for v in mat[prow]]
        for r in range(len(mat)):
            if r != prow and mat[r][col] % p:
                f = mat[r][col]
                mat[r] = [(v - f * w) % p for v, w in zip(mat[r], mat[prow])]
        pivots.append(col)
        prow += 1
        if prow == len(mat):
            break
    rank = prow
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for r, pc in enumerate(pivots):
            v[pc] = (-mat[r][fc]) % p
        basis.append(v)
    return rank, basis


def rank_mod_p(rows, ncols, p):
    return nullspace_mod_p(rows, ncols, p)[0]


# ------------------------------------------------- constraint-row constructors

def degenerate_rows(dom, S):
    """4 rows on F^{2n}: parity(u0|S) = 0 (2 rows) and parity(u1|S) = 0 (2)."""
    n, p = dom.n, dom.p
    c, cx = grs_check_rows(dom, S)
    rows = []
    for blk in (0, n):
        for row in (c, cx):
            vec = [0] * (2 * n)
            for j, i in enumerate(S):
                vec[blk + i] = row[j]
            rows.append(vec)
    return rows


def witness_rows(dom, gamma, S):
    """2 gamma-folded rows on F^{2n} for the witness (S, gamma)."""
    n, p = dom.n, dom.p
    c, cx = grs_check_rows(dom, S)
    rows = []
    for row in (c, cx):
        vec = [0] * (2 * n)
        for j, i in enumerate(S):
            vec[i] = row[j]
            vec[n + i] = gamma * row[j] % p
        rows.append(vec)
    return rows


def solve_stack(dom, rows, rng, tries=40):
    """Random kernel element of `rows` that is NOT a codeword pair.
    Returns (u0, u1, rank) or (None, None, rank)."""
    n, p = dom.n, dom.p
    rank, basis = nullspace_mod_p(rows, 2 * n, p)
    if rank >= 2 * (n - dom.k):
        return None, None, rank
    for _ in range(tries):
        sol = [0] * (2 * n)
        for b in basis:
            coef = rng.randrange(p)
            for i in range(2 * n):
                sol[i] = (sol[i] + coef * b[i]) % p
        u0, u1 = sol[:n], sol[n:]
        if not (agrees_with_code_on(dom, u0, list(range(n)))
                and agrees_with_code_on(dom, u1, list(range(n)))):
            return u0, u1, rank
    return None, None, rank


# -------------------------------------------- per-degenerate-subset enumeration

def degenerate_gamma_candidates(dom, u0, u1, S):
    """Exact candidate bad scalars of a DEGENERATE subset S:
    gamma_x = -d0(x)/d1(x) over off-S points x with d1(x) != 0, where
    d_i = u_i - v_i and v_i is the unique codeword agreeing with u_i on S.
    Returns [] if S is not degenerate for this stack."""
    n, p, k = dom.n, dom.p, dom.k
    v0 = interp_full(dom, list(S[:k]), [u0[i] for i in S[:k]])
    v1 = interp_full(dom, list(S[:k]), [u1[i] for i in S[:k]])
    if any(v0[i] != u0[i] or v1[i] != u1[i] for i in S):
        return []
    d0 = [(u0[i] - v0[i]) % p for i in range(n)]
    d1 = [(u1[i] - v1[i]) % p for i in range(n)]
    out = []
    for x in range(n):
        if x in S:
            continue
        if d1[x] % p:
            out.append(((-d0[x]) * pow(d1[x], p - 2, p)) % p)
    return out


def analyze_stack(dom, name, u0, u1, subsets, rng, extra_candidates=()):
    """Certified bad-scalar count of one stack: enumerate candidates via the
    per-subset pencils, fully verify each, dedupe, rank the witness rows,
    recount independently when over the generic cap."""
    n, k, t, p = dom.n, dom.k, dom.t, dom.p
    budget, cap = n, 2 * (n - k) // (t - k) - 1
    verified = {}
    for S in subsets:
        for gam in degenerate_gamma_candidates(dom, u0, u1, S):
            if gam not in verified and verify_bad(dom, u0, u1, gam, list(S)):
                verified[gam] = list(S)
    for gam, S in extra_candidates:
        if gam not in verified and verify_bad(dom, u0, u1, gam, list(S)):
            verified[gam] = list(S)
    # structured sweep of extra subsets (windows + random), G85-style, to catch
    # candidates outside the constructed pencils
    sweep = [tuple(sorted((s + i) % n for i in range(t))) for s in range(n)]
    sweep += [tuple(sorted(rng.sample(range(n), t))) for _ in range(2000)]
    for S in sweep:
        c, cx = grs_check_rows(dom, S)
        a1 = sum(ci * u0[i] for ci, i in zip(c, S)) % p
        a2 = sum(ci * u0[i] for ci, i in zip(cx, S)) % p
        b1 = sum(ci * u1[i] for ci, i in zip(c, S)) % p
        b2 = sum(ci * u1[i] for ci, i in zip(cx, S)) % p
        if a1 == a2 == b1 == b2 == 0:
            for gam in degenerate_gamma_candidates(dom, u0, u1, S):
                if gam not in verified and verify_bad(dom, u0, u1, gam, list(S)):
                    verified[gam] = list(S)
            continue
        if b1:
            gam = (p - a1) * pow(b1, p - 2, p) % p
        elif b2:
            gam = (p - a2) * pow(b2, p - 2, p) % p
        else:
            continue
        if (a1 + gam * b1) % p == 0 and (a2 + gam * b2) % p == 0:
            if gam not in verified and verify_bad(dom, u0, u1, gam, list(S)):
                verified[gam] = list(S)
    certified = len(verified)
    # rank of the gamma-folded witness rows of every certified witness
    rows = []
    for gam, S in verified.items():
        rows.extend(witness_rows(dom, gam, S))
    rank = rank_mod_p(rows, 2 * n, p) if rows else 0
    deficit = 2 * certified - rank
    if certified > cap:  # independent recount, second interpolation path
        recount = sum(1 for gam, S in verified.items()
                      if verify_bad(dom, u0, u1, gam, S, alt=True))
        assert recount == certified, \
            f"recount mismatch {recount} != {certified} ({name})"
        # third path: re-derive each gamma from the parity pencil of a shifted
        # t-subset of its own agreement set
        for gam, S in verified.items():
            line = [(u0[i] + gam * u1[i]) % p for i in range(n)]
            w = interp_full(dom, S[:k], [line[i] for i in S[:k]])
            A = [i for i in range(n) if w[i] == line[i]]
            assert len(A) >= t
            S2 = A[-t:]
            assert verify_bad(dom, u0, u1, gam, S2), \
                f"agreement-shift reverify failed ({name}, gamma={gam})"
    return {"stack": name, "certified": certified, "rank": rank,
            "deficit": deficit, "witnesses": verified,
            "over_cap": certified > cap, "over_budget": certified > budget}


# ---------------------------------------------------------------------- cells

def run_cell(n, k, t, p, tag, results):
    dom = Domain(n, k, t, p)
    rng = random.Random(f"{MASTER_SEED}-{n}-{p}-{tag}")
    budget, m = n, t - k
    cap = 2 * (n - k) // m - 1
    dmax = (n - k) // m - 1          # generic max degenerate subsets
    print(f"\n== CELL n={n} k={k} t={t} p={p} (~2^{math.log2(p):.2f}, {tag})"
          f"  m={m} dim=2(n-k)={2*(n-k)} cap={cap} budget={budget} Dmax={dmax}")
    rows_out = []

    def record(res, family, note=""):
        v = "OVER-BUDGET" if res["over_budget"] else \
            ("OVER-CAP" if res["over_cap"] else "within-cap")
        print(f"   {family:26s} certified={res['certified']:4d} "
              f"rank={res['rank']:3d} deficit={res['deficit']:4d} "
              f"-> {v} {note}")
        rows_out.append(dict(n=n, p=p, tag=tag, family=family,
                             certified=res["certified"], rank=res["rank"],
                             deficit=res["deficit"], cap=cap, budget=budget,
                             verdict=v))
        return res

    worst = None
    # ---- Family A: D shared/degenerate subsets --------------------------
    for D in sorted({1, 2, dmax // 2, dmax - 1, dmax, dmax + 1}):
        if D < 1:
            continue
        subsets = [tuple(sorted(rng.sample(range(n), t))) for _ in range(D)]
        rows = []
        for S in subsets:
            rows.extend(degenerate_rows(dom, S))
        u0, u1, rank0 = solve_stack(dom, rows, rng)
        name = f"A-degenerate-D{D}"
        if u0 is None:
            print(f"   {name:26s} UNPLANTABLE (constraint rank {rank0} >= "
                  f"{2*(n-k)})")
            rows_out.append(dict(n=n, p=p, tag=tag, family=name, certified=0,
                                 rank=rank0, deficit=0, cap=cap, budget=budget,
                                 verdict="UNPLANTABLE"))
            continue
        res = record(analyze_stack(dom, name, u0, u1, subsets, rng),
                     name, f"(constraintRank={rank0}, predicted<= {D*(n-t)})")
        res["u0"], res["u1"], res["subsets"] = u0, u1, subsets
        if worst is None or res["certified"] > worst["certified"]:
            worst = res
    # ---- Family E: degenerate + generic planted on residual budget ------
    D = dmax - 1
    subsets = [tuple(sorted(rng.sample(range(n), t))) for _ in range(D)]
    rows = []
    for S in subsets:
        rows.extend(degenerate_rows(dom, S))
    extra = []
    for _ in range((2 * (n - k) - len(rows) - 1) // (2 * m)):
        gam = rng.randrange(1, p)
        S = tuple(sorted(rng.sample(range(n), t)))
        extra.append((gam, S))
        rows.extend(witness_rows(dom, gam, S))
    u0, u1, rank0 = solve_stack(dom, rows, rng)
    if u0 is not None:
        res = record(analyze_stack(dom, f"E-mixed-D{D}+r{len(extra)}",
                                   u0, u1, subsets, rng,
                                   extra_candidates=extra),
                     f"E-mixed-D{D}+r{len(extra)}", f"(constraintRank={rank0})")
        res["u0"], res["u1"], res["subsets"] = u0, u1, subsets
        if worst is None or res["certified"] > worst["certified"]:
            worst = res
    # ---- Family B: large zero set on u1 ---------------------------------
    Z = sorted(rng.sample(range(n), min(n - 2, t + 4)))
    u1b = [0] * n
    for i in range(n):
        if i not in Z:
            u1b[i] = 1 + rng.randrange(p - 1)
    u0b = [rng.randrange(p) for _ in range(n)]
    zsubs = [tuple(sorted(rng.sample(Z, t))) for _ in range(20)]
    record(analyze_stack(dom, "B-zeroset-u1", u0b, u1b, zsubs, rng),
           "B-zeroset-u1", f"(|Z|={len(Z)})")
    # ---- Family C: coset-supported ---------------------------------------
    u0c = [rng.randrange(p) if i % 2 == 0 else 0 for i in range(n)]
    u1c = [rng.randrange(p) if i % 2 == 0 else 0 for i in range(n)]
    record(analyze_stack(dom, "C-coset", u0c, u1c, [], rng), "C-coset")
    # ---- Family D: structured (S, gamma) rank scan (no stack) ------------
    print("   -- family D rank scan of structured (S_i, gamma_i) systems --")
    scans = []
    S0 = tuple(sorted(rng.sample(range(n), t)))
    scans.append(("D-sharedS-r8", [(rng.randrange(1, p), S0) for _ in range(8)]))
    base = sorted(rng.sample(range(n), t + 8))
    chain = [tuple(sorted(base[i:i + t])) for i in range(8)]
    scans.append(("D-chain-overlap-r8",
                  [(rng.randrange(1, p), S) for S in chain]))
    a0, d = rng.randrange(1, p), rng.randrange(1, p)
    scans.append(("D-gammaAP-r8",
                  [((a0 + i * d) % p, tuple(sorted(rng.sample(range(n), t))))
                   for i in range(8)]))
    g0 = pow(rng.randrange(2, p - 1), (p - 1) // math.gcd(p - 1, 64), p)
    scans.append(("D-gammaMultSubgroup-r8",
                  [(pow(g0, i + 1, p), tuple(sorted(rng.sample(range(n), t))))
                   for i in range(8)]))
    for name, plan in scans:
        rows = []
        for gam, S in plan:
            rows.extend(witness_rows(dom, gam, S))
        rank = rank_mod_p(rows, 2 * n, p)
        print(f"   {name:26s} rows={len(rows):3d} rank={rank:3d} "
              f"deficit={len(rows)-rank}")
    # ---- reproduction line for the worst over-budget stack ---------------
    if worst is not None and worst["over_budget"]:
        print(f"\n   REPRO (worst over-budget stack, {worst['stack']}):")
        print(f"   p={p}")
        print(f"   subsets={worst['subsets']}")
        print(f"   u0={worst['u0']}")
        print(f"   u1={worst['u1']}")
        gams = sorted(worst["witnesses"])
        print(f"   certified bad gammas ({len(gams)}): {gams}")
    return rows_out


def run():
    print("G88 syzygy-configuration hunt (large-field regime)")
    print("cap = 2(n-k)/(t-k) - 1 (generic planting law, G85);"
          " budget = n (wall analogue)")
    results = []
    # n=32: p_count = C(32,18)/32 ~ 2^23.8; probe at 2^30 and 2^40 (both >>)
    n, k, t = 32, 16, 18
    for tag, tgt in (("2^30", 1 << 30), ("2^40", 1 << 40)):
        results += run_cell(n, k, t, next_prime_1_mod(n, tgt), tag, results)
    # n=64: p_count ~ 2^54.5; probe at 2^60
    n, k, t = 64, 32, 34
    for tag, tgt in (("2^60", 1 << 60),):
        results += run_cell(n, k, t, next_prime_1_mod(n, tgt), tag, results)

    print("\n\nSUMMARY (certified = fully verified, exact, deduped;"
          " deficit = 2*certified - witnessRowRank)")
    print("| n | p tag | family | certified | rank | deficit | cap | budget"
          " | verdict |")
    print("|---|---|---|---|---|---|---|---|---|")
    for r in results:
        print(f"| {r['n']} | {r['tag']} | {r['family']} | {r['certified']} "
              f"| {r['rank']} | {r['deficit']} | {r['cap']} | {r['budget']} "
              f"| {r['verdict']} |")

    over = [r for r in results if r["verdict"] == "OVER-BUDGET"]
    print(f"\nDECISIVE VERDICT (question 3): "
          f"{'WALL BUDGET ANALOGUE REFUTED at large p' if over else 'survives'}"
          f" -- {len(over)} over-budget stacks certified.")
    # production extrapolation arithmetic (exact integers)
    npd, kpd = 1 << 30, 1 << 29
    m = (1 << 24) + 1
    tpd = kpd + m
    Dmax = (npd - kpd) // m - 1
    print("\nPRODUCTION EXTRAPOLATION (n=2^30, k=2^29, t-k=2^24+1):")
    print(f"  D_max = (n-k)/(t-k) - 1 = {Dmax}")
    print(f"  syzygy-channel bad-scalar yield ~ D_max*(n-t) = "
          f"{Dmax * (npd - tpd)} (~2^{math.log2(max(1, Dmax*(npd-tpd))):.2f})"
          f" vs budget n = {npd} (~2^30)")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    run()
