#!/usr/bin/env python3
"""G85 large-field probe of the rate-half predecessor-count wall hypothesis.

Follow-up to G84 (`probe_rate_half_predecessor_count_small_scale.py`,
`docs/kb/deltastar-466-g84-wall-hypothesis-smallscale-probe-2026-07-10.md`).

G84 refuted the small-field ANALOGUES of the production hypothesis

  #{gamma : mcaEvent C (predecessorRadius n a) u0 u1 gamma} <= n     (budget = n)

(production: n = 2^30, k = 2^29, a = 31*2^24, threshold t = k + 2^24 + 1,
P = 2^30*(2^128+192)+1) at every cell with p = poly(n), and predicted the
refutations are small-field artifacts: the first-moment heuristic
  E[#witness (S, w) pairs per gamma]  ~ C(n,t) * p^{-(t-k)}
  E[#bad gamma per stack]             ~ C(n,t) * p^{-(t-k)+1}
collapses once p >> C(n,t)^{1/(t-k)}.  This probe tests that prediction at the
faithful cell n = 64, k = 32, t = 34 (t - k = 2; both G84 translations coincide,
64 | n), across primes bracketing

  p* := C(64,34)^{1/(t-k)} = isqrt(C(64,34))     (saturation threshold: below it
        the heuristic says EVERY gamma is bad),
  p_count := C(64,34)/n                          (count threshold: below it the
        heuristic bad COUNT still exceeds the budget n even though the bad
        FRACTION is < 1).

Exact computational skeleton (same reduction as G84, sharpened)
---------------------------------------------------------------
gamma is bad  <=>  exists codeword w, A_w = {i : w i = (u0+gamma*u1) i},
                   |A_w| >= t, NOT pairJointAgreesOn C A_w u0 u1.
For a fixed t-subset S, "some codeword agrees with the line on ALL of S" is
equivalent to the two GRS parity checks (dual of RS_k on t = k+2 points):
  sum_{i in S} c_i * x_i^j * line_i = 0,  j = 0, 1,
  c_i := 1 / prod_{l in S, l != i} (x_i - x_l).
Writing a_j = H_j(u0|S), b_j = H_j(u1|S), the condition on gamma is the AFFINE
system  a + gamma * b = 0  in F^2: at most ONE bad-candidate gamma per subset S
unless a = b = 0 (degenerate subset: every gamma passes the parity check).
Hence:
  * CONSTRUCTIVE (importance) channel: enumerate a pool of t-subsets S, solve
    for the unique candidate gamma per S, then FULLY verify mcaEvent for each
    candidate (interpolate w, compute A_w, check NOT pairJoint).  Every verified
    gamma is a CERTIFIED witness => certified lower bound on the bad count.
    This is exactly the (S, c)-pair construction: rigorous in the refutation
    direction.
  * UNIFORM gamma sampling: because badness-via-S is affine in gamma, a
    uniformly sampled gamma is bad via the pool iff it lies in the enumerated
    candidate set (or a degenerate subset exists); the Monte Carlo below is a
    literal seeded sampler run against that reduction plus full verification.
  * PLANTED channel (the only channel that survives large p): choose r distinct
    gammas and t-subsets S_1..S_r, and solve the HOMOGENEOUS linear system
      H_{S_j}(u0|S_j) + gamma_j * H_{S_j}(u1|S_j) = 0,  j = 1..r
    (2r equations, 2n unknowns).  The kernel always contains the 2k-dimensional
    codeword-pair space {(v0, v1)} (never bad).  Non-codeword solutions exist
    iff rank < 2(n-k), i.e. generically iff  r <= (n-k) - 1  (t-k = 2), giving
    the LINEAR-CHANNEL LAW: max plantable distinct bad gammas
      r_max = 2(n-k)/(t-k) - 1   (= 31 at n=64; = 15 at n=32;
                                  ~ 2^30/(2^24+1) ~ 63 << 2^30 at production).

Secondary sweep at n = 32, k = 16, t = k+2 = 18 (G84 structural translation,
same margin shape t-k = 2): there C(32,18) = 471435600 is small enough that a
multi-million-subset pool CERTIFIES refutations through ~2*p*, so the collapse
curve is *measured*, not just heuristic, across its threshold.

All arithmetic exact (Python bigints; numpy int64 fast path only when p < 2^31
so products < 2^62 stay exact).  Deterministic seeds.  Every REFUTED verdict is
re-verified witness-by-witness with an independent second interpolation path.
"""

import math
import random
import sys

try:
    import numpy as np
    HAVE_NUMPY = True
except ImportError:
    HAVE_NUMPY = False

MASTER_SEED = 466_85
SAMPLE_N = 10_000          # uniform gamma samples per stack
NUMPY_P_MAX = (1 << 31) - 1  # int64 exactness bound: p^2 < 2^62
VERIFY_CAP_EXTRA = 100     # verify up to budget + this many distinct candidates

# ------------------------------------------------------------------ primality

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)  # deterministic < 3.3e24


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
    """Smallest prime p >= target with p == 1 (mod n)."""
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
    """Montgomery batch inversion (one powmod for the whole list)."""
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
    """(c_i, c_i * x_i) parity rows of RS_k restricted to the t-subset S."""
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
    """Evaluations on the full domain of the degree<k polynomial through the k
    points (xs[idxs[j]], vals[j]) (barycentric, batch-inverted)."""
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
    """True iff some codeword agrees with u on ALL of A (|A| >= k => unique)."""
    w = interp_full(dom, A[: dom.k], [u[i] for i in A[: dom.k]])
    return all(w[i] == u[i] for i in A)


def verify_bad(dom, u0, u1, gamma, S, alt=False):
    """Full mcaEvent verification of candidate gamma via subset S.
    alt=True uses an independent interpolation node set (recount path)."""
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
        A = A[::-1]  # different node choice inside the pairJoint checks too
    return not (agrees_with_code_on(dom, u0, A) and agrees_with_code_on(dom, u1, A))


# ------------------------------------------------------------------- the pool

def build_pool(dom, M, rng):
    """Pool of t-subsets: contiguous windows, stride cosets, then random."""
    n, t = dom.n, dom.t
    seen = set()
    for s in range(n):
        seen.add(tuple(sorted((s + i) % n for i in range(t))))
    for stride in (2, 4):
        for off in range(stride):
            idx = sorted(set((off + stride * i) % n for i in range(t)))
            if len(idx) == t:
                seen.add(tuple(idx))
    pool = list(seen)
    while len(pool) < M:
        cand = tuple(sorted(rng.sample(range(n), t)))
        pool.append(cand)  # dup subsets harmless (dedup happens on gammas)
    return pool[:M] if len(pool) > M else pool


class PoolChecks:
    """Precomputed parity rows for every subset in the pool (stack-independent)."""

    def __init__(self, dom, pool):
        self.dom, self.pool = dom, pool
        self.numpy = HAVE_NUMPY and dom.p <= NUMPY_P_MAX
        if self.numpy:
            self._build_numpy()
        else:
            self.rows = [grs_check_rows(dom, S) for S in pool]

    def _build_numpy(self):
        dom, pool = self.dom, self.pool
        p, t = dom.p, dom.t
        idx = np.array(pool, dtype=np.int64)
        xs = np.array(dom.xs, dtype=np.int64)
        M = len(pool)
        c = np.empty((M, t), dtype=np.int64)
        chunk = max(1, 60_000_000 // (t * t))
        for lo in range(0, M, chunk):
            X = xs[idx[lo: lo + chunk]]                      # (B, t)
            acc = np.ones_like(X)
            for l in range(t):
                d = (X - X[:, l][:, None]) % p
                d[:, l] = 1
                acc = acc * d % p
            c[lo: lo + chunk] = self._inv_np(acc, p)
        self.idx = idx
        self.c = c
        self.cx = c * xs[idx] % p

    @staticmethod
    def _inv_np(a, p):
        r = np.ones_like(a)
        base = a % p
        e = p - 2
        while e:
            if e & 1:
                r = r * base % p
            base = base * base % p
            e >>= 1
        return r

    def candidates(self, u0, u1):
        """Return ({gamma: subset_index}, [degenerate subset indices])."""
        p = self.dom.p
        if self.numpy:
            u0a = np.array(u0, dtype=np.int64)
            u1a = np.array(u1, dtype=np.int64)
            U0, U1 = u0a[self.idx], u1a[self.idx]
            a1 = (self.c * U0 % p).sum(1) % p
            a2 = (self.cx * U0 % p).sum(1) % p
            b1 = (self.c * U1 % p).sum(1) % p
            b2 = (self.cx * U1 % p).sum(1) % p
            deg = (a1 == 0) & (a2 == 0) & (b1 == 0) & (b2 == 0)
            piv1 = b1 != 0
            piv2 = (~piv1) & (b2 != 0)
            g = np.zeros_like(a1)
            if piv1.any():
                g[piv1] = (p - a1[piv1]) % p * self._inv_np(b1[piv1], p) % p
            if piv2.any():
                g[piv2] = (p - a2[piv2]) % p * self._inv_np(b2[piv2], p) % p
            ok = (piv1 | piv2) \
                & ((a1 + g * b1) % p == 0) & ((a2 + g * b2) % p == 0)
            cand = {}
            for i in np.nonzero(ok)[0]:
                cand.setdefault(int(g[i]), int(i))
            return cand, [int(i) for i in np.nonzero(deg)[0]]
        cand, degen = {}, []
        for si, S in enumerate(self.pool):
            c, cx = self.rows[si]
            a1 = a2 = b1 = b2 = 0
            for j, i in enumerate(S):
                a1 += c[j] * u0[i]
                a2 += cx[j] * u0[i]
                b1 += c[j] * u1[i]
                b2 += cx[j] * u1[i]
            a1, a2, b1, b2 = a1 % p, a2 % p, b1 % p, b2 % p
            if a1 == a2 == b1 == b2 == 0:
                degen.append(si)
                continue
            if b1:
                g = (p - a1) * pow(b1, p - 2, p) % p
            elif b2:
                g = (p - a2) * pow(b2, p - 2, p) % p
            else:
                continue
            if (a1 + g * b1) % p == 0 and (a2 + g * b2) % p == 0:
                cand.setdefault(g, si)
        return cand, degen


# ------------------------------------------------------------- planted stacks

def nullspace_mod_p(rows, ncols, p):
    """(rank, basis) of the kernel of the row list, exact mod-p Gauss."""
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


def make_planted(dom, r, rng):
    """Try to plant r distinct bad gammas.  Returns
    (u0, u1, [(gamma_j, S_j)], rank) or (None, None, plan, rank) on failure."""
    n, p, t = dom.n, dom.p, dom.t
    gammas = rng.sample(range(1, min(p, 1 << 62)), r) if p < (1 << 62) else \
        [rng.randrange(1, p) for _ in range(r)]
    plan, rows = [], []
    for gam in gammas:
        S = tuple(sorted(rng.sample(range(n), t)))
        plan.append((gam, S))
        c, cx = grs_check_rows(dom, S)
        for row in (c, cx):
            vec = [0] * (2 * n)
            for j, i in enumerate(S):
                vec[i] = row[j]
                vec[n + i] = gam * row[j] % p
            rows.append(vec)
    rank, basis = nullspace_mod_p(rows, 2 * n, p)
    if rank >= 2 * (n - dom.k):     # kernel = codeword pairs only: no bad stack
        return None, None, plan, rank
    for _ in range(20):
        sol = [0] * (2 * n)
        for b in basis:
            coef = rng.randrange(p)
            for i in range(2 * n):
                sol[i] = (sol[i] + coef * b[i]) % p
        u0, u1 = sol[:n], sol[n:]
        if not (agrees_with_code_on(dom, u0, list(range(n)))
                and agrees_with_code_on(dom, u1, list(range(n)))):
            return u0, u1, plan, rank
    return None, None, plan, rank


# ------------------------------------------------------------------- stacks

def random_codeword(dom, rng):
    coeffs = [rng.randrange(dom.p) for _ in range(dom.k)]
    out = []
    for x in dom.xs:
        acc = 0
        for cf in reversed(coeffs):
            acc = (acc * x + cf) % dom.p
        out.append(acc)
    return out


def make_stacks(dom, rng):
    """G84 battery (trimmed): the worst small-scale families + random."""
    n, p, k, t = dom.n, dom.p, dom.k, dom.t
    stacks = []

    def rvec():
        return [rng.randrange(p) for _ in range(n)]

    for i in range(5):
        stacks.append((f"random-{i}", rvec(), rvec()))
    stacks.append(("codeword-pair", random_codeword(dom, rng),
                   random_codeword(dom, rng)))
    e = n - t
    for i in range(2):
        c = random_codeword(dom, rng)
        u0 = list(c)
        for j in rng.sample(range(n), max(e, 1)):
            u0[j] = (u0[j] + 1 + rng.randrange(p - 1)) % p
        stacks.append((f"near-codeword-{i}",
                       u0, rvec() if i % 2 == 0 else random_codeword(dom, rng)))
    for i in range(2):
        c1, c2 = random_codeword(dom, rng), random_codeword(dom, rng)
        c3, c4 = random_codeword(dom, rng), random_codeword(dom, rng)
        cut = t - 1
        stacks.append((f"split-codeword-{i}",
                       [c1[j] if j < cut else c2[j] for j in range(n)],
                       [c3[j] if j < cut else c4[j] for j in range(n)]))
    stacks.append(("monomial-k-k1",
                   [pow(x, k, p) for x in dom.xs],
                   [pow(x, k + 1, p) for x in dom.xs]))
    stacks.append(("subgroup-supported",
                   [rng.randrange(p) if j % 2 == 0 else 0 for j in range(n)],
                   [rng.randrange(p) if j % 2 == 1 else 0 for j in range(n)]))
    u0s, u1s = [0] * n, [0] * n
    for j in rng.sample(range(n), n - t + 1):
        u0s[j] = 1 + rng.randrange(p - 1)
    for j in rng.sample(range(n), n - t + 1):
        u1s[j] = 1 + rng.randrange(p - 1)
    stacks.append(("spike", u0s, u1s))
    return stacks


# ------------------------------------------------------------- cell analysis

def analyze_stack(dom, checks, name, u0, u1, rng, planted_plan=None):
    """Certified bad-gamma lower bound + sampled fraction for one stack."""
    n, p = dom.n, dom.p
    budget = n
    cand, degen = checks.candidates(u0, u1)
    verified = {}
    # planted witnesses first (their subsets are not in the shared pool)
    if planted_plan:
        for gam, S in planted_plan:
            if gam not in verified and verify_bad(dom, u0, u1, gam, list(S)):
                verified[gam] = ("planted", list(S))
    cap = budget + VERIFY_CAP_EXTRA
    for gam in sorted(cand):
        if len(verified) >= cap:
            break
        if gam in verified:
            continue
        S = list(checks.pool[cand[gam]])
        if verify_bad(dom, u0, u1, gam, S):
            verified[gam] = ("pool", S)
    # degenerate all-gamma subsets: every gamma passes the parity check there;
    # verify a spread of gammas through the first such subset
    degen_all_bad = False
    degen_probe_hits = 0
    if degen and len(verified) <= budget:
        S = list(checks.pool[degen[0]])
        probe = {rng.randrange(p) for _ in range(min(p, budget + 2 + 16))}
        for gam in probe:
            if verify_bad(dom, u0, u1, gam, S):
                degen_probe_hits += 1
                if gam not in verified:
                    verified[gam] = ("degenerate", S)
        degen_all_bad = degen_probe_hits == len(probe) and degen_probe_hits > 0
    certified = len(verified)
    # literal uniform-gamma Monte Carlo (badness-via-pool is affine in gamma,
    # so pool-relative badness of a sample = membership in the candidate set /
    # degenerate-subset verification; every hit is fully verified)
    srng = random.Random(f"{MASTER_SEED}-{name}-{p}-sample")
    hits = 0
    memo = {}
    for _ in range(SAMPLE_N):
        gam = srng.randrange(p)
        if gam in verified:
            hits += 1
        elif gam in cand:
            if gam not in memo:
                memo[gam] = verify_bad(dom, u0, u1, gam,
                                       list(checks.pool[cand[gam]]))
            hits += memo[gam]
        elif degen and degen_probe_hits > 0 and \
                verify_bad(dom, u0, u1, gam, list(checks.pool[degen[0]])):
            # only worth a full check when the degenerate probe found any bad
            # gamma at all (a degenerate subset with a 0/18 probe is a
            # codeword-pair-type subset: parity-degenerate but pairJoint)
            hits += 1
    frac = hits / SAMPLE_N
    refuted = certified > budget
    if refuted:  # independent recount of every witness, second interpolation path
        recount = sum(
            1 for gam, (_, S) in verified.items()
            if verify_bad(dom, u0, u1, gam, S, alt=True))
        assert recount == certified, \
            f"recount mismatch {recount} != {certified} ({name}, p={p})"
    return {
        "stack": name, "certified": certified, "frac": frac,
        "degen_all": degen_all_bad, "refuted": refuted,
        "n_candidates": len(cand) + len(degen),
    }


def run_cell(n, k, t, p, tag, M, rng_seed, results):
    dom = Domain(n, k, t, p)
    rng = random.Random(f"{MASTER_SEED}-{n}-{p}-{rng_seed}")
    pool = build_pool(dom, M, rng)
    checks = PoolChecks(dom, pool)
    budget = n
    C = math.comb(n, t)
    heur_frac = min(1.0, C / p**2)
    heur_count = C / p
    rows = []
    for name, u0, u1 in make_stacks(dom, rng):
        rows.append(analyze_stack(dom, checks, name, u0, u1, rng))
    # planted stacks around the linear-channel cap r_max = (n-k) - 1
    rmax = (n - k) - 1
    for r in (rmax // 2, rmax, rmax + 1, rmax + 2):
        u0, u1, plan, rank = make_planted(dom, r, rng)
        name = f"planted-r{r}"
        if u0 is None:
            rows.append({"stack": name, "certified": 0, "frac": 0.0,
                         "degen_all": False, "refuted": False,
                         "n_candidates": 0,
                         "note": f"UNPLANTABLE rank={rank}>=2(n-k)={2*(n-k)}"})
            continue
        res = analyze_stack(dom, checks, name, u0, u1, rng, planted_plan=plan)
        res["note"] = f"rank={rank}"
        rows.append(res)
    worst = max(rows, key=lambda r: r["certified"])
    verdict = "REFUTED-CERTIFIED" if worst["certified"] > budget else \
        "CONSISTENT(no violation found)"
    coverage = len(pool) / p
    print(f"\n== n={n} t={t} p={p} (~2^{math.log2(p):.1f}, {tag}) "
          f"pool M={len(pool)} coverage M/p={coverage:.2e}")
    print(f"   heuristic: per-gamma frac ~ min(1, C/p^2) = {heur_frac:.3e},"
          f" count ~ C/p = {heur_count:.3e}, budget = {budget}")
    for r in rows:
        note = r.get("note", "")
        print(f"   {r['stack']:22s} certifiedLB={r['certified']:6d} "
              f"sampledFrac={r['frac']:.4f} cand={r['n_candidates']:6d} "
              f"{'ALL-GAMMA-DEGEN ' if r['degen_all'] else ''}{note}")
    print(f"   worst stack: {worst['stack']} certifiedLB={worst['certified']} "
          f"-> {verdict}")
    results.append(dict(n=n, t=t, p=p, tag=tag, M=len(pool),
                        worst=worst["certified"], worst_stack=worst["stack"],
                        frac=worst["frac"], heur_count=heur_count,
                        heur_frac=heur_frac, budget=budget, verdict=verdict))


# ----------------------------------------------------------------------- main

def run():
    print("G85 large-field probe: rate-half predecessor-count wall hypothesis")
    print("faithful cell n=64 k=32 t=34 (t-k=2); secondary n=32 k=16 t=18")
    C64, C32 = math.comb(64, 34), math.comb(32, 18)
    ps64, ps32 = math.isqrt(C64), math.isqrt(C32)
    print(f"\nC(64,34) = {C64}  (~2^{math.log2(C64):.2f})")
    print(f"p*(64)   = C(64,34)^(1/2) = {ps64}  (~2^{math.log2(ps64):.2f})")
    print(f"p_count(64) = C(64,34)/64 = {C64 // 64}  (~2^{math.log2(C64 / 64):.2f})")
    print(f"C(32,18) = {C32};  p*(32) = {ps32};  p_count(32) = {C32 // 32}")
    print(f"linear-channel planting cap r_max = (n-k)-1: 31 at n=64, 15 at n=32")

    results = []

    # --- n = 32 secondary sweep (measured collapse: pool certifies through
    #     ~2 p*; beyond that the pool channel thins as M/p and the planted
    #     channel floor r_max = 15 takes over)
    n, k, t = 32, 16, 18
    targets32 = [("p*/8", ps32 // 8), ("p*/2", ps32 // 2), ("p*", ps32),
                 ("2p*", 2 * ps32), ("8p*", 8 * ps32),
                 ("64p*", 64 * ps32), ("p_count", C32 // 32),
                 ("2^40", 1 << 40)]
    for tag, tgt in targets32:
        p = next_prime_1_mod(n, max(tgt, n + 1))
        M = 2_000_000 if (HAVE_NUMPY and p <= NUMPY_P_MAX) else 20_000
        run_cell(n, k, t, p, tag, M, "n32", results)

    # --- n = 64 faithful sweep across p* and beyond
    n, k, t = 64, 32, 34
    targets64 = [("p*/8", ps64 // 8), ("p*/2", ps64 // 2), ("p*", ps64),
                 ("2p*", 2 * ps64), ("8p*", 8 * ps64),
                 ("2^54", 1 << 54), ("p_count", C64 // 64),
                 ("2^57", 1 << 57), ("2^80", 1 << 80)]
    for tag, tgt in targets64:
        p = next_prime_1_mod(n, max(tgt, n + 1))
        M = 1_000_000 if (HAVE_NUMPY and p <= NUMPY_P_MAX) else 20_000
        run_cell(n, k, t, p, tag, M, "n64", results)

    # ------------------------------------------------------------- summary
    print("\n\nCOLLAPSE CURVE (worst stack per cell; certified = rigorous lower"
          " bound;\nheuristic count = C(n,t)/p first-moment law)")
    print("| n | tag | p | log2 p | pool M | certified LB (worst) | worst stack"
          " | sampled frac | heuristic count | budget | verdict |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for r in results:
        print(f"| {r['n']} | {r['tag']} | {r['p']} | {math.log2(r['p']):.2f} "
              f"| {r['M']} | {r['worst']} | {r['worst_stack']} "
              f"| {r['frac']:.4f} | {r['heur_count']:.3e} | {r['budget']} "
              f"| {r['verdict']} |")

    print("\nHONEST SCOPE / production extrapolation")
    print("- Certified lower bounds come from the exact affine-in-gamma per-"
          "subset\n  reduction; a CONSISTENT verdict only means the pool+planted"
          " channels found\n  no violation (pool coverage M/p is printed; it is"
          " vanishing at large p).")
    print("- First-moment law: bad count ~ C(n,t)*p^(k-t+1) + linear channel"
          " ~ 2(n-k)/(t-k).")
    m = 1 << 24
    npd, kpd = 1 << 30, 1 << 29
    tpd = kpd + m + 1
    # log2 C(2^30, 2^29 + 2^24 + 1) via entropy/normal approximation
    log2C = npd - 2 * m * m / (npd * math.log(2)) - 0.5 * math.log2(math.pi * npd / 2)
    log2p = math.log2(npd) + 128 + math.log2(1 + 192 / 2**128)
    log2_comb = log2C - (tpd - kpd - 1) * log2p
    print(f"- Production (n=2^30, t-k=2^24+1, P~2^158): log2(combinatorial"
          f" count)\n  ~ {log2C:.0f} - (2^24)*{log2p:.1f} ~ {log2_comb:.3e}"
          " (astronomically negative);")
    print(f"  linear channel cap 2(n-k)/(t-k) = 2^30/(2^24+1) ~ "
          f"{2 * (npd - kpd) / (tpd - kpd):.1f} << budget 2^30.")
    print("- This is EVIDENCE (measured collapse + exact channel caps), NOT a"
          " proof:\n  the first-moment law is a heuristic upper story, and only"
          " the lower-bound\n  (planted/constructive) side is rigorous here.")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    run()
