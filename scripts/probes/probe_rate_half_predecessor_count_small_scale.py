#!/usr/bin/env python3
"""G84 red-team probe: small-scale instantiation of the ONE wall hypothesis of the
conditional rate-half production pin
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`
(ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeRateHalfBracket.lean).

Production hypothesis (exact Lean shape)
----------------------------------------
For EVERY stack (u0, u1) in (F_P^n)^2, with
  C  = evalCode g n (k-1)      -- RS, smooth 2^30 subgroup domain, n = 2^30, k = 2^29
  dp = predecessorRadius n a   -- = (a-1)/n with a = 31*2^24, i.e. 31/64 - 2^-30
the bad-scalar count
  #{gamma in F_P : mcaEvent C dp u0 u1 gamma} <= 2^30  (= n; 2n for the second field).

mcaEvent C d u0 u1 gamma  (Errors.lean:216) :=
  exists S, |S| >= (1-d)*n,
    (exists w in C, w = u0 + gamma*u1 on S)  AND  NOT pairJointAgreesOn C S u0 u1
pairJointAgreesOn C S u0 u1 := exists v0 in C, exists v1 in C,
    forall i in S, v0 i = u0 i and v1 i = u1 i.

With d = (a-1)/n the size constraint is |S| >= n - (a-1) =: t (integer, exact).
Production: a = 31*2^24 so t = n - a + 1 = 33*2^24 + 1 = k + m + 1, m := n/64 = 2^24.

Reduction used (proved in comments below, exact, no approximation):
  gamma is bad  <=>  exists codeword w with A_w := {i : w i = line_gamma i},
                     |A_w| >= t, and NOT pairJointAgreesOn C A_w u0 u1.
  (S must be a subset of A_w for its witness codeword; pairJointAgreesOn is
   antitone in S, so NOT pairJoint is monotone in S and S = A_w is optimal;
   pairJoint(A_w) => pairJoint(S) for every S subseteq A_w. Exact equivalence.)
  A codeword agreeing with a vector on ALL of a set A with |A| >= t >= k+1 is
  unique if it exists: it equals the interpolation through any k points of A.

Small-scale translation table (budget analogue: production 2^30 = n -> budget n)
  T-literal    : radius = largest Hamming lattice point strictly below 31/64,
                 i.e. w_lat = ceil(31n/64) - 1, threshold t = n - w_lat.
                 For n in {8,16,32} this DEGENERATES to t = k+1, the predecessor of
                 1/2 -- the rung the Lean file itself REFUTES at production
                 (firstPrime_rateHalf_not_halfPredecessor_badCount_le_length).
  T-structural : keeps the production shape t = k + m + 1 with m = max(1, n/64)
                 (production m = n/64 = 2^24). For n <= 64: t = k + 2.
  n = 64 is the smallest n where the two translations coincide (t = 34) and the
  literal 31/64 predecessor is faithful (64 | n).

Candidate codeword enumeration: exact (all C(n,k) k-subsets) when C(n,k) <= CAP,
else a fixed sampled pool (random + structured subsets) -- sampled cells give a
LOWER bound on the bad count (sufficient for refutation, weaker for survival).

Deterministic (fixed seeds), exact modular arithmetic (int64, p < 2^15 so all
products < 2^30 fit). numpy used only for batched exact integer mod-p linear maps.
"""

import itertools
import random
import sys

try:
    import numpy as np
except ImportError:
    print("ERROR: numpy required", file=sys.stderr)
    sys.exit(1)

SUBSET_CAP = 14000          # exact enumeration iff C(n,k) <= CAP
SAMPLED_POOL = 4000         # random k-subsets in sampled mode
MASTER_SEED = 466_84

# ---------------------------------------------------------------- field utils

def is_prime(x):
    if x < 2:
        return False
    for d in range(2, int(x ** 0.5) + 1):
        if x % d == 0:
            return False
    return True


def primes_1_mod_n(n, count):
    """Smallest `count` primes p = n*c + 1 (analogue of the prize-prime shape
    P = 2^30 * c + 1)."""
    out, c = [], 1
    while len(out) < count:
        p = n * c + 1
        if is_prime(p):
            out.append(p)
        c += 1
    return out


def subgroup_generator(p, n):
    """Element of exact multiplicative order n (n a power of 2, n | p-1)."""
    for a in range(2, p):
        g = pow(a, (p - 1) // n, p)
        if pow(g, n, p) == 1 and pow(g, n // 2, p) != 1:
            return g
    raise RuntimeError("no generator")


# ------------------------------------------------- interpolation machinery

def lagrange_matrix(xs_all, T, p):
    """n x k matrix M with (M @ v) = evaluations on the full domain of the unique
    degree < k polynomial through {(xs_all[T[j]], v[j])}."""
    k = len(T)
    n = len(xs_all)
    pts = [xs_all[i] for i in T]
    # full product poly coeffs of prod (X - x_j), ascending
    P = [1]
    for x in pts:
        Q = [0] * (len(P) + 1)
        for i, c in enumerate(P):
            Q[i] = (Q[i] - c * x) % p
            Q[i + 1] = (Q[i + 1] + c) % p
        P = Q
    M = [[0] * k for _ in range(n)]
    for j, xj in enumerate(pts):
        # synthetic division P / (X - xj): coeffs of degree k-1 poly, ascending
        B = [0] * k
        carry = P[k]
        for deg in range(k - 1, -1, -1):
            B[deg] = carry
            carry = (P[deg] + carry * xj) % p
        # denom = prod_{i != j} (xj - xi)
        denom = 1
        for i, xi in enumerate(pts):
            if i != j:
                denom = denom * (xj - xi) % p
        dinv = pow(denom, p - 2, p)
        for r in range(n):
            x = xs_all[r]
            acc = 0
            for deg in range(k - 1, -1, -1):
                acc = (acc * x + B[deg]) % p
            M[r][j] = acc * dinv % p
    return M


def interpolate_on(xs_all, idxs, vals, p, k):
    """Evaluations on the full domain of the degree<k interpolation through the
    first k points (idxs[j], vals[j]).  Independent slow path (used in the
    pairJoint check and in the recount verifier)."""
    M = lagrange_matrix(xs_all, idxs[:k], p)
    n = len(xs_all)
    out = [0] * n
    for r in range(n):
        acc = 0
        row = M[r]
        for j in range(k):
            acc += row[j] * vals[j]
        out[r] = acc % p
    return out


# ------------------------------------------------------------- the MCA probe

class Cell:
    def __init__(self, n, p, t, label):
        self.n, self.p, self.t, self.label = n, p, t, label
        self.k = n // 2
        self.g = subgroup_generator(p, n)
        self.xs = [pow(self.g, i, p) for i in range(n)]
        # subset pool
        allc = 1
        for i in range(self.k):
            allc = allc * (n - i) // (i + 1)
        self.exact = allc <= SUBSET_CAP
        if self.exact:
            pool = list(itertools.combinations(range(n), self.k))
        else:
            rng = random.Random(f"{MASTER_SEED}-{n}-{p}-pool")
            seen = set()
            # structured subsets: contiguous windows, even/odd strides (subgroup
            # cosets of the smooth domain), interleavings
            for s in range(n):
                seen.add(tuple(sorted((s + i) % n for i in range(self.k))))
            for stride in (2, 4):
                for off in range(stride):
                    idx = [(off + stride * i) % n for i in range(self.k)]
                    if len(set(idx)) == self.k:
                        seen.add(tuple(sorted(idx)))
            while len(seen) < SAMPLED_POOL:
                seen.add(tuple(sorted(rng.sample(range(n), self.k))))
            pool = sorted(seen)
        self.pool = pool
        self.mats = np.array(
            [lagrange_matrix(self.xs, T, p) for T in pool], dtype=np.int64)
        self.pool_idx = np.array(pool, dtype=np.int64)

    def codeword_agreeing_on_all(self, u, A):
        """True iff some codeword agrees with u on ALL of A (|A| >= k)."""
        vals = [u[i] for i in A[: self.k]]
        w = interpolate_on(self.xs, A, vals, self.p, self.k)
        return all(w[i] == u[i] for i in A)

    def bad_gammas(self, u0, u1):
        """Set of bad gamma for stack (u0,u1) using the cell's candidate pool.
        Exact if self.exact, else a lower bound."""
        n, p, t = self.n, self.p, self.t
        u0a = np.array(u0, dtype=np.int64)
        u1a = np.array(u1, dtype=np.int64)
        bad = []
        for gamma in range(p):
            line = (u0a + gamma * u1a) % p
            gathered = line[self.pool_idx]                      # (S, k)
            cands = np.einsum("sij,sj->si", self.mats, gathered) % p
            agree = (cands == line[None, :])
            counts = agree.sum(axis=1)
            hits = np.nonzero(counts >= t)[0]
            if hits.size == 0:
                continue
            seen_w = set()
            isbad = False
            for h in hits:
                wkey = cands[h].tobytes()
                if wkey in seen_w:
                    continue
                seen_w.add(wkey)
                A = [int(i) for i in np.nonzero(agree[h])[0]]
                joint = (self.codeword_agreeing_on_all(u0, A)
                         and self.codeword_agreeing_on_all(u1, A))
                if not joint:
                    isbad = True
                    break
            if isbad:
                bad.append(gamma)
        return bad

    def recount(self, u0, u1):
        """Independent recount (slow path, no numpy einsum) of the bad set."""
        n, p, t, k = self.n, self.p, self.t, self.k
        bad = []
        for gamma in range(p):
            line = [(u0[i] + gamma * u1[i]) % p for i in range(n)]
            seen_w, isbad = set(), False
            for T in self.pool:
                w = interpolate_on(self.xs, list(T), [line[i] for i in T], p, k)
                key = tuple(w)
                if key in seen_w:
                    continue
                seen_w.add(key)
                A = [i for i in range(n) if w[i] == line[i]]
                if len(A) < t:
                    continue
                if not (self.codeword_agreeing_on_all(u0, A)
                        and self.codeword_agreeing_on_all(u1, A)):
                    isbad = True
                    break
            if isbad:
                bad.append(gamma)
        return bad


# ------------------------------------------------------------------- stacks

def random_codeword(rng, cell):
    coeffs = [rng.randrange(cell.p) for _ in range(cell.k)]
    out = []
    for x in cell.xs:
        acc = 0
        for c in reversed(coeffs):
            acc = (acc * x + c) % cell.p
        out.append(acc)
    return out


def make_stacks(cell):
    """Deterministic adversarial + random stack battery."""
    n, p, k = cell.n, cell.p, cell.k
    rng = random.Random(f"{MASTER_SEED}-{n}-{p}-{cell.label}-stacks")
    stacks = []

    def rvec():
        return [rng.randrange(p) for _ in range(n)]

    for i in range(20):
        stacks.append((f"random-{i}", rvec(), rvec()))
    for i in range(3):
        stacks.append((f"codeword-pair-{i}",
                       random_codeword(rng, cell), random_codeword(rng, cell)))
    # near-codewords: codeword + weight-e error, e = n - t (max tolerated errors)
    e = n - cell.t
    for i in range(6):
        c = random_codeword(rng, cell)
        pos = rng.sample(range(n), max(e, 1))
        u0 = list(c)
        for j in pos:
            u0[j] = (u0[j] + 1 + rng.randrange(p - 1)) % p
        partner = rvec() if i % 2 == 0 else random_codeword(rng, cell)
        stacks.append((f"near-codeword-{i}", u0, partner))
    # split-codeword far lines: c1 on a window of size t-1, c2 elsewhere
    for i in range(6):
        c1, c2 = random_codeword(rng, cell), random_codeword(rng, cell)
        cut = cell.t - 1
        u0 = [c1[j] if j < cut else c2[j] for j in range(n)]
        c3, c4 = random_codeword(rng, cell), random_codeword(rng, cell)
        u1 = [c3[j] if j < cut else c4[j] for j in range(n)]
        stacks.append((f"split-codeword-{i}", u0, u1))
    # monomial ladder just above degree bound (x^k, x^{k+1} evaluations)
    u0 = [pow(x, k, p) for x in cell.xs]
    u1 = [pow(x, k + 1, p) for x in cell.xs]
    stacks.append(("monomial-k-k1", u0, u1))
    # subgroup-supported: mass on the index-2 subgroup coset (even/odd powers)
    for i in range(4):
        u0 = [rng.randrange(p) if j % 2 == 0 else 0 for j in range(n)]
        u1 = [rng.randrange(p) if j % 2 == 1 else 0 for j in range(n)]
        stacks.append((f"subgroup-supported-{i}", u0, u1))
    # sparse spikes (far-line pattern family from the campaign probes)
    for i in range(4):
        u0, u1 = [0] * n, [0] * n
        for j in rng.sample(range(n), n - cell.t + 1):
            u0[j] = 1 + rng.randrange(p - 1)
        for j in rng.sample(range(n), n - cell.t + 1):
            u1[j] = 1 + rng.randrange(p - 1)
        stacks.append((f"spike-{i}", u0, u1))
    return stacks


# --------------------------------------------------------------------- main

def run():
    print("G84 small-scale probe of the rate-half predecessor-count wall hypothesis")
    print("budget analogue: production 2^30 = n  ->  per-stack bad-count budget = n")
    print()
    results = []
    for n in (8, 16, 32, 64):
        k = n // 2
        # literal predecessor of 31/64 on the n-lattice
        w_lit = -(-31 * n // 64) - 1          # ceil(31n/64) - 1
        t_lit = n - w_lit
        # structural production shape t = k + m + 1, m = max(1, n/64)
        m = max(1, n // 64)
        t_str = k + m + 1
        translations = [("literal", t_lit)]
        if t_str != t_lit:
            translations.append(("structural", t_str))
        nprimes = 3 if n <= 16 else (2 if n == 32 else 1)
        for p in primes_1_mod_n(n, nprimes):
            for label, t in translations:
                cell = Cell(n, p, t, label)
                mode = "EXACT" if cell.exact else f"SAMPLED({len(cell.pool)})"
                budget = n
                worst = (-1, None, None)
                for sname, u0, u1 in make_stacks(cell):
                    bad = cell.bad_gammas(u0, u1)
                    if len(bad) > worst[0]:
                        worst = (len(bad), sname, (u0, u1, bad))
                cnt, sname, wit = worst
                verdict = "SURVIVES" if cnt <= budget else "REFUTED-AT-ANALOGUE"
                if verdict == "REFUTED-AT-ANALOGUE":
                    u0, u1, bad = wit
                    rec = cell.recount(u0, u1)
                    assert set(rec) == set(bad), "recount mismatch!"
                    print(f"!! REFUTATION n={n} p={p} t={t} ({label}) "
                          f"stack={sname} count={cnt} > budget={budget}")
                    print(f"   independent recount confirms: {len(rec)} bad gammas")
                    print(f"   repro: n={n} p={p} g={cell.g} t={t}")
                    print(f"   u0={u0}")
                    print(f"   u1={u1}")
                    print(f"   bad gammas={sorted(bad)}")
                results.append((n, p, label, t, mode, cnt, sname, budget, verdict))
                print(f"n={n:3d} p={p:4d} k={k:3d} t={t:3d} [{label:10s}] {mode:14s} "
                      f"worst={cnt:4d} ({sname}) budget={budget:3d} -> {verdict}")
    print()
    print("| n | p | translation | t | mode | worst count | worst stack | budget | verdict |")
    print("|---|---|---|---|---|---|---|---|---|")
    for n, p, label, t, mode, cnt, sname, budget, verdict in results:
        print(f"| {n} | {p} | {label} | {t} | {mode} | {cnt} | {sname} | {budget} | {verdict} |")
    print()
    print("HONEST SCOPE: sampled cells lower-bound the count (refutations valid,")
    print("survival weaker); the literal translation degenerates to the refuted")
    print("half-predecessor rung for n<64; production margin m=2^24 vs m<=2 here;")
    print("small-n survival is NOT evidence of the production hypothesis.")


if __name__ == "__main__":
    run()
