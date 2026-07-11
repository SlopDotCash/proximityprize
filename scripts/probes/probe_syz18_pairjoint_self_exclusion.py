#!/usr/bin/env python3
"""probe_syz18_pairjoint_self_exclusion.py -- #466 SYZ18 truth test.

CONJECTURE (SYZ18, "pairJoint self-exclusion"): at rate 1/2, for a radius delta in the
strip (Johnson ~ 0.293, 1/3), any stack (u0,u1) with MORE than budget-many bad scalars
must be a *syzygy* config (rank-deficient witness family, per G86/G87), and such a config
is *self-excluding*: at least one of its putatively-bad scalars actually satisfies the
pairJoint clause, so it was never mcaEvent-bad.  If true throughout the strip, the strip
is good and delta*(rate 1/2) = 1/3 exactly.

We test this DIRECTLY.

--------------------------------------------------------------------------------
EXACT mcaEvent BADNESS CRITERION (list-decoding regime; generalizes the unique-regime
criterion of probe_strip_sup_exactness.py to 2e >= d, which is where the strip lives).

Code C = RS[F_p, mu_n, k] = {eval of deg<k poly on mu_n}.  Parity rows H (r = n-k rows):
H[rr,j] = x_j^(rr+1), rr = 0..r-1.  Syndrome of word w: s(w) = H @ w in F^r.
For support E subset [n], S(E) := column span of H[:,E] = { syndromes of words supported
on E }.  Membership t in S(E)  <=>  rank(H_E) == rank([H_E | t])  (exact GF(p) rank).

mcaEvent(gamma) for stack with syndromes (s0,s1), line syndrome t_g = s0 + gamma*s1:
    gamma is BAD  <=>  EXISTS support E, |E| <= e, with
        t_g in S(E)   AND   NOT ( s0 in S(E)  AND  s1 in S(E) ).
Derivation: a codeword explains the line on witness set S = complement(E) iff line-word
has error supported on E iff t_g in S(E).  Adversary maximizes S (minimizes E).
pairJointAgreesOn(S) <=> s0 in S(E) and s1 in S(E) (the two codewords are independent).
mcaEvent requires an explaining codeword AND ¬pairJoint on the SAME S, existential over E.

A gamma with t_g in S(E) for some E but where EVERY explaining E also has s0,s1 in S(E)
is RESCUED by pairJoint (a joint codeword pair agrees on the witness set): not bad.

Budget (G86/G87 dichotomy): r_max = floor((2(n-k) - 1)/((n-k) - e)).  More than r_max
truly-bad scalars forces a syzygy among the witness functionals.
--------------------------------------------------------------------------------
"""
from __future__ import annotations
import itertools, sys, json, time
from typing import List, Tuple

# ---------------------------------------------------------------- GF(p) linear algebra
def find_gen(p, n):
    # multiplicative generator of an order-n subgroup: need n | p-1
    assert (p - 1) % n == 0, f"need n|p-1: n={n} p={p}"
    cof = (p - 1) // n
    # primitive root
    def is_prim(g):
        m = p - 1
        f = set()
        d = 2
        mm = m
        while d * d <= mm:
            while mm % d == 0:
                f.add(d); mm //= d
            d += 1
        if mm > 1: f.add(mm)
        return all(pow(g, m // q, p) != 1 for q in f)
    g = 2
    while not is_prim(g): g += 1
    return pow(g, cof, p)  # order exactly n

def mat_rank_mod(rows: List[List[int]], p: int) -> int:
    M = [r[:] for r in rows]
    R = len(M);
    if R == 0: return 0
    Cn = len(M[0])
    rank = 0
    col = 0
    for col in range(Cn):
        piv = None
        for i in range(rank, R):
            if M[i][col] % p != 0:
                piv = i; break
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col], p - 2, p)
        M[rank] = [(x * inv) % p for x in M[rank]]
        for i in range(R):
            if i != rank and M[i][col] % p != 0:
                f = M[i][col]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[rank])]
        rank += 1
        if rank == R: break
    return rank

class Cell:
    def __init__(self, n, k, p, e):
        self.n, self.k, self.p, self.e = n, k, p, e
        self.r = n - k
        self.d = n - k + 1
        g = find_gen(p, n)
        self.dom = [pow(g, j, p) for j in range(n)]
        # H columns: col j = [x_j^1, ..., x_j^r]
        self.Hcol = [[pow(self.dom[j], rr + 1, p) for rr in range(self.r)] for j in range(n)]
        self.budget = (2 * self.r - 1) // (self.r - e)
        # cache of left-null / rank for supports
        self._Erank = {}

    def col(self, j): return self.Hcol[j]

    def in_SE(self, t: List[int], E: Tuple[int, ...]) -> bool:
        # t in column span of H[:,E]  <=> rank(H_E)==rank([H_E|t]) ; rows = r
        base = [self.col(j) for j in E]  # list of columns (each length r)
        # build row-form: transpose -> r rows each len |E|
        r = self.r
        HE_rows = [[base[c][rr] for c in range(len(E))] for rr in range(r)]
        rk = self._Erank.get(E)
        if rk is None:
            rk = mat_rank_mod(HE_rows, self.p); self._Erank[E] = rk
        aug = [row + [t[rr]] for rr, row in enumerate(HE_rows)]
        return mat_rank_mod(aug, self.p) == rk

    def line_synd(self, s0, s1, g):
        return [(a + g * b) % self.p for a, b in zip(s0, s1)]

    def classify_gamma(self, s0, s1, g, supports):
        """Return (explainable, bad). explainable: some E explains line.
        bad: some explaining E has NOT both s0,s1 in S(E). If explainable but every
        explaining E has both s0,s1 in S(E) -> RESCUED (explainable, not bad)."""
        t = self.line_synd(s0, s1, g)
        expl = False
        bad = False
        for E in supports:
            if self.in_SE(t, E):
                expl = True
                if not (self.in_SE(s0, E) and self.in_SE(s1, E)):
                    bad = True
                    return True, True
        return expl, bad

    def supports_upto(self, e=None):
        e = self.e if e is None else e
        out = []
        for size in range(0, e + 1):
            out += list(itertools.combinations(range(self.n), size))
        return out

# ------------------------------------------------------------ word-level cross-check
def word_level_bad(cell: Cell, u0, u1, g):
    n, k, p, e = cell.n, cell.k, cell.p, cell.e
    dom = cell.dom
    line = [(u0[j] + g * u1[j]) % p for j in range(n)]
    cws = []
    for coeffs in itertools.product(range(p), repeat=k):
        cws.append([sum(c * pow(x, i, p) for i, c in enumerate(coeffs)) % p for x in dom])
    def expl(vec, S):
        return any(all(w[j] == vec[j] for j in S) for w in cws)
    for size in range(n - e, n + 1):
        for S in itertools.combinations(range(n), size):
            if expl(line, S) and not (expl(u0, S) and expl(u1, S)):
                return True
    return False

def synd(cell, w):
    return [sum(cell.Hcol[j][rr] * w[j] for j in range(cell.n)) % cell.p for rr in range(cell.r)]

def cross_validate(cell: Cell, samples, seed=1):
    import random
    rng = random.Random(seed)
    sups = cell.supports_upto()
    p, n = cell.p, cell.n
    for _ in range(samples):
        u0 = [rng.randrange(p) for _ in range(n)]
        u1 = [rng.randrange(p) for _ in range(n)]
        s0, s1 = synd(cell, u0), synd(cell, u1)
        for g in range(p):
            _, syn_bad = cell.classify_gamma(s0, s1, g, sups)
            w_bad = word_level_bad(cell, u0, u1, g)
            if syn_bad != w_bad:
                return False, (u0, u1, g, syn_bad, w_bad)
    return True, None

# ------------------------------------------------------------ GF(p) nullspace
def left_null(cols, r, p):
    """cols: list of column-vectors (len r). Return basis of left-null space:
    vectors L in F^r with L . col = 0 for every col. Rows = r-dim vectors."""
    # We want L (1 x r) with L @ H_E = 0. i.e. H_E^T @ L^T = 0. Solve for L^T (r-vector).
    # Build matrix A = H_E^T (rows = |E|, cols = r); nullspace of A.
    A = [[cols[c][rr] for rr in range(r)] for c in range(len(cols))]  # |E| x r
    return nullspace(A, r, p)

def nullspace(A, ncols, p):
    """Return basis (list of vectors len ncols) of {x : A x = 0}."""
    M = [row[:] for row in A]
    nrows = len(M)
    pivots = {}
    rank = 0
    for col in range(ncols):
        piv = None
        for i in range(rank, nrows):
            if M[i][col] % p != 0:
                piv = i; break
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col], p - 2, p)
        M[rank] = [(x * inv) % p for x in M[rank]]
        for i in range(nrows):
            if i != rank and M[i][col] % p != 0:
                f = M[i][col]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[rank])]
        pivots[col] = rank
        rank += 1
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for col, rw in pivots.items():
            v[col] = (-M[rw][fc]) % p
        basis.append(v)
    return basis

def construct_syzygy(cell: Cell, gammas, supports_for_gamma, p):
    """Solve for (s0,s1) in F^{2r} with s0+gamma_i s1 in S(E_i) for all i.
    Constraint per i: for each L in left_null(H_{E_i}):  L.s0 + gamma_i (L.s1)=0.
    Return list of nontrivial solutions (s0,s1) (basis of the joint nullspace)."""
    r = cell.r
    rows = []
    for g, E in zip(gammas, supports_for_gamma):
        cols = [cell.col(j) for j in E]
        Ls = left_null(cols, r, p)
        for L in Ls:
            row = [x % p for x in L] + [(g * x) % p for x in L]  # [L | gamma L]
            rows.append(row)
    ns = nullspace(rows, 2 * r, p) if rows else []
    return [(v[:r], v[r:]) for v in ns], len(rows)

# ------------------------------------------------------------ driver / experiments
def full_bad_scan(cell: Cell, s0, s1):
    """Over all gamma in F_p: return (bad_list, rescued_list) where rescued = explainable
    but pairJoint-saved (not bad). Uses full support set (all E, |E|<=e)."""
    sups = cell.supports_upto()
    bad, rescued = [], []
    for g in range(cell.p):
        expl, isbad = cell.classify_gamma(s0, s1, g, sups)
        if isbad: bad.append(g)
        elif expl: rescued.append(g)
    return bad, rescued

def phase1_direct_construction(cell: Cell, seed=0, max_N=None, trials=400):
    """Directly build syzygy stacks: pick N gammas + supports, solve for (s0,s1),
    then measure TRUE bad count and rescue count. Push N above budget and see whether
    the pairJoint clause always rescues at least one (self-exclusion)."""
    import random
    rng = random.Random(seed)
    p, n, e, r = cell.p, cell.n, cell.e, cell.r
    budget = cell.budget
    Nmax = max_N or (budget + 6)
    all_sup_e = list(itertools.combinations(range(n), e))
    gammas_all = list(range(1, p))  # nonzero labels; 0 handled by reparam symmetry
    best = {"true_bad": 0, "example": None}
    overbudget_configs = 0
    overbudget_selfexcluding = 0
    overbudget_violations = []  # configs with true_bad > budget AND no rescue among them
    for _ in range(trials):
        N = rng.randint(budget + 1, Nmax)  # aim OVER budget
        gammas = rng.sample(gammas_all, min(N, len(gammas_all)))
        sups = [random.Random(rng.random()).choice(all_sup_e) for _ in gammas]
        sols, ncon = construct_syzygy(cell, gammas, sups, p)
        for (s0, s1) in sols[:3]:
            if all(x == 0 for x in s0) and all(x == 0 for x in s1):
                continue
            bad, rescued = full_bad_scan(cell, s0, s1)
            tb = len(bad)
            if tb > best["true_bad"]:
                best = {"true_bad": tb, "example": (list(s0), list(s1), bad, rescued),
                        "budget": budget}
            if tb > budget:
                overbudget_configs += 1
                # self-exclusion asks: among the *targeted* gammas that we forced
                # explainable, is at least one rescued (pairJoint fires)?
                forced_rescued = [g for g in gammas if g in rescued]
                if forced_rescued:
                    overbudget_selfexcluding += 1
                else:
                    # even stronger check: is ANY gamma in F rescued while >budget bad?
                    if not rescued:
                        overbudget_violations.append((list(s0), list(s1), bad))
    return best, overbudget_configs, overbudget_selfexcluding, overbudget_violations

def run(cell: Cell, name, validate=0):
    print(f"\n=== cell {name}: RS[F_{cell.p}, mu_{cell.n}, k={cell.k}] "
          f"d={cell.d} e={cell.e} (delta={cell.e/cell.n:.4f}) r={cell.r} "
          f"budget r_max={cell.budget}")
    if validate:
        ok, w = cross_validate(cell, validate)
        print(f"  cross-validation vs word-level mcaEvent ({validate} stacks): "
              f"{'PASS' if ok else 'FAIL '+repr(w)}")
        if not ok: sys.exit(1)
    best, ob, se, viol = phase1_direct_construction(cell)
    print(f"  MAX true-bad over constructed syzygy stacks: {best['true_bad']} "
          f"(budget {cell.budget})")
    print(f"  over-budget configs found: {ob};  of those self-excluding "
          f"(a targeted gamma rescued): {se}")
    print(f"  over-budget configs with ZERO rescue anywhere (CONJECTURE VIOLATIONS): "
          f"{len(viol)}")
    if best["example"]:
        s0, s1, bad, resc = best["example"]
        print(f"    example max stack: #bad={len(bad)} #rescued(pairJoint)={len(resc)} "
              f"bad={bad[:20]} rescued={resc[:20]}")
    if viol:
        print(f"    !!! VIOLATION example: {viol[0]}")
    return {"cell": name, "n": cell.n, "k": cell.k, "p": cell.p, "e": cell.e,
            "delta": cell.e/cell.n, "budget": cell.budget,
            "max_true_bad": best["true_bad"], "overbudget": ob,
            "overbudget_selfexcluding": se, "violations": len(viol)}

def main():
    results = []
    # validation cells (small, word-level enumerable)
    # unique regime tiny (sanity)
    results.append(run(Cell(6, 1, 7, 2), "V0-unique n6k1p7e2", validate=30))
    # list regime small validation: n=8,k=2,e=4 -> 2e=8 > d=7 (list); p=? need 8|p-1: p=17
    results.append(run(Cell(8, 2, 17, 4), "V1-list n8k2p17e4", validate=15))
    # STRIP cells, rate 1/2, delta in (0.293,1/3):
    # n=10,k=5,e=3: delta=0.30 (>Johnson .293). p: 10|p-1 -> p=11 (small) or 31,41,61,71,101
    results.append(run(Cell(10, 5, 11, 3), "S1-strip n10k5p11e3", validate=8))
    results.append(run(Cell(10, 5, 101, 3), "S2-strip n10k5p101e3"))
    # n=12,k=6,e=4: delta=1/3 boundary. p: 12|p-1 -> p=13,37,61,73
    results.append(run(Cell(12, 6, 13, 4), "S3-strip n12k6p13e4"))
    results.append(run(Cell(12, 6, 61, 4), "S4-strip n12k6p61e4"))
    # n=16,k=8,e=5: delta=0.3125. p:16|p-1 -> p=17,97,113
    results.append(run(Cell(16, 8, 17, 5), "S5-strip n16k8p17e5"))
    with open("scripts/probes/syz18_results.json", "w") as f:
        json.dump(results, f, indent=1)
    print("\nDONE. Summary:")
    for r in results:
        v = "VIOLATIONS!" if r["violations"] else "clean"
        print(f"  {r['cell']}: max_bad={r['max_true_bad']} budget={r['budget']} "
              f"overbudget={r['overbudget']} selfexcl={r['overbudget_selfexcluding']} -> {v}")

if __name__ == "__main__":
    main()
