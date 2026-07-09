#!/usr/bin/env python3
"""sweep_A07_k2_interior.py  --  A07: discharge InteriorCeiling at k=2 (the r=3 slice).

ACTIONABLE A07 (merged 357-T02 ; 371-T01).  The FIRST decisive higher-dimensional
test of the KKH26 interior-ceiling pin.  k=1 (pair-ownership, the r=2 / dimension-one
slice) is already pinned unconditionally.  This probe attacks the r=3 / dimension-TWO
slice (code = affine words c0 + c1*x on the smooth domain x_i = g^i), which is the
rate rho = k/n = 2/8 = 1/4 member at n = 8, mu = 3 -- the in-window ceiling
  delta* = 1 - 3/2^mu = 1 - 3/8 = 5/8,  Johnson 1-sqrt(1/4)=1/2 < 5/8 < 3/4 = capacity.

THE PIN STRUCTURE (KKH26DimTwoPin.lean, axiom-clean):
  * GOOD side  (dimTwo_badScalars_card_mul_twelve_le): for EVERY stack (u0,u1) and
    threshold t >= 4 (strictly below the ceiling radius), the number of bad scalars is
       #bad  <=  n(n-1)(n-2)/12  =  28      (at n = 8).
  * BAD  side  (KKH26 witness spread): the ceiling stack (u0,u1) = (x^3, x^2) at the
    ceiling threshold t = 3 reaches
       #bad  >=  2^3 * C(4,3)  =  32   (the in-tree lower-bound term of the
       TwoPowerSubsetSumSpectrum  N(mu=3,r=3) = 2^3 C(4,3) + 2 C(4,1) = 32 + 8 = 40).
  * BAND  [28/p, 32/p) is therefore NONEMPTY (28 < 32), and that gap is what makes the
    pin fire.  KKH26 spread referenced in the actionable = 2^3*C(4,3) = 32.

WHAT THIS PROBE ADDS over probe_dim2_interior_ceiling.py (which only ran p = 257):
  1. FIELD-INDEPENDENCE at the prize-relevant primes p = 12289 (the NTT prime used by
     deltaStar_dimTwo_pin_F12289) and p = 65537 (the Fermat prime F_4).  The pin is
     claimed q-independent; this checks the count law (good <=28, ceiling >=32) is the
     SAME at all three primes 257 / 12289 / 65537.
  2. WIDE-CIRCUIT / PENCIL CENSUS stacks: exhaustive monomial pencils (x^e0, x^e1) for
     0<=e0,e1<8, plus randomized "wide circuit" stacks (low-entropy + dense + collinear-
     designed), and a hill-climb -- the census the actionable asked for.
  3. DECISIVE verdict per the actionable contract:
       count <= 32 below the ceiling  ==>  r=3 pin SURVIVES   (we further verify the
                                           sharper good bound <= 28 at threshold 4);
       count  > 32                    ==>  InteriorCeiling_k2_REFUTED (countermodel).

THREE INDEPENDENT BADNESS CHECKERS (Lean mcaEvent semantics) agree byte-exactly:
  (E) exhaustive: exists S, |S|>=t, (u0+gamma*u1)|S affine, NOT (u0|S affine AND u1|S affine);
  (D) derived:    exists S, |S|>=t, (u0+gamma*u1)|S affine, u1|S NOT affine;
  (F) fast:       exists pair-generated line w with |A_w|>=t and u1|A_w not affine.

Run:  python scripts/probes/sweep_A07_k2_interior.py
Exit 0 iff every pre-registered check passes (the r=3 pin survives at all primes).
"""

import itertools
import random
import sys
from math import comb

random.seed(40702)  # A07

N = 8
MU = 3
RHO = "1/4"                          # k=2 dimension code => rate 2/8
GOOD_BOUND = N * (N - 1) * (N - 2) // 12   # 28  (triple-ownership ceiling, threshold 4)
KKH26_SPREAD = 2 ** 3 * comb(4, 3)         # 32  (in-tree lower-bound term; "the spread")
SPECTRUM = sum(2 ** a * comb(4, a) for a in (1, 3))  # N(3,3) = 2C(4,1)+2^3 C(4,3)=8+32=40

# the prize-relevant primes (1 = p mod 8 so an order-8 element exists):
#   257    (the original probe prime),
#   12289  (the NTT prime; used by deltaStar_dimTwo_pin_F12289),
#   65537  (the Fermat prime F_4).
PRIMES = [257, 12289, 65537]

FAIL = 0


def report(name, ok, detail=""):
    global FAIL
    print(f"  [{'PASS' if ok else 'FAIL'}] {name} {detail}", flush=True)
    if not ok:
        FAIL += 1


def order8_gen(p):
    for g in range(2, p):
        if pow(g, 8, p) == 1 and pow(g, 4, p) != 1:
            return g
    return None


class Field:
    def __init__(self, p):
        self.P = p
        self.G = order8_gen(p)
        assert self.G is not None, p
        self.X = [pow(self.G, i, p) for i in range(N)]
        assert len(set(self.X)) == N and pow(self.G, N, p) == 1
        assert pow(self.G, N // 2, p) == p - 1

    def inv(self, a):
        return pow(a % self.P, self.P - 2, self.P)

    def is_affine(self, idxs, y):
        """points (X[i], y[i]), i in idxs, all on one affine line (X's distinct)."""
        if len(idxs) <= 2:
            return True
        P, X = self.P, self.X
        a, b = idxs[0], idxs[1]
        for c in idxs[2:]:
            d = ((X[b] - X[a]) * (y[c] - y[a]) - (X[c] - X[a]) * (y[b] - y[a])) % P
            if d != 0:
                return False
        return True

    # ---- three independent badness checkers (Lean mcaEvent semantics) ----
    def bad_exhaustive(self, u0, u1, gamma, t):
        P = self.P
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
        for s in range(t, N + 1):
            for S in itertools.combinations(range(N), s):
                if self.is_affine(S, ug) and not (
                        self.is_affine(S, u0) and self.is_affine(S, u1)):
                    return True
        return False

    def bad_derived(self, u0, u1, gamma, t):
        P = self.P
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
        for s in range(t, N + 1):
            for S in itertools.combinations(range(N), s):
                if self.is_affine(S, ug) and not self.is_affine(S, u1):
                    return True
        return False

    def bad_fast(self, u0, u1, gamma, t):
        P, X = self.P, self.X
        ug = [(u0[i] + gamma * u1[i]) % P for i in range(N)]
        for a, b in itertools.combinations(range(N), 2):
            inv = self.inv(X[b] - X[a])
            c1 = (ug[b] - ug[a]) * inv % P
            c0 = (ug[a] - c1 * X[a]) % P
            A = [i for i in range(N) if (c0 + c1 * X[i] - ug[i]) % P == 0]
            if len(A) >= t and not self.is_affine(A, u1):
                return True
        return False

    def colDet(self, y, i, j, k):
        """3-point collinearity determinant of (X[t], y[t]); linear in y, zero iff
        the three graph points are collinear (distinct X's)."""
        P, X = self.P, self.X
        return ((X[j] - X[i]) * (y[k] - y[i]) - (X[k] - X[i]) * (y[j] - y[i])) % P

    def bad_candidates(self, u0, u1):
        """Each bad scalar (threshold >= 4) satisfies colDet u0 + g*colDet u1 = 0 on some
        non-collinear u1-triple (colDet u1 != 0), so this candidate set is EXHAUSTIVE and
        its cost C(8,3)=56 is INDEPENDENT of p -- the key to the large-prime lanes."""
        P = self.P
        cands = set()
        for i, j, k in itertools.combinations(range(N), 3):
            d1 = self.colDet(u1, i, j, k)
            if d1 != 0:
                d0 = self.colDet(u0, i, j, k)
                cands.add((-d0) * self.inv(d1) % P)
        return cands

    def count_bad_candidates(self, u0, u1, t):
        """p-independent-cost exhaustive count via the candidate-determined scalars.

        Valid for ANY threshold t >= 3: a bad scalar makes (u0+g*u1) affine on a >=t-subset
        S while (u0,u1) is not jointly affine on S; pick any non-collinear u1-triple inside
        S (exists since u1|S is not affine), giving colDet u0 + g*colDet u1 = 0 with
        colDet u1 != 0 -> g = -colDet u0 / colDet u1.  (At t=3 the witness IS a triple; if
        u1|that triple were affine the joint pair would form, so the determining triple has
        colDet u1 != 0 -- same candidate generator.)  Cost = C(8,3) = 56, p-INDEPENDENT."""
        return sum(1 for g in self.bad_candidates(u0, u1) if self.bad_fast(u0, u1, g, t))

    def count_bad(self, u0, u1, t, check_all=False):
        """All-gammas reference count (cheap only at small p); validates the candidate
        method when check_all is set (also runs the 3-way mcaEvent agreement)."""
        cnt = 0
        cand = self.bad_candidates(u0, u1) if check_all else None
        for g in range(self.P):
            f = self.bad_fast(u0, u1, g, t)
            if check_all:
                e = self.bad_exhaustive(u0, u1, g, t)
                d = self.bad_derived(u0, u1, g, t)
                if not (e == d == f):
                    raise AssertionError(
                        f"checker mismatch p={self.P} g={g}: E={e} D={d} F={f}")
                # candidate exhaustiveness: every bad g (at t>=4) is a candidate
                if f and t >= 4 and g not in cand:
                    raise AssertionError(
                        f"candidate method MISSED a bad scalar p={self.P} g={g}")
            if f:
                cnt += 1
        return cnt

    def monomial(self, e):
        return [pow(x, e, self.P) for x in self.X]

    def rand_word(self):
        return [random.randrange(self.P) for _ in range(N)]

    def lowent_word(self):
        alpha = random.randrange(2, 5)
        vals = [random.randrange(self.P) for _ in range(alpha)]
        return [vals[random.randrange(alpha)] for _ in range(N)]


def census_stacks(F):
    """Wide-circuit / pencil census: all monomial pencils + structured + random + lowent."""
    stacks = []
    # 1. ALL monomial pencils (x^e0, x^e1), 0 <= e0, e1 < 8  -- the "pencil" census.
    for e0 in range(8):
        for e1 in range(8):
            stacks.append((F.monomial(e0), F.monomial(e1), f"pencil(x^{e0},x^{e1})"))
    # 2. The KKH26 ceiling stack and its transpose (carry their own marker).
    # (already included as pencil(x^3,x^2) / pencil(x^2,x^3))
    # 3. Wide-circuit: dense random + low-entropy (forces heavy level sets).
    for k in range(150):
        stacks.append((F.rand_word(), F.rand_word(), "rand"))
    for k in range(150):
        u0 = F.lowent_word()
        u1 = F.lowent_word() if random.random() < 0.7 else F.rand_word()
        stacks.append((u0, u1, "lowent"))
    return stacks


def hill_climb(F, t, seed_stacks, iters=1200):
    """Maximize #bad at threshold t from the best census seed (candidate-based count)."""
    P = F.P
    cb = lambda u0, u1: F.count_bad_candidates(u0, u1, t)
    cur = max(seed_stacks, key=lambda s: cb(s[0], s[1]))
    cur_c = cb(cur[0], cur[1])
    best, best_c = (list(cur[0]), list(cur[1])), cur_c
    u0, u1 = list(cur[0]), list(cur[1])
    for _ in range(iters):
        nu0, nu1 = list(u0), list(u1)
        for _ in range(random.randrange(1, 3)):
            (nu0 if random.randrange(2) == 0 else nu1)[random.randrange(N)] = \
                random.randrange(P)
        c = cb(nu0, nu1)
        if c >= cur_c:
            u0, u1, cur_c = nu0, nu1, c
            if c > best_c:
                best, best_c = (list(nu0), list(nu1)), c
    return best_c


def main():
    print("=" * 78)
    print("sweep_A07_k2_interior.py  --  InteriorCeiling at k=2 (r=3 slice), n=8, rho=1/4")
    print(f"  GOOD bound (#bad <= n(n-1)(n-2)/12) = {GOOD_BOUND}   "
          f"KKH26 spread 2^3*C(4,3) = {KKH26_SPREAD}   "
          f"full spectrum N(3,3) = {SPECTRUM}")
    print(f"  in-window: Johnson 1/2 < ceiling delta*=1-3/8=5/8 < capacity 3/4")
    print("=" * 78)

    summary = {}
    for p in PRIMES:
        print(f"\n--- prime p = {p}  (order-8 generator g = {order8_gen(p)}) ---")
        F = Field(p)

        # small_prime: at p=257 we can afford the FULL all-gammas reference count and the
        # 3-way mcaEvent agreement + candidate-exhaustiveness check.  At the large prize
        # primes we use the p-independent-cost candidate count (validated exhaustive at 257).
        small = (p == 257)

        # (A) The BAD side: the KKH26 ceiling stack at the ceiling threshold t=3 reaches >=32.
        kk_u0, kk_u1 = F.monomial(3), F.monomial(2)
        if small:
            # validate the candidate count equals the all-gammas count + 3-way agreement.
            ceil_all = F.count_bad(kk_u0, kk_u1, 3, check_all=True)
            ceil_cnt = F.count_bad_candidates(kk_u0, kk_u1, 3)
            report("ceiling: candidate count == all-gammas count @ p=257",
                   ceil_cnt == ceil_all, f"cand={ceil_cnt} all={ceil_all}")
        else:
            ceil_cnt = F.count_bad_candidates(kk_u0, kk_u1, 3)
        report(f"BAD side: (x^3,x^2) @ t=3 reaches the spread {KKH26_SPREAD}",
               ceil_cnt >= KKH26_SPREAD, f"#bad = {ceil_cnt} (full spectrum {SPECTRUM})")

        # (B) The GOOD side: census of stacks at threshold t=4 (below the ceiling).
        stacks = census_stacks(F)
        worst, worst_lbl = 0, None
        for i, (u0, u1, lbl) in enumerate(stacks):
            if small and ((i < 48) or lbl.startswith("pencil")):
                # validate the candidate method IS exhaustive against the all-gammas count
                c_all = F.count_bad(u0, u1, 4, check_all=True)
                c_cand = F.count_bad_candidates(u0, u1, 4)
                if c_all != c_cand:
                    raise AssertionError(
                        f"candidate vs all-gammas mismatch p={p} {lbl}: {c_cand}!={c_all}")
                c = c_all
            else:
                c = F.count_bad_candidates(u0, u1, 4)
            if c > worst:
                worst, worst_lbl = c, lbl
        if small:
            report("3-checker byte-exact + candidate-exhaustiveness validated @ p=257", True,
                   "(no mismatch raised)")
        report(f"GOOD side census max #bad <= {GOOD_BOUND}",
               worst <= GOOD_BOUND, f"max = {worst} via {worst_lbl}")

        # (C) hill-climb to stress the good bound.
        hc = hill_climb(F, 4, stacks)
        worst = max(worst, hc)
        report(f"GOOD side after hill-climb #bad <= {GOOD_BOUND}",
               worst <= GOOD_BOUND, f"max = {worst}")

        # (D) THE DECISIVE k=2 VERDICT for this prime.
        #   below-ceiling count must stay <= 32 (the spread) -- and we get the sharper 28.
        survives = worst <= KKH26_SPREAD
        report(f"DECISIVE: below-ceiling #bad <= spread {KKH26_SPREAD} -> r=3 pin survives",
               survives, f"(max {worst}; sharper good bound {GOOD_BOUND})")
        summary[p] = (ceil_cnt, worst, survives)

    # (E) FIELD-INDEPENDENCE: the count law is identical across all three primes.
    print("\n--- field-independence verdict ---")
    ceils = {p: s[0] for p, s in summary.items()}
    goods = {p: s[1] for p, s in summary.items()}
    report("ceiling-stack #bad identical at all primes (q-independent count law)",
           len(set(ceils.values())) == 1, f"{ceils}")
    report("good-side max <= 28 at all primes (q-independent good count law)",
           all(v <= GOOD_BOUND for v in goods.values()), f"{goods}")

    print("\n" + "=" * 78)
    print("SUMMARY  (prime | ceiling #bad @t=3 | below-ceiling max @t=4 | survives)")
    for p in PRIMES:
        c, w, s = summary[p]
        print(f"  p={p:6d} | ceiling {c:4d} | below-ceiling max {w:3d} | "
              f"{'SURVIVES' if s else 'REFUTED'}")
    all_survive = all(s[2] for s in summary.values())
    print(f"\nVERDICT: r=3 (k=2) interior-ceiling pin "
          f"{'SURVIVES at all primes' if all_survive else 'REFUTED'}.")
    print(f"  band [{GOOD_BOUND}/p, {KKH26_SPREAD}/p) nonempty: {GOOD_BOUND < KKH26_SPREAD}")
    print(f"Total failures: {FAIL}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
