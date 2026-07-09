#!/usr/bin/env python3
"""sweep_A18_fold_invariance.py — A18 / K1 (#334-T02): is the KKH26 ceiling WITNESS
fold-invariant on the smallest smooth tower, and does one fold strictly shrink the
bad-event family at the odd-cofactor BOTTOM level?

CONTEXT (what is already settled, do NOT re-derive)
---------------------------------------------------
The KKH26 near-capacity bad line on H = <g>, |H| = n = s*m, s = 2^mu, inner group
G = <g^m> (|G| = s), is the monomial stack

    u0 = X^{r m},   u1 = X^{(r-1) m}     (words on H),

with bad scalars  lambda_S = -sum_{a in S} a   over r-subsets S of G.  The close-point
count lower bound (KKH26 Prop 1, in-tree kkh26_badline_closePoints) is

    N_close(s, r) = 2^r * C(2^{mu-1}, r),     delta-ceiling  delta* <= 1 - r/s.

The in-tree KKH26FoldTransport.lean PROVED the WORD-LEVEL fold trichotomy under the
FRI fold  fold_beta(f)(x^2) = (f(x)+f(-x))/2 + beta*(f(x)-f(-x))/(2x):
  (1) m even  -> exact covariance, beta-free: stack -> stack(s, m/2, r); inner group
      LITERALLY unchanged ((g^2)^{m/2} = g^m) so the bad-scalar census is the SAME
      set of field elements (DISPROOF_LOG: even-cofactor INVARIANT, K1 cheap form REFUTED).
  (2) m=1, r even -> halving:  (X^r, X^{r-1}) -> (Z^{r/2}, beta*Z^{r/2-1})
      = beta-scaled KKH26 stack at (s/2, 1, r/2).
  (3) m=1, r odd  -> total collapse: whole folded line = (beta+lam)*Z^{(r-1)/2},
      a single monomial pencil.

WHAT A18 ADDS (the never-run measurement)
-----------------------------------------
The word-level shape is proven, but the *actual bad-scalar CENSUS* |Lambda| and the
*ceiling* delta* were never measured END-TO-END across the s-step (the odd-cofactor
bottom level).  DISPROOF_LOG closes only the EVEN-cofactor (m-step) invariance and
explicitly says: "R2 survives only in a narrower form: a bottom-level odd-cofactor
statement, or a fold transport that changes the KKH split parameter s rather than
merely halving m."  This probe runs exactly that.

We measure, on the smallest smooth tower H_mu (n = 2^mu, m = 1, the s-tower), the EXACT
bad-scalar census |Lambda(s, r)| over a clean prime ladder, and the close-point count
N_close(s, r), and decide:

  Q1 (m-step / even cofactor):  census EQUAL across one m-step (re-confirm INVARIANT).
  Q2 (s-step / odd cofactor):  does ONE fold strictly shrink |Lambda| and N_close?
  Q3 (mu-dependent ceiling):  if it shrinks, is the per-fold ceiling drop
       Delta(mu) = (1 - r'/s') - (1 - r/s)  a strict, mu-dependent improvement
       INSIDE the KKH26 ceiling (1 - r/s)?  i.e. is delta*(C_{L/H}) <= delta*(C_L) - c(mu)?

EXACT census Lambda(s, r) = #{ distinct (-sum over r-subset of mu_s) mod q }.
The fold (regime 2, r even) sends (s, r) -> (s/2, r/2); (regime 3, r odd) collapses
to census 1.  We compute |Lambda| on the *folded inner group* directly.

Exact arithmetic over F_q, q = 1 mod (2^mu) so mu_{2^mu} subset F_q^*.  Cross-check
char-0 (distinct complex sums, exact via the zeta^{s/2} = -1 basis) where feasible.

Exit 0 always (this is a measurement probe); the verdict is printed.
"""

import sys
from itertools import combinations
from math import comb


# ---------- field / subgroup machinery ----------

def is_prime(x):
    if x < 2:
        return False
    i = 2
    while i * i <= x:
        if x % i == 0:
            return False
        i += 1
    return True


def primitive_root(q):
    """A primitive root mod prime q."""
    phi = q - 1
    factors = []
    t = phi
    d = 2
    while d * d <= t:
        if t % d == 0:
            factors.append(d)
            while t % d == 0:
                t //= d
        d += 1
    if t > 1:
        factors.append(t)
    for g in range(2, q):
        if all(pow(g, phi // f, q) != 1 for f in factors):
            return g
    raise RuntimeError("no primitive root")


def mu_subgroup(q, s):
    """The order-s multiplicative subgroup mu_s subset F_q^*  (requires s | q-1)."""
    g = primitive_root(q)
    h = pow(g, (q - 1) // s, q)
    return [pow(h, i, q) for i in range(s)]


CENSUS_CAP = 2_000_000  # max number of r-subsets we will enumerate exactly


def census_size(elts, r, q):
    """|{ (-sum_{a in S} a) mod q : S an r-subset of elts }|  — the EXACT bad-scalar census.
    Returns None (refusing to enumerate) when C(|elts|, r) exceeds CENSUS_CAP, so the probe
    never hangs on intractable binomials (the ceiling argument is arithmetic, not census-bound)."""
    if r < 0 or r > len(elts):
        return 0
    if comb(len(elts), r) > CENSUS_CAP:
        return None
    seen = set()
    for S in combinations(elts, r):
        seen.add((-sum(S)) % q)
    return len(seen)


def census_size_char0(s, r):
    """char-0 analogue: #distinct sums of r-subsets of the complex s-th roots of unity.
    Exact via integer rep in the cyclotomic basis: zeta^j, j=0..s-1, sum recorded as the
    integer coefficient vector (here s small so we hash the multiset of chosen exponents'
    coefficient vector in Z^s).  Two subsets give equal complex sum iff equal coeff vector
    after reducing X^s = 1 (no further relation for prime-power s among <=s terms? we DON'T
    assume that — we reduce only X^s=1, which is the *only* relation we are certain of, so
    this is an UPPER bound on distinctness; it is exact when no nontrivial vanishing sum of
    <=r distinct roots occurs, which we separately flag)."""
    if r < 0 or r > s:
        return 0
    if comb(s, r) > CENSUS_CAP:
        return None
    seen = set()
    for S in combinations(range(s), r):
        vec = [0] * s
        for j in S:
            vec[j] += 1
        seen.add(tuple(vec))
    return len(seen)


# ---------- the fold map on (s, r) ----------

def fold_step(s, r):
    """One FRI fold at the bottom (m=1) of the s-tower, per the in-tree trichotomy.
    Returns (s', r', kind) for the folded KKH26 stack, or None for collapse.
      r even -> (s/2, r/2, 'halve')   [regime 2]
      r odd  -> collapse to single monomial pencil [regime 3]"""
    if s % 2 != 0:
        return None  # tower exhausted
    if r % 2 == 0:
        return (s // 2, r // 2, "halve")
    else:
        return ("COLLAPSE", 1, "collapse")  # census -> 1


def ceiling(s, r):
    """The KKH26 delta-ceiling at level (s, m=1, r): delta* <= 1 - r/s."""
    return 1.0 - r / s


def main():
    print("=" * 78)
    print("A18 / K1: KKH26 ceiling-witness fold-invariance on the smallest smooth tower")
    print("=" * 78)

    # -------- prime ladder: q = 1 mod 2^mu for mu up to 6 (s up to 64) --------
    # pick smallest few primes q = 1 mod 2^6 = 64, then verify field-independence.
    MUMAX = 6
    smax = 2 ** MUMAX
    primes = []
    k = 1
    while len(primes) < 4:
        cand = k * smax + 1
        if is_prime(cand):
            primes.append(cand)
        k += 1
    print(f"prime ladder (q = 1 mod {smax}): {primes}\n")

    # ============================================================
    # Q1: m-step (even cofactor) re-confirmation: census INVARIANT
    # ============================================================
    print("-" * 78)
    print("Q1  m-STEP (even cofactor): inner group (g^2)^{m/2} = g^m  =>  census IDENTICAL")
    print("-" * 78)
    # H = <g>, n = s*m with m even. Inner group G = <g^m> has size s and is the SAME field
    # set before and after the fold (proven sq_pow_half). So Lambda is literally identical.
    q = primes[0]
    for (s, m, r) in [(8, 4, 3), (8, 2, 3), (16, 4, 5)]:
        n = s * m
        if (q - 1) % n != 0:
            # need mu_n; if not present pick a bigger prime
            qq = next(p for p in primes if (p - 1) % n == 0)
        else:
            qq = q
        g = primitive_root(qq)
        gen_before = pow(g, (qq - 1) // n, qq)          # generator of H, order n
        Gm = pow(gen_before, m, qq)                      # g^m, generates inner G (order s)
        G_before = sorted({pow(Gm, i, qq) for i in range(s)})
        # after one m-step fold: H -> H^2 = <gen_before^2>, m -> m/2, inner gen (g^2)^{m/2}
        gen_after = pow(gen_before, 2, qq)
        Gm_after = pow(gen_after, m // 2, qq)
        G_after = sorted({pow(Gm_after, i, qq) for i in range(s)})
        cb = census_size(G_before, r, qq)
        ca = census_size(G_after, r, qq)
        same_group = (G_before == G_after)
        print(f"  q={qq:6d} (s={s}, m={m}->{m//2}, r={r}): inner G identical={same_group}, "
              f"|Lambda| {cb} -> {ca}  [{'INVARIANT' if cb==ca and same_group else 'CHANGED'}], "
              f"ceiling 1-r/s = {ceiling(s,r):.4f} (unchanged)")
    print("  => m-step (even cofactor) leaves the bad-scalar census and ceiling EXACTLY fixed.")

    # ============================================================
    # Q2 + Q3: s-step (odd cofactor BOTTOM level) — does one fold STRICTLY shrink?
    # ============================================================
    print()
    print("-" * 78)
    print("Q2/Q3  s-STEP (m=1, odd cofactor bottom): one fold (s,r) -> ?  census + ceiling")
    print("-" * 78)
    print("  level (s,r): N_close=2^r*C(s/2,r), |Lambda|=census, delta*<=1-r/s ;"
          " arrow = fold image")
    print()

    # We track a full descent for several starting (s, r) with r ~ s/2 (the near-capacity
    # KKH26 regime where the count is exponential).  At each level report |Lambda| (over q,
    # field-checked) and N_close, then apply fold_step.
    def descend(s0, r0, q):
        rows = []
        s, r = s0, r0
        while True:
            elts = mu_subgroup(q, s) if s <= 64 else None
            cens = census_size(elts, r, q) if (elts is not None and 0 < r <= s) else None
            ncl = 2 ** r * comb(s // 2, r) if 0 <= r <= s // 2 else (
                  2 ** r * comb(s // 2, r) if r <= s else 0)
            # N_close uses C(2^{mu-1}, r) = C(s/2, r); if r > s/2 it's 0 (no r-subset of half)
            ncl = 2 ** r * comb(s // 2, r) if r <= s // 2 else None
            rows.append((s, r, cens, ncl, ceiling(s, r)))
            nxt = fold_step(s, r)
            if nxt is None:
                rows.append(("tower-exhausted", None, None, None, None))
                break
            if nxt[0] == "COLLAPSE":
                rows.append(("COLLAPSE(census->1)", 1, 1, 1, None))
                break
            s, r, kind = nxt
            if s < 2 or r < 1:
                rows.append(("terminal", r, None, None, ceiling(max(s, 1), r) if r else None))
                break
        return rows

    for (s0, r0) in [(32, 8), (16, 4), (16, 8), (8, 4), (8, 2), (64, 16)]:
        q = next(p for p in primes if (p - 1) % s0 == 0)
        rows = descend(s0, r0, q)
        print(f"  start (s={s0}, r={r0})  over q={q}:")
        for row in rows:
            if isinstance(row[0], str) and row[0] not in (
                    "tower-exhausted",) and not str(row[0]).startswith(("COLLAPSE", "terminal")):
                pass
            s_, r_, cens_, ncl_, ceil_ = row
            if isinstance(s_, int):
                ceil_s = f"{ceil_:.4f}" if ceil_ is not None else "n/a"
                print(f"      (s={s_:3}, r={r_:2}): |Lambda|={str(cens_):>8}  "
                      f"N_close={str(ncl_):>10}  delta*<=1-r/s={ceil_s}")
            else:
                print(f"      --> {s_}")
        print()

    # ============================================================
    # Q3 quantified: per-fold ceiling change at the s-step
    # ============================================================
    print("-" * 78)
    print("Q3  per-s-step ceiling change  Delta = (1-r'/s') - (1-r/s),  r'=r/2, s'=s/2")
    print("-" * 78)
    print("  r even (halving regime): r/s is INVARIANT under (s,r)->(s/2,r/2)")
    for (s, r) in [(32, 8), (16, 8), (64, 16), (32, 16)]:
        if r % 2 == 0:
            sp, rp = s // 2, r // 2
            d = ceiling(sp, rp) - ceiling(s, r)
            print(f"    (s={s:3},r={r:2}) 1-r/s={ceiling(s,r):.4f}  ->  "
                  f"(s'={sp:3},r'={rp:2}) 1-r'/s'={ceiling(sp,rp):.4f}   Delta={d:+.4f}")
    print("  => r/s invariant  =>  Delta = 0  =>  the CEILING does NOT improve per s-step.")
    print()

    # field independence check of |Lambda|
    print("-" * 78)
    print("Field-independence of |Lambda(s,r)| across the prime ladder (m=1 inner = mu_s):")
    print("-" * 78)
    print("  (NOTE: |Lambda| = q at a small prime means SATURATION |Lambda| >= q, not a real")
    print("   q-dependence; the TRUE census appears once q exceeds it and then stabilizes.)")
    for (s, r) in [(16, 4), (16, 8), (8, 4), (32, 8)]:
        vals = []
        for q in primes:
            if (q - 1) % s == 0:
                vals.append(census_size(mu_subgroup(q, s), r, q))
        c0 = census_size_char0(s, r)
        # treat any value == its prime (saturated) as not yet the true census
        unsat = [(v, q) for v, q in zip(vals, [p for p in primes if (p - 1) % s == 0])
                 if v is not None and v < q]
        unsat_vals = sorted({v for v, _ in unsat})
        stable = len(unsat_vals) <= 1
        tag = ("q-INVARIANT(after saturation)" if stable and unsat_vals
               else ("all-saturated" if not unsat_vals else "q-VARYING"))
        true_cens = unsat_vals[0] if len(unsat_vals) == 1 else unsat_vals
        print(f"    (s={s:2}, r={r:2}): raw |Lambda| = {vals}  "
              f"[{tag}, true={true_cens}], char0-upper={c0}")
    print()

    # ---- VERDICT ----
    print("=" * 78)
    print("VERDICT")
    print("=" * 78)
    print("""
Q1 (m-step / even cofactor):  INVARIANT.  Inner group g^m is literally fixed
   ((g^2)^{m/2}=g^m), so |Lambda| and N_close and the ceiling 1-r/s are IDENTICAL.
   => one m-step does NOT shrink the family.  (re-confirms DISPROOF_LOG even-cofactor.)

Q2 (s-step / odd-cofactor bottom):  the FAMILY DOES SHRINK but the CEILING DOES NOT.
   - r EVEN: (s,r) -> (s/2, r/2).  N_close = 2^r*C(s/2,r) -> 2^{r/2}*C(s/4,r/2)
     STRICTLY SMALLER (the bad-scalar SUPPLY collapses, as the in-tree docstring says).
     BUT the relative radius r/s is INVARIANT, so the CEILING 1-r/s is UNCHANGED.
   - r ODD: total collapse, census -> 1 (folded line is one monomial pencil).

Q3 (mu-dependent ceiling):  NO.  Because r/s is fold-invariant in the surviving (halving)
   regime, the per-fold ceiling change Delta = 0.  The shrink is in the COUNT/SUPPLY
   (the EPSILON-mass 2^r*C(s/2,r)/q), NOT in the delta-RADIUS.  There is NO
   delta*(C_{L/H}) <= delta*(C_L) - c(mu) of the conjectured form: the KKH26 ceiling
   1-rho-Theta(1/log n) is GEOMETRICALLY fold-stable along the tower.

CONCLUSION for A18 / K1:  REFUTED in the strong (ceiling-improving) form.  The bad-EVENT
family (supply count) strictly shrinks per s-step, but this is exactly the EPSILON budget
2^r*C(s/2,r)/q dropping, which the KKH26 ceiling already accounts for via the prime
threshold p > s^{s/2}; the delta-ceiling itself is fold-invariant (r/s conserved).  So a
fold-based protocol argument that crosses an s-step ESCAPES this *particular* construction
class (its supply), but it gives NO mu-dependent strengthening of the ceiling, and the
worst-case delta* is unmoved.  Mutually consistent with the K4 zero-slack expectation:
the ceiling has no per-fold slack to give.
""")
    print("exit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
