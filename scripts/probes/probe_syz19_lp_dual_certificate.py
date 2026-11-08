#!/usr/bin/env python3
"""SYZ19: LP-dual certificate hunt for the rate-1/2 decisive strip (Johnson, 1/3).

Context (issues #466/#507).  SYZ7 mapped the strip; SYZ9 landed ONE dual
certificate -- the degenerate-channel rank wall

    (t-k)*B  <  (n-k)*(n-t)          [ _SYZ9ChannelRankWall.channel_master ]

which is exactly the LP optimum of a ONE-resource relaxation (rank budget)
applied to the s=t degenerate family only, and it dips below the budget B=n
exactly for delta < (1-rho)/(2-rho) = 1/3.  SYZ9 is valid ONLY against the
degenerate channel (per-subset independent rank accounting).

This probe asks the SYZ19 question: does a RICHER witness-profile LP, built
from per-family constraints that correspond to proven in-tree theorems plus an
ADDITIVE aggregate rank constraint, still certify #bad <= budget throughout the
strip?  IMPORTANT SCOPE (audit 2026-10-28, finding L120): the per-family rows
below are proved, but the aggregate row  sum_i (s_i - k) <= n - k  is an
ASSUMED independence (additive) model, NOT a proved all-stack constraint -- see
"Aggregate constraint" below for an exact counterexample.  So every LP optimum
printed here is exact for the assumed additive model only; a value below budget
would certify #bad <= budget only for stacks whose families' constraint spaces
are independent (or after replacing the sum by the rank of the joint constraint
span), and a value above budget does not exhibit any over-budget stack.

Witness model (each row cites the in-tree theorem it encodes)
------------------------------------------------------------
A "degenerate family" is a codeword pair (v0,v1) with a shared core C (the
joint-agreement locus |C| = s).  On C both u0|C and u1|C are codeword
restrictions.  Per family:

  * RANK COST = 2*(s-k) out of the 2*(n-k) syndrome-pair budget (codimension of
      ONE family's constraint space; costs of different families add only when
      their constraint spaces are independent).
      [ _G86RankCollapseDichotomy.plantable_generic_cap ,
        _G87McaEventSyndromeBridge  -- 2(s-k) parity rows force u0|C,u1|C
        onto the code; a stack with >=64 bad scalars forces a syzygy ]
  * YIELD (bad scalars) <= floor((n-s)/(t-s)) for s<t, or (n-s) for s>=t.
      Off-core point x owns the UNIQUE scalar gamma_x = -d0(x)/d1(x)
      (d_i = u_i - v_i, zero on C); off-core points partition among the
      family's scalars, and a bad scalar's agreement set C u {owned} must
      reach size >= t, so it owns >= t-s off-core points.
      [ SYZ2 mcaEvent_pencil (per-scalar affine pencil, uniqueness of
        gamma_x) ; SYZ3 witness ; the >=t threshold is the mcaEvent radius ]
  * INDEPENDENCE / cross-family overlap: two distinct-codeword cores agree on
      <= k-1 points, else (>= k agreement) the two codewords COINCIDE and the
      families merge (one codeword pair, not two).
      [ RS distance: two RS[n,k] codewords agreeing on >= k points are equal;
        CodeGeometry / rsCode_noWeightLE ]

Aggregate constraint (ASSUMED additive model, not proved):
    sum_i (s_i - k) <= n - k.
What is proved [G86/G87 syndrome-pair dim] is that the RANK OF THE JOINT
constraint span of all families is <= 2*(n-k).  Per-core codimensions do not add
when the constraint spaces overlap, so the summed cost can exceed n-k for genuinely
contributing families.  Exact counterexample (rate 1/2, delta = 1/3 BOUNDARY, not a
strict-strip one): F_1009, n=18, k=9, t=12.  Slopes m in {1,2,4,8,16}; domain = the
ten coordinates x_ij = -m_i-m_j, the hole 0, and seven coordinates 100..106; G =
prod_{z=100..106}(X-z).  u0 = 0 except u0(0) = G(0); u1(x_ij) = -G(x_ij)*m_i*m_j and
u1 = 0 at the hole and the G-roots.  For each m the pair (0, G*(mX+m^2)) (degree
8 < k) has exact joint core = its four incident x_ij plus the seven G-roots (s=11;
two cores meet in 8 < k), and gamma = 1/m^2 adds the hole (agreement 12 = t);
nonjoint because a degree<9 u0-explainer vanishing on the 11-point core is zero
while u0(0) != 0.  So all five families contribute (gammas {1,757,946,741,942}),
yet their summed cost is 5*(11-9) = 10 > 9 = n-k.  (Five bad scalars do not exceed
the scalar budget 18; this refutes only the additive aggregate, not a correctly
guarded theorem.)  A valid all-stack certificate must use the joint constraint-span
rank, or explicitly assume/prove independence before summing costs.

Budget analogue B = n (production eps* * q ~ n).

LPs computed (all exact rational; small simplex for the knapsack), all inside the
assumed additive model:
  LPfix  : SYZ9's certificate -- rank LP with the core PINNED at s=t.
           opt = (n-k)*(n-t)/(t-k) = R*c/m.  (SYZ9's own validity is for the
           degenerate channel with per-subset independent rank accounting.)
  LPvar  : rank LP over VARIABLE core size s (knapsack, exact simplex).
           opt = R * max_s yield(s)/(s-k).
  LP3    : RESTRICTED uniform-core-size model: for each single core size s, take
           D = min(rank cap, Fisher cross-family overlap cap (<= k-1)) families all
           of size s; maximize D*yield(s) over s.  It is not a general mixed-size
           LP (an independent bounded-knapsack replay found no differing optimum on
           the currently selected rows, but that is a check, not a theorem).

Scope: diagnostic test oracle (T62); see also the rank/generation residuals.

Run:  python3 scripts/probes/probe_syz19_lp_dual_certificate.py
"""

from fractions import Fraction as F
import math

JOHNSON = 1 - math.sqrt(0.5)   # ~0.29289
THIRD = 1.0 / 3.0


def yield_bound(n, k, t, s):
    """Proven per-family yield upper bound: off-core points partition among
    scalars, each bad scalar owns >= t-s of them (SYZ2 uniqueness of gamma_x)."""
    ts = t - s
    if ts <= 0:
        return n - s
    if n - s < ts:
        return 0
    return (n - s) // ts


def rank_cost(k, s):
    """Proven per-family syndrome-pair rank cost 2(s-k) (G86/G87). We work in
    units of pairs, so cost = (s-k), budget = (n-k).  Summing these costs across
    families against the budget is the ASSUMED additive model (valid only for
    independent constraint spaces; see module docstring, L120)."""
    return s - k


def exact_simplex_knapsack(items, cap):
    """Exact-rational LP:  max sum x_i * val_i  s.t.  sum x_i * cost_i <= cap,
    x_i >= 0.  (Continuous single-resource knapsack: optimum = cap * best
    value/cost ratio.)  Implemented by exact ratio scan = the LP dual: the dual
    is  min cap*y  s.t.  cost_i*y >= val_i  ->  y* = max_i val_i/cost_i.
    Returns (opt, dual_y, argmax_item)."""
    best_ratio = F(0)
    arg = None
    for it in items:
        val, cost = it["val"], it["cost"]
        if cost <= 0:
            continue
        r = F(val, cost)
        if r > best_ratio:
            best_ratio = r
            arg = it
    opt = F(cap) * best_ratio
    return opt, best_ratio, arg


def maxD_fisher(n, s, lam):
    """Max D size-s cores with pairwise overlap <= lam, from the convexity
    (Fisher) double count:  n*a*(a-1) <= D*(D-1)*lam, a = D*s/n.
    This encodes RS cross-family agreement <= k-1 (lam = k-1)."""
    D = 1
    while D <= n:
        Dn = D + 1
        a = F(Dn * s, n)
        lhs = n * a * (a - 1)
        rhs = Dn * (Dn - 1) * lam
        if lhs > rhs:
            break
        D = Dn
    return D


def zone(delta):
    d = float(delta)
    if d < JOHNSON:
        return "below-J"
    if d < THIRD:
        return "STRIP"
    if d < THIRD + 1e-9:
        return "=1/3"
    return "above-1/3"


def run():
    print("SYZ19 LP-dual certificate hunt (rate 1/2)")
    print(f"Johnson = 1 - sqrt(1/2) = {JOHNSON:.5f} ; 1/3 = {THIRD:.5f}")
    print("budget B = n.  Per-family rows are proven; the summed rank budget")
    print("sum_i(s_i-k) <= n-k is an ASSUMED additive (independence) model, not an")
    print("all-stack theorem (see header) -- optima are exact for that model only.")
    print("LPfix = SYZ9 (core pinned s=t) ; LPvar = variable core (rank only) ;")
    print("LP3 = uniform-core-size model with Fisher cross-overlap <= k-1.\n")

    for n, k in [(32, 16), (64, 32)]:
        R = n - k
        lam = k - 1
        print(f"==== n={n} k={k} R=n-k={R} lambda=k-1={lam} budget={n} ====")
        hdr = (f"  {'t':>3} {'delta':>7} {'zone':<9} {'m':>3} {'c':>3} "
               f"{'LPfix':>7} {'LPvar':>7}(s*) {'LP3':>6}(s*,D) {'bud':>4}")
        print(hdr)
        for t in range(k + 2, n):
            delta = F(n - t, n)
            if not (0.24 <= float(delta) <= 0.40):
                continue
            m, c = t - k, n - t
            lpfix = F(R * c, m)  # SYZ9

            # variable-core knapsack (rank only)
            items = []
            for s in range(k + 1, n):
                y = yield_bound(n, k, t, s)
                if y <= 0:
                    continue
                items.append({"s": s, "val": y, "cost": rank_cost(k, s)})
            lpvar, dual_y, arg = exact_simplex_knapsack(items, R)
            svar = arg["s"] if arg else None

            # LP3: restricted uniform-core-size model -- all D families share one core
            # size s; D capped by the additive rank budget and the Fisher overlap cap
            best3, info3 = 0, None
            for it in items:
                s, y = it["s"], it["val"]
                Drank = R // (s - k)
                Dfish = maxD_fisher(n, s, lam)
                D = min(Drank, Dfish)
                bad = D * y
                if bad > best3:
                    best3, info3 = bad, (s, D)

            z = zone(delta)
            print(f"  {t:>3} {float(delta):>7.4f} {z:<9} {m:>3} {c:>3} "
                  f"{float(lpfix):>7.1f} {float(lpvar):>7.1f}({svar}) "
                  f"{best3:>6}({info3[0]},{info3[1]}) {n:>4}")
        print()

    print("READ-OFF")
    print("--------")
    print("* LPfix (SYZ9) dips below budget for every STRIP row and stays above")
    print("  for above-1/3 rows -- inside the additive model with the core pinned")
    print("  at s=t (the degenerate channel, SYZ9's independent-accounting scope).")
    print("  It is not an all-stack certificate.")
    print("* LPvar / LP3 EXCEED budget across the whole strip AND below Johnson,")
    print("  driven by minimal cores s=k+1, while empirics stay far below (see")
    print("  probe_syz7_strip_scan.py).  The per-family facts are each proven, but")
    print("  the summed rank budget is an assumption: per-family rank costs do NOT")
    print("  add when constraint spaces overlap (exact F_1009 boundary example in")
    print("  the header: five contributing families, summed cost 10 > n-k = 9).")
    print("  So neither the excess nor a sub-budget value is an all-stack verdict.")
    print("  Missing ingredient: a bound in terms of the RANK of the joint")
    print("  constraint span (or a proved independence hypothesis) feeding a")
    print("  bad-count bound.  Names the next theorem (SYZ7 item 3).")


if __name__ == "__main__":
    run()
