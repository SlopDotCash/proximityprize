#!/usr/bin/env python3
"""
probe_466b_cmk_countermeasure.py  (#466 round 2, lane CMK)

REFUTATION PROBE for the abstract form of "CMK moment-problem rigidity"
(round-1 outcomes note deltastar-466-round1-outcomes-2026-07-01.md, section E):

    ABSTRACT CMK CLAIM (to refute):
      mu = (1/m) * sum_i delta_{x_i}, m equal real atoms;
      second moment pinned EXACTLY at the Parseval value  m_2 = P2;
      Wick envelope  |m_{2r}| <= K^r * (2r-1)!! * n^r  for all 1 <= r <= R
      ==>  max_i |x_i| <= C(K) * sqrt(n * log m)      for some R << log m.

COUNTERMEASURE (symmetric 4-value, m equal atoms, repetitions allowed):
      2 atoms at +/-T  (one each), (m-2)/2 atoms at each of +/-s,
      s^2 := (m*P2 - 2*T^2)/(m-2)   so that  m_2 = P2  EXACTLY.
  All odd moments vanish identically (better than the true eta-field, whose
  first moment is -n/(q-1) per atom), realness and equal mass hold, and it is
  an actual positive measure, so EVERY implicit moment-matrix constraint
  (Hankel PSD, Krein conditions, Christoffel bounds) holds automatically.
  The ONLY active constraints on T are the even Wick envelopes r = 1..R.

HONEST P2 (read off the in-tree substrate, not approximated):
  GaussPeriodParsevalFloor.sum_sq_erase_zero:
      sum_{b != 0} ||eta_b||^2 = q*n - n^2,   q = |F|, n = |mu_n|.
  eta is constant on the m = (q-1)/n multiplicative cosets of mu_n
  (eta_{bu} = eta_b for u in mu_n), so the empirical measure of the m distinct
  coset values has second moment
      P2 = (q*n - n^2) / (n*m) = n*(q-n)/(q-1) = n - (n-1)/m   at q = n*m + 1.
  (The orchestrator's "n*(1-n/q)" is the same thing up to O(n/q^2); we use the
  exact rational  P2 = (m*n - (n-1))/m .)

Wick-envelope bookkeeping vs the in-tree DC-subtracted form: with
  DCSubtractedMoment.sum_nonzero_moment: sum_{b!=0}||eta_b||^{2r} = q*E_r - n^{2r}
and the DC-subtracted bound A_r = E_r - n^{2r}/q <= K^r (2r-1)!! n^r, the
per-atom moment satisfies m_{2r} = q*A_r/(q-1) <= (q/(q-1)) * K^r (2r-1)!! n^r,
i.e. the abstract envelope with a multiplicative slack (q/(q-1)) = 1 + 2^{-158}.
We use the clean envelope  m_{2r} <= K^r (2r-1)!! n^r  as stated by round 1;
the 2^{-158} slack changes nothing below (checked: verdicts identical).

ALL VERDICTS USE EXACT INTEGER/RATIONAL ARITHMETIC (fractions.Fraction).
Floats appear ONLY in display columns (marked ~).

Feasibility structure (why binary search is a proof, not a heuristic):
each constraint function
    f_r(T^2) = 2*T^{2r}*(m-2)^r + (m-2)*(m*n-(n-1)-2*T^2)^r
is CONVEX in T^2 (sum of a convex power and a convex power of an affine map),
and f_r(0) <= RHS_r (verified below for every row), so the feasible set in T^2
is an interval [0, Tmax^2]; we certify ok(Tmax) and not ok(Tmax+1).

ln(m) bounds are certified exactly in-probe:
  ln 2 = sum_{k>=1} 1/(k 2^k);  partial sum S_K is a strict lower bound and
  S_K + 1/((K+1) 2^K) a strict upper bound (geometric tail).  This gives
  rational LN2_LO < ln 2 < LN2_HI, hence exact integer brackets for ln m.

The #400 trap does not apply: this probe touches no character sums at all --
it is a pure moment-problem countermeasure (no primes, no subgroups sampled).

Output: scripts/probes/_out_466b_cmk_countermeasure.txt
"""

from fractions import Fraction
import math
import sys

# ----------------------------------------------------------------------------
# exact ln 2 bracket:  ln 2 = sum_{k>=1} 1/(k 2^k)
# ----------------------------------------------------------------------------
def ln2_bracket(K=40):
    S = Fraction(0)
    for k in range(1, K + 1):
        S += Fraction(1, k * 2**k)
    lo = S                                   # strict lower bound (all terms > 0)
    hi = S + Fraction(1, (K + 1) * 2**K)     # tail < sum of geometric / (K+1)
    return lo, hi

LN2_LO, LN2_HI = ln2_bracket()
assert LN2_LO < LN2_HI
# sanity vs float
assert abs(float(LN2_LO) - math.log(2)) < 1e-12

def ln_pow2_bracket(e):
    """exact rational bracket for ln(2^e)"""
    return e * LN2_LO, e * LN2_HI

# ----------------------------------------------------------------------------
# double factorial (2r-1)!!
# ----------------------------------------------------------------------------
def dfact(r):
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v

# ----------------------------------------------------------------------------
# the countermeasure feasibility check (exact, cleared denominators)
# ----------------------------------------------------------------------------
def make_checker(n, m, Knum, Kden, R):
    """Returns ok(T) checking, for the symmetric 4-value measure with edge T:
         s2num = m*n - (n-1) - 2*T^2  >= 0                      (s^2 >= 0)
         for all r in 1..R:
           Kden^r * (2*T^(2r)*(m-2)^r + (m-2)*s2num^r)
             <= Knum^r * (2r-1)!! * n^r * m * (m-2)^r
       which is  m_{2r} <= K^r (2r-1)!! n^r  with everything cleared.
       Parseval m_2 = P2 holds by CONSTRUCTION of s2num (identity, no check
       needed: 2T^2 + (m-2)*s2num/(m-2) = m*n-(n-1) = m*P2)."""
    A0 = m * n - (n - 1)
    m2 = m - 2
    # precompute per-r constants
    rhs_const = [None] * (R + 1)
    for r in range(1, R + 1):
        rhs_const[r] = (Knum**r) * dfact(r) * (n**r) * m * (m2**r)

    def check(T, return_binding=False):
        s2num = A0 - 2 * T * T
        if s2num < 0:
            return (False, None) if return_binding else False
        binding = None
        best_slack = None
        for r in range(1, R + 1):
            lhs = (Kden**r) * (2 * T**(2 * r) * m2**r + m2 * s2num**r)
            rhs = rhs_const[r]
            if lhs > rhs:
                return (False, r) if return_binding else False
            # track tightest constraint (largest lhs/rhs)
            sl = Fraction(lhs, rhs)
            if best_slack is None or sl > best_slack:
                best_slack, binding = sl, r
        return (True, (binding, best_slack)) if return_binding else True

    def slack(T, r):
        """exact lhs/rhs of constraint r at edge T"""
        s2num = A0 - 2 * T * T
        lhs = (Kden**r) * (2 * T**(2 * r) * m2**r + m2 * s2num**r)
        return Fraction(lhs, rhs_const[r])

    return check, A0, slack

def max_T(n, m, Knum, Kden, R):
    check, A0, slack = make_checker(n, m, Knum, Kden, R)
    assert check(0), "f_r(0) <= RHS must hold (interval-from-zero premise)"
    lo, hi = 0, 1
    while check(hi):
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if check(mid):
            lo = mid
        else:
            hi = mid
    # certificates.  NOTE: the r=1 constraint is T-INDEPENDENT (it is the
    # Parseval identity, slack exactly 1-(n-1)/(n*m)), so "tightest slack at
    # Tmax" would always report r=1 at K=1.  The true T-binding constraint is
    # the first one VIOLATED at Tmax+1.
    okT, _info = check(lo, return_binding=True)
    assert okT
    viol, binding_r = check(lo + 1, return_binding=True)
    assert viol is False
    return lo, binding_r, slack(lo, binding_r)

# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------
def run():
    out = []
    def p(s=""):
        out.append(s)
        print(s)

    p("=" * 100)
    p("PROBE 466b -- CMK abstract moment-problem rigidity: explicit refuting measure")
    p("=" * 100)

    # ------------------------------------------------------------------
    # prize scale
    # ------------------------------------------------------------------
    MU = 30
    n = 2**MU                 # 2^30
    m = 2**128                # number of atoms (cosets), q = n*m + 1
    lnm_lo, lnm_hi = ln_pow2_bracket(128)
    # integer brackets for ln m used in EXACT verdicts:
    L_LO, L_HI = 88, 89
    assert lnm_lo > L_LO and lnm_hi < L_HI, "ln(2^128) in (88,89) must certify"
    p(f"\nprize scale: n = 2^{MU}, m = 2^128 atoms (q = n*m+1), "
      f"P2 = n - (n-1)/m exact")
    p(f"ln m = 128*ln2 in ({float(lnm_lo):.6f}, {float(lnm_hi):.6f}); "
      f"certified integer bracket {L_LO} < ln m < {L_HI} (exact rational series bound)")
    p(f"sqrt(2 n ln m) ~ {math.sqrt(2*n*float(lnm_lo)):.1f} ~ 2^{math.log2(math.sqrt(2*n*float(lnm_lo))):.2f}")

    sqrt2nlnm = math.sqrt(2 * n * 128 * math.log(2))   # display only
    sqrtnlnm = math.sqrt(n * 128 * math.log(2))        # display only

    Rlist = [4, 8, 11, 22, 44, 89, 128, 178]
    p(f"\nR rows: {Rlist}   (178 = first integer >= 2*ln m: 2*ln m < 178 since ln m < 89)")
    p("countermeasure: atoms {+T, -T} x1 each, {+s, -s} x (m-2)/2 each "
      "(m-2 = 2^128-2, (m-2)/2 integer)")
    p("verdicts (EXACT): 'T > a*sqrt(n ln m)' certified via T^2 > a^2*n*89 "
      "(89 > ln m); complement via T^2 < 16*n*88 (88 < ln m)")

    for (Knum, Kden, Kname) in [(1, 1, "K = 1"), (21, 20, "K = 1.05 (=21/20)")]:
        p("\n" + "-" * 100)
        p(f"{Kname}: envelope m_2r <= K^r (2r-1)!! n^r for r = 1..R; "
          f"Parseval m_2 = P2 exact by construction")
        p("-" * 100)
        p(f"{'R':>4} | {'Tmax (exact int)':>42} | {'~T/sqrt(2n ln m)':>16} | "
          f"{'bind r':>6} | {'>2':>3} {'>4':>3} {'>8':>3}  (a*sqrt(n ln m), exact)")
        rows = {}
        for R in Rlist:
            T, br, tight = max_T(n, m, Knum, Kden, R)
            rows[R] = T
            ratio = T / sqrt2nlnm
            v = []
            for a in (2, 4, 8):
                v.append("YES" if T * T > a * a * n * L_HI else "no ")
            p(f"{R:>4} | {T:>42} | {ratio:>16.3f} | {br:>6} | "
              f"{v[0]} {v[1]} {v[2]}   (tightness lhs/rhs at bind: {float(tight):.4f})")
        # positive complement row
        Tc = rows[178]
        drop = Tc * Tc < 16 * n * L_LO
        p(f"\n  complement (R = 178 >= 2 ln m): Tmax = {Tc}  "
          f"~{Tc/sqrtnlnm:.2f}*sqrt(n ln m); EXACT check Tmax^2 < 16*n*88: "
          f"{'YES -- admissible edge is back at the prize scale' if drop else 'NO (!!)'}")
        p("   (recovers the KNOWN conditional moment bound at log depth -- cite "
          "GaussPeriodMomentBound / prize_scale_bound_at_saddle; NOT re-landed here)")

    # ------------------------------------------------------------------
    # small-r caution check (orchestrator: 'check r=1..3 carefully')
    # ------------------------------------------------------------------
    p("\n" + "-" * 100)
    p("small-r caution: per-single-constraint caps (K=1) -- does ANY small r "
      "already cap T at prize scale?")
    p("-" * 100)
    for r0 in (1, 2, 3):
        # max T subject ONLY to constraint r = r0 (and s2 >= 0), same convexity
        A0 = m * n - (n - 1)
        m2 = m - 2
        rhs = dfact(r0) * (n**r0) * m * (m2**r0)
        def ok1(T, r0=r0, rhs=rhs):
            s2num = A0 - 2 * T * T
            if s2num < 0:
                return False
            return 2 * T**(2 * r0) * m2**r0 + m2 * s2num**r0 <= rhs
        lo, hi = 0, 1
        while ok1(hi):
            lo, hi = hi, hi * 2
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ok1(mid):
                lo = mid
            else:
                hi = mid
        p(f"  r = {r0} alone: Tmax = {lo}  ~ 2^{math.log2(lo):.2f}  "
          f"~ {lo/sqrtnlnm:.3g} * sqrt(n ln m)  -->  "
          f"{'NO small-r cap (orders above prize scale)' if lo*lo > 64*n*L_HI else 'CAPS AT PRIZE SCALE (!!)'}")
    p("  r = 1 is the Parseval constraint itself (equality by construction, "
      "P2 = n-(n-1)/m < n = 1!!*n^1: satisfied strictly).")

    # ------------------------------------------------------------------
    # the Lean brick's toy instance (theorem MUST match probe: pitfall (d))
    # ------------------------------------------------------------------
    p("\n" + "-" * 100)
    p("TOY INSTANCE for Frontier/_R2B_CMKDepthIrreducibility.lean "
      "(n = 2^10, m = 2^40, R = 5, T = 900)")
    p("-" * 100)
    tn, tm, tR, tT = 2**10, 2**40, 5, 900
    tlo, thi = ln_pow2_bracket(40)
    p(f"  ln m = 40*ln2 in ({float(tlo):.6f}, {float(thi):.6f}); L := 28 >= ln m "
      f"(certified: 40*ln2 < 40*{float(LN2_HI):.10f} < 28); R = 5 << 28")
    A0 = tm * tn - (tn - 1)
    s2num = A0 - 2 * tT * tT
    p(f"  A = m*n-(n-1)-2T^2 = {s2num}  (>0: s^2 = A/(m-2) >= 0 OK)")
    p(f"  s^2 = {s2num}/{tm-2} ~ {s2num/(tm-2):.6f}  (vs n = {tn})")
    m2 = tm - 2
    allok = True
    for r in range(1, tR + 1):
        lhs = 2 * tT**(2 * r) * m2**r + m2 * s2num**r
        rhs = dfact(r) * tn**r * tm * m2**r
        ok = lhs <= rhs
        allok &= ok
        p(f"  r={r}: m_2r <= {dfact(r)}*n^{r} ?  lhs/rhs = {lhs/rhs:.6f}  "
          f"{'OK' if ok else 'VIOLATED'}   (exact integers compared)")
    # Parseval identity
    p(f"  Parseval: m_2 = (2T^2 + A)/m = (m*n-(n-1))/m = P2 exact (identity).")
    edge = tT * tT > 16 * tn * 28
    p(f"  edge: T^2 = {tT*tT} > 16*n*L = {16*tn*28} ?  "
      f"{'YES' if edge else 'NO'}  ==> T > 4*sqrt(n*L) >= 4*sqrt(n ln m)")
    toy_msg = ("ALL constraints verified; edge exceeds 4*sqrt(n ln m); "
               "matches the Lean brick") if (allok and edge) else "MISMATCH (!!)"
    p(f"  toy verdict: {toy_msg}")

    # ------------------------------------------------------------------
    # verdict
    # ------------------------------------------------------------------
    p("\n" + "=" * 100)
    p("VERDICT")
    p("=" * 100)
    p("""
The abstract CMK moment-problem theorem is FALSE at every depth R << log m:
the symmetric 4-value equal-atom measure satisfies (i) m equal real atoms,
(ii) EXACT Parseval m_2 = P2 = n-(n-1)/m, (iii) the full Wick envelope
m_2r <= K^r (2r-1)!! n^r for ALL r <= R, and (iv) every positivity/Hankel/
Krein constraint (it is an actual measure) -- yet its edge T exceeds
8*sqrt(n ln m) for R <= 11 (K=1; ratio ~12*sqrt(2n ln m) at R=11, ~7000x at
R=4) and still exceeds 2*sqrt(n ln m) at R = 22.  Depth is IRREDUCIBLE:
moment data to depth R buys edge control m^(1/2R) -- no theorem from these
inputs at R << log m can bound the edge at the prize scale, so CMK cannot
shortcut the r ~ ln q Wick obligation.  The admissible edge falls back to
O(sqrt(n log m)) only at R ~ ln m (binding r plateaus at r* ~ ln(m/2) ~ 88),
recovering exactly the known conditional moment bound -- nothing new there.

Scope (honest): this kills ONLY the abstract-moment form of CMK (equal atoms
+ Parseval + Wick-to-depth-R as the ONLY inputs).  A b_k-native (Jacobi/
Hankel-window) CMK variant consuming MORE than moments is not touched -- but
round-1 P4 independently found no O(1)-window Hankel functional pins k*
per-prime, so that route is separately squeezed.
""")

    with open("scripts/probes/_out_466b_cmk_countermeasure.txt", "w") as f:
        f.write("\n".join(out) + "\n")
    p("[written scripts/probes/_out_466b_cmk_countermeasure.txt]")

if __name__ == "__main__":
    run()
