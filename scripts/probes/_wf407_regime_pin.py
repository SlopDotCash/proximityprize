#!/usr/bin/env python3
"""
_wf407_regime_pin.py  --  PIN THE PRIZE REGIME for #407.

Question: is the prize regime FIXED-INDEX (m = 2^128 const, n = Theta(p), beta -> 1)
as the newest comment claims, or THIN (n ~ p^{1/4}, beta ~ 4-5) as the older KB/memory framing says?

Spec (ABF26 / proximity prize): proximity loss target eps* = 2^-128.
Field size q = p must satisfy the field-size requirement q >~ a/eps* where a is the per-fold
list parameter (a = Theta(n/eta), or a = n in the tight BCHKS rows). The cleanest reading of the
prize spec: to get eps* = 2^-128 with a ~ n, you need q ~ a/eps* ~ n * 2^128.
=> p ≈ n * 2^128, i.e. the multiplicative INDEX m = (p-1)/n ≈ 2^128 is HELD CONSTANT as n -> infinity.

We tabulate, for the FIXED-eps* family p = n*2^128 (rounded to a prime conceptually):
  - m = (p-1)/n  (the index; should be ~2^128 constant)
  - beta = log_n p = 1 + 128/log2(n)   (should -> 1)
  - |H|/sqrt(p) = n/sqrt(p) = sqrt(n/2^128)  (positive-proportion test: -> grows; H NOT thin)
  - exponent delta_H s.t. |H| = n = p^{delta_H}, delta_H = log_p n = 1/beta  (-> 1)
  - is n > p^{1/4}?  (Burgess / di Benedetto in-regime test)

Then we CONTRAST with the OLD thin framing's single instance n=2^32 (claimed p=2^160 => |H|=p^{1/5}).
We show that single instance corresponds to a DIFFERENT, larger eps*-budget reading, and trace which
reading the spec actually forces.
"""
import math

print("="*100)
print("PART A — FIXED-eps* family  p ≈ n * 2^128   (q ~ a/eps*, a~n, eps*=2^-128)")
print("="*100)
print(f"{'n=2^k':>8} {'log2(p)':>9} {'m=(p-1)/n':>14} {'log2(m)':>9} "
      f"{'beta=log_n p':>13} {'delta_H=log_p n':>16} {'n/sqrt(p)':>12} {'n>p^.25?':>9}")
EPS_BITS = 128
for k in range(16, 41, 2):
    n = 2.0**k
    log2_p = k + EPS_BITS            # p = n*2^128 => log2 p = k+128
    log2_m = log2_p - k              # = 128 exactly
    m = 2.0**log2_m
    beta = log2_p / k                # log_n p = log2 p / log2 n
    delta_H = k / log2_p             # log_p n
    n_over_sqrtp = 2.0**(k - log2_p/2.0)   # n / sqrt(p) = 2^{k - log2p/2}
    p_quarter_exp = log2_p/4.0
    n_gt_pquarter = k > p_quarter_exp
    print(f"{'2^'+str(k):>8} {log2_p:>9.1f} {'2^'+f'{log2_m:.0f}':>14} {log2_m:>9.1f} "
          f"{beta:>13.4f} {delta_H:>16.4f} {n_over_sqrtp:>12.3e} {str(n_gt_pquarter):>9}")

print()
print("Observations (PART A): m=2^128 CONSTANT (by construction); beta = 1 + 128/k -> 1; "
      "delta_H = log_p n -> 1 (positive proportion exponent).")
print("n/sqrt(p) = sqrt(n)/2^64: at k=128 this hits 1 (H = sqrt p); for k<128 H is SMALLER than sqrt p;")
print("for k>128 H EXCEEDS sqrt p. So 'positive proportion' (n=Theta(p)) is the n->infinity LIMIT, not")
print("true at any finite prize instance with k<128.  n>p^{1/4} test below.")

print()
print("="*100)
print("PART B — when is n > p^{1/4}?  (Burgess / di Benedetto t>p^{1/4} in-regime gate)")
print("="*100)
print("n > p^{1/4}  <=>  k > (k+128)/4  <=>  4k > k+128  <=>  3k > 128  <=>  k > 42.67")
kstar = 128.0/3.0
print(f"  threshold: k* = 128/3 = {kstar:.3f}.  So for n=2^k with k>=43, n>p^{{1/4}} (Burgess regime).")
print(f"  For the often-quoted single instance k=32: 4k=128 < k+128=160 => n=2^32 < p^{{1/4}}=2^40. THIN there.")
print(f"  But the prize is an ASYMPTOTIC family n->infinity; for k>=43 (and certainly k->inf) n>p^{{1/4}}.")

print()
print("="*100)
print("PART C — the OLD 'n=2^32 => p=2^160 => |H|=p^{1/5}' single instance: which eps* does it encode?")
print("="*100)
# old framing: n=2^32, p=2^160 => log2 m = 128. Same m=2^128!  beta = 160/32 = 5.
n_old, log2p_old = 32, 160
log2m_old = log2p_old - n_old
beta_old = log2p_old / n_old
print(f"  n=2^{n_old}, p=2^{log2p_old}:  log2 m = {log2m_old} (= 2^128, SAME index!), "
      f"beta = {beta_old:.1f}, |H|=p^{{1/{beta_old:.0f}}}.")
print(f"  KEY RECONCILIATION: the 'thin' instance n=2^32,p=2^160 has the SAME m=2^128 as the fixed-index")
print(f"  family. 'beta=5' and 'fixed index m=2^128' are the SAME object viewed at ONE finite n=2^32.")
print(f"  beta is LARGE only because n is SMALL relative to 2^128; as n grows toward 2^128, beta -> 2,")
print(f"  and as n -> infinity past 2^128, beta -> 1. The index m=2^128 is the invariant; beta is n-dependent.")

print()
print("="*100)
print("PART D — di Benedetto record bound t^{1-31/2880} vs prize target sqrt(n log m) AT THESE PARAMS")
print("="*100)
print(f"{'n=2^k':>8} {'log2 B_record':>16} {'log2 B_target':>16} {'record/target (log2 gap)':>26}")
for k in range(16, 41, 2):
    n = 2.0**k
    log2_p = k + EPS_BITS
    log2_m = 128.0
    # di Benedetto: B <= t^{1-31/2880}, t=n.  (only valid for t>p^{1/4}; we report anyway for comparison)
    log2_B_record = k * (1.0 - 31.0/2880.0)
    # prize target: B <= C*sqrt(n*log m) ; log2 of sqrt(n ln m) = k/2 + 0.5*log2(ln(2^128))
    ln_m = 128.0*math.log(2.0)
    log2_B_target = k/2.0 + 0.5*math.log2(ln_m)
    gap = log2_B_record - log2_B_target
    print(f"{'2^'+str(k):>8} {log2_B_record:>16.2f} {log2_B_target:>16.2f} {gap:>26.2f}")
print("  The record bound is ~ t^{0.989} ~ n (linear); target ~ sqrt(n). The log2-gap = (0.49*k - const)")
print("  GROWS with k: di Benedetto saves only a power 31/2880 off trivial, never reaches sqrt. Confirmed wall.")

print()
print("="*100)
print("PART E — VERDICT: which wall is load-bearing AT THE REALISTIC PRIZE INSTANCES")
print("="*100)
print("Workbench (PROXIMITY_PRIZE_WORKBENCH.lean:97): production n=2^25, q=n*2^128=2^153, eps*=2^-128.")
print("Spec caps n=2^a at a<=40 (k<=2^40). So every PRIZE instance has k in [25,40].")
print()
print(f"{'n=2^k':>8} {'log2 p':>8} {'beta':>7} {'|H| vs p^.25':>14} {'|H| vs sqrt p':>14}")
for k in [25, 30, 32, 40]:
    logp = k+128
    beta = logp/k
    burgess = 'ABOVE' if k > logp/4 else 'below'
    sqrtp = 'ABOVE' if k > logp/2 else 'below'
    print(f"{'2^'+str(k):>8} {logp:>8} {beta:>7.2f} {burgess:>14} {sqrtp:>14}")
print()
print("FINDINGS:")
print(" 1. The INDEX m=2^128 is constant -> the comment is RIGHT that this is the invariant, not n=p^delta.")
print(" 2. BUT 'beta->1 / positive-proportion' is a PURE n->infinity asymptotic. The Burgess gate k>128/3")
print("    =42.67 is NEVER met for prize k<=40. Every realistic prize instance is THIN (k<p^{1/4} AND k<sqrt p).")
print(" 3. So di-Benedetto/Burgess are NOT in-regime at the actual prize params (their window (p^.25,p^.5)")
print("    requires k in (42.67, ...) — empty for k<=40). The comment's claim that positive-proportion puts")
print("    Burgess back in regime is asymptotically true but VACUOUS at every prize instance.")
print(" 4. The LOAD-BEARING wall at prize params is EFFECTIVE GAUSS-SUM EQUIDISTRIBUTION for a FIXED-INDEX")
print("    (m=2^128) family — geometrically a THIN subgroup at each instance (n=p^{1/beta}, beta in [4.2,6.1]).")
print("    This is the BGK/di-Benedetto thin-subgroup wall, NOT a positive-proportion/Burgess-amenable one.")
print(" 5. RECONCILIATION: 'fixed-index' and 'thin beta~5' are the SAME family. The comment is HALF-RIGHT:")
print("    correct that m is the invariant and the wall is fixed-index Gauss-sum equidistribution; WRONG that")
print("    this moves us out of the thin/BGK regime or into Burgess range at any realizable prize instance.")
print(" 6. The record bound (di-Benedetto t^{1-31/2880}) needs t>p^{1/4} (NOT met at prize k) AND is a half-")
print("    power short anyway. NO method (Burgess/large-sieve/Sato-Tate) is unlocked by the fixed-index view.")
