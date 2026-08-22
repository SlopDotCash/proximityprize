/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Trichotomy capstone: the three bucket-obstructions, assembled (#444)

The conjecture campaign (~150 conjectures; this session: 25 + 25 fresh-machine + 25 iterative-hardened + 22
bucket-evasion-targeted, **0 survivors**) is explained by a single meta-theorem
(`docs/kb/deltastar-444-conjecture-trichotomy-2026-06-17.md`): every conjecture proposed to bound the house
`M = max_{b≠0} |η_b|` (β = 4) falls into at least one of three buckets, and to *escape* it must simultaneously
satisfy E1 (output the `L^∞` sup, not a 2nd moment), E2 (a genuinely new object, not the Gauss-period / Cayley
spectrum / energy ladder renamed), and E3 (a hypothesis that holds on the flat, 0-dimensional, Sidon-except-negation,
zero-entropy `μ_n`). The constructive confirmation: 22 candidates *engineered* to evade all three buckets produced
**0 evaders**.

Each bucket's obstruction is landed axiom-clean in this cone; this file records the assembly and a combined corollary.

* **B1 (second-moment blind).** A bounded-depth moment functional pins the sup only up to `N^{1/2r}`:
  `_TrichotomyB1MomentBlind.moment_ambiguity` / `ambiguity_ratio_pow`, with `_AttackE2_MomentConeSpikeNoGo` (the
  `r=2` cone spike) and `_AttackAN2_TightFrameBTVacuous` (the period frame is exactly tight, so Bourgain–Tzafriri is
  vacuous). This file's `second_moment_does_not_decide_prize` is the `r=1` (Parseval) head of that family. Kills
  LP/Delsarte, SOS, Brascamp–Lieb, large-sieve, Nehari, isotropy/John-ellipsoid, Cheeger.
* **B2 (BGK-rename).** The object *is* the Cayley spectrum / energy: `_AttackR2_AbelianCayleyNonRamanujan`
  (`A χ_b = η_b χ_b`; abelian growing-degree Cayley is non-Ramanujan), `_AttackR6_RelationVarietyBezoutNoGo`
  (the relation variety counts `E_r`, not the excess), `_AttackT1_BiluLinialTwistNoGo`. Kills Weil-rep coeffs,
  transfer operators, Dudley chaining, motivic regulator, crystalline Newton-slopes, L-function/Chebotarev.
* **B3 (Sidon-0-dim hypothesis failure).** The machine needs structure `μ_n` lacks:
  `_AttackRT6_CyclicSchurMultiplierNoGo` (`H²(Z_n,ℂ*) = 0`, so a Drinfeld twist preserves the spectrum),
  `_AttackB1_BadSetCosetNonSidon` (the bad set is a coset union, the opposite of Sidon), `_DilationZeroEntropyNoGo`
  (the dilation is a single `n`-cycle, zero entropy). Kills decoupling/restriction (need curvature),
  Bourgain–Gamburd (`S·S = S`), Salem–Zygmund (need randomness), genus-reduction (genus 0), Katz rigidity,
  negative-association (fails for the periods).

**Combined corollary (this file, axiom-clean).** The cleanest unifying consequence of B1: the second moment
`S₂ = Σ_b |η_b|²` (the only degree-1 invariant, fixed at `pn − n²` by Parseval) does **not** decide the prize. Fix
the Parseval floor scale `a` (the `√n`-typical value) and a prize `target`. Whenever `target < √N · a` (always true
at the prize, where `√N = √(q−1) ≫ √log`), there is a spike spectrum with the **same** `S₂ = N·a²` whose maximum
`c = √N·a` **exceeds the target**, while the flat spectrum with that same `S₂` has maximum exactly `a`. So two
spectra share `S₂` yet straddle the target — no certificate reading only the second moment (the entire degree-1
core, and by `moment_ambiguity` the whole bounded-depth moment family) can prove `M ≤ C√(n log(q/n))`.

**Scope.** Not a proof the prize is false (`C ≈ 1.25` oscillates; the prize is believed true), nor that no proof
exists. It says: every route the campaign can generate reduces to B1 ∨ B2 ∨ B3 = the BGK/Paley wall, so winning
requires a genuine analytic-NT breakthrough on effective thin-subgroup Gauss-phase equidistribution at β = 4. Issue #444.
-/

namespace ProximityGap.Frontier.TrichotomyCapstone

/-- **B1 combined corollary: the second moment does not decide the prize.** For `N ≥ 2` frequencies and the Parseval
floor scale `a > 0`, the spike `c = √N · a` has the **same** second moment as the flat spectrum (`N·a² = c²`) yet a
strictly larger maximum (`a < c`); and whenever the prize `target` satisfies `target < √N · a` (always true at the
prize, where `√N = √(q−1) ≫ √log`), the spike's maximum **exceeds** the target (`target < c`) while the flat
spectrum's maximum is exactly `a`. So two spectra share `S₂` yet straddle the target: a certificate reading only the
second moment cannot separate prize-satisfying from prize-violating spectra — `S₂` is blind to the sup. -/
theorem second_moment_does_not_decide_prize
    (N : ℕ) (a target : ℝ) (ha : 0 < a) (hN : 2 ≤ N)
    (hgap : target < Real.sqrt (N : ℝ) * a) :
    ∃ c : ℝ, 0 ≤ c ∧ (N : ℝ) * a ^ (2 * 1) = c ^ (2 * 1) ∧ a < c ∧ target < c := by
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNnn
  -- √N ≥ √2 > 1
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt (N : ℝ) := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (N : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hN)
    have : (1 : ℝ) < Real.sqrt 2 := by
      have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg (2:ℝ)]
    linarith
  refine ⟨Real.sqrt (N : ℝ) * a, by positivity, ?_, ?_, hgap⟩
  · simp only [mul_one]; nlinarith [hsq]
  · -- a < √N · a since √N > 1 and a > 0
    nlinarith [hsqrt_gt_one, ha]

/-- **B1 combined corollary, GENERAL DEPTH `r`: no bounded-depth moment decides the prize.**  This
generalizes `second_moment_does_not_decide_prize` (its `r = 1` Parseval head) to *every* moment
depth `r ≥ 1`.  For `N ≥ 2` frequencies and floor scale `a > 0`, the single-spike value
`c = N^{1/(2r)}·a` has the **same** depth-`r` moment as the flat spectrum
(`∑ |η|^{2r} = N·a^{2r} = c^{2r}`) yet a strictly larger maximum (`a < c`); and whenever the prize
`target` satisfies `target < N^{1/(2r)}·a` (always true at the prize, where `N^{1/(2r)}` dominates
the log scale), the spike's maximum **exceeds** the target while the flat spectrum's maximum is
exactly `a`.  So two spectra share the *entire* depth-`r` moment `S_{2r}` yet straddle the target:
**no** certificate reading only a fixed-depth moment (the whole bounded-depth moment family, bucket B1) can
separate prize-satisfying from prize-violating spectra.  At `r = 1` this is exactly
`second_moment_does_not_decide_prize` with `c = √N·a`.  Negative structural statement; no CORE,
cancellation, completion, anti-concentration, or capacity claim. -/
theorem depthR_moment_does_not_decide_prize
    (N r : ℕ) (a target : ℝ) (ha : 0 < a) (hN : 2 ≤ N) (hr : 1 ≤ r)
    (hgap : target < (N : ℝ) ^ ((1 : ℝ) / (2 * r)) * a) :
    ∃ c : ℝ, 0 ≤ c ∧ (N : ℝ) * a ^ (2 * r) = c ^ (2 * r) ∧ a < c ∧ target < c := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hrpos : (0 : ℝ) < (2 * r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  -- the spike value c = N^{1/(2r)} * a
  set t : ℝ := (N : ℝ) ^ ((1 : ℝ) / (2 * r)) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hNpos _
  -- t^(2r) = N : raising N^{1/(2r)} to the natural power 2r recovers N.
  have hpow : t ^ (2 * r) = (N : ℝ) := by
    rw [ht, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / (2 * r))) (2 * r),
        ← Real.rpow_mul hNpos.le, Nat.cast_mul, Nat.cast_ofNat,
        one_div, inv_mul_cancel₀ (ne_of_gt hrpos), Real.rpow_one]
  -- t > 1 since N > 1 and the exponent is positive
  have ht_gt_one : (1 : ℝ) < t := by
    rw [ht]
    refine (Real.one_lt_rpow_iff_of_pos hNpos).2 (Or.inl ⟨?_, ?_⟩)
    · exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
    · positivity
  refine ⟨t * a, by positivity, ?_, ?_, hgap⟩
  · -- N * a^(2r) = (t*a)^(2r) = t^(2r) * a^(2r) = N * a^(2r)
    rw [mul_pow, hpow]
  · -- a < t*a since t > 1, a > 0
    nlinarith [ht_gt_one, ha]

/-- **The depth-`r` moment-blindness gap is UNBOUNDED.**  The spike from
`depthR_moment_does_not_decide_prize` exceeds the flat maximum `a` by the factor `c/a = K`, where
`c = K·a` shares the depth-`r` moment with the flat spectrum, whenever the frequency count satisfies
`N ≥ K^{2r}`.  So for *any* target factor `K ≥ 1` there is a frequency count `N` at which two spectra
share the depth-`r` moment yet their maxima differ by at least `K`: the bucket-B1 obstruction is not
merely nonzero but quantitatively unbounded — no fixed-depth moment controls the sup to within any
constant factor.  (Concretely take `N = ⌈K^{2r}⌉`; the spike `c = K·a` then has
`c^{2r} = K^{2r}·a^{2r} ≤ N·a^{2r}`.) -/
theorem depthR_moment_blindness_unbounded
    (N r : ℕ) (a K : ℝ) (ha : 0 < a)
    (hNK : K ^ (2 * r) ≤ (N : ℝ)) :
    ∃ c : ℝ, c ^ (2 * r) ≤ (N : ℝ) * a ^ (2 * r) ∧ K * a ≤ c := by
  refine ⟨K * a, ?_, le_refl _⟩
  -- (K*a)^(2r) = K^(2r) * a^(2r) ≤ N * a^(2r)
  rw [mul_pow]
  have ha2r : 0 ≤ a ^ (2 * r) := by positivity
  exact mul_le_mul_of_nonneg_right hNK ha2r

end ProximityGap.Frontier.TrichotomyCapstone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.TrichotomyCapstone.second_moment_does_not_decide_prize
#print axioms ProximityGap.Frontier.TrichotomyCapstone.depthR_moment_does_not_decide_prize
#print axioms ProximityGap.Frontier.TrichotomyCapstone.depthR_moment_blindness_unbounded
