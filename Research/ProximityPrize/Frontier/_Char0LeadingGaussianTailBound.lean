/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The char-0 LEADING term obeys the Gaussian-tail bound — RIGOROUSLY (#444, conj #3 corrected)

## Context (probe-grounded, see `scripts/probes/`)

The machine campaign found a **Gaussian-tail decay law** for the DC-subtracted additive energy:
`A_r / Wick ≈ exp(−r²/2n)` (fitted constant `c → 1/2`, `Wick = (2r−1)‼·n^r`); the in-tree
`_ErWickGaussianTailDecay` lands `decay-law ⟹ prize` but leaves the law itself as the named open input.

Conjecture #3 proposed an *exact* closed form `A_r = Wick·∏_{j=1}^{r−1}(1−j/n)` (the falling-factorial /
discrete-Gaussian correction). **`scripts/probes/probe_falling_factorial_char0_energy.py` REFUTES exactness**:
the true char-0 generic additive energy decays strictly FASTER than `Wick·∏(1−j/n)` (e.g. n=8,r=6:
`E_r/Wick = 0.0258` vs `∏(1−j/n) = 0.0769`). So #3 as an equality is FALSE.

**What IS true and provable** (`probe_char0_energy_exact_formula.py`, `probe_char0_leading_and_wick.py`,
`probe_leading_gaussian_tail_bound.py`, all PASS): the char-0 generic additive energy
`E_r^{char0} = #{(a,b)∈Sᵣ×Sᵣ : Σa = Σb}` has the exact partition formula, whose **leading (all-distinct)
term** is `L_r = r!·n^{(r)} = r!·n^r·∏_{j=0}^{r−1}(1−j/n)` (`n^{(r)}` = the falling factorial of `n`). For
depth within the regime (`r ≤ n`, which holds at prize scale `r ≈ log p ≪ n`), this leading term satisfies
the **Gaussian-tail bound rigorously**:
  `L_r ≤ Wick · exp(−r(r−1)/(2n))`,
because `r! ≤ (2r−1)‼` and `∏_{j=1}^{r−1}(1−j/n) ≤ exp(−r(r−1)/(2n))` (each `1−x ≤ e^{−x}`).

This file proves that chain with NO open input: it turns the machine-FITTED `exp(−r²/2n)` factor into a
**proven** inequality for the dominant char-0 contribution. **Honest scope:** this is the char-0
leading-term fact only — NOT the prize. The prize is the char-`p` transfer of the *full* energy bound
(the BGK/Paley wall, with the non-abelian Chebotarev obstruction of `_CharPTransferChebotarevObstruction`).
No CORE/BGK/capacity claim is made.

**CRITICAL CLARIFICATION (generic ≠ subgroup; see `_SubgroupVsGenericEnergyReconcile`).** The `E_r^{char0}`
here is the energy of a GENERIC (Sidon-to-high-order) set, which sits BELOW the falling-factorial form
`(2r−1)‼·(n)_r = Wick·∏(1−j/n)` (probe n=8,r=2: `120 < 168`). The PRIZE object is the multiplicative
SUBGROUP `μ_n`, which is generally NOT Sidon and EXCEEDS the falling-factorial form at deep `r`, the excess
growing with `r` (probe `E_r(μ_n)/[Wick·∏(1−j/n)]` = 1.0→1.016→1.078 at n=8). The subgroup `E_r(μ_n)` is
(n,p)-DEPENDENT (NOT a universal closed form): at r=2 it is `2n²−n` for n=3,5 (Sidon), `3n²−3n` for n=4,6,8,
and p-dependent at n=16 — see `_SubgroupVsGenericEnergyReconcile` for the full honest accounting (an earlier
draft over-claimed `E_2(μ_n)=3n²−3n` universally; FALSE, corrected after adversarial re-audit). So conj #3
fails on BOTH sides — generic decays faster (below), subgroup variably above (Shaw 0040d6507) — and the prize
wall lives in the (n,p)-dependent subgroup EXCESS. The `leadingTerm` and bounds below are the GENERIC
leading-term object (a clean lower reference), NOT a bound on the subgroup energy.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Char0LeadingGaussianTailBound

open scoped BigOperators
open Finset Real

/-- The factorial factor `r! = ∏_{j∈range r}(j+1)`, as a real number. -/
noncomputable def factFactor (r : ℕ) : ℝ := ∏ j ∈ range r, ((j : ℝ) + 1)

/-- The double-factorial / Wick factor `(2r−1)‼ = ∏_{j∈range r}(2j+1)` (= `1·3·5···(2r−1)`), as a real. -/
noncomputable def wickFactor (r : ℕ) : ℝ := ∏ j ∈ range r, (2 * (j : ℝ) + 1)

/-- The falling-factorial product `∏_{j∈range r}(1 − j/n)` (the `j=0` factor is `1`, so this equals
`∏_{j=1}^{r−1}(1 − j/n)`). This is the discrete-Gaussian correction in conj #3. -/
noncomputable def fallingProd (n : ℝ) (r : ℕ) : ℝ := ∏ j ∈ range r, (1 - (j : ℝ) / n)

/-- The char-0 leading term `L_r = r!·n^r·∏_{j=0}^{r−1}(1−j/n)` (= `r!·n^{(r)}`, the all-distinct
contribution to the char-0 generic additive energy). -/
noncomputable def leadingTerm (n : ℝ) (r : ℕ) : ℝ := factFactor r * n ^ r * fallingProd n r

/-- The Wick ceiling `Wick = (2r−1)‼·n^r`. -/
noncomputable def wick (n : ℝ) (r : ℕ) : ℝ := wickFactor r * n ^ r

/-- **Fact F: `r! ≤ (2r−1)‼`.** Termwise `j+1 ≤ 2j+1` over `range r`, both nonneg factors. -/
theorem factFactor_le_wickFactor (r : ℕ) : factFactor r ≤ wickFactor r := by
  unfold factFactor wickFactor
  apply Finset.prod_le_prod
  · intro j _; positivity
  · intro j _
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith

/-- `0 ≤ r!` factor. -/
theorem factFactor_nonneg (r : ℕ) : 0 ≤ factFactor r := by
  unfold factFactor; apply Finset.prod_nonneg; intro j _; positivity

/-- `0 < (2r−1)‼` factor. -/
theorem wickFactor_pos (r : ℕ) : 0 < wickFactor r := by
  unfold wickFactor; apply Finset.prod_pos; intro j _; positivity

/-- Each falling factor is nonneg in the regime `r ≤ n`: for `j ∈ range r`, `j < r ≤ n` so `j/n ≤ 1`. -/
theorem fallingProd_factor_nonneg {n : ℝ} (hn : 0 < n) {r : ℕ} (hr : (r : ℝ) ≤ n)
    {j : ℕ} (hj : j ∈ range r) : (0 : ℝ) ≤ 1 - (j : ℝ) / n := by
  rw [mem_range] at hj
  have hjr : (j : ℝ) < r := by exact_mod_cast hj
  have hjn : (j : ℝ) < n := lt_of_lt_of_le hjr hr
  have : (j : ℝ) / n ≤ 1 := by
    rw [div_le_one hn]; linarith
  linarith

/-- `0 ≤ fallingProd n r` in the regime `r ≤ n`. -/
theorem fallingProd_nonneg {n : ℝ} (hn : 0 < n) {r : ℕ} (hr : (r : ℝ) ≤ n) :
    0 ≤ fallingProd n r := by
  unfold fallingProd
  apply Finset.prod_nonneg
  intro j hj
  exact fallingProd_factor_nonneg hn hr hj

/-- The sum identity `∑_{j∈range r} j = r(r−1)/2` over `ℝ` (Gauss). -/
theorem sum_range_id_real (r : ℕ) :
    (∑ j ∈ range r, (j : ℝ)) = (r : ℝ) * ((r : ℝ) - 1) / 2 := by
  have : (∑ j ∈ range r, (j : ℝ)) = ((∑ j ∈ range r, j : ℕ) : ℝ) := by
    push_cast; ring
  rw [this, Finset.sum_range_id]
  -- Nat.sum_range_id gives `r*(r-1)/2`? Mathlib: `Finset.sum_range_id_mul_two` and `Gauss`.
  -- Use the standard `Finset.sum_range_id : ∑ i in range n, i = n*(n-1)/2`.
  cases r with
  | zero => simp
  | succ m =>
    have h2 : ((Nat.succ m * (Nat.succ m - 1) / 2 : ℕ) : ℝ)
        = (Nat.succ m : ℝ) * ((Nat.succ m : ℝ) - 1) / 2 := by
      have hdvd : 2 ∣ Nat.succ m * (Nat.succ m - 1) := by
        have := Nat.even_mul_pred_self (Nat.succ m)
        exact (even_iff_two_dvd).1 this
      rw [Nat.cast_div hdvd (by norm_num)]
      push_cast
      ring
    rw [h2]

/-- **Fact B (the rigorous Gaussian-tail half).** For `0 < n` and `r ≤ n`,
`∏_{j∈range r}(1 − j/n) ≤ exp(−r(r−1)/(2n))`. Each factor `1 − j/n ≤ exp(−j/n)` (elementary
`1 − x ≤ e^{−x}`), the product of exponentials is the exponential of the sum, and `∑ j = r(r−1)/2`. -/
theorem fallingProd_le_gaussianTail {n : ℝ} (hn : 0 < n) {r : ℕ} (hr : (r : ℝ) ≤ n) :
    fallingProd n r ≤ Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n)) := by
  have key : fallingProd n r ≤ Real.exp (-(∑ j ∈ range r, (j : ℝ)) / n) := by
    unfold fallingProd
    calc ∏ j ∈ range r, (1 - (j : ℝ) / n)
        ≤ ∏ j ∈ range r, Real.exp (-((j : ℝ) / n)) := by
          apply Finset.prod_le_prod
          · intro j hj; exact fallingProd_factor_nonneg hn hr hj
          · intro j _
            have h := Real.add_one_le_exp (-((j : ℝ) / n))
            linarith
      _ = Real.exp (∑ j ∈ range r, -((j : ℝ) / n)) := by rw [← Real.exp_sum]
      _ = Real.exp (-(∑ j ∈ range r, (j : ℝ)) / n) := by
          congr 1
          rw [neg_div, Finset.sum_div]
          simp
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [sum_range_id_real]
  rw [neg_div, neg_div, div_div]

/-- **Fact E (the brick): the char-0 LEADING term obeys the Gaussian-tail bound.** For `0 < n` and
`r ≤ n` (the prize regime `r ≈ log p ≪ n`),
  `L_r = r!·n^r·∏_{j=0}^{r−1}(1−j/n)  ≤  (2r−1)‼·n^r · exp(−r(r−1)/(2n)) = Wick·exp(−r(r−1)/(2n))`.
This converts the machine-FITTED `exp(−r²/2n)` factor into a PROVEN inequality for the dominant
(all-distinct) contribution to the char-0 generic additive energy. NOT the prize (char-`p` transfer = wall);
honest char-0 leading-term scope only. -/
theorem leadingTerm_le_wick_gaussianTail {n : ℝ} (hn : 0 < n) {r : ℕ} (hr : (r : ℝ) ≤ n) :
    leadingTerm n r ≤ wick n r * Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n)) := by
  unfold leadingTerm wick
  have hnr : (0 : ℝ) ≤ n ^ r := by positivity
  have hfall := fallingProd_le_gaussianTail hn hr
  have hfact := factFactor_le_wickFactor r
  have hfact_nn := factFactor_nonneg r
  have hwf_pos := wickFactor_pos r
  have hexp_pos : (0 : ℝ) < Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n)) := Real.exp_pos _
  have hfall_nn := fallingProd_nonneg hn hr
  -- factFactor r * n^r * fallingProd  ≤  wickFactor r * n^r * exp(...)
  -- step 1: factFactor * fallingProd ≤ wickFactor * exp(...)   (both bounds, nonneg)
  have hstep : factFactor r * fallingProd n r
      ≤ wickFactor r * Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n)) := by
    calc factFactor r * fallingProd n r
        ≤ wickFactor r * fallingProd n r :=
          mul_le_mul_of_nonneg_right hfact hfall_nn
      _ ≤ wickFactor r * Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n)) :=
          mul_le_mul_of_nonneg_left hfall (le_of_lt hwf_pos)
  calc factFactor r * n ^ r * fallingProd n r
      = (factFactor r * fallingProd n r) * n ^ r := by ring
    _ ≤ (wickFactor r * Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n))) * n ^ r :=
        mul_le_mul_of_nonneg_right hstep hnr
    _ = wickFactor r * n ^ r * Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n)) := by ring

/-- **Corollary: the leading term is sub-Wick.** `L_r ≤ Wick` (the Gaussian-tail factor is `≤ 1`), i.e. the
char-0 leading contribution already obeys the prize-shaped ceiling. (The `exp(·) ≤ 1` factor matches the
in-tree `gaussianTail_le_one`.) -/
theorem leadingTerm_le_wick {n : ℝ} (hn : 0 < n) {r : ℕ} (hr : (r : ℝ) ≤ n) :
    leadingTerm n r ≤ wick n r := by
  refine (leadingTerm_le_wick_gaussianTail hn hr).trans ?_
  have hw : 0 ≤ wick n r := by
    unfold wick; have := wickFactor_pos r; positivity
  have hle1 : Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
      have hr1 : (-1 : ℝ) ≤ (r : ℝ) - 1 := by linarith
      rcases Nat.eq_zero_or_pos r with hr0' | hr0'
      · subst hr0'; simp
      · have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0'
        nlinarith
    · positivity
  calc wick n r * Real.exp (-((r : ℝ) * ((r : ℝ) - 1)) / (2 * n))
      ≤ wick n r * 1 := mul_le_mul_of_nonneg_left hle1 hw
    _ = wick n r := mul_one _

end ArkLib.ProximityGap.Char0LeadingGaussianTailBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Char0LeadingGaussianTailBound.factFactor_le_wickFactor
#print axioms ArkLib.ProximityGap.Char0LeadingGaussianTailBound.fallingProd_le_gaussianTail
#print axioms ArkLib.ProximityGap.Char0LeadingGaussianTailBound.leadingTerm_le_wick_gaussianTail
#print axioms ArkLib.ProximityGap.Char0LeadingGaussianTailBound.leadingTerm_le_wick
