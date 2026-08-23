/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# The incidence-deviation bound from a uniform char-sum (Gauss-period) bound — #407

This file proves the **deviation-of-incidence brick**: the quantitative step that turns a
uniform per-frequency bound `‖η_b‖ ≤ B` (`b ≠ 0`) on the subgroup Gauss period into a bound on
how far the far-line incidence `I(s₀, s₁)` can stray from its first-moment mean `|G|`.

## WHAT IS AND IS NOT PROVEN (honesty header — read before reusing)

The bound proven here is the **naive `(#frequencies)·B` triangle bound** over the deviation-support
hyperplane, summed *with no cancellation between distinct frequencies*:

  > `I(s₀, s₁) ≤ |G| + (#deviationSupport s₁)·B ≤ |G| + q·B`   (`q = |F|`).

It is the per-*term* bound `‖η_b‖ ≤ B` applied independently to each of the up-to-`q` annihilating
frequencies and then triangle-summed.  It is **NOT** a claim that the char-sum bound `B` "feeds
far-line incidence linearly with no √-loss into the prize budget", and it is **NOT** a per-frequency
`I ≲ B` bound.  The factor of `q` on `B` is real: the deviation support is a whole hyperplane of
size up to `q`, and this brick assumes worst-case alignment (no oscillatory cancellation among the
`#deviationSupport` error terms).  Whether those terms *do* cancel down to `√q · B`-scale (the
square-root-cancellation that the prize budget needs) is exactly the **open Paley/BCHKS-1.12
square-root** and is **not** addressed here.

The mechanism is the exact term-by-term spectral identity
`IncidencePeriodBridge.lineIncidence_period_sum`:

  > `I(s₀, s₁) = ∑_{b : b·s₁ = 0} conj(η_b) · ψ(b·s₀)`.

The trivial frequency `b = 0` always satisfies `b·s₁ = 0`, contributes `conj(η₀)·ψ(0) = |G|`
(the average / first moment), and the remaining `s₁^⊥ \ {0}` frequencies carry the spectral
error.  Each error term has modulus `‖conj(η_b)·ψ(b·s₀)‖ = ‖η_b‖ · 1 ≤ B` (additive characters
have unit modulus, conjugation is an isometry), so the **triangle-summed** total deviation is

  > `|I(s₀, s₁) − |G|| ≤ (#{b ≠ 0 : b·s₁ = 0}) · B ≤ q·B`.

**Relation to the energy lane.**  The competing energy lane (`addEnergy_le_of_worstCase`) loses a
square root (`T² ≤ |G|·E`).  This brick avoids *that particular* loss because it is the raw
`(#frequencies)·B` count, but the trade is that it pays a full factor of `q` on `B` (one per error
term, no inter-term cancellation).  It is **linear in `B`** only in the sense that `B` enters
once per term; it does **not** make the prize budget reachable for any nonzero `B` (see
`CharSumDeltaStarBridge` for the budget arithmetic: `(|G| + q·B)/q ≤ ε*` at the prize budget
`q·ε* ≈ n` forces `B ≲ 0`).  Reaching `q·ε* ≈ n` requires the per-frequency square-root
cancellation `∑_b conj(η_b)ψ(b·s₀) ≲ √q · B`, which is the open Paley/BCHKS-1.12 problem and is
NOT supplied by this file.

This is the intermediate brick consumed by the bridge theorem
`CharSumDeltaStarBridge.le_mcaDeltaStar_of_uniformCharSumBound`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); pure triangle inequality on the
term-by-term spectral identity, no field-size or regime hypotheses.  Issue #407.
-/

set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.IncidenceDeviationCharSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The set of **nonzero** frequencies annihilating the line direction `s₁` — the spectral
support of the incidence deviation (the `s₁^⊥` hyperplane minus the trivial frequency). -/
def deviationSupport (s₁ : F) : Finset F :=
  (Finset.univ.filter (fun b : F => b * s₁ = 0)).erase 0

omit [DecidableEq F] in
/-- An additive character has modulus `1` on every input. Over a finite field every value
`ψ a : ℂ` is a root of unity (`val_mem_rootsOfUnity`), hence a pure phase. -/
theorem norm_addChar_apply (ψ : AddChar F ℂ) (a : F) : ‖ψ a‖ = 1 := by
  have hR : 0 < ringChar F := by
    have := CharP.ringChar_ne_zero_of_finite F
    omega
  have H := Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.val_mem_rootsOfUnity a hR)
  rwa [IsUnit.unit_spec] at H

/-- **The trivial frequency contributes the first moment.** At `b = 0` the spectral term is
`conj(η₀)·ψ(0) = |G|`. -/
theorem zero_freq_term {ψ : AddChar F ℂ} (G : Finset F) (s₀ : F) :
    (starRingEnd ℂ) (eta ψ G 0) * ψ (0 * s₀) = (G.card : ℂ) := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by
    simp [eta, AddChar.map_zero_eq_one]
  rw [h0, zero_mul, AddChar.map_zero_eq_one, mul_one, map_natCast]

/-- **The incidence-deviation identity.** The far-line incidence minus its first-moment mean
`|G|` equals the sum of period terms over the *nonzero* annihilating frequencies:

  `I(s₀, s₁) − |G| = ∑_{b ∈ deviationSupport s₁} conj(η_b)·ψ(b·s₀)`.

This isolates the spectral error from the average. -/
theorem incidence_sub_mean {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) :
    (lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)
      = ∑ b ∈ deviationSupport s₁,
          (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀) := by
  classical
  have hmem : (0 : F) ∈ Finset.univ.filter (fun b : F => b * s₁ = 0) := by
    simp
  rw [lineIncidence_period_sum hψ G s₀ s₁,
    ← Finset.add_sum_erase _ _ hmem, zero_freq_term G s₀]
  unfold deviationSupport
  ring

/-- **The deviation bound from a uniform char-sum bound (modulus form).** If every nonzero
frequency has `‖η_b‖ ≤ B`, then the far-line incidence deviates from its first-moment mean by at
most the number of nonzero annihilating frequencies times `B`:

  `|I(s₀, s₁) − |G|| ≤ (#deviationSupport s₁) · B`.

Pure triangle inequality on `incidence_sub_mean`; each error term has modulus
`‖η_b‖·‖ψ(b·s₀)‖ = ‖η_b‖ ≤ B`.  This is the **naive `(#frequencies)·B` count** — `B` is paid once
per annihilating frequency, with **no cancellation assumed between distinct frequencies**, and
`#deviationSupport` is a hyperplane of size up to `q` (`deviationSupport_card_le`).  It is NOT a
per-frequency `I ≲ B` bound and does NOT escape the prize budget for nonzero `B` (the genuine
square-root cancellation `∑_b ≲ √q·B` is the open Paley/BCHKS-1.12 problem, not proven here). -/
theorem incidence_dev_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) {B : ℝ}
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖
      ≤ ((deviationSupport s₁).card : ℝ) * B := by
  classical
  rw [incidence_sub_mean hψ G s₀ s₁]
  calc ‖∑ b ∈ deviationSupport s₁, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)‖
      ≤ ∑ b ∈ deviationSupport s₁, ‖(starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _b ∈ deviationSupport s₁, B := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
        rw [norm_mul, Complex.norm_conj, norm_addChar_apply, mul_one]
        exact hB b hb0
    _ = ((deviationSupport s₁).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The deviation support is bounded by `q`.** A coarse but unconditional cardinality bound:
`#deviationSupport s₁ ≤ #{b : b·s₁ = 0} ≤ |F| = q`.  Combined with `incidence_dev_le` this gives
the worst-case incidence bound `I ≤ |G| + q·B`.  Note the support is genuinely a hyperplane of
size up to `q`; this `q` factor on `B` is what makes the resulting budget hypothesis in
`CharSumDeltaStarBridge` vacuous at the prize budget for nonzero `B` (it is the naive per-frequency
count, not a square-root-cancelled sum). -/
theorem deviationSupport_card_le (s₁ : F) :
    (deviationSupport s₁).card ≤ Fintype.card F := by
  classical
  unfold deviationSupport
  exact le_trans (Finset.card_erase_le)
    (le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_univ)))

/-- **Coarse `q·B` deviation bound.** Combining `incidence_dev_le` with
`deviationSupport_card_le`: under a uniform nonzero-frequency period bound, the complex-valued
incidence deviation is at most `q·B`. This is the exact two-sided band in modulus form; it still
uses the naive triangle sum over all annihilating frequencies, with no inter-frequency
cancellation. -/
theorem incidence_dev_le_q_mul {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖
      ≤ (Fintype.card F : ℝ) * B := by
  classical
  exact le_trans (incidence_dev_le hψ G s₀ s₁ hB) (by
    apply mul_le_mul_of_nonneg_right _ hB0
    exact_mod_cast deviationSupport_card_le s₁)

/-- **Real absolute `q·B` incidence band.** Same as `incidence_dev_le_q_mul`, rewritten as the
real statement `|I(s₀,s₁)-|G|| ≤ q·B`. This is the direct consumer form of the matching upper and
lower bounds below, and makes explicit that the file proves an absolute band, not only two
one-sided inequalities. -/
theorem lineIncidence_abs_sub_mean_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    |(lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ)|
      ≤ (Fintype.card F : ℝ) * B := by
  classical
  have hdev := incidence_dev_le_q_mul hψ G s₀ s₁ hB0 hB
  have hcast : ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖
      = |(lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ)| := by
    rw [show ((lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ))
          = (((lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rwa [hcast] at hdev

/-- **Worst-case incidence upper bound from a uniform char-sum bound.** Combining the deviation
bound with the cardinality bound: under `‖η_b‖ ≤ B` (`b ≠ 0`), the (real, nonnegative) far-line
incidence satisfies

  `I(s₀, s₁) ≤ |G| + q·B`.

This is the **naive `(#frequencies)·B` form** the bridge consumes: the `q·B` term is the full
hyperplane count (one `B` per annihilating frequency, no inter-frequency cancellation), NOT a
square-root-cancelled `√q·B`.  WARNING for the prize budget: at `q·ε* ≈ n` with `|G| ≈ n`, the
bridge's budget `(|G| + q·B)/q ≤ ε*` reduces to `B ≲ ε* − |G|/q ≈ 0`, so this bound clears the
prize budget only for `B = 0`.  A power-saving `B = n^{1−c}` does NOT clear it through this brick;
reaching the budget needs the open per-frequency square-root cancellation (Paley/BCHKS-1.12),
which this file does not supply. -/
theorem lineIncidence_le_mean_add {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    (lineIncidence G s₀ s₁ : ℝ) ≤ (G.card : ℝ) + (Fintype.card F : ℝ) * B := by
  classical
  have hdev := incidence_dev_le hψ G s₀ s₁ hB
  -- Pass to the real part: ‖(I : ℂ) - |G|‖ ≥ |I - |G|| ≥ I - |G| (as reals).
  have hcast : ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖
      = |(lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ)| := by
    rw [show ((lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ))
          = (((lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hcast] at hdev
  have habs : (lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ)
      ≤ ((deviationSupport s₁).card : ℝ) * B :=
    le_trans (le_abs_self _) hdev
  have hcard : ((deviationSupport s₁).card : ℝ) * B ≤ (Fintype.card F : ℝ) * B := by
    apply mul_le_mul_of_nonneg_right _ hB0
    exact_mod_cast deviationSupport_card_le s₁
  linarith

/-- **Worst-case incidence LOWER bound from a uniform char-sum bound.** The matching lower companion
of `lineIncidence_le_mean_add`: the same modulus deviation bound `|I − |G|| ≤ (#devSupport)·B ≤ q·B`
bounds the deviation from BELOW too, so `I(s₀,s₁) ≥ |G| − q·B`. Together with the upper bound this
pins the far-line incidence to the band `|G| ± q·B` around its first-moment mean `|G|`,
from a uniform Gauss-period bound `B`. (Same naive `(#frequencies)·B` triangle scale — see the
file honesty header; NOT the cancellation-sharp bound, and NOT a CORE statement.) -/
theorem lineIncidence_ge_mean_sub {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    (G.card : ℝ) - (Fintype.card F : ℝ) * B ≤ (lineIncidence G s₀ s₁ : ℝ) := by
  classical
  have hdev := incidence_dev_le hψ G s₀ s₁ hB
  have hcast : ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖
      = |(lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ)| := by
    rw [show ((lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ))
          = (((lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hcast] at hdev
  -- the deviation is bounded from below: -(devSupport·B) ≤ I - |G|
  have habs : -(((deviationSupport s₁).card : ℝ) * B)
      ≤ (lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ) :=
    neg_le_of_abs_le hdev
  have hcard : ((deviationSupport s₁).card : ℝ) * B ≤ (Fintype.card F : ℝ) * B := by
    apply mul_le_mul_of_nonneg_right _ hB0
    exact_mod_cast deviationSupport_card_le s₁
  linarith

end ArkLib.ProximityGap.IncidenceDeviationCharSum

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.incidence_sub_mean
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.incidence_dev_le
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.incidence_dev_le_q_mul
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.lineIncidence_abs_sub_mean_le
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.lineIncidence_le_mean_add
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.lineIncidence_ge_mean_sub
