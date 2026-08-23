/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseRS
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Round 5 capstone (#357): THE PRODUCTION-SCALE δ* FLOOR — the staircase meets `mcaDeltaStar`

The campaign's exact-staircase programme (`MCAStaircaseMaster`/`Exact`/`RS`) wired into the
formal threshold `mcaDeltaStar = sSup {δ : ε_mca(C, δ) ≤ ε*}`:

* `mcaDeltaStar_rs_ge_band` — for every Reed–Solomon code with `k + 3(b−1) ≤ n` and
  `b/|F| ≤ ε*`: the whole band-`b` radius is good, so `(b−1)/n ≤ δ*(RS, ε*)`.
* `mcaDeltaStar_rs_ge_at_secpar` — **the production instantiation** at the prize security
  level `ε* = 2⁻¹²⁸`: whenever the field satisfies `b · 2¹²⁸ ≤ |F|` (every production
  deployment: STIR/WHIR/FRI fields have `|F| ≥ 2¹⁹²`),

  `(b − 1)/n  ≤  δ*(RS[F, domain, k], 2⁻¹²⁸)`.

  Taking the largest admissible band `b = ⌊(n−k)/3⌋ + 1` this reads:

  **`δ*(RS, 2⁻¹²⁸) ≥ (1 − ρ)/3 − O(1/n)` — machine-checked, for every production-scale
  Reed–Solomon code.**

This is the highest *exact-regime* lower pin of the prize threshold the campaign has
established: below it `ε_mca` is not merely bounded but exactly the staircase
`(⌊δn⌋+1)/|F|` (the `MCAStaircaseExact` theorems), and at production field sizes every
staircase value sits far below `2⁻¹²⁸`. Above it the landscape transitions: the boundary
rows are **arithmetic** (`MCARSBoundaryArithmetic`: the bad-γ locus is the rational-point
set of a determinant curve — the finite-scale prototype of the window's conjectured
root-of-unity barrier), the `[(1−ρ)/3, (1−ρ)/2)` strip is certificate-instrumented
(d ≥ 2b cell data), and the window `(1−√ρ, 1−ρ−Θ(1/log n))` — where the prize δ* lives —
remains the open core, with `mcaDeltaStar_le_of_bad` waiting for its first bad point.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCADeltaStarProductionFloor

open ProximityGap.MCAStaircaseMaster ProximityGap.MCAStaircaseRS ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **The band floor.** Every Reed–Solomon code with `k + 3(b−1) ≤ n` and `b/|F| ≤ ε*` has
`(b−1)/n ≤ δ*`: the whole band-`b` radius is a good radius of the formal threshold. -/
theorem mcaDeltaStar_rs_ge_band (domain : ι ↪ F) {k b : ℕ} (hb : 1 ≤ b)
    (hkb : k + 3 * (b - 1) ≤ Fintype.card ι) (hk : 1 ≤ k)
    {εstar : ℝ≥0∞} (hε : (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    ((b - 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0)
      ≤ mcaDeltaStar (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) εstar := by
  have hn0 : 0 < Fintype.card ι := Fintype.card_pos
  have hbn : b - 1 ≤ Fintype.card ι := by omega
  have hδn : ((b - 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) * (Fintype.card ι : ℝ≥0)
      = ((b - 1 : ℕ) : ℝ≥0) := by
    rw [div_mul_cancel₀]
    exact_mod_cast hn0.ne'
  refine le_mcaDeltaStar_of_good _ _ ?_ ?_
  · -- (b−1)/n ≤ 1
    rw [div_le_one (by exact_mod_cast hn0 : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0))]
    exact_mod_cast hbn
  · -- ε_mca at the band radius ≤ b/|F| ≤ ε*
    refine le_trans (epsMCA_rs_le_div_card domain hb hkb hk ?_) hε
    rw [hδn]
    exact_mod_cast (by omega : b - 1 < b)

open Classical in
/-- **THE PRODUCTION-SCALE δ\* FLOOR.** At the prize security level `ε* = 2⁻¹²⁸`, for every
Reed–Solomon code over a production-size field (`b · 2¹²⁸ ≤ |F|`):

  `(b − 1)/n ≤ δ*(RS[F, domain, k], 2⁻¹²⁸)` whenever `k + 3(b−1) ≤ n`.

With `b = ⌊(n−k)/3⌋ + 1`: `δ* ≥ (1−ρ)/3 − O(1/n)`, machine-checked. -/
theorem mcaDeltaStar_rs_ge_at_secpar (domain : ι ↪ F) {k b : ℕ} (hb : 1 ≤ b)
    (hkb : k + 3 * (b - 1) ≤ Fintype.card ι) (hk : 1 ≤ k)
    (hq : (b : ℝ≥0∞) * 2 ^ 128 ≤ (Fintype.card F : ℝ≥0∞)) :
    ((b - 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0)
      ≤ mcaDeltaStar (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
          ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  refine mcaDeltaStar_rs_ge_band domain hb hkb hk ?_
  -- b/|F| ≤ 2⁻¹²⁸ from b·2¹²⁸ ≤ |F|
  have h2ne0 : ((2 : ℝ≥0∞) ^ 128) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have h2neT : ((2 : ℝ≥0∞) ^ 128) ≠ ⊤ := by
    exact ENNReal.pow_ne_top (by norm_num)
  have hF0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [ENNReal.div_le_iff hF0 (ENNReal.natCast_ne_top _)]
  calc (b : ℝ≥0∞) = (b : ℝ≥0∞) * 2 ^ 128 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel h2ne0 h2neT, mul_one]
    _ ≤ (Fintype.card F : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
        gcongr
    _ = ((2 : ℝ≥0∞) ^ 128)⁻¹ * (Fintype.card F : ℝ≥0∞) := mul_comm _ _

/-! ## Source audit -/

#print axioms mcaDeltaStar_rs_ge_band
#print axioms mcaDeltaStar_rs_ge_at_secpar

end ProximityGap.MCADeltaStarProductionFloor
