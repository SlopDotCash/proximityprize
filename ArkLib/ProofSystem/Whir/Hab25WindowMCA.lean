/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MCAPairSeam
import ArkLib.Data.CodingTheory.ProximityGap.Hab25WindowCount
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ConjectureGlue

/-!
# The unconditional WHIR pair-generator MCA on the unique-decoding window

The first **unconditional** instance of the #302 Johnson mutual-correlated-agreement
chain: on the window `2n + 2^m ≤ 3·⌈B*·n⌉` (i.e. `B* ⪆ 2/3`), the affine-line power
generator has mutual correlated agreement with the WHIR conjecture's **exact pair error**
`errStar δ = 2^{2m} / (|F|·(2·min(1−√ρ−δ, √ρ/20))⁷)` — no capture hypothesis, no numeric
side condition, nothing.

Composition: `johnsonNumericBound_of_window'` (the residual holds outright on the window,
for **every** `η` — the numeric edge was proven `η`-free) is instantiated **per-`δ`** at
`η := μ(δ) = min(1−√ρ−δ, √ρ/20)`, where `johnsonBoundReal ≤ errStar` is the proven
`Hab25ConjectureGlue.johnsonBoundReal_le_errStar_real`; the per-`δ` chain feeds the
`epsMCA` seam directly (the fixed-`η` `Hab25WhirBridge` interface cannot express a
`δ`-dependent `η`, the seam can).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Classical in
/-- **The unconditional WHIR pair-generator MCA on the unique-decoding window.** For
`B* ⪆ 2/3` (the window inequality `2n + 2^m ≤ 3·⌈B*·n⌉`) and `√ρ ≤ B*`, the affine-line
power generator has mutual correlated agreement with the conjecture's exact pair error —
with no remaining hypotheses. -/
theorem hasMutualCorrAgreement_genRSC_pair_of_window
    (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (BStar : ℝ) (hB : 0 ≤ BStar)
    (hkn : 2 ^ m + 1 ≤ Fintype.card ι)
    (hrB : Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) ≤ BStar)
    (hwin : 2 * Fintype.card ι + 2 ^ m ≤
      3 * ⌈Real.toNNReal BStar * (Fintype.card ι : ℝ≥0)⌉₊) :
    haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin 2) φ m exp).hℓ
    hasMutualCorrAgreement (RSGenerator.genRSC (Fin 2) φ m exp) BStar
      (fun δr => ENNReal.ofReal ((2 ^ (2 * m) : ℝ) /
        ((Fintype.card F : ℝ) *
          (2 * min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - δr)
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)) ^ 7))) := by
  refine hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le φ m exp hexp0 hexp1
    BStar hB _ ?_
  intro δ h1 h2
  -- the radius is admissible for the conjecture comparison
  have hδB : (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) :=
    lt_of_lt_of_le h2 (by linarith)
  -- the window holds at `δ`: `B* ≤ 1 − δ` and the ceiling is monotone
  have hδ1 : δ ≤ 1 := by
    have hδR : (δ : ℝ) ≤ 1 := by linarith
    exact_mod_cast hδR
  have hmono : Real.toNNReal BStar ≤ 1 - δ := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_sub hδ1, NNReal.coe_one]
    linarith
  have hwinδ : 2 * Fintype.card ι + 2 ^ m ≤
      3 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ := by
    refine le_trans hwin (Nat.mul_le_mul_left 3 (Nat.ceil_le_ceil ?_))
    exact mul_le_mul_left hmono _
  -- the per-`δ` Johnson numeric residual, at `η := μ(δ)`
  have hJNB := johnsonNumericBound_of_window' (F₀ := F) (ι₀ := ι) φ (2 ^ m)
    (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
      (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal δ
    (Nat.two_pow_pos m) hkn hwinδ
  -- the proven `johnsonBoundReal ≤ errStar` comparison at that `η`
  have hglue := Hab25JohnsonEndgame.johnsonBoundReal_le_errStar_real φ m
    (by omega) δ hδB
  exact le_trans hJNB (ENNReal.ofReal_le_ofReal hglue)

end MutualCorrAgreement

/-! ## Axiom audit — kernel-clean. -/
#print axioms MutualCorrAgreement.hasMutualCorrAgreement_genRSC_pair_of_window
