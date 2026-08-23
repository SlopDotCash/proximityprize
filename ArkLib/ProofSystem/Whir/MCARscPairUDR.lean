/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MutualCorrAgreement
import ArkLib.ProofSystem.Whir.MCACurveSeam
import ArkLib.Data.CodingTheory.ProximityGap.MCACurveEvent
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDRBound
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ConjectureGlue

/-!
# Pair-generator mutual correlated agreement for Reed–Solomon, below the unique-decoding radius

This file discharges `mca_rsc` (`MutualCorrAgreement.lean`) for the pair power generator
(`parℓ = Fin 2`, exponents `(0, 1)`, affine-line combiner `(1, γ)`) in the
**unique-decoding regime**: the Corollary 4.11 bound `(B*, errStar)` with
`B* = (1 + ρ)/2` and `errStar = (parℓ − 1)·2^m / (ρ·|F|)` holds verbatim for any smooth
Reed–Solomon code `RS[F, φ, 2^m]` with `2^m ≤ |ι|`.

* `mca_rsc_pair_holds` — the literal `mca_rsc α φ m (Fin 2) exp` with the mild hypotheses
  `2^m ≤ |ι|` and `exp j = j`.

The proof composes already-proven, axiom-clean bricks:

* `hasMutualCorrAgreement_genRSC_pair_of_epsMCACurve_le` (`MCACurveSeam.lean`) reduces the
  generator MCA to a per-`δ` curve-error bound `ε_mcaCurve(C, 2, δ) ≤ errStar δ` on the
  admissible range `0 < δ < 1 − B*`;
* `epsMCACurve_two_eq_epsMCA` (`MCACurveEvent.lean`) identifies the `L = 2` curve error with
  the affine-line error `ε_mca`;
* `epsMCA_rs_udr_le_full` (`MCAUDRBound.lean`) bounds `ε_mca(RS[F, φ, 2^m], δ) ≤ |ι|/|F|`
  below the unique-decoding radius, in the regime `2(|ι| − ⌈(1−δ)|ι|⌉) < |ι| − 2^m + 1`.

The arithmetic glue: the rate is `ρ = 2^m/|ι|` (`rate_smoothCode_coe`), so the claimed
`errStar = 1·2^m/(ρ·|F|)` equals exactly `|ι|/|F|`, matching the `ε_mca` bound; the
admissible range `δ < 1 − (1+ρ)/2 = (1−ρ)/2` is the relative unique-decoding radius
(`relativeUniqueDecodingRadius_RS_eq'`), and it forces the integer regime via
`⌈(1−δ)|ι|⌉ ≥ (1−δ)|ι|` together with `2δ|ι| < |ι| − 2^m`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace MutualCorrAgreement

open NNReal Generator ReedSolomon
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Corollary 4.11 in the unique-decoding regime.** The pair power generator
`genRSC (Fin 2) φ m exp` (exponents `(0, 1)`, affine-line combiner `(1, γ)`) is a proximity
generator with mutual correlated agreement for every smooth Reed–Solomon code
`RS[F, φ, 2^m]` with `2^m ≤ |ι|`, with the proximity bounds
`B* = (1 + ρ)/2` (the relative unique-decoding radius complement) and
`errStar = (parℓ − 1)·2^m / (ρ·|F|) = |ι|/|F|`, where `ρ = 2^m/|ι|`.

This is `mca_rsc` verbatim at `parℓ = Fin 2`, established below the unique-decoding radius by
composing the curve seam, the `L = 2` curve↔line error identity, and the from-scratch
unique-decoding MCA bound `epsMCA_rs_udr_le_full`. -/
theorem mca_rsc_pair_holds
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι) (hexp : ∀ j : Fin 2, exp j = (j : ℕ)) :
    mca_rsc α φ m (Fin 2) exp := by
  classical
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  -- the rate value `ρ = 2^m / n`
  have hrate : (RSGenerator.genRSC (Fin 2) φ m exp).rate
      = (2 ^ m : ℝ) / (Fintype.card ι : ℝ) := by
    have h := rate_smoothCode_coe (F₀ := F) (ι₀ := ι) φ m hk
    simpa [RSGenerator.genRSC] using h
  set n := Fintype.card ι with hndef
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hcFpos : 0 < Fintype.card F := Fintype.card_pos
  have hcFR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hcFpos
  unfold mca_rsc
  apply hasMutualCorrAgreement_genRSC_pair_of_epsMCACurve_le φ m exp hexp
  · -- `0 ≤ B* = (1 + ρ)/2`
    rw [hrate]
    have : (0 : ℝ) ≤ (2 ^ m : ℝ) / (n : ℝ) := by positivity
    linarith
  · -- the curve-error bound `ε_mcaCurve(C, 2, δ) ≤ errStar δ`
    intro δ hδ0 hδB
    rw [hrate] at hδB
    -- `δ < (1 − ρ)/2`, the relative unique-decoding radius
    have hδB' : (δ : ℝ) < (1 - (2 ^ m : ℝ) / (n : ℝ)) / 2 := by linarith [hδB]
    have hδ1 : (δ : ℝ) < 1 := by
      have h0 : (0:ℝ) ≤ (2 ^ m : ℝ) / (n : ℝ) := by positivity
      linarith [hδB']
    -- (1) the relative-UDR side condition
    have hδudr : δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
        (C := ReedSolomon.code φ (2 ^ m)) := by
      rw [relativeUniqueDecodingRadius_RS_eq' (α := φ) (n := 2 ^ m) hk]
      rw [← NNReal.coe_le_coe]
      push_cast
      rw [NNReal.coe_sub (by
        rw [← NNReal.coe_le_coe]; push_cast
        rw [div_le_one hnR]; exact_mod_cast hk)]
      push_cast
      linarith [hδB']
    -- (2) the integer regime `2(n − ⌈(1−δ)n⌉) < n − 2^m + 1`
    have hreg : 2 * (n - ⌈(1 - δ) * (n : ℝ≥0)⌉₊) < n - 2 ^ m + 1 := by
      set t : ℕ := ⌈(1 - δ) * (n : ℝ≥0)⌉₊ with htdef
      -- `t ≥ (1 − δ)·n` over the reals
      have htge : ((1 : ℝ) - (δ : ℝ)) * (n : ℝ) ≤ (t : ℝ) := by
        have hceil : ((1 - δ) * (n : ℝ≥0) : ℝ≥0) ≤ (t : ℝ≥0) := Nat.le_ceil _
        have hc := (NNReal.coe_le_coe.mpr hceil)
        push_cast at hc
        rw [NNReal.coe_sub (by exact_mod_cast hδ1.le)] at hc
        push_cast at hc
        convert hc using 2
      -- `2δn < n − 2^m` from `δ < (1 − ρ)/2`
      have hkey : 2 * (δ : ℝ) * (n : ℝ) < (n : ℝ) - (2 ^ m : ℝ) := by
        have h2 : (δ : ℝ) * 2 < 1 - (2 ^ m : ℝ) / (n : ℝ) := by linarith [hδB']
        have hm := mul_lt_mul_of_pos_right h2 hnR
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hnR)] at hm
        linarith [hm]
      -- `n − t ≤ δn` over the reals (Nat subtraction floors at `0`)
      have hnt : ((n - t : ℕ) : ℝ) ≤ (δ : ℝ) * (n : ℝ) := by
        by_cases hle : t ≤ n
        · rw [Nat.cast_sub hle]; nlinarith [htge]
        · rw [not_le] at hle
          rw [Nat.sub_eq_zero_of_le hle.le]
          have hpos : (0:ℝ) ≤ (δ:ℝ) * (n:ℝ) := by positivity
          simpa using hpos
      have h2nt : (2 * (n - t : ℕ) : ℝ) < ((n : ℝ) - (2 ^ m : ℝ)) := by
        nlinarith [hkey, hnt]
      have hnm : ((n - 2 ^ m : ℕ) : ℝ) = (n : ℝ) - (2 ^ m : ℝ) := by
        rw [Nat.cast_sub hk]; push_cast; ring
      have hfin : (2 * (n - t) : ℕ) < (n - 2 ^ m : ℕ) + 1 := by
        have hlt : ((2 * (n - t) : ℕ) : ℝ) < ((n - 2 ^ m : ℕ) : ℝ) + 1 := by
          rw [hnm]; push_cast at h2nt ⊢; linarith [h2nt]
        exact_mod_cast hlt
      omega
    -- chain: `ε_mcaCurve(C, 2, δ) = ε_mca(C, δ) ≤ |ι|/|F| = errStar δ`
    rw [show ((RSGenerator.genRSC (Fin 2) φ m exp).C : Set (ι → F))
        = (ReedSolomon.code φ (2 ^ m) : Set (ι → F)) from rfl]
    rw [ProximityGap.epsMCACurve_two_eq_epsMCA (F := F) (A := F)]
    refine le_trans
      (ProximityGap.UDRwire.epsMCA_rs_udr_le_full φ (2 ^ m) hk δ hδudr hreg) ?_
    -- `errStar = (2 − 1)·2^m/(ρ·|F|) = n/|F|`
    rw [hrate]
    have hval : (((Fintype.card (Fin 2) : ℝ)) - 1)
          * ((2 ^ m : ℝ) / (((2 ^ m : ℝ) / (n : ℝ)) * (Fintype.card F : ℝ)))
        = (n : ℝ) / (Fintype.card F : ℝ) := by
      have hmmR : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
      simp only [Fintype.card_fin]
      field_simp
      ring
    rw [hval, ENNReal.ofReal_div_of_pos hcFR, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]

end MutualCorrAgreement

/-! ## Axiom audit — all kernel-clean. -/
#print axioms MutualCorrAgreement.mca_rsc_pair_holds
