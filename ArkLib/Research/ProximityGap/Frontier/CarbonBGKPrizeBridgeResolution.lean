/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineIncidenceSpectral
import ArkLib.Data.CodingTheory.ProximityGap.IncidenceDeviationCharSum
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import ArkLib.Research.ProximityGap.DesignatedPrimeJohnson
import ArkLib.Research.ProximityGap.Frontier.SmoothTwoHeadProduction
import Mathlib.InformationTheory.Hamming

/-!
# Resolution of the BGK-to-Prize Bridge and Normalized Syndrome-Space Spectral Laws

This module resolves three coupled questions on the analytic-to-coding bridge behind
`ArkLib.Research.ProximityGap.Frontier._PrizeFloorOfBGK`,
`ArkLib.Data.CodingTheory.ProximityGap.IncidenceDeviationCharSum`, and
`ArkLib.Research.ProximityGap.PROXIMITY_PRIZE_WORKBENCH`:

1. **Exact normalized `(n - k)`-dimensional syndrome-space spectral bridge (eliminating `q * B`):**
   `IncidenceDeviationCharSum` worked in the 1D model `V = F` without dividing by `|V|`,
   producing a vacuous `q * B` deviation factor. Over an arbitrary finite `F`-vector space `V`
   (such as the `(n - k)`-dimensional syndrome space `F^{n - k}`), we prove that for any
   `s₁ ≠ 0` the annihilator hyperplane `s₁^⊥` has exact size `|V| / |F|`
   (`card_directionPerp_mul_eq`), so the `|F| / |V|` Fourier normalization cancels
   `#(s₁^⊥ \ {0}) = |V| / |F| - 1` to `(1 - |F| / |V|) * B ≤ B`
   (`syndromeLineIncidence_abs_sub_mean_le`), welded directly to `FarFromCode` MCA bad-scalar
   counts (`far_mcaBadCount_eq_syndromeLineIncidence`, `far_mcaBadCount_abs_sub_mean_le`).
   Conversely, Parseval (`syndrome_charSum_sup_sq_ge_parseval`) proves that any phase-forgetting
   uniform character bound `B` over `V̂ \ {0}` obeys `(|V| - 1) * B^2 ≥ |S| * (|V| - |S|)`,
   explaining why phase cancellation across `s₁^⊥ \ {0}` is essential once `|S| ≫ n^2`.

2. **Exact refutation of the unguarded Workbench residual `WorstCaseIncidenceBound`:**
   In `PROXIMITY_PRIZE_WORKBENCH` (§3), `WorstCaseIncidenceBound H b B` omits `FarFromCode` and
   quantifies over all `s₁ ≠ 0`. For every nonzero parity-check map `H ≠ 0`, every radius `b ≥ 1`,
   and every budget `B < |F|`, taking `s₀ = 0` and `s₁ = H (Pi.single i 1) ≠ 0` yields `|F|`
   distinct weight-`≤ 1` witnesses `γ • Pi.single i 1`, refuting `WorstCaseIncidenceBound H b B`.

3. **Unconditional refutation of the linear-budget BGK-to-above-Johnson upgrade (`_PrizeFloorOfBGK`)
   and exact MCA-vs-List separation above Johnson:**
   `_PrizeFloorOfBGK` posited that proving `WorstCaseIncompleteSumBound ψ G M` on `μ_n` would
   upgrade to above-Johnson `WorstCaseIncidenceBounded C δ B` at the prize budget `B = ⌊p ε*⌋`.
   Combining `OpenCoreConditionalPin.worstCaseIncidence_pin` with `DesignatedPrimeJohnson` and
   `SmoothTwoHeadProduction`, we prove unconditionally that:
   * At `P₁` (`B = 2^30 = n`), `WorstCaseIncidenceBounded` is **false** at every above-Johnson
     radius `δ ∈ [johnson k, 1]` across **all four prize rates** `{1/2, 1/4, 1/8, 1/16}`,
     regardless of whether `WorstCaseIncompleteSumBound ψ G M` holds (even for `M = 0`).
   * At `P₂` (`B = 2^31 = 2n`) and rate `1/8` (`k = 2^27`), at the explicit above-Johnson error
     radius `e = 694,116,763`, **Grand List Decoding succeeds within budget**
     (`≤ 1,660,990,722 ≤ 2^31`), whereas **Grand MCA `WorstCaseIncidenceBounded` fails** at the
     exact same code, prime, radius, and budget—proving unconditionally that worst-case list-size
     bounds do not transfer linearly to line-MCA incidence bounds at `O(n)` budgets.
   * Across **every** smooth `2^30`-element domain over **every** finite field `F` with
     `2^30 ≤ |F| / 2^128 ≤ 1,163,220,311` (covering the entire `[2^158, 2^158 + 2^144]` split-prime
     sixth-moment window), `WorstCaseIncidenceBounded` fails above Johnson at rates `1/8` and
     `1/16`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonBGKPrizeBridgeResolution

open Finset
open scoped NNReal ENNReal
open _root_.ProximityGap
open _root_.ProximityGap.MCAThresholdLedger
open _root_.ProximityGap.OpenCoreConditionalPin
open _root_.ProximityGap.FarCosetExplosion
open ArkLib.ProximityGap.LineIncidenceSpectral
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ProximityPrize

/-! ## §1. Normalized `(n - k)`-dimensional syndrome-space spectral bridge -/

/-- Additive characters of the `F`-module `V` annihilating the line direction `s₁`. -/
noncomputable def directionPerp (F : Type*) [Field F] {V : Type*}
    [AddCommGroup V] [Fintype V] [Module F V] (s₁ : V) : Finset (AddChar V ℂ) :=
  Finset.univ.filter (fun ψ : AddChar V ℂ => directionChar (F := F) ψ s₁ = 0)

/-- Number of scalars `γ : F` for which the affine syndrome line `s₀ + γ • s₁` meets `S`. -/
def syndromeLineIncidence (F : Type*) [Field F] [Fintype F] {V : Type*}
    [AddCommGroup V] [DecidableEq V] [Module F V] (S : Finset V) (s₀ s₁ : V) : ℕ :=
  (Finset.univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card

/-- The trivial character always lies in the annihilator hyperplane `directionPerp F s₁`. -/
theorem zero_mem_directionPerp (F : Type*) [Field F] {V : Type*}
    [AddCommGroup V] [Fintype V] [Module F V] (s₁ : V) :
    (0 : AddChar V ℂ) ∈ directionPerp F s₁ := by
  simp only [directionPerp, Finset.mem_filter, Finset.mem_univ, true_and]
  ext γ
  simp only [directionChar_apply, AddChar.zero_apply]

/-- **Exact annihilator-hyperplane cardinality.** For any nonzero syndrome direction `s₁ ≠ 0` in a
finite `F`-vector space `V`, `#(s₁^⊥) * |F| = |V|`. Proved directly by specializing
`lineIncidence_spectral` to `S = {0}` and `s₀ = 0`. -/
theorem card_directionPerp_mul_eq {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Fintype V] [DecidableEq V] [Module F V]
    {s₁ : V} (hs₁ : s₁ ≠ 0) :
    (directionPerp F s₁).card * Fintype.card F = Fintype.card V := by
  classical
  have hspec := lineIncidence_spectral (F := F) ({(0 : V)} : Finset V) 0 s₁
  have hlhs : Finset.univ.filter (fun γ : F => (0 : V) + γ • s₁ ∈ ({(0 : V)} : Finset V))
      = {(0 : F)} := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_add,
      Finset.mem_singleton, smul_eq_zero, hs₁, or_false]
  rw [hlhs, Finset.card_singleton, Nat.cast_one, one_mul] at hspec
  have hrhs : (∑ ψ : AddChar V ℂ,
      (if directionChar (F := F) ψ s₁ = 0
        then ∑ s ∈ ({(0 : V)} : Finset V), ψ ((0 : V) - s) else 0))
      = ((directionPerp F s₁).card : ℂ) := by
    have h1 : ∀ ψ : AddChar V ℂ,
        (∑ s ∈ ({(0 : V)} : Finset V), ψ ((0 : V) - s)) = 1 := by
      intro ψ
      rw [Finset.sum_singleton, sub_self, AddChar.map_zero_eq_one]
    simp_rw [h1]
    rw [directionPerp, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hrhs, mul_comm] at hspec
  exact_mod_cast hspec.symm

/-- Inversion preserves the punctured annihilator hyperplane `(directionPerp F s₁).erase 0`. -/
theorem inv_mem_erase_zero_directionPerp {F V : Type*} [Field F]
    [AddCommGroup V] [Fintype V] [Module F V] {s₁ : V}
    {ψ : AddChar V ℂ} (hψ : ψ ∈ (directionPerp F s₁).erase 0) :
    ψ⁻¹ ∈ (directionPerp F s₁).erase 0 := by
  obtain ⟨hψ0, hdir⟩ := Finset.mem_erase.mp hψ
  have hdir' : directionChar (F := F) ψ s₁ = 0 := (Finset.mem_filter.mp hdir).2
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hinv
    apply hψ0
    ext x
    have hx := congrFun (congrArg DFunLike.coe hinv) (-x)
    simpa only [AddChar.inv_apply, neg_neg, AddChar.zero_apply] using hx
  · simp only [directionPerp, Finset.mem_filter, Finset.mem_univ, true_and]
    ext γ
    have hγ := congrFun (congrArg DFunLike.coe hdir') (-γ)
    simpa only [directionChar_apply, AddChar.inv_apply, neg_smul, AddChar.zero_apply] using hγ

/-- **Exact spectral deviation identity on `V`.** Isolates the first-moment term `|F| * |S|` at
`ψ = 0` from the punctured `s₁^⊥ \ {0}` error sum. -/
theorem syndromeLineIncidence_mul_sub_spectral {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Fintype V] [DecidableEq V] [Module F V]
    (S : Finset V) (s₀ s₁ : V) :
    (syndromeLineIncidence F S s₀ s₁ : ℂ) * (Fintype.card V : ℂ)
      - (Fintype.card F : ℂ) * (S.card : ℂ)
      = (Fintype.card F : ℂ) *
          ∑ ψ ∈ (directionPerp F s₁).erase 0, ψ s₀ * ∑ s ∈ S, ψ⁻¹ s := by
  have hspec := lineIncidence_spectral (F := F) S s₀ s₁
  change (syndromeLineIncidence F S s₀ s₁ : ℂ) * (Fintype.card V : ℂ) = _ at hspec
  rw [← Finset.sum_filter (p := fun ψ : AddChar V ℂ => directionChar (F := F) ψ s₁ = 0)
    (f := fun ψ => ∑ s ∈ S, ψ (s₀ - s))] at hspec
  change (syndromeLineIncidence F S s₀ s₁ : ℂ) * (Fintype.card V : ℂ) =
    (Fintype.card F : ℂ) * ∑ ψ ∈ directionPerp F s₁, ∑ s ∈ S, ψ (s₀ - s) at hspec
  rw [← Finset.add_sum_erase _ _ (zero_mem_directionPerp F s₁)] at hspec
  have hzero : (∑ s ∈ S, (0 : AddChar V ℂ) (s₀ - s)) = (S.card : ℂ) := by
    simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hzero, mul_add] at hspec
  have hshift : ∀ ψ ∈ (directionPerp F s₁).erase 0,
      (∑ s ∈ S, ψ (s₀ - s)) = ψ s₀ * ∑ s ∈ S, ψ⁻¹ s := by
    intro ψ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.inv_apply]
  rw [Finset.sum_congr rfl hshift] at hspec
  linear_combination hspec

/-- **Normalized `(n - k)`-dimensional hyperplane triangle bound (no `q`-loss).**
For `s₁ ≠ 0`, dividing by `|V|` cancels `#(s₁^⊥ \ {0}) = |V| / |F| - 1` against `|F| / |V|`,
giving `|I - |F| * |S| / |V|| ≤ (1 - |F| / |V|) * B` with **no factor of `|F|`** on `B`
(resolving the 1D normalization artifact noted in `IncidenceDeviationCharSum`). -/
theorem syndromeLineIncidence_abs_sub_mean_le {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Fintype V] [DecidableEq V] [Module F V]
    (S : Finset V) (s₀ : V) {s₁ : V} (hs₁ : s₁ ≠ 0) {B : ℝ}
    (hB : ∀ ψ ∈ (directionPerp F s₁).erase 0, ‖∑ s ∈ S, ψ s‖ ≤ B) :
    |(syndromeLineIncidence F S s₀ s₁ : ℝ)
        - (Fintype.card F : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ)|
      ≤ (1 - (Fintype.card F : ℝ) / (Fintype.card V : ℝ)) * B := by
  have hvpos : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hid := congrArg norm (syndromeLineIncidence_mul_sub_spectral (F := F) S s₀ s₁)
  have hlhs : ‖(syndromeLineIncidence F S s₀ s₁ : ℂ) * (Fintype.card V : ℂ)
      - (Fintype.card F : ℂ) * (S.card : ℂ)‖
      = |(syndromeLineIncidence F S s₀ s₁ : ℝ) * (Fintype.card V : ℝ)
          - (Fintype.card F : ℝ) * (S.card : ℝ)| := by
    rw [show (syndromeLineIncidence F S s₀ s₁ : ℂ) * (Fintype.card V : ℂ)
          - (Fintype.card F : ℂ) * (S.card : ℂ)
        = ((((syndromeLineIncidence F S s₀ s₁ : ℝ) * (Fintype.card V : ℝ)
            - (Fintype.card F : ℝ) * (S.card : ℝ)) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hnormF : ‖(Fintype.card F : ℂ)‖ = (Fintype.card F : ℝ) := by
    rw [show (Fintype.card F : ℂ) = (((Fintype.card F : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hlhs, norm_mul, hnormF] at hid
  have hsum : ‖∑ ψ ∈ (directionPerp F s₁).erase 0, ψ s₀ * ∑ s ∈ S, ψ⁻¹ s‖
      ≤ (((directionPerp F s₁).erase 0).card : ℝ) * B := by
    calc ‖∑ ψ ∈ (directionPerp F s₁).erase 0, ψ s₀ * ∑ s ∈ S, ψ⁻¹ s‖
        ≤ ∑ ψ ∈ (directionPerp F s₁).erase 0, ‖ψ s₀ * ∑ s ∈ S, ψ⁻¹ s‖ := norm_sum_le _ _
      _ ≤ ∑ _ψ ∈ (directionPerp F s₁).erase 0, B := by
          refine Finset.sum_le_sum (fun ψ hψ => ?_)
          rw [norm_mul, ψ.norm_apply s₀, one_mul]
          exact hB ψ⁻¹ (inv_mem_erase_zero_directionPerp hψ)
      _ = (((directionPerp F s₁).erase 0).card : ℝ) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_nat : ((directionPerp F s₁).erase 0).card + 1 = (directionPerp F s₁).card :=
    Finset.card_erase_add_one (zero_mem_directionPerp F s₁)
  have hmul_nat := card_directionPerp_mul_eq (F := F) hs₁
  have hcard_real : (Fintype.card F : ℝ) * (((directionPerp F s₁).erase 0).card : ℝ)
      = (Fintype.card V : ℝ) - (Fintype.card F : ℝ) := by
    have h1 : (((directionPerp F s₁).erase 0).card : ℝ) + 1 = ((directionPerp F s₁).card : ℝ) := by
      exact_mod_cast hcard_nat
    have h2 : ((directionPerp F s₁).card : ℝ) * (Fintype.card F : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast hmul_nat
    linear_combination (Fintype.card F : ℝ) * h1 + h2
  have hunnorm : |(syndromeLineIncidence F S s₀ s₁ : ℝ) * (Fintype.card V : ℝ)
      - (Fintype.card F : ℝ) * (S.card : ℝ)|
      ≤ ((Fintype.card V : ℝ) - (Fintype.card F : ℝ)) * B := by
    calc |(syndromeLineIncidence F S s₀ s₁ : ℝ) * (Fintype.card V : ℝ)
            - (Fintype.card F : ℝ) * (S.card : ℝ)|
        = (Fintype.card F : ℝ) *
            ‖∑ ψ ∈ (directionPerp F s₁).erase 0, ψ s₀ * ∑ s ∈ S, ψ⁻¹ s‖ := hid
      _ ≤ (Fintype.card F : ℝ) * ((((directionPerp F s₁).erase 0).card : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
      _ = ((Fintype.card F : ℝ) * (((directionPerp F s₁).erase 0).card : ℝ)) * B := by ring
      _ = ((Fintype.card V : ℝ) - (Fintype.card F : ℝ)) * B := by rw [hcard_real]
  have hdiv := div_le_div_of_nonneg_right hunnorm hvpos.le
  have hquot_lhs : ((syndromeLineIncidence F S s₀ s₁ : ℝ) * (Fintype.card V : ℝ)
      - (Fintype.card F : ℝ) * (S.card : ℝ)) / (Fintype.card V : ℝ)
      = (syndromeLineIncidence F S s₀ s₁ : ℝ)
        - (Fintype.card F : ℝ) * (S.card : ℝ) / (Fintype.card V : ℝ) := by
    rw [sub_div, mul_div_cancel_right₀ _ hvpos.ne']
  have hquot_rhs : (((Fintype.card V : ℝ) - (Fintype.card F : ℝ)) * B) / (Fintype.card V : ℝ)
      = (1 - (Fintype.card F : ℝ) / (Fintype.card V : ℝ)) * B := by
    rw [mul_div_right_comm, sub_div, div_self hvpos.ne']
  have habs_div : |((syndromeLineIncidence F S s₀ s₁ : ℝ) * (Fintype.card V : ℝ)
      - (Fintype.card F : ℝ) * (S.card : ℝ))| / (Fintype.card V : ℝ) =
      |((syndromeLineIncidence F S s₀ s₁ : ℝ) * (Fintype.card V : ℝ)
        - (Fintype.card F : ℝ) * (S.card : ℝ)) / (Fintype.card V : ℝ)| := by
    rw [abs_div, abs_of_pos hvpos]
  rwa [habs_div, hquot_lhs, hquot_rhs] at hdiv

/-- **Parseval lower bound on any uniform syndrome character-sum bound.**
Any `B ≥ 0` bounding `‖∑_{s ∈ S} ψ s‖ ≤ B` across all nontrivial characters `ψ ≠ 0` of `V`
must satisfy `|S| * (|V| - |S|) ≤ (|V| - 1) * B^2`. Thus in codimension `n - k ≥ 2` where the
syndrome ball `S` has size `|S| ≈ n * |V| / |F| ≫ n^2`, no phase-forgetting bound on `V` can
make `B = O(n)`. -/
theorem syndrome_charSum_sup_sq_ge_parseval {V : Type*} [AddCommGroup V] [Fintype V]
    [DecidableEq V] (S : Finset V) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ψ : AddChar V ℂ, ψ ≠ 0 → ‖∑ s ∈ S, ψ s‖ ≤ B) :
    (S.card : ℝ) * ((Fintype.card V : ℝ) - (S.card : ℝ))
      ≤ ((Fintype.card V : ℝ) - 1) * B ^ 2 := by
  classical
  have hl2 := charSum_l2_pairing S
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : AddChar V ℂ))] at hl2
  have hz : (∑ s ∈ S, (0 : AddChar V ℂ) s) * (∑ t ∈ S, (0 : AddChar V ℂ)⁻¹ t)
      = (S.card : ℂ) * (S.card : ℂ) := by
    have hinv : (0 : AddChar V ℂ)⁻¹ = 0 := by
      ext x
      simp only [AddChar.inv_apply, AddChar.zero_apply]
    rw [hinv]
    simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hz] at hl2
  have hsub : (∑ ψ ∈ Finset.univ.erase (0 : AddChar V ℂ),
      (∑ s ∈ S, ψ s) * (∑ t ∈ S, ψ⁻¹ t))
      = (Fintype.card V : ℂ) * (S.card : ℂ) - (S.card : ℂ) * (S.card : ℂ) := by
    linear_combination hl2
  have hnorm := congrArg norm hsub
  have hS_le : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast S.card_le_univ
  have hrhs : ‖(Fintype.card V : ℂ) * (S.card : ℂ) - (S.card : ℂ) * (S.card : ℂ)‖
      = (S.card : ℝ) * ((Fintype.card V : ℝ) - (S.card : ℝ)) := by
    rw [show (Fintype.card V : ℂ) * (S.card : ℂ) - (S.card : ℂ) * (S.card : ℂ)
        = ((((S.card : ℝ) * ((Fintype.card V : ℝ) - (S.card : ℝ))) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))]
  rw [hrhs] at hnorm
  have hcard_dual : ((Finset.univ.erase (0 : AddChar V ℂ)).card : ℝ)
      = (Fintype.card V : ℝ) - 1 := by
    have hc1 : (Finset.univ.erase (0 : AddChar V ℂ)).card + 1 = Fintype.card (AddChar V ℂ) := by
      simpa only [Finset.card_univ] using
        Finset.card_erase_add_one (Finset.mem_univ (0 : AddChar V ℂ))
    rw [AddChar.card_eq] at hc1
    have hc1' : ((Finset.univ.erase (0 : AddChar V ℂ)).card : ℝ) + 1 = (Fintype.card V : ℝ) := by
      exact_mod_cast hc1
    linarith
  calc (S.card : ℝ) * ((Fintype.card V : ℝ) - (S.card : ℝ))
      = ‖∑ ψ ∈ Finset.univ.erase (0 : AddChar V ℂ),
          (∑ s ∈ S, ψ s) * (∑ t ∈ S, ψ⁻¹ t)‖ := hnorm.symm
    _ ≤ ∑ ψ ∈ Finset.univ.erase (0 : AddChar V ℂ),
          ‖(∑ s ∈ S, ψ s) * (∑ t ∈ S, ψ⁻¹ t)‖ := norm_sum_le _ _
    _ ≤ ∑ _ψ ∈ Finset.univ.erase (0 : AddChar V ℂ), B ^ 2 := by
        refine Finset.sum_le_sum (fun ψ hψ => ?_)
        have hψ0 : ψ ≠ 0 := (Finset.mem_erase.mp hψ).1
        have hinv0 : ψ⁻¹ ≠ 0 := by
          intro h0
          apply hψ0
          ext x
          have hx := congrFun (congrArg DFunLike.coe h0) (-x)
          simpa only [AddChar.inv_apply, neg_neg, AddChar.zero_apply] using hx
        rw [norm_mul, sq]
        exact mul_le_mul (hB ψ hψ0) (hB ψ⁻¹ hinv0) (norm_nonneg _) hB0
    _ = ((Finset.univ.erase (0 : AddChar V ℂ)).card : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card V : ℝ) - 1) * B ^ 2 := by rw [hcard_dual]

open Classical in
/-- The `(n - k)`-dimensional syndrome ball of a parity-check map `H : (ι → F) →ₗ[F] V` at
relative agreement slack `δ`: syndromes of error words vanishing on at least `(1 - δ) |ι|`
coordinates. -/
noncomputable def syndromeBall {ι F V : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup V] [DecidableEq V] [Module F V]
    (H : (ι → F) →ₗ[F] V) (δ : ℝ≥0) : Finset V :=
  (Finset.univ.filter (fun e : ι → F =>
    ((Finset.univ.filter (fun i : ι => e i = 0)).card : ℝ≥0)
      ≥ (1 - δ) * Fintype.card ι)).image H

open Classical in
/-- **Exact geometric identification of far-coset MCA bad-scalar counts with `(n - k)`-dimensional
syndrome-line incidence.** Supplies the missing in-tree identification noted in
`IncidenceDeviationCharSum` for any linear code `LinearMap.ker H`. -/
theorem far_mcaBadCount_eq_syndromeLineIncidence {ι F V : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup V] [DecidableEq V] [Module F V]
    (H : (ι → F) →ₗ[F] V) (δ : ℝ≥0) {u₀ u₁ : ι → F}
    (hfar : FarFromCode (LinearMap.ker H : Set (ι → F)) δ u₁) :
    (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (LinearMap.ker H : Set (ι → F)) δ u₀ u₁ γ)).card
      = syndromeLineIncidence F (syndromeBall H δ) (H u₀) (H u₁) := by
  rw [badScalars_eq_explainable (LinearMap.ker H : Set (ι → F)) δ hfar]
  unfold syndromeLineIncidence syndromeBall
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨S, hS, w, hw, hag⟩
    refine ⟨u₀ + γ • u₁ - w, ?_, ?_⟩
    · have hsub : S ⊆ Finset.univ.filter (fun i : ι => (u₀ + γ • u₁ - w) i = 0) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, sub_eq_zero]
        exact (hag i hi).symm
      exact le_trans hS (Nat.cast_le.mpr (Finset.card_le_card hsub))
    · rw [map_sub, map_add, map_smul, LinearMap.mem_ker.mp hw, sub_zero]
  · rintro ⟨e, he, hHe⟩
    refine ⟨Finset.univ.filter (fun i : ι => e i = 0), he, u₀ + γ • u₁ - e, ?_, ?_⟩
    · change H (u₀ + γ • u₁ - e) = 0
      rw [map_sub, map_add, map_smul, hHe, sub_self]
    · intro i hi
      have hei : e i = 0 := (Finset.mem_filter.mp hi).2
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hei, sub_zero]

open Classical in
/-- **Far-coset MCA spectral deviation law on the `(n - k)`-dimensional syndrome quotient.** -/
theorem far_mcaBadCount_abs_sub_mean_le {ι F V : Type} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup V] [Fintype V] [DecidableEq V] [Module F V]
    (H : (ι → F) →ₗ[F] V) (δ : ℝ≥0) {u₀ u₁ : ι → F}
    (hfar : FarFromCode (LinearMap.ker H : Set (ι → F)) δ u₁)
    (hs₁ : H u₁ ≠ 0) {B : ℝ}
    (hB : ∀ ψ ∈ (directionPerp F (H u₁)).erase 0, ‖∑ s ∈ syndromeBall H δ, ψ s‖ ≤ B) :
    |((Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) (LinearMap.ker H : Set (ι → F)) δ u₀ u₁ γ)).card : ℝ)
        - (Fintype.card F : ℝ) * ((syndromeBall H δ).card : ℝ) / (Fintype.card V : ℝ)|
      ≤ (1 - (Fintype.card F : ℝ) / (Fintype.card V : ℝ)) * B := by
  rw [far_mcaBadCount_eq_syndromeLineIncidence H δ hfar]
  exact syndromeLineIncidence_abs_sub_mean_le (syndromeBall H δ) (H u₀) hs₁ hB

/-! ## §2. Refutation of the unguarded Workbench residual `WorstCaseIncidenceBound` -/

/-- Exact mirror of `ProximityPrize.badScalars` (`PROXIMITY_PRIZE_WORKBENCH.lean:269`). -/
noncomputable def workbenchBadScalars {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ)
    (s₀ s₁ : Fin m → F) : Finset F :=
  Finset.univ.filter (fun γ => ∃ e : Fin n → F, hammingNorm e ≤ b ∧ H e = s₀ + γ • s₁)

/-- Exact mirror of `ProximityPrize.cosetLowWeight` (`PROXIMITY_PRIZE_WORKBENCH.lean:278`). -/
noncomputable def workbenchCosetLowWeight {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ)
    (s₀ s₁ : Fin m → F) : Finset (Fin n → F) :=
  Finset.univ.filter (fun e => hammingNorm e ≤ b ∧ ∃ γ : F, H e = s₀ + γ • s₁)

/-- Exact mirror of `ProximityPrize.WorstCaseIncidenceBound`
(`PROXIMITY_PRIZE_WORKBENCH.lean:351`). -/
def WorkbenchWorstCaseIncidenceBound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b B : ℕ) : Prop :=
  ∀ s₀ s₁ : Fin m → F, s₁ ≠ 0 → (workbenchCosetLowWeight H b s₀ s₁).card ≤ B

private theorem exists_single_ne_zero_of_ne_zero {F : Type*} [Semiring F] [DecidableEq F]
    {n m : ℕ} {H : (Fin n → F) →ₗ[F] (Fin m → F)} (hH : H ≠ 0) :
    ∃ i : Fin n, H (Pi.single i (1 : F)) ≠ 0 := by
  by_contra h
  push Not at h
  apply hH
  apply LinearMap.ext
  intro v
  ext j
  have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : F) : Fin n → F) := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hv, map_sum]
  simp only [map_smul, h, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply, Pi.zero_apply]

private theorem hammingNorm_smul_single_le_one {F : Type*} [Semiring F] [DecidableEq F]
    {n : ℕ} (i : Fin n) (γ : F) :
    hammingNorm (γ • (Pi.single i (1 : F) : Fin n → F)) ≤ 1 := by
  let e : Fin n → F := Pi.single i 1
  change hammingNorm (γ • e) ≤ 1
  refine le_trans hammingNorm_smul_le_hammingNorm ?_
  have hsub : Finset.univ.filter (fun j : Fin n => e j ≠ 0) ⊆ {i} := by
    intro j hj
    have hj0 : e j ≠ 0 := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_singleton]
    by_contra hji
    exact hj0 (Pi.single_eq_of_ne (M := fun _ => F) hji (1 : F))
  exact le_trans (Finset.card_le_card hsub) (le_of_eq (Finset.card_singleton i))

/-- **Every nonzero parity-check map has a weight-`1` syndrome line with `|F|` bad scalars.**
Taking `s₀ = 0` and `s₁ = H (Pi.single i 1) ≠ 0` makes every `γ ∈ F` realized by
`γ • Pi.single i 1` of Hamming weight `≤ 1`. -/
theorem workbench_badScalars_card_eq_card_field {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {n m : ℕ} {H : (Fin n → F) →ₗ[F] (Fin m → F)} (hH : H ≠ 0)
    {b : ℕ} (hb : 1 ≤ b) :
    ∃ s₁ : Fin m → F, s₁ ≠ 0 ∧
      (workbenchBadScalars H b 0 s₁).card = Fintype.card F ∧
      Fintype.card F ≤ (workbenchCosetLowWeight H b 0 s₁).card := by
  classical
  obtain ⟨i, hi⟩ := exists_single_ne_zero_of_ne_zero hH
  let e₀ : Fin n → F := Pi.single i 1
  refine ⟨H e₀, hi, ?_, ?_⟩
  · have hall : workbenchBadScalars H b 0 (H e₀) = Finset.univ := by
      ext γ
      simp only [workbenchBadScalars, Finset.mem_filter, Finset.mem_univ, true_and,
        zero_add, iff_true]
      exact ⟨γ • e₀, le_trans (hammingNorm_smul_single_le_one i γ) hb, map_smul H γ e₀⟩
    rw [hall, Finset.card_univ]
  · have hinj : Function.Injective (fun γ : F => γ • e₀) := by
      intro γ₁ γ₂ heq
      have hval := congrFun heq i
      simpa only [e₀, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] using hval
    have himg : Finset.univ.image (fun γ : F => γ • e₀)
        ⊆ workbenchCosetLowWeight H b 0 (H e₀) := by
      intro w hw
      obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hw
      simp only [workbenchCosetLowWeight, Finset.mem_filter, Finset.mem_univ, true_and, zero_add]
      exact ⟨le_trans (hammingNorm_smul_single_le_one i γ) hb, γ, map_smul H γ e₀⟩
    calc Fintype.card F
        = (Finset.univ.image (fun γ : F => γ • e₀)).card := by
            rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      _ ≤ (workbenchCosetLowWeight H b 0 (H e₀)).card :=
            Finset.card_le_card himg

/-- **Refutation of `WorkbenchWorstCaseIncidenceBound` for every `H ≠ 0`, `b ≥ 1`, `B < |F|`.**
Because `PROXIMITY_PRIZE_WORKBENCH` omits `FarFromCode` (`u₁` is `1/n`-close to `0 ∈ ker H`, so
true MCA is jointly explained), its unguarded `(R)` proposition fails for every nontrivial
budget `B < |F|`. -/
theorem not_workbenchWorstCaseIncidenceBound {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {n m : ℕ} {H : (Fin n → F) →ₗ[F] (Fin m → F)} (hH : H ≠ 0)
    {b B : ℕ} (hb : 1 ≤ b) (hB : B < Fintype.card F) :
    ¬ WorkbenchWorstCaseIncidenceBound H b B := by
  intro hR
  obtain ⟨s₁, hs₁, -, hlow⟩ := workbench_badScalars_card_eq_card_field hH hb
  exact not_lt_of_ge (le_trans hlow (hR 0 s₁ hs₁)) hB

/-! ## §3. Unconditional refutation of linear-budget BGK-to-above-Johnson upgrades
and exact MCA-vs-List separation above Johnson -/

private theorem budget_ratio_le_tol {p B : ℕ} (hp : 0 < p) (hB : B * 2 ^ 128 ≤ p) :
    (B : ℝ≥0∞) / (p : ℝ≥0∞) ≤ 1 / (2 : ℝ≥0∞) ^ 128 := by
  have hp0 : (p : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h2 : ((2 : ℝ≥0) ^ 128) ≠ 0 := pow_ne_zero 128 two_ne_zero
  have hnn : (B : ℝ≥0) / (p : ℝ≥0) ≤ 1 / (2 : ℝ≥0) ^ 128 := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hp) (pow_pos zero_lt_two 128), one_mul]
    exact_mod_cast hB
  have henn := ENNReal.coe_le_coe.mpr hnn
  rwa [ENNReal.coe_div hp0, ENNReal.coe_natCast, ENNReal.coe_div h2, ENNReal.coe_one,
    ENNReal.coe_pow, ENNReal.coe_ofNat] at henn

/-- **General contrapositive of `OpenCoreConditionalPin.worstCaseIncidence_pin`.**
Whenever `mcaDeltaStar C ε* < δ` and `δ ≤ 1` with `B / |F| ≤ ε*`, `WorstCaseIncidenceBounded C δ B`
is unconditionally false. -/
theorem not_worstCaseIncidenceBounded_of_mcaDeltaStar_lt {ι F A : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ1 : δ ≤ 1)
    (hlt : (mcaDeltaStar (F := F) (A := A) C εstar : ℝ) < (δ : ℝ))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ B := by
  intro hI
  have hle := worstCaseIncidence_pin (F := F) (A := A) C εstar hδ1 hI hbudget
  exact not_le_of_gt hlt (by exact_mod_cast hle)

private theorem not_worstCaseIncidenceBounded_of_below {p k B : ℕ} [Fact p.Prime]
    (D : Fin (2 ^ 30) ↪ ZMod p)
    (hbelow : DesignatedPrimeJohnson.below D k 1)
    (hB : B ≤ p / 2 ^ 128) {δ : ℝ≥0}
    (hJ : DesignatedPrimeJohnson.johnson k ≤ (δ : ℝ)) (hδ1 : δ ≤ 1) :
    ¬ WorstCaseIncidenceBounded (F := ZMod p) (A := ZMod p)
        (ReedSolomon.code D k : Set (Fin (2 ^ 30) → ZMod p)) δ B := by
  unfold DesignatedPrimeJohnson.below at hbelow
  rw [mcaDeltaStar_interleaved_eq] at hbelow
  refine not_worstCaseIncidenceBounded_of_mcaDeltaStar_lt
    (ReedSolomon.code D k : Set (Fin (2 ^ 30) → ZMod p)) (1 / (2 : ℝ≥0∞) ^ 128) hδ1
    (lt_of_lt_of_le hbelow hJ) ?_
  rw [ZMod.card p]
  exact budget_ratio_le_tol (Fact.out : p.Prime).pos
    ((Nat.mul_le_mul_right (2 ^ 128) hB).trans (Nat.div_mul_le_self p (2 ^ 128)))

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30Second.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- **Unconditional refutation of the linear-budget above-Johnson upgrade on `P₁` at all four
prize rates.** On the first designated prime (`B ≤ P₁ / 2^128 = 2^30 = n`), for every prize
dimension `k ∈ {2^29, 2^28, 2^27, 2^26}` and every radius `δ ∈ [johnson k, 1]`,
`WorstCaseIncidenceBounded` is false—and hence **cannot** be implied by
`WorstCaseIncompleteSumBound ψ G M` for any `M` (even `M = 0`), resolving the open upgrade
question in `_PrizeFloorOfBGK`. -/
theorem firstPrime_no_aboveJohnson_incidence_at_prizeBudget
    {k : ℕ} (hk : k = 2 ^ 29 ∨ k = 2 ^ 28 ∨ k = 2 ^ 27 ∨ k = 2 ^ 26)
    {B : ℕ} (hB : B ≤ ArkLib.ProximityGap.PrizeShapePrimeP30.P / 2 ^ 128)
    {δ : ℝ≥0} (hJ : DesignatedPrimeJohnson.johnson k ≤ (δ : ℝ)) (hδ1 : δ ≤ 1) :
    ¬ WorstCaseIncidenceBounded
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (ReedSolomon.code FirstPrimeSepticCores.domain k :
          Set (Fin (2 ^ 30) → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)) δ B := by
  obtain ⟨h29, h28, h27, h26⟩ := DesignatedPrimeJohnson.first_four 1
  rcases hk with rfl | rfl | rfl | rfl
  · exact not_worstCaseIncidenceBounded_of_below _ h29 hB hJ hδ1
  · exact not_worstCaseIncidenceBounded_of_below _ h28 hB hJ hδ1
  · exact not_worstCaseIncidenceBounded_of_below _ h27 hB hJ hδ1
  · exact not_worstCaseIncidenceBounded_of_below _ h26 hB hJ hδ1

/-- Explicit corollary for `_PrizeFloorOfBGK`: no `WorstCaseIncompleteSumBound ψ G M` hypothesis
can imply above-Johnson `WorstCaseIncidenceBounded` at the `P₁` prize budget, because `ψ = 0` or
even any primitive character with `G = ∅, M = 0` (or any true subgroup bound on `μ_{2^30}`) leaves
the conclusion unconditionally false. -/
theorem firstPrime_bgk_does_not_upgrade_above_johnson
    {ψ : AddChar (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) ℂ}
    {G : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)} {M : ℝ}
    (_hBGK : WorstCaseIncompleteSumBound ψ G M)
    {k : ℕ} (hk : k = 2 ^ 29 ∨ k = 2 ^ 28 ∨ k = 2 ^ 27 ∨ k = 2 ^ 26)
    {δ : ℝ≥0} (hJ : DesignatedPrimeJohnson.johnson k ≤ (δ : ℝ)) (hδ1 : δ ≤ 1) :
    ¬ WorstCaseIncidenceBounded
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (ReedSolomon.code FirstPrimeSepticCores.domain k :
          Set (Fin (2 ^ 30) → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P))
        δ (ArkLib.ProximityGap.PrizeShapePrimeP30.P / 2 ^ 128) :=
  firstPrime_no_aboveJohnson_incidence_at_prizeBudget hk le_rfl hJ hδ1

/-- **Exact separation between Grand List Decoding and Grand MCA above Johnson on `P₂`
(rate `1/8`).**
At the second designated prime (`B = P₂ / 2^128 = 2^31 = 2n`), rate `1/8` (`k = 2^27`), and the
first integer error count `e = 694,116,763` strictly above Johnson:
1. `johnson (2^27) < 694116763 / 2^30`;
2. **Worst-case list decoding succeeds within the 128-bit budget:** every center has at most
   `1,660,990,722 ≤ P₂ / 2^128` codewords within `694,116,763` errors;
3. **Worst-case line-MCA incidence fails at the exact same code, radius, and budget:**
   `¬ WorstCaseIncidenceBounded (ReedSolomon.code dom (2^27)) (694116763 / 2^30) (P₂ / 2^128)`. -/
theorem secondPrime_rateEighth_list_beats_johnson_while_mca_fails :
    let P₂ := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
    let dom := ArkLib.ProximityGap.Frontier.SecondPrimeSmoothSeed.dom
    let δabove : ℝ≥0 := (694116763 : ℝ≥0) / (2 ^ 30 : ℝ≥0)
    DesignatedPrimeJohnson.johnson (2 ^ 27) < (δabove : ℝ) ∧
      InterleavedListJohnsonRank.AtErrors dom 1 (2 ^ 27) 694116763 (P₂ / 2 ^ 128) ∧
      ¬ WorstCaseIncidenceBounded (F := ZMod P₂) (A := ZMod P₂)
          (ReedSolomon.code dom (2 ^ 27) : Set (Fin (2 ^ 30) → ZMod P₂))
          δabove (P₂ / 2 ^ 128) := by
  dsimp only
  obtain ⟨-, habove, hlist, hbud⟩ :=
    DesignatedPrimeJohnson.second_eighth_list
      ArkLib.ProximityGap.Frontier.SecondPrimeSmoothSeed.dom 1
  have habove' : DesignatedPrimeJohnson.johnson (2 ^ 27) <
      (((694116763 : ℝ≥0) / (2 ^ 30 : ℝ≥0) : ℝ≥0) : ℝ) := by
    convert habove using 2
    norm_num
  have hδ1 : ((694116763 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num
  refine ⟨habove', hlist.trans (by exact_mod_cast hbud), ?_⟩
  exact not_worstCaseIncidenceBounded_of_below _
    (DesignatedPrimeJohnson.second_lower_rates 1).1 le_rfl habove'.le hδ1

/-- **Universal smooth-window obstruction across all fields with `|F| / 2^128 ≤ 1,163,220,311`.**
For *every* finite field `F` in this budget band—including the entire narrow split-prime window
`[2^158, 2^158 + 2^144]` where `> 2^106` primes satisfy the unit sixth-moment Wick bound
`E_3(μ_{2^30}) ≤ 15 n^3`—and *every* smooth domain `D : Fin (2^30) ↪ F`, both low prize rates
`k = 2^27` (`1/8`) and `k = 2^26` (`1/16`) have `mcaDeltaStar < johnson k`, refuting
`WorstCaseIncidenceBounded` at every `δ ∈ [johnson k, 1]` and budget `B = |F| / 2^128`. -/
theorem smoothWindow_lowRate_below_johnson {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (D : Fin (2 ^ 30) ↪ F) [ReedSolomon.Smooth D]
    {B : ℕ} (hB : Fintype.card F / 2 ^ 128 = B) (hBmax : B ≤ 1163220311)
    {k : ℕ} (hk : k = 2 ^ 27 ∨ k = 2 ^ 26) :
    (mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code D k : Set (Fin (2 ^ 30) → F)) (1 / (2 : ℝ≥0∞) ^ 128) : ℝ)
      < DesignatedPrimeJohnson.johnson k := by
  have hn : Fintype.card (Fin (2 ^ 30)) = SmoothTwoHeadProduction.n := by
    simp only [Fintype.card_fin, SmoothTwoHeadProduction.n]
    norm_num
  rcases hk with rfl | rfl
  · have hcap : DoubleQuadraticThreshold.agreements SmoothTwoHeadProduction.n (2 ^ 27)
        ≤ SmoothTwoHeadProduction.n - B / 2 + 1 := by
      unfold DoubleQuadraticThreshold.agreements DoubleQuadraticThreshold.margin
        SmoothTwoHeadProduction.n
      split_ifs <;> omega
    have hcurve := (SmoothTwoHeadProduction.curve D hn (k := 2 ^ 27) (a := 469762048) (B := B)
      (by decide) (by decide) (by decide) hB hcap (by dsimp [SmoothTwoHeadProduction.n]; omega) 1).1
    rw [mcaDeltaStar_interleaved_eq] at hcurve
    rw [hcurve]
    have hfirst : SmoothTwoHeadProduction.first 469762048 B ≤ 581610155 := by
      unfold SmoothTwoHeadProduction.first
      omega
    have hle_nn : ((SmoothTwoHeadProduction.first 469762048 B : ℕ) : ℝ≥0) /
        (SmoothTwoHeadProduction.n : ℝ≥0) ≤ ((581610155 : ℕ) : ℝ≥0) / ((2 ^ 30 : ℕ) : ℝ≥0) := by
      rw [show SmoothTwoHeadProduction.n = (2 ^ 30 : ℕ) from rfl]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hfirst) (Nat.cast_nonneg _)
    have hle : (((SmoothTwoHeadProduction.first 469762048 B : ℕ) : ℝ≥0) /
        (SmoothTwoHeadProduction.n : ℝ≥0) : ℝ) ≤
        ((581610155 : ℕ) : ℝ) / ((2 ^ 30 : ℕ) : ℝ) := by exact_mod_cast hle_nn
    refine lt_of_le_of_lt hle ?_
    unfold DesignatedPrimeJohnson.johnson
    exact (RankJohnsonComparison.below_iff (n := 2 ^ 30) (by decide) (2 ^ 27 - 1)
      (some ⟨581610155, by decide⟩)).mpr (by decide)
  · have hcap : DoubleQuadraticThreshold.agreements SmoothTwoHeadProduction.n (2 ^ 26)
        ≤ SmoothTwoHeadProduction.n - B / 2 + 1 := by
      unfold DoubleQuadraticThreshold.agreements DoubleQuadraticThreshold.margin
        SmoothTwoHeadProduction.n
      split_ifs <;> omega
    have hcurve := (SmoothTwoHeadProduction.curve D hn (k := 2 ^ 26) (a := 503316480) (B := B)
      (by decide) (by decide) (by decide) hB hcap (by dsimp [SmoothTwoHeadProduction.n]; omega) 1).1
    rw [mcaDeltaStar_interleaved_eq] at hcurve
    rw [hcurve]
    have hfirst : SmoothTwoHeadProduction.first 503316480 B ≤ 581610155 := by
      unfold SmoothTwoHeadProduction.first
      omega
    have hle_nn : ((SmoothTwoHeadProduction.first 503316480 B : ℕ) : ℝ≥0) /
        (SmoothTwoHeadProduction.n : ℝ≥0) ≤ ((581610155 : ℕ) : ℝ≥0) / ((2 ^ 30 : ℕ) : ℝ≥0) := by
      rw [show SmoothTwoHeadProduction.n = (2 ^ 30 : ℕ) from rfl]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hfirst) (Nat.cast_nonneg _)
    have hle : (((SmoothTwoHeadProduction.first 503316480 B : ℕ) : ℝ≥0) /
        (SmoothTwoHeadProduction.n : ℝ≥0) : ℝ) ≤
        ((581610155 : ℕ) : ℝ) / ((2 ^ 30 : ℕ) : ℝ) := by exact_mod_cast hle_nn
    refine lt_of_le_of_lt hle ?_
    unfold DesignatedPrimeJohnson.johnson
    exact (RankJohnsonComparison.below_iff (n := 2 ^ 30) (by decide) (2 ^ 26 - 1)
      (some ⟨581610155, by decide⟩)).mpr (by decide)

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms card_directionPerp_mul_eq
#print axioms syndromeLineIncidence_abs_sub_mean_le
#print axioms syndrome_charSum_sup_sq_ge_parseval
#print axioms far_mcaBadCount_eq_syndromeLineIncidence
#print axioms far_mcaBadCount_abs_sub_mean_le
#print axioms not_workbenchWorstCaseIncidenceBound
#print axioms firstPrime_no_aboveJohnson_incidence_at_prizeBudget
#print axioms firstPrime_bgk_does_not_upgrade_above_johnson
#print axioms secondPrime_rateEighth_list_beats_johnson_while_mca_fails
#print axioms smoothWindow_lowRate_below_johnson

end ArkLib.ProximityGap.Frontier.CarbonBGKPrizeBridgeResolution
