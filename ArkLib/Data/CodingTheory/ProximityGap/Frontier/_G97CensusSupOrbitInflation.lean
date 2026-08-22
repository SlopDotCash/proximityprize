/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# LANE G97: the depth-`r` census can NEVER reach the sup wall `M` — orbit inflation, `r`-uniform

## Context (the G96 referee's binding obstruction, made a theorem)

The G96 referee (`fable_g96_hbk_input_probe` + `fable_g96b_object_match`) refereed the G86–G91
depth-census program (`_G91DepthFiveUnorderedHBKBridge`) and returned a decisive verdict: the
census bounds are *sound* but **structurally blind** to the single-embedding / non-Fourier wall
`M = max_{b≠0} ‖η_b‖`.  The exact reason it recorded as the binding obstruction:

> the depth-`r` census `E_r = p⁻¹ Σ_b ‖η_b‖^{2r}` bounds the AVERAGE `2r`-moment; the `M`-wall is
> the SUP `max ‖η_b‖`.  Because the `‖η_b‖ = M` frequencies form a full `φ(n)`-size phase-coherent
> Frobenius orbit (G74), `Σ ‖η_b‖^{2r} ≥ φ(n)·M^{2r}`, so `(p·E_r)^{1/2r} ≥ φ^{1/2r}·M > M` — every
> census/energy bound is inflated above the true wall and CANNOT close the single-embedding `M`
> bound.  Endpoint-2 is NOT reachable by any additive-energy depth census, no matter how tight the
> depth-quotient.

The referee measured the inflation ratio `(p·E₅ − n^{10})^{1/10}/M ∈ [1.31, 1.43]` at every
adversarial thin cell, and the DC-subtracted probe (`g97_census_sup_inflation_probe`) confirms the
extracted ratio `(Σ_{b≠0}‖η_b‖^{2r})^{1/2r}/M > 1` at *every* finite rung `r = 1..6` and every cell
(e.g. `1.25`–`2.30` at the `n=8..32` walls), decreasing toward `1` but never reaching it.

This file turns that obstruction into an **axiom-clean, `r`-uniform** theorem.  It abstracts over
the modulus spectrum `η : ι → ℝ` (instantiate `η_b := ‖η_b‖`), a `Finset O` of maximisers all
pinned to the sup value `M`, and the rung `r`.  The single arithmetic fact underneath is
`Σ_b (η_b)^{2r} ≥ (card O) · M^{2r}` (drop all non-orbit terms, pin the orbit terms to `M`), whence
the census-extracted bound `(Σ_b (η_b)^{2r})^{1/2r} ≥ (card O)^{1/2r} · M`, which is **strictly**
`> M` as soon as `card O ≥ 2` and `M > 0`.  It is deliberately NOT a wrapper:

* G67 (`_G67SignedCensusSupExtractionNoGo`) closes the *signed depth-reweighting* lever — a negative
  transfer weight inverts the census, never bounds the sup.  Different object (weights `w`, not the
  orbit multiplicity of the sup).
* G80 (`_G80SignedL1CertificatePinnedToWall`) pins the *signed `l1` certificate value* to `M`.
  Different functional (unit-`l1` correlation, not a `2r`-moment census).
* `RealizerL2NotSup` / `_Attack07L2LinfGap` prove an `L²`/`L∞` gap for a *single concrete incidence
  realizer* / a *degenerate-direction spike*.  Those are fixed-object, single-`r` statements.  G97
  is the `r`-UNIFORM depth-census statement — the sup-extraction inflation factor `(card O)^{1/2r}`
  is `> 1` at *every* rung, so the ENTIRE depth-census program (all rungs `r`, the G86–G91 line) is
  blind to the wall, not merely one moment.

## Honest scope

Proves: whenever `≥ 2` spectrum entries share the maximal modulus `M > 0`, every depth-`r` census
`Σ (η_b)^{2r}` overshoots `M^{2r}` by at least the orbit multiplicity, so the `2r`-th root
extraction strictly exceeds `M` at every finite rung.  This is the precise sense in which no
additive-energy depth census reaches the sup wall.  It does NOT claim the wall itself is
unreachable by a genuine sup-side / cancellation argument — only that the census (average-moment)
route is inflated at every
rung.  Combined with the fully wall-pinned fixed-cell ledger and the closed non-BGK escapes, the
honest frontier statement stands: `δ*` CORE is ON-BGK/Paley at the adversarial thin subgroup; the
depth-census program (G86–G91) is average-moment control that is structurally inflated above the
sup, hence cannot close the single-embedding non-Fourier `M` bound.  CORE OPEN, ON-BGK.
-/

namespace ArkLib.ProximityGap.Frontier.G97CensusSupOrbitInflation

open Finset

variable {ι : Type*}

/-- The depth-`r` census total over a spectrum `η : ι → ℝ` and a support `s : Finset ι`:
`censusTotal s η r = Σ_{b ∈ s} (η b)^{2r}` (the `p·E_r` un-normalised even-power moment sum). -/
noncomputable def censusTotal (s : Finset ι) (η : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ b ∈ s, (η b) ^ (2 * r)

/-- Every census term is nonnegative (an even power of a real). -/
theorem censusTerm_nonneg (η : ι → ℝ) (r : ℕ) (b : ι) : 0 ≤ (η b) ^ (2 * r) := by
  have : (η b) ^ (2 * r) = ((η b) ^ r) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [this]
  exact sq_nonneg _

/-- The census total is nonnegative. -/
theorem censusTotal_nonneg (s : Finset ι) (η : ι → ℝ) (r : ℕ) : 0 ≤ censusTotal s η r :=
  Finset.sum_nonneg fun b _ => censusTerm_nonneg η r b

/-- **Orbit floor for the census.**  If every frequency in the sub-support `O ⊆ s` is pinned to the
sup value `M` (i.e. `η b = M` on `O`), the census total is at least the orbit multiplicity times
`M^{2r}`.  Drop the (nonnegative, even-power) non-orbit terms, then pin the `O`-terms to `M`. -/
theorem card_orbit_mul_pow_le_censusTotal
    {s O : Finset ι} (η : ι → ℝ) {M : ℝ} {r : ℕ}
    (hOs : O ⊆ s) (hpin : ∀ b ∈ O, η b = M) :
    (O.card : ℝ) * M ^ (2 * r) ≤ censusTotal s η r := by
  have hOsum : ∑ b ∈ O, (η b) ^ (2 * r) = (O.card : ℝ) * M ^ (2 * r) := by
    rw [Finset.sum_congr rfl (fun b hb => by rw [hpin b hb])]
    rw [Finset.sum_const, nsmul_eq_mul]
  calc (O.card : ℝ) * M ^ (2 * r)
      = ∑ b ∈ O, (η b) ^ (2 * r) := hOsum.symm
    _ ≤ censusTotal s η r :=
        Finset.sum_le_sum_of_subset_of_nonneg hOs
          (fun b _ _ => censusTerm_nonneg η r b)

/-- **Census extraction is inflated by the orbit multiplicity (the `2r`-th root form).**
Taking the `(2r)`-th root of the orbit floor: the census-extracted bound
`(censusTotal)^{1/(2r)}` is at least `(card O)^{1/(2r)} · M`.  Stated with `Real.rpow`
so the extraction is literally the "recover `M` from the census" operation the referee tested. -/
theorem censusExtraction_ge_orbitFactor_mul
    {s O : Finset ι} (η : ι → ℝ) {M : ℝ} {r : ℕ}
    (hOs : O ⊆ s) (hpin : ∀ b ∈ O, η b = M) (hM : 0 ≤ M) (hr : 0 < r) :
    ((O.card : ℝ) ^ ((1 : ℝ) / (2 * r))) * M
      ≤ (censusTotal s η r) ^ ((1 : ℝ) / (2 * r)) := by
  have hfloor := card_orbit_mul_pow_le_censusTotal η hOs hpin (M := M) (r := r)
  have hbaseNonneg : (0 : ℝ) ≤ (O.card : ℝ) * M ^ (2 * r) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)
  -- monotonicity of rpow (exponent `1/(2r) ≥ 0`) on the floor inequality
  have hmono : ((O.card : ℝ) * M ^ (2 * r)) ^ ((1 : ℝ) / (2 * r))
      ≤ (censusTotal s η r) ^ ((1 : ℝ) / (2 * r)) :=
    Real.rpow_le_rpow hbaseNonneg hfloor (by positivity)
  -- factor the LHS root: `(K · M^{2r})^{1/(2r)} = K^{1/(2r)} · M`
  have hrootM : (M ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) = M := by
    rw [← Real.rpow_natCast M (2 * r), ← Real.rpow_mul hM]
    rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [show (2 : ℝ) * (r : ℝ) * ((1 : ℝ) / (2 * r)) = 1 by field_simp]
    rw [Real.rpow_one]
  have hfactor : ((O.card : ℝ) * M ^ (2 * r)) ^ ((1 : ℝ) / (2 * r))
      = (O.card : ℝ) ^ ((1 : ℝ) / (2 * r)) * M := by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hM _), hrootM]
  rw [hfactor] at hmono
  exact hmono

/-- **The orbit inflation factor is strictly `> 1` at every finite rung once `card O ≥ 2`.**
`(card O)^{1/(2r)} > 1` whenever `card O ≥ 2` and `r ≥ 1`. -/
theorem orbitFactor_gt_one
    {O : Finset ι} {r : ℕ} (hcard : 2 ≤ O.card) (hr : 0 < r) :
    (1 : ℝ) < (O.card : ℝ) ^ ((1 : ℝ) / (2 * r)) := by
  have hbase : (1 : ℝ) < (O.card : ℝ) := by
    have : (2 : ℝ) ≤ (O.card : ℝ) := by exact_mod_cast hcard
    linarith
  have hexp : (0 : ℝ) < (1 : ℝ) / (2 * r) := by positivity
  exact (Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨hbase, hexp⟩)

/-- **HEADLINE — the depth-`r` census strictly overshoots the sup wall `M`, at EVERY rung.**
If `≥ 2` spectrum entries are pinned to the maximal modulus `M > 0`, the census-extracted bound
`(censusTotal)^{1/(2r)}` is `> M` for every `r ≥ 1`.  No additive-energy depth census, at any
depth, reaches the single-embedding sup wall: the extraction is inflated by `(card O)^{1/(2r)} > 1`.
This is the `r`-uniform census→sup blindness the G96 referee named as the binding obstruction. -/
theorem census_extraction_strictly_exceeds_wall
    {s O : Finset ι} (η : ι → ℝ) {M : ℝ} {r : ℕ}
    (hOs : O ⊆ s) (hpin : ∀ b ∈ O, η b = M)
    (hM : 0 < M) (hcard : 2 ≤ O.card) (hr : 0 < r) :
    M < (censusTotal s η r) ^ ((1 : ℝ) / (2 * r)) := by
  have hfactor := orbitFactor_gt_one (O := O) (r := r) hcard hr
  have hlow := censusExtraction_ge_orbitFactor_mul η hOs hpin hM.le hr
  have hstrict : M < (O.card : ℝ) ^ ((1 : ℝ) / (2 * r)) * M := by
    calc M = 1 * M := (one_mul M).symm
      _ < (O.card : ℝ) ^ ((1 : ℝ) / (2 * r)) * M := by
          exact mul_lt_mul_of_pos_right hfactor hM
  exact lt_of_lt_of_le hstrict hlow

/-- **DC-dominance corollary — the census also can't beat the wall from the DC term alone.**
If a *single* frequency (the DC index `d ∈ s`) carries modulus `N ≥ M`, the raw census extraction is
already `≥ N ≥ M`.  Together with the headline (strict overshoot from the DC-subtracted orbit), this
records BOTH inflation sources the probe measured: the DC term `n^{2r}` alone forces the extraction
`≥ n ≥ M`, and even after subtracting it the Frobenius M-orbit forces a strict overshoot. -/
theorem census_extraction_ge_dc
    {s : Finset ι} (η : ι → ℝ) {N M : ℝ} {d : ι} {r : ℕ}
    (hd : d ∈ s) (hdc : η d = N) (hNM : M ≤ N) (hN : 0 ≤ N) (hr : 0 < r) :
    M ≤ (censusTotal s η r) ^ ((1 : ℝ) / (2 * r)) := by
  have hsingle : N ^ (2 * r) ≤ censusTotal s η r := by
    have : (η d) ^ (2 * r) ≤ censusTotal s η r :=
      Finset.single_le_sum (f := fun b => (η b) ^ (2 * r))
        (fun b _ => censusTerm_nonneg η r b) hd
    rwa [hdc] at this
  have hmono : (N ^ (2 * r)) ^ ((1 : ℝ) / (2 * r))
      ≤ (censusTotal s η r) ^ ((1 : ℝ) / (2 * r)) :=
    Real.rpow_le_rpow (pow_nonneg hN _) hsingle (by positivity)
  have hroot : (N ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) = N := by
    rw [← Real.rpow_natCast N (2 * r), ← Real.rpow_mul hN]
    rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [show (2 : ℝ) * (r : ℝ) * ((1 : ℝ) / (2 * r)) = 1 by field_simp]
    rw [Real.rpow_one]
  rw [hroot] at hmono
  exact le_trans hNM hmono

end ArkLib.ProximityGap.Frontier.G97CensusSupOrbitInflation
