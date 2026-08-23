/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.Hab25WhirBridge
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ConjectureGlue
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernel
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffLargeReduction
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.LocalSeriesProducer
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.Assembly
import ArkLib.Data.CodingTheory.GuruswamiSudan.Hab25FactorWeld

/-!
# The literal pair-case Johnson conjecture, reduced to the per-`δ` Johnson numeric residual

`Hab25WhirBridge.lean` composes the Hab25 chain into `hasMutualCorrAgreement` for an
*abstract* target `(BStar, errStar)` and still carries the closed-form comparison
`ofReal (johnsonBoundReal …) ≤ errStar δ` as a hypothesis; `Hab25ConjectureGlue.lean`
proves exactly that comparison for the *literal* conjecture error at the per-`δ` parameter
`η := μ(δ) = min(1 − √ρ − δ, √ρ/20)`. This file splices the two (pure wiring, no new
mathematics), so that the **verbatim statement** `mca_johnson_bound_CONJECTURE` at
`parℓ = Fin 2` (Conjecture 4.12, Johnson regime, affine-line generator) is concluded with
no comparison or plumbing hypotheses left:

* `mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound` — the per-`δ`
  `JohnsonNumericBound` at `η := μ(δ)` implies the literal pair-case conjecture;
* `mca_johnson_bound_CONJECTURE_pair_of_claim1_cells` — the literal pair-case conjecture
  from per-`δ`, per-stack Claim-1 cell data alone (the BCIKS20 Steps 5–7 capture output,
  the single remaining deep input), with the cell count in the per-`δ` GS list shape.
* `mca_johnson_bound_CONJECTURE_pair_of_decode_family_pinning` — the same literal
  conjecture from the producer-facing §5 data: per-cell decoded-polynomial families plus
  affine pinning above the `|ι|` threshold.
* `mca_johnson_bound_CONJECTURE_pair_of_decode_family_window` — the same result on the
  unique-decoding window proved in `Hab25CaptureKernelUD`: per-cell decoded-polynomial
  families alone imply the capture data.
* `mca_johnson_bound_CONJECTURE_pair_of_fixed_linear_factor_cells` — the same result
  from cell data where each large cell is claimed by one fixed linear `K = F(Z)` factor,
  using the proved factor-weld pinning theorem.
* `decode_family_affine_pinning_of_strictCoeffPolysResidual` — the local bridge from the
  BCIKS20 `StrictCoeffPolysResidual` surface to the affine-pinning witness consumed by
  the capture kernel.
* `decode_family_affine_pinning_of_strictCoeffPolysLargeResidual` — the same bridge from
  the large-sector residual, the actual §5 core after the small-good-set reduction.
* `prob_close_curve_gt_of_cell_card_gt` — the inverse threshold adapter: a large cell inside
  `RS_goodCoeffsCurve` yields the probability premise needed by the strict residual.
* `hsteps57_of_strictCoeffPolysResidual` — the same strict-residual bridge packaged in
  Claim-1's literal capture-above-threshold shape.
* `hsteps57_of_strictCoeffPolysLargeResidual` — the large-sector form in Claim-1's
  literal capture-above-threshold shape.
* `hsteps57_of_strictCoeffPolysResidual_cell_card_gt` /
  `hsteps57_of_strictCoeffPolysLargeResidual_cell_card_gt` — the same Claim-1 capture
  surfaces with the probability premise discharged by a concrete large cell.
* `decode_family_affine_pinning_of_rawGSCargo` / `hsteps57_of_rawGSCargo` — the same
  bridge from the raw GS cargo bundle produced by the local-series/Hensel lane.
* `hsteps57_of_rawGSCargo_cell_card_gt` — the raw-cargo Claim-1 capture front door with
  the probability premise discharged from a concrete large cell.
* `mca_johnson_bound_CONJECTURE_pair_of_coeff_polys_cells` — the same result from
  BCIKS-style coefficient-polynomial data on each large cell; the curve assembly theorem
  specializes at `Fin 2` to affine pinning.

Orientation of the comparison was independently re-checked numerically before wiring
(`scripts/probes/probe_conjecture_pair_wiring.py`: 1320 grid points, 0 violations, worst
ratio `1.8·10⁻³`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset
open Polynomial.Bivariate
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped Polynomial

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The rate of the pair power generator is exactly `2^m / |ι|` (as a real number). -/
theorem rate_genRSC_pair (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι) :
    (RSGenerator.genRSC (Fin 2) φ m exp).rate =
      (2 ^ m : ℝ) / (Fintype.card ι : ℝ) := by
  have h := rate_smoothCode_coe (F₀ := F) (ι₀ := ι) φ m hk
  simpa [RSGenerator.genRSC] using h

open Classical in
/-- **The literal pair-case Johnson conjecture from the per-`δ` Johnson numeric
residual.** If, for every admissible `δ` (i.e. `0 < δ < 1 − √ρ` with `ρ = 2^m/|ι|`),
the Hab25 numeric residual `JohnsonNumericBound` holds at the per-`δ` parameter
`η := μ(δ) = min(1 − √ρ − δ, √ρ/20)`, then `mca_johnson_bound_CONJECTURE` holds
verbatim at `parℓ = Fin 2` with exponents `(0, 1)` — `BStar = √ρ` and the conjecture's
exact `errStar`. The closed-form comparison is discharged by
`johnsonBoundReal_le_errStar_real`; no side hypotheses remain. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι)
    (hJNB : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      JohnsonNumericBound (F₀ := F) (ι₀ := ι) φ (2 ^ m)
        (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
          (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal δ) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  classical
  have hrate := rate_genRSC_pair φ m exp hk
  have hmca :
      haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m exp).parℓ :=
        (RSGenerator.genRSC (Fin 2) φ m exp).hℓ
      hasMutualCorrAgreement (RSGenerator.genRSC (Fin 2) φ m exp)
        (Real.sqrt (RSGenerator.genRSC (Fin 2) φ m exp).rate)
        (fun x =>
          ENNReal.ofReal
            (((Fintype.card (Fin 2) : ℝ) - 1) * 2 ^ (2 * m) /
              ((Fintype.card F : ℝ) *
                (2 * min
                  (1 - Real.sqrt (RSGenerator.genRSC (Fin 2) φ m exp).rate - x)
                  (Real.sqrt (RSGenerator.genRSC (Fin 2) φ m exp).rate / 20)) ^ 7))) := by
    refine hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le φ m exp hexp0 hexp1
      _ (Real.sqrt_nonneg _) _ ?_
    intro δ hδ0 hδB
    rw [hrate] at hδB
    refine le_trans (hJNB δ hδ0 hδB) ?_
    rw [hrate, show ((Fintype.card (Fin 2) : ℝ) - 1) = 1 from by norm_num, one_mul]
    exact ENNReal.ofReal_le_ofReal
      (johnsonBoundReal_le_errStar_real φ m hk δ hδB)
  unfold mca_johnson_bound_CONJECTURE
  exact hmca

omit [DecidableEq ι] in
/-- **The literal pair-case Johnson conjecture from per-stack Claim-1 cell data alone.**
For every admissible `δ` and word stack, suppose the bad scalars decompose into `≤ L`
cells satisfying the capture-above-`n` dichotomy (the BCIKS20 Steps 5–7 output — the
single remaining deep input of the #302 chain), with `L` within the per-`δ` GS list-size
shape. Then `mca_johnson_bound_CONJECTURE` holds verbatim at `parℓ = Fin 2`: nothing
between the capture data and the literal conjecture statement remains unproven. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_claim1_cells
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (Index : Finset Idx) (Ecell : Idx → Finset F),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          ∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            ∃ a b : F[X], a.natDegree < 2 ^ m ∧ b.natDegree < 2 ^ m ∧
              ∀ γ ∈ Ecell ij,
                AffineCaptured φ (2 ^ m) δ u γ (a, b)) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  classical
  refine mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound α φ m exp
    hexp0 hexp1 hk ?_
  intro δ hδ0 hδB
  exact johnsonNumericBound_of_claim1_cells φ (2 ^ m) _ δ L hk
    (hL δ hδ0 hδB) (hdata δ hδ0 hδB)

open Classical in
/-- **The literal pair-case Johnson conjecture from decode-family affine pinning.**
This is the producer-facing form of `mca_johnson_bound_CONJECTURE_pair_of_claim1_cells`:
for every admissible `δ` and stack, the bad scalars are covered by `≤ L` cells; each scalar
in a cell has a decoded polynomial `Pcell ij γ`; and any cell larger than the domain is
affine-pinned as `Pcell ij γ = v₀ + γ·v₁` with degree `< 2^m`. The capture kernel converts
that exact §5/Hensel output surface into Claim-1 capture data, after which the already-proven
Hab25 numeric and WHIR wiring finish the literal pair-case conjecture. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_decode_family_pinning
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
          (Ecell : Idx → Finset F) (Pcell : Idx → F → F[X]),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
            ∃ d : McaDecode φ (2 ^ m) δ u γ, d.P = Pcell ij γ) ∧
          (∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            ∃ v₀ v₁ : F[X], v₀.natDegree < 2 ^ m ∧ v₁.natDegree < 2 ^ m ∧
              ∀ γ ∈ Ecell ij, Pcell ij γ = v₀ + Polynomial.C γ * v₁)) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  refine mca_johnson_bound_CONJECTURE_pair_of_claim1_cells α φ m exp
    hexp0 hexp1 hk L hL ?_
  intro δ hδ0 hδB u
  obtain ⟨Idx, hIdx, Index, Ecell, Pcell, hcard, hcover, hdec, hpin⟩ :=
    hdata δ hδ0 hδB u
  letI : DecidableEq Idx := hIdx
  refine ⟨Idx, Index, Ecell, hcard, hcover, ?_⟩
  intro ij hij hlarge
  exact hsteps57_of_decode_family_pinning (domain := φ) (k := 2 ^ m)
    (δ := δ) (u := u) (Ecell ij) (Fintype.card ι) (Pcell ij)
    (hdec ij hij) (hpin ij hij) hlarge

open Classical in
/-- **The literal pair-case Johnson conjecture on the unique-decoding window.**
This is the O88/K4 depth-0 front door: if every admissible radius lies in the window
`2·|ι| + 2^m ≤ 3·⌈(1−δ)|ι|⌉₊`, then the affine-pinning leg of the Claim-1 cells is no
longer a producer hypothesis. The proved kernel theorem `hsteps57_of_window` constructs
the pencil from any per-cell decoded-polynomial family, and the existing Claim-1/Hab25
numeric wiring finishes the literal pair-case Johnson MCA conjecture. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_decode_family_window
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hwin : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      2 * Fintype.card ι + 2 ^ m ≤
        3 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
          (Ecell : Idx → Finset F) (Pcell : Idx → F → F[X]),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          ∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
            ∃ d : McaDecode φ (2 ^ m) δ u γ, d.P = Pcell ij γ) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  refine mca_johnson_bound_CONJECTURE_pair_of_claim1_cells α φ m exp
    hexp0 hexp1 hk L hL ?_
  intro δ hδ0 hδB u
  obtain ⟨Idx, hIdx, Index, Ecell, Pcell, hcard, hcover, hdec⟩ :=
    hdata δ hδ0 hδB u
  letI : DecidableEq Idx := hIdx
  refine ⟨Idx, Index, Ecell, hcard, hcover, ?_⟩
  intro ij hij hlarge
  have hkpos : 0 < 2 ^ m := by positivity
  exact hsteps57_of_window (domain := φ) (k := 2 ^ m) (δ := δ) (u := u)
    hkpos (Ecell ij) (T := Fintype.card ι) Fintype.card_pos (Pcell ij)
    (hdec ij hij) (hwin δ hδ0 hδB) hlarge

open Classical in
/-- **The literal pair-case Johnson conjecture from fixed linear factor cells.** This is the
Guruswami-Sudan factor-weld-facing version of the pair-case theorem: after the bad scalars
are decomposed into cells with decoded-polynomial families `Pcell`, any large cell is
assumed to be claimed by one fixed linear `K = F(Z)` factor with affine pair `(a, b)`, and
the representative denominator survives on the cell. The proven factor weld turns that into
cellwise affine pinning, and the capture-kernel / Claim-1 / Hab25 arithmetic chain finishes
the literal pair-case Johnson conjecture. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_fixed_linear_factor_cells
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
          (Ecell : Idx → Finset F) (Pcell : Idx → F → F[X]),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
            ∃ d : McaDecode φ (2 ^ m) δ u γ, d.P = Pcell ij γ) ∧
          (∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            ∃ (rep : (F[X])[X][Y]) (dR : F[X]) (p : (RatFunc F)[X]) (a b : F[X]),
              a.natDegree < 2 ^ m ∧ b.natDegree < 2 ^ m ∧
              rep.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
                Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
                  (Polynomial.X - Polynomial.C p) ∧
              p = a.map (algebraMap F (RatFunc F)) +
                Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)) ∧
              (∀ γ ∈ Ecell ij, dR.eval γ ≠ 0) ∧
              ∀ γ ∈ Ecell ij,
                (Polynomial.X - Polynomial.C (Pcell ij γ)) ∣
                  rep.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  refine mca_johnson_bound_CONJECTURE_pair_of_decode_family_pinning α φ m exp
    hexp0 hexp1 hk L hL ?_
  intro δ hδ0 hδB u
  obtain ⟨Idx, hIdx, Index, Ecell, Pcell, hcard, hcover, hdec, hfactor⟩ :=
    hdata δ hδ0 hδB u
  letI : DecidableEq Idx := hIdx
  refine ⟨Idx, inferInstance, Index, Ecell, Pcell, hcard, hcover, hdec, ?_⟩
  intro ij hij hlarge
  obtain ⟨rep, dR, p, a, b, ha, hb, hrep, haffine, hden, hclaim⟩ :=
    hfactor ij hij hlarge
  exact GuruswamiSudan.OverRatFunc.decoded_family_affine_pinning_of_fixed_linear_rep
    (Ecell := Ecell ij) (P := Pcell ij) (k := 2 ^ m)
    ha hb hrep haffine hden hclaim

omit [Nonempty ι] [DecidableEq ι] in
/-- **Affine pinning from the BCIKS20 strict-coefficient residual.**  This is the local
adapter between the §5 residual language and the WHIR/Hab25 capture kernel: once the
decoded family `P` satisfies the `StrictCoeffPolysResidual` input on the full good-curve
set, the residual supplies degree-`< 2` coefficient polynomials. The curve assembly theorem
then specializes those witnesses at `k = 1` to a single affine pencil on any selected cell
`Ecell ⊆ RS_goodCoeffsCurve`. -/
theorem decode_family_affine_pinning_of_strictCoeffPolysResidual
    {deg : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hStrict : _root_.ProximityGap.StrictCoeffPolysResidual
      (k := 1) (deg := deg) (domain := φ) (δ := δ))
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < deg ∧ v₁.natDegree < deg ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ := by
  classical
  obtain ⟨B, hBdeg, hcoeff⟩ :=
    hStrict (by norm_num) u hprob hJ hsqrt P hPgood
  obtain ⟨A, hAdeg, hP⟩ :=
    _root_.ProximityGap.decoded_family_coefficients_of_coeff_polys
      (l := 0) (deg := deg) (S' := Ecell) (P := P) B
      (by simpa using hBdeg)
      (fun z hz => (hPgood z (hsubset hz)).1)
      (fun z hz j hj => hcoeff z (hsubset hz) j hj)
  refine ⟨A 0, A 1, hAdeg 0, hAdeg 1, fun γ hγ => ?_⟩
  simpa [Fin.sum_univ_two] using hP γ hγ

omit [Nonempty ι] [DecidableEq ι] in
/-- **Affine pinning from the large-sector BCIKS20 strict-coefficient residual.**
`StrictCoeffLargeReduction` proves that the full strict coefficient residual is equivalent
to this large-good-set restriction; this wrapper exposes the actual §5 core directly on the
K4 affine-pinning surface. -/
theorem decode_family_affine_pinning_of_strictCoeffPolysLargeResidual
    {deg : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hLarge : _root_.ProximityGap.StrictCoeffPolysLargeResidual
      (k := 1) (deg := deg) (domain := φ) (δ := δ))
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < deg ∧ v₁.natDegree < deg ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ :=
  decode_family_affine_pinning_of_strictCoeffPolysResidual (φ := φ)
    (_root_.ProximityGap.strictCoeffPolysResidual_of_large hLarge)
    u hprob hJ hsqrt P Ecell hsubset hPgood

/-- **Claim-1 capture from the BCIKS20 strict-coefficient residual.**  This packages
`decode_family_affine_pinning_of_strictCoeffPolysResidual` in the exact `hsteps57` shape
used by `claim1_dichotomy`: the strict-coefficient residual pins the decoded family to
one affine pencil on the cell, and the capture kernel turns those equalities plus the
per-scalar decodes into `AffineCaptured` witnesses. -/
theorem hsteps57_of_strictCoeffPolysResidual
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hStrict : _root_.ProximityGap.StrictCoeffPolysResidual
      (k := 1) (deg := deg) (domain := φ) (δ := δ))
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) := by
  refine hsteps57_of_decode_family_pinning (domain := φ) (k := deg)
    (δ := δ) (u := u) Ecell T P hdec ?_
  intro _hlarge
  exact decode_family_affine_pinning_of_strictCoeffPolysResidual
    (φ := φ) hStrict u hprob hJ hsqrt P Ecell hsubset hPgood

/-- **Claim-1 capture from the large-sector BCIKS20 strict-coefficient residual.**
This is the producer-facing form after the small-good-set interpolation sector has been
removed: the remaining large-sector §5 residual directly implies Claim-1's
capture-above-threshold hypothesis for a selected cell. -/
theorem hsteps57_of_strictCoeffPolysLargeResidual
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hLarge : _root_.ProximityGap.StrictCoeffPolysLargeResidual
      (k := 1) (deg := deg) (domain := φ) (δ := δ))
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) :=
  hsteps57_of_strictCoeffPolysResidual (φ := φ)
    (_root_.ProximityGap.strictCoeffPolysResidual_of_large hLarge)
    u hprob hJ hsqrt P Ecell hsubset hPgood hdec

omit [Nonempty ι] [DecidableEq ι] in
/-- **Probability from a large good-coefficient cell.**  The BCIKS20 curve layer proves the
exact identity
`Pr[δᵣ(curve z, RS) ≤ δ] = |RS_goodCoeffsCurve| / |F|`.  This adapter runs the identity in
the reverse direction on any selected cell: if `Ecell ⊆ RS_goodCoeffsCurve` and
`η * |F| < |Ecell|`, then the curve is close with probability strictly larger than `η`.
It is the local bridge that lets Claim-1/§5 residual data consume concrete large-cell
cardinality hypotheses instead of a separately supplied probability bound. -/
theorem prob_close_curve_gt_of_cell_card_gt
    {deg : ℕ} (φ : ι ↪ F) {δ η : ℝ≥0}
    (u : Code.WordStack F (Fin 2) ι) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (η : ENNReal) * (Fintype.card F : ENNReal) <
      (Ecell.card : ENNReal)) :
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
        ReedSolomon.code φ deg) ≤ δ] > (η : ENNReal) := by
  classical
  let G : Finset F :=
    _root_.ProximityGap.RS_goodCoeffsCurve
      (k := 1) (deg := deg) (domain := φ) u δ
  have hcard_le : Ecell.card ≤ G.card := Finset.card_le_card hsubset
  have hcard_le_enn : (Ecell.card : ENNReal) ≤ (G.card : ENNReal) := by
    exact_mod_cast hcard_le
  have hgood : (η : ENNReal) * (Fintype.card F : ENNReal) <
      (G.card : ENNReal) :=
    lt_of_lt_of_le hcard hcard_le_enn
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hqtop : (Fintype.card F : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top (Fintype.card F)
  have hlt_div : (η : ENNReal) <
      (G.card : ENNReal) / (Fintype.card F : ENNReal) := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hq0) (Or.inl hqtop)]
    exact hgood
  have hPr := _root_.ProximityGap.prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := 1) (deg := deg) (domain := φ) (δ := δ) u
  have hq0_nn : (Fintype.card F : ℝ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hlt_div_nn :
      (η : ENNReal) <
        (((_root_.ProximityGap.RS_goodCoeffsCurve
          (k := 1) (deg := deg) (domain := φ) u δ).card : ℝ≥0) /
            (Fintype.card F : ℝ≥0) : ℝ≥0) := by
    simpa [G, ENNReal.coe_div hq0_nn, ENNReal.coe_natCast] using hlt_div
  rw [hPr]
  simpa [gt_iff_lt] using hlt_div_nn

omit [Nonempty ι] [DecidableEq ι] in
/-- **Affine pinning from strict residual plus a large cell.**  This is
`decode_family_affine_pinning_of_strictCoeffPolysResidual` with its probability hypothesis
discharged from `Ecell ⊆ RS_goodCoeffsCurve` and the cardinal inequality
`errorBound * |F| < |Ecell|`. -/
theorem decode_family_affine_pinning_of_strictCoeffPolysResidual_cell_card_gt
    {deg : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hStrict : _root_.ProximityGap.StrictCoeffPolysResidual
      (k := 1) (deg := deg) (domain := φ) (δ := δ))
    (u : Code.WordStack F (Fin 2) ι)
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (_root_.ProximityGap.errorBound δ deg φ : ENNReal) *
      (Fintype.card F : ENNReal) < (Ecell.card : ENNReal))
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < deg ∧ v₁.natDegree < deg ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ := by
  classical
  have hprob := prob_close_curve_gt_of_cell_card_gt
    (φ := φ) (deg := deg) (δ := δ)
    (η := _root_.ProximityGap.errorBound δ deg φ) u Ecell hsubset hcard
  have hprob' :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) := by
    simpa using hprob
  exact decode_family_affine_pinning_of_strictCoeffPolysResidual
    (φ := φ) hStrict u hprob' hJ hsqrt P Ecell hsubset hPgood

/-- **Claim-1 capture from strict residual plus a large cell.**  This packages the
cardinality-to-probability adapter in the exact capture-above-threshold shape consumed by
`claim1_dichotomy`: a selected large cell inside `RS_goodCoeffsCurve` supplies the
probability side-condition of the §5 strict residual. -/
theorem hsteps57_of_strictCoeffPolysResidual_cell_card_gt
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hStrict : _root_.ProximityGap.StrictCoeffPolysResidual
      (k := 1) (deg := deg) (domain := φ) (δ := δ))
    (u : Code.WordStack F (Fin 2) ι)
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (_root_.ProximityGap.errorBound δ deg φ : ENNReal) *
      (Fintype.card F : ENNReal) < (Ecell.card : ENNReal))
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) := by
  refine hsteps57_of_decode_family_pinning (domain := φ) (k := deg)
    (δ := δ) (u := u) Ecell T P hdec ?_
  intro _hlarge
  exact decode_family_affine_pinning_of_strictCoeffPolysResidual_cell_card_gt
    (φ := φ) hStrict u hJ hsqrt P Ecell hsubset hcard hPgood

/-- **Claim-1 capture from the large-sector residual plus a large cell.**  This is the
producer-facing form of the large-cell adapter after the small-good-set sector has been
removed. -/
theorem hsteps57_of_strictCoeffPolysLargeResidual_cell_card_gt
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hLarge : _root_.ProximityGap.StrictCoeffPolysLargeResidual
      (k := 1) (deg := deg) (domain := φ) (δ := δ))
    (u : Code.WordStack F (Fin 2) ι)
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (_root_.ProximityGap.errorBound δ deg φ : ENNReal) *
      (Fintype.card F : ENNReal) < (Ecell.card : ENNReal))
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) :=
  hsteps57_of_strictCoeffPolysResidual_cell_card_gt (φ := φ)
    (_root_.ProximityGap.strictCoeffPolysResidual_of_large hLarge)
    u hJ hsqrt P Ecell hsubset hcard hPgood hdec

omit [Nonempty ι] [DecidableEq ι] in
/-- **Affine pinning from raw Guruswami-Sudan cargo.** This is the composed §5 producer
front door: the local-series/Hensel lane turns the raw cargo bundle into the
`StrictCoeffPolysResidual`, and the strict-residual bridge then specializes the
coefficient-polynomial witnesses at `Fin 2` to a single affine pencil on the selected cell. -/
theorem decode_family_affine_pinning_of_rawGSCargo
    {deg : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < deg ∧ v₁.natDegree < deg ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ := by
  exact decode_family_affine_pinning_of_strictCoeffPolysResidual (φ := φ)
    (ArkLib.RawGS304.strictCoeffPolysResidual_of_rawGSCargo
      (k := 1) (deg := deg) (domain := φ) (δ := δ) hInput)
    u hprob hJ hsqrt P Ecell hsubset hPgood

omit [Nonempty ι] [DecidableEq ι] in
/-- **Affine pinning from raw Guruswami-Sudan cargo in the reduced large-sector shape.**
The raw cargo producer may assume `2 < |RS_goodCoeffsCurve|` directly; the small sector is
handled by `StrictCoeffLargeReduction`, and the resulting large residual feeds the same
affine-pinning bridge. -/
theorem decode_family_affine_pinning_of_rawGSCargo_large
    {deg : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      1 + 1 < (_root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u' δ).card →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < deg ∧ v₁.natDegree < deg ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ := by
  exact decode_family_affine_pinning_of_strictCoeffPolysLargeResidual (φ := φ)
    (ArkLib.RawGS304.strictCoeffPolysLargeResidual_of_rawGSCargo
      (k := 1) (deg := deg) (domain := φ) (δ := δ) hInput)
    u hprob hJ hsqrt P Ecell hsubset hPgood

/-- **Claim-1 capture from raw Guruswami-Sudan cargo.** The raw GS cargo bundle is now a
direct producer-facing input for the exact `hsteps57` surface consumed by
`claim1_dichotomy`.  The only remaining content inside this assumption is the explicit cargo:
factor/cell data, cofinite avoidance, the genuine-tail vanishing, and the Claim-5.9
truncated-series reading. -/
theorem hsteps57_of_rawGSCargo
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) := by
  refine hsteps57_of_decode_family_pinning (domain := φ) (k := deg)
    (δ := δ) (u := u) Ecell T P hdec ?_
  intro _hlarge
  exact decode_family_affine_pinning_of_rawGSCargo
    (φ := φ) hInput u hprob hJ hsqrt P Ecell hsubset hPgood

/-- **Claim-1 capture from raw GS cargo in the reduced large-sector shape.** -/
theorem hsteps57_of_rawGSCargo_large
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      1 + 1 < (_root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u' δ).card →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)))
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) := by
  refine hsteps57_of_decode_family_pinning (domain := φ) (k := deg)
    (δ := δ) (u := u) Ecell T P hdec ?_
  intro _hlarge
  exact decode_family_affine_pinning_of_rawGSCargo_large
    (φ := φ) hInput u hprob hJ hsqrt P Ecell hsubset hPgood

omit [Nonempty ι] [DecidableEq ι] in
/-- **Affine pinning from raw GS cargo plus a large cell.** This is the cardinality-facing
producer wrapper: the selected cell supplies the strict-residual probability premise through
`prob_close_curve_gt_of_cell_card_gt`, and the raw cargo supplies the §5 local-series data. -/
theorem decode_family_affine_pinning_of_rawGSCargo_cell_card_gt
    {deg : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (_root_.ProximityGap.errorBound δ deg φ : ENNReal) *
      (Fintype.card F : ENNReal) < (Ecell.card : ENNReal))
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < deg ∧ v₁.natDegree < deg ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ := by
  classical
  have hprob := prob_close_curve_gt_of_cell_card_gt
    (φ := φ) (deg := deg) (δ := δ)
    (η := _root_.ProximityGap.errorBound δ deg φ) u Ecell hsubset hcard
  have hprob' :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) := by
    simpa using hprob
  exact decode_family_affine_pinning_of_rawGSCargo
    (φ := φ) hInput u hprob' hJ hsqrt P Ecell hsubset hPgood

omit [Nonempty ι] [DecidableEq ι] in
/-- **Affine pinning from large-sector raw GS cargo plus a large cell.**  This is the
cardinality-facing version of `decode_family_affine_pinning_of_rawGSCargo_large`: the selected
cell supplies the probability premise, while the cargo producer only has to handle the reduced
large-good-set residual branch. -/
theorem decode_family_affine_pinning_of_rawGSCargo_large_cell_card_gt
    {deg : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      1 + 1 < (_root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u' δ).card →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (_root_.ProximityGap.errorBound δ deg φ : ENNReal) *
      (Fintype.card F : ENNReal) < (Ecell.card : ENNReal))
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < deg ∧ v₁.natDegree < deg ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ := by
  classical
  have hprob := prob_close_curve_gt_of_cell_card_gt
    (φ := φ) (deg := deg) (δ := δ)
    (η := _root_.ProximityGap.errorBound δ deg φ) u Ecell hsubset hcard
  have hprob' :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) := by
    simpa using hprob
  exact decode_family_affine_pinning_of_rawGSCargo_large
    (φ := φ) hInput u hprob' hJ hsqrt P Ecell hsubset hPgood

/-- **Claim-1 capture from raw GS cargo plus a large cell.** This is the closest current
producer-facing K4 surface to the BCIKS20/Haböck Step-5–7 narrative: a concrete large cell
inside the good-coefficient curve set supplies the probability mass, while `RawGSCargo`
contains exactly the local-series/Hensel data still needed by the strict-residual producer. -/
theorem hsteps57_of_rawGSCargo_cell_card_gt
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (_root_.ProximityGap.errorBound δ deg φ : ENNReal) *
      (Fintype.card F : ENNReal) < (Ecell.card : ENNReal))
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) := by
  refine hsteps57_of_decode_family_pinning (domain := φ) (k := deg)
    (δ := δ) (u := u) Ecell T P hdec ?_
  intro _hlarge
  exact decode_family_affine_pinning_of_rawGSCargo_cell_card_gt
    (φ := φ) hInput u hJ hsqrt P Ecell hsubset hcard hPgood

/-- **Claim-1 capture from large-sector raw GS cargo plus a large cell.** -/
theorem hsteps57_of_rawGSCargo_large_cell_card_gt
    {deg T : ℕ} [NeZero deg] (φ : ι ↪ F) {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
          ReedSolomon.code φ deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) *
            (_root_.ProximityGap.errorBound δ deg φ : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg φ →
      1 + 1 < (_root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u' δ).card →
      ∀ P' : F → F[X],
        (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
            (k := 1) (deg := deg) (domain := φ) u' δ,
          (P' z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
        ArkLib.RawGS304.RawGSCargo
          (k := 1) (deg := deg) (domain := φ) (δ := δ) u' P')
    (u : Code.WordStack F (Fin 2) ι)
    (hJ :
      (1 - (LinearCode.rate (ReedSolomon.code φ deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg φ)
    (P : F → F[X]) (Ecell : Finset F)
    (hsubset : Ecell ⊆
      _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ)
    (hcard : (_root_.ProximityGap.errorBound δ deg φ : ENNReal) *
      (Fintype.card F : ENNReal) < (Ecell.card : ENNReal))
    (hPgood : ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
        (k := 1) (deg := deg) (domain := φ) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ φ) ≤ δ)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode φ deg δ u γ, d.P = P γ) :
    T < Ecell.card →
      ∃ a b : F[X], a.natDegree < deg ∧ b.natDegree < deg ∧
        ∀ γ ∈ Ecell, AffineCaptured φ deg δ u γ (a, b) := by
  refine hsteps57_of_decode_family_pinning (domain := φ) (k := deg)
    (δ := δ) (u := u) Ecell T P hdec ?_
  intro _hlarge
  exact decode_family_affine_pinning_of_rawGSCargo_large_cell_card_gt
    (φ := φ) hInput u hJ hsqrt P Ecell hsubset hcard hPgood

open Classical in
/-- **The literal pair-case Johnson conjecture from coefficient-polynomial cells.**
BCIKS-style strict coefficient data says that every coefficient of the decoded family
`Pcell ij γ` is a degree-`< 2` polynomial in the cell parameter `γ`. The curve assembly
theorem `decoded_family_coefficients_of_coeff_polys` therefore specializes to
`Pcell ij γ = v₀ + γ·v₁` on that cell, with both `v₀` and `v₁` of RS degree. This theorem
feeds that affine pinning into the capture-kernel/Claim-1/Hab25 chain and concludes the
literal pair-case Johnson conjecture. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_coeff_polys_cells
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
          (Ecell : Idx → Finset F) (Pcell : Idx → F → F[X]),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
            ∃ d : McaDecode φ (2 ^ m) δ u γ, d.P = Pcell ij γ) ∧
          (∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            (∀ γ ∈ Ecell ij, (Pcell ij γ).natDegree < 2 ^ m) ∧
              ∃ B : ℕ → F[X],
                (∀ j < 2 ^ m, (B j).natDegree < 2) ∧
                  ∀ γ ∈ Ecell ij, ∀ j < 2 ^ m,
                    (Pcell ij γ).coeff j = (B j).eval γ)) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  classical
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  refine mca_johnson_bound_CONJECTURE_pair_of_decode_family_pinning α φ m exp
    hexp0 hexp1 hk L hL ?_
  intro δ hδ0 hδB u
  obtain ⟨Idx, hIdx, Index, Ecell, Pcell, hcard, hcover, hdec, hcoeffData⟩ :=
    hdata δ hδ0 hδB u
  letI : DecidableEq Idx := hIdx
  refine ⟨Idx, inferInstance, Index, Ecell, Pcell, hcard, hcover, hdec, ?_⟩
  intro ij hij hlarge
  obtain ⟨hPdeg, B, hBdeg, hcoeff⟩ := hcoeffData ij hij hlarge
  obtain ⟨A, hAdeg, hP⟩ :=
    _root_.ProximityGap.decoded_family_coefficients_of_coeff_polys
      (l := 0) (deg := 2 ^ m) (S' := Ecell ij) (P := Pcell ij) B
      hBdeg hPdeg hcoeff
  refine ⟨A 0, A 1, hAdeg 0, hAdeg 1, fun γ hγ => ?_⟩
  simpa [Fin.sum_univ_two] using hP γ hγ

end MutualCorrAgreement

/-! ## Axiom audit — all kernel-clean. -/
#print axioms MutualCorrAgreement.rate_genRSC_pair
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_claim1_cells
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_decode_family_pinning
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_decode_family_window
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_fixed_linear_factor_cells
#print axioms MutualCorrAgreement.decode_family_affine_pinning_of_strictCoeffPolysResidual
#print axioms MutualCorrAgreement.decode_family_affine_pinning_of_strictCoeffPolysLargeResidual
#print axioms MutualCorrAgreement.prob_close_curve_gt_of_cell_card_gt
#print axioms MutualCorrAgreement.decode_family_affine_pinning_of_strictCoeffPolysResidual_cell_card_gt
#print axioms MutualCorrAgreement.hsteps57_of_strictCoeffPolysResidual
#print axioms MutualCorrAgreement.hsteps57_of_strictCoeffPolysLargeResidual
#print axioms MutualCorrAgreement.hsteps57_of_strictCoeffPolysResidual_cell_card_gt
#print axioms MutualCorrAgreement.hsteps57_of_strictCoeffPolysLargeResidual_cell_card_gt
#print axioms MutualCorrAgreement.decode_family_affine_pinning_of_rawGSCargo
#print axioms MutualCorrAgreement.decode_family_affine_pinning_of_rawGSCargo_large
#print axioms MutualCorrAgreement.hsteps57_of_rawGSCargo
#print axioms MutualCorrAgreement.hsteps57_of_rawGSCargo_large
#print axioms MutualCorrAgreement.decode_family_affine_pinning_of_rawGSCargo_cell_card_gt
#print axioms MutualCorrAgreement.decode_family_affine_pinning_of_rawGSCargo_large_cell_card_gt
#print axioms MutualCorrAgreement.hsteps57_of_rawGSCargo_cell_card_gt
#print axioms MutualCorrAgreement.hsteps57_of_rawGSCargo_large_cell_card_gt
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_coeff_polys_cells
