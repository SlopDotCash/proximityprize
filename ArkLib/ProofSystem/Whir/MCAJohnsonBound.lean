/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Whir.MCAConjecturePairReduction
import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.LocalSeriesProducer
import ArkLib.Data.CodingTheory.ProximityGap.Hab25K4FiberReduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25GradedNumericEdge

/-!
# Johnson MCA Bound Wiring

This file records issue-facing compositions for the literal pair-case
`mca_johnson_bound_CONJECTURE`.  The raw-cargo route still carries explicit cell-production
data, while the graded route packages the remaining factor-cell K4 statement and composes it
with the proved Johnson-budget arithmetic.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped BigOperators ENNReal ProbabilityTheory Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def johnsonConjectureEta (n k : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  (min (1 - Real.sqrt ((k : ℝ) / (n : ℝ)) - (δ : ℝ))
    (Real.sqrt ((k : ℝ) / (n : ℝ)) / 20)).toNNReal

/-- The remaining factor-cell K4 surface consumed by the graded Johnson numeric edge.

**Classification (#351 audit, 2026-06-11): honest open research** — a cell-cardinality
bound on the decode loci of one irreducible factor of the Guruswami–Sudan interpolant,
the K4 leg of the `mca_johnson_bound_CONJECTURE` campaign (#334, successor to #232; the
BCIKS20/GS open cores are tracked at #304).  Conditionally reduced to
`K4ComponentResidual` by `K4GradedFactorCellResidual_of_component` below; no in-tree
producer exists and none should be fabricated. -/
def K4GradedFactorCellResidual {n : ℕ} [NeZero n]
    (φ : Fin n ↪ F) (k gsMult : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ (u : Code.WordStack F (Fin 2) (Fin n)) (E : Finset F) (P : F → F[X])
    (R : Polynomial (Polynomial (Polynomial F))),
    Irreducible R →
    (∀ γ ∈ E, ∃ d : McaDecode φ k δ u γ, d.P = P γ) →
    (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
    E.card ≤ n * (GuruswamiSudan.constraintIndices gsMult).card *
      (gs_degree_bound k n gsMult / (k - 1))

/-- The deeper per-component K4 surface after taking one good fiber of the factor cell.

**Classification (#351 audit, 2026-06-11): honest open research** — the per-fiber form of
`K4GradedFactorCellResidual` (one good fiber `x₀` of the interpolant factor), the deepest
open core of the Johnson-bound campaign (#334; BCIKS20/GS cores at #304).  Known
obstruction: the fiber-counting step wants Weil-grade input on curves that Mathlib lacks
(see the #232 round-8 coset-wall record).  No in-tree producer; do not fabricate. -/
def K4ComponentResidual {n : ℕ} [NeZero n]
    (φ : Fin n ↪ F) (k gsMult : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ (u : Code.WordStack F (Fin 2) (Fin n)) (E : Finset F) (P : F → F[X])
    (R : Polynomial (Polynomial (Polynomial F))),
    Irreducible R →
    (∀ γ ∈ E, ∃ d : McaDecode φ k δ u γ, d.P = P γ) →
    (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
    ∃ (x₀ : F) (T' T₀ : ℕ),
      fiberAt x₀ R ≠ 0 ∧
      (∀ S : Finset F,
        (∀ γ ∈ S, (fiberAt x₀ R).map (Polynomial.evalRingHom γ) = 0) →
        S.card ≤ T₀) ∧
      (∀ E' : Finset F, E' ⊆ E →
        ∀ H, H ∈ UniqueFactorizationMonoid.factors (fiberAt x₀ R) →
        (∀ γ ∈ E', ((H.map (Polynomial.evalRingHom γ)).eval ((P γ).eval x₀) = 0)) →
        E'.card ≤ T') ∧
      ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) * max T' T₀ ≤
        n * (GuruswamiSudan.constraintIndices gsMult).card *
          (gs_degree_bound k n gsMult / (k - 1))

/-- A per-component fiber K4 statement implies the factor-cell K4 surface consumed by the
graded numeric edge. -/
theorem K4GradedFactorCellResidual_of_component {n k gsMult : ℕ} [NeZero n]
    (φ : Fin n ↪ F) (δ : ℝ≥0)
    (hcomponent : K4ComponentResidual φ k gsMult δ) :
    K4GradedFactorCellResidual φ k gsMult δ := by
  intro u E P R hirr hdec hdvd
  obtain ⟨x₀, T', T₀, hfib, hdegT, hK4H, hbudget⟩ :=
    hcomponent u E P R hirr hdec hdvd
  exact le_trans
    (cell_card_le_of_component_K4_pair R x₀ E P T' T₀ hfib hdec hdvd hdegT hK4H)
    hbudget

#print axioms MutualCorrAgreement.K4GradedFactorCellResidual_of_component

open Classical in
/-- The literal pair-case Johnson MCA bound from the two current producer branches.

Raw Guruswami-Sudan cargo by itself does not decompose the bad scalars into cells. This
composition theorem therefore keeps the producer-facing cell data explicit: every large cell
is discharged either by the unique-decoding/window capture kernel, or by the strict-branch
raw-GS cargo plus the large-cell probability adapter. -/
theorem mca_johnson_bound_CONJECTURE_holds_of_rawGSCargo
    (α : F) (φ : ι ↪ F) (m : ℕ) [ReedSolomon.Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hInput : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
            ReedSolomon.code φ (2 ^ m)) ≤ δ] >
            (((1 : ℕ) : ENNReal) *
              (_root_.ProximityGap.errorBound δ (2 ^ m) φ : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code φ (2 ^ m)) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate (2 ^ m) φ →
        ∀ P' : F → F[X],
          (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
              (k := 1) (deg := 2 ^ m) (domain := φ) u' δ,
            (P' z).natDegree < 2 ^ m ∧
              δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
          ArkLib.RawGS304.RawGSCargo
            (k := 1) (deg := 2 ^ m) (domain := φ) (δ := δ) u' P')
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
          ∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            (2 * Fintype.card ι + 2 ^ m ≤
              3 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) ∨
            ((1 - (LinearCode.rate (ReedSolomon.code φ (2 ^ m)) : ℝ≥0)) / 2 < δ ∧
              δ < 1 - ReedSolomon.sqrtRate (2 ^ m) φ ∧
              Ecell ij ⊆ _root_.ProximityGap.RS_goodCoeffsCurve
                (k := 1) (deg := 2 ^ m) (domain := φ) u δ ∧
              (_root_.ProximityGap.errorBound δ (2 ^ m) φ : ENNReal) *
                (Fintype.card F : ENNReal) < ((Ecell ij).card : ENNReal) ∧
              ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
                  (k := 1) (deg := 2 ^ m) (domain := φ) u δ,
                (Pcell ij z).natDegree < 2 ^ m ∧
                  δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
                    (Pcell ij z).eval ∘ φ) ≤ δ)) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  classical
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  refine mca_johnson_bound_CONJECTURE_pair_of_claim1_cells α φ m exp hexp0 hexp1 hk L hL ?_
  intro δ hδ0 hδB u
  obtain ⟨Idx, hIdx, Index, Ecell, Pcell, hcard, hcover, hdec, hcell⟩ :=
    hdata δ hδ0 hδB u
  letI : DecidableEq Idx := hIdx
  refine ⟨Idx, Index, Ecell, hcard, hcover, ?_⟩
  intro ij hij hlarge
  rcases hcell ij hij hlarge with hwin | hstrict
  · have hkpos : 0 < 2 ^ m := by positivity
    exact hsteps57_of_window (domain := φ) (k := 2 ^ m) (δ := δ) (u := u)
      hkpos (Ecell ij) (T := Fintype.card ι) Fintype.card_pos (Pcell ij)
      (hdec ij hij) hwin hlarge
  · rcases hstrict with ⟨hJ, hsqrt, hsubset, hlargeCell, hPgood⟩
    exact hsteps57_of_rawGSCargo_cell_card_gt (deg := 2 ^ m) (T := Fintype.card ι)
      (φ := φ) (hInput δ hδ0 hδB) u hJ hsqrt (Pcell ij) (Ecell ij)
      hsubset hlargeCell hPgood (hdec ij hij) hlarge

#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_holds_of_rawGSCargo

/-- The literal pair-case Johnson MCA bound from the closed graded K4 seam.

This is the WHIR-facing capstone of the current GS cell-production lane for domains already
indexed by `Fin n`: the graded numeric edge proves all Johnson-budget arithmetic, so the
only remaining mathematical input is the true factor-cell K4 statement.  The theorem keeps
the Guruswami-Sudan multiplicity as a per-radius choice `gsMult`; `hMult` says it is exactly
the Hab25 multiplicity at the conjecture's `η(δ) = min(1 - sqrt(ρ) - δ, sqrt(ρ) / 20)`. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_K4_graded_closed
    {n whirM : ℕ} [NeZero n]
    (α : F) (φ : Fin n ↪ F) [ReedSolomon.Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (gsMult : ℝ≥0 → ℕ)
    (hk7 : 7 ≤ 2 ^ whirM)
    (hkn : 2 ^ whirM + 1 ≤ n)
    (hρ : Real.sqrt (((2 ^ whirM : ℕ) : ℝ) / (n : ℝ)) ≤ 9 / 10)
    (hMult : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ whirM : ℝ) / (n : ℝ)) →
      (gsMult δ : ℝ) =
        hab25M n (2 ^ whirM) (johnsonConjectureEta n (2 ^ whirM) δ))
    (hδJ : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ whirM : ℝ) / (n : ℝ)) →
      (δ : ℝ) < gs_johnson (2 ^ whirM) n (gsMult δ))
    (hK4 : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ whirM : ℝ) / (n : ℝ)) →
      K4GradedFactorCellResidual φ (2 ^ whirM) (gsMult δ) δ) :
    mca_johnson_bound_CONJECTURE α φ whirM (Fin 2) exp := by
  classical
  refine mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound α φ whirM exp
    hexp0 hexp1 (by rw [Fintype.card_fin]; omega) ?_
  intro δ hδ0 hδB
  have hδBn :
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ whirM : ℝ) / (n : ℝ)) := by
    simpa using hδB
  have hδ1 : δ ≤ 1 := by
    have hδR : (δ : ℝ) ≤ 1 := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt ((2 ^ whirM : ℝ) / (n : ℝ)) :=
        Real.sqrt_nonneg _
      linarith
    exact_mod_cast hδR
  have hgsMultPos : 1 ≤ gsMult δ := by
    have hge : (1 : ℝ) ≤ (gsMult δ : ℝ) := by
      have hM3 :
          (3 : ℝ) ≤
            hab25M n (2 ^ whirM) (johnsonConjectureEta n (2 ^ whirM) δ) :=
        hab25M_ge_three n (2 ^ whirM) _
      rw [hMult δ hδ0 hδBn]
      linarith
    exact_mod_cast hge
  have hK4δ :
      ∀ (u : Code.WordStack F (Fin 2) (Fin n)) (E : Finset F) (P : F → F[X])
        (R : Polynomial (Polynomial (Polynomial F))),
        Irreducible R →
        (∀ γ ∈ E, ∃ d : McaDecode φ (2 ^ whirM) δ u γ, d.P = P γ) →
        (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
        E.card ≤ n * (GuruswamiSudan.constraintIndices (gsMult δ)).card *
          (gs_degree_bound (2 ^ whirM) n (gsMult δ) / (2 ^ whirM - 1)) := by
    simpa [K4GradedFactorCellResidual] using hK4 δ hδ0 hδBn
  have hJ := johnsonNumericBound_of_K4_graded_closed (domain := φ)
    (η := johnsonConjectureEta n (2 ^ whirM) δ) (δ := δ) hk7 hkn hgsMultPos hρ
    (hMult δ hδ0 hδBn) hδ1 (hδJ δ hδ0 hδBn) hK4δ
  simpa [johnsonConjectureEta] using hJ

#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_K4_graded_closed

end MutualCorrAgreement
