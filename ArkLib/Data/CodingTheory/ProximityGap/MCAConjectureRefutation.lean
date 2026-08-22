/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBoundsProofs

/-!
# Refuting the ABF26 §4.5 MCA conjecture from the CS25 complete-CA-breakdown (#141 / #232)

`GrandChallenges.mcaConjecture` asserts a uniform polynomial upper bound
`ε_mca(C,δ) ≤ (1/|F|)·n^{c₁}/(ρ^{c₂}·η^{c₃})` (`η = 1−ρ−δ`), with the constants `(c₁,c₂,c₃)`
quantified **before** the `∀` over Reed–Solomon codes.

This file gives the **verified disproof skeleton**: since `ε_mca ≥ ε_ca` (`epsCA_le_epsMCA`), a
complete correlated-agreement breakdown (`1 ≤ ε_ca`, i.e. CS25 Cor 1 / ABF26 Thm 4.17) at a radius
`δ < 1−ρ` where the conjecture's *own* polynomial bound is `< 1` contradicts the conjectured upper
bound on `ε_mca`.

* `CS25BreakdownBelowConjectureBound` — the precise condition: for **every** choice of the
  conjecture's constants there is an RS code + radius with `1 ≤ ε_ca` and conjecture-bound `< 1`.
* `not_mcaConjecture_of_cs25BreakdownBelowBound` — **`CS25BreakdownBelowConjectureBound → ¬ mcaConjecture`**,
  axiom-clean.
* `cs25BreakdownBelowBound_of_breakdownFamily` — reduces that condition to the existing in-repo CS25
  admit `rs_epsCA_breakdown_cs25` together with the *quantitative regime* `bound < 1` (large field,
  entropy band). Hence the only remaining gap to an **unconditional** in-Lean disproof of
  `mcaConjecture` is (a) porting CS25's `ε_ca = 1` lower bound (the `qEntropy ↔ RS-ball-count` bridge,
  flagged as the missing ingredient in `CapacityBounds`) and (b) the regime check `bound < 1`.

**Honest status.** This is *not* an unconditional disproof: the CS25 breakdown (`1 ≤ ε_ca`) is an
external admit, not yet ported. What is proven here, axiom-clean, is that the breakdown — a
literature-established result — **does** refute the conjecture, and exactly what quantitative form it
must take. The earlier `MCAThresholdLedger.candidate_uptocapacity_REFUTED` refutes only the *naive*
constant-bound up-to-capacity form (small-field `constCode`); this reduction targets the genuine
polynomial conjecture.
-/

open scoped NNReal ENNReal

namespace ProximityGap.GrandChallenges

/-- **The precise condition under which CS25's complete-CA-breakdown refutes `mcaConjecture`.**
For EVERY choice of the conjecture's polynomial constants `(c₁,c₂,c₃)` there is a Reed–Solomon code
and a radius `δ < 1 − ρ` at which correlated agreement breaks down (`1 ≤ ε_ca`) while the conjecture's
own bound is `< 1`. -/
def CS25BreakdownBelowConjectureBound : Prop :=
  ∀ c₁ c₂ c₃ : ℝ,
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
      0 < k ∧
      (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC ∧
      1 ≤ epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ δ ∧
      mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃ < 1

/-- **The ABF26 §4.5 MCA conjecture is FALSE given the CS25 breakdown reaches below its bound.**
Since `ε_mca ≥ ε_ca` (`epsCA_le_epsMCA`), a complete CA breakdown (`1 ≤ ε_ca`) at a radius where the
conjecture's polynomial bound is `< 1` immediately contradicts the conjectured upper bound on `ε_mca`.
This reduces the disproof of `mcaConjecture` to the (literature-established) CS25 near-capacity
breakdown in the large-field regime. Axiom-clean. -/
theorem not_mcaConjecture_of_cs25BreakdownBelowBound
    (H : CS25BreakdownBelowConjectureBound) : ¬ mcaConjecture := by
  rintro ⟨c₁, c₂, c₃, hconj⟩
  obtain ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ, hk, hδ, hca, hbnd⟩ := H c₁ c₂ c₃
  letI := hFι; letI := hNι; letI := hDι; letI := hFld; letI := hFF; letI := hDF
  have hge := le_trans hca (epsCA_le_epsMCA _ δ)
  have hle := hconj domain k δ hk hδ
  have hlt : ENNReal.ofReal
      (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) < 1 :=
    ENNReal.ofReal_lt_one.mpr hbnd
  exact absurd (lt_of_le_of_lt (le_trans hge hle) hlt) (lt_irrefl 1)

/-- Reduce `CS25BreakdownBelowConjectureBound` to the existing in-repo CS25 admit
`rs_epsCA_breakdown_cs25` (which yields `ε_ca = 1` in its entropy band) together with the quantitative
regime hypotheses (`δ < 1−ρ`, `0 < k`, `bound < 1`).  This isolates the remaining gap to an
unconditional disproof: porting CS25's `ε_ca = 1` lower bound plus checking the band sits below the
polynomial bound for a sufficiently large field. -/
theorem cs25BreakdownBelowBound_of_breakdownFamily
    (W : ∀ c₁ c₂ c₃ : ℝ,
        ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
          (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
          (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
          0 < k ∧
          (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC ∧
          epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ δ = 1 ∧
          mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃ < 1) :
    CS25BreakdownBelowConjectureBound := by
  intro c₁ c₂ c₃
  obtain ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ, hk, hδ, hca1, hbnd⟩ := W c₁ c₂ c₃
  exact ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ, hk, hδ, hca1.ge, hbnd⟩

/-!
## Wiring to the single named external Prop

The reduction above (`cs25BreakdownBelowBound_of_breakdownFamily`) consumes an anonymous family
hypothesis bundling *both* the CS25 breakdown and the quantitative regime. The declarations below
split that family into its two honest ingredients, following the `ExternalDebt.lean` convention
(named `Prop` residual + proven `_of_residuals` reduction):

1. `CS25BreakdownLowerResidualUniversal` — the **external** input: the universal (over the
   domain/field types) form of `CodingTheory.cs25_rs_epsCA_breakdown_lower_residual`
   (CapacityBoundsProofs, T4.17 / Issue #82), i.e. CS25 Corollary 1's hard `1 ≤ ε_ca` half in the
   entropy band. This is the *only* paper-level gap.
2. `CS25BandInstanceBelowConjectureBound` — the **regime** input: for every choice of the
   conjecture's constants there is an RS instance inside the CS25 entropy band, strictly below
   capacity, whose conjecture bound is `< 1`. This is number-theoretic bookkeeping (pick `δ` with
   `H_q(δ) > 1 − ρ` but `δ < 1 − ρ`, then grow `|F|` until `n^{c₁}/(|F|·ρ^{c₂}·η^{c₃}) < 1`) and is
   in principle provable in tree; it is kept as a named Prop until that arithmetic is formalized.

`not_mcaConjecture_of_bandInstances_and_cs25Lower` then derives `¬ mcaConjecture` from exactly
these two named Props, with the `ε_ca = 1 ⇒ 1 ≤ ε_mca` glue and the `≤ 1` half of the breakdown
(`rs_epsCA_breakdown_cs25_of_lower_bound`) all proven in tree.
-/

/-- **The single external input (CS25, Corollary 1).** Universal-over-types form of
`CodingTheory.cs25_rs_epsCA_breakdown_lower_residual`: for every finite RS instance in the CS25
entropy band, the hard `1 ≤ ε_ca` lower half of the complete CA breakdown holds. -/
def CS25BreakdownLowerResidualUniversal : Prop :=
  ∀ (ιC : Type) (iFι : Fintype ιC) (iNι : Nonempty ιC) (iDι : DecidableEq ιC)
    (FC : Type) (iFld : Field FC) (iFF : Fintype FC) (iDF : DecidableEq FC),
    letI := iFι; letI := iNι; letI := iDι; letI := iFld; letI := iFF; letI := iDF
    CodingTheory.cs25_rs_epsCA_breakdown_lower_residual (ι := ιC) (F := FC)

/-- **The quantitative regime input.** For every choice of the conjecture's polynomial constants
`(c₁,c₂,c₃)` there is an RS instance lying inside the CS25 entropy band (so the external breakdown
applies), strictly below capacity (`δ < 1 − ρ`), with the conjecture's own bound `< 1`. Purely
arithmetic/number-theoretic; no proximity-gaps content. -/
def CS25BandInstanceBelowConjectureBound : Prop :=
  ∀ c₁ c₂ c₃ : ℝ,
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
      0 < k ∧
      (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC ∧
      10 ≤ Fintype.card FC ∧
      (1 - CodingTheory.qEntropy (Fintype.card FC) (δ : ℝ) + 2 / (Fintype.card ιC : ℝ)
          + ((CodingTheory.qEntropy (Fintype.card FC) (δ : ℝ) - (δ : ℝ))
              / (Fintype.card ιC : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / Fintype.card ιC) ∧
      ((k : ℝ) / Fintype.card ιC ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ιC : ℝ)) ∧
      mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃ < 1

/-- The band-instance regime plus the universal CS25 lower residual discharge
`CS25BreakdownBelowConjectureBound`. Axiom-clean; the only unproven inputs are the two named
hypotheses. -/
theorem cs25BreakdownBelowBound_of_bandInstances
    (hBand : CS25BandInstanceBelowConjectureBound)
    (hCS25 : CS25BreakdownLowerResidualUniversal) :
    CS25BreakdownBelowConjectureBound := by
  intro c₁ c₂ c₃
  obtain ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ,
    hk, hδ, hq, hlo, hhi, hbnd⟩ := hBand c₁ c₂ c₃
  letI := hFι; letI := hNι; letI := hDι; letI := hFld; letI := hFF; letI := hDF
  exact ⟨ιC, hFι, hNι, hDι, FC, hFld, hFF, hDF, domain, k, δ, hk, hδ,
    hCS25 ιC hFι hNι hDι FC hFld hFF hDF domain k δ hq hlo hhi, hbnd⟩

/-- **`¬ mcaConjecture` from exactly two named Props**: the external CS25 Cor-1 lower residual and
the arithmetic regime check. All other glue is proven in tree. -/
theorem not_mcaConjecture_of_bandInstances_and_cs25Lower
    (hBand : CS25BandInstanceBelowConjectureBound)
    (hCS25 : CS25BreakdownLowerResidualUniversal) :
    ¬ mcaConjecture :=
  not_mcaConjecture_of_cs25BreakdownBelowBound
    (cs25BreakdownBelowBound_of_bandInstances hBand hCS25)

#print axioms not_mcaConjecture_of_cs25BreakdownBelowBound
#print axioms cs25BreakdownBelowBound_of_breakdownFamily
#print axioms cs25BreakdownBelowBound_of_bandInstances
#print axioms not_mcaConjecture_of_bandInstances_and_cs25Lower

end ProximityGap.GrandChallenges
