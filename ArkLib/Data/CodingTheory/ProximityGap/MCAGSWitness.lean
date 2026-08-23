/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Reducing the GS-exposed Grand MCA conjecture to a named list-decoding bound (Issue #52)

`MCAGS.lean` builds the GS-exposed MCA framework and proves its UDR floor (Steps 1–3), but
leaves the prize-range statement `epsMCAgs_prizeBound_conjecture` as a bare named `Prop`:
its proof *is* the open beyond-UDR GS list-decoder mass bound. The mass bound stays open.

This file does the honest, closeable work the issue asks for:

1. **Reduce the conjecture to a precisely-named GS list-decoding theorem.**
   `epsMCAgsMassBound` names the per-stack beyond-UDR content (each stack's GS-row bad-`γ`
   probability is within the prize RHS), and `epsMCAgs_prizeBound_of_massBound` proves the
   conjecture's existential follows from it by the supremum plumbing. The open content is now
   one explicit hypothesis, not a `sorry`.

2. **Connect the proven Step-3 count to the error.** `MCAGS.gsList_bad_gamma_bound` (the
   `|L|`-pinning of bad `γ`) was proved in isolation; `epsMCAgs_le_listSize_div_of_pivotCovering`
   wires it into an actual `epsMCAgs ≤ |L|/q` bound under the GS-row *pivot-covering* condition
   (each stack has a `u₁`-active coordinate lying in every GS-row bad `γ`'s witness set — the
   shape a genuine GS decoder produces). This makes the mass bound a consequence of a
   list-size + coverage statement, the precisely-named external GS theorem.

3. **Connect to the `GrandChallenges` lower-witness API.** `MCALowerWitness.ofGSMassBound`:
   when a faithful GS family makes `epsMCAgs = epsMCA` (the faithfulness hypothesis, supplied
   in UDR by the singleton bridge) and the mass bound clears `ε*`, the radius is a verified
   `MCALowerWitness` for the actual Grand MCA Challenge.

Everything here is `sorry`-free plumbing; the genuinely open prize content is isolated into the
explicit hypotheses (`epsMCAgsMassBound`, the pivot-covering family, the faithfulness equality).

## References

- [ABF26] §1 Grand MCA Challenge; §4.3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace MCAGS

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step 1: the named per-stack mass bound, and the conjecture reduction -/

/-- **The beyond-UDR GS-row mass bound, as a named per-stack hypothesis.** For each line
stack `u`, the GS-row bad-`γ` probability against the stack's GS list `L u` is within the
target `bound`. This is exactly the per-instance shape a GS list decoder proves; the
conjecture's supremum form is its `iSup`. -/
def epsMCAgsMassBound (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) (bound : ENNReal) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    Pr_{let γ ← $ᵖ F}[mcaEventGSrow (L u) C δ (u 0) (u 1) γ] ≤ bound

/-- **The mass bound bounds the GS-exposed error.** `epsMCAgs` is the supremum of the
per-stack GS-row probabilities, so a uniform per-stack bound bounds it. -/
theorem epsMCAgs_le_of_massBound (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) {bound : ENNReal}
    (h : epsMCAgsMassBound (F := F) C δ L bound) :
    epsMCAgs (F := F) C δ L ≤ bound := by
  unfold epsMCAgs
  exact iSup_le h

/-- The supremum-form GS error bound supplies the uniform per-stack mass-bound hypothesis. -/
theorem epsMCAgsMassBound_of_epsMCAgs_le (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) {bound : ENNReal}
    (h : epsMCAgs (F := F) C δ L ≤ bound) :
    epsMCAgsMassBound (F := F) C δ L bound := by
  intro u
  unfold epsMCAgs at h
  exact le_trans
    (le_iSup (f := fun u : WordStack F (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEventGSrow (L u) C δ (u 0) (u 1) γ]) u) h

/-- Uniform per-stack GS-row mass bounds are exactly the supremum-form `epsMCAgs` bound. -/
theorem epsMCAgsMassBound_iff_epsMCAgs_le (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) {bound : ENNReal} :
    epsMCAgsMassBound (F := F) C δ L bound ↔ epsMCAgs (F := F) C δ L ≤ bound :=
  ⟨epsMCAgs_le_of_massBound C δ L, epsMCAgsMassBound_of_epsMCAgs_le C δ L⟩

/-- Per-stack GS-row mass bounds are monotone in the target bound. -/
theorem epsMCAgsMassBound.mono {C : Set (ι → F)} {δ : ℝ≥0}
    {L : WordStack F (Fin 2) ι → Finset (ι → F)} {bound₁ bound₂ : ENNReal}
    (h : epsMCAgsMassBound (F := F) C δ L bound₁) (hle : bound₁ ≤ bound₂) :
    epsMCAgsMassBound (F := F) C δ L bound₂ := fun u => le_trans (h u) hle

/-- **Reduction of the GS-exposed prize conjecture to the named mass bound (Issue #52 ask 2).**
Given constants `c₁, c₂, c₃` for which the per-stack GS-row mass bound holds at the prize RHS,
the conjecture `epsMCAgs_prizeBound_conjecture` follows. The open beyond-UDR content is now the
single explicit hypothesis `hMass`; the rest is the supremum plumbing. -/
theorem epsMCAgs_prizeBound_of_massBound
    (domain : ι ↪ F) (m : ℕ)
    (c₁ c₂ c₃ : ℝ)
    (hMass : ∀ (j : Fin 4) (η δ : ℝ≥0),
      0 < η → (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
      ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
        epsMCAgsMassBound (F := F)
          ((ReedSolomon.code (domain := domain)
            ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L
          (ENNReal.ofReal
            (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃))) :
    epsMCAgs_prizeBound_conjecture domain m := by
  refine ⟨c₁, c₂, c₃, fun j η δ hη hδ L => ?_⟩
  exact epsMCAgs_le_of_massBound _ _ _ (hMass j η δ hη hδ L)

/-- A GS-exposed prize-conjecture hypothesis unpacks to constants and a per-stack mass bound at
the prize RHS. The conjecture remains an explicit input; this only converts its supremum-shaped
conclusion into the lower-witness API's uniform mass-bound shape. -/
theorem exists_epsMCAgsMassBound_of_prizeBound_conjecture
    (domain : ι ↪ F) (m : ℕ)
    (hPrize : epsMCAgs_prizeBound_conjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η → (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          epsMCAgsMassBound (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L
            (ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)) := by
  rcases hPrize with ⟨c₁, c₂, c₃, hBound⟩
  refine ⟨c₁, c₂, c₃, fun j η δ hη hδ L => ?_⟩
  exact epsMCAgsMassBound_of_epsMCAgs_le _ _ _ (hBound j η δ hη hδ L)

/-! ## Step 2: the Step-3 count, wired into an `epsMCAgs` bound

`gsList_bad_gamma_bound` pins the bad `γ` by `|L|`, but only under the *pivot-covering*
condition: a `u₁`-active coordinate `x` lying in every bad `γ`'s witness set. We package that
condition per stack and turn the count into a probability bound. -/

open Classical in
/-- **Per-stack pivot covering.** Stack `u` has a `u₁`-active coordinate `x` such that every
GS-row bad `γ` carries a list codeword matching the line at `x`. This is the hypothesis under
which the per-`γ` count collapses to the sharp `|L|` (rather than `|L|²·d`); a genuine GS
decoder over the affine pivot produces exactly this. -/
def PivotCovering (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) (u : WordStack F (Fin 2) ι) : Prop :=
  ∃ x : ι, u 1 x ≠ 0 ∧
    ∀ γ : F, mcaEventGSrow (L u) C δ (u 0) (u 1) γ →
      ∃ w ∈ L u, w x = u 0 x + γ * u 1 x

open Classical in
/-- **Step-3 count ⟹ per-stack probability bound.** Under pivot covering, the GS-row bad-`γ`
probability is at most `|L u| / q`. Wires `gsList_bad_gamma_bound` (the `|L|`-pinning) into the
probability. -/
theorem mcaEventGSrow_prob_le_listSize_div (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) (u : WordStack F (Fin 2) ι)
    (hcov : PivotCovering (F := F) C δ L u) :
    Pr_{let γ ← $ᵖ F}[mcaEventGSrow (L u) C δ (u 0) (u 1) γ] ≤
      ((L u).card : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨x, hx, hcover⟩ := hcov
  rw [prob_uniform_eq_card_filter_div_card]
  set S := Finset.univ.filter (fun γ : F => mcaEventGSrow (L u) C δ (u 0) (u 1) γ) with hS
  -- bad-`γ` set injects into the list via the pivot pinning
  have hScard : S.card ≤ (L u).card := by
    refine gsList_bad_gamma_bound (L u) (u 0) (u 1) x hx S ?_
    intro γ hγ
    rw [hS, Finset.mem_filter] at hγ
    exact hcover γ hγ.2
  have hden : (↑(↑(Fintype.card F) : ℝ≥0) : ENNReal) = (↑(Fintype.card F) : ENNReal) := by
    push_cast; rfl
  rw [hden]
  gcongr
  exact_mod_cast hScard

open Classical in
/-- **Step 2 packaged (Issue #52 ask 2): `epsMCAgs ≤ ℓ/q` from a uniform list-size + covering.**
If every stack is pivot-covered and its GS list has size `≤ ℓ`, then the GS-exposed error is at
most `ℓ/q`. This is the GS list-decoder error bound, now a genuine consequence of the proven
Step-3 count — the file previously left them disconnected. -/
theorem epsMCAgs_le_listSize_div_of_pivotCovering (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) (ℓ : ℕ)
    (hcov : ∀ u, PivotCovering (F := F) C δ L u)
    (hsize : ∀ u, (L u).card ≤ ℓ) :
    epsMCAgs (F := F) C δ L ≤ (ℓ : ENNReal) / (Fintype.card F : ENNReal) := by
  unfold epsMCAgs
  refine iSup_le fun u => ?_
  refine le_trans (mcaEventGSrow_prob_le_listSize_div C δ L u (hcov u)) ?_
  gcongr
  exact_mod_cast hsize u

/-- **Mass bound from list-size + covering.** Combines the previous bound with a numeric check
`ℓ/q ≤ bound` to produce the named mass bound — closing the chain
`(GS list size ℓ + covering) ⟹ mass bound ⟹ prize conjecture`. -/
theorem epsMCAgsMassBound_of_pivotCovering (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) (ℓ : ℕ) {bound : ENNReal}
    (hcov : ∀ u, PivotCovering (F := F) C δ L u)
    (hsize : ∀ u, (L u).card ≤ ℓ)
    (hle : (ℓ : ENNReal) / (Fintype.card F : ENNReal) ≤ bound) :
    epsMCAgsMassBound (F := F) C δ L bound := by
  intro u
  refine le_trans (mcaEventGSrow_prob_le_listSize_div C δ L u (hcov u)) (le_trans ?_ hle)
  gcongr
  exact_mod_cast hsize u

/-! ## Step 3: connection to the `GrandChallenges` lower-witness API

A *faithful* GS family makes the GS-exposed error agree with the abstract `ε_mca` (the
singleton bridge supplies this in UDR; in general it is the open list-coverage statement). When
faithfulness holds and the GS error clears `ε*`, the radius is a genuine `MCALowerWitness`. -/

/-- **Faithful GS-list family.** The abstract Grand MCA bad-event probability is bounded by the
GS-exposed bad-event probability for the supplied list family.  This is the named faithfulness
surface that #66 still needs beyond UDR.

The intended proof target is not a naive comparison between the abstract event and the non-row
`mcaEventGS` singleton bridge.  The beyond-UDR route has to normalize the abstract pair witness
to the GS-row event below, then provide list faithfulness for that row witness. -/
def FaithfulGSFamily (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) : Prop :=
  epsMCA (F := F) (A := F) C δ ≤ epsMCAgs (F := F) C δ L

/-- **Pointwise GS-row faithfulness target.** This is the correct event-level target for the
#66 faithfulness proof: every abstract `mcaEvent` for a stack and challenge `γ` must be converted
to the row-normalized GS event against that stack's list.

The hard proof is the row/pair normalization plus list coverage.  This declaration only names the
target in the shape that can be lifted to `FaithfulGSFamily`. -/
def GSRowFaithfulnessTarget (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) : Prop :=
  ∀ u : WordStack F (Fin 2) ι, ∀ γ : F,
    mcaEvent C δ (u 0) (u 1) γ → mcaEventGSrow (L u) C δ (u 0) (u 1) γ

/-- A pointwise row-normalization/list-faithfulness target supplies the global faithful-family
comparison by probability monotonicity and the two worst-case suprema. -/
theorem FaithfulGSFamily.of_rowFaithfulnessTarget (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F))
    (hrow : GSRowFaithfulnessTarget (F := F) C δ L) :
    FaithfulGSFamily (F := F) C δ L := by
  unfold FaithfulGSFamily epsMCA epsMCAgs
  refine iSup_le fun u => ?_
  refine le_trans (Pr_le_Pr_of_implies _ _ _ (hrow u)) ?_
  exact le_iSup
    (fun u : WordStack F (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEventGSrow (L u) C δ (u 0) (u 1) γ]) u

/-- A faithful GS family plus a GS mass bound bounds the actual Grand MCA error. -/
theorem epsMCA_le_of_faithful_mass (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) {bound : ENNReal}
    (hfaithful : FaithfulGSFamily (F := F) C δ L)
    (hMass : epsMCAgsMassBound (F := F) C δ L bound) :
    epsMCA (F := F) (A := F) C δ ≤ bound :=
  le_trans hfaithful (epsMCAgs_le_of_massBound _ _ _ hMass)

/-- **Lower witness from a faithful GS mass bound (Issue #52 ask 3).** If a GS family `L` is
faithful at radius `δ` (`epsMCA ≤ epsMCAgs` — the abstract error is captured by the GS-exposed
one) and the mass bound clears `ε*`, then `δ` is a verified `MCALowerWitness` for the actual
Grand MCA Challenge: `δ* ≥ δ`. The faithfulness hypothesis is the precisely-named open content
(discharged in UDR by `mcaEventGS_singleton_eq_mcaEvent_udr`). -/
def MCALowerWitness.ofGSMassBound (C : LinearCode ι F) (δ ε_star : ℝ≥0)
    (hδ : δ ≤ 1)
    (L : WordStack F (Fin 2) ι → Finset (ι → F))
    (hfaithful : epsMCA (F := F) (A := F) (C : Set (ι → F)) δ ≤
      epsMCAgs (F := F) (C : Set (ι → F)) δ L)
    (hMass : epsMCAgsMassBound (F := F) (C : Set (ι → F)) δ L (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (C : Set (ι → F)) ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ
    (le_trans hfaithful (epsMCAgs_le_of_massBound _ _ _ hMass))

/-- Packaged #66 frontier for turning a faithful GS mass bound into a lower witness.

The fields are exactly the remaining open inputs at this layer: a GS list family, its
faithfulness comparison to the abstract MCA event, and its mass bound at `ε*`. -/
structure GSMassLowerWitnessFrontier (C : LinearCode ι F) (δ ε_star : ℝ≥0) where
  listFamily : WordStack F (Fin 2) ι → Finset (ι → F)
  faithful : FaithfulGSFamily (F := F) (C : Set (ι → F)) δ listFamily
  mass : epsMCAgsMassBound (F := F) (C : Set (ι → F)) δ listFamily (ε_star : ENNReal)

/-- Reassemble a Grand MCA lower witness from the packaged GS mass frontier. -/
def MCALowerWitness.ofGSMassFrontier (C : LinearCode ι F) (δ ε_star : ℝ≥0)
    (hδ : δ ≤ 1)
    (frontier : GSMassLowerWitnessFrontier (F := F) C δ ε_star) :
    GrandChallenges.MCALowerWitness (C : Set (ι → F)) ε_star :=
  MCALowerWitness.ofGSMassBound C δ ε_star hδ
    frontier.listFamily frontier.faithful frontier.mass

/-- Packaged #66 pivot/list-size frontier for producing a faithful GS mass frontier.

This keeps the remaining GS decoder obligations visible as hypotheses: a uniform list-size
bound, pivot coverage for every stack, faithfulness against the abstract MCA event, and the
numeric check that the resulting `ℓ / |F|` mass clears `ε*`. -/
structure GSPivotLowerWitnessFrontier (C : LinearCode ι F) (δ ε_star : ℝ≥0) where
  listFamily : WordStack F (Fin 2) ι → Finset (ι → F)
  listSize : ℕ
  faithful : FaithfulGSFamily (F := F) (C : Set (ι → F)) δ listFamily
  covering : ∀ u, PivotCovering (F := F) (C : Set (ι → F)) δ listFamily u
  sizeBound : ∀ u, (listFamily u).card ≤ listSize
  clearsTarget : (listSize : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)

/-- The pivot/list-size frontier supplies the mass frontier consumed by the lower-witness API. -/
def GSPivotLowerWitnessFrontier.toGSMassLowerWitnessFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0)
    (frontier : GSPivotLowerWitnessFrontier (F := F) C δ ε_star) :
    GSMassLowerWitnessFrontier (F := F) C δ ε_star where
  listFamily := frontier.listFamily
  faithful := frontier.faithful
  mass := epsMCAgsMassBound_of_pivotCovering
    (F := F) (C := (C : Set (ι → F))) δ frontier.listFamily frontier.listSize
    frontier.covering frontier.sizeBound frontier.clearsTarget

/-- A faithful pivot/list-size frontier bounds the actual Grand MCA error by `ε*`. -/
theorem epsMCA_le_of_pivot_frontier (C : LinearCode ι F) (δ ε_star : ℝ≥0)
    (frontier : GSPivotLowerWitnessFrontier (F := F) C δ ε_star) :
    epsMCA (F := F) (A := F) (C : Set (ι → F)) δ ≤ (ε_star : ENNReal) :=
  epsMCA_le_of_faithful_mass (F := F) (C := (C : Set (ι → F))) δ frontier.listFamily
    frontier.faithful
    (GSPivotLowerWitnessFrontier.toGSMassLowerWitnessFrontier C δ ε_star frontier).mass

/-- Reassemble a Grand MCA lower witness from the packaged pivot/list-size frontier. -/
def MCALowerWitness.ofGSPivotFrontier (C : LinearCode ι F) (δ ε_star : ℝ≥0)
    (hδ : δ ≤ 1)
    (frontier : GSPivotLowerWitnessFrontier (F := F) C δ ε_star) :
    GrandChallenges.MCALowerWitness (C : Set (ι → F)) ε_star :=
  MCALowerWitness.ofGSMassFrontier C δ ε_star hδ
    (GSPivotLowerWitnessFrontier.toGSMassLowerWitnessFrontier C δ ε_star frontier)

/-! ## Source audit for the faithful GS mass and pivot-frontier layers -/

#print axioms FaithfulGSFamily
#print axioms GSRowFaithfulnessTarget
#print axioms FaithfulGSFamily.of_rowFaithfulnessTarget
#print axioms epsMCAgsMassBound_of_epsMCAgs_le
#print axioms epsMCAgsMassBound_iff_epsMCAgs_le
#print axioms epsMCAgsMassBound.mono
set_option linter.style.longLine false in
#print axioms exists_epsMCAgsMassBound_of_prizeBound_conjecture
#print axioms epsMCA_le_of_faithful_mass
#print axioms MCALowerWitness.ofGSMassBound
#print axioms GSMassLowerWitnessFrontier
#print axioms MCALowerWitness.ofGSMassFrontier
#print axioms GSPivotLowerWitnessFrontier
#print axioms GSPivotLowerWitnessFrontier.toGSMassLowerWitnessFrontier
#print axioms epsMCA_le_of_pivot_frontier
#print axioms MCALowerWitness.ofGSPivotFrontier

end MCAGS

end ProximityGap
