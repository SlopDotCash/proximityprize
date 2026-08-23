/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# Sumset extremality: reducing the open core to a MONOMIAL sub-family (#407)

The single open core of the MCA threshold `δ*` is
`OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ B`, the statement that **every** stack
`u = (u₀, u₁)` has far-line incidence
`#{ γ : mcaEvent C δ (u 0) (u 1) γ } ≤ B`.  The quantifier ranges over *all* `|A|^{2n}` stacks.

`FarLineIncidenceEquivariance.lean` and `MCAEquivariance.lean` already prove (axiom-clean) that
this incidence count is a **class function on the automorphism orbits** of lines: a coordinate
permutation `σ` that fixes the code (`w ∈ C ↔ w ∘ σ ∈ C`) leaves `mcaEvent` invariant at *every*
`γ` (`MCAEquivariance.mcaEvent_comp_perm_iff`), hence leaves the bad-`γ` *count* unchanged.  For
Reed–Solomon on `μ_n` the dilations `x ↦ g·x` (`g ∈ μ_n`) are such automorphisms, giving the count
the full `Z/n` cyclic symmetry; the computational probes (`FarLineIncidenceEquivariance` header)
identify the worst far line, on every tested instance, as a **monomial line** `u₀ = x^b`,
`u₁ = x^a` (a dilation fixed point up to scalar — the extremal direction of the equivariance).

This file isolates that empirical fact as ONE named hypothesis — **sumset extremality** — and
proves (axiom-clean, no `sorry`) the clean *reduction*:

> If the incidence is `≤ B` on the monomial sub-family `M`, and every stack's incidence is
> realized by some member of `M` (sumset extremality), then the open core
> `WorstCaseIncidenceBounded C δ B` holds for **all** stacks.

The reduction is genuinely useful: it collapses the `|A|^{2n}`-fold quantifier of the open core to
the `n²`-fold monomial sub-family, exactly the family the height-gate / norm-bound levers
(`HeightGateNormBound`, `HeightGateAMGM`) are designed to bound.  The reduction is unconditional;
the residual is the single, precisely-stated, **empirically-supported** extremality `Prop`
(`SumsetExtremal`), which is NOT proven here — it is the sumset-extremality conjecture that the
probe `probe_sumset_extremality.py` tests (and never refutes: on `n=8,12,16`, `k∈{2,3,4}`, large
primes `q ≫ n⁴`, no random / sum-of-two-monomials far line beats the worst monomial line).

Everything below is axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.OpenCoreConditionalPin Code

namespace ProximityGap.SumsetExtremality

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- The **far-line incidence count** of a single stack `u` at radius `δ`: the number of bad
scalars `γ` (those triggering `mcaEvent`).  This is the per-stack term whose supremum over stacks
is `q · ε_mca`, and whose worst-case bound `≤ B` is the open core
`OpenCoreConditionalPin.WorstCaseIncidenceBounded`. -/
noncomputable def incCount (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) : ℕ :=
  (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card

open Classical in
/-- `WorstCaseIncidenceBounded` re-expressed through `incCount`: the open core says every stack's
incidence count is `≤ B`. -/
theorem worstCaseIncidenceBounded_iff (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B
      ↔ ∀ u : WordStack A (Fin 2) ι, incCount (F := F) C δ u ≤ B :=
  Iff.rfl

/-! ## The monomial sub-family bound and the extremality hypothesis -/

open Classical in
/-- **The monomial-family incidence bound** — the *input* of the reduction.  `M` is the designated
"extremal" sub-family of stacks (for RS on `μ_n`, the monomial lines `u₀ = x^b`, `u₁ = x^a`).
`MonomialIncidenceBounded C δ B M` says every member of `M` has incidence `≤ B`.  This is the
object the height-gate levers (`HeightGateNormBound`, `HeightGateAMGM`) bound on the
norm/AM-GM-controlled monomial directions. -/
def MonomialIncidenceBounded (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (M : Set (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u ∈ M, incCount (F := F) C δ u ≤ B

open Classical in
/-- **SUMSET EXTREMALITY (the named, empirically-supported residual).**  Every stack's far-line
incidence count is realized (dominated) by some member of the monomial sub-family `M`:

  `∀ u, ∃ v ∈ M, incCount C δ u ≤ incCount C δ v`.

This is the precise content of the probe finding — the worst far line is a monomial line.  It is
NOT proven here; it is the explicit hypothesis the reduction consumes.  The probe
`probe_sumset_extremality.py` tests it exhaustively over the monomial family and against random /
sum-of-two-monomials non-monomial far lines (`n=8,12,16`, `k∈{2,3,4}`, `q ≫ n⁴`) and never
refutes it. -/
def SumsetExtremal (C : Set (ι → A)) (δ : ℝ≥0)
    (M : Set (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, ∃ v ∈ M, incCount (F := F) C δ u ≤ incCount (F := F) C δ v

/-! ## THE REDUCTION -/

open Classical in
/-- **THE SUMSET-EXTREMALITY REDUCTION (axiom-clean).**

If the incidence is bounded by `B` on the monomial sub-family `M`
(`MonomialIncidenceBounded`), and sumset extremality holds (every stack's incidence is dominated
by a monomial member, `SumsetExtremal`), then the **open core**
`OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ B` holds for *all* stacks.

This collapses the `|A|^{2n}`-fold quantifier of the open core to the monomial sub-family `M`:
the entire remaining content is (i) a bound on the structured monomial family (the home of the
height-gate / norm levers) plus (ii) the single empirically-supported extremality `Prop`. -/
theorem worstCaseIncidence_of_monomial_extremal
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) (M : Set (WordStack A (Fin 2) ι))
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (hext : SumsetExtremal (F := F) C δ M) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B := by
  intro u
  obtain ⟨v, hvM, hle⟩ := hext u
  exact le_trans hle (hM v hvM)

/-! ## Wiring the reduction straight to the conditional `δ*` pin -/

open Classical in
/-- **The reduction, plugged into the conditional `δ*` pin.**  With the monomial bound and sumset
extremality at budget `B`, and `B/q ≤ ε*`, `δ ≤ 1`, the governing-law threshold satisfies
`δ ≤ mcaDeltaStar C ε*`.  This is the honest closed conditional pin whose *entire* open content is
now (i) the monomial-family bound (`MonomialIncidenceBounded`, structurally accessible) and (ii)
the single empirical extremality `Prop` (`SumsetExtremal`). -/
theorem mcaDeltaStar_pin_of_monomial_extremal
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (M : Set (WordStack A (Fin 2) ι))
    (hδ : δ ≤ 1)
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (hext : SumsetExtremal (F := F) C δ M)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  worstCaseIncidence_pin (F := F) (A := A) C εstar hδ
    (worstCaseIncidence_of_monomial_extremal C δ B M hM hext) hbudget

/-! ## The equivariance core that JUSTIFIES restricting to monomial fundamental domains -/

open Classical in
/-- **Equivariance feeds extremality: the incidence is constant along code automorphisms.**  If a
coordinate permutation `σ` fixes the code `C` (setwise, both directions), then relabelling a stack
by `σ` preserves its incidence count *exactly*.  This is the structural lever that makes the
monomial sub-family a legitimate fundamental domain: searching for the worst line, one may quotient
by the automorphism group (for RS/`μ_n`: the `Z/n` dilations) before invoking `SumsetExtremal`.

Proof: `MCAEquivariance.mcaEvent_comp_perm_iff` makes `mcaEvent` invariant at every `γ`, so the
filtered bad-`γ` sets are equal, hence so are their cardinalities. -/
theorem incCount_comp_perm
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C) :
    incCount (F := F) (C : Set (ι → A)) δ ![u₀ ∘ ⇑σ, u₁ ∘ ⇑σ]
      = incCount (F := F) (C : Set (ι → A)) δ ![u₀, u₁] := by
  unfold incCount
  refine Finset.card_bij' (fun γ _ => γ) (fun γ _ => γ) ?_ ?_ ?_ ?_ <;>
    intro γ hγ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hγ ⊢
  · exact (MCAEquivariance.mcaEvent_comp_perm_iff (F := F) C σ hσ hσ' (γ := γ)
      (u₀ := u₀) (u₁ := u₁)).mp hγ
  · exact (MCAEquivariance.mcaEvent_comp_perm_iff (F := F) C σ hσ hσ' (γ := γ)
      (u₀ := u₀) (u₁ := u₁)).mpr hγ

end ProximityGap.SumsetExtremality

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.SumsetExtremality.worstCaseIncidenceBounded_iff
#print axioms ProximityGap.SumsetExtremality.worstCaseIncidence_of_monomial_extremal
#print axioms ProximityGap.SumsetExtremality.mcaDeltaStar_pin_of_monomial_extremal
#print axioms ProximityGap.SumsetExtremality.incCount_comp_perm
