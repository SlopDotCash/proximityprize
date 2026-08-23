/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# The sub-domain lift (#371): the tower-restriction lemma

The generic transfer mechanism of the divisor-lattice tower (the SPECTRUM law's
recursion): an `mcaEvent` witnessed entirely inside a sub-domain lifts to the
super-domain instance, at the radius recalibrated by the domain sizes.

Concretely: let `dom : Fin n ↪ F` be the big evaluation domain and
`dom' : Fin m ↪ F` a sub-domain (an `ι : Fin m ↪ Fin n` with
`dom' = dom ∘ ι`).  If the restricted rows `(u₀ ∘ ι, u₁ ∘ ι)` exhibit the MCA
event for `RS[F, dom', k]` at radius `δm`, then `(u₀, u₁)` exhibit it for
`RS[F, dom, k]` at every radius `δn` with `(1−δn)·n ≤ (1−δm)·m`:

* the witness set maps forward (`Finset.map ι`, same cardinality);
* the explaining codeword is the *same polynomial*, evaluated on the big domain;
* joint-agreement on the lifted set restricts back, so the negative clause
  transfers contrapositively.

Consequence (`badSet_lift_subset`): the bad-scalar set of the sub-instance
embeds in the bad-scalar set of the super-instance — every level-`d`
configuration of the tower (configurations supported on `μ_d`-cosets) feeds the
production instance's spectrum.  This is the formal restriction step of the
tower recursion behind `InteriorSpectrumSilent`
(`DeltaStarCeilingTightTheory.lean`).
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.MCASubdomainLift

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n m : ℕ} [NeZero n] [NeZero m]

/-- **The tower-restriction lemma**: an MCA event of the sub-domain instance
(restricted rows, sub-domain code, radius `δm`) lifts to the super-domain
instance at any radius `δn` with `(1−δn)·n ≤ (1−δm)·m`.  The explaining
codeword lifts as the same polynomial; the joint-agreement obstruction
restricts back. -/
theorem mcaEvent_lift_subdomain (dom : Fin n ↪ F) (dom' : Fin m ↪ F)
    (ι : Fin m ↪ Fin n) (hcomp : ∀ j, dom' j = dom (ι j)) {k : ℕ}
    {δm δn : ℝ≥0} (hδ : (1 - δn) * (n : ℝ≥0) ≤ (1 - δm) * (m : ℝ≥0))
    {u₀ u₁ : Fin n → F} {γ : F}
    (h : mcaEvent (F := F)
        ((rsCode dom' k : Submodule F (Fin m → F)) : Set (Fin m → F)) δm
        (u₀ ∘ ι) (u₁ ∘ ι) γ) :
    mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δn
        u₀ u₁ γ := by
  obtain ⟨S, hcard, ⟨w, hw, hagree⟩, hnot⟩ := h
  obtain ⟨P, hP, rfl⟩ := hw
  refine ⟨S.map ι, ?_, ⟨fun i => P.eval (dom i), ⟨P, hP, rfl⟩, ?_⟩, ?_⟩
  · -- cardinality: the lifted set has the same size, and the radii recalibrate
    rw [Finset.card_map]
    rw [Fintype.card_fin] at hcard
    calc (1 - δn) * (Fintype.card (Fin n) : ℝ≥0)
        = (1 - δn) * (n : ℝ≥0) := by rw [Fintype.card_fin]
      _ ≤ (1 - δm) * (m : ℝ≥0) := hδ
      _ ≤ (S.card : ℝ≥0) := hcard
  · -- agreement: the same polynomial explains the line on the lifted set
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simpa [hcomp] using hagree j hj
  · -- the negative clause: joint agreement upstairs restricts downstairs
    rintro ⟨v₀, hv₀, v₁, hv₁, hagr⟩
    apply hnot
    obtain ⟨P₀, hP₀, rfl⟩ := hv₀
    obtain ⟨P₁, hP₁, rfl⟩ := hv₁
    refine ⟨fun j => P₀.eval (dom' j), ⟨P₀, hP₀, rfl⟩,
      fun j => P₁.eval (dom' j), ⟨P₁, hP₁, rfl⟩, ?_⟩
    intro j hj
    have h2 := hagr (ι j) (Finset.mem_map_of_mem ι hj)
    exact ⟨by simpa [hcomp] using h2.1, by simpa [hcomp] using h2.2⟩

open Classical in
/-- **The spectrum embedding**: the bad-scalar set of the sub-domain instance
is contained in the bad-scalar set of the super-domain instance — the formal
restriction step of the divisor-lattice tower recursion. -/
theorem badSet_lift_subset (dom : Fin n ↪ F) (dom' : Fin m ↪ F)
    (ι : Fin m ↪ Fin n) (hcomp : ∀ j, dom' j = dom (ι j)) {k : ℕ}
    {δm δn : ℝ≥0} (hδ : (1 - δn) * (n : ℝ≥0) ≤ (1 - δm) * (m : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom' k : Submodule F (Fin m → F)) : Set (Fin m → F)) δm
        (u₀ ∘ ι) (u₁ ∘ ι) γ)
      ⊆ Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δn
        u₀ u₁ γ) := by
  intro γ hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
  exact mcaEvent_lift_subdomain dom dom' ι hcomp hδ hγ

end ProximityGap.MCASubdomainLift

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MCASubdomainLift.mcaEvent_lift_subdomain
#print axioms ProximityGap.MCASubdomainLift.badSet_lift_subset
