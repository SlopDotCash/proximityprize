/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24AgreementHypergraph

/-!
# [AGL24] subfamily transport: the 2.3 → 2.8 weld, edge layer (issue #346, brick 5a)

The pointwise weld of Lemmas 2.3 and 2.8 re-indexes the vertex subset `J ⊆ [L+1]` produced
by Lemma 2.3 onto `Fin |J|`, turning the *restricted* agreement hypergraph into the agreement
hypergraph of the *subfamily*. This brick proves the edge layer of that transport:

* `agreementEdge_comp` — the agreement hypergraph commutes with subfamily restriction:
  the edge of the re-indexed subfamily is the preimage of the original edge;
* `agreementEdge_comp_inter` — consequently, for `ι` enumerating `J`, the re-indexed edge is
  the preimage of the original edge *intersected with `J`* (the exact restricted-edge shape
  Lemma 2.3's weak-partition-connectivity speaks about).

The remaining transport layer — `WeaklyPartitionConnected` across the order isomorphism
`Fin |J| ≃o J` (Finpartition pullback + touched-cell count preservation) — is the catalogued
next unit; with it, `exists_wpc_subset_of_bad_list` (Lemma 2.3) feeds
`RIM_eval_not_injective` (Lemma 2.8) directly, completing the deterministic chain
bad-list ⟹ rank-deficit that the Theorem 1.1 union bound consumes.
-/

open Finset

namespace AGL24

variable {ι' α : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq α]

/-- **The agreement hypergraph commutes with subfamily restriction**: the edge of the
re-indexed subfamily `c ∘ σ` is the `σ`-preimage of the original edge. -/
theorem agreementEdge_comp {L t : ℕ} (y : ι' → α) (c : Fin (L + 1) → ι' → α)
    (σ : Fin (t + 1) → Fin (L + 1)) (hσ : Function.Injective σ) (i : ι') :
    agreementEdge y (fun j' => c (σ j')) i
      = (agreementEdge y c i).preimage σ hσ.injOn := by
  ext j'
  simp only [agreementEdge, Finset.mem_preimage, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- For an enumeration `σ` of the vertex subset `J` (i.e. `σ` injective with range `J`), the
re-indexed subfamily's edge is the preimage of the *`J`-restricted* original edge — the exact
shape Lemma 2.3's weak-partition-connectivity constrains. -/
theorem agreementEdge_comp_inter {L t : ℕ} (y : ι' → α) (c : Fin (L + 1) → ι' → α)
    {J : Finset (Fin (L + 1))} (σ : Fin (t + 1) → Fin (L + 1))
    (hσ : Function.Injective σ) (hrange : ∀ j', σ j' ∈ J) (i : ι') :
    agreementEdge y (fun j' => c (σ j')) i
      = ((agreementEdge y c i) ∩ J).preimage σ hσ.injOn := by
  rw [agreementEdge_comp y c σ hσ i]
  ext j'
  simp only [Finset.mem_preimage, Finset.mem_inter]
  exact ⟨fun h => ⟨h, hrange j'⟩, fun h => h.1⟩

/-- The subfamily of pairwise-distinct coefficient vectors over a `≥ 2`-element index set is
not all-equal — the hypothesis Lemma 2.8 needs, produced by Lemma 2.3's `|J| ≥ 2`
(the paper's Remark 2.10). -/
theorem subfamily_not_all_equal {L t k : ℕ} {F : Type*} [Field F]
    (f : Fin (L + 1) → Fin k → F)
    (hdistinct : Function.Injective f)
    (σ : Fin (t + 1) → Fin (L + 1)) (hσ : Function.Injective σ) (ht : 1 ≤ t) :
    ∃ j j' : Fin (t + 1), (fun j' => f (σ j')) j ≠ (fun j' => f (σ j')) j' := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  intro h
  have hσne : σ ⟨0, by omega⟩ ≠ σ ⟨1, by omega⟩ := fun hc =>
    absurd (hσ hc) (by simp [Fin.ext_iff])
  exact hσne (hdistinct h)


/-! ## The weak-partition-connectivity transport -/

variable {L t k : ℕ}

/-- The pushforward of a partition of `univ : Finset (Fin (t+1))` along an injective map into
`Fin (L+1)` with image `J`: a partition of `J`. -/
def Finpartition.pushforward {J : Finset (Fin (L + 1))}
    (σ : Fin (t + 1) → Fin (L + 1)) (hσ : Function.Injective σ)
    (himg : Finset.univ.image σ = J)
    (P' : Finpartition (Finset.univ : Finset (Fin (t + 1)))) : Finpartition J where
  parts := P'.parts.image (Finset.image σ)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro c₁ hc₁ c₂ hc₂ hne
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hc₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hc₂
    have hpne : p₁ ≠ p₂ := fun h => hne (by rw [h])
    have hdisj := (Finset.supIndep_iff_pairwiseDisjoint.mp P'.supIndep) hp₁ hp₂ hpne
    exact (Finset.disjoint_image hσ).mpr hdisj
  sup_parts := by
    ext y
    simp only [Finset.mem_sup, Finset.mem_image, id]
    constructor
    · rintro ⟨c, ⟨p, _, rfl⟩, hyc⟩
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hyc
      rw [← himg]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    · intro hy
      rw [← himg] at hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨p, hp, hxp⟩ := P'.exists_mem (Finset.mem_univ x)
      exact ⟨p.image σ, ⟨p, hp, rfl⟩, Finset.mem_image.mpr ⟨x, hxp, rfl⟩⟩
  bot_notMem := by
    intro hmem
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hmem
    have hp0 : p = ∅ := Finset.image_eq_empty.mp hpe
    rw [hp0] at hp
    exact P'.bot_notMem hp

/-- **The weak-partition-connectivity transport**: if the restriction of the edge family to
`J` is `k`-weakly-partition-connected, so is its `σ`-preimage family on the full vertex set
`Fin (t+1)` (for `σ` injective with image `J`). -/
theorem weaklyPartitionConnected_preimage {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (e : ι' → Finset (Fin (L + 1))) {J : Finset (Fin (L + 1))}
    (σ : Fin (t + 1) → Fin (L + 1)) (hσ : Function.Injective σ)
    (himg : Finset.univ.image σ = J)
    (hwpc : WeaklyPartitionConnected k J e) :
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1)))
      (fun i => (e i).preimage σ hσ.injOn) := by
  classical
  intro P'
  set P := Finpartition.pushforward σ hσ himg P' with hP
  have himg_inj : Function.Injective (Finset.image σ) := Finset.image_injective hσ
  have hcard : P.parts.card = P'.parts.card := by
    rw [hP]
    exact Finset.card_image_of_injective _ himg_inj
  have htouched : ∀ i : ι',
      (touchedCells P (e i ∩ J)).card
        = (touchedCells P' ((e i).preimage σ hσ.injOn ∩ Finset.univ)).card := by
    intro i
    rw [show touchedCells P (e i ∩ J)
        = (touchedCells P' ((e i).preimage σ hσ.injOn ∩ Finset.univ)).image
            (Finset.image σ) from ?_]
    · rw [Finset.card_image_of_injective _ himg_inj]
    ext c
    simp only [touchedCells, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨hc, x, hx⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      rw [Finset.mem_inter] at hx
      obtain ⟨hxe, hxp⟩ := hx
      obtain ⟨x0, hx0p, rfl⟩ := Finset.mem_image.mp hxp
      refine ⟨x0, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨?_, Finset.mem_univ x0⟩, hx0p⟩⟩
      rw [Finset.mem_preimage]
      exact (Finset.mem_inter.mp hxe).1
    · rintro ⟨p, ⟨hp, x0, hx0⟩, rfl⟩
      rw [Finset.mem_inter, Finset.mem_inter] at hx0
      obtain ⟨⟨hx0e, -⟩, hx0p⟩ := hx0
      rw [Finset.mem_preimage] at hx0e
      refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, σ x0, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · refine Finset.mem_inter.mpr ⟨hx0e, ?_⟩
        rw [← himg]
        exact Finset.mem_image.mpr ⟨x0, Finset.mem_univ x0, rfl⟩
      · exact Finset.mem_image.mpr ⟨x0, hx0p, rfl⟩
  calc k * (P'.parts.card - 1) = k * (P.parts.card - 1) := by rw [hcard]
  _ ≤ ∑ i, ((touchedCells P (e i ∩ J)).card - 1) := hwpc P
  _ = ∑ i, ((touchedCells P' ((e i).preimage σ hσ.injOn ∩ Finset.univ)).card - 1) :=
      Finset.sum_congr rfl fun i _ => by rw [htouched i]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.agreementEdge_comp
#print axioms AGL24.agreementEdge_comp_inter
#print axioms AGL24.subfamily_not_all_equal
#print axioms AGL24.weaklyPartitionConnected_preimage
