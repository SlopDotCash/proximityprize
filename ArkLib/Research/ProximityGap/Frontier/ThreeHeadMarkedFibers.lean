/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.FourHeadExtensionSharpness

/-! # Reserved fold values on a fourth polynomial head

Each old off-core slot supplies its own label. The fourth head supplies several
additional labels by using a different set of marked roots for each fold.
-/

set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.ThreeHeadMarkedFibers
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open FourHeadExtensionSharpness

variable {F I : Type} [Field F] [Fintype I]

/-- A folded polynomial with a large joint core and extra marked agreements
gives a native bad event when at least one marked site has a row mismatch. -/
theorem marked_event [Finite F] [Nonempty I] (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) (u : WordStack F (Fin 2) I)
    (z : F) (a b : F[X]) (C₀ S : Finset I) (ha : a.degree < k) (hb : b.degree < k)
    (large : k ≤ C₀.card) (sub : C₀ ⊆ S)
    (size : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ S.card)
    (core : ∀ x ∈ C₀, a.eval (dom x) = u 0 x ∧ b.eval (dom x) = u 1 x)
    (fold : ∀ x ∈ S, (a + C z * b).eval (dom x) = u 0 x + z * u 1 x)
    (mismatch : ∃ x ∈ S, (a.eval (dom x), b.eval (dom x)) ≠ (u 0 x, u 1 x)) :
    _root_.ProximityGap.mcaEvent (ReedSolomon.code dom k : Set (I → F)) δ (u 0) (u 1) z := by
  classical
  letI := Fintype.ofFinite F
  obtain ⟨x, hx, bad⟩ := mismatch
  apply McaDecode.mcaEvent
  refine ⟨S, a + C z * b, ?_, size, fold, ?_⟩
  · by_cases h : z = 0
    · simpa [h] using ha
    · exact (degree_add_le _ _).trans_lt (max_lt ha ((degree_C_mul h).trans_lt hb))
  · intro joint
    apply HalfPredecessorCoreFreshDecode.not_pairJointAgreesOn_insert_core
      dom k u C₀ x a b ha hb large core bad
    obtain ⟨v, hv, w, hw, agree⟩ := joint
    exact ⟨v, hv, w, hw, fun i hi => agree i ((insert_subset hx sub) hi)⟩

/-- All distinct old slots and all reserved fourth-head witnesses count in the
same event set for the same two received words. -/
theorem marked_mass [DecidableEq I] {k c : ℕ} (dom : I ↪ F) (δ : ℝ≥0) (u : WordStack F (Fin 2) I)
    (core : Fin 3 → Finset I) (size : ∀ i, (core i).card = c) (label : Slot core → F)
    (inj : Function.Injective label) (marks : Finset F)
    (free : ∀ i, label i ∉ marks)
    (old : ∀ i, _root_.ProximityGap.mcaEvent (ReedSolomon.code dom k : Set (I → F))
      δ (u 0) (u 1) (label i))
    (extra : ∀ z ∈ marks, _root_.ProximityGap.mcaEvent (ReedSolomon.code dom k : Set (I → F))
      δ (u 0) (u 1) z) :
    ∃ G : Finset F, G.card = 3 * (Fintype.card I - c) + marks.card ∧
      ∀ z ∈ G, _root_.ProximityGap.mcaEvent (ReedSolomon.code dom k : Set (I → F))
        δ (u 0) (u 1) z := by
  classical
  have dis : Disjoint (univ.image label) marks := by
    apply disjoint_left.mpr
    rintro _ hi
    obtain ⟨i, _, rfl⟩ := mem_image.mp hi
    exact free i
  refine ⟨univ.image label ∪ marks, ?_, ?_⟩
  · rw [card_union_of_disjoint dis, card_image_of_injective _ inj, card_univ]
    simp [Slot, Fintype.card_sigma, size]
  · intro z hz
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      exact old i
    · exact extra z hz

/-- Degree, error count, and number of reserved fourth-head labels. -/
def cell : Fin 5 → ℕ × ℕ × ℕ :=
  ![(71582789, 715827881, 8), (71582790, 715827880, 8), (71582792, 715827879, 9),
    (76695849, 715827878, 12), (79536437, 715827877, 15)]

/-- Give the first columns as much usable room as needed and fill the marks
cyclically. A prefix of length a multiple of the number of marks is balanced. -/
def cyclicPrefix (m z c : ℕ) := c / m + if z < c % m then 1 else 0

/-- Explicit per-label schedules in all five production rows. Each old head
has enough singleton sites, each fiber has enough roots, and the resulting
bad-label count exceeds the fixed integer budget. -/
theorem schedules : ∀ i : Fin 5,
    let (d, e, m) := cell i
    let n := 1073741824
    let c := n - e - 1
    let room := c - 2 * d
    let outer := n + 2 * d - 3 * c
    let need := (n - e) - (2 * d + outer)
    let degree (j : Fin 3) := (d + j.val) / 3
    let quota (j : Fin 3) := min room (m * degree j)
    let cut₁ := min (m * need) (quota 0)
    let cut₂ := min (m * need) (cut₁ + quota 1)
    let edge (z : Fin m) (j : Fin 3) : ℕ := ![cyclicPrefix m z cut₁,
      cyclicPrefix m z cut₂ - cyclicPrefix m z cut₁, need - cyclicPrefix m z cut₂] j
    (∀ z : Fin m, (∑ j, edge z j) = need ∧ ∀ j, edge z j ≤ degree j) ∧
      (∀ j, (∑ z, edge z j) ≤ room) ∧
      4 * d + 3 * room + outer = n ∧ d + 1 ≤ 2 * d + outer ∧ 0 < need ∧
      2 * n < 3 * (e + 1) + m := by decide

#print axioms marked_event
#print axioms marked_mass
#print axioms schedules
end ArkLib.ProximityGap.Frontier.ThreeHeadMarkedFibers
