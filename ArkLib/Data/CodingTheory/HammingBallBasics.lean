/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Basic facts about Hamming balls (`ListDecodable.hammingBall` / `relHammingBall`)

Centre membership, radius monotonicity, and the zero-radius singleton for the Hamming-ball
*sets* from `ListDecodability.lean` — foundational facts for covering / list-decoding arguments.
-/

namespace ListDecodable

variable {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]

/-- The centre of a Hamming ball lies in the ball (`hammingDist y y = 0 ≤ r`). -/
lemma self_mem_hammingBall (y : ι → F) (r : ℕ) : y ∈ hammingBall y r := by
  simp [hammingBall, hammingDist_self]

/-- The Hamming ball is monotone in its (absolute) radius. -/
lemma hammingBall_mono {y : ι → F} {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    hammingBall y r₁ ⊆ hammingBall y r₂ := by
  intro x hx
  simp only [hammingBall, Set.mem_setOf_eq] at hx ⊢
  exact le_trans hx h

/-- The relative Hamming ball is monotone in its (relative) radius. -/
lemma relHammingBall_mono {y : ι → F} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    relHammingBall y r₁ ⊆ relHammingBall y r₂ := by
  intro x hx
  simp only [relHammingBall, Set.mem_setOf_eq] at hx ⊢
  exact le_trans hx h

/-- A zero-radius Hamming ball is the singleton of its centre. -/
lemma hammingBall_zero (y : ι → F) : hammingBall y 0 = {y} := by
  ext x
  simp only [hammingBall, Set.mem_setOf_eq, Nat.le_zero, hammingDist_eq_zero,
    Set.mem_singleton_iff]
  exact eq_comm

/-- **List-decodability is antitone in the radius**: shrinking the decoding radius preserves
`(r, ℓ)`-list-decodability (fewer codewords are close), via `closeCodewordsRel_subset_of_le`. -/
theorem listDecodable_of_radius_le {F : Type*} [Fintype F] [DecidableEq F]
    {C : Code ι F} {r' r ℓ : ℝ} (hr : r' ≤ r) (h : listDecodable C r ℓ) :
    listDecodable C r' ℓ := by
  intro y
  refine le_trans ?_ (h y)
  exact_mod_cast Set.ncard_le_ncard (closeCodewordsRel_subset_of_le hr y) (Set.toFinite _)

/-- **List-decodability is monotone in the list-size bound**: relaxing the allowed list size
preserves list-decodability. -/
theorem listDecodable_of_bound_le {F : Type*} [Fintype F] [DecidableEq F]
    {C : Code ι F} {r ℓ ℓ' : ℝ} (hℓ : ℓ ≤ ℓ') (h : listDecodable C r ℓ) :
    listDecodable C r ℓ' := by
  intro y
  exact le_trans (h y) hℓ

/-- **Combined monotonicity for `listDecodable`**: shrink the radius and relax the list-size
bound in one predicate-level wrapper. -/
theorem listDecodable_mono {F : Type*} [Fintype F] [DecidableEq F]
    {C : Code ι F} {r' r ℓ ℓ' : ℝ} (hr : r' ≤ r) (hℓ : ℓ ≤ ℓ')
    (h : listDecodable C r ℓ) : listDecodable C r' ℓ' :=
  listDecodable_of_bound_le hℓ (listDecodable_of_radius_le hr h)

/-- **List-decodability is monotone under taking subcodes**: if every list for `C'` is bounded by
`ℓ`, then every list for a subcode `C ⊆ C'` is bounded by the same `ℓ`. -/
theorem listDecodable_mono_code {F : Type*} [Fintype F] [DecidableEq F]
    {C C' : Code ι F} {δ ℓ : ℝ} (hsubcode : C ⊆ C') (h : listDecodable C' δ ℓ) :
    listDecodable C δ ℓ := by
  intro y
  refine le_trans ?_ (h y)
  have hsub : closeCodewordsRel C y δ ⊆ closeCodewordsRel C' y δ :=
    fun c hc => ⟨hsubcode hc.1, hc.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **Combined subcode/radius/bound monotonicity for `listDecodable`.**  A subcode remains
list-decodable when the decoding radius is shrunk and the target list-size bound is relaxed. -/
theorem listDecodable_mono_code_radius_bound {F : Type*} [Fintype F] [DecidableEq F]
    {C C' : Code ι F} {r' r ℓ ℓ' : ℝ} (hsubcode : C ⊆ C') (hr : r' ≤ r)
    (hℓ : ℓ ≤ ℓ') (h : listDecodable C' r ℓ) : listDecodable C r' ℓ' :=
  listDecodable_mono hr hℓ (listDecodable_mono_code hsubcode h)

/-- **`Lambda` bound ⇒ list-decodability** (converse of `Lambda_le_natCast_of_forall_ncard_le`):
if the maximised list size `|Λ(C,δ)|` is `≤ ℓ`, then `C` is `(δ, ℓ)`-list-decodable. -/
theorem listDecodable_of_Lambda_le {F : Type*} [Fintype F] [DecidableEq F]
    {C : Code ι F} {δ : ℝ} {ℓ : ℕ} (h : Lambda C δ ≤ (ℓ : ℕ∞)) : listDecodable C δ (ℓ : ℝ) := by
  intro y
  have hy : ((closeCodewordsRel C y δ).ncard : ℕ∞) ≤ (ℓ : ℕ∞) :=
    le_trans (le_iSup (fun f => ((closeCodewordsRel C f δ).ncard : ℕ∞)) y) h
  have hnat : (closeCodewordsRel C y δ).ncard ≤ ℓ := by exact_mod_cast hy
  exact_mod_cast hnat

/-- **List-decodability ⇒ `Lambda` bound** at a natural list-size bound.  This is the
predicate-to-maximised endpoint companion to `listDecodable_of_Lambda_le`. -/
theorem Lambda_le_of_listDecodable_nat {F : Type*}
    {C : Code ι F} {δ : ℝ} {ℓ : ℕ} (h : listDecodable C δ (ℓ : ℝ)) :
    Lambda C δ ≤ (ℓ : ℕ∞) :=
  Lambda_le_natCast_of_forall_ncard_le fun f => by
    exact_mod_cast h f

/-- **Predicate / maximised-list equivalence** for natural list-size bounds. -/
theorem listDecodable_iff_Lambda_le_nat {F : Type*}
    {C : Code ι F} {δ : ℝ} {ℓ : ℕ} :
    listDecodable C δ (ℓ : ℝ) ↔ Lambda C δ ≤ (ℓ : ℕ∞) := by
  refine ⟨Lambda_le_of_listDecodable_nat, ?_⟩
  intro h y
  have hy : ((closeCodewordsRel C y δ).ncard : ℕ∞) ≤ (ℓ : ℕ∞) :=
    le_trans (le_iSup (fun f => ((closeCodewordsRel C f δ).ncard : ℕ∞)) y) h
  have hnat : (closeCodewordsRel C y δ).ncard ≤ ℓ := by exact_mod_cast hy
  exact_mod_cast hnat

/-- **`Lambda` is monotone in the code**: a subcode has a smaller maximised list size, since each
point list `closeCodewordsRel` grows with the code. -/
theorem Lambda_mono_code {F : Type*} [Finite F] {C C' : Code ι F} (h : C ⊆ C') (δ : ℝ) :
    Lambda C δ ≤ Lambda C' δ := by
  refine iSup_mono fun f => ?_
  have hsub : closeCodewordsRel C f δ ⊆ closeCodewordsRel C' f δ := fun c hc => ⟨h hc.1, hc.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **Combined code/radius monotonicity for `Lambda`.**  Passing to a subcode and shrinking the
radius can only decrease the maximised list size. -/
theorem Lambda_mono_code_radius {F : Type*} [Finite F] {C C' : Code ι F}
    (hsubcode : C ⊆ C') {δ δ' : ℝ} (hδ : δ ≤ δ') : Lambda C δ ≤ Lambda C' δ' := by
  exact le_trans (Lambda_mono (C := C) hδ) (Lambda_mono_code hsubcode δ')

end ListDecodable

#print axioms ListDecodable.self_mem_hammingBall
#print axioms ListDecodable.hammingBall_mono
#print axioms ListDecodable.relHammingBall_mono
#print axioms ListDecodable.hammingBall_zero
#print axioms ListDecodable.listDecodable_of_radius_le
#print axioms ListDecodable.listDecodable_of_bound_le
#print axioms ListDecodable.listDecodable_mono
#print axioms ListDecodable.listDecodable_mono_code
#print axioms ListDecodable.listDecodable_mono_code_radius_bound
#print axioms ListDecodable.listDecodable_of_Lambda_le
#print axioms ListDecodable.Lambda_le_of_listDecodable_nat
#print axioms ListDecodable.listDecodable_iff_Lambda_le_nat
#print axioms ListDecodable.Lambda_mono_code
#print axioms ListDecodable.Lambda_mono_code_radius
