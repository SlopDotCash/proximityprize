/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Probability.Combinatorial

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Set.PowersetCard
import ArkLib.Data.Probability.Notation

/-!
# Probabilistic combinatorics

Stand-alone probabilistic-combinatorics statements used elsewhere in ArkLib.
This includes the fixed-cardinality subset sample space needed for random Reed-Solomon domains and
`exists_large_image_of_pairwise_collision_bound`, which is Claim B.1 of [ABF26].

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

namespace Probability

open Finset NNReal ENNReal ProbabilityTheory

/-! ## Uniform fixed-cardinality subsets

ABF26 T3.6 and T4.15 sample a Reed-Solomon evaluation domain uniformly from the size-`n`
subsets of a finite field.  Mathlib already provides the exact sample space as
`Set.powersetCard α n`; the definitions below expose the ArkLib-facing probability primitive and
basic cardinality facts without asserting any of the random-RS bounds themselves. -/

/-- The sample space of finite subsets of `α` with cardinality exactly `n`.

This is a thin ArkLib-facing name for Mathlib's `Set.powersetCard α n`. -/
abbrev SizeSubset (α : Type*) (n : ℕ) :=
  Set.powersetCard α n

namespace SizeSubset

variable {α : Type*} {n : ℕ}

/-- The number of size-`n` subsets of a finite type is `|α| choose n`. -/
theorem card [Fintype α] :
    Nat.card (SizeSubset α n) = (Fintype.card α).choose n := by
  simpa [SizeSubset, Nat.card_eq_fintype_card] using
    (Set.powersetCard.card (α := α) (n := n))

/-- Fintype-cardinality form of `SizeSubset.card`. -/
theorem fintype_card [Fintype α] :
    Fintype.card (SizeSubset α n) = (Fintype.card α).choose n := by
  rw [Fintype.card_eq_nat_card, card]

/-- If `n ≤ |α|`, then the size-`n` subset sample space is nonempty. -/
theorem nonempty_of_le [Fintype α] (h : n ≤ Fintype.card α) :
    Nonempty (SizeSubset α n) := by
  classical
  have hNonempty :
      (Finset.powersetCard n (Finset.univ : Finset α)).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using h)
  rcases hNonempty with ⟨s, hs⟩
  exact ⟨⟨s, (Finset.mem_powersetCard.mp hs).2⟩⟩

/-- Every sample in `SizeSubset α n` has cardinality `n`. -/
@[simp]
theorem val_card (s : SizeSubset α n) :
    (s : Finset α).card = n :=
  Set.powersetCard.card_eq s

/-- A positive-cardinality sample carries a nonempty subtype of its elements. -/
theorem nonempty_coe (s : SizeSubset α n) (hn : 0 < n) :
    Nonempty s := by
  classical
  obtain ⟨x, hx⟩ : (s : Finset α).Nonempty := by
    rw [← Finset.card_pos, val_card]
    exact hn
  exact ⟨⟨x, hx⟩⟩

/-- The canonical embedding from a size-`n` subset into its ambient type. -/
noncomputable def toEmbedding (s : SizeSubset α n) : s ↪ α where
  toFun x := x.1
  inj' := by
    intro x y h
    exact Subtype.ext h

variable {β : Type*}

/-- Transport a size-`n` subset across an equivalence of ambient types. -/
noncomputable def mapEquiv (e : α ≃ β) :
    SizeSubset α n ≃ SizeSubset β n where
  toFun := Set.powersetCard.map n e.toEmbedding
  invFun := Set.powersetCard.map n e.symm.toEmbedding
  left_inv s := by
    apply Subtype.ext
    ext x
    simp [Set.powersetCard.map]
  right_inv t := by
    apply Subtype.ext
    ext x
    simp [Set.powersetCard.map]

end SizeSubset

/-- Uniform distribution on the size-`n` subsets of a finite type. -/
noncomputable def uniformSizeSubset (α : Type*) [Fintype α] (n : ℕ)
    [Nonempty (SizeSubset α n)] : PMF (SizeSubset α n) :=
  ProximityPrize.Compatibility.uniformOfFintype (SizeSubset α n)

/-- Uniform distribution on size-`n` subsets, using `n ≤ |α|` to provide nonemptiness. -/
noncomputable def uniformSizeSubsetOfLe (α : Type*) [Fintype α] (n : ℕ)
    (h : n ≤ Fintype.card α) : PMF (SizeSubset α n) := by
  letI : Nonempty (SizeSubset α n) := SizeSubset.nonempty_of_le (α := α) (n := n) h
  exact uniformSizeSubset α n

/-- Point mass of the uniform size-`n` subset distribution. -/
theorem uniformSizeSubset_apply {α : Type*} [Fintype α] {n : ℕ}
    [Nonempty (SizeSubset α n)] (s : SizeSubset α n) :
    uniformSizeSubset α n s = (Fintype.card (SizeSubset α n) : ENNReal)⁻¹ := by
  simp [uniformSizeSubset, ProximityPrize.Compatibility.uniformOfFintype_apply]

/-- The uniform size-`n` subset distribution has full support. -/
@[simp]
theorem support_uniformSizeSubset {α : Type*} [Fintype α] {n : ℕ}
    [Nonempty (SizeSubset α n)] :
    (uniformSizeSubset α n).support = ⊤ := by
  simp [uniformSizeSubset]

/-- Every size-`n` subset lies in the support of the uniform size-`n` subset distribution. -/
theorem mem_support_uniformSizeSubset {α : Type*} [Fintype α] {n : ℕ}
    [Nonempty (SizeSubset α n)] (s : SizeSubset α n) :
    s ∈ (uniformSizeSubset α n).support := by
  rw [support_uniformSizeSubset]
  trivial

/-- Point mass of the uniform size-`n` subset distribution, with the denominator rewritten as
`|α| choose n`. -/
theorem uniformSizeSubset_apply_choose {α : Type*} [Fintype α] {n : ℕ}
    [Nonempty (SizeSubset α n)] (s : SizeSubset α n) :
    uniformSizeSubset α n s = ((Fintype.card α).choose n : ENNReal)⁻¹ := by
  rw [uniformSizeSubset_apply, SizeSubset.fintype_card]

/-- Point mass of `uniformSizeSubsetOfLe`, with the denominator rewritten as `|α| choose n`. -/
theorem uniformSizeSubsetOfLe_apply {α : Type*} [Fintype α] {n : ℕ}
    (h : n ≤ Fintype.card α) (s : SizeSubset α n) :
    uniformSizeSubsetOfLe α n h s = ((Fintype.card α).choose n : ENNReal)⁻¹ := by
  classical
  simp [uniformSizeSubsetOfLe, uniformSizeSubset_apply_choose]

/-- The le-supplied uniform size-`n` subset distribution has full support. -/
@[simp]
theorem support_uniformSizeSubsetOfLe {α : Type*} [Fintype α] {n : ℕ}
    (h : n ≤ Fintype.card α) :
    (uniformSizeSubsetOfLe α n h).support = ⊤ := by
  classical
  simp [uniformSizeSubsetOfLe]

/-- Every size-`n` subset lies in the support of the le-supplied uniform distribution. -/
theorem mem_support_uniformSizeSubsetOfLe {α : Type*} [Fintype α] {n : ℕ}
    (h : n ≤ Fintype.card α) (s : SizeSubset α n) :
    s ∈ (uniformSizeSubsetOfLe α n h).support := by
  rw [support_uniformSizeSubsetOfLe h]
  trivial

/-- Uniform fixed-size subset sampling is invariant under equivalence of ambient finite types. -/
theorem uniformSizeSubset_apply_mapEquiv {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    [Nonempty (SizeSubset α n)] [Nonempty (SizeSubset β n)] (e : α ≃ β)
    (s : SizeSubset α n) :
    uniformSizeSubset β n (SizeSubset.mapEquiv e s) =
      uniformSizeSubset α n s := by
  simp [uniformSizeSubset_apply_choose, Fintype.card_congr e]

/-- Le-supplied uniform fixed-size subset sampling is invariant under ambient equivalences. -/
theorem uniformSizeSubsetOfLe_apply_mapEquiv {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (e : α ≃ β) (hα : n ≤ Fintype.card α) (hβ : n ≤ Fintype.card β)
    (s : SizeSubset α n) :
    uniformSizeSubsetOfLe β n hβ (SizeSubset.mapEquiv e s) =
      uniformSizeSubsetOfLe α n hα s := by
  simp [uniformSizeSubsetOfLe_apply, Fintype.card_congr e]

/-! ## Colliding-pair helpers (ABF26 Appendix B counting)

Helper definitions and the central Cauchy-Schwarz-on-fibers lemma used
by `exists_large_image_of_pairwise_collision_bound` (Claim B.1). -/

section CollidingPairs

variable {S T : Type} [Fintype S] [DecidableEq S] [DecidableEq T]

/-- Number of *ordered* pairs `(x, y) : S × S` with `x ≠ y` and `φ x = φ y`.

This equals twice the number of distinct (unordered) colliding pairs;
working ordered avoids needing a `LinearOrder S` to canonicalise unordered
pairs. Paper's `|C_φ|` is `numCollsOrdered φ / 2`. -/
def numCollsOrdered (φ : S → T) : ℕ :=
  (Finset.univ.filter (fun p : S × S ↦ p.1 ≠ p.2 ∧ φ p.1 = φ p.2)).card

/-- Sum of squared fiber-cardinalities = `|S| + numCollsOrdered`.

Each ordered pair `(x, y)` with `φ x = φ y` is counted once on the LHS
(via its common image μ); the `|S|` diagonal pairs `(x, x)` and the
`numCollsOrdered` off-diagonal pairs partition them. -/
lemma sum_fiber_sq_eq (φ : S → T) :
    ∑ μ ∈ Finset.univ.image φ,
        ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card)^2 =
      Fintype.card S + numCollsOrdered φ := by
  classical
  -- Step 1: LHS = #{(x, y) : φ x = φ y}.
  -- Each μ ∈ image contributes |fiber μ|² = |fiber μ × fiber μ| = #{(x,y) : φ x = φ y = μ}.
  have step1 :
      ∑ μ ∈ Finset.univ.image φ,
          ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card)^2 =
        (Finset.univ.filter (fun p : S × S ↦ φ p.1 = φ p.2)).card := by
    -- The matching-pair set D = univ.filter (φ p.1 = φ p.2) partitions by φ p.1 ∈ image.
    set D := Finset.univ.filter (fun p : S × S ↦ φ p.1 = φ p.2)
    -- D maps into image φ via the projection p ↦ φ p.1
    have hMaps : (D : Set (S × S)).MapsTo (fun p : S × S ↦ φ p.1)
                  (Finset.univ.image φ : Finset T) := by
      intros p _
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨p.1, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : S × S ↦ φ p.1)
        (t := Finset.univ.image φ) hMaps]
    apply Finset.sum_congr rfl
    intros μ _
    -- {p ∈ D | φ p.1 = μ} = fiber μ × fiber μ.
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨x, y⟩
    simp only [D, Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and]
    -- Goal: (φ x = μ ∧ φ y = μ) ↔ φ x = φ y ∧ φ x = μ
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx.trans hy.symm, hx⟩
    · rintro ⟨h_match, hx⟩
      exact ⟨hx, h_match.symm.trans hx⟩
  rw [step1]
  -- Step 2: #{(x, y) : φ x = φ y} = |diag| + |off-diag matching|.
  -- diag = {(x, x)}; off-diag matching = numCollsOrdered's filter set.
  have step2 :
      (Finset.univ.filter (fun p : S × S ↦ φ p.1 = φ p.2)).card =
        (Finset.univ.filter (fun p : S × S ↦ p.1 = p.2)).card +
        (Finset.univ.filter (fun p : S × S ↦ p.1 ≠ p.2 ∧ φ p.1 = φ p.2)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      by_cases hxy : x = y
      · simp [hxy]
      · constructor
        · intro hφ; right; exact ⟨hxy, hφ⟩
        · rintro (h_eq | ⟨_, hφ⟩) <;> [exact (hxy h_eq).elim; exact hφ]
    · rw [Finset.disjoint_filter]
      intros _ _ h_eq h_ne_and; exact h_ne_and.1 h_eq
  rw [step2]
  -- Step 3: diag count = |S| via the (x : S) ↔ ((x, x) ∈ diag) bijection.
  congr 1
  -- diag = (Finset.univ : Finset S).image (fun x ↦ (x, x))
  rw [show (Finset.univ.filter (fun p : S × S ↦ p.1 = p.2)) =
        (Finset.univ : Finset S).image (fun x ↦ (x, x)) by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h_eq; exact ⟨x, ⟨rfl, h_eq⟩⟩
    · rintro ⟨a, ⟨rfl, rfl⟩⟩; rfl]
  rw [Finset.card_image_of_injective _ (fun a b h ↦ (Prod.mk.injEq _ _ _ _).mp h |>.1)]
  rfl

/-- Cauchy-Schwarz applied to fiber cardinalities.

Equivalent to `Finset.sq_sum_le_card_mul_sum_sq` over the image of `φ`,
combined with `sum_fiber_sq_eq` to rewrite the squared-sum side and
with `Finset.card_eq_sum_card_image` to identify
`Σ μ ∈ image, |fiber μ| = |S|`. -/
lemma cauchy_schwarz_fiber (φ : S → T) :
    (Fintype.card S)^2 ≤
      (Finset.univ.image φ).card * (Fintype.card S + numCollsOrdered φ) := by
  classical
  -- Fiber decomposition: Σ μ ∈ image, |fiber μ| = |S|.
  have h_sum_card :
      ∑ μ ∈ Finset.univ.image φ,
          (Finset.univ.filter (fun x : S ↦ φ x = μ)).card = Fintype.card S := by
    have := Finset.card_eq_sum_card_image φ (Finset.univ : Finset S)
    simpa using this.symm
  -- Cast inequality through ℝ since Chebyshev requires LinearOrderedSemifield.
  have h_cs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ.image φ)
    (f := fun μ ↦ ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))
  -- LHS in ℝ: (Σ μ, |fiber μ|)² = |S|² (via h_sum_card cast).
  have h_lhs :
      (∑ μ ∈ Finset.univ.image φ,
          ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))
        = (Fintype.card S : ℝ) := by
    rw [← Nat.cast_sum, h_sum_card]
  -- RHS sum in ℝ: Σ μ, |fiber μ|² = |S| + numCollsOrdered φ (via sum_fiber_sq_eq cast).
  have h_rhs :
      (∑ μ ∈ Finset.univ.image φ,
          (((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))^2)
        = ((Fintype.card S + numCollsOrdered φ : ℕ) : ℝ) := by
    rw [show (∑ μ ∈ Finset.univ.image φ,
          (((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))^2)
        = (∑ μ ∈ Finset.univ.image φ,
          (((Finset.univ.filter (fun x : S ↦ φ x = μ)).card)^2 : ℕ) : ℝ) by
      push_cast; rfl]
    rw [← Nat.cast_sum, sum_fiber_sq_eq]
  rw [h_lhs, h_rhs] at h_cs
  -- h_cs : (Fintype.card S : ℝ)² ≤ (#image : ℝ) * (Fintype.card S + numColls : ℝ)
  exact_mod_cast h_cs

end CollidingPairs

end Probability
