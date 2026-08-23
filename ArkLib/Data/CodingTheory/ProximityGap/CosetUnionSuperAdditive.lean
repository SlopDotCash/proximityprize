/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardIdentity

/-!
# Super-additive deep-band supply from multiple coset structures (#389)

`CosetUnionGrowth.coset_union_growth` lower-bounds the zero-sum-`(d·j)`-subset count by
`C(|orbits|, j)` from one family of disjoint zero-sum `d`-subsets.  When a domain carries **two**
independent such structures — e.g. on `6 ∣ n`, both additive antipodal pairs (`d = 2`) and
multiplicative cube cosets (`d = 3`) — and the two structures produce *distinct* `(d·j)`-subsets,
the contributions **add**:

> **`coset_union_growth_two`** — `C(|O₁|, j₁) + C(|O₂|, j₂) ≤ #{ zero-sum m-subsets }` whenever
> `O₁` (zero-sum `d₁`-subsets) and `O₂` (zero-sum `d₂`-subsets) satisfy `d₁·j₁ = d₂·j₂ = m` and no
> `j₁`-union from `O₁` equals a `j₂`-union from `O₂`.

The cross-disjointness is genuine, not an artifact: a union of cube cosets is *not* closed under
negation (`−1 ∉ μ₃`), so it can never equal a union of antipodal pairs.  Hence on `6 ∣ n` the
sextic word `x⁶` has supply `≥ C(n/2, 3) + C(n/3, 2)` — strictly more than either structure alone.
Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- The union map on `j`-subfamilies of a disjoint zero-sum `d`-coset family lands in the zero-sum
`(d·j)`-subsets and is injective (the engine of `coset_union_growth`, packaged for reuse). -/
theorem coset_family_facts (dom : Fin n ↪ F) (O : Finset (Finset (Fin n))) (d j : ℕ)
    (hd : 1 ≤ d) (hcard : ∀ X ∈ O, X.card = d) (hsum : ∀ X ∈ O, ∑ i ∈ X, dom i = 0)
    (hdisj : ∀ X ∈ O, ∀ X' ∈ O, X ≠ X' → Disjoint X X') :
    (∀ P ∈ O.powersetCard j, P.biUnion id ∈
        ((Finset.univ : Finset (Fin n)).powersetCard (d * j)).filter
          (fun T => ∑ i ∈ T, dom i = 0))
      ∧ Set.InjOn (fun P : Finset (Finset (Fin n)) => P.biUnion id) ↑(O.powersetCard j) := by
  classical
  refine ⟨?_, ?_⟩
  · intro P hP
    obtain ⟨hPsub, hPcard⟩ := Finset.mem_powersetCard.mp hP
    have hPdisj : ∀ X ∈ P, ∀ X' ∈ P, X ≠ X' → Disjoint (id X) (id X') :=
      fun X hX X' hX' hne => hdisj X (hPsub hX) X' (hPsub hX') hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_biUnion hPdisj]
      have hsz : ∑ X ∈ P, (id X).card = P.card * d :=
        by rw [Finset.sum_congr rfl (fun X hX => by simpa using hcard X (hPsub hX)),
          Finset.sum_const, smul_eq_mul]
      rw [hsz, hPcard]; ring
    · rw [Finset.sum_biUnion hPdisj]
      exact Finset.sum_eq_zero (fun X hX => hsum X (hPsub hX))
  · intro P hP Q hQ hPQ
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hP hQ
    have hbi : P.biUnion id = Q.biUnion id := hPQ
    have key : ∀ (A B : Finset (Finset (Fin n))), A ⊆ O → B ⊆ O →
        A.biUnion id = B.biUnion id → A ⊆ B := by
      intro A B hA hB hAB X hX
      have hXne : X.Nonempty := Finset.card_pos.mp (by rw [hcard X (hA hX)]; omega)
      obtain ⟨x, hx⟩ := hXne
      have hxU : x ∈ B.biUnion id := by
        rw [← hAB]; exact Finset.mem_biUnion.mpr ⟨X, hX, hx⟩
      obtain ⟨X', hX', hxX'⟩ := Finset.mem_biUnion.mp hxU
      have : X = X' := by
        by_contra hne
        exact (Finset.disjoint_left.mp (hdisj X (hA hX) X' (hB hX') hne) hx) hxX'
      rwa [this]
    exact Finset.Subset.antisymm (key P Q hP.1 hQ.1 hbi) (key Q P hQ.1 hP.1 hbi.symm)

open Classical in
/-- **Super-additive coset growth.**  Two independent disjoint zero-sum coset families at the same
union size `d₁·j₁ = d₂·j₂` whose unions never coincide contribute **additively** to the zero-sum
subset count. -/
theorem coset_union_growth_two (dom : Fin n ↪ F)
    (O₁ O₂ : Finset (Finset (Fin n))) (d₁ d₂ j₁ j₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hm : d₁ * j₁ = d₂ * j₂)
    (hcard₁ : ∀ X ∈ O₁, X.card = d₁) (hsum₁ : ∀ X ∈ O₁, ∑ i ∈ X, dom i = 0)
    (hdisj₁ : ∀ X ∈ O₁, ∀ X' ∈ O₁, X ≠ X' → Disjoint X X')
    (hcard₂ : ∀ X ∈ O₂, X.card = d₂) (hsum₂ : ∀ X ∈ O₂, ∑ i ∈ X, dom i = 0)
    (hdisj₂ : ∀ X ∈ O₂, ∀ X' ∈ O₂, X ≠ X' → Disjoint X X')
    (hcross : ∀ P₁ ∈ O₁.powersetCard j₁, ∀ P₂ ∈ O₂.powersetCard j₂,
        P₁.biUnion id ≠ P₂.biUnion id) :
    (O₁.card).choose j₁ + (O₂.card).choose j₂ ≤
      (((Finset.univ : Finset (Fin n)).powersetCard (d₁ * j₁)).filter
        (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  set Z := ((Finset.univ : Finset (Fin n)).powersetCard (d₁ * j₁)).filter
    (fun T => ∑ i ∈ T, dom i = 0) with hZ
  obtain ⟨hmem₁, hinj₁⟩ := coset_family_facts dom O₁ d₁ j₁ hd₁ hcard₁ hsum₁ hdisj₁
  obtain ⟨hmem₂, hinj₂⟩ := coset_family_facts dom O₂ d₂ j₂ hd₂ hcard₂ hsum₂ hdisj₂
  set A := (O₁.powersetCard j₁).image (fun P => P.biUnion id) with hA
  set B := (O₂.powersetCard j₂).image (fun P => P.biUnion id) with hB
  have hAZ : A ⊆ Z := by
    intro x hx; obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx; exact hmem₁ P hP
  have hBZ : B ⊆ Z := by
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
    have h := hmem₂ P hP
    rw [← hm] at h
    exact h
  have hAcard : A.card = (O₁.card).choose j₁ := by
    rw [hA, Finset.card_image_of_injOn hinj₁, Finset.card_powersetCard]
  have hBcard : B.card = (O₂.card).choose j₂ := by
    rw [hB, Finset.card_image_of_injOn hinj₂, Finset.card_powersetCard]
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨P₁, hP₁, h₁⟩ := Finset.mem_image.mp hxA
    obtain ⟨P₂, hP₂, h₂⟩ := Finset.mem_image.mp hxB
    exact hcross P₁ hP₁ P₂ hP₂ (h₁.trans h₂.symm)
  calc (O₁.card).choose j₁ + (O₂.card).choose j₂
      = A.card + B.card := by rw [hAcard, hBcard]
    _ = (A ∪ B).card := (Finset.card_union_of_disjoint hABdisj).symm
    _ ≤ Z.card := Finset.card_le_card (Finset.union_subset hAZ hBZ)

open Classical in
/-- **Super-additive supply.**  The deep-band supply of `x^{d₁·j₁}` is at least
`C(|O₁|, j₁) + C(|O₂|, j₂)` when the domain carries two independent disjoint sum-zero coset
families whose unions never coincide. -/
theorem coset_supply_super_additive (dom : Fin n ↪ F)
    (O₁ O₂ : Finset (Finset (Fin n))) (d₁ d₂ j₁ j₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hdj : 2 ≤ d₁ * j₁) (hm : d₁ * j₁ = d₂ * j₂)
    (hcard₁ : ∀ X ∈ O₁, X.card = d₁) (hsum₁ : ∀ X ∈ O₁, ∑ i ∈ X, dom i = 0)
    (hdisj₁ : ∀ X ∈ O₁, ∀ X' ∈ O₁, X ≠ X' → Disjoint X X')
    (hcard₂ : ∀ X ∈ O₂, X.card = d₂) (hsum₂ : ∀ X ∈ O₂, ∑ i ∈ X, dom i = 0)
    (hdisj₂ : ∀ X ∈ O₂, ∀ X' ∈ O₂, X ≠ X' → Disjoint X X')
    (hcross : ∀ P₁ ∈ O₁.powersetCard j₁, ∀ P₂ ∈ O₂.powersetCard j₂,
        P₁.biUnion id ≠ P₂.biUnion id) :
    (O₁.card).choose j₁ + (O₂.card).choose j₂ ≤
      ((Finset.univ.filter (fun c =>
        c ∈ (rsCode dom (d₁ * j₁ - 1) : Submodule F (Fin n → F))
          ∧ d₁ * j₁ - 1 + 1 ≤ (agreeSet c (fun i => (dom i) ^ (d₁ * j₁ - 1 + 1))).card))).card := by
  rw [general_orchard_card dom (by omega : 1 ≤ d₁ * j₁ - 1),
    show d₁ * j₁ - 1 + 1 = d₁ * j₁ from by omega]
  exact coset_union_growth_two dom O₁ O₂ d₁ d₂ j₁ j₂ hd₁ hd₂ hm hcard₁ hsum₁ hdisj₁
    hcard₂ hsum₂ hdisj₂ hcross

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.coset_family_facts
#print axioms ProximityGap.PairRank.coset_union_growth_two
#print axioms ProximityGap.PairRank.coset_supply_super_additive
