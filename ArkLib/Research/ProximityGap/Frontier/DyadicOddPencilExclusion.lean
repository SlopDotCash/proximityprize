import ArkLib.Research.ProximityGap.Frontier.DyadicParityLemma
import ArkLib.Research.ProximityGap.Frontier.DyadicOddPencilCount

/-!
# Odd triples with reflection equations on `ZMod (2 ^ (e + 1))`

Composition of the parity lemma for sets with the class-count theorem. Three pairwise
disjoint sets of the same odd size `m ≥ 5` in `ZMod (2 ^ (e + 1))` that satisfy the
reflection equations in all three roles obey `3 * (m - 2) ≤ 2 ^ e`.

The reflection equations (`Refl`) are the hypothesis. For the three root sets of a three-split
pencil in characteristic zero they follow from the multiplicative independence of the
cyclotomic numbers `1 - ζ ^ r`; that step is not formalised. See
`docs/research/proximity-gap/dyadic-radius-successor-list-three.md`, Theorem A.
-/

open Finset

namespace ProximityGap.DyadicOddPencil

open ProximityGap.DyadicParity

variable (e : ℕ)

/-- Reflection equations on `β` for the pair `(α, γ)`. -/
def Refl (β α γ : Finset (ZMod (2 ^ (e + 1)))) : Prop :=
  ∃ c : ZMod (2 ^ (e + 1)) → ℂ, ∀ x ∈ β, ∀ i, par e i = 1 →
    antiDiff e α γ (x + i) + antiDiff e α γ (x - i) = c i

/-- The parity class as a Boolean. -/
noncomputable def cl (x : ZMod (2 ^ (e + 1))) : Bool := decide (par e x = 1)

/-- The antipode. -/
def anti (x : ZMod (2 ^ (e + 1))) : ZMod (2 ^ (e + 1)) := x + 2 ^ e

lemma par_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma anti_anti (x : ZMod (2 ^ (e + 1))) : anti e (anti e x) = x := by
  unfold anti
  rw [add_assoc, half_add_half, add_zero]

lemma half_ne_zero : ((2 : ZMod (2 ^ (e + 1))) ^ e) ≠ 0 := by
  intro h
  have h' : ((2 ^ e : ℕ) : ZMod (2 ^ (e + 1))) = 0 := by
    push_cast
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hle := Nat.le_of_dvd (by positivity) h'
  have : 2 ^ e < 2 ^ (e + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

lemma anti_ne (x : ZMod (2 ^ (e + 1))) : anti e x ≠ x := by
  unfold anti
  intro h
  exact half_ne_zero e (by simpa using h)

lemma cl_anti (he : 1 ≤ e) (x : ZMod (2 ^ (e + 1))) : cl e (anti e x) = cl e x := by
  unfold cl anti
  rw [map_add, par_half e he, add_zero]

/-- Reflection equations give the forcing hypothesis of the class-count theorem. -/
lemma forces_of_refl (he : 1 ≤ e) {β α γ : Finset (ZMod (2 ^ (e + 1)))} (hdisj : Disjoint α γ)
    (h : Refl e β α γ) :
    Forces (anti e) (cl e) β α ∧ Forces (anti e) (cl e) β γ := by
  obtain ⟨c, hc⟩ := h
  have main : ∀ b, 3 ≤ nb (cl e) β b →
      SymOn (anti e) (cl e) α (!b) ∧ SymOn (anti e) (cl e) γ (!b) := by
    intro b hb
    unfold nb at hb
    obtain ⟨x₁, x₂, x₃, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hb
    rw [Finset.mem_filter] at h1 h2 h3
    set w : ZMod 2 := if b then 1 else 0 with hw
    have cls_eq : ∀ x : ZMod (2 ^ (e + 1)), cl e x = b → par e x = w := by
      intro x hx
      unfold cl at hx
      cases b
      · have : ¬ par e x = 1 := by simpa using hx
        rcases par_cases (par e x) with h0 | h1
        · simpa [hw] using h0
        · exact absurd h1 this
      · have : par e x = 1 := by simpa using hx
        simpa [hw] using this
    have other : ∀ x : ZMod (2 ^ (e + 1)), cl e x = (!b) → par e x = w + 1 := by
      intro x hx
      unfold cl at hx
      cases b
      · have : par e x = 1 := by simpa using hx
        simpa [hw] using this
      · have : ¬ par e x = 1 := by simpa using hx
        rcases par_cases (par e x) with h0 | h1
        · rw [h0, hw]
          decide
        · exact absurd h1 this
    obtain ⟨sα, sγ⟩ := symmetric_on_other_class e he α γ hdisj w c h12 h13 h23
      (cls_eq x₁ h1.2) (cls_eq x₂ h2.2) (cls_eq x₃ h3.2)
      (hc x₁ h1.1) (hc x₂ h2.1) (hc x₃ h3.1)
    exact ⟨fun y hy hcy ↦ sα y hy (other y hcy), fun y hy hcy ↦ sγ y hy (other y hcy)⟩
  exact ⟨fun b hb ↦ (main b hb).1, fun b hb ↦ (main b hb).2⟩

/-- Each parity class of `ZMod (2 ^ (e + 1))` has `2 ^ e` elements. -/
lemma class_card (b : Bool) :
    (univ.filter (fun x : ZMod (2 ^ (e + 1)) ↦ cl e x = b)).card = 2 ^ e := by
  have hflip : ∀ x : ZMod (2 ^ (e + 1)), cl e (x + 1) = !(cl e x) := by
    intro x
    unfold cl
    rw [map_add, map_one]
    rcases par_cases (par e x) with h0 | h1
    · rw [h0]; decide
    · rw [h1]; decide
  have heq : (univ.filter (fun x : ZMod (2 ^ (e + 1)) ↦ cl e x = b)).card
      = (univ.filter (fun x : ZMod (2 ^ (e + 1)) ↦ cl e x = !b)).card := by
    refine Finset.card_bij (fun x _ ↦ x + 1) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, by rw [hflip, hx.2]⟩
    · intro x _ y _ hxy
      exact add_right_cancel hxy
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨y - 1, ?_, by ring⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have := hflip (y - 1)
      rw [sub_add_cancel, hy.2] at this
      cases b <;> cases hc : cl e (y - 1) <;> simp_all
  have htot : (univ.filter (fun x : ZMod (2 ^ (e + 1)) ↦ cl e x = b)).card
      + (univ.filter (fun x : ZMod (2 ^ (e + 1)) ↦ cl e x = !b)).card = 2 ^ (e + 1) := by
    have h := ProximityGap.DyadicOddPencil.nb_add' (cl e) (univ : Finset (ZMod (2 ^ (e + 1)))) b
    unfold nb at h
    rw [h, Finset.card_univ, ZMod.card]
  rw [← heq] at htot
  have hp : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
  omega

/-- **Odd triples.** Three pairwise disjoint sets of odd size `m ≥ 5` in `ZMod (2 ^ (e + 1))`
satisfying the reflection equations in all three roles have `3 * (m - 2) ≤ 2 ^ e`. -/
theorem odd_triple_bound (he : 1 ≤ e) {A B T : Finset (ZMod (2 ^ (e + 1)))} {m : ℕ}
    (hm : 5 ≤ m) (hodd : Odd m) (hA : A.card = m) (hB : B.card = m) (hT : T.card = m)
    (dAB : Disjoint A B) (dAT : Disjoint A T) (dBT : Disjoint B T)
    (rA : Refl e A B T) (rB : Refl e B A T) (rT : Refl e T A B) :
    3 * (m - 2) ≤ 2 ^ e := by
  obtain ⟨fAB, fAT⟩ := forces_of_refl e he dBT rA
  obtain ⟨fBA, fBT⟩ := forces_of_refl e he dAT rB
  obtain ⟨fTA, fTB⟩ := forces_of_refl e he dAB rT
  obtain ⟨b, hb⟩ := three_odd_sets_one_class (anti_anti e) (anti_ne e) (cl_anti e he)
    hm hodd hA hB hT dAB dAT dBT fAB fAT fBA fBT fTA fTB
  rw [class_card] at hb
  exact hb

end ProximityGap.DyadicOddPencil

#print axioms ProximityGap.DyadicOddPencil.odd_triple_bound
