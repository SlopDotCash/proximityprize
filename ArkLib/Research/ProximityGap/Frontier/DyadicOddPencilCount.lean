import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Three odd sets forced into one parity class

Combinatorial core of "Theorem A" in
`docs/research/proximity-gap/dyadic-radius-successor-list-three.md`.

`X` is a finite set with a fixed-point-free involution `a` (the antipode) and a two-valued
class function `c` preserved by `a`. Three pairwise disjoint sets of the same odd size `m ≥ 5`
are given. Whenever one of them has three points in a class, each of the other two is assumed
symmetric on the opposite class (this is what the parity lemma supplies for a three-split
pencil). Then all three sets have at most two points outside one common class, so that class
has at least `3 * (m - 2)` points.

The hypothesis `Forces` is an assumption here. Its derivation from a polynomial pencil uses
the cyclotomic-unit lattice and is not formalised.
-/

open Finset

namespace ProximityGap.DyadicOddPencil

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Number of points of `S` in class `b`. -/
def nb (c : X → Bool) (S : Finset X) (b : Bool) : ℕ := (S.filter (fun x ↦ c x = b)).card

/-- `S` is closed under the antipode inside class `b`. -/
def SymOn (a : X → X) (c : X → Bool) (S : Finset X) (b : Bool) : Prop :=
  ∀ x ∈ S, c x = b → a x ∈ S

/-- Three points of `S` in a class force `S'` to be symmetric on the other class. -/
def Forces (a : X → X) (c : X → Bool) (S S' : Finset X) : Prop :=
  ∀ b, 3 ≤ nb c S b → SymOn a c S' (!b)

lemma nb_add (c : X → Bool) (S : Finset X) : nb c S true + nb c S false = S.card := by
  unfold nb
  have h : S.filter (fun x ↦ c x = false) = S.filter (fun x ↦ ¬ c x = true) := by
    apply Finset.filter_congr
    intro x _
    cases c x <;> simp
  rw [h, Finset.card_filter_add_card_filter_not]

lemma nb_add' (c : X → Bool) (S : Finset X) (b : Bool) : nb c S b + nb c S (!b) = S.card := by
  cases b
  · simpa [add_comm] using nb_add c S
  · simpa using nb_add c S

/-- A set symmetric on a class has an even number of points there. -/
lemma even_nb_of_symOn {a : X → X} {c : X → Bool} (ha : ∀ x, a (a x) = x) (hfix : ∀ x, a x ≠ x)
    (hc : ∀ x, c (a x) = c x) {S : Finset X} {b : Bool} (h : SymOn a c S b) :
    Even (nb c S b) := by
  unfold nb
  have hsum : ∑ x ∈ S.filter (fun x ↦ c x = b), (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun x _ ↦ a x) ?_ ?_ ?_ ?_
    · intro x _
      decide
    · intro x _ _
      exact hfix x
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨h x hx.1 hx.2, by rw [hc]; exact hx.2⟩
    · intro x _
      exact ha x
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact (ZMod.natCast_eq_zero_iff_even).mp hsum

/-- If `S₁` has three points in class `b` and `S₃` has three in the other class, an odd set
forced by both cannot exist. -/
lemma mixed_false {a : X → X} {c : X → Bool} (ha : ∀ x, a (a x) = x) (hfix : ∀ x, a x ≠ x)
    (hc : ∀ x, c (a x) = c x) {S₁ S₂ S₃ : Finset X} {b : Bool}
    (h12 : Forces a c S₁ S₂) (h32 : Forces a c S₃ S₂)
    (h1 : 3 ≤ nb c S₁ b) (h3 : 3 ≤ nb c S₃ (!b)) (hodd : Odd S₂.card) : False := by
  have e1 : Even (nb c S₂ (!b)) := even_nb_of_symOn ha hfix hc (h12 b h1)
  have e2 : Even (nb c S₂ b) := by
    have := even_nb_of_symOn ha hfix hc (h32 (!b) h3)
    simpa using this
  have hsum := nb_add' c S₂ b
  rw [← hsum] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (e2.add e1)

/-- **Class count.** Under the forcing hypotheses, three pairwise disjoint sets of odd size
`m ≥ 5` leave at most two points each outside one common class `b`; hence that class has at
least `3 * (m - 2)` points. -/
theorem three_odd_sets_one_class {a : X → X} {c : X → Bool} (ha : ∀ x, a (a x) = x)
    (hfix : ∀ x, a x ≠ x) (hc : ∀ x, c (a x) = c x) {A B T : Finset X} {m : ℕ}
    (hm : 5 ≤ m) (hodd : Odd m) (hA : A.card = m) (hB : B.card = m) (hT : T.card = m)
    (dAB : Disjoint A B) (dAT : Disjoint A T) (dBT : Disjoint B T)
    (fAB : Forces a c A B) (fAT : Forces a c A T) (fBA : Forces a c B A)
    (fBT : Forces a c B T) (fTA : Forces a c T A) (fTB : Forces a c T B) :
    ∃ b, 3 * (m - 2) ≤ (univ.filter (fun x : X ↦ c x = b)).card := by
  -- every set has a class with at most two points
  have small : ∀ S S' : Finset X, S.card = m → S'.card = m → Forces a c S S' →
      ∃ b, nb c S b ≤ 2 := by
    intro S S' hS hS' f
    by_contra hcon
    push_neg at hcon
    have ht : 3 ≤ nb c S true := hcon true
    have hf : 3 ≤ nb c S false := hcon false
    have e1 : Even (nb c S' false) := by
      have := even_nb_of_symOn ha hfix hc (f true ht)
      simpa using this
    have e2 : Even (nb c S' true) := by
      have := even_nb_of_symOn ha hfix hc (f false hf)
      simpa using this
    have hsum := nb_add c S'
    rw [hS'] at hsum
    rw [← hsum] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (e2.add e1)
  obtain ⟨bA, hbA⟩ := small A B hA hB fAB
  obtain ⟨bB, hbB⟩ := small B A hB hA fBA
  obtain ⟨bT, hbT⟩ := small T A hT hA fTA
  -- the complementary class of each set holds at least `m - 2 ≥ 3` points
  have big : ∀ S : Finset X, S.card = m → ∀ b, nb c S b ≤ 2 → m - 2 ≤ nb c S (!b) := by
    intro S hS b hb
    have := nb_add' c S b
    omega
  have gA := big A hA bA hbA
  have gB := big B hB bB hbB
  have gT := big T hT bT hbT
  have oA : Odd A.card := hA ▸ hodd
  have oB : Odd B.card := hB ▸ hodd
  have oT : Odd T.card := hT ▸ hodd
  -- the three small classes coincide
  have hAB : bA = bB := by
    by_contra hne
    have hB' : (!bA) = bB := by cases bA <;> cases bB <;> simp_all
    -- A is big on !bA = bB, B is big on !bB = bA; T shares its big class with one of them
    rcases Bool.eq_or_eq_not bT bA with hTA | hTA
    · -- T and A big on !bA; B big on bA = !(!bA)
      have h1 : 3 ≤ nb c T (!bA) := by rw [← hTA]; omega
      have h3 : 3 ≤ nb c B (!(!bA)) := by rw [hB']; omega
      exact mixed_false ha hfix hc fTA fBA h1 h3 oA
    · -- T big on !bT = bA, together with B (big on !bB = bA); A big on !bA
      have hT' : (!bT) = bA := by rw [hTA]; simp
      have h1 : 3 ≤ nb c T bA := by rw [← hT']; omega
      have hB'' : (!bB) = bA := by rw [← hB']; simp
      have h1' : 3 ≤ nb c B bA := by rw [← hB'']; omega
      have h3 : 3 ≤ nb c A (!bA) := by omega
      exact mixed_false ha hfix hc fTB fAB h1 h3 oB
  have hAT : bA = bT := by
    by_contra hne
    have hT' : (!bT) = bA := by cases bA <;> cases bT <;> simp_all
    -- A and B big on !bA; T big on bA
    have h1 : 3 ≤ nb c A (!bA) := by omega
    have h3 : 3 ≤ nb c T (!(!bA)) := by
      have : (!(!bA)) = (!bT) := by rw [hT']; simp
      rw [this]; omega
    exact mixed_false ha hfix hc fAB fTB h1 h3 oB
  subst hAB
  subst hAT
  refine ⟨!bA, ?_⟩
  -- disjoint filtered pieces inside the class
  have hsub : (A.filter (fun x ↦ c x = !bA)) ∪ (B.filter (fun x ↦ c x = !bA))
      ∪ (T.filter (fun x ↦ c x = !bA)) ⊆ univ.filter (fun x : X ↦ c x = !bA) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with (h | h) | h <;> exact h.2
  have hcard := Finset.card_le_card hsub
  have d1 : Disjoint (A.filter (fun x ↦ c x = !bA)) (B.filter (fun x ↦ c x = !bA)) :=
    Finset.disjoint_filter_filter dAB
  have d2 : Disjoint ((A.filter (fun x ↦ c x = !bA)) ∪ (B.filter (fun x ↦ c x = !bA)))
      (T.filter (fun x ↦ c x = !bA)) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter_filter dAT, Finset.disjoint_filter_filter dBT⟩
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1] at hcard
  unfold nb at gA gB gT
  omega

end ProximityGap.DyadicOddPencil

#print axioms ProximityGap.DyadicOddPencil.three_odd_sets_one_class
