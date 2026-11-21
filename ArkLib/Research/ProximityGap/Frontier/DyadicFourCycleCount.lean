import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The 4-cycle overlap pattern is inconsistent with antipodal forcing

Combinatorial core of Section 4 of
`docs/research/proximity-gap/dyadic-radius-successor-list-three.md`.

`X` carries a fixed-point-free involution `a` and an `a`-invariant two-valued class function `c`.
Four pairwise disjoint sets `Q₀,…,Q₃` of the same odd size `q ≥ 5` and four further points
`s₀,…,s₃` (with `sₖ` the overlap site of heads `k, k+1`) are given, and each class contains
`2 * q + 2` of these points. Vertex `j` forces: three points of `Qⱼ` in a class make both
neighbour sets `Q_{j-1} ∪ {s_{j-2}}` and `Q_{j+1} ∪ {s_{j+1}}` symmetric on the other class.
These hypotheses are contradictory.

The forcing hypotheses are assumptions here; they come from the parity lemma applied to the
vanisher-ratio conditions of a 4-cycle, whose derivation uses cyclotomic units and is not
formalised. The arithmetic core `cycle_arith` is proved by splitting on the eight threshold
conditions and calling `omega` in each case.
-/

open Finset

namespace ProximityGap.DyadicFourCycle

set_option maxHeartbeats 0 in
/-- The arithmetic core: the parity, two-special and two-owner constraints of a 4-cycle are
inconsistent with the class counts once the common odd size is at least five. -/
theorem cycle_arith (q x0f x0t x1f x1t x2f x2t x3f x3t c0f c0t c1f c1t c2f c2t c3f c3t : ℕ) (hq : 5 ≤ q) (hodd : q % 2 = 1)
    (hx0 : x0t + x0f = q) (hc0 : c0t + c0f = 1)
    (hx1 : x1t + x1f = q) (hc1 : c1t + c1f = 1)
    (hx2 : x2t + x2f = q) (hc2 : c2t + c2f = 1)
    (hx3 : x3t + x3f = q) (hc3 : c3t + c3f = 1)
    (hsf : x0f + x1f + x2f + x3f + c0f + c1f + c2f + c3f = 2 * q + 2)
    (hst : x0t + x1t + x2t + x3t + c0t + c1t + c2t + c3t = 2 * q + 2)
    (pE0f : 3 ≤ x1t → (x0f + c3f) % 2 = 0)
    (pG0f : 3 ≤ x3t → (x0f + c0f) % 2 = 0)
    (f10f : 3 ≤ x1t → 3 ≤ x3t → c3f = 0 ∧ c0f = 0)
    (pE0t : 3 ≤ x1f → (x0t + c3t) % 2 = 0)
    (pG0t : 3 ≤ x3f → (x0t + c0t) % 2 = 0)
    (f10t : 3 ≤ x1f → 3 ≤ x3f → c3t = 0 ∧ c0t = 0)
    (pE1f : 3 ≤ x2t → (x1f + c0f) % 2 = 0)
    (pG1f : 3 ≤ x0t → (x1f + c1f) % 2 = 0)
    (f11f : 3 ≤ x2t → 3 ≤ x0t → c0f = 0 ∧ c1f = 0)
    (pE1t : 3 ≤ x2f → (x1t + c0t) % 2 = 0)
    (pG1t : 3 ≤ x0f → (x1t + c1t) % 2 = 0)
    (f11t : 3 ≤ x2f → 3 ≤ x0f → c0t = 0 ∧ c1t = 0)
    (pE2f : 3 ≤ x3t → (x2f + c1f) % 2 = 0)
    (pG2f : 3 ≤ x1t → (x2f + c2f) % 2 = 0)
    (f12f : 3 ≤ x3t → 3 ≤ x1t → c1f = 0 ∧ c2f = 0)
    (pE2t : 3 ≤ x3f → (x2t + c1t) % 2 = 0)
    (pG2t : 3 ≤ x1f → (x2t + c2t) % 2 = 0)
    (f12t : 3 ≤ x3f → 3 ≤ x1f → c1t = 0 ∧ c2t = 0)
    (pE3f : 3 ≤ x0t → (x3f + c2f) % 2 = 0)
    (pG3f : 3 ≤ x2t → (x3f + c3f) % 2 = 0)
    (f13f : 3 ≤ x0t → 3 ≤ x2t → c2f = 0 ∧ c3f = 0)
    (pE3t : 3 ≤ x0f → (x3t + c2t) % 2 = 0)
    (pG3t : 3 ≤ x2f → (x3t + c3t) % 2 = 0)
    (f13t : 3 ≤ x0f → 3 ≤ x2f → c2t = 0 ∧ c3t = 0)
    (ow0f : 3 ≤ x3t → 3 ≤ x2t → c0f = 0)
    (ow0t : 3 ≤ x3f → 3 ≤ x2f → c0t = 0)
    (ow1f : 3 ≤ x0t → 3 ≤ x3t → c1f = 0)
    (ow1t : 3 ≤ x0f → 3 ≤ x3f → c1t = 0)
    (ow2f : 3 ≤ x1t → 3 ≤ x0t → c2f = 0)
    (ow2t : 3 ≤ x1f → 3 ≤ x0f → c2t = 0)
    (ow3f : 3 ≤ x2t → 3 ≤ x1t → c3f = 0)
    (ow3t : 3 ≤ x2f → 3 ≤ x1f → c3t = 0)
    : False := by
  rcases Nat.lt_or_ge x0t 3 with a0t | a0t <;>
  rcases Nat.lt_or_ge x0f 3 with a0f | a0f <;>
  rcases Nat.lt_or_ge x1t 3 with a1t | a1t <;>
  rcases Nat.lt_or_ge x1f 3 with a1f | a1f <;>
  rcases Nat.lt_or_ge x2t 3 with a2t | a2t <;>
  rcases Nat.lt_or_ge x2f 3 with a2f | a2f <;>
  rcases Nat.lt_or_ge x3t 3 with a3t | a3t <;>
  rcases Nat.lt_or_ge x3f 3 with a3f | a3f <;>
  (
    try have e_pE0f := pE0f (by assumption)
    try have e_pG0f := pG0f (by assumption)
    try have e_f10f := f10f (by assumption) (by assumption)
    try have e_pE0t := pE0t (by assumption)
    try have e_pG0t := pG0t (by assumption)
    try have e_f10t := f10t (by assumption) (by assumption)
    try have e_pE1f := pE1f (by assumption)
    try have e_pG1f := pG1f (by assumption)
    try have e_f11f := f11f (by assumption) (by assumption)
    try have e_pE1t := pE1t (by assumption)
    try have e_pG1t := pG1t (by assumption)
    try have e_f11t := f11t (by assumption) (by assumption)
    try have e_pE2f := pE2f (by assumption)
    try have e_pG2f := pG2f (by assumption)
    try have e_f12f := f12f (by assumption) (by assumption)
    try have e_pE2t := pE2t (by assumption)
    try have e_pG2t := pG2t (by assumption)
    try have e_f12t := f12t (by assumption) (by assumption)
    try have e_pE3f := pE3f (by assumption)
    try have e_pG3f := pG3f (by assumption)
    try have e_f13f := f13f (by assumption) (by assumption)
    try have e_pE3t := pE3t (by assumption)
    try have e_pG3t := pG3t (by assumption)
    try have e_f13t := f13t (by assumption) (by assumption)
    try have e_ow0f := ow0f (by assumption) (by assumption)
    try have e_ow0t := ow0t (by assumption) (by assumption)
    try have e_ow1f := ow1f (by assumption) (by assumption)
    try have e_ow1t := ow1t (by assumption) (by assumption)
    try have e_ow2f := ow2f (by assumption) (by assumption)
    try have e_ow2t := ow2t (by assumption) (by assumption)
    try have e_ow3f := ow3f (by assumption) (by assumption)
    try have e_ow3t := ow3t (by assumption) (by assumption)
    clear pE0f pG0f f10f pE0t pG0t f10t pE1f pG1f f11f pE1t pG1t f11t pE2f pG2f f12f pE2t pG2t f12t pE3f pG3f f13f pE3t pG3t f13t ow0f ow0t ow1f ow1t ow2f ow2t ow3f ow3t
    omega)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Number of points of `S` in class `b`. -/
def nb (c : X → Bool) (S : Finset X) (b : Bool) : ℕ := (S.filter (fun x ↦ c x = b)).card

/-- Indicator that the point `s` lies in class `b`. -/
def cls (c : X → Bool) (s : X) (b : Bool) : ℕ := if c s = b then 1 else 0

/-- `S` is closed under the antipode inside class `b`. -/
def SymOn (a : X → X) (c : X → Bool) (S : Finset X) (b : Bool) : Prop :=
  ∀ x ∈ S, c x = b → a x ∈ S

lemma nb_add (c : X → Bool) (S : Finset X) : nb c S true + nb c S false = S.card := by
  unfold nb
  have h : S.filter (fun x ↦ c x = false) = S.filter (fun x ↦ ¬ c x = true) := by
    apply Finset.filter_congr
    intro x _
    cases c x <;> simp
  rw [h, Finset.card_filter_add_card_filter_not]

lemma cls_add (c : X → Bool) (s : X) : cls c s true + cls c s false = 1 := by
  unfold cls
  cases c s <;> simp

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

/-- Parity of a class count when the set becomes symmetric after adding one point. -/
lemma parity_insert {a : X → X} {c : X → Bool} (ha : ∀ x, a (a x) = x) (hfix : ∀ x, a x ≠ x)
    (hc : ∀ x, c (a x) = c x) {Q : Finset X} {s : X} {b : Bool} (hs : s ∉ Q)
    (h : SymOn a c (insert s Q) b) : (nb c Q b + cls c s b) % 2 = 0 := by
  have hev := even_nb_of_symOn ha hfix hc h
  have hcount : nb c (insert s Q) b = nb c Q b + cls c s b := by
    unfold nb cls
    rw [Finset.filter_insert]
    by_cases hsb : c s = b
    · have hnot : s ∉ Q.filter (fun x ↦ c x = b) := fun hmem ↦ hs (Finset.mem_filter.mp hmem).1
      simp [hsb, Finset.card_insert_of_notMem hnot]
    · simp [hsb]
  rw [hcount] at hev
  exact Nat.even_iff.mp hev

/-- One set cannot be completed to a symmetric set on a class by two different points of
that class. -/
lemma two_specials {a : X → X} {c : X → Bool} (ha : ∀ x, a (a x) = x) (hfix : ∀ x, a x ≠ x)
    (hc : ∀ x, c (a x) = c x) {Q : Finset X} {s s' : X} {b : Bool} (hne : s ≠ s')
    (hs : s ∉ Q) (hs' : s' ∉ Q) (h : SymOn a c (insert s Q) b) (h' : SymOn a c (insert s' Q) b) :
    cls c s b = 0 ∧ cls c s' b = 0 := by
  have key : ∀ t t' : X, t ≠ t' → t ∉ Q → SymOn a c (insert t Q) b →
      SymOn a c (insert t' Q) b → cls c t b = 0 := by
    intro t t' hne ht h1 h2
    unfold cls
    by_contra hcon
    have hcb : c t = b := by
      by_contra hne'
      exact hcon (by simp [hne'])
    have h3 : a t ∈ insert t Q := h1 t (Finset.mem_insert_self t Q) hcb
    have h4 : a t ∈ Q := by
      rcases Finset.mem_insert.mp h3 with h5 | h5
      · exact absurd h5 (hfix t)
      · exact h5
    have h6 : a (a t) ∈ insert t' Q :=
      h2 (a t) (Finset.mem_insert_of_mem h4) (by rw [hc]; exact hcb)
    rw [ha] at h6
    rcases Finset.mem_insert.mp h6 with h7 | h7
    · exact hne h7
    · exact ht h7
  exact ⟨key s s' hne hs h h', key s' s (Ne.symm hne) hs' h' h⟩

/-- A point of class `b` cannot complete two disjoint sets to symmetric sets on `b`. -/
lemma two_owners {a : X → X} {c : X → Bool} (ha : ∀ x, a (a x) = x) (hfix : ∀ x, a x ≠ x)
    (hc : ∀ x, c (a x) = c x) {Q Q' : Finset X} {s : X} {b : Bool} (hd : Disjoint Q Q')
    (hs : s ∉ Q) (hs' : s ∉ Q') (h : SymOn a c (insert s Q) b)
    (h' : SymOn a c (insert s Q') b) : cls c s b = 0 := by
  unfold cls
  by_contra hcon
  have hcb : c s = b := by
    by_contra hne'
    exact hcon (by simp [hne'])
  have mem : ∀ R : Finset X, SymOn a c (insert s R) b → a s ∈ R := by
    intro R hR
    rcases Finset.mem_insert.mp (hR s (Finset.mem_insert_self s R) hcb) with h5 | h5
    · exact absurd h5 (hfix s)
    · exact h5
  exact (Finset.disjoint_left.mp hd (mem Q h)) (mem Q' h')

/-- **The 4-cycle is impossible.** -/
theorem four_cycle_false {a : X → X} {c : X → Bool} (ha : ∀ x, a (a x) = x)
    (hfix : ∀ x, a x ≠ x) (hc : ∀ x, c (a x) = c x)
    {Q0 Q1 Q2 Q3 : Finset X} {s0 s1 s2 s3 : X} {q : ℕ} (hq : 5 ≤ q) (hodd : q % 2 = 1)
    (k0 : Q0.card = q) (k1 : Q1.card = q) (k2 : Q2.card = q) (k3 : Q3.card = q)
    (d01 : Disjoint Q0 Q1) (d12 : Disjoint Q1 Q2) (d23 : Disjoint Q2 Q3) (d30 : Disjoint Q3 Q0)
    (s01 : s0 ≠ s1) (s12 : s1 ≠ s2) (s23 : s2 ≠ s3) (s30 : s3 ≠ s0)
    (n00 : s0 ∉ Q0) (n01 : s0 ∉ Q1) (n11 : s1 ∉ Q1) (n12 : s1 ∉ Q2)
    (n22 : s2 ∉ Q2) (n23 : s2 ∉ Q3) (n33 : s3 ∉ Q3) (n30 : s3 ∉ Q0)
    (classf : nb c Q0 false + nb c Q1 false + nb c Q2 false + nb c Q3 false
      + cls c s0 false + cls c s1 false + cls c s2 false + cls c s3 false = 2 * q + 2)
    (classt : nb c Q0 true + nb c Q1 true + nb c Q2 true + nb c Q3 true
      + cls c s0 true + cls c s1 true + cls c s2 true + cls c s3 true = 2 * q + 2)
    (F0t : 3 ≤ nb c Q0 true → SymOn a c (insert s2 Q3) (!true) ∧
      SymOn a c (insert s1 Q1) (!true))
    (F0f : 3 ≤ nb c Q0 false → SymOn a c (insert s2 Q3) (!false) ∧
      SymOn a c (insert s1 Q1) (!false))
    (F1t : 3 ≤ nb c Q1 true → SymOn a c (insert s3 Q0) (!true) ∧
      SymOn a c (insert s2 Q2) (!true))
    (F1f : 3 ≤ nb c Q1 false → SymOn a c (insert s3 Q0) (!false) ∧
      SymOn a c (insert s2 Q2) (!false))
    (F2t : 3 ≤ nb c Q2 true → SymOn a c (insert s0 Q1) (!true) ∧
      SymOn a c (insert s3 Q3) (!true))
    (F2f : 3 ≤ nb c Q2 false → SymOn a c (insert s0 Q1) (!false) ∧
      SymOn a c (insert s3 Q3) (!false))
    (F3t : 3 ≤ nb c Q3 true → SymOn a c (insert s1 Q2) (!true) ∧
      SymOn a c (insert s0 Q0) (!true))
    (F3f : 3 ≤ nb c Q3 false → SymOn a c (insert s1 Q2) (!false) ∧
      SymOn a c (insert s0 Q0) (!false))
    : False := by
  exact cycle_arith q (nb c Q0 false) (nb c Q0 true) (nb c Q1 false) (nb c Q1 true) (nb c Q2 false) (nb c Q2 true) (nb c Q3 false) (nb c Q3 true)
    (cls c s0 false) (cls c s0 true) (cls c s1 false) (cls c s1 true) (cls c s2 false) (cls c s2 true) (cls c s3 false) (cls c s3 true)
    hq hodd
    ((nb_add c Q0).trans k0) (cls_add c s0)
    ((nb_add c Q1).trans k1) (cls_add c s1)
    ((nb_add c Q2).trans k2) (cls_add c s2)
    ((nb_add c Q3).trans k3) (cls_add c s3)
    classf classt
    (fun h ↦ parity_insert ha hfix hc (n30) (by simpa using (F1t h).1))
    (fun h ↦ parity_insert ha hfix hc (n00) (by simpa using (F3t h).2))
    (fun h h' ↦ two_specials ha hfix hc (s30) (n30) (n00) (by simpa using (F1t h).1) (by simpa using (F3t h').2))
    (fun h ↦ parity_insert ha hfix hc (n30) (by simpa using (F1f h).1))
    (fun h ↦ parity_insert ha hfix hc (n00) (by simpa using (F3f h).2))
    (fun h h' ↦ two_specials ha hfix hc (s30) (n30) (n00) (by simpa using (F1f h).1) (by simpa using (F3f h').2))
    (fun h ↦ parity_insert ha hfix hc (n01) (by simpa using (F2t h).1))
    (fun h ↦ parity_insert ha hfix hc (n11) (by simpa using (F0t h).2))
    (fun h h' ↦ two_specials ha hfix hc (s01) (n01) (n11) (by simpa using (F2t h).1) (by simpa using (F0t h').2))
    (fun h ↦ parity_insert ha hfix hc (n01) (by simpa using (F2f h).1))
    (fun h ↦ parity_insert ha hfix hc (n11) (by simpa using (F0f h).2))
    (fun h h' ↦ two_specials ha hfix hc (s01) (n01) (n11) (by simpa using (F2f h).1) (by simpa using (F0f h').2))
    (fun h ↦ parity_insert ha hfix hc (n12) (by simpa using (F3t h).1))
    (fun h ↦ parity_insert ha hfix hc (n22) (by simpa using (F1t h).2))
    (fun h h' ↦ two_specials ha hfix hc (s12) (n12) (n22) (by simpa using (F3t h).1) (by simpa using (F1t h').2))
    (fun h ↦ parity_insert ha hfix hc (n12) (by simpa using (F3f h).1))
    (fun h ↦ parity_insert ha hfix hc (n22) (by simpa using (F1f h).2))
    (fun h h' ↦ two_specials ha hfix hc (s12) (n12) (n22) (by simpa using (F3f h).1) (by simpa using (F1f h').2))
    (fun h ↦ parity_insert ha hfix hc (n23) (by simpa using (F0t h).1))
    (fun h ↦ parity_insert ha hfix hc (n33) (by simpa using (F2t h).2))
    (fun h h' ↦ two_specials ha hfix hc (s23) (n23) (n33) (by simpa using (F0t h).1) (by simpa using (F2t h').2))
    (fun h ↦ parity_insert ha hfix hc (n23) (by simpa using (F0f h).1))
    (fun h ↦ parity_insert ha hfix hc (n33) (by simpa using (F2f h).2))
    (fun h h' ↦ two_specials ha hfix hc (s23) (n23) (n33) (by simpa using (F0f h).1) (by simpa using (F2f h').2))
    (fun h h' ↦ two_owners ha hfix hc (d01) (n00) (n01) (by simpa using (F3t h).2) (by simpa using (F2t h').1))
    (fun h h' ↦ two_owners ha hfix hc (d01) (n00) (n01) (by simpa using (F3f h).2) (by simpa using (F2f h').1))
    (fun h h' ↦ two_owners ha hfix hc (d12) (n11) (n12) (by simpa using (F0t h).2) (by simpa using (F3t h').1))
    (fun h h' ↦ two_owners ha hfix hc (d12) (n11) (n12) (by simpa using (F0f h).2) (by simpa using (F3f h').1))
    (fun h h' ↦ two_owners ha hfix hc (d23) (n22) (n23) (by simpa using (F1t h).2) (by simpa using (F0t h').1))
    (fun h h' ↦ two_owners ha hfix hc (d23) (n22) (n23) (by simpa using (F1f h).2) (by simpa using (F0f h').1))
    (fun h h' ↦ two_owners ha hfix hc (d30) (n33) (n30) (by simpa using (F2t h).2) (by simpa using (F1t h').1))
    (fun h h' ↦ two_owners ha hfix hc (d30) (n33) (n30) (by simpa using (F2f h).2) (by simpa using (F1f h').1))

end ProximityGap.DyadicFourCycle

#print axioms ProximityGap.DyadicFourCycle.four_cycle_false
