import ArkLib.Research.ProximityGap.Frontier.SixthMomentAntipodalShape

/-!
# Sixth-moment witnesses from carries in base three

The first family appends an antipodal pair to the four-term relation
`a + a + a - 3*a = 0`. The second uses two consecutive carries and
contains no antipodal pair. The proofs distinguish their multiset parameters
and count all their ordered representatives.
-/

open ArkLib.ProximityGap.Frontier.SixthMomentAntipodalShape

namespace ArkLib.ProximityGap.Frontier.SixthMomentTripleCarry

variable {F : Type*} [Field F]

/-- The four-term carry relation together with an arbitrary opposite pair. -/
def pairedCarry (a b : F) : Multiset F :=
  ({a} + {a} + {a} + {-(3*a)}) + pair b

/-- Two consecutive carries of a base-three digit. -/
def doubleCarry (a : F) : Multiset F :=
  {a} + {a} + {a} + {3*a} + {3*a} + {-(9*a)}

@[simp] theorem pairedCarry_sum (a b : F) : (pairedCarry a b).sum = 0 := by
  simp [pairedCarry,pair]; ring

@[simp] theorem doubleCarry_sum (a : F) : (doubleCarry a).sum = 0 := by
  simp [doubleCarry]; ring

private theorem heavy [DecidableEq F] (a b : F) :
    3 ≤ (pairedCarry a b).count a := by simp [pairedCarry]

private theorem unique_heavy [DecidableEq F] (a b x : F) (hb : b ≠ -b)
    (hh : 3 ≤ (pairedCarry a b).count x) : x = a := by
  by_contra hx
  simp only [pairedCarry,pair,Multiset.count_add,Multiset.count_singleton,ite_eq_right hx] at hh
  have h2 : ¬ (x=b ∧ x= -b) := fun h ↦ hb (h.1.symm.trans h.2)
  split_ifs at hh <;> grind

/-- The repeated value determines the four-term carry and the remaining pair
is recovered as an unordered antipodal pair. -/
theorem pairedCarry_eq_iff (a b c d : F) (hb : b ≠ -b) :
    pairedCarry a b = pairedCarry c d ↔ a = c ∧ (b = d ∨ b = -d) := by
  classical
  constructor
  · intro he
    have hac : c=a := unique_heavy a b c hb (he ▸ heavy c d)
    subst c
    have hp : pair b = pair d := add_left_cancel he
    have hm : b ∈ pair d := hp ▸ (by simp [pair] : b ∈ pair b)
    simpa [pair] using hm
  · rintro ⟨rfl,rfl | rfl⟩
    · rfl
    · simp [pairedCarry,pair,add_comm]

private theorem symmetric_count [DecidableEq F] (x a : F) : (pair a).count x = (pair a).count (-x) := by
  simp only [pair, Multiset.count_add, Multiset.count_singleton, neg_eq_iff_eq_neg, neg_neg, add_comm]

theorem pairedCarry_not_pairable (a b : F) (ha : a ≠ -a) (hb : b ≠ -b) :
    ¬ Pairable (pairedCarry a b) := by
  classical
  rintro ⟨x,y,z,hs⟩
  have hh : 3 ≤ (pairedCarry a b).count (-a) := by
    have h₀ := heavy a b
    rw [hs] at h₀ ⊢
    simpa only [Multiset.count_add, ← symmetric_count a] using h₀
  exact ha (unique_heavy a b (-a) hb hh).symm


omit [Field F] in
private theorem pack [DecidableEq F] (a : F) (k : ℕ) (s : Multiset F) (ha : a ∉ s) :
    (Multiset.replicate k a+s).countPerms = (k+s.card).choose k*s.countPerms := by
  rw [Multiset.countPerms_filter_ne a]
  have hzero : (Multiset.replicate k a).filter (a ≠ ·) = 0 :=
    Multiset.filter_eq_nil.mpr (fun b hb ↦ by
      simpa only [not_ne_iff] using (Multiset.eq_of_mem_replicate hb).symm)
  have heq : s.filter (a ≠ ·) = s :=
    Multiset.filter_eq_self.mpr (fun b hb h ↦ ha (h ▸ hb))
  simp [Multiset.filter_add,hzero,heq,Multiset.count_eq_zero_of_notMem ha]

private def blocks (a b c d : F) (i j k l : ℕ) : Multiset F :=
  Multiset.replicate i a + (Multiset.replicate j b +
    (Multiset.replicate k c + (Multiset.replicate l d + 0)))

omit [Field F] in
private theorem blocks_perms [DecidableEq F] (a b c d : F) (i j k l : ℕ)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    (blocks a b c d i j k l).countPerms =
      (i+(j+(k+l))).choose i * ((j+(k+l)).choose j * ((k+l).choose k)) := by
  unfold blocks
  rw [pack a _ _ (by simp [Multiset.mem_replicate,hab,hac,had]),pack b _ _ (by simp [Multiset.mem_replicate,hbc,hbd]),
    pack c _ _ (by simp [Multiset.mem_replicate,hcd]),pack d _ _ (by simp)]
  simp

omit [Field F] in
private theorem three_blocks [DecidableEq F] (a b c : F) (i j k : ℕ)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    (Multiset.replicate i a + (Multiset.replicate j b + (Multiset.replicate k c + 0))).countPerms =
      (i+(j+k)).choose i * (j+k).choose j := by
  rw [pack a _ _ (by simp [Multiset.mem_replicate,hab,hac]),pack b _ _ (by simp [Multiset.mem_replicate,hbc]),pack c _ _ (by simp)]
  simp

/-- An ordinary choice of antipodal class has 120 ordered representatives. -/
theorem pairedCarry_count_generic [DecidableEq F] (a b : F)
    (h₁ : a ≠ -(3*a)) (h₂ : a ≠ b) (h₃ : a ≠ -b)
    (h₄ : -(3*a) ≠ b) (h₅ : -(3*a) ≠ -b) (h₆ : b ≠ -b) :
    (pairedCarry a b).countPerms = 120 := by
  have he : pairedCarry a b = blocks a (-(3*a)) b (-b) 3 1 1 1 := by
    simp [pairedCarry,blocks,pair,Multiset.replicate_succ,← Multiset.singleton_add,add_assoc]
  rw [he,blocks_perms _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆]
  decide

/-- The appended pair from the class of the repeated entry has 30 orderings. -/
theorem pairedCarry_count_self [DecidableEq F] (a : F)
    (h₁ : a ≠ -a) (h₂ : a ≠ -(3*a)) (h₃ : -a ≠ -(3*a)) :
    (pairedCarry a a).countPerms = 30 := by
  have he : pairedCarry a a = Multiset.replicate 4 a +
      (Multiset.replicate 1 (-a) + (Multiset.replicate 1 (-(3*a))+0)) := by
    simp only [pairedCarry,pair,Multiset.replicate_succ,Multiset.replicate_zero,
      ← Multiset.singleton_add,add_zero]
    ac_rfl
  rw [he,three_blocks _ _ _ _ _ _ h₁ h₂ h₃]
  decide

/-- Appending the class of three times the repeated entry gives 60 orderings. -/
theorem pairedCarry_count_triple [DecidableEq F] (a : F)
    (h₁ : a ≠ -(3*a)) (h₂ : a ≠ 3*a) (h₃ : -(3*a) ≠ 3*a) :
    (pairedCarry a (3*a)).countPerms = 60 := by
  have he : pairedCarry a (3*a) = Multiset.replicate 3 a +
      (Multiset.replicate 2 (-(3*a)) + (Multiset.replicate 1 (3*a)+0)) := by
    simp only [pairedCarry,pair,Multiset.replicate_succ,Multiset.replicate_zero,
      ← Multiset.singleton_add,add_zero]
    ac_rfl
  rw [he,three_blocks _ _ _ _ _ _ h₁ h₂ h₃]
  decide

/-- A two-carry sextuple has 60 orderings. -/
theorem doubleCarry_count [DecidableEq F] (a : F)
    (h₁ : a ≠ 3*a) (h₂ : a ≠ -(9*a)) (h₃ : 3*a ≠ -(9*a)) :
    (doubleCarry a).countPerms = 60 := by
  have he : doubleCarry a = Multiset.replicate 3 a +
      (Multiset.replicate 2 (3*a) + (Multiset.replicate 1 (-(9*a))+0)) := by
    simp only [doubleCarry,Multiset.replicate_succ,Multiset.replicate_zero,
      ← Multiset.singleton_add,add_zero]
    ac_rfl
  rw [he,three_blocks _ _ _ _ _ _ h₁ h₂ h₃]
  decide

/-- The triply occurring entry distinguishes the double-carry witnesses. -/
theorem doubleCarry_eq_iff (a c : F) (hc : 3*c ≠ -(9*c)) :
    doubleCarry a = doubleCarry c ↔ a = c := by
  classical
  refine ⟨fun he ↦ ?_, fun eq ↦ eq ▸ rfl⟩
  by_contra hac
  have hh : 3 ≤ (doubleCarry c).count a := by rw [← he]; simp [doubleCarry]
  simp only [doubleCarry,Multiset.count_add,Multiset.count_singleton,ite_eq_right hac] at hh
  split_ifs at hh <;> grind

/-- In characteristic greater than five, the counts at the exceptional classes
and at the no-opposite double carry need only the nonzero scale. -/
theorem special_counts [DecidableEq F] [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (5 : F)]
    (a : F) (ha : a ≠ 0) :
    (pairedCarry a a).countPerms = 30 ∧ (pairedCarry a (3*a)).countPerms = 60 ∧
      (doubleCarry a).countPerms = 60 := by
  have h2 := NeZero.ne (2 : F)
  have h3 := NeZero.ne (3 : F)
  have h5 := NeZero.ne (5 : F)
  have h2a := mul_ne_zero h2 ha
  have h4a := mul_ne_zero (pow_ne_zero 2 h2) ha
  have h6a := mul_ne_zero (mul_ne_zero h2 h3) ha
  have h10a := mul_ne_zero (mul_ne_zero h2 h5) ha
  have h12a := mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2) h3) ha
  refine ⟨pairedCarry_count_self a ?_ ?_ ?_, pairedCarry_count_triple a ?_ ?_ ?_,
    doubleCarry_count a ?_ ?_ ?_⟩ <;> intro he <;>
    first | exact h2a (by linear_combination he) | exact h2a (by linear_combination -he)
          | exact h4a (by linear_combination he) | exact h6a (by linear_combination -he)
          | exact h10a (by linear_combination he) | exact h12a (by linear_combination he)

private theorem mem_double (a x : F) : x ∈ doubleCarry a ↔ x=a ∨ x = 3*a ∨ x = -(9*a) := by
  simp [doubleCarry]

/-- With two and three nonzero, the double carry contains no opposite pair. -/
theorem no_opposite_double [NeZero (2 : F)] [NeZero (3 : F)] (a : F) (ha : a ≠ 0) :
    ∀ x ∈ doubleCarry a, -x ∉ doubleCarry a := by
  intro x hx hnx
  have h2 := NeZero.ne (2 : F)
  have h3 := NeZero.ne (3 : F)
  have h2a := mul_ne_zero h2 ha
  have h4a := mul_ne_zero (pow_ne_zero 2 h2) ha
  have h8a := mul_ne_zero (pow_ne_zero 3 h2) ha
  have h6a := mul_ne_zero (mul_ne_zero h2 h3) ha
  have h18a := mul_ne_zero (mul_ne_zero h2 (pow_ne_zero 2 h3)) ha
  rcases (mem_double _ _).mp hx with rfl | rfl | rfl <;>
    rcases (mem_double _ _).mp hnx with he | he | he <;>
    first | exact h2a (by linear_combination -he) | exact h4a (by linear_combination -he)
          | exact h8a (by linear_combination he) | exact h6a (by linear_combination -he)
          | exact h6a (by linear_combination he) | exact h18a (by linear_combination he)

theorem doubleCarry_not_pairable [NeZero (2 : F)] [NeZero (3 : F)] (a : F) (ha : a ≠ 0) :
    ¬ Pairable (doubleCarry a) := by
  rintro ⟨x,y,z,hs⟩
  have hx : x ∈ doubleCarry a := by rw [hs]; simp [pair]
  exact no_opposite_double a ha x hx (by rw [hs]; simp [pair])

theorem doubleCarry_ne_pairedCarry [NeZero (2 : F)] [NeZero (3 : F)] (a b c : F) (ha : a ≠ 0) :
    doubleCarry a ≠ pairedCarry b c := by
  intro he
  have hc : c ∈ doubleCarry a := by rw [he]; simp [pairedCarry,pair]
  exact no_opposite_double a ha c hc (by rw [he]; simp [pairedCarry,pair])

/-- The number of ordered witnesses from the pairable and two carry families. -/
theorem all_families_polynomial (t : ℚ) :
    (15*(2*t)^3-45*(2*t)^2+40*(2*t)) +
      (2*t)*(120*(t-2)+30+60) + 60*(2*t) =
    15*(2*t)^3 + 15*(2*t)^2 - 50*(2*t) := by ring

#print axioms pairedCarry_eq_iff
#print axioms pairedCarry_not_pairable
#print axioms pairedCarry_count_generic
#print axioms pairedCarry_count_self
#print axioms pairedCarry_count_triple
#print axioms special_counts
#print axioms doubleCarry_count
#print axioms doubleCarry_eq_iff
#print axioms doubleCarry_not_pairable
#print axioms doubleCarry_ne_pairedCarry
#print axioms all_families_polynomial

end ArkLib.ProximityGap.Frontier.SixthMomentTripleCarry
