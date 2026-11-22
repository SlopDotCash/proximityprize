/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Two equal symmetrisations force a dyadic reflection

The antipodal difference of two disjoint locator indicators takes integer values.
A two-centre identity reflects this function, and a third centre kills it.
-/

namespace ProximityGap.DyadicAntiperiodicReflection

/-- Every nonzero translation of a dyadic cyclic group generates the antipode. -/
theorem reaches_antipode (k : ℕ) (d : ZMod (2^(k+1))) (hd : d ≠ 0) :
    ∃ m : ℕ, m • d = (2^k : ℕ) := by
  let : NeZero (2^(k+1)) := ⟨by positivity⟩
  have hv : d.val ≠ 0 := by
    intro h
    apply hd
    rw [← ZMod.natCast_zmod_val d, h]
    exact Nat.cast_zero
  obtain ⟨t,u,⟨v,ho⟩,hu⟩ := Nat.exists_eq_two_pow_mul_odd hv
  have hpos : 0 < u := by omega
  have hle : 2^t ≤ d.val := by rw [hu]; exact Nat.le_mul_of_pos_right _ hpos
  have ht : t ≤ k := by
    have hp := hle.trans_lt d.val_lt
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show k+1 ≤ t by omega)
    omega
  refine ⟨2^(k-t), ?_⟩
  have he : 2^(k-t)*d.val = 2^(k+1)*v + 2^k := by
    rw [hu, ← Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel ht, ho, pow_succ]
    ring
  rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val d, ← Nat.cast_mul, he,
    Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]

private theorem same_after_steps {G : Type*} [AddCommGroup G] (f : G → ℤ) (d : G)
    (hp : ∀ j, f (j+d) = f j) (j : G) (m : ℕ) : f (j + m • d) = f j := by
  induction m with
  | zero => simp
  | succ m ih => simpa only [succ_nsmul, ← add_assoc, hp] using ih

private theorem period_kills (k : ℕ) (f : ZMod (2^(k+1)) → ℤ)
    (ha : ∀ j, f (j + (2^k : ℕ)) = -f j)
    (d : ZMod (2^(k+1))) (hd : d ≠ 0) (hp : ∀ j, f (j+d) = f j) :
    ∀ j, f j = 0 := by
  obtain ⟨m,hm⟩ := reaches_antipode k d hd
  intro j
  have h := same_after_steps f d hp j m
  rw [hm,ha] at h
  omega

/-- Equal symmetric sums around two distinct centres force reflection symmetry. -/
theorem two_centres (k : ℕ) (f : ZMod (2^(k+1)) → ℤ)
    (ha : ∀ j, f (j + (2^k : ℕ)) = -f j)
    (x y : ZMod (2^(k+1))) (hne : x ≠ y)
    (hs : ∀ i, f (x+i)+f (x-i) = f (y+i)+f (y-i)) :
    ∀ j, f j = f (x+y-j) := by
  let D (j : ZMod (2^(k+1))) := f j - f (x+y-j)
  have hh : (2^k : ZMod (2^(k+1))) + (2^k : ZMod (2^(k+1))) = 0 := by
    simpa only [pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, mul_two] using
      (ZMod.natCast_self (2^(k+1)))
  have hA (j) : D (j + (2^k : ℕ)) = -D j := by
    have eq : x+y-(j+(2^k : ℕ)) = (x+y-j)+(2^k : ℕ) := by
      push_cast
      linear_combination -hh
    unfold D
    rw [eq, ha, ha]
    ring
  have hP (j) : D (j+(y-x)) = D j := by
    have h := hs (j-x)
    have e₁ : x+(j-x)=j := by abel
    have e₂ : y+(j-x)=j+(y-x) := by abel
    have e₃ : y-(j-x)=x+y-j := by abel
    have e₄ : x-(j-x)=x+y-(j+(y-x)) := by abel
    rw [e₁,e₂,e₃,e₄] at h
    unfold D
    omega
  intro j
  exact sub_eq_zero.mp (period_kills k D hA (y-x) (sub_ne_zero.mpr hne.symm) hP j)

/-- Three distinct equal symmetrisations annihilate the antipodal difference. -/
theorem three_centres (k : ℕ) (f : ZMod (2^(k+1)) → ℤ)
    (ha : ∀ j, f (j + (2^k : ℕ)) = -f j)
    (x y z : ZMod (2^(k+1))) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : ∀ i, f (x+i)+f (x-i) = f (y+i)+f (y-i))
    (ht : ∀ i, f (x+i)+f (x-i) = f (z+i)+f (z-i)) :
    ∀ j, f j = 0 := by
  have h₁ := two_centres k f ha x y hxy hs
  have h₂ := two_centres k f ha x z hxz ht
  apply period_kills k f ha (z-y) (sub_ne_zero.mpr hyz.symm)
  intro j
  calc
    f (j+(z-y)) = f (x+z-(x+y-j)) := by congr 1; abel
    _ = f (x+y-j) := (h₂ _).symm
    _ = f j := (h₁ j).symm

/-- Antisymmetry about two distinct reflection axes forces a half-turn
antiperiodic integer signal to vanish. -/
theorem two_antireflections (k : ℕ) (f : ZMod (2^(k+1)) → ℤ)
    (ha : ∀ j, f (j + (2^k : ℕ)) = -f j)
    (a b : ZMod (2^(k+1))) (hne : a ≠ b)
    (h₁ : ∀ j, f (a-j) = -f j) (h₂ : ∀ j, f (b-j) = -f j) :
    ∀ j, f j = 0 := by
  apply period_kills k f ha (b-a) (sub_ne_zero.mpr hne.symm)
  intro j
  calc
    f (j+(b-a)) = f (b-(a-j)) := by congr 1; abel
    _ = -f (a-j) := h₂ _
    _ = f j := by rw [h₁, neg_neg]

/-- Three disjoint fibers have at most two occupants on each half of a four-site
orbit. If all three signed differences agree, both half populations match. -/
theorem three_fibers_in_two_site_halves (a b c A B C : ℕ)
    (left : a+b+c ≤ 2) (right : A+B+C ≤ 2)
    (hab : (a : ℤ) - A = (b : ℤ) - B) (hbc : (b : ℤ) - B = (c : ℤ) - C) :
    a = A ∧ b = B ∧ c = C := by
  omega

/-- Equal half populations on every block make the whole fiber even. -/
theorem balanced_total_even {ι : Type*} [Fintype ι] (a b : ι → ℕ) (h : ∀ j, a j = b j) :
    Even (∑ j, (a j + b j)) := by
  refine ⟨∑ j, b j, ?_⟩
  simp_rw [h, Finset.sum_add_distrib]

private def otherDifference (i : Fin 3) (d : Fin 3 → ℤ) : ℤ :=
  match i.val with
  | 0 => d 1 - d 2
  | 1 => d 0 - d 2
  | _ => d 0 - d 1

private lemma two_other_differences (d : Fin 3 → ℤ) (i j : Fin 3) (hne : i ≠ j)
    (hi : otherDifference i d = 0) (hj : otherDifference j d = 0) :
    d 0 = d 1 ∧ d 1 = d 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [otherDifference] <;> omega

/-- If two distinct fiber differences are protected on every four-site block,
the first fiber has even cardinality, including when the protecting rows vary by block. -/
theorem variable_protection_even {ι : Type*} [Fintype ι] (lo hi : ι → Fin 3 → ℕ)
    (small₁ : ∀ x, lo x 0 + lo x 1 + lo x 2 ≤ 2)
    (small₂ : ∀ x, hi x 0 + hi x 1 + hi x 2 ≤ 2)
    (protect : ∀ x, ∃ i j : Fin 3, i ≠ j ∧
      (∀ a b : Fin 3, a ≠ i → b ≠ i →
        (lo x a : ℤ) - hi x a = (lo x b : ℤ) - hi x b) ∧
      (∀ a b : Fin 3, a ≠ j → b ≠ j →
        (lo x a : ℤ) - hi x a = (lo x b : ℤ) - hi x b)) :
    Even (∑ x, (lo x 0 + hi x 0)) := by
  apply balanced_total_even
  intro x
  let d (i : Fin 3) := (lo x i : ℤ) - hi x i
  have holds (i : Fin 3) (h : ∀ a b, a ≠ i → b ≠ i → d a = d b) :
      otherDifference i d = 0 := by
    fin_cases i
    · exact sub_eq_zero.mpr (h 1 2 (by decide) (by decide))
    · exact sub_eq_zero.mpr (h 0 2 (by decide) (by decide))
    · exact sub_eq_zero.mpr (h 0 1 (by decide) (by decide))
  obtain ⟨i, j, hn, ha, hb⟩ := protect x
  obtain ⟨he, hf⟩ := two_other_differences d i j hn (holds i ha) (holds j hb)
  exact (three_fibers_in_two_site_halves _ _ _ _ _ _ (small₁ x) (small₂ x) he hf).1

#print axioms variable_protection_even
#print axioms three_fibers_in_two_site_halves
#print axioms balanced_total_even
#print axioms two_antireflections
#print axioms reaches_antipode
#print axioms two_centres
#print axioms three_centres

end ProximityGap.DyadicAntiperiodicReflection
