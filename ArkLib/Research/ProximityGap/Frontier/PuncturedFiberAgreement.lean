/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Extending agreements off polynomial fibers across punctures

Suppose each Reed–Solomon head agrees with a shared received word away from its own
fiber of a polynomial H on the retained coordinates. If at least k + deg H points
remain, each triple of weighted heads satisfies a polynomial identity. Applying it
on the original domain forces all heads to coincide when its size is at least
k + 2 deg H. For the four quarter-cosets at rate one half this permits any quarter
of the coordinates to be erased.
-/

set_option autoImplicit false

namespace ProximityGap.PuncturedFiberAgreement

open Polynomial

variable {F I : Type*} [Field F]

/-- Agreement outside the exceptional fiber makes the weighted evaluations affine
in the fiber label, even on the exceptional fiber itself. -/
private theorem weighted_eval (H P : F[X]) (a x w : F)
    (hw : H.eval x ≠ a → P.eval x = w) :
    ((H - C a) * P).eval x = (H.eval x - a) * w := by
  simp only [eval_mul, eval_sub, eval_C]
  by_cases hx : H.eval x = a
  · simp [hx]
  · rw [hw hx]

/-- A family of heads with one excluded fiber per head has just one polynomial
when the retained and full domains clear their respective interpolation bounds.
The labels may repeat. The two finite sets need only satisfy the stated properties. -/
theorem heads_eq_of_punctured_fiber_agreement
    (H : F[X]) (a : I → F) (P : I → F[X]) (w : F → F)
    (retained full : Finset F) (k : ℕ)
    (hdeg : ∀ i, (P i).natDegree < k)
    (hpoly : ∀ i, H ≠ C (a i))
    (hret : H.natDegree + k ≤ retained.card)
    (hfull : H.natDegree + H.natDegree + k ≤ full.card)
    (hcover : ∀ x ∈ full, ∃ i, a i = H.eval x)
    (hagree : ∀ i x, x ∈ retained → H.eval x ≠ a i → (P i).eval x = w x)
    (i j : I) : P i = P j := by
  classical
  let Q (t : I) := (H - C (a t)) * P t
  have hfactor (t : I) : (H - C (a t)).natDegree ≤ H.natDegree := by
    simp
  have hQ (t : I) : (Q t).natDegree < retained.card :=
    (natDegree_mul_le.trans (Nat.add_le_add_right (hfactor t) _)).trans_lt
      ((Nat.add_lt_add_left (hdeg t) _).trans_le hret)
  have hweighted (t : I) (x : F) (hx : x ∈ retained) :
      (Q t).eval x = (H.eval x - a t) * w x :=
    weighted_eval H (P t) (a t) x (w x) (hagree t x hx)
  have triple (l : I) :
      C (a j - a l) * Q i + C (a l - a i) * Q j + C (a i - a j) * Q l = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ retained
    · intro x hx
      simp only [eval_add, eval_mul, eval_C, hweighted _ x hx]
      ring
    · exact (natDegree_add_le ..).trans_lt (max_lt
        ((natDegree_add_le ..).trans_lt (max_lt
          ((natDegree_C_mul_le ..).trans_lt (hQ i))
          ((natDegree_C_mul_le ..).trans_lt (hQ j))))
        ((natDegree_C_mul_le ..).trans_lt (hQ l)))
  have hzero : (H - C (a i)) * (H - C (a j)) * (P i - P j) = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ full
    · intro x hx
      obtain ⟨l, hl⟩ := hcover x hx
      have ht := congrArg (eval x) (triple l)
      simp only [Q, eval_add, eval_mul, eval_sub, eval_C, eval_zero, hl, sub_self,
        zero_mul, mul_zero, add_zero] at ht
      simp only [eval_mul, eval_sub, eval_C]
      linear_combination -ht
    · exact (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add (hfactor i) (hfactor j)))
        (natDegree_sub_le ..))).trans_lt
          ((Nat.add_lt_add_left (max_lt (hdeg i) (hdeg j)) _).trans_le hfull)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr (hpoly i)) (sub_ne_zero.mpr (hpoly j))))

/-- On four equal fibers of the m-th power map, retaining any three quarters
suffices for equality at rate one half. The cardinality of the original domain
and the coverage by fiber values are explicit, so the result also applies to a
multiplicative coset of the standard order-four quotient domain. -/
theorem quarter_coset_heads_eq [DecidableEq F] (m : ℕ) (hm : 0 < m)
    (a : I → F) (P : I → F[X]) (w : F → F) (retained full : Finset F)
    (hn : full.card = 4 * m) (hret : 3 * m ≤ retained.card)
    (hdeg : ∀ i, (P i).natDegree < 2 * m)
    (hcover : ∀ x ∈ full, ∃ i, a i = x ^ m)
    (hagree : ∀ i x, x ∈ retained → x ^ m ≠ a i → (P i).eval x = w x)
    (i j : I) : P i = P j := by
  apply heads_eq_of_punctured_fiber_agreement (X ^ m) a P w retained full (2*m) hdeg
  · intro t h
    have he := congrArg natDegree h
    simp at he
    omega
  · simp only [natDegree_X_pow]
    omega
  · simp only [natDegree_X_pow]
    omega
  · simpa using hcover
  · simpa using hagree

/-- When fewer than k retained points lie outside one chosen fiber, a
nonzero codeword may be substituted for the zero head on that fiber's index.
Its locator vanishes on every point on which that head must match zero. -/
theorem nonconstant_heads_of_small_complement [DecidableEq I] [DecidableEq F]
    (H : F[X]) (a : I → F) (S : Finset F) {k : ℕ} (hk : 0 < k)
    (i j : I) (hij : i ≠ j)
    (hS : (S.filter fun x => H.eval x ≠ a i).card < k) :
    ∃ P : I → F[X], (∀ t, (P t).natDegree < k) ∧
      (∀ t x, x ∈ S → H.eval x ≠ a t → (P t).eval x = 0) ∧ P i ≠ P j := by
  classical
  let T := S.filter fun x => H.eval x ≠ a i
  let L : F[X] := ∏ x ∈ T, (X - C x)
  have hm : L.Monic := monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
  have hd : L.natDegree = T.card := by
    unfold L
    rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
    simp
  refine ⟨fun t => if t = i then L else 0, ?_, ?_, ?_⟩
  · intro t
    change (if t = i then L else 0).natDegree < k
    split_ifs
    · exact hd.trans_lt hS
    · simpa using hk
  · intro t x hx hne
    change (if t = i then L else 0).eval x = 0
    split_ifs with ht
    · subst t
      have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hne⟩
      simp only [L, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero hxT (sub_self x)
    · simp
  · simpa [hij.symm] using hm.ne_zero

#print axioms quarter_coset_heads_eq
#print axioms nonconstant_heads_of_small_complement

#print axioms heads_eq_of_punctured_fiber_agreement

end ProximityGap.PuncturedFiberAgreement
