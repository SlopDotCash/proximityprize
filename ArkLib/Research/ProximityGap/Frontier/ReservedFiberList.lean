/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Algebra.Polynomial.BigOperators

/-! # A list of RS codewords on equal power-map fibers

Multiply a quotient-domain capacity witness by a polynomial vanishing on all
but one point of a reserved fiber. Every chosen quotient fiber then contributes
its full size, and the reserved roots contribute further agreements.
-/

namespace ProximityGap.ReservedFiberList

open Polynomial Finset
open scoped BigOperators

variable {F I J : Type*} [Field F] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

private noncomputable def locator (S : Finset I) (a : I → F) : F[X] :=
  ∏ i ∈ S, (X - C (a i))

omit [Fintype I] [DecidableEq I] in
private theorem locator_eval_zero {S : Finset I} {a : I → F} {x : F} :
    (locator S a).eval x = 0 ↔ ∃ i ∈ S, x = a i := by
  simp [locator, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

noncomputable def candidate (h : F[X]) (a : I → F)
    (b s : ℕ) (T : Finset I) : F[X] :=
  h * ((X ^ b - locator T a).comp (X ^ s))

omit [Fintype I] [DecidableEq I] in
private theorem candidate_degree (h : F[X]) (a : I → F) {b s : ℕ} {T : Finset I}
    (hb : 0 < b) (hT : T.card = b) (hh : h.natDegree < s) :
    (candidate h a b s T).natDegree < b * s := by
  have hm : (locator T a).Monic := monic_prod_X_sub_C a T
  have hd : (locator T a).natDegree = b := by simp [locator, hT]
  have hlow : ((X : F[X]) ^ b - locator T a).natDegree < b := by
    by_cases hz : ((X : F[X]) ^ b - locator T a) = 0
    · simpa [hz] using hb
    apply (natDegree_lt_iff_degree_lt hz).mpr
    have hdeg : ((X : F[X]) ^ b).degree = (locator T a).degree := by
      rw [degree_X_pow, degree_eq_natDegree hm.ne_zero, hd]
    simpa using degree_sub_lt_left hdeg (pow_ne_zero _ X_ne_zero)
      (show ((X : F[X]) ^ b).leadingCoeff = (locator T a).leadingCoeff by
        rw [(monic_X_pow b).leadingCoeff, hm.leadingCoeff])
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  dsimp [candidate]
  calc
    _ ≤ h.natDegree + ((X ^ (c+1) - locator T a).comp (X ^ s)).natDegree :=
      natDegree_mul_le
    _ ≤ h.natDegree + c * s := by
      rw [natDegree_comp, natDegree_X_pow]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hlow)) _
    _ < (c + 1) * s := by rw [Nat.add_mul, one_mul]; omega

variable (α : I × J ↪ F) (a : I ↪ F) (i₀ : I) (j₀ : J)

noncomputable def reserve : F[X] :=
  ∏ j ∈ (univ.erase j₀), (X - C (α (i₀,j)))

omit [Fintype I] [DecidableEq I] in
private theorem reserve_eval_zero (ij : I × J) :
    (reserve α i₀ j₀).eval (α ij) = 0 ↔ ij.1 = i₀ ∧ ij.2 ≠ j₀ := by
  rcases ij with ⟨i,j⟩
  simp [reserve, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, α.injective.eq_iff, and_comm]

omit [Fintype I] [DecidableEq I] in
/-- The actual RS words from any two different selected fiber sets have distinct
agreement supports. This equivalence also describes their common center. -/
theorem candidate_agreement (b s : ℕ) (T : Finset I)
    (hpow : ∀ ij, α ij ^ s = a ij.1) (ij : I × J) :
    (candidate (reserve α i₀ j₀) a b s T).eval (α ij) =
      (reserve α i₀ j₀).eval (α ij) * (α ij ^ s) ^ b ↔
      (ij.1 = i₀ ∧ ij.2 ≠ j₀) ∨ ij.1 ∈ T := by
  simp only [candidate, eval_mul, eval_comp, eval_pow, eval_X, eval_sub]
  rw [← sub_eq_zero, ← mul_sub, sub_sub_cancel_left, mul_neg, neg_eq_zero, mul_eq_zero,
    reserve_eval_zero, locator_eval_zero, hpow]
  simp [a.injective.eq_iff]

/-- A binomial lower bound at one explicit Hamming radius. The hypotheses present
the evaluation domain by its equal power-map fibers, with one distinguished point. -/
theorem list_lower_bound (i₀ : I) (j₀ : J) (b : ℕ) (hb : 0 < b)
    (hpow : ∀ ij, α ij ^ Fintype.card J = a ij.1) :
    (((Fintype.card I - 1).choose b : ℕ) : ℕ∞) ≤
      Code.Lambda (ReedSolomon.code α (b * Fintype.card J) : Set (I × J → F))
        (((Fintype.card I * Fintype.card J - (b * Fintype.card J + (Fintype.card J - 1)) : ℕ) : ℝ)
          / Fintype.card (I × J)) := by
  classical
  let s := Fintype.card J
  let h := reserve α i₀ j₀
  let center : I × J → F := fun ij => h.eval (α ij) * (α ij ^ s) ^ b
  let word := fun T : Finset I => fun ij => (candidate h a b s T).eval (α ij)
  let sets := (univ.erase i₀).powersetCard b
  have hs : 0 < s := Fintype.card_pos_iff.mpr ⟨j₀⟩
  have hgood (T) (hT : T ∈ sets) : T.card = b ∧ i₀ ∉ T := by
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
    exact ⟨hcard, fun hi => (Finset.notMem_erase _ _) (hsub hi)⟩
  have hinj : Set.InjOn word (sets : Set (Finset I)) := by
    intro S hS T hT heq
    ext i
    have h := congrFun heq (i,j₀)
    have h₁ := candidate_agreement α a i₀ j₀ b s S hpow (i,j₀)
    have h₂ := candidate_agreement α a i₀ j₀ b s T hpow (i,j₀)
    change (candidate _ _ _ _ S).eval _ = (candidate _ _ _ _ T).eval _ at h
    rw [h] at h₁
    simpa using h₁.symm.trans h₂
  let R := Fintype.card I * s - (b * s + (s - 1))
  have hmem : (↑(sets.image word) : Set (I × J → F)) ⊆
      Code.closeCodewordsRel (ReedSolomon.code α (b*s) : Set (I × J → F)) center
        ((R : ℝ) / Fintype.card (I × J)) := by
    rw [← Code.closeCodewords_eq_closeCodewordsRel]
    intro w hw
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hw
    obtain ⟨hc,hex⟩ := hgood T hT
    refine ⟨ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _
      (candidate_degree h a hb hc ?_) (fun _ => rfl), ?_⟩
    · simpa [h, reserve, s] using Nat.sub_lt hs (by decide : 0 < 1)
    · rw [Code.mem_hammingBall_iff]
      have he : (univ.filter fun ij => center ij = word T ij) =
          (T ×ˢ (univ : Finset J)) ∪ ({i₀} ×ˢ univ.erase j₀) := by
        ext ij
        simp only [mem_filter, mem_univ, true_and, mem_union, mem_product, mem_erase,
          mem_singleton, and_true]
        rw [eq_comm, show (word T ij = center ij) ↔ _ from
          candidate_agreement α a i₀ j₀ b s T hpow ij]
        tauto
      have hd : Disjoint (T ×ˢ (univ : Finset J)) ({i₀} ×ˢ univ.erase j₀) := by
        rw [Finset.disjoint_left]
        intro ij hx hy
        exact hex (by simpa [show ij.1 = i₀ from by simpa using (mem_product.mp hy).1]
          using (mem_product.mp hx).1)
      have hcard := congrArg Finset.card he
      rw [card_union_of_disjoint hd] at hcard
      simp [hc] at hcard
      have hh := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (I × J))) (p := fun ij => center ij = word T ij)
      simp only [card_univ, Fintype.card_prod] at hh
      change (univ.filter (fun ij => center ij ≠ word T ij)).card ≤ R
      dsimp [R,s]
      omega
  have bound := Code.encard_le_Lambda_of_subset_closeCodewordsRel hmem
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injOn hinj] at bound
  simpa [sets, R, s] using bound

/-- Consecutive powers of an element of order M*s, indexed by fiber and position. -/
def cyclicDomain {M s : ℕ} (g : Fˣ) (hg : orderOf g = s * M) :
    Fin M × Fin s ↪ F where
  toFun ij := ↑(g ^ (finProdFinEquiv (ij.2, ij.1)).val)
  inj' := by
    intro ij ij' h
    apply Prod.swap_injective
    apply finProdFinEquiv.injective
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := g) _ _ (Units.ext h)
    · change _ < orderOf g
      rw [hg]
      exact (finProdFinEquiv (ij.2, ij.1)).isLt
    · change _ < orderOf g
      rw [hg]
      exact (finProdFinEquiv (ij'.2, ij'.1)).isLt

/-- The distinct labels of the power-map fibers in a cyclic domain. -/
def cyclicLabels {M s : ℕ} (hs : 0 < s) (g : Fˣ) (hg : orderOf g = s * M) :
    Fin M ↪ F where
  toFun i := ↑(g ^ (s * i.val))
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left hs (pow_injOn_Iio_orderOf
      (hg ▸ Nat.mul_lt_mul_of_pos_left i.isLt hs)
      (hg ▸ Nat.mul_lt_mul_of_pos_left j.isLt hs) (Units.ext hij))

/-- Raising a domain coordinate to the fiber size gives its quotient label. -/
theorem cyclicDomain_pow {M s : ℕ} (hs : 0 < s) (g : Fˣ) (hg : orderOf g = s * M)
    (ij : Fin M × Fin s) :
    cyclicDomain g hg ij ^ Fintype.card (Fin s) = cyclicLabels hs g hg ij.1 := by
  rw [Fintype.card_fin]
  change ((g : F) ^ (ij.1.val + M * ij.2.val)) ^ s = (g : F) ^ (s * ij.1.val)
  rw [← pow_mul, Nat.add_mul, Nat.mul_comm ij.1.val s, pow_add]
  have hz : (g : F) ^ (s * M) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val (show g ^ (s * M) = 1 from hg ▸ pow_orderOf_eq_one g)
  rw [show M * ij.2.val * s = (s * M) * ij.2.val by ac_rfl,
    pow_mul (g : F) (s*M) ij.2.val, hz, one_pow, mul_one]

/-- The concrete cyclic subgroup case of the binomial bound. -/
theorem cyclic_list_lower_bound {M s b : ℕ} (hM : 0 < M) (hs : 0 < s)
    (hb : 0 < b) (g : Fˣ) (hg : orderOf g = s * M) :
    (((M - 1).choose b : ℕ) : ℕ∞) ≤
      Code.Lambda (ReedSolomon.code (cyclicDomain g hg) (b * s) : Set (Fin M × Fin s → F))
        (((M * s - (b * s + (s - 1)) : ℕ) : ℝ) / (M * s : ℕ)) := by
  simpa [Fintype.card_prod] using
    list_lower_bound (cyclicDomain g hg) (cyclicLabels hs g hg)
      (⟨0,hM⟩ : Fin M) (⟨0,hs⟩ : Fin s) b hb (cyclicDomain_pow hs g hg)

#print axioms cyclic_list_lower_bound

end ProximityGap.ReservedFiberList
