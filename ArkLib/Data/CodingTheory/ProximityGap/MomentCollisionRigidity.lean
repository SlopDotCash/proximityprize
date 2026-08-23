/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.MomentCollisionTower

/-!
# Issue #232 (ABF26) — DEPTH-`t` moment-collision rigidity: the anti-concentration band of the
# moment-collision scalar.

The fleet's `CollisionRigidityThreeSwap.lean` proved (for `t = 2`) that the first two power sums
determine a set of size `≤ 2`, so every off-diagonal `(∑x, ∑x²)`-collision moves `≥ 3` elements per
side. This file **generalizes that to all depths `t`** via Newton's identities, and connects it to
the depth-`t` moment tower of `MomentCollisionTower.lean`.

## Main results

* `powerSum_rigidity` — over a field of characteristic `0` or `> t`, two **disjoint** finsets of
  equal size `j ≤ t` sharing all power sums `∑ x^i` for `1 ≤ i ≤ t` are **equal**. (Power sums
  `p₁ … p_j` pin the elementary symmetric functions `e₀ … e_j` via Newton's identities — Mathlib's
  `MvPolynomial.mul_esymm_eq_sum` transported to `Multiset.esymm`/power sums through `aeval` — and
  equal `e_i` make the monic root polynomials `∏(X − a)` equal, whose roots recover the finsets.)
* `collision_symmDiff_ge_succ` — for distinct equal-size `S, S'` sharing all power sums up to `t`,
  `|S \ S'| ≥ t + 1` (symmetric difference `≥ 2(t+1)`).
* `statCollision_momentVec_eq_choose_of_le` — **the moment-tower anti-concentration band.** For the
  depth-`t` moment statistic `momentVec t : S ↦ (∑x, …, ∑xᵗ)`, every collision with agreement size
  `a ≤ t` is diagonal, so `statCollision G a (momentVec t) = C(|G|, a)` exactly. The depth-`t`
  moment-collision scalar (the prize object from `MomentCollisionTower`) sits at its trivial floor —
  maximal anti-concentration — for all `a ≤ t`; the prize-deciding excess lives entirely at
  `a ≥ t + 1`, a degree-`(t+1)` curve point count.

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). The char condition `i ≠ 0`
for `1 ≤ i ≤ t` holds for the prize's smooth `2^k`-subgroup (`char F` an odd prime `> t`, since `t`
is the constant interleaving depth and `|F| < 2^256`). This characterizes *where* the moment-collision
excess lives (`a ≥ t + 1`); it does **not** bound that excess — the open Weil magnitude.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial Finset BigOperators
open ArkLib.ProximityGap.MomentCollisionTower

namespace ArkLib.ProximityGap.MomentCollisionRigidity

/-- Power sum of a multiset: `∑ x∈s, x^n`. -/
noncomputable def psumMs {R : Type*} [CommRing R] (s : Multiset R) (n : ℕ) : R :=
  (s.map (· ^ n)).sum

lemma aeval_psum {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] (f : σ → R) (k : ℕ) :
    MvPolynomial.aeval f (MvPolynomial.psum σ R k) = psumMs (univ.val.map f) k := by
  unfold psumMs MvPolynomial.psum
  rw [map_sum, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  simp [Function.comp]

lemma multiset_newton {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → R) (k : ℕ) :
    (k : R) * (univ.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * psumMs (univ.val.map f) a.2 := by
  have h := MvPolynomial.mul_esymm_eq_sum σ R k
  have h2 := congrArg (MvPolynomial.aeval f) h
  rw [map_mul, map_natCast, MvPolynomial.aeval_esymm_eq_multiset_esymm] at h2
  rw [h2, map_mul, map_pow, map_neg, map_one, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, map_mul, map_pow, map_neg, map_one,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, aeval_psum]

lemma finset_newton {F : Type*} [Field F] (A : Finset F) (k : ℕ) :
    (k : F) * A.val.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * A.val.esymm a.1 * psumMs A.val a.2 := by
  classical
  have key := multiset_newton (Subtype.val : A → F) k
  have huniv : (Finset.univ.val.map (Subtype.val : A → F)) = A.val := by
    have h : (Finset.univ : Finset A) = A.attach := rfl
    rw [h]; exact Multiset.attach_map_val _
  rwa [huniv] at key

lemma psumMs_val {F : Type*} [Field F] (A : Finset F) (i : ℕ) :
    psumMs A.val i = ∑ x ∈ A, x ^ i := by
  unfold psumMs
  rw [Finset.sum_eq_multiset_sum]

/-- **Power sums determine elementary symmetric functions.** -/
lemma esymm_eq_of_psum_eq {F : Type*} [Field F] {j : ℕ} (A B : Finset F)
    (hchar : ∀ i, 0 < i → i ≤ j → (i : F) ≠ 0)
    (hpsum : ∀ i, 1 ≤ i → i ≤ j → psumMs A.val i = psumMs B.val i)
    (k : ℕ) (hk : k ≤ j) :
    A.val.esymm k = B.val.esymm k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp [Multiset.esymm]
    · have hkne : (k : F) ≠ 0 := hchar k hkpos hk
      have hA := finset_newton A k
      have hB := finset_newton B k
      have hsum : (∑ a ∈ Finset.antidiagonal k with a.1 < k,
            (-1) ^ a.1 * A.val.esymm a.1 * psumMs A.val a.2) =
          (∑ a ∈ Finset.antidiagonal k with a.1 < k,
            (-1) ^ a.1 * B.val.esymm a.1 * psumMs B.val a.2) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
        obtain ⟨hsum_eq, hlt⟩ := ha
        have ha2pos : 1 ≤ a.2 := by omega
        have ha2le : a.2 ≤ j := by omega
        rw [ih a.1 hlt (by omega), hpsum a.2 ha2pos ha2le]
      rw [hsum] at hA
      have hcancel : (k : F) * A.val.esymm k = (k : F) * B.val.esymm k := by rw [hA, hB]
      exact mul_left_cancel₀ hkne hcancel

/-- The monic root polynomial `∏_{a∈A} (X - C a)`. -/
noncomputable def prodPoly {F : Type*} [Field F] (A : Finset F) : F[X] :=
  (A.val.map (X - C ·)).prod

lemma prodPoly_natDegree {F : Type*} [Field F] (A : Finset F) :
    (prodPoly A).natDegree = A.card := by
  unfold prodPoly; rw [natDegree_multiset_prod_X_sub_C_eq_card, Finset.card_val]

lemma prodPoly_coeff {F : Type*} [Field F] {j : ℕ} (A : Finset F) (hcard : A.card = j)
    {m : ℕ} (hm : m ≤ j) :
    (prodPoly A).coeff m = (-1) ^ (j - m) * A.val.esymm (j - m) := by
  unfold prodPoly
  have hcA : Multiset.card A.val = j := by rw [Finset.card_val]; exact hcard
  have h := Multiset.prod_X_sub_C_coeff A.val (k := m) (by rw [hcA]; exact hm)
  rwa [hcA] at h

lemma prodPoly_roots {F : Type*} [Field F] (A : Finset F) : (prodPoly A).roots = A.val := by
  unfold prodPoly; exact roots_multiset_prod_X_sub_C A.val

lemma prodPoly_eq_of_esymm_eq {F : Type*} [Field F] {j : ℕ} (A B : Finset F)
    (hcard : A.card = j) (hcardB : B.card = j)
    (hesymm : ∀ i, i ≤ j → A.val.esymm i = B.val.esymm i) :
    prodPoly A = prodPoly B := by
  apply Polynomial.ext
  intro m
  by_cases hm : m ≤ j
  · rw [prodPoly_coeff A hcard hm, prodPoly_coeff B hcardB hm, hesymm (j - m) (by omega)]
  · push_neg at hm
    have hdA : (prodPoly A).natDegree = j := by rw [prodPoly_natDegree, hcard]
    have hdB : (prodPoly B).natDegree = j := by rw [prodPoly_natDegree, hcardB]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdA]; exact hm),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdB]; exact hm)]

/-- **The root polynomial recovers the finset** (injectivity of `A ↦ ∏ (X - C a)`). -/
lemma eq_of_prodPoly_eq {F : Type*} [Field F] (A B : Finset F)
    (h : prodPoly A = prodPoly B) : A = B := by
  have hr : A.val = B.val := by rw [← prodPoly_roots A, ← prodPoly_roots B, h]
  exact Finset.val_inj.mp hr

/-- **Depth-`t` moment-collision rigidity.** Two disjoint finsets of equal size `j ≤ t` over a field
of characteristic `0` or `> t`, sharing all power sums `∑ x^i` for `1 ≤ i ≤ t`, are equal. -/
theorem powerSum_rigidity {F : Type*} [Field F] {t j : ℕ} (A B : Finset F)
    (ht : 0 < t)
    (hchar : ∀ i, 0 < i → i ≤ t → (i : F) ≠ 0)
    (hcardA : A.card = j) (hcardB : B.card = j) (hjt : j ≤ t)
    (hpow : ∀ i, 1 ≤ i → i ≤ t → ∑ x ∈ A, x ^ i = ∑ x ∈ B, x ^ i) :
    A = B := by
  apply eq_of_prodPoly_eq
  apply prodPoly_eq_of_esymm_eq A B hcardA hcardB
  intro i hi
  refine esymm_eq_of_psum_eq A B (fun n hn hnj => hchar n hn (le_trans hnj hjt))
    (fun n hn hnj => ?_) i hi
  rw [psumMs_val, psumMs_val]
  exact hpow n hn (le_trans hnj hjt)

/-- **Large set-difference of a moment collision.** Distinct equal-size finsets sharing all power
sums up to `t` differ in at least `t + 1` elements per side. -/
theorem collision_symmDiff_ge_succ {F : Type*} [Field F] [DecidableEq F] {t : ℕ}
    (S S' : Finset F) (ht : 0 < t)
    (hchar : ∀ i, 0 < i → i ≤ t → (i : F) ≠ 0)
    (hcard : S.card = S'.card) (hne : S ≠ S')
    (hpow : ∀ i, 1 ≤ i → i ≤ t → ∑ x ∈ S, x ^ i = ∑ x ∈ S', x ^ i) :
    t + 1 ≤ (S \ S').card := by
  classical
  by_contra hlt
  push_neg at hlt
  set A := S \ S' with hA
  set B := S' \ S with hB
  have hcardAB : A.card = B.card := card_sdiff_eq_card_sdiff_iff.mpr hcard
  have hdisj : Disjoint A B := disjoint_sdiff_sdiff
  have hpowAB : ∀ i, 1 ≤ i → i ≤ t → ∑ x ∈ A, x ^ i = ∑ x ∈ B, x ^ i := by
    intro i _ hit
    have h := hpow i (by assumption) hit
    have e1 : A = S \ (S ∩ S') := by
      rw [hA]; ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    have e2 : B = S' \ (S' ∩ S) := by
      rw [hB]; ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [e1, e2, Finset.sum_sdiff_eq_sub Finset.inter_subset_left,
        Finset.sum_sdiff_eq_sub Finset.inter_subset_left, Finset.inter_comm S' S, h]
  have hjt : A.card ≤ t := by omega
  have hAB : A = B :=
    powerSum_rigidity A B ht hchar rfl hcardAB.symm hjt hpowAB
  have hAempty : A = ∅ := by
    have hself : Disjoint A A := by rw [hAB] at hdisj ⊢; exact hdisj
    exact (Finset.disjoint_self_iff_empty A).mp hself
  have hBempty : B = ∅ := by rw [← hAB]; exact hAempty
  have hSsub : S ⊆ S' := by
    intro x hx; by_contra hxn
    exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxn⟩) (by rw [← hA, hAempty]; exact Finset.notMem_empty x)
  have hS'sub : S' ⊆ S := by
    intro x hx; by_contra hxn
    exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxn⟩) (by rw [← hB, hBempty]; exact Finset.notMem_empty x)
  exact hne (Finset.Subset.antisymm hSsub hS'sub)

/-- **The moment-tower anti-concentration band (the Tower corollary).** For the depth-`t` moment
statistic `momentVec t : S ↦ (∑x, …, ∑xᵗ)`, every collision with `a ≤ t` is diagonal — so
`statCollision G a (momentVec t) = C(|G|, a)` exactly. The depth-`t` moment-collision scalar is at
its trivial floor (maximal anti-concentration) for all agreement sizes `a ≤ t`; the prize-deciding
excess lives entirely at `a ≥ t + 1`, a degree-`(t+1)` curve point count. Generalizes the fleet's
`t = 2` `collisionSet_le_two_eq_diagonal` to all depths. -/
theorem statCollision_momentVec_eq_choose_of_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {t : ℕ} (ht : 0 < t) (hchar : ∀ i, 0 < i → i ≤ t → (i : F) ≠ 0)
    (G : Finset F) {a : ℕ} (ha : a ≤ t) :
    statCollision G a (momentVec t) = (G.card).choose a := by
  refine le_antisymm ?_ (statCollision_ge_choose G a (momentVec t))
  have key : ∀ S S' : Finset F, S ∈ G.powersetCard a → S' ∈ G.powersetCard a →
      momentVec t S = momentVec t S' → S = S' := by
    intro S S' hS hS' hcol
    by_contra hne
    have hcardSS : S.card = S'.card := by
      rw [(Finset.mem_powersetCard.mp hS).2, (Finset.mem_powersetCard.mp hS').2]
    have hpow : ∀ i, 1 ≤ i → i ≤ t → ∑ x ∈ S, x ^ i = ∑ x ∈ S', x ^ i := by
      intro i hi1 hit
      have hj : (i - 1) < t := by omega
      have hcf := congrFun hcol (⟨i - 1, hj⟩ : Fin t)
      simp only [momentVec, Fin.val_mk] at hcf
      rwa [Nat.sub_add_cancel hi1] at hcf
    have h3 := collision_symmDiff_ge_succ S S' ht hchar hcardSS hne hpow
    have hle : (S \ S').card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
    rw [(Finset.mem_powersetCard.mp hS).2] at hle
    omega
  unfold statCollision
  rw [← Finset.card_powersetCard a G]
  apply Finset.card_le_card_of_injOn (fun p => p.1)
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    rw [Finset.mem_coe]; exact hp.1.1
  · intro p hp p' hp' h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨⟨hpS, hpS'⟩, hpcol⟩ := hp
    obtain ⟨⟨hp'S, hp'S'⟩, hp'col⟩ := hp'
    have e1 : p.1 = p.2 := key _ _ hpS hpS' hpcol
    have e2 : p'.1 = p'.2 := key _ _ hp'S hp'S' hp'col
    have h' : p.1 = p'.1 := h
    refine Prod.ext_iff.mpr ⟨h', ?_⟩
    rw [← e1, h']; exact e2

end ArkLib.ProximityGap.MomentCollisionRigidity

#print axioms ArkLib.ProximityGap.MomentCollisionRigidity.powerSum_rigidity
#print axioms ArkLib.ProximityGap.MomentCollisionRigidity.collision_symmDiff_ge_succ
#print axioms ArkLib.ProximityGap.MomentCollisionRigidity.statCollision_momentVec_eq_choose_of_le
