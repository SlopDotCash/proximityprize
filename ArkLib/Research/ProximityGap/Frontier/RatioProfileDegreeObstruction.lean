/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card

/-!
# A one-spike obstruction to arbitrary low-degree ratio profiles (#464)

The ratio-census route can only use bounded-degree polynomial or rational profiles after a real
structural bridge.  An arbitrary profile need not have such a representation: a numerator that
realizes a one-point spike over an injective evaluation domain is forced to vanish at every other
domain point and stay nonzero at the spike, hence it has degree at least `n - 1`.

This is a guardrail for the open δ* bridge, not a floor proof: it rules out the shortcut "compress
an arbitrary bad-scalar ratio profile into a uniformly bounded-degree polynomial line" without
additional structure.
-/

set_option autoImplicit false

namespace ProximityGap.RatioProfileDegreeObstruction

open Polynomial

variable {ι F : Type*} [Fintype ι] [Field F]

/-- **One-spike numerator degree obstruction.** If a numerator `P` vanishes on every point of an
injective domain except `i0`, but at `i0` equals a nonzero scalar multiple of a nonvanishing
denominator `Q`, then `P` has degree at least `|ι| - 1`. -/
theorem spike_numerator_degree_ge (dom : ι → F) (hdom : Function.Injective dom) (i0 : ι)
    (P Q : F[X]) {a : F} (ha : a ≠ 0) (hQ0 : Q.eval (dom i0) ≠ 0)
    (hzero : ∀ i, i ≠ i0 → P.eval (dom i) = 0)
    (hspike : P.eval (dom i0) = a * Q.eval (dom i0)) :
    Fintype.card ι - 1 ≤ P.natDegree := by
  classical
  have hPeval_ne : P.eval (dom i0) ≠ 0 := by
    rw [hspike]
    exact mul_ne_zero ha hQ0
  have hPne : P ≠ 0 := by
    intro hP
    exact hPeval_ne (by simp [hP])
  have herase_card : (Finset.univ.erase i0).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ]
  have hroot_card : (Finset.univ.erase i0).card ≤ P.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun i => dom i)
    · intro i hi
      have hi_ne : i ≠ i0 := (Finset.mem_erase.mp hi).1
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hPne,
        Polynomial.IsRoot.def]
      exact hzero i hi_ne
    · intro i _ j _ hij
      exact hdom hij
  have hroot_bound : (Finset.univ.erase i0).card ≤ P.natDegree := by
    calc
      (Finset.univ.erase i0).card ≤ P.roots.toFinset.card := hroot_card
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
  simpa [herase_card] using hroot_bound

/-- **Sparse-support numerator degree obstruction.** If `P` vanishes off a finite support `S`
but is nonzero at one point of `S`, then `P` has at least one root at every domain point outside
`S`, forcing degree at least `|ι| - #S`. -/
theorem sparse_numerator_degree_ge (dom : ι → F)
    (hdom : Function.Injective dom) (support : Finset ι) (i0 : ι)
    (P Q : F[X]) {a : F} (ha : a ≠ 0) (hQ0 : Q.eval (dom i0) ≠ 0)
    (hzero : ∀ i, i ∉ support → P.eval (dom i) = 0)
    (hspike : P.eval (dom i0) = a * Q.eval (dom i0)) :
    Fintype.card ι - support.card ≤ P.natDegree := by
  classical
  have hPeval_ne : P.eval (dom i0) ≠ 0 := by
    rw [hspike]
    exact mul_ne_zero ha hQ0
  have hPne : P ≠ 0 := by
    intro hP
    exact hPeval_ne (by simp [hP])
  let Z : Finset ι := Finset.univ \ support
  have hZ_card : Z.card = Fintype.card ι - support.card := by
    change (Finset.univ \ support).card = Fintype.card ι - support.card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ support), Finset.card_univ]
  have hroot_card : Z.card ≤ P.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun i => dom i)
    · intro i hi
      have hi_not_support : i ∉ support := (Finset.mem_sdiff.mp hi).2
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hPne,
        Polynomial.IsRoot.def]
      exact hzero i hi_not_support
    · intro i _ j _ hij
      exact hdom hij
  have hroot_bound : Z.card ≤ P.natDegree := by
    calc
      Z.card ≤ P.roots.toFinset.card := hroot_card
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
  simpa [hZ_card] using hroot_bound

/-- Representation-facing form of `spike_numerator_degree_ge`: if `P/Q` realizes the ratio profile
that is `a` at `i0` and `0` everywhere else, with `Q` nonzero at the spike, then the numerator has
degree at least `|ι| - 1`. -/
theorem spike_profile_numerator_degree_ge [DecidableEq ι] (dom : ι → F)
    (hdom : Function.Injective dom) (i0 : ι) (P Q : F[X]) {a : F} (ha : a ≠ 0)
    (hQ0 : Q.eval (dom i0) ≠ 0)
    (hprofile : ∀ i, P.eval (dom i) = (if i = i0 then a else 0) * Q.eval (dom i)) :
    Fintype.card ι - 1 ≤ P.natDegree := by
  classical
  refine spike_numerator_degree_ge dom hdom i0 P Q ha hQ0 ?_ ?_
  · intro i hi
    rw [hprofile i, if_neg hi, zero_mul]
  · simpa using hprofile i0

/-- Representation-facing sparse-support form: if `P/Q` realizes a profile supported on `support`
and the profile is nonzero at one supported point where `Q` is nonzero, then the numerator degree
is at least the complement size `|ι| - #support`. -/
theorem sparse_profile_numerator_degree_ge [DecidableEq ι] (dom : ι → F)
    (hdom : Function.Injective dom) (support : Finset ι) (i0 : ι) (hi0 : i0 ∈ support)
    (P Q : F[X]) (r : ι → F) {a : F} (ha : a ≠ 0)
    (hQ0 : Q.eval (dom i0) ≠ 0) (hr : r i0 = a)
    (hprofile : ∀ i, P.eval (dom i) =
      (if i ∈ support then r i else 0) * Q.eval (dom i)) :
    Fintype.card ι - support.card ≤ P.natDegree := by
  classical
  refine sparse_numerator_degree_ge dom hdom support i0 P Q ha hQ0 ?_ ?_
  · intro i hi
    rw [hprofile i, if_neg hi, zero_mul]
  · rw [hprofile i0, if_pos hi0, hr]

/-- **Support-degree necessary condition for sparse represented profiles.**  If a represented
ratio profile is supported on `support` and is nonzero at one supported point where `Q` is
nonzero, then the support size plus the numerator degree must cover the whole domain:
`|ι| ≤ #support + deg(P)`.  This is the subtraction-free form of
`sparse_profile_numerator_degree_ge`. -/
theorem sparse_profile_support_card_add_natDegree_ge [DecidableEq ι] (dom : ι → F)
    (hdom : Function.Injective dom) (support : Finset ι) (i0 : ι) (hi0 : i0 ∈ support)
    (P Q : F[X]) (r : ι → F) {a : F} (ha : a ≠ 0)
    (hQ0 : Q.eval (dom i0) ≠ 0) (hr : r i0 = a)
    (hprofile : ∀ i, P.eval (dom i) =
      (if i ∈ support then r i else 0) * Q.eval (dom i)) :
    Fintype.card ι ≤ support.card + P.natDegree := by
  have hdeg :=
    sparse_profile_numerator_degree_ge dom hdom support i0 hi0 P Q r ha hQ0 hr hprofile
  simpa [Nat.add_comm] using (Nat.sub_le_iff_le_add.mp hdeg)

/-- Contrapositive scanner form: a numerator of degree `< |ι| - 1` cannot realize a nonzero
one-spike ratio profile over an injective domain. -/
theorem not_spike_profile_of_natDegree_lt [DecidableEq ι] (dom : ι → F)
    (hdom : Function.Injective dom) (i0 : ι) (P Q : F[X]) {a : F} (ha : a ≠ 0)
    (hQ0 : Q.eval (dom i0) ≠ 0) (hdeg : P.natDegree < Fintype.card ι - 1) :
    ¬ ∀ i, P.eval (dom i) = (if i = i0 then a else 0) * Q.eval (dom i) := by
  intro hprofile
  exact (not_lt_of_ge
    (spike_profile_numerator_degree_ge dom hdom i0 P Q ha hQ0 hprofile)) hdeg

/-- Contrapositive sparse-support scanner: a numerator of degree `< |ι| - #support` cannot
realize a nonzero profile supported on `support`. -/
theorem not_sparse_profile_of_natDegree_lt [DecidableEq ι] (dom : ι → F)
    (hdom : Function.Injective dom) (support : Finset ι) (i0 : ι) (hi0 : i0 ∈ support)
    (P Q : F[X]) (r : ι → F) {a : F} (ha : a ≠ 0)
    (hQ0 : Q.eval (dom i0) ≠ 0) (hr : r i0 = a)
    (hdeg : P.natDegree < Fintype.card ι - support.card) :
    ¬ ∀ i, P.eval (dom i) =
      (if i ∈ support then r i else 0) * Q.eval (dom i) := by
  intro hprofile
  exact (not_lt_of_ge
    (sparse_profile_numerator_degree_ge dom hdom support i0 hi0 P Q r ha hQ0 hr
      hprofile)) hdeg

/-- Contrapositive support-degree scanner: a represented nonzero profile supported on `support`
is impossible when `#support + deg(P) < |ι|`. -/
theorem not_sparse_profile_of_support_card_add_natDegree_lt [DecidableEq ι] (dom : ι → F)
    (hdom : Function.Injective dom) (support : Finset ι) (i0 : ι) (hi0 : i0 ∈ support)
    (P Q : F[X]) (r : ι → F) {a : F} (ha : a ≠ 0)
    (hQ0 : Q.eval (dom i0) ≠ 0) (hr : r i0 = a)
    (hsmall : support.card + P.natDegree < Fintype.card ι) :
    ¬ ∀ i, P.eval (dom i) =
      (if i ∈ support then r i else 0) * Q.eval (dom i) := by
  intro hprofile
  exact (not_lt_of_ge
    (sparse_profile_support_card_add_natDegree_ge dom hdom support i0 hi0 P Q r ha hQ0 hr
      hprofile)) hsmall

end ProximityGap.RatioProfileDegreeObstruction

/-! ## Axiom audit — kernel-clean. -/
namespace ProximityGap.RatioProfileDegreeObstruction

#print axioms spike_numerator_degree_ge
#print axioms sparse_numerator_degree_ge
#print axioms spike_profile_numerator_degree_ge
#print axioms sparse_profile_numerator_degree_ge
#print axioms sparse_profile_support_card_add_natDegree_ge
#print axioms not_spike_profile_of_natDegree_lt
#print axioms not_sparse_profile_of_natDegree_lt
#print axioms not_sparse_profile_of_support_card_add_natDegree_lt

end ProximityGap.RatioProfileDegreeObstruction
