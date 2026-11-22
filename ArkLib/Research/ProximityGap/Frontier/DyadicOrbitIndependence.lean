/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic

/-! # A single test for independence of a dyadic orbit in characteristic two

In the binary permutation module of a cyclic group of order a power of two,
every nonzero translation-stable relation space contains the all-ones vector.
Thus a linear map with translation-stable kernel is injective precisely when
the sum of all the basis images is nonzero. For odd dyadic cyclotomic factors
modulo sign, these basis images are the square classes of the factors.
-/

namespace ProximityGap.DyadicOrbitIndependence

private theorem constant_of_period_one {n : ℕ} [NeZero n] (v : ZMod n → ZMod 2)
    (hp : ∀ i, v (i+1) = v i) (hne : v ≠ 0) : v = fun _ ↦ 1 := by
  have hn (m : ℕ) : v (m : ZMod n) = v 0 := by
    induction m with
    | zero => simp
    | succ m ih => simpa only [Nat.cast_succ, hp] using ih
  have hc (i : ZMod n) : v i = v 0 := by simpa only [ZMod.natCast_zmod_val] using hn i.val
  have h0 : v 0 ≠ 0 := by
    intro hz
    exact hne (funext fun i ↦ (hc i).trans hz)
  have h1 : v 0 = 1 := by
    have H : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact H _ h0
  exact funext fun i ↦ (hc i).trans h1

private theorem one_of_period {n : ℕ} [NeZero n] (R : Set (ZMod n → ZMod 2))
    (hs : ∀ v ∈ R, ∀ a : ZMod n, (fun i ↦ v (i+a)) ∈ R)
    (ha : ∀ v ∈ R, ∀ w ∈ R, v+w ∈ R) (j : ℕ)
    (v : ZMod n → ZMod 2) (hv : v ∈ R) (hne : v ≠ 0)
    (hp : ∀ i, v (i+(2:ZMod n)^j) = v i) : (fun _ ↦ 1) ∈ R := by
  induction j generalizing v with
  | zero =>
    have h := constant_of_period_one v (by simpa only [pow_zero] using hp) hne
    rwa [← h]
  | succ j ih =>
    let q : ZMod n := 2^j
    by_cases h : ∀ i, v (i+q) = v i
    · exact ih v hv hne h
    let w (i : ZMod n) := v i + v (i+q)
    have hw : w ∈ R := ha v hv _ (hs v hv q)
    have h2 : ∀ a b : ZMod 2, a+b=0 → b=a := by decide
    have hw0 : w ≠ 0 := by
      intro hz
      exact h fun i ↦ h2 _ _ (congrFun hz i)
    apply ih w hw hw0
    intro i
    have hq : i+q+q = i+(2:ZMod n)^(j+1) := by dsimp [q]; ring
    change v (i+q) + v (i+q+q) = v i + v (i+q)
    rw [hq, hp, add_comm]

/-- Every nonzero translation-stable binary relation space on a dyadic cycle
contains the all-ones relation. -/
theorem one_mem_of_nonzero (k : ℕ) (R : Set (ZMod (2^k) → ZMod 2))
    (hs : ∀ v ∈ R, ∀ a : ZMod (2^k), (fun i ↦ v (i+a)) ∈ R)
    (ha : ∀ v ∈ R, ∀ w ∈ R, v+w ∈ R)
    (h : ∃ v ∈ R, v ≠ 0) : (fun _ ↦ 1) ∈ R := by
  let : NeZero (2^k) := ⟨by positivity⟩
  obtain ⟨v,hv,hne⟩ := h
  apply one_of_period R hs ha k v hv hne
  intro i
  have hz : (2 : ZMod (2^k)) ^ k = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2^k)
  rw [hz, add_zero]

/-- For a linear map from a binary dyadic cycle with translation-stable kernel,
testing the all-ones relation is equivalent to testing every relation. -/
theorem injective_iff_total_ne_zero (k : ℕ) {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (L : (ZMod (2^k) → ZMod 2) →ₗ[ZMod 2] V)
    (hshift : ∀ v, L v = 0 → ∀ a : ZMod (2^k), L (fun i ↦ v (i+a)) = 0) :
    Function.Injective L ↔ L (fun _ ↦ 1) ≠ 0 := by
  constructor
  · intro hi h
    have hz : (fun _ : ZMod (2^k) ↦ (1 : ZMod 2)) = 0 := hi (h.trans L.map_zero.symm)
    exact one_ne_zero (congrFun hz 0)
  · intro h v w he
    apply sub_eq_zero.mp
    by_contra hn
    have hp : v-w ∈ (LinearMap.ker L : Set _) := by simpa [LinearMap.mem_ker] using sub_eq_zero.mpr he
    exact h (one_mem_of_nonzero k (LinearMap.ker L : Set _) hshift
      (fun _ ha _ hb ↦ (LinearMap.ker L).add_mem ha hb) ⟨v-w,hp,hn⟩)

#print axioms one_mem_of_nonzero
#print axioms injective_iff_total_ne_zero

end ProximityGap.DyadicOrbitIndependence
