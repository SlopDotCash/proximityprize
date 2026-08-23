/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.OrderOfElement
import ArkLib.Data.CodingTheory.ProximityGap.CosetRigidity

/-!
# Power-of-2 sharpness of the vanishing-statistic count (Issue #232)

Complement to `CosetExactCount.card_vanishingEsymm_subsets_eq` (which counts the `h ∣ n` case as
exactly `n/h`). Here we prove the **dichotomy**: a vanishing-statistic `h`-subset of `μ_n` injects
into the `gcd(h,n)`-th roots of unity, so `|S| ≤ gcd(h,n)`; hence when `h ∤ n` (so `gcd(h,n) < h`)
**no** such subset exists (`not_exists_esymm_zero_of_not_dvd`). Over the smooth domain `μ_{2^k}` the
only divisors of `n=2^k` are powers of `2`, so vanishing-statistic `h`-subsets exist **iff** `h` is
a power of `2` — a structural fact special to the power-of-2 smooth domain the prize fixes, and a
sharp reason the coset construction is confined to power-of-2 agreement levels. Axiom-clean.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Power-of-2 sharpness / the `h ∤ n` vanishing.** If an `h`-subset `S ⊆ μ_n` has
`e_1(S)=…=e_{h-1}(S)=0` then (rigidity) all its elements share `x^h = c`; combined with `x^n = 1`
this forces `x^{gcd(h,n)}` to be the common constant, so `S` injects into the `gcd(h,n)`-th roots of
unity — hence `|S| ≤ gcd(h,n)`. Therefore when `h ∤ n` (so `gcd(h,n) < h`) NO such `S` exists.
Over the smooth domain `μ_{2^k}` this says: vanishing-statistic `h`-subsets exist **only** when `h`
is a power of `2`; for every non-power-of-2 `h` the count is `0`. -/
theorem card_le_gcd_of_esymm_zero {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    (S : Finset F) (hSsub : ∀ x ∈ S, x ^ n = 1) (hScard : S.card = h)
    (hesymm : ∀ j, 1 ≤ j → j ≤ h - 1 → S.val.esymm j = 0) :
    S.card ≤ Nat.gcd h n := by
  classical
  obtain ⟨c, hc⟩ := all_pow_eq_of_esymm_zero hh hScard hesymm
  obtain ⟨y, hy⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hy0 : y ≠ 0 := by
    intro h0; have := hc y hy; rw [h0, zero_pow (by omega : h ≠ 0)] at this
    have hyn := hSsub y hy; rw [h0, zero_pow (by omega : n ≠ 0)] at hyn
    exact one_ne_zero hyn.symm
  set g := Nat.gcd h n with hg
  -- image of S under x ↦ x * y⁻¹ lands in the g-th roots of unity
  have hmem : ∀ x ∈ S, (x * y⁻¹) ^ g = 1 := by
    intro x hx
    have hcne : c ≠ 0 := by rw [← hc y hy]; exact pow_ne_zero h hy0
    have hxh : (x * y⁻¹) ^ h = 1 := by
      rw [mul_pow, inv_pow, hc x hx, hc y hy, mul_inv_cancel₀ hcne]
    have hxn : (x * y⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hSsub x hx, hSsub y hy, inv_one, mul_one]
    have hd1 := orderOf_dvd_of_pow_eq_one hxh
    have hd2 := orderOf_dvd_of_pow_eq_one hxn
    have : orderOf (x * y⁻¹) ∣ g := Nat.dvd_gcd hd1 hd2
    exact orderOf_dvd_iff_pow_eq_one.mp this
  -- the map x ↦ x*y⁻¹ is injective on S
  have hginj : Set.InjOn (fun x => x * y⁻¹) S := by
    intro a _ b _ hab
    simpa [mul_left_inj' (inv_ne_zero hy0)] using hab
  -- S.image (·*y⁻¹) ⊆ (X^g - 1).roots.toFinset, card ≤ g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n hh
  set T : Finset F := S.image (fun x => x * y⁻¹) with hT
  have hTcard : T.card = S.card := Finset.card_image_of_injOn hginj
  have hTsub : T ⊆ (nthRoots g (1 : F)).toFinset := by
    intro z hz
    rw [hT, Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Multiset.mem_toFinset, mem_nthRoots hgpos]
    exact hmem x hx
  calc S.card = T.card := hTcard.symm
    _ ≤ (nthRoots g (1 : F)).toFinset.card := Finset.card_le_card hTsub
    _ ≤ Multiset.card (nthRoots g (1 : F)) := Multiset.toFinset_card_le _
    _ ≤ g := card_nthRoots g 1

/-- **Count is zero when `h ∤ n`.** No `h`-subset of `μ_n` has `e_1=…=e_{h-1}=0` unless `h ∣ n`. -/
theorem not_exists_esymm_zero_of_not_dvd {n h : ℕ} (hn : 0 < n) (hh : 0 < h) (hnd : ¬ h ∣ n)
    (S : Finset F) (hSsub : ∀ x ∈ S, x ^ n = 1) (hScard : S.card = h)
    (hesymm : ∀ j, 1 ≤ j → j ≤ h - 1 → S.val.esymm j = 0) : False := by
  have hle := card_le_gcd_of_esymm_zero hn hh S hSsub hScard hesymm
  rw [hScard] at hle
  have hlt : Nat.gcd h n < h := by
    rcases lt_or_eq_of_le (Nat.gcd_le_left (m := h) n hh) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ Nat.gcd_dvd_right h n) hnd
  omega

end ArkLib.ProximityGap.Rigidity

#print axioms ArkLib.ProximityGap.Rigidity.not_exists_esymm_zero_of_not_dvd
