/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPow

/-!
# Q1 char-0 sharpening — Claim A as a clean iff (dyadic Lam–Leung), issue #407

This file packages **Claim A** of the Q1 char-0 sharpening
(`docs/kb/deltastar-407-Q1-inequality-sharpened-2026-06-14.md`) as a single iff at the level of
finite subsets of the `2^(m+1)`-th roots of unity in a characteristic-zero field:

  `e_1(S) = ∑_{x ∈ S} x = 0   ⟺   S = −S   (antipodal-symmetric)`.

Here `S ⊆ μ_{2^(m+1)}` and `e_1(S)` is the first elementary symmetric function (the linear power
sum), which is `± the top odd coefficient` (`w^{k−1}`) of the even/odd split
`σ_S(z) = G(z²) + z·H(z²)`.  So this iff is exactly the statement
`deg_w H = k − 1 ⟺ e_1(S) ≠ 0` paired with the antipodal characterization of `e_1(S) = 0`:
when `e_1(S) = 0` we have `S = −S`, the antipodal-symmetric case where `H = 0`.

## Mechanism

* **Forward (`∑ = 0 ⟹ S = −S`)** is the dyadic Lam–Leung theorem at the prime 2, already proven
  in `LamLeungTwoPow.vanishing_sum_antipodal` (a vanishing sum of `2^(m+1)`-th roots is closed
  under negation).  We upgrade `∀ x ∈ S, −x ∈ S` to the set equality `S.image (−·) = S` by a
  cardinality argument (negation is injective).
* **Converse (`S = −S ⟹ ∑ = 0`)** is a fixed-point-free involution argument: pairing `x ↔ −x`
  cancels the sum.  The pairing is fixed-point-free because `0 ∉ S` (roots of unity are nonzero)
  and `char ≠ 2`, so `x ≠ −x`.  We use `Finset.sum_involution`.

## Scope (honest)

This is the **characteristic-0** statement only.  The char-`p` version — whether the odd power
sums `e_1 ≡ e_3 ≡ … ≡ 0 (mod p)` can hold *simultaneously* for an antipodal-free `S` at prize
scale — is the open NOVEL-A simultaneous-rigidity problem and is **not** addressed here.  Dyadic
necessity (`N = 2^μ` essential) is documented numerically in
`scripts/probes/probe_q1_claimAB_dyadic.py`: non-power-of-2 `N` violates Claim A (e.g. `N = 12`
has 4 antipodal-free vanishing sums), matching the char-`p` failure mode.

Axiom-clean.  Issue #407.
-/

open Finset

namespace ProximityGap

namespace Q1ClaimA

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

omit [DecidableEq F] [CharZero F] in
/-- **Converse direction (the easy half).**  A negation-closed finite set of nonzero elements of
a field of characteristic `≠ 2` has vanishing sum: pairing `x ↔ −x` is a fixed-point-free
involution that cancels the sum. -/
theorem sum_eq_zero_of_neg_closed [NeZero (2 : F)] {S : Finset F} (h0 : (0 : F) ∉ S)
    (hsym : ∀ x ∈ S, -x ∈ S) :
    ∑ x ∈ S, x = 0 := by
  classical
  refine Finset.sum_involution (fun x _ => -x) ?_ ?_ ?_ ?_
  · -- `f a + f (g a) = a + (-a) = 0`
    intro a _; ring
  · -- fixed-point-free on nonzero elements: `a ≠ 0 ⟹ -a ≠ a`
    intro a ha hne hcontra
    apply hne
    have htwo : (2 : F) * a = 0 := by linear_combination -hcontra
    have h2 : (2 : F) ≠ 0 := NeZero.ne _
    rcases mul_eq_zero.mp htwo with h | h
    · exact absurd h h2
    · -- `a = 0`, contradicting `0 ∉ S`
      exact absurd (h ▸ ha) h0
  · -- `-a ∈ S` for `a ∈ S`
    intro a ha; exact hsym a ha
  · -- involution: `-(-a) = a`
    intro a _; ring

omit [CharZero F] in
/-- Negation-closedness as a pointwise statement upgrades to the set equality `S.image (−·) = S`,
since negation is injective. -/
theorem image_neg_eq_of_neg_closed {S : Finset F} (hsym : ∀ x ∈ S, -x ∈ S) :
    S.image (fun x => -x) = S := by
  classical
  have hsub : S.image (fun x => -x) ⊆ S := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hsym x hx
  have hcard : (S.image (fun x => -x)).card = S.card :=
    Finset.card_image_of_injective S neg_injective
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

omit [CharZero F] in
/-- Conversely, `S.image (−·) = S` gives the pointwise negation-closedness. -/
theorem neg_closed_of_image_neg_eq {S : Finset F} (hS : S.image (fun x => -x) = S) :
    ∀ x ∈ S, -x ∈ S := by
  intro x hx
  rw [← hS]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- **Claim A (forward), set form.**  In characteristic zero, a vanishing sum of `2^(m+1)`-th
roots of unity is antipodal-symmetric: `S.image (−·) = S`. -/
theorem image_neg_eq_of_sum_eq_zero {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hS : ∀ x ∈ S, x ^ (2 ^ (m + 1)) = 1) (hsum : ∑ x ∈ S, x = 0) :
    S.image (fun x => -x) = S :=
  image_neg_eq_of_neg_closed (LamLeungTwoPow.vanishing_sum_antipodal hζ hS hsum)

omit [DecidableEq F] [CharZero F] in
/-- The `2^(m+1)`-th roots of unity are nonzero, so `0 ∉ S` for any set of them. -/
theorem zero_not_mem {m : ℕ} {S : Finset F}
    (hS : ∀ x ∈ S, x ^ (2 ^ (m + 1)) = 1) :
    (0 : F) ∉ S := by
  intro h0
  have := hS 0 h0
  rw [zero_pow (by positivity)] at this
  exact zero_ne_one this

/-- **Claim A, the iff (dyadic Lam–Leung, characteristic 0).**

For a finite set `S` of `2^(m+1)`-th roots of unity in a characteristic-zero field,
`e_1(S) = ∑_{x ∈ S} x = 0` holds **iff** `S` is antipodal-symmetric (`S.image (−·) = S`).

This is the clean iff form of Claim A: the linear power sum / top odd coefficient `e_1(S)`
vanishes exactly when `S = −S`. -/
theorem sum_eq_zero_iff_image_neg_eq {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hS : ∀ x ∈ S, x ^ (2 ^ (m + 1)) = 1) :
    (∑ x ∈ S, x = 0) ↔ S.image (fun x => -x) = S := by
  constructor
  · intro hsum
    exact image_neg_eq_of_sum_eq_zero hζ hS hsum
  · intro himg
    have h2 : NeZero (2 : F) := ⟨two_ne_zero⟩
    exact sum_eq_zero_of_neg_closed (zero_not_mem hS) (neg_closed_of_image_neg_eq himg)

end Q1ClaimA

end ProximityGap

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ProximityGap.Q1ClaimA.sum_eq_zero_of_neg_closed
#print axioms ProximityGap.Q1ClaimA.image_neg_eq_of_sum_eq_zero
#print axioms ProximityGap.Q1ClaimA.sum_eq_zero_iff_image_neg_eq
