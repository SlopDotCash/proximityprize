/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AbacusNCore
import Mathlib

/-!
# The rectangle n-core dichotomy (#389/#371) — the adversarial HOMDS shape, pinned

For the smooth domain `μ_n` the higher-order-MDS / GM-MDS certificate `det(ζ^(β_j·i))` is nonzero
iff the abacus `n`-core of the β-set is empty (`HOMDSSmoothObstruction`, `AbacusNCore`).  The
list-decoding obstruction shapes are *rectangles* `λ = a^h`.  This file pins exactly when a rectangle
is empty-`n`-core:

> **`rectBeta_nCoreEmpty_iff`** — for `0 < h < n`, `nCoreEmpty (a^h) ↔ n ∣ a`.

So a rectangle of height `h < n` (e.g. a list of `L = h < n` codewords) has an empty `n`-core — HOMDS
holds — **iff its width `a` is a multiple of the domain size**.  Generic widths (`n ∤ a`) give a
NONEMPTY core: rectangles are exactly the adversarial nonempty-core shape, and the obstruction reduces
to the single arithmetic condition `n ∣ a`.  This scopes the live n-core route's open crux to a
concrete target — *are rectangle agreement-patterns `a^L` with `n ∤ a` GM-MDS-reachable by an actual
window-radius `RS[μ_n,k]` list-decoding instance?* — since the dichotomy guarantees those are the only
regular shapes that can fail.

Proof: `nCoreEmpty ⟺ β_j` distinct mod n.  For `n ∣ a` every `β_j ≡ n−1−j`, manifestly distinct.
For `n ∤ a` the explicit pair `j₁ = min(h−1, r−1)`, `j₂ = j₁+(n−r)` (`r = a % n`) collides mod n.
Axiom-clean.
-/

open Finset
open ArkLib.ProximityGap.AbacusNCore

namespace ArkLib.ProximityGap.RectNCore

/-- The β-set of the rectangle partition `λ = a^h` over the domain `μ_n`:
`β_j = (a if j < h else 0) + (n − 1 − j)`. -/
def rectBeta (n a h : ℕ) : Fin n → ℕ := fun j => (if (j : ℕ) < h then a else 0) + (n - 1 - (j : ℕ))

/-- **The rectangle n-core dichotomy.** For the rectangle partition `a^h` over `μ_n`
(`0 < h < n`), the abacus `n`-core is empty **iff** `n ∣ a` — equivalently the smooth-domain HOMDS
certificate `det(ζ^(β_j·i))` is nonzero iff the rectangle width is a multiple of the domain size.
Generic widths (`n ∤ a`) give a NONEMPTY core, so rectangles are exactly the adversarial
nonempty-core shape and the obstruction is the single arithmetic condition `n ∣ a`. -/
theorem rectBeta_nCoreEmpty_iff (n a h : ℕ) (h0 : 0 < h) (hn : h < n) :
    nCoreEmpty (rectBeta n a h) ↔ n ∣ a := by
  classical
  have hnpos : 0 < n := lt_trans h0 hn
  rw [nCoreEmpty_iff_injOn_mod]
  constructor
  · -- injective ⟹ n ∣ a  (contrapositive: n ∤ a gives an explicit collision)
    intro hinj
    by_contra hndvd
    set r := a % n with hr
    have hrlt : r < n := Nat.mod_lt a hnpos
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) hndvd
      · exact h
    set j1 : ℕ := min (h - 1) (r - 1) with hj1
    set j2 : ℕ := j1 + (n - r) with hj2
    have hj1le1 : j1 ≤ h - 1 := min_le_left _ _
    have hj1le2 : j1 ≤ r - 1 := min_le_right _ _
    have hj1ge : h - 1 ≤ j1 ∨ r - 1 ≤ j1 := by
      rcases le_total (h - 1) (r - 1) with hle | hle
      · exact Or.inl (by rw [hj1, min_eq_left hle])
      · exact Or.inr (by rw [hj1, min_eq_right hle])
    have hj1ltn : j1 < n := by omega
    have hj2ltn : j2 < n := by omega
    have hj1lth : j1 < h := by omega
    have hj2geh : h ≤ j2 := by omega
    have hane : j1 ≠ j2 := by omega
    have haq : a = n * (a / n) + r := by rw [hr]; exact (Nat.div_add_mod a n).symm
    have heq : (fun j : Fin n => rectBeta n a h j % n) ⟨j1, hj1ltn⟩
             = (fun j : Fin n => rectBeta n a h j % n) ⟨j2, hj2ltn⟩ := by
      show ((if j1 < h then a else 0) + (n - 1 - j1)) % n
         = ((if j2 < h then a else 0) + (n - 1 - j2)) % n
      rw [if_pos hj1lth, if_neg (not_lt.mpr hj2geh), zero_add]
      have hmul : (a / n + 1) * n = n * (a / n) + n := by ring
      have hkey : a + (n - 1 - j1) = (n - 1 - j2) + (a / n + 1) * n := by omega
      rw [hkey, Nat.add_mul_mod_self_right]
    have hfeq : (⟨j1, hj1ltn⟩ : Fin n) = ⟨j2, hj2ltn⟩ := hinj heq
    exact hane (congrArg Fin.val hfeq)
  · -- n ∣ a ⟹ every β j % n = n−1−j ⟹ injective
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hval : ∀ j : Fin n, rectBeta n a h j % n = n - 1 - (j : ℕ) := by
      intro j
      have hjlt : (j : ℕ) < n := j.2
      show ((if (j : ℕ) < h then a else 0) + (n - 1 - (j : ℕ))) % n = n - 1 - (j : ℕ)
      by_cases hjh : (j : ℕ) < h
      · rw [if_pos hjh, hc]
        have hlt : n - 1 - (j : ℕ) < n := by omega
        have hrw : n * c + (n - 1 - (j : ℕ)) = (n - 1 - (j : ℕ)) + c * n := by ring
        rw [hrw, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      · rw [if_neg hjh, zero_add, Nat.mod_eq_of_lt (by omega)]
    intro x y hxy
    simp only [] at hxy
    rw [hval x, hval y] at hxy
    exact Fin.ext (by have := x.2; have := y.2; omega)

end ArkLib.ProximityGap.RectNCore

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.RectNCore.rectBeta_nCoreEmpty_iff
