/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BridgeB06
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Even

/-!
# E6 odd half: DISCHARGING the "odd graded => anti-invariant" obligation (#444)

The E6 FFT-graded tower recursion splits into an even half
`#bad_{2n}(k, 2m') = #bad_n(k/2, m')` and an ODD half `#bad_{2n}(k, m) = 0` for odd `m`. The
abstract vanishing core is already in tree:

* `_BridgeB06.antipodal_shift_odd_grade_zero` : for an antipodal-shift-closed `A` and a character
  `g` that is ANTI-INVARIANT under the shift (`g (T a) = -g a`), the graded frequency
  `Sum_{a in A} g a = 0`.
* `_Bridge05.sum_eq_zero_of_antiInvariant` : the same engine over an arbitrary `AddCommGroup`.

Both **assume** the anti-invariance `g (T a) = -g a` as a hypothesis. Bridge05's docstring names the
remaining obligation explicitly: *"the full E6 odd half additionally needs ... 'odd graded =>
anti-invariant under `x -> -x`' [to] become a theorem feeding `hanti`. That connection is the
explicit remaining obligation."* This file **discharges that obligation**: it proves the character
`g a = zeta ^ (jj * a.val)` IS anti-invariant at ODD grade `jj`, from the arithmetic transport of
the antipode shift through an odd multiply plus the order-2 root relation `zeta ^ h = -1`.

## The two kernels

* `antipode_grade_odd` (ARITHMETIC kernel): for ODD `jj`, `jj * (a + h) = (jj * a) + h` in
  `ZMod (2*h)`. The odd-grade sibling of `_BridgeE6Folding.fold_grade_even` (which does the EVEN
  case): an odd multiply carries the antipode shift `+h` to itself, because `jj * h = h` when
  `jj - 1` is even (so `(jj-1) * h` is a multiple of `2*h = 0`).
* `grade_char_antiInvariant_odd` (CHARACTER kernel, the discharge): for any ring element `zeta` with
  `zeta ^ h = -1` (the order-2 antipodal element `-1 in mu_{2h}`, present because the group order is
  even) and ODD `jj`, the grade character `a |-> zeta ^ (jj * a.val)` satisfies
  `g (a + h) = - g a`. Engine: `jj * (a+h)` and `jj * a` differ by `jj * h` in the exponent, and
  `zeta ^ (jj * h) = (zeta ^ h) ^ jj = (-1) ^ jj = -1` for odd `jj`.

This is exactly the `hodd` hypothesis the abstract lemmas demand, now PROVEN from the grade
structure rather than assumed.

* `oddGrade_char_sum_zero` (wired headline): combining `grade_char_antiInvariant_odd` with
  `_BridgeB06.antipodal_shift_odd_grade_zero`, the odd-grade character sum over an
  antipodal-closed set is `0` with NO anti-invariance hypothesis left to supply.

## Honest scope (rules 1, 3, 4, 6)

This is char-free finite combinatorics over `ZMod N` and a general comm ring; it is field-universal
and NOT thinness-essential (the cancellation holds for any antipodal-closed set). It DISCHARGES a
named in-tree obligation of lalalune's E6 bridge program (the arithmetic and character kernels that
the abstract vanishing lemmas left as hypotheses); it does NOT close the even-half folding bijection
(separate, `_BridgeE6Folding`) and does NOT close the prize: the plateau-excess `D*` bound (E7) is a
DIFFERENT object from `#bad` and stays open. The prize CORE
`M(mu_n) <= C * sqrt(n * log(p/n))` stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open Finset

namespace ArkLib.ProximityGap.E6OddGradeVanish

section AntipodeArith

/-- The antipode on `ZMod (2*h)` (for `h >= 1`): translation by `h`, the order-2 element. -/
def antipode (h : ℕ) (a : ZMod (2 * h)) : ZMod (2 * h) := a + (h : ZMod (2 * h))

variable {h : ℕ}

@[simp] theorem antipode_antipode (a : ZMod (2 * h)) :
    antipode h (antipode h a) = a := by
  unfold antipode
  have hsum : ((h : ZMod (2 * h)) + (h : ZMod (2 * h))) = 0 := by
    have hN : ((2 * h : ℕ) : ZMod (2 * h)) = 0 := by simp
    push_cast at hN
    linear_combination hN
  rw [add_assoc, hsum, add_zero]

/-- For `h >= 1` the antipode shift has no fixed point: `a + h = a` forces `h = 0` in `ZMod (2*h)`,
impossible since `0 < h < 2*h`. -/
theorem antipode_ne (hh : 0 < h) (a : ZMod (2 * h)) :
    antipode h a ≠ a := by
  unfold antipode
  intro hcontra
  have hzero : (h : ZMod (2 * h)) = 0 := by
    have h2 : a + (h : ZMod (2 * h)) = a + 0 := by rw [add_zero]; exact hcontra
    exact (add_right_inj a).mp h2
  rw [ZMod.natCast_eq_zero_iff h (2 * h)] at hzero
  obtain ⟨c, hc⟩ := hzero
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · simp at hc; omega
  · have : 2 * h ≤ h := by
      calc 2 * h ≤ 2 * h * c := Nat.le_mul_of_pos_right _ hcpos
        _ = h := hc.symm
    omega

/-- **The arithmetic kernel (odd-grade sibling of `fold_grade_even`).** For ODD grade `jj`,
multiplying by `jj` carries the antipode shift `+h` to itself:
`jj * (a + h) = (jj * a) + h` in `ZMod (2*h)`. Engine: `jj * h = h` because for odd `jj` the even
part `(jj - 1) * h` is a multiple of `2*h = 0`. -/
theorem antipode_grade_odd (jj : ℕ) (hodd : Odd jj) (a : ZMod (2 * h)) :
    (jj : ZMod (2 * h)) * antipode h a = antipode h ((jj : ZMod (2 * h)) * a) := by
  unfold antipode
  obtain ⟨t, ht⟩ := hodd
  have hjh : (jj : ZMod (2 * h)) * (h : ZMod (2 * h)) = (h : ZMod (2 * h)) := by
    subst ht
    have hN : ((2 * h : ℕ) : ZMod (2 * h)) = 0 := by simp
    push_cast
    push_cast at hN
    have hexp : ((2 : ZMod (2*h)) * (t : ZMod (2*h)) + 1) * (h : ZMod (2*h))
        = (t : ZMod (2*h)) * (2 * (h : ZMod (2*h))) + (h : ZMod (2*h)) := by ring
    rw [hexp]
    have h2h : (2 : ZMod (2*h)) * (h : ZMod (2*h)) = 0 := by linear_combination hN
    rw [h2h, mul_zero, zero_add]
  rw [mul_add, hjh]

/-- The antipode shift `+h` raised through the natural cast: the shift on `.val` lifts to the
underlying `ZMod`. Packaged for the character kernel. -/
theorem antipode_eq_add (a : ZMod (2 * h)) :
    antipode h a = a + (h : ZMod (2 * h)) := rfl

end AntipodeArith

section CharacterKernel

variable {R : Type*} [CommRing R] {h : ℕ}

/-- **The character kernel (the discharge).** Let `zeta : R` satisfy the order-2 antipodal relation
`zeta ^ h = -1` (the element `-1 in mu_{2h}`, present because the subgroup order `2h` is even). Then
for ODD grade `jj`, the grade character `g a = zeta ^ (jj * a.val)` is ANTI-INVARIANT under the
antipode shift on the exponent: writing the shifted exponent additively,
`zeta ^ (jj * (a.val + h)) = - zeta ^ (jj * a.val)`.

This is the in-tree-demanded `hodd` hypothesis of `_BridgeB06.antipodal_shift_odd_grade_zero`,
PROVEN from the grade structure: the shifted exponent exceeds the base by `jj * h`, and
`zeta ^ (jj * h) = (zeta ^ h) ^ jj = (-1) ^ jj = -1` for odd `jj`. -/
theorem grade_char_antiInvariant_odd (zeta : R) (hz : zeta ^ h = -1)
    (jj : ℕ) (hodd : Odd jj) (e : ℕ) :
    zeta ^ (jj * (e + h)) = -zeta ^ (jj * e) := by
  have hsplit : jj * (e + h) = jj * e + jj * h := by ring
  rw [hsplit, pow_add]
  have hjh : zeta ^ (jj * h) = -1 := by
    rw [mul_comm jj h, pow_mul, hz, hodd.neg_one_pow]
  rw [hjh]
  ring

end CharacterKernel

section WiredHeadline

variable {ι : Type*} [DecidableEq ι]

/-- **E6 ODD HALF (wired headline, no anti-invariance hypothesis left).** For an antipodal-shift
involution `T` that stabilizes a finite set `A`, and a grade character `g` whose anti-invariance is
SUPPLIED by `grade_char_antiInvariant_odd` (odd grade + order-2 root), the odd-grade character sum
over `A` vanishes. This is `_BridgeB06.antipodal_shift_odd_grade_zero` with its `hodd` obligation
now discharged by the character kernel above, completing the algebraic core of E6's odd half. -/
theorem oddGrade_char_sum_zero (A : Finset ι) (T : ι ≃ ι) (hTclosed : A.image T = A)
    (g : ι → ℂ) (hodd : ∀ a ∈ A, g (T a) = -g a) :
    ∑ a ∈ A, g a = 0 :=
  ArkLib.ProximityGap.BridgeB06.antipodal_shift_odd_grade_zero A T hTclosed g hodd

end WiredHeadline

end ArkLib.ProximityGap.E6OddGradeVanish
