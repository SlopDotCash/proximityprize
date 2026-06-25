/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Semiprimitive shortcut gate in the split prime-field regime

The classical semiprimitive Gauss-period mechanism asks for a divisibility of the form

`n ∣ p^t + 1`

(equivalently `p^t ≡ -1 mod n`).  The #464 prize regime over prime fields is the opposite
arithmetic situation: the subgroup order `n` divides `p - 1`, i.e. `p ≡ 1 mod n`.

This file records the elementary obstruction.  If `p ≡ 1 mod n`, then every power satisfies
`p^t ≡ 1 mod n`, hence `p^t + 1 ≡ 2 mod n`.  For `n > 2` this cannot be `0 mod n`.
In particular, for dyadic subgroups `n = 2^a`, `a >= 2`, the semiprimitive divisibility
condition is arithmetically incompatible with the split prime-field condition.

No analytic number theory is proved here.  This is only the modular arithmetic gate explaining why
the semiprimitive closed-form Gauss-period shortcut does not apply to the split prime-field
delta-star floor problem.
-/

namespace ArkLib.ProximityGap.Frontier.SemiprimitiveSplitPrimeFieldGate

/-- The semiprimitive divisibility shape: some exponent has `p^t ≡ -1 mod n`. -/
def SemiprimitiveDivisibility (p n : ℕ) : Prop :=
  ∃ t : ℕ, n ∣ p ^ t + 1

/-- Split modulo `n` is stable under all powers. -/
theorem pow_modEq_one_of_split {p n t : ℕ} (hp : p ≡ 1 [MOD n]) :
    p ^ t ≡ 1 [MOD n] := by
  simpa using Nat.ModEq.pow t hp

/-- Under the split condition `p ≡ 1 mod n`, every semiprimitive candidate
`p^t + 1` is congruent to `2`, not `0`. -/
theorem pow_add_one_modEq_two_of_split {p n t : ℕ} (hp : p ≡ 1 [MOD n]) :
    p ^ t + 1 ≡ 2 [MOD n] := by
  calc
    p ^ t + 1 ≡ 1 + 1 [MOD n] :=
      (pow_modEq_one_of_split (t := t) hp).add (Nat.ModEq.refl 1)
    _ = 2 := by norm_num

/-- If `n > 2`, the split prime-field condition rules out the semiprimitive divisibility
`n ∣ p^t + 1` at every exponent `t`. -/
theorem not_dvd_pow_add_one_of_split {p n t : ℕ} (hn : 2 < n) (hp : p ≡ 1 [MOD n]) :
    ¬ n ∣ p ^ t + 1 := by
  intro hdiv
  have hzero : p ^ t + 1 ≡ 0 [MOD n] := Nat.modEq_zero_iff_dvd.mpr hdiv
  have htwo : p ^ t + 1 ≡ 2 [MOD n] := pow_add_one_modEq_two_of_split hp
  have h20 : (2 : ℕ) ≡ 0 [MOD n] := htwo.symm.trans hzero
  rw [Nat.ModEq, Nat.mod_eq_of_lt hn, Nat.zero_mod] at h20
  omega

/-- Split prime-field congruence is incompatible with the semiprimitive condition for every
nontrivial modulus `n > 2`. -/
theorem not_semiprimitiveDivisibility_of_split {p n : ℕ} (hn : 2 < n)
    (hp : p ≡ 1 [MOD n]) :
    ¬ SemiprimitiveDivisibility p n := by
  rintro ⟨t, hdiv⟩
  exact not_dvd_pow_add_one_of_split (p := p) (t := t) hn hp hdiv

/-- Congruence-from-remainder form of `not_dvd_pow_add_one_of_split`. -/
theorem not_dvd_pow_add_one_of_mod_eq_one {p n t : ℕ} (hn : 2 < n)
    (hp : p % n = 1) :
    ¬ n ∣ p ^ t + 1 := by
  have hpmod : p ≡ 1 [MOD n] := by
    rw [Nat.ModEq]
    simpa [Nat.mod_eq_of_lt (by omega : 1 < n)] using hp
  exact not_dvd_pow_add_one_of_split (p := p) (n := n) (t := t) hn hpmod

/-- Dyadic moduli `2^a` are above `2` once `a >= 2`. -/
theorem two_lt_two_pow_of_two_le {a : ℕ} (ha : 2 <= a) :
    2 < 2 ^ a := by
  calc
    2 < 2 ^ 2 := by norm_num
    _ <= 2 ^ a := Nat.pow_le_pow_right (by norm_num : 1 <= (2 : ℕ)) ha

/-- Dyadic split prime-field gate: for `a >= 2`, no exponent can satisfy
`2^a ∣ p^t + 1` when `p ≡ 1 mod 2^a`. -/
theorem dyadic_not_dvd_pow_add_one_of_split {p a t : ℕ} (ha : 2 <= a)
    (hp : p ≡ 1 [MOD 2 ^ a]) :
    ¬ 2 ^ a ∣ p ^ t + 1 :=
  not_dvd_pow_add_one_of_split (p := p) (n := 2 ^ a) (t := t)
    (two_lt_two_pow_of_two_le ha) hp

/-- Bundled dyadic verdict: split prime-field congruence and semiprimitive divisibility are
mutually incompatible for every prize-relevant dyadic subgroup `2^a`, `a >= 2`. -/
theorem dyadic_not_semiprimitiveDivisibility_of_split {p a : ℕ} (ha : 2 <= a)
    (hp : p ≡ 1 [MOD 2 ^ a]) :
    ¬ SemiprimitiveDivisibility p (2 ^ a) := by
  exact not_semiprimitiveDivisibility_of_split
    (p := p) (n := 2 ^ a) (two_lt_two_pow_of_two_le ha) hp

/-! ## Axiom audit -/
#print axioms SemiprimitiveDivisibility
#print axioms pow_modEq_one_of_split
#print axioms pow_add_one_modEq_two_of_split
#print axioms not_dvd_pow_add_one_of_split
#print axioms not_semiprimitiveDivisibility_of_split
#print axioms not_dvd_pow_add_one_of_mod_eq_one
#print axioms two_lt_two_pow_of_two_le
#print axioms dyadic_not_dvd_pow_add_one_of_split
#print axioms dyadic_not_semiprimitiveDivisibility_of_split

end ArkLib.ProximityGap.Frontier.SemiprimitiveSplitPrimeFieldGate
