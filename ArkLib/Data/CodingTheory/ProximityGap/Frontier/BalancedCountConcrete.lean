/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergyThreeExact

/-!
# Grounding AVENUE A: the `BalancedCount` carrier is CONCRETE, not just an abstract hypothesis (#444)

`Frontier/CharZeroEnergyThreeExact.lean` proves the depth-3 additive energy closed form
`E_3(mu_n) = 15n^3 - 45n^2 + 40n` from an ABSTRACT carrier `B : N -> N -> Z` satisfying the named
`BalancedCount` predicate (base case + the add-one-class recursions `rec2`, `rec4`, `rec6`). That
predicate was stated but NEVER instantiated: nothing in tree exhibited a concrete `B` satisfying it,
so the `B6_eq_E3` reduction (and the `kappa6_eq` consequence) rested on a possibly-vacuous structure.

This file removes that gap. It defines the concrete class-balanced count by the explicit add-one-class
convolution

  `balancedCount k 0       = if k = 0 then 1 else 0`,
  `balancedCount k (m+1)   = SUM_{j=0..k/2}  C(k, 2j) * C(2j, j) * balancedCount (k - 2j) m`,

which is exactly the number of length-`k` antipodal-class tuples (each of `m` classes `{z,-z}` used
with equal `+`/`-` multiplicity) -- the zero-sum count `E_{k/2}(mu_{2m})` under the Lam-Leung balance
characterization. It then proves

  **`balancedCount_isBalancedCount : BalancedCount balancedCount`**

i.e. the concrete carrier satisfies the base case `base0` and all three recursions `rec2`, `rec4`,
`rec6` of `Frontier.CharZeroEnergyThree.BalancedCount`. Consequently the recursion-solution theorems
of that file (`B2_closed`, `B4_closed`, `B6_closed`, `B6_eq_E3`) hold for the CONCRETE count:

  **`balancedCount_eq_E3 : balancedCount 6 m = 15(2m)^3 - 45(2m)^2 + 40(2m)`**.

So the `BalancedCount` named input of AVENUE A is now DISCHARGED by an explicit carrier -- the
structure is non-vacuous and the depth-3 energy closed form is grounded on a concrete combinatorial
object, not a bare hypothesis.

## Probe

`scripts/probes/probe_balanced_count_recursion.py` (brute enumeration of `Fin k -> Fin m x Bool`
class-balanced tuples, `k in {0,2,4,6}`, `m = 0..3`) confirms `balancedCount k m` equals the brute
class-balanced tuple count at every checked `(k, m)`, and that the brute count satisfies `rec2`,
`rec4`, `rec6` directly. `scripts/probes/probe_balanced_convolution.py` confirms the convolution
recursion reproduces the brute count (`conv == brute` at all `(k, m)` checked).

## Honest scope (and relation to PR #450)

This is a pure-combinatorics grounding of an ALREADY-PROVEN reduction: it makes the `BalancedCount`
carrier concrete and exhibits it satisfying the predicate, so AVENUE A's `B6_eq_E3` rests on a
witnessed structure rather than a bare, never-instantiated abstract hypothesis.

**Relation to PR #450 (`E3StrataCharZero` / `negSymCount_six_closed`).** PR #450 independently proved
the SAME depth-3 closed form `15n^3 - 45n^2 + 40n` DIRECTLY on the real field-tuple object
(`negSymCount G 6` over a negation-closed `G subset F`), a strictly stronger result than this carrier
grounding -- so the analytic CONTENT of AVENUE A's `E_3` value is already settled in tree by #450, NOT
by this file. What this file adds is narrow and honest: #450 does NOT instantiate the specific abstract
carrier `CharZeroEnergyThree.BalancedCount` that `B6_eq_E3`/`kappa6_eq` consume, so that structure was
still dangling (never witnessed). This exhibits the explicit witness, closing the lone
non-vacuity/instantiation gap of `CharZeroEnergyThreeExact.lean`. It is combinatorial hygiene grounding
an abstract carrier, NOT a frontier advance.

It does NOT discharge the OTHER named input of AVENUE A (`hLL`, the Lam-Leung depth-<=3 balance
characterization tying this combinatorial count to the actual additive-energy zero-sum count -- the
separate analytic input, developed in `LamLeungUnconditionalGeneral.lean` and, on the real object, in
#450's `_E3NegSymConverse`). And it is NOT a CORE closure and NOT thinness-essential: the deep BGK /
Paley-wall residual lives at depth `r ~ log m`, untouched here. CORE
(`M(mu_n) <= C*sqrt(n*log(p/n))`) stays OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree

namespace ArkLib.ProximityGap.Frontier.BalancedCountConcrete

/-- **The concrete class-balanced count.** `balancedCount k m` is the number of length-`k` tuples
over `m` antipodal classes `{z, -z}` in which every class is used with equal `+`/`-` multiplicity,
defined by the explicit add-one-class convolution recursion (a new class occupies `2j` of the `k`
positions, with `j` `+`'s and `j` `-`'s among them, contributing `C(k, 2j) * C(2j, j)`). -/
def balancedCount : ℕ → ℕ → ℤ
  | k, 0 => if k = 0 then 1 else 0
  | k, (m + 1) => ∑ j ∈ Finset.range (k / 2 + 1),
      (Nat.choose k (2 * j) : ℤ) * (Nat.choose (2 * j) j : ℤ) * balancedCount (k - 2 * j) m

@[simp] theorem balancedCount_zero_class (k : ℕ) :
    balancedCount k 0 = if k = 0 then 1 else 0 := rfl

theorem balancedCount_succ (k m : ℕ) :
    balancedCount k (m + 1) = ∑ j ∈ Finset.range (k / 2 + 1),
      (Nat.choose k (2 * j) : ℤ) * (Nat.choose (2 * j) j : ℤ) * balancedCount (k - 2 * j) m := rfl

/-- **`balancedCount 0 m = 1`**: the empty tuple is balanced over any number of classes. -/
@[simp] theorem balancedCount_zero_len (m : ℕ) : balancedCount 0 m = 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [balancedCount_succ]
      simp [ih]

/-- **`base0`**: no classes ⟹ no nonempty balanced tuple. -/
theorem balancedCount_base0 (k : ℕ) (hk : 1 ≤ k) : balancedCount k 0 = 0 := by
  have hk0 : k ≠ 0 := by omega
  simp [balancedCount_zero_class, hk0]

/-- **`rec2`**: the length-2 add-one-class recursion. The `j`-sum (`j = 0, 1`) gives
`balancedCount 2 m + C(2,2)*C(2,1)*balancedCount 0 m = balancedCount 2 m + 2`. -/
theorem balancedCount_rec2 (m : ℕ) :
    balancedCount 2 (m + 1) = balancedCount 2 m + 2 := by
  rw [balancedCount_succ]
  -- range (2/2 + 1) = range 2 = {0, 1}
  simp only [show (2 : ℕ) / 2 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [balancedCount_zero_len, show Nat.choose 2 0 = 1 from rfl,
    show Nat.choose 2 2 = 1 from rfl, show Nat.choose 0 0 = 1 from rfl]

/-- **`rec4`**: the length-4 add-one-class recursion. The `j`-sum (`j = 0,1,2`) gives
`balancedCount 4 m + C(4,2)*C(2,1)*balancedCount 2 m + C(4,4)*C(4,2)*balancedCount 0 m
= balancedCount 4 m + 12*balancedCount 2 m + 6`. -/
theorem balancedCount_rec4 (m : ℕ) :
    balancedCount 4 (m + 1) = balancedCount 4 m + 12 * balancedCount 2 m + 6 := by
  rw [balancedCount_succ]
  simp only [show (4 : ℕ) / 2 + 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [balancedCount_zero_len, show Nat.choose 4 0 = 1 from rfl,
    show Nat.choose 4 2 = 6 from rfl, show Nat.choose 4 4 = 1 from rfl,
    show Nat.choose 2 1 = 2 from rfl, show Nat.choose 0 0 = 1 from rfl]

/-- **`rec6`**: the length-6 add-one-class recursion. The `j`-sum (`j = 0,1,2,3`) gives
`balancedCount 6 m + C(6,2)*C(2,1)*balancedCount 4 m + C(6,4)*C(4,2)*balancedCount 2 m
+ C(6,6)*C(6,3)*balancedCount 0 m = balancedCount 6 m + 30*balancedCount 4 m + 90*balancedCount 2 m
+ 20`. -/
theorem balancedCount_rec6 (m : ℕ) :
    balancedCount 6 (m + 1)
      = balancedCount 6 m + 30 * balancedCount 4 m + 90 * balancedCount 2 m + 20 := by
  rw [balancedCount_succ]
  simp only [show (6 : ℕ) / 2 + 1 = 4 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [balancedCount_zero_len, show Nat.choose 6 0 = 1 from rfl,
    show Nat.choose 6 2 = 15 from rfl, show Nat.choose 6 4 = 15 from rfl,
    show Nat.choose 6 6 = 1 from rfl, show Nat.choose 2 1 = 2 from rfl,
    show Nat.choose 4 2 = 6 from rfl, show Nat.choose 6 3 = 20 from rfl,
    show Nat.choose 0 0 = 1 from rfl]

/-- **The concrete carrier satisfies `BalancedCount`.** Discharges the AVENUE A named input with an
explicit witness: `balancedCount` is a concrete `B : N -> N -> Z` satisfying `base0`, `rec2`, `rec4`,
`rec6`. -/
theorem balancedCount_isBalancedCount : BalancedCount balancedCount where
  base0 := balancedCount_base0
  rec2 := balancedCount_rec2
  rec4 := balancedCount_rec4
  rec6 := balancedCount_rec6

/-- **`BalancedCount` is non-vacuous** (existence of a carrier). -/
theorem exists_balancedCount : ∃ B : ℕ → ℕ → ℤ, BalancedCount B :=
  ⟨balancedCount, balancedCount_isBalancedCount⟩

/-! ### The depth `2, 4, 6` closed forms, now for the CONCRETE count. -/

/-- **`balancedCount 2 m = 2m`** (`E_1(mu_{2m}) = n`), via `B2_closed` on the concrete carrier. -/
theorem balancedCount_two (m : ℕ) : balancedCount 2 m = 2 * m :=
  B2_closed balancedCount_isBalancedCount m

/-- **`balancedCount 4 m = 12m^2 - 6m`** (`E_2(mu_{2m}) = 3n^2 - 3n`), via `B4_closed`. -/
theorem balancedCount_four (m : ℕ) : balancedCount 4 m = 12 * (m : ℤ) ^ 2 - 6 * m :=
  B4_closed balancedCount_isBalancedCount m

/-- **`balancedCount 6 m = 120m^3 - 180m^2 + 80m`** (depth-3 energy), via `B6_closed`. -/
theorem balancedCount_six (m : ℕ) :
    balancedCount 6 m = 120 * (m : ℤ) ^ 3 - 180 * (m : ℤ) ^ 2 + 80 * m :=
  B6_closed balancedCount_isBalancedCount m

/-- **AVENUE A target on the concrete count: `E_3(mu_n) = 15n^3 - 45n^2 + 40n`** (`n = 2m`).
The depth-3 additive-energy class-balanced count `balancedCount 6 m` equals the AVENUE A closed form,
now from the EXPLICIT carrier rather than the abstract hypothesis. -/
theorem balancedCount_eq_E3 (m : ℕ) :
    balancedCount 6 m = 15 * (2 * (m : ℤ)) ^ 3 - 45 * (2 * (m : ℤ)) ^ 2 + 40 * (2 * (m : ℤ)) :=
  B6_eq_E3 balancedCount_isBalancedCount m

end ArkLib.ProximityGap.Frontier.BalancedCountConcrete

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.BalancedCountConcrete.balancedCount_isBalancedCount
#print axioms ArkLib.ProximityGap.Frontier.BalancedCountConcrete.balancedCount_eq_E3
#print axioms ArkLib.ProximityGap.Frontier.BalancedCountConcrete.exists_balancedCount
