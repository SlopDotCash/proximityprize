/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# G302: the only common bounded-order sponsor normal is order seven, and it is sign-decoupled

G297 proves that the weighted kernels

```text
W_a(t) = #{(y,z) in G^2 : a*y-z=t}
```

are constant on coefficient cosets `aG`, while their centered alignments still have prime- and
rank-dependent signs. After G301 closes the uniform quotient average, the smallest remaining
coefficient-axis proposal is a generator-independent bounded-order character normal shared by both
sponsor quotient groups.

Their exact orders are

```text
m1 = 2^128 + 192,
 m2 = 2^129 + 13,
```

and `gcd(m1,m2)=7`. Hence every nonprincipal character order common to both sponsors is exactly
seven. The canonical generator-independent primitive-order-seven trace has Ramanujan weight

```text
c_7(j) = 6  if 7 divides j,
         -1 otherwise.
```

The weight is invariant under every change of cyclic generator because multiplication by a unit
modulo seven preserves divisibility by seven.

The exact integer probe `scripts/probes/g302_common_order7_normal_nogo.py` evaluates

```text
L7(r) = sum_j c_7(j) A_{g^j}(R_r)
```

on 27 proper dyadic subgroup cells and both live ranks. Agreement with the coefficient-two target
is exactly `27/54`, and all four sign quadrants occur. In particular, on the single subgroup
`mu_16 <= F_113^*`, the mismatch reverses at adjacent ranks:

```text
r=5: A_2=+1,727,120, L7=-20,424,976;
r=6: A_2=   -77,440, L7= +1,048,640.
```

Thus the unique common fixed-order, generator-independent nonprincipal normal carries no uniform
sign information. This does not exclude a sponsor-specific order or a full-family Gross--Koblitz
normal chosen independently before evaluation. It closes only the common bounded-order shortcut.
FS15--FS18 remain fixed-depth almost-all-prime magnitude statements; they do not select either
sponsor or the row-labelled sign at the in-window production depth.

This is an axiom-clean sponsor-arithmetic and exact-census no-go, not a sponsor estimate or prize
closure. CORE remains open / on-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G302CommonOrderSevenNormalNoGo

/-- Quotient order at the first certified sponsor prime. -/
def sponsorOrderOne : ℕ := 2 ^ 128 + 192

/-- Quotient order at the second certified sponsor prime. -/
def sponsorOrderTwo : ℕ := 2 ^ 129 + 13

/-- The primitive-order-seven Ramanujan weight. -/
def ramanujanWeightSeven (j : ℕ) : ℤ := if 7 ∣ j then 6 else -1

/-- The sponsor quotient orders have greatest common divisor exactly seven. -/
theorem sponsor_orders_gcd : Nat.gcd sponsorOrderOne sponsorOrderTwo = 7 := by
  norm_num [sponsorOrderOne, sponsorOrderTwo, Nat.gcd]

/-- **Unique common nonprincipal fixed order.** Every common divisor of the two sponsor quotient
orders that is at least two is seven. -/
theorem common_nonprincipal_order_eq_seven {d : ℕ} (hd : 2 ≤ d)
    (h1 : d ∣ sponsorOrderOne) (h2 : d ∣ sponsorOrderTwo) : d = 7 := by
  have hdiv : d ∣ Nat.gcd sponsorOrderOne sponsorOrderTwo := Nat.dvd_gcd h1 h2
  rw [sponsor_orders_gcd] at hdiv
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdiv with h | h
  · omega
  · exact h

/-- The order-seven trace is independent of the chosen cyclic generator. Multiplication by a unit
modulo seven preserves the two Ramanujan weight classes. -/
theorem ramanujanWeightSeven_mul_of_coprime (u j : ℕ) (hu : Nat.Coprime u 7) :
    ramanujanWeightSeven (u * j) = ramanujanWeightSeven j := by
  unfold ramanujanWeightSeven
  by_cases hj : 7 ∣ j
  · have hmul : 7 ∣ u * j := dvd_mul_of_dvd_right hj u
    simp [hj, hmul]
  · have hu7 : ¬ 7 ∣ u := by
      intro h
      have hdiv : 7 ∣ Nat.gcd u 7 := Nat.dvd_gcd h (dvd_refl 7)
      rw [hu] at hdiv
      norm_num at hdiv
    have hmul : ¬ 7 ∣ u * j := by
      intro h
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h with h | h
      · exact hu7 h
      · exact hj h
    simp [hj, hmul]

/-- One exact target/normal comparison from the committed G302 integer census. -/
structure OrderSevenCell where
  p : Nat
  n : Nat
  m : Nat
  r : Nat
  target : Int
  normal : Int
  deriving DecidableEq, Repr

/-- Negative target and negative order-seven normal. -/
def cell8p113r5 : OrderSevenCell :=
  { p := 113, n := 8, m := 14, r := 5, target := -13128, normal := -364312 }

/-- Negative target and positive order-seven normal. -/
def cell16p113r6 : OrderSevenCell :=
  { p := 113, n := 16, m := 7, r := 6, target := -77440, normal := 1048640 }

/-- Positive target and negative order-seven normal. -/
def cell8p337r5 : OrderSevenCell :=
  { p := 337, n := 8, m := 42, r := 5, target := 282928, normal := -5712824 }

/-- Positive target and positive order-seven normal. -/
def cell8p281r5 : OrderSevenCell :=
  { p := 281, n := 8, m := 35, r := 5, target := 189728, normal := 413632 }

/-- Rank-five comparison on `mu_16 <= F_113^*`. -/
def cell16p113r5 : OrderSevenCell :=
  { p := 113, n := 16, m := 7, r := 5, target := 1727120, normal := -20424976 }

/-- The canonical common-order normal realizes all four sign quadrants against the target. -/
theorem orderSeven_all_four_sign_quadrants :
    (cell8p113r5.target < 0 ∧ cell8p113r5.normal < 0) ∧
    (cell16p113r6.target < 0 ∧ 0 < cell16p113r6.normal) ∧
    (0 < cell8p337r5.target ∧ cell8p337r5.normal < 0) ∧
    (0 < cell8p281r5.target ∧ 0 < cell8p281r5.normal) := by
  decide

/-- On one fixed prime and proper dyadic subgroup, adjacent ranks reverse the mismatch in both
directions. Thus neither sign of `L7` supplies a rank-uniform implication for the target. -/
theorem same_subgroup_adjacent_rank_mismatch_reversal :
    cell16p113r5.p = cell16p113r6.p ∧
    cell16p113r5.n = cell16p113r6.n ∧
    cell16p113r5.m = cell16p113r6.m ∧
    cell16p113r5.r + 1 = cell16p113r6.r ∧
    0 < cell16p113r5.target ∧ cell16p113r5.normal < 0 ∧
    cell16p113r6.target < 0 ∧ 0 < cell16p113r6.normal := by
  decide

/-- Packaged exact no-go: the unique common nonprincipal bounded order is seven, and its canonical
primitive trace disagrees with the coefficient-two target in both polarities on adjacent ranks. -/
theorem common_bounded_order_normal_does_not_track_target :
    Nat.gcd sponsorOrderOne sponsorOrderTwo = 7 ∧
    (0 < cell16p113r5.target ∧ cell16p113r5.normal < 0) ∧
    (cell16p113r6.target < 0 ∧ 0 < cell16p113r6.normal) := by
  exact ⟨sponsor_orders_gcd,
    ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩⟩

#print axioms sponsor_orders_gcd
#print axioms common_nonprincipal_order_eq_seven
#print axioms ramanujanWeightSeven_mul_of_coprime
#print axioms orderSeven_all_four_sign_quadrants
#print axioms same_subgroup_adjacent_rank_mismatch_reversal
#print axioms common_bounded_order_normal_does_not_track_target

end ArkLib.ProximityGap.Frontier.G302CommonOrderSevenNormalNoGo
