/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CyclicPowerFiber

/-!
# The `m`-th power range IS the `n`-torsion subgroup `μ_n` (#444)

`_CyclicPowerFiber.sum_pow_eq_smul_sum_range_of_dvd` discharges the `(BRIDGE)` collapse
`Σ_x F(x^m) = m • Σ_{y ∈ range(·^m)} F y` over a finite cyclic group. But it lands on the **abstract
range** `range(powMonoidHom m)`. The prize object is the **explicit `n`-th roots of unity**
`μ_n = {y : y^n = 1}` (the `n` points whose Salem–Zygmund equidistribution is the prize). The
identification `range(·^m) = μ_n` is documented in `_MonomialWeylBridge`/`_CyclicPowerFiber` as
PROSE ("`m = (p−1)/n` divides `N` so the range is the order-`n` subgroup `μ_n`"), never a theorem.

This file proves it. In a finite cyclic group `G` of order `N` with `m·n = N`:
```
        range(x ↦ x^m)  =  { y : y^n = 1 }  =  μ_n,      and  #μ_n = n.                (RANGE=μ_n)
```
Both directions are elementary once cardinalities are pinned:
* `⊆`: if `y = x^m` then `y^n = x^{mn} = x^N = 1` (`pow_card_eq_one`).
* `#{y : y^n = 1} = gcd(N, n) = n` (Mathlib `IsCyclic.card_powMonoidHom_ker`, the kernel of `·^n` is
  exactly the `n`-torsion; reused via `_CyclicPowerFiber.card_fiber_one_eq_gcd`), and
  `#range(·^m) = N / gcd(N, m) = N / m = n` (`IsCyclic.card_powMonoidHom_range`).
* equal finite cardinalities + one ⊆-containment ⟹ set equality (`Finset.eq_of_subset_of_card_le`).

Composing `(RANGE=μ_n)` into `_CyclicPowerFiber.sum_pow_eq_smul_sum_range_of_dvd` lands `(BRIDGE)`
on the **literal** `n`-torsion finset:
```
        Σ_x F(x^m)  =  m • Σ_{y : y^n = 1} F y,                              (BRIDGE on μ_n)
```
i.e. for `G = F_p^*`, `m = (p−1)/n`, `F y = e_p(b·y)`: `Σ_{x∈F_p^*} e_p(b·x^m) = m · η_b`, with
`η_b` summed over the **actual** `n`-th roots of unity `μ_n`, not an abstract range.

**Honest scope.** Pure finite-cyclic-group structure (field-universal, NON-MOMENT). NOT a CORE
closure; by rule 3 the thinness-essential prize cannot be proved by a field-universal range/torsion
identity. Its value is that it pins `(BRIDGE)` onto the explicit prize set `μ_n`, so downstream
monomial-Weyl-sum work reasons about the literal roots of unity. The open analytic prize (the
monomial Weil-sum bound) is
untouched. Probe `scripts/probes/probe_range_eq_torsion.py`: 0 fails / 107 over the prize regime
(n=2^a, p ≡ 1 mod n, p ≫ n^3, incl. Fermat 257, 65537): `range(·^m) = {y : y^n = 1}`, `#range = n`.
Issue #444.
-/

namespace ProximityGap.Frontier.CyclicPowerRangeTorsion

open Finset MonoidHom

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]

/-- The `n`-torsion finset `{y : y^n = 1}` of a finite cyclic group has cardinality `gcd(#G, n)`.
This is `_CyclicPowerFiber.card_fiber_one_eq_gcd` (the kernel of `·^n` is exactly the fiber over
`1`), restated as the `n`-torsion count. -/
theorem card_torsion_eq_gcd (n : ℕ) :
    (univ.filter (fun y : G => y ^ n = 1)).card = (Nat.card G).gcd n :=
  ProximityGap.Frontier.CyclicPowerFiber.card_fiber_one_eq_gcd n

/-- When `n ∣ #G`, the `n`-torsion finset has cardinality exactly `n` (`gcd(#G, n) = n`). For the
prize `n ∣ p−1` this is `#μ_n = n`. -/
theorem card_torsion_eq_of_dvd (n : ℕ) (hn : n ∣ Nat.card G) :
    (univ.filter (fun y : G => y ^ n = 1)).card = n := by
  rw [card_torsion_eq_gcd n, Nat.gcd_eq_right hn]

/-- **`(RANGE = μ_n)`: the `m`-th power range IS the `n`-torsion finset**, for `m·n = #G`.
The abstract `range(powMonoidHom m)` (the finset on which `(BRIDGE)` collapses) equals the explicit
`n`-th-roots-of-unity finset `{y : y^n = 1} = μ_n`. -/
theorem range_eq_torsion (m n : ℕ) (hmn : m * n = Nat.card G) :
    (univ.filter (fun y : G => y ∈ (powMonoidHom m : G →* G).range))
      = (univ.filter (fun y : G => y ^ n = 1)) := by
  have hmd : m ∣ Nat.card G := ⟨n, hmn.symm⟩
  have hnd : n ∣ Nat.card G := ⟨m, by rw [← hmn]; ring⟩
  -- range ⊆ torsion: y = x^m ⟹ y^n = x^(mn) = x^N = 1.
  have hsub : (univ.filter (fun y : G => y ∈ (powMonoidHom m : G →* G).range))
      ⊆ (univ.filter (fun y : G => y ^ n = 1)) := by
    intro y hy
    rw [mem_filter] at hy ⊢
    refine ⟨mem_univ y, ?_⟩
    obtain ⟨x, hx⟩ := hy.2
    rw [powMonoidHom_apply] at hx
    rw [← hx, ← pow_mul, hmn, pow_card_eq_one']
  -- cardinalities: #range = N/gcd(N,m) = N/m = n; #torsion = gcd(N,n) = n.
  have hcr : (univ.filter (fun y : G => y ∈ (powMonoidHom m : G →* G).range)).card = n := by
    have hrange : (univ.filter (fun y : G => y ∈ (powMonoidHom m : G →* G).range)).card
        = Nat.card (powMonoidHom m : G →* G).range := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hNpos : 0 < Nat.card G := Nat.card_pos
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, zero_mul] at hmn; omega
      · exact h0
    rw [hrange, IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right hmd]
    rw [← hmn, Nat.mul_div_cancel_left n hmpos]
  have hct : (univ.filter (fun y : G => y ^ n = 1)).card = n := card_torsion_eq_of_dvd n hnd
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcr, hct])

/-- **`(BRIDGE)` on the explicit `n`-torsion `μ_n`.** The power-sum collapses onto the literal
`n`-th roots of unity: `Σ_x F(x^m) = m • Σ_{y : y^n = 1} F y` for `m·n = #G`. Composes
`range_eq_torsion`
into `_CyclicPowerFiber.sum_pow_eq_smul_sum_range_of_dvd`. For `G = F_p^*`, `F y = e_p(b·y)`:
`Σ_{x∈F_p^*} e_p(b·x^m) = m · Σ_{y∈μ_n} e_p(b·y) = m · η_b`. -/
theorem sum_pow_eq_smul_sum_torsion {M : Type*} [AddCommMonoid M] (m n : ℕ) (F : G → M)
    (hmn : m * n = Nat.card G) :
    ∑ x, F (x ^ m) = m • ∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F y := by
  have hmd : m ∣ Nat.card G := ⟨n, hmn.symm⟩
  rw [ProximityGap.Frontier.CyclicPowerFiber.sum_pow_eq_smul_sum_range_of_dvd m F hmd,
    range_eq_torsion m n hmn]

end ProximityGap.Frontier.CyclicPowerRangeTorsion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CyclicPowerRangeTorsion.card_torsion_eq_gcd
#print axioms ProximityGap.Frontier.CyclicPowerRangeTorsion.card_torsion_eq_of_dvd
#print axioms ProximityGap.Frontier.CyclicPowerRangeTorsion.range_eq_torsion
#print axioms ProximityGap.Frontier.CyclicPowerRangeTorsion.sum_pow_eq_smul_sum_torsion
