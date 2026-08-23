/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MonomialWeylBridge

/-!
# The cyclic `m`-to-1 fiber count: discharging the `(BRIDGE)` hypotheses (#444)

`_MonomialWeylBridge.sum_pow_uniform_fiber` reduces the prize quantity to a single complete monomial
exponential sum
```
        Σ_{x ∈ F_p^*} e_p(b · x^m)  =  c · Σ_{y ∈ H} e_p(b · y)         (BRIDGE, conditional)
```
**conditionally** on two hypotheses: that the `m`-th power map is **uniformly `c`-to-1 onto a finset
`H`** (`hin`: every `y ∈ H` has exactly `c` preimages; `hout`: every `y ∉ H` has none). In
`_MonomialWeylBridge` those were carried as hypotheses, and the cyclic-group facts that make them
true (`H = μ_n`, `c = m` for `F_p^*`) were **documented, not proved**.

This file proves them. In a **finite cyclic group** `G` of order `N`, the `m`-th power map
`(· ^ m) = powMonoidHom m` is a group homomorphism whose
* range is the unique subgroup of order `N / gcd(N, m)` (Mathlib
  `IsCyclic.card_powMonoidHom_range`);
* kernel has order `gcd(N, m)` (Mathlib `IsCyclic.card_powMonoidHom_ker`);
* **every fiber over a point of the range has cardinality `= #ker = gcd(N, m)`** (a homomorphism's
  fibers are kernel-cosets, via `MonoidHom.card_fiber_eq_of_mem_range`);
* every fiber off the range is empty.

So with `H = (powMonoidHom m).range` and `c = gcd(N, m)` the two `(BRIDGE)` hypotheses hold
**unconditionally**, and `sum_pow_uniform_fiber` / `sum_pow_eq_const_smul` collapse with no side
condition. For the prize `G = F_p^*` (`N = p−1`, cyclic), `m = (p−1)/n` divides `N` so
`gcd(N, m) = m` and the range is the order-`n` subgroup `μ_n`; the corollary
`sum_pow_eq_smul_sum_range_of_isCyclic` is exactly `Σ_{x∈F_p^*} F(x^m) = m · Σ_{y∈μ_n} F y`, i.e.
`(BRIDGE)` with the hypotheses discharged.

**Honest scope.** This is the **structural / group-theoretic** half of `(BRIDGE)`: pure
finite-cyclic-group functoriality (field-universal, NON-MOMENT). It is NOT a CORE closure. By rule 3
the prize is thinness-essential and cannot be proved by a field-universal fiber-count. The remaining
gap is the **analytic** monomial Weil-sum bound `|Σ_x e_p(b x^m)| ≤ C√(p · log…)` (documented in
`_MonomialWeylBridge` as the open prize), which this file does not touch. Probe
`scripts/probes/probe_cyclic_power_fiber.py`: 0 fails / 25 over the prize regime (n=2^a, p≫n^3,
p≡1 mod n, incl. Fermat 257, 65537): uniform `m`-to-1 onto `μ_n`, `gcd(p−1, m) = m`. Issue #444.
-/

namespace ProximityGap.Frontier.CyclicPowerFiber

open Finset MonoidHom

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]

/-- The fiber of the `m`-th power map over `1` is exactly the kernel of `powMonoidHom m`, so its
cardinality is `gcd(#G, m)` (Mathlib `IsCyclic.card_powMonoidHom_ker`). -/
theorem card_fiber_one_eq_gcd (m : ℕ) :
    (univ.filter (fun x : G => x ^ m = 1)).card = (Nat.card G).gcd m := by
  rw [← Fintype.card_subtype (fun x : G => x ^ m = 1)]
  rw [← IsCyclic.card_powMonoidHom_ker (G := G) m, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  refine Equiv.subtypeEquivRight (fun x => ?_)
  rw [mem_ker, powMonoidHom_apply]

/-- **Uniform fiber count (the `m`-to-1 mechanism, unconditional over a finite cyclic group).**
Every value `y` in the **range** of the `m`-th power map has exactly `gcd(#G, m)` preimages; value
**off** the range has none. This discharges, unconditionally, the `hin`/`hout` hypotheses that
`_MonomialWeylBridge.sum_pow_uniform_fiber` carried abstractly. -/
theorem card_fiber_powMonoidHom (m : ℕ) (y : G) :
    (univ.filter (fun x : G => x ^ m = y)).card
      = if y ∈ (powMonoidHom m : G →* G).range then (Nat.card G).gcd m else 0 := by
  by_cases hy : y ∈ (powMonoidHom m : G →* G).range
  · rw [if_pos hy]
    have h1 : (1 : G) ∈ Set.range (powMonoidHom m : G →* G) := ⟨1, by simp⟩
    have hyr : y ∈ Set.range (powMonoidHom m : G →* G) := by
      rcases hy with ⟨x, hx⟩; exact ⟨x, hx⟩
    have hcong := MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom m : G →* G) hyr h1
    simp only [powMonoidHom_apply] at hcong
    calc (univ.filter (fun x : G => x ^ m = y)).card
        = (univ.filter (fun g : G => g ^ m = 1)).card := hcong
      _ = (Nat.card G).gcd m := card_fiber_one_eq_gcd m
  · rw [if_neg hy]
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact hy ⟨x, by simpa [powMonoidHom_apply] using hx⟩

variable {M : Type*} [AddCommMonoid M]

/-- **`(BRIDGE)`, hypotheses discharged.** Over a finite cyclic group `G`, the power-sum of any `F`
over the `m`-th powers collapses onto the **range** of the power map with the uniform multiplicity
`gcd(#G, m)`:
`Σ_x F(x^m) = gcd(#G, m) • Σ_{y ∈ range(·^m)} F y`. Composes `card_fiber_powMonoidHom` into
`_MonomialWeylBridge.sum_pow_eq_const_smul`, eliminating its `hin`/`hout` hypotheses. For
`G = F_p^*`, `m = (p−1)/n` (so `gcd(#G,m) = m`, `range = μ_n`) this is exactly `(BRIDGE)`:
`Σ_{x∈F_p^*} e_p(b·x^m) = m · Σ_{y∈μ_n} e_p(b·y) = m · η_b`. -/
theorem sum_pow_eq_smul_sum_range_of_isCyclic (m : ℕ) (F : G → M) :
    ∑ x, F (x ^ m)
      = (Nat.card G).gcd m • ∑ y ∈ (univ.filter
          (fun y : G => y ∈ (powMonoidHom m : G →* G).range)), F y := by
  refine ProximityGap.Frontier.MonomialWeylBridge.sum_pow_eq_const_smul m ((Nat.card G).gcd m) F
    (univ.filter (fun y : G => y ∈ (powMonoidHom m : G →* G).range)) ?_ ?_
  · intro y hy
    rw [mem_filter] at hy
    rw [card_fiber_powMonoidHom m y, if_pos hy.2]
  · intro y hy
    rw [mem_filter] at hy
    rw [card_fiber_powMonoidHom m y, if_neg (fun hc => hy ⟨mem_univ y, hc⟩)]

/-- The collapse multiplicity simplifies to `m` exactly when `m ∣ #G` (the prize case `m = (p−1)/n`,
`#G = p−1`): `Σ_x F(x^m) = m • Σ_{y ∈ range} F y`. -/
theorem sum_pow_eq_smul_sum_range_of_dvd (m : ℕ) (F : G → M) (hm : m ∣ Nat.card G) :
    ∑ x, F (x ^ m)
      = m • ∑ y ∈ (univ.filter
          (fun y : G => y ∈ (powMonoidHom m : G →* G).range)), F y := by
  rw [sum_pow_eq_smul_sum_range_of_isCyclic m F, Nat.gcd_eq_right hm]

end ProximityGap.Frontier.CyclicPowerFiber

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CyclicPowerFiber.card_fiber_one_eq_gcd
#print axioms ProximityGap.Frontier.CyclicPowerFiber.card_fiber_powMonoidHom
#print axioms ProximityGap.Frontier.CyclicPowerFiber.sum_pow_eq_smul_sum_range_of_isCyclic
#print axioms ProximityGap.Frontier.CyclicPowerFiber.sum_pow_eq_smul_sum_range_of_dvd
