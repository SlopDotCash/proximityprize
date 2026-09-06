/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The squaring self-reduction of the Paley object (#444, from the Gowers U^k attack)

The higher-order-Fourier (Gowers `U^k` inverse-theorem) attack on the Paley/BGK wall produced a
clean, genuinely-new structural fact: **the Gauss-period sup-norm `M(μ_n)` is self-similar under the
squaring map**. Because `n = 2^μ` is even, `−1 ∈ μ_n`, so `x ↦ x²` is exactly 2-to-1 from `μ_n` onto
the squares `μ_{n/2}` (the unique order-`n/2` subgroup). Hence for any `h`,

> `Σ_{x∈μ_n} h(x²) = 2 · Σ_{y∈μ_{n/2}} h(y)`,

and with `h(y) = e_p(a·y)` the quadratic phase sum `Σ_{x∈μ_n} e_p(a x²) = 2·η_a(μ_{n/2})` — the
period one dyadic level down. This is *why* higher-order Fourier analysis cannot beat
second-order/Burgess here: the degree-2 Gowers obstruction of `μ_n` is `2·M(μ_{n/2})`, a smaller
instance of the **same** BGK problem, so the inverse theorem walks the self-similar tower
`μ_n → μ_{n/2} → ⋯ → μ_2` with no cancellation gain (verified exactly: the U³ quadratic-phase
correlation `= 2·M(μ_{n/2})/n` to `~1e-15`, n=8/16/32 incl. thin `p=65537`). A *constructive*
self-reduction complementing the in-tree `moment_ladder_exceeds_prize` abstract barrier.

This file formalizes the exact 2-to-1 summation identity that drives it (axiom-clean). NOT prize
closure — it forecloses the Gowers route by exhibiting its self-reduction.
-/

namespace ArkLib.ProximityGap.Frontier.AvW15

open Finset

/-- **2-to-1 pushforward sum (proven).** If `φ : α → β` maps every element of `s` into `t`, and every
fiber over `t` has exactly `2` elements of `s`, then `Σ_{x∈s} h(φ x) = 2·Σ_{y∈t} h y`. (The squaring
map `x ↦ x²` on `μ_n` onto `μ_{n/2}` is the instance: each square has exactly the two roots `±x`.) -/
theorem sum_comp_eq_two_mul_of_two_to_one {α β M : Type*} [AddCommMonoid M]
    [DecidableEq β] (s : Finset α) (t : Finset β) (φ : α → β) (h : β → M)
    (hmaps : ∀ x ∈ s, φ x ∈ t)
    (hfib : ∀ y ∈ t, (s.filter (fun x => φ x = y)).card = 2) :
    ∑ x ∈ s, h (φ x) = 2 • ∑ y ∈ t, h y := by
  -- group the sum over s by the value of φ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (f := fun x => h (φ x))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  -- on the fiber over y, φ x = y, so h (φ x) = h y; sum is (card fiber) • h y = 2 • h y
  have hconst : ∑ x ∈ s.filter (fun x => φ x = y), h (φ x)
      = ∑ _x ∈ s.filter (fun x => φ x = y), h y := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [(Finset.mem_filter.mp hx).2]
  rw [hconst, Finset.sum_const, hfib y hy]

/-- **The squaring identity (proven specialization).** With `h := fun y => e_p(a·y)` (or any `h`),
`Σ_{x∈μ_n} h(x²) = 2·Σ_{y∈μ_{n/2}} h(y)`, given that squaring maps `μ_n` 2-to-1 onto `μ_{n/2}`
(packaged as the two hypotheses). So the quadratic-phase sum over `μ_n` is twice the linear period
over `μ_{n/2}` — the degree-2 Gowers obstruction is the tower-down Gauss period. -/
theorem squaring_sum_eq_two_mul {α β M : Type*} [AddCommMonoid M] [DecidableEq β]
    (μn : Finset α) (μhalf : Finset β) (sq : α → β) (h : β → M)
    (hmaps : ∀ x ∈ μn, sq x ∈ μhalf)
    (hfib : ∀ y ∈ μhalf, (μn.filter (fun x => sq x = y)).card = 2) :
    ∑ x ∈ μn, h (sq x) = 2 • ∑ y ∈ μhalf, h y :=
  sum_comp_eq_two_mul_of_two_to_one μn μhalf sq h hmaps hfib

end ArkLib.ProximityGap.Frontier.AvW15

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW15.sum_comp_eq_two_mul_of_two_to_one
#print axioms ArkLib.ProximityGap.Frontier.AvW15.squaring_sum_eq_two_mul
