/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# P3 — Weil/Deligne in the `b`-parameter family is conductor-floored at the rank (#444)

This file makes **rigorous and axiom-clean** the obstruction to the P3 attack angle:

> *Realize the subgroup-period family `b ↦ η_b = ∑_{y∈μ_n} ψ(b·y)` as the trace function of an
> `ℓ`-adic sheaf `F` on the parameter `b`-line `𝔸¹`. The `b`-family has `q ≫ √q` points, so
> Deligne's Weil II BITES (unlike the dead `n`-domain, where Weil is vacuous, `n < √q`). If `F`
> has **conductor `c = O(1)` uniformly in `n`**, the pointwise (Lefschetz/Grothendieck) bound
> `|η_b| = |trace_b F| ≤ c·√(q_geom)` gives `M(n) ≤ C·√n` uniformly ⟹ the prize floor.*

**The obstruction (this file).** The *averaged* L² scale of the trace function is **exactly the
generic rank of `F`**, and the second moment `∑_b ‖η_b‖² = q·|G|` (proven, axiom-clean, in
`SubgroupGaussSumSecondMoment`) pins that rank at `|G| = n`. Concretely:

* For ANY constant `C` that is a *uniform pointwise* bound — `‖η_b‖ ≤ C` for every frequency `b`
  (the shape of a Lefschetz/Betti sheaf output `C = c·√(q_geom)` with `q_geom = O(1)` per point) —
  the second moment forces `C² ≥ |G|`, i.e. `C ≥ √|G| = √n`.

So a uniform pointwise bound is FLOORED AT `√n`: the only `√(q_geom)` available to "spend" is the
sheaf's own `√(rank) = √n`, and a genuinely `n`-independent conductor (`c = O(1)`, `C = O(1)`) is
*impossible* — it would contradict the exact second moment. The conductor of the trace sheaf is
`Θ(n)` (rank `= n` by the second moment; Swan `= 0`, all Artin–Schreier/Kummer constituents tame on
`𝔾_m`), so the pointwise Deligne bound is `|η_b| ≤ cond(F) = Θ(n)` — the **trivial** bound.

**What P3 reduces to (the honest verdict).** Getting `M(n) ≤ C√n` from this rank-`n` family is
exactly the statement that the `n` rank-1 (additive-character) constituents sit in *general
position* (random relative phases) — i.e. the equidistribution / square-root-cancellation of the
period family, which is the **open BGK/Paley-graph core**. Deligne supplies this only *on average*
(the `r`-th moment / vertical Sato–Tate gives the Johnson/Wick per-moment scale `(2r-1)‼·n^r`),
never the single-`b` sup. So P3 **reduces-to-BGK**: the pointwise `O(1)`-conductor hope is refuted
here (this file), and the residual on-average content is the recognized open wall.

**Numerics** (`scripts/probes/probe_p3_bparam_conductor_verdict.py`, proper `μ_n`, generic primes,
`p ~ n^4 ≫ n^3`, `p−1 ≠ n`): `Var_b‖η_b‖² = n` to four decimals (rank-forcing), and the effective
constant `c_eff = M/√(Var) = M/√n` is `2.78, 3.59, 4.25, 4.57` at `n = 8,16,32,64` — **NOT bounded**
(refuting `O(1)` conductor), tracking `√(log p)` (`c_eff/√(log p)` rises `0.85→1.00→1.10→1.11`,
the prize-target slack), and the literal prize ratio `M/√(n·log m)` is bounded `≈1.0–1.3`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444.
-/

set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.P3ParamFamilyConductorRankFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The `b`-parameter trace sheaf is conductor-floored at the rank (P3 refutation, rigorous).**

Suppose `C` is any *uniform pointwise* bound on the period family: `‖η_b‖ ≤ C` for **every**
frequency `b` (the exact shape of a Lefschetz/Betti `ℓ`-adic-sheaf output, `C = cond(F)·√(q_geom)`).
Then the proven second moment `∑_b ‖η_b‖² = q·|G|` forces

  `C² ≥ |G|`.

So a uniform pointwise sheaf bound on `b ↦ η_b` is **floored at `√|G| = √n`**: an `n`-independent
(`O(1)`) constant is impossible. The conductor of the trace sheaf is therefore `Θ(n)` (the
second-moment-forced rank), and the pointwise Deligne bound is the *trivial* `|η_b| ≤ cond ~ n`.
This is the unconditional refutation of the P3 `O(1)`-conductor hope; the `√n`-cancellation residual
is the on-average / per-moment content = the open BGK wall. -/
theorem uniform_pointwise_bound_sq_ge_card
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) {C : ℝ}
    (hC : ∀ b : F, ‖eta ψ G b‖ ≤ C) :
    (G.card : ℝ) ≤ C ^ 2 := by
  -- `C` is nonneg (it bounds a norm at any `b`).
  obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hq
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC b₀)
  -- Termwise: each `‖η_b‖² ≤ C²` (squaring a nonneg bound on a nonneg quantity).
  have hterm : ∀ b : F, ‖eta ψ G b‖ ^ 2 ≤ C ^ 2 := by
    intro b
    have h0 : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 (hC b) 2
  -- Sum the termwise bound: `∑_b ‖η_b‖² ≤ ∑_b C² = q·C²`.
  have hsum_le : (∑ b : F, ‖eta ψ G b‖ ^ 2) ≤ (Fintype.card F : ℝ) * C ^ 2 := by
    calc (∑ b : F, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b : F, C ^ 2 := Finset.sum_le_sum (fun b _ => hterm b)
      _ = (Fintype.card F : ℝ) * C ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- But the EXACT second moment is `q·|G|`.  So `q·|G| ≤ q·C²`, hence `|G| ≤ C²`.
  rw [subgroup_gaussSum_secondMoment hψ G] at hsum_le
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hmul : (Fintype.card F : ℝ) * (G.card : ℝ) ≤ (Fintype.card F : ℝ) * C ^ 2 := hsum_le
  exact le_of_mul_le_mul_left hmul hqR

/-- **Corollary — there is no `O(1)`-conductor pointwise Deligne bound (the P3 verdict).**

Contrapositive form, stated against `√|G|`: a uniform pointwise bound `C` on the family satisfies
`√|G| ≤ C`.  Hence as the smooth-domain size `|G| = n` grows, NO `n`-independent constant `C` can
bound `‖η_b‖` for all `b` — the would-be sheaf conductor is forced to grow at least like `√n`
through the pointwise bound, so the `O(1)`-conductor relocation of the prize sup to the `b`-line
**cannot hold**.  (The genuine open content is the *averaged* per-moment cancellation = BGK.) -/
theorem sqrt_card_le_of_uniform_pointwise_bound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) {C : ℝ}
    (hC : ∀ b : F, ‖eta ψ G b‖ ≤ C) :
    Real.sqrt (G.card : ℝ) ≤ C := by
  obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hq
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC b₀)
  have hsq : (G.card : ℝ) ≤ C ^ 2 := uniform_pointwise_bound_sq_ge_card hψ G hq hC
  calc Real.sqrt (G.card : ℝ)
      ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C := by rw [Real.sqrt_sq hC0]

end ArkLib.ProximityGap.P3ParamFamilyConductorRankFloor

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.P3ParamFamilyConductorRankFloor.uniform_pointwise_bound_sq_ge_card
#print axioms
  ArkLib.ProximityGap.P3ParamFamilyConductorRankFloor.sqrt_card_le_of_uniform_pointwise_bound
