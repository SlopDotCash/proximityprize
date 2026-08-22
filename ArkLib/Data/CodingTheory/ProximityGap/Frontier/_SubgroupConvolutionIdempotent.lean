/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Subgroup multiplicative-convolution idempotent — the ℓ-adic/Katz–Mellin monodromy NO-GO (#407/#444)

**Negative guardrail (exotic-math sweep).** This file proves the route *"use Katz's big-monodromy
/ Tannakian–Mellin theory on the convolution powers of the subgroup indicator `1_G` to force a
square-root cancellation of the dyadic Gauss periods"* is **structurally vacuous**: the
multiplicative-convolution powers of a finite subgroup's indicator do not GROW, they are a fixed
PROJECTOR (idempotent up to a scalar). It does **not** close the prize — the open `L^∞`
`√(log)` core (the BGK/Paley wall) survives untouched. See #407, #444, and the exotic sweep.

## The math

For a finite multiplicative subgroup `H ≤ Fˣ` of order `n = |H|`, the `r`-fold *multiplicative*
convolution of its indicator `1_H` evaluates to

> `(1_H)^{*r}(z) = #{ (x₁,…,x_r) ∈ Hʳ : x₁···x_r = z } = n^{r-1} · 1_H(z)`.

Reason (proved below as a **count identity**, which *is* the convolution value): if `z ∈ H` then
the first `r−1` coordinates are free and the last is forced `x_r = (x₁⋯x_{r-1})⁻¹·z ∈ H` (the
product of subgroup elements with `z` stays in `H` by closure), so the fibre has exactly `n^{r-1}`
points; if `z ∉ H` the fibre is empty (a product of `H`-elements can never leave `H`).

**Why this is a no-go for monodromy.** Katz's big-monodromy / Tannakian–Mellin machinery extracts
square-root cancellation from a family whose convolution powers exhibit `f^r/r!`-type generic-rank
GROWTH (the geometric monodromy group then fills out a large classical group). Here the convolution
object is a PROJECTOR: its "rank" (the support `H`, and the scalar `n^{r-1}`) is **constant in `r`**
— no growth. The geometric monodromy is the smallest torus `GL(1)^f`, and Katz big-monodromy cannot
apply to a subgroup indicator. So the Mellin/monodromy route produces nothing; the cancellation
question remains the open BGK `L^∞` core.

## Honesty (project §6)

This is a **NEGATIVE** brick: it establishes that the Mellin-monodromy route is *vacuous* (constant
rank ⇒ no big monodromy ⇒ no √-cancellation theorem). It does **NOT** prove `M(n) ≤ C√(n log q)`;
that `L^∞` factor is the open BGK/Paley-conjecture core. All theorems below are exact combinatorial
count identities, `sorry`-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## References
- [Katz] N. Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups* — Mellin/big-monodromy.
- [BGK] Bourgain–Glibichuk–Konyagin — the best proven incomplete-character-sum bound (the wall).
- #407, #444, the exotic-math sweep.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.SubgroupConvolutionIdempotent

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- The `r`-fold multiplicative-convolution fibre of the subgroup indicator over a subgroup
`H ≤ G`, evaluated at `z`: the count of `r`-tuples in `H` whose product is `z`. This Finset count
**is** the convolution value `(1_H)^{*r}(z)`. -/
noncomputable def convCount (H : Subgroup G) [Fintype H] (r : ℕ) (z : G) : ℕ :=
  (Finset.univ.filter (fun v : Fin r → H => (∏ i, (v i : G)) = z)).card

/-- **Off-support vanishing.** If `z ∉ H`, no tuple of `H`-elements multiplies to `z`
(a finite product of subgroup elements stays in `H`), so the convolution fibre is empty:
`(1_H)^{*r}(z) = 0`. This is the `1_H(z) = 0` half of the projector identity. -/
theorem convCount_eq_zero_of_not_mem (H : Subgroup G) [Fintype H] (r : ℕ) {z : G}
    (hz : z ∉ H) : convCount H r z = 0 := by
  classical
  rw [convCount, Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro v _ hv
  apply hz
  rw [← hv]
  exact Subgroup.prod_mem H (fun i _ => (v i).2)

/-- **The projector identity (general `r ≥ 1`), on-support value.** For `z ∈ H` and `r ≥ 1`,
`(1_H)^{*r}(z) = n^{r-1}` where `n = |H|`. The witnessing bijection: a tuple `v : Fin r → H` with
`∏ v i = z` is determined by its first `r−1` coordinates (the last is forced
`v_{r-1} = (∏_{i<r-1} v i)⁻¹·z ∈ H`), giving a bijection onto `Fin (r-1) → H`, whose cardinality is
`n^{r-1}`. The *rank/support is constant in `r`* — the idempotent (Tannakian projector) phenomenon
that voids the Mellin-monodromy route. -/
theorem convCount_eq_pow (H : Subgroup G) [Fintype H] {r : ℕ} (hr : 1 ≤ r) {z : G}
    (hz : z ∈ H) : convCount H r z = (Nat.card H) ^ (r - 1) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [convCount]
  -- Bijection: the filtered set ≃ (Fin m → H) via restriction to the first m coordinates.
  -- The forced last coordinate, as an element of H:
  let lastCoord : (Fin m → H) → H := fun w =>
    ⟨(∏ i, (w i : G))⁻¹ * z,
      Subgroup.mul_mem H (Subgroup.inv_mem H (Subgroup.prod_mem H (fun i _ => (w i).2))) hz⟩
  have hcard :
      (Finset.univ.filter (fun v : Fin (m + 1) → H => (∏ i, (v i : G)) = z)).card
        = (Finset.univ : Finset (Fin m → H)).card := by
    refine Finset.card_bij' (fun v _ i => v i.castSucc) (fun w _ => Fin.snoc w (lastCoord w))
      (fun v _ => Finset.mem_univ _) ?_ ?_ ?_
    · -- invFun maps into the filtered set
      intro w _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      -- product over Fin (m+1) of the snoc tuple = (∏ w) * (last) = (∏ w) * ((∏ w)⁻¹ * z) = z
      rw [Fin.prod_univ_castSucc]
      have h1 : ∀ i : Fin m, ((Fin.snoc w (lastCoord w) : Fin (m+1) → H) i.castSucc : G) = (w i : G) := by
        intro i; rw [Fin.snoc_castSucc]
      have h2 : ((Fin.snoc w (lastCoord w) : Fin (m+1) → H) (Fin.last m) : G)
          = (∏ i, (w i : G))⁻¹ * z := by rw [Fin.snoc_last]
      rw [h2]
      simp only [h1]
      group
    · -- left inverse: snoc (toFun v) (forced last) = v
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      funext i
      simp only
      refine Fin.lastCases ?_ (fun j => ?_) i
      · -- last coordinate is forced equal to v (last)
        simp only [Fin.snoc_last]
        apply Subtype.ext
        change (∏ j : Fin m, (v j.castSucc : G))⁻¹ * z = (v (Fin.last m) : G)
        have hprod : (∏ j : Fin m, (v j.castSucc : G)) * (v (Fin.last m) : G) = z := by
          rw [← Fin.prod_univ_castSucc (fun i => (v i : G))]; exact hv
        rw [← hprod]; group
      · simp only [Fin.snoc_castSucc]
    · -- right inverse: toFun (snoc w last) = w
      intro w _
      funext j
      simp only [Fin.snoc_castSucc]
  rw [hcard]
  rw [Finset.card_univ, Fintype.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The convolution power is a scalar multiple of the indicator (projector form).** Packaging
both halves: `(1_H)^{*r}(z) = n^{r-1}·1_H(z)` for all `z` and `r ≥ 1`, where `1_H(z) ∈ {0,1}`.
The scalar `n^{r-1}` is the only `r`-dependence; the *support and rank are constant in `r`*. This
is the exact statement that the multiplicative convolution of a subgroup indicator is an
idempotent (up to the `n^{r-1}` normalization), so no convolution-power growth is available to
feed Katz big-monodromy. -/
theorem convCount_eq_pow_mul_indicator (H : Subgroup G) [Fintype H] {r : ℕ} (hr : 1 ≤ r) (z : G)
    [Decidable (z ∈ H)] :
    convCount H r z = (Nat.card H) ^ (r - 1) * (if z ∈ H then 1 else 0) := by
  by_cases hz : z ∈ H
  · rw [if_pos hz, mul_one]; exact convCount_eq_pow H hr hz
  · rw [if_neg hz, mul_zero]; exact convCount_eq_zero_of_not_mem H r hz

/-- **Rank/support is constant in `r` (the no-growth core).** The support of the `r`-fold
convolution power — the set of `z` with nonzero fibre — is exactly `H`, *independent of `r ≥ 1`*.
Big-monodromy needs the convolution support/generic rank to GROW with `r`; here it is frozen at
`H`, so the geometric monodromy is the minimal torus and Katz's theorem is inapplicable. -/
theorem convCount_support_eq (H : Subgroup G) [Fintype H] {r : ℕ} (hr : 1 ≤ r) :
    {z : G | convCount H r z ≠ 0} = (H : Set G) := by
  classical
  ext z
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hz
    by_contra hzH
    exact hz (convCount_eq_zero_of_not_mem H r hzH)
  · intro hz
    rw [convCount_eq_pow H hr hz]
    exact pow_ne_zero _ (by
      have : 0 < Nat.card H := Nat.card_pos
      omega)

/-- **Idempotence in the literal sense, two consecutive ranks have the same support and a
`n`-fold scalar ratio.** For `r ≥ 1` and any `z ∈ H`, advancing the convolution order by one
multiplies the value by exactly `n = |H|`: `(1_H)^{*(r+1)}(z) = n · (1_H)^{*r}(z)`. A genuine
spectral object would change rank; the subgroup convolution only rescales — the projector
signature. -/
theorem convCount_succ_eq_card_mul (H : Subgroup G) [Fintype H] {r : ℕ} (hr : 1 ≤ r) {z : G}
    (hz : z ∈ H) : convCount H (r + 1) z = (Nat.card H) * convCount H r z := by
  rw [convCount_eq_pow H (by omega) hz, convCount_eq_pow H hr hz]
  have : r + 1 - 1 = (r - 1) + 1 := by omega
  rw [this, pow_succ]
  ring

/-! ### Explicit low-order witnesses (the projector phenomenon, concretely).

These specialize the general identity to `r = 2, 3` so the constant-rank / `n^{r-1}`-scaling is
visible without unfolding the general bijection: `#{(x,y)∈H² : xy=z} = n` and
`#{(x,y,w)∈H³ : xyw=z} = n²` for `z ∈ H`. -/

/-- `r = 2`: `#{(x,y) ∈ H² : x·y = z} = |H|` for `z ∈ H`. The fibre is `n^{2-1} = n`. -/
theorem convCount_two (H : Subgroup G) [Fintype H] {z : G} (hz : z ∈ H) :
    convCount H 2 z = Nat.card H := by
  rw [convCount_eq_pow H (by norm_num) hz]; simp

/-- `r = 3`: `#{(x,y,w) ∈ H³ : x·y·w = z} = |H|²` for `z ∈ H`. The fibre is `n^{3-1} = n²`. -/
theorem convCount_three (H : Subgroup G) [Fintype H] {z : G} (hz : z ∈ H) :
    convCount H 3 z = (Nat.card H) ^ 2 := by
  rw [convCount_eq_pow H (by norm_num) hz]

end ProximityGap.Frontier.SubgroupConvolutionIdempotent

/-! ## Axiom audit — kernel-clean (`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`). -/
#print axioms ProximityGap.Frontier.SubgroupConvolutionIdempotent.convCount_eq_zero_of_not_mem
#print axioms ProximityGap.Frontier.SubgroupConvolutionIdempotent.convCount_eq_pow
#print axioms ProximityGap.Frontier.SubgroupConvolutionIdempotent.convCount_eq_pow_mul_indicator
#print axioms ProximityGap.Frontier.SubgroupConvolutionIdempotent.convCount_support_eq
#print axioms ProximityGap.Frontier.SubgroupConvolutionIdempotent.convCount_succ_eq_card_mul
#print axioms ProximityGap.Frontier.SubgroupConvolutionIdempotent.convCount_two
#print axioms ProximityGap.Frontier.SubgroupConvolutionIdempotent.convCount_three
