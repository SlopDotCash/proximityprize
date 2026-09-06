/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The exact r-th period moment ↔ additive zero-sum census bridge (#407)

This lands the EXACT identity tying the `r`-th power-moment of the Gauss periods
`η_b = Σ_{y∈G} ψ(by)` to the additive **zero-sum census** of `G`:

> `Σ_{b∈F} (η_b)^r = |F| · #{(y₁,…,y_r) ∈ Gʳ : y₁ + ⋯ + y_r = 0}`.

It generalizes the first-moment vanishing (`sum_eta_eq_zero`: `r = 1`) and the Parseval second
moment to ALL orders, via the SAME character-orthogonality mechanism (`AddChar.sum_mulShift`):
expand the `r`-th power into an `r`-fold sum over `Gʳ` (`Finset.sum_pow'`), swap the `b`-sum
inside, and collapse each tuple by orthogonality — the inner `Σ_b ψ(b · Σyᵢ)` is `|F|` when the
tuple sums to `0` and `0` otherwise.

## Why this is the deep-Sidon / odd-moment bridge (probe-validated, #407)

Probes (`probe_407_odd_moment_thinness.py`, `probe_407_oddmom_scaling.py`, `probe_407_Wr_odd_depth.py`,
`probe_407_depth_vs_M.py`) confirmed numerically (machine precision, proper thin subgroups
`μ_n ⊊ F_p^*`, multiple primes) that:

* `A_r := Σ_{b≠0} η_b^r = |F|·W_r − n^r` where `W_r` is the zero-sum census count and `n = |G|`
  (subtracting the `b = 0` term `η_0^r = n^r`). This file proves the un-subtracted identity exactly.
* For odd `r` **to the Sidon depth** (where `W_r = 0`), `A_r = −n^r` is RIGID and `p`-independent —
  so the apparent "signed sqrt-cancellation" `A_r/(p·M^r) → 0` is a NORMALIZATION ARTIFACT, NOT a
  proof handle for `M = max_{b≠0}‖η_b‖`. (Refutes odd-moment-as-lever; cf. the rigid-equation NC3
  no-go in `DISPROOF_LOG.md`.)
* The genuine thinness invariant is the **onset depth** `d_odd(n,p)` (first odd `r` with `W_r > 0`),
  which GROWS strictly with thinness `β = log_n p` (n=16: `r=7 → 9 → 11 → none` as `β: 2.45 → 4.6`).
  `probe_407_depth_vs_M.py` then showed this depth does NOT control the normalized sup
  `M/√(n·log(p/n))` (flat ~1.1–1.3 across `d_odd = 5…13`) ⇒ depth is a true thinness invariant but
  **non-proving** for the sup-norm at accessible scale. Honest mapped wall; this file lands the exact
  algebraic substrate (the moment↔census bridge) that those probes used, axiom-clean.

Issue #407. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.GaussPeriodMomentCensus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Helper: a primitive additive character carries a finite sum to the product of its values
(`ψ(Σ yᵢ) = Π ψ(yᵢ)`), by `map_add_eq_mul`. -/
theorem addChar_map_sum (ψ : AddChar F ℂ) {ι : Type*} (s : Finset ι) (g : ι → F) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, map_add_eq_mul, ih]

/-- The additive **zero-sum census** of `G` at depth `r`: the number of `r`-tuples
`(y₀,…,y_{r-1}) ∈ Gʳ` (packaged as functions `Fin r → F` valued in `G`) whose coordinates
sum to `0`. -/
noncomputable def zeroSumCensus (G : Finset F) (r : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => G)).filter
    (fun f : Fin r → F => (∑ i, f i) = 0)).card

/-- **The r-th period moment ↔ zero-sum census bridge.**
`Σ_{b∈F} (η_b)^r = |F| · #{(y₁,…,y_r) ∈ Gʳ : Σ yᵢ = 0}`, for any subgroup-or-set `G ⊆ F`
and primitive additive character `ψ`. Pure character orthogonality, all orders `r`. -/
theorem sum_eta_pow_eq_card_mul_zeroSumCensus
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b : F, (eta ψ G b) ^ r
      = (Fintype.card F : ℂ) * (zeroSumCensus G r : ℂ) := by
  -- Expand η_b^r as an r-fold sum over Gʳ via `Finset.sum_pow'`.
  have hpow : ∀ b : F, (eta ψ G b) ^ r
      = ∑ f ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * (∑ i, f i)) := by
    intro b
    simp only [eta]
    rw [Finset.sum_pow']
    apply Finset.sum_congr rfl
    intro f _
    -- ψ (b * Σ_i f i) = Π_i ψ (b * f i)
    rw [Finset.mul_sum, addChar_map_sum]
  -- Swap the b-sum inside and collapse by orthogonality.
  calc ∑ b : F, (eta ψ G b) ^ r
      = ∑ b : F, ∑ f ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * (∑ i, f i)) := by
        exact Finset.sum_congr rfl (fun b _ => hpow b)
    _ = ∑ f ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ b : F, ψ (b * (∑ i, f i)) := by
        rw [Finset.sum_comm]
    _ = ∑ f ∈ Fintype.piFinset (fun _ : Fin r => G),
          (if (∑ i, f i) = 0 then (Fintype.card F : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro f _
        have h := AddChar.sum_mulShift (∑ i, f i) hψ
        rw [h]
        by_cases hs : (∑ i, f i) = 0
        · simp [hs]
        · simp [hs]
    _ = (Fintype.card F : ℂ) * (zeroSumCensus G r : ℂ) := by
        rw [← Finset.sum_filter, Finset.sum_const, zeroSumCensus, nsmul_eq_mul, mul_comm]

/-- The principal (`b = 0`) period is the cardinality: `η_0 = Σ_{y∈G} ψ(0) = |G|`. -/
theorem eta_zero_eq_card {ψ : AddChar F ℂ} (G : Finset F) :
    eta ψ G 0 = (G.card : ℂ) := by
  simp only [eta, zero_mul, map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The DELETED (b ≠ 0) period-moment ↔ census bridge** — the prize-relevant form.
Deleting the isolated principal term `η_0^r = (|G|)^r` from the full-`F` identity gives
`Σ_{b≠0} (η_b)^r = |F| · zeroSumCensus G r − (|G|)^r`. This is the EXACT algebraic substrate
`A_r = |F|·W_r − n^r` that every odd-`r` deep-signed probe (#407, #444) and the campaign's ODD-`r`
signed-cancellation map use; the parent file proved only the un-deleted full-`F` identity, leaving
this (the actually-used object) in prose. Pure `Fintype.sum_eq_sum_compl_add` on the singleton `{0}`. -/
theorem sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ (Finset.univ.erase (0 : F)), (eta ψ G b) ^ r
      = (Fintype.card F : ℂ) * (zeroSumCensus G r : ℂ) - (G.card : ℂ) ^ r := by
  have hfull := sum_eta_pow_eq_card_mul_zeroSumCensus hψ G r
  -- Split the full sum over `F` into the `b = 0` term plus the sum over `b ≠ 0`.
  have hsplit : ∑ b : F, (eta ψ G b) ^ r
      = (eta ψ G 0) ^ r + ∑ b ∈ (Finset.univ.erase (0 : F)), (eta ψ G b) ^ r := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F))]
  rw [hsplit, eta_zero_eq_card] at hfull
  -- hfull : |F| * census = (G.card)^r + S  ⇒  S = |F| * census - (G.card)^r
  linear_combination hfull

/-- **Rigidity at vanishing census** (the deep-Sidon / odd-`r` rigid value, kernel-anchored).
Whenever the additive zero-sum census vanishes (`zeroSumCensus G r = 0` — e.g. for odd `r` below the
Sidon onset depth `d_odd`), the deleted period-moment is the `p`-INDEPENDENT rigid value
`Σ_{b≠0} η_b^r = −(|G|)^r`. This is the exact algebraic content of the campaign's odd-`r`
sign-rigidity finding (`A_r = −n^r`, negative + magnitude-rigid in the wraparound-free regime): the
apparent "signed √-cancellation" `A_r/(p·M^r)→0` is a normalization artifact of a RIGID equation, not
a proof handle for the sup-norm. Immediate from the deleted census bridge with the census term zero. -/
theorem sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hcensus : zeroSumCensus G r = 0) :
    ∑ b ∈ (Finset.univ.erase (0 : F)), (eta ψ G b) ^ r = -((G.card : ℂ) ^ r) := by
  rw [sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub hψ G r, hcensus]
  simp

end ProximityGap.Frontier.GaussPeriodMomentCensus

/-! ## Axiom audit -/
open ProximityGap.Frontier.GaussPeriodMomentCensus in
#print axioms sum_eta_pow_eq_card_mul_zeroSumCensus
open ProximityGap.Frontier.GaussPeriodMomentCensus in
#print axioms sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub
open ProximityGap.Frontier.GaussPeriodMomentCensus in
#print axioms sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero
