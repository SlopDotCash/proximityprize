/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The moment-ladder tail floor (#444) — and why it converges to (but never reaches) Gaussian

`_AvW9` proved the Parseval floor `#{b : ‖η_b‖² > K·n} ≤ q/K` (a `1/K` suppression, from the 2nd
moment). This file proves the **whole ladder**: the `r`-th moment gives a `1/K^r` suppression. The
abstract Markov-at-power-`r` inequality, specialized to `a_b = ‖η_b‖²` with the `2r`-th period moment
`Σ_b ‖η_b‖^{2r} ≤ Cᵣ·q·n^r` (the additive-energy / Wick budget), yields

> `#{b : ‖η_b‖² > K·n} ≤ Cᵣ · q / K^r`.

So each rung of the moment ladder sharpens the polynomial floor by one power of `1/K`. As `r → ∞`
this approaches the Gaussian tail `e^{-cK}` — **which is exactly the Paley/BGK conjecture**. The
catch, made exact this session (`docs/kb/deltastar-444-SADDLE-K-DIAGNOSTIC-2026-06-19.md`): the
constant `Cᵣ` is *not* uniform — the measured energy ratio `Cᵣ^{1/r} = K_max ~ n^{0.77}` diverges, so
the ladder's product `Cᵣ/K^r` stops improving before `r` reaches `log q`. The ladder climbs toward
Gaussian but the diverging `Cᵣ` caps it at the BGK exponent `n^{1-o(1)}`. Closing the final
`n^{o(1)}` gap is the open conjecture — it requires the energy budget `Cᵣ` to stay bounded
(equivalently `K_max = O(1)`), which is false for the *moment* object but (per the spectral
universality data) plausibly true for the *max*.

## Honest scope
PROVEN: the abstract Markov-at-power-`r` floor and its period-moment specialization (axiom-clean),
strictly generalizing `_AvW9` (the `r=1` case). This formalizes the entire moment ladder and pins
the exact reason it falls short. NOT the conjecture (the uniform `Cᵣ` is open). NOT closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW10

open Finset

/-- **Markov at power `r` (proven).** For nonnegative `a : ι → ℝ` over finite `s` with bounded `r`-th
moment `Σ a_i^r ≤ S`, and `T > 0`, `r ≥ 1`: `#{i : a_i > T} ≤ S / T^r`. (Each exceeding index
contributes `> T^r` to the `r`-th-moment sum.) Generalizes `_AvW9.count_large_le_of_sum` (`r = 1`). -/
theorem count_large_le_of_moment {ι : Type*} (s : Finset ι) (a : ι → ℝ) (S T : ℝ) (r : ℕ)
    (hr : 1 ≤ r) (ha : ∀ i ∈ s, 0 ≤ a i) (hT : 0 < T)
    (hmom : ∑ i ∈ s, (a i) ^ r ≤ S) :
    ((s.filter (fun i => T < a i)).card : ℝ) ≤ S / T ^ r := by
  set B := s.filter (fun i => T < a i) with hB
  have hBsub : B ⊆ s := filter_subset _ _
  have hTr : 0 < T ^ r := pow_pos hT r
  -- on B, a_i^r > T^r, so the r-th-moment mass over B is ≥ |B|·T^r
  have hmassB : (B.card : ℝ) * T ^ r ≤ ∑ i ∈ B, (a i) ^ r := by
    have hconst : ∑ _i ∈ B, T ^ r ≤ ∑ i ∈ B, (a i) ^ r := by
      apply Finset.sum_le_sum
      intro i hi
      have hlt : T < a i := (Finset.mem_filter.mp hi).2
      have hTi : T ≤ a i := hlt.le
      gcongr
    rwa [Finset.sum_const, nsmul_eq_mul] at hconst
  -- mass over B ≤ total r-th moment ≤ S
  have hBs : ∑ i ∈ B, (a i) ^ r ≤ ∑ i ∈ s, (a i) ^ r :=
    Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun i hi _ => pow_nonneg (ha i hi) r)
  have hkey : (B.card : ℝ) * T ^ r ≤ S := le_trans hmassB (le_trans hBs hmom)
  rw [le_div_iff₀ hTr]
  linarith [hkey]

/-- **The `r`-th rung of the period moment ladder (proven specialization).** With `a_b = ‖η_b‖²`,
the `2r`-th period moment `Σ_b ‖η_b‖^{2r} = Σ_b (‖η_b‖²)^r ≤ Cᵣ·q·n^r` (the Wick/energy budget),
the count of frequencies whose squared period exceeds `K·n` is `≤ Cᵣ·q / K^r`. Stated abstractly:
`etaSq b = ‖η_b‖²`, moment bound as hypothesis. This is the `1/K^r` suppression — `r=1` recovers
`_AvW9`'s `q/K` Parseval floor; growing `r` drives toward the Gaussian `e^{-cK}` (the conjecture). -/
theorem period_moment_ladder_floor {ι : Type*} (s : Finset ι) (etaSq : ι → ℝ)
    (Cr q n K : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hnn : ∀ b ∈ s, 0 ≤ etaSq b)
    (hmom : ∑ b ∈ s, (etaSq b) ^ r ≤ Cr * q * n ^ r)
    (hn : 0 < n) (hK : 0 < K) :
    ((s.filter (fun b => K * n < etaSq b)).card : ℝ) ≤ Cr * q / K ^ r := by
  have hT : 0 < K * n := mul_pos hK hn
  have h := count_large_le_of_moment s etaSq (Cr * q * n ^ r) (K * n) r hr hnn hT hmom
  -- (Cr·q·n^r)/(K·n)^r = Cr·q/K^r
  have hsimp : (Cr * q * n ^ r) / (K * n) ^ r = Cr * q / K ^ r := by
    rw [mul_pow]
    rw [show Cr * q * n ^ r = (Cr * q) * n ^ r from rfl]
    rw [mul_div_mul_right _ _ (pow_ne_zero r (ne_of_gt hn))]
  rwa [hsimp] at h

end ArkLib.ProximityGap.Frontier.AvW10

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW10.count_large_le_of_moment
#print axioms ArkLib.ProximityGap.Frontier.AvW10.period_moment_ladder_floor
