/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceParsevalBridge

/-!
# The per-frequency triangle ceiling `‖K̂(k)‖ ≤ m−1` and `T r ≤ (m−1)^{2r}` (#407 / #444)

The one-step Gauss-period kernel spectrum `K̂(k) = kernelSpectrum (dftChar k) u = ∑_{a≠0} u(a)·ψ_k(a)`
is a sum of `m−1` unit-modulus terms (`‖u a‖ = 1`, `‖ψ_k(a)‖ = 1`), so the triangle inequality gives
the trivial per-frequency ceiling:

> **`‖kernelSpectrum (dftChar k) u‖ ≤ m − 1`**  for every frequency `k` (unit-modulus phases).

This is the spectral analogue of the phase-mass extremizer (`‖S‖ ≤ m−1`). Through the Parseval bridge
`T r = (1/m) ∑_k |K̂(k)|^{2r}` it immediately yields the clean spectral ceiling on the resonance tower:

> **`resonanceMoment u r ≤ (m − 1)^{2r}`**  (unit-modulus phases),

since every one of the `m` summands `|K̂(k)|^{2r} ≤ (m−1)^{2r}` and the `1/m` cancels the count. This
is the `K̂(0)`-saturated trivial regime: equality at the DC frequency `k = 0`, where
`K̂(0) = ∑_{a≠0} u(a) = S` attains `m−1` for the constant phase vector (no cancellation). The open
prize lives entirely in beating this at the WORST frequency `max_b |K̂(b)|` — i.e. exhibiting
genuine multiplicative phase cancellation `|K̂(b)| ≪ m−1` at the adversarial `b`.

## Honest scope

CERTAIN ceiling (triangle inequality on unit-modulus terms + the proven Parseval bridge), not a CORE
bound. It bounds `T` ABOVE by the TRIVIAL `(m−1)^{2r}` (the no-cancellation regime), which is the
WRONG direction for the prize (the prize needs `√`-cancellation `T = Θ(m^r) ≪ (m−1)^{2r}`). It does
NOT bound `max_b |K̂(b)|` below the trivial `m−1` — that is the open Gauss-period/BGK content. CORE
`M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion / moment-as-prize /
anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- `‖dftChar k a‖ = 1`: the DFT character is unit-modulus (`AddChar.norm_apply`). -/
theorem norm_dftChar (k a : ZMod m) : ‖dftChar k a‖ = 1 := by
  unfold dftChar
  exact AddChar.norm_apply _ _

/-- **The per-frequency triangle ceiling: `‖K̂(k)‖ ≤ m − 1`** (unit-modulus phases).
`K̂(k) = ∑_{a≠0} u(a)·ψ_k(a)` is a sum of `m − 1` unit-modulus terms; triangle inequality. -/
theorem norm_kernelSpectrum_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (k : ZMod m) :
    ‖kernelSpectrum (dftChar k) u‖ ≤ (m : ℝ) - 1 := by
  classical
  unfold kernelSpectrum
  set s := Finset.univ.filter (fun a : ZMod m => a ≠ 0) with hs
  calc ‖∑ a ∈ s, u a * dftChar k a‖
      ≤ ∑ a ∈ s, ‖u a * dftChar k a‖ := norm_sum_le _ _
    _ = ∑ a ∈ s, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [norm_mul, hu, norm_dftChar, one_mul]
    _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (m : ℝ) - 1 := by
        rw [hs, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
          Finset.card_univ, ZMod.card]
        have hm : 1 ≤ m := NeZero.one_le
        rw [Nat.cast_sub hm, Nat.cast_one]

/-- **The spectral (trivial) ceiling on the resonance tower: `T r ≤ (m − 1)^{2r}`** (unit phases).
Through the Parseval bridge `m·T r = ∑_k ‖K̂(k)‖^{2r}`, each of the `m` summands is at most
`(m−1)^{2r}` by the per-frequency triangle ceiling, so `m·T r ≤ m·(m−1)^{2r}`. The `K̂(0)`-saturated
no-cancellation regime; the prize needs `T r = Θ(m^r) ≪ (m−1)^{2r}`. -/
theorem resonanceMoment_le_pow (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    resonanceMoment u r ≤ ((m : ℝ) - 1) ^ (2 * r) := by
  classical
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
    linarith
  have hbridge := resonanceMoment_eq_spectral_powerMean u r
  -- ∑_k ‖K̂(k)‖^{2r} ≤ ∑_k (m-1)^{2r} = m·(m-1)^{2r}
  have hsum_le : (∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ (2 * r))
      ≤ (m : ℝ) * ((m : ℝ) - 1) ^ (2 * r) := by
    calc (∑ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ (2 * r))
        ≤ ∑ k : ZMod m, ((m : ℝ) - 1) ^ (2 * r) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_kernelSpectrum_le u hu k) (2 * r)
      _ = (m : ℝ) * ((m : ℝ) - 1) ^ (2 * r) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  -- m·T r = ∑_k ‖K̂‖^{2r} ≤ m·(m-1)^{2r} ⇒ T r ≤ (m-1)^{2r}
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  have hmul : (m : ℝ) * resonanceMoment u r ≤ (m : ℝ) * ((m : ℝ) - 1) ^ (2 * r) := by
    rw [hbridge]; exact hsum_le
  exact le_of_mul_le_mul_left hmul hmpos

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.norm_dftChar
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.norm_kernelSpectrum_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_le_pow
