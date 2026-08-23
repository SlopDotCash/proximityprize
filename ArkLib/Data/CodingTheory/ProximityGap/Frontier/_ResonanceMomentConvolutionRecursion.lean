/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSumConvolutionRecursion

/-!
# Aggregate L² recursion of the resonance moment via Young's convolution inequality (#407 / #444)

Direct consequence of the exact phase-sum convolution recursion
`phaseSum u (r+1) c = ∑_{a≠0} u(a)·phaseSum u r (c−a)`
(`_ResonancePhaseSumConvolutionRecursion`): applying Cauchy–Schwarz to the `(m−1)`-term inner sum
and summing over `c` (with the shift `c ↦ c−a` a bijection of `ZMod m`) gives the clean aggregate
**L² recursion** for the named free variable `T r = resonanceMoment u r`:

> **`T (r+1) ≤ (m−1)² · T r`** for unit-modulus phases.

This is the `T`-level (aggregate) analogue of the L∞ submultiplicativity in
`_ResonancePhaseSumConvolutionSubmult`. Iterating from the base `T 1 = m−1` it reproduces the
trivial ceiling `T r ≤ m·(m−1)^{2(r−1)}` order (the Cauchy–Schwarz step loses the `1/m` Plancherel
normalisation; that lost factor IS the cancellation budget).

## Why this is the right follow-on (probe-confirmed slack, not a re-confirmation)

Probe `scripts/probes/probe_T_recursion.py` (random unit phases, `m∈{3,5,7}`, `r∈{1,2,3}`): the
inequality `T(r+1) ≤ (m−1)²·T(r)` holds with STRICT SLACK at every instance (e.g. `m=7,r=1`:
`64.76` vs `216`). The slack is exactly the Cauchy–Schwarz defect = the phase coherence the
convolution fails to achieve — i.e. the gap between this phase-blind recursion and the true
`Θ(m^r)` √-cancellation regime. The recursion thus PINS where the open content lives: in the
Cauchy–Schwarz inequality's defect (the `b≠0` Fourier mass `K̂(b)`), NOT in the bound itself.

## Honest scope

A CERTAIN consequence of the recursion (Young's convolution inequality, kernel L¹ mass `m−1`). It
does NOT close the `(m−1)²` ↦ `Θ(m)` gap — that needs the cancellation budget (the open
Gauss-period/BGK `K̂(b)` profile). CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE /
cancellation / completion / moment / anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- The nonzero-residue filter has cardinality `m − 1`. -/
private theorem card_nz_filter :
    (Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card = m - 1 := by
  classical
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, ZMod.card]

/-- **Per-frequency Cauchy–Schwarz on the convolution recursion (unit phases).**
`‖phaseSum u (r+1) c‖² ≤ (m−1) · ∑_{a≠0} ‖phaseSum u r (c−a)‖²`. The `(m−1)`-term inner sum is
bounded by Cauchy–Schwarz, with each `‖u a‖ = 1`. -/
theorem normSq_phaseSum_succ_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (r : ℕ) (c : ZMod m) :
    ‖phaseSum u (r + 1) c‖ ^ 2
      ≤ ((m : ℝ) - 1) *
        ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
          ‖phaseSum u r (c - a)‖ ^ 2 := by
  classical
  set s := Finset.univ.filter (fun a : ZMod m => a ≠ 0) with hs
  rw [phaseSum_succ]
  -- ‖∑_{a∈s} u a * P_r(c-a)‖ ≤ ∑ ‖u a * P_r(c-a)‖ = ∑ ‖P_r(c-a)‖, then Cauchy-Schwarz on s.
  have hpoint : ∀ a ∈ s, ‖u a * phaseSum u r (c - a)‖ = ‖phaseSum u r (c - a)‖ := by
    intro a _; rw [norm_mul, hu, one_mul]
  -- |∑|² ≤ (∑ 1²)(∑ ‖.‖²) = (m-1) · ∑ ‖.‖²  (Finset.inner_mul_le_norm_mul_norm style)
  have hcs : (∑ a ∈ s, ‖phaseSum u r (c - a)‖) ^ 2
      ≤ (s.card : ℝ) * ∑ a ∈ s, ‖phaseSum u r (c - a)‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc ‖∑ a ∈ s, u a * phaseSum u r (c - a)‖ ^ 2
      ≤ (∑ a ∈ s, ‖u a * phaseSum u r (c - a)‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _)
    _ = (∑ a ∈ s, ‖phaseSum u r (c - a)‖) ^ 2 := by
        rw [Finset.sum_congr rfl hpoint]
    _ ≤ (s.card : ℝ) * ∑ a ∈ s, ‖phaseSum u r (c - a)‖ ^ 2 := hcs
    _ = ((m : ℝ) - 1) * ∑ a ∈ s, ‖phaseSum u r (c - a)‖ ^ 2 := by
        rw [hs, card_nz_filter]
        have hm : 1 ≤ m := NeZero.one_le
        push_cast [Nat.cast_sub hm]; ring_nf

/-- **Aggregate L² recursion of the resonance moment: `T (r+1) ≤ (m−1)² · T r`** (unit phases).
Sum the per-frequency Cauchy–Schwarz bound over `c`, swap the order, and use that `c ↦ c−a` is a
bijection of `ZMod m` so each inner `∑_c ‖phaseSum u r (c−a)‖² = T r`. The `(m−1)` factors are
the kernel L¹ mass (from Cauchy–Schwarz width) and the bijection count. -/
theorem resonanceMoment_succ_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    resonanceMoment u (r + 1) ≤ ((m : ℝ) - 1) ^ 2 * resonanceMoment u r := by
  classical
  set s := Finset.univ.filter (fun a : ZMod m => a ≠ 0) with hs
  unfold resonanceMoment
  -- ∑_c ‖P_{r+1} c‖² ≤ ∑_c (m-1) ∑_{a∈s} ‖P_r (c-a)‖²
  calc (∑ c : ZMod m, ‖phaseSum u (r + 1) c‖ ^ 2)
      ≤ ∑ c : ZMod m, ((m : ℝ) - 1) * ∑ a ∈ s, ‖phaseSum u r (c - a)‖ ^ 2 :=
        Finset.sum_le_sum (fun c _ => normSq_phaseSum_succ_le u hu r c)
    _ = ((m : ℝ) - 1) * ∑ c : ZMod m, ∑ a ∈ s, ‖phaseSum u r (c - a)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = ((m : ℝ) - 1) * ∑ a ∈ s, ∑ c : ZMod m, ‖phaseSum u r (c - a)‖ ^ 2 := by
        rw [Finset.sum_comm]
    _ = ((m : ℝ) - 1) * ∑ a ∈ s, ∑ c : ZMod m, ‖phaseSum u r c‖ ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro a _
        exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun c => rfl)
    _ = ((m : ℝ) - 1) * ((s.card : ℝ) * ∑ c : ZMod m, ‖phaseSum u r c‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((m : ℝ) - 1) ^ 2 * ∑ c : ZMod m, ‖phaseSum u r c‖ ^ 2 := by
        rw [hs, card_nz_filter]
        have hm : 1 ≤ m := NeZero.one_le
        push_cast [Nat.cast_sub hm]; ring

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.normSq_phaseSum_succ_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_succ_le
