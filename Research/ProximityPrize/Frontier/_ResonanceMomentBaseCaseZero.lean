/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# The depth-`0` base case of the resonance moment (#407 / #444)

The deep resonance moment `T r = resonanceMoment u r = ∑_c ‖phaseSum u r c‖²` is the `√p`-free
open core of the prize (`GaussPhaseResonance`). Its one-step structure is now fully formalized:
the EXACT convolution recursion `phaseSum u (r+1) c = ∑_{a≠0} u(a)·phaseSum u r (c−a)`
(`_ResonancePhaseSumConvolutionRecursion`), the aggregate `L²` recursion `T(r+1) ≤ (m−1)²·T r`
(`_ResonanceMomentConvolutionRecursion`), and the depth-`1` evaluation `T 1 = m−1`
(`_ResonanceMomentBaseCase`).

What was MISSING (grep-confirmed: no `phaseSum _ 0` / `resonanceMoment _ 0` pin anywhere in
`ProximityGap/`) is the depth-`0` **initial condition** of that whole recursion tower:

> **`phaseSum u 0 c = if c = 0 then 1 else 0`**, hence **`resonanceMoment u 0 = 1`**.

The depth-`0` filter ranges over the single empty tuple `X : Fin 0 → ZMod m`: the predicate
`∀ i, X i ≠ 0` is vacuously true and the empty sum `∑ i, X i = 0`, so the filter is `{∅}` when
`c = 0` and `∅` otherwise; the empty product is `1`. This pins the base rung so the iterated
chain `T r ≤ (m−1)^{2r}` reads off the recursion from a real `r = 0` start (value `1`), not the
`r ≥ 1` partial form.

PROBE: `scripts/probes/probe_resonance_r0.py` (random unit phases, `m ∈ {5,7,11}`) confirms
`phaseSum u 0 c = [c=0?1:0]` and `T 0 = 1` to machine epsilon.

This is a CERTAIN exact algebraic identity (an initial condition), NOT a bound. It makes NO
CORE / cancellation / completion / moment / anti-concentration / capacity claim. The prize
`M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN; the open content is the spectral profile of `K̂(b)`,
not this base case.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407 / #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- The depth-`0` filter `{X : Fin 0 → ZMod m | (∀ i, X i ≠ 0) ∧ ∑ i, X i = c}` is the singleton
`{Fin.elim0-style empty tuple}` exactly when `c = 0`, and empty otherwise. We package the
membership criterion: any `X : Fin 0 → ZMod m` is in the filter iff `c = 0` (there being only one
such `X` by `Subsingleton`). -/
theorem mem_phaseSum_zero_filter (c : ZMod m) (X : Fin 0 → ZMod m) :
    (X ∈ (Finset.univ.filter (fun X : Fin 0 → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c))) ↔ c = 0 := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hsum⟩
    simpa [Fin.sum_univ_zero] using hsum.symm
  · intro hc
    refine ⟨fun i => i.elim0, ?_⟩
    simp [hc]

/-- **`phaseSum u 0 c = if c = 0 then 1 else 0`.** The depth-`0` phase-sum is the empty-tuple
initial condition: it is the Kronecker delta at `c = 0` (the empty product is `1`). -/
theorem phaseSum_zero (u : ZMod m → ℂ) (c : ZMod m) :
    phaseSum u 0 c = if c = 0 then 1 else 0 := by
  classical
  unfold phaseSum
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    rw [Finset.sum_eq_single (fun _ => (0 : ZMod m))]
    · simp
    · intro b _ hb
      exact absurd (Subsingleton.elim b (fun _ => 0)) hb
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨fun i => i.elim0, by simp⟩⟩) h
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro X hX
    exact absurd ((mem_phaseSum_zero_filter c X).mp hX) hc

/-- **`resonanceMoment u 0 = 1`.** The depth-`0` resonance moment is the initial condition of the
entire recursion tower: `T 0 = ∑_c ‖phaseSum u 0 c‖² = ‖1‖² = 1`, the single nonzero term being
the Kronecker delta at `c = 0`. Holds for ALL phase vectors `u` (no unit hypothesis needed). -/
theorem resonanceMoment_zero (u : ZMod m → ℂ) :
    resonanceMoment u 0 = 1 := by
  classical
  unfold resonanceMoment
  rw [Finset.sum_eq_single (0 : ZMod m)]
  · rw [phaseSum_zero, if_pos rfl]; simp
  · intro c _ hc
    rw [phaseSum_zero, if_neg hc]; simp
  · intro h
    exact absurd (Finset.mem_univ (0 : ZMod m)) h

/-- **`ResonanceConjecture u 0` holds UNCONDITIONALLY** (for ALL `u`, no unit / `m ≥ 2` hypothesis).
The depth-`0` conjecture target is `(2·m·log m)^0 = 1` and `T 0 = 1`, so the bound `T 0 ≤ 1` holds
with equality. This is the base-case companion of the depth-`1` discharge
`resonanceConjecture_one_of_unit`: the Resonance Conjecture is trivially true at the small depths
`r ∈ {0, 1}`; the open Gauss-period / BGK content lives at depth `r ≍ log m`. -/
theorem resonanceConjecture_zero (u : ZMod m → ℂ) :
    ResonanceConjecture u 0 := by
  unfold ResonanceConjecture
  rw [resonanceMoment_zero, pow_zero]

end ArkLib.ProximityGap.GaussPhaseResonance
