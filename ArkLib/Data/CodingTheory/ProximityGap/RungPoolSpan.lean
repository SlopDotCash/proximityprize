/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungFrameCensus

/-!
# The rung pool–span law (#371, round-7 target): the c-dichotomy

The remaining counting side of the level-1 rung.  Subtracting two defect
identities of a polynomial-pair stack (deg `R₁ = degR`, multipliers within the
graded budget) gives `(γ₁ − γ₂)·R₁ = g₁·m_{S₁} − g₂·m_{S₂} + (P₂ − P₁)`
EXACTLY.  Consequences:

* **`pool_pair_span`** — for DISTINCT bad scalars, `R₁` lies in the span of
  the pair's witness data: `R₁ = c·(g₁·m_{S₁} − g₂·m_{S₂} + (P₂ − P₁))` with
  `c = (γ₁ − γ₂)⁻¹` — the direction row is reconstructible from ANY two
  distinct bad scalars.  The witness family of a multi-bad stack is therefore
  a rigid `R₁`-pinned module — the surface on which the small-overlap "pool"
  is counted;
* **`same_witness_data_same_gamma`** — the type-(b) collapse: equal witness
  data (`g₁·m_{S₁} = g₂·m_{S₂}` and `P₁ = P₂`) forces equal scalars whenever
  `deg R₁ ≥ k` (the difference would have degree `< k`).

Probe record: `probe_wb371_rung_census.py` — the pool (mutually small-overlap
bad families) is EMPTY at every tested stack (the maximum is always the fully
attached antipodal pencil); the swarm's absolute 52-cap is exactly the
pool-side Fisher at `s = k`, which this span-rigidity must (and the probes
say does) collapse.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section PoolSpan

variable {dom : Fin n ↪ F} {k : ℕ}
variable {R₀ R₁ : F[X]}

/-- **The pool–span law**: two distinct bad scalars reconstruct the direction
row from their witness data. -/
theorem pool_pair_span
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂)
    {P₁ P₂ g₁ g₂ : F[X]} {S₁ S₂ : Finset (Fin n)}
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂) :
    R₁ = C (γ₁ - γ₂)⁻¹ *
      (g₁ * vanishingPoly dom S₁ - g₂ * vanishingPoly dom S₂ + (P₁ - P₂)) := by
  have hγ : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  have hkey : C (γ₁ - γ₂) * R₁
      = g₁ * vanishingPoly dom S₁ - g₂ * vanishingPoly dom S₂ + (P₁ - P₂) := by
    rw [C_sub]
    linear_combination hid₁ - hid₂
  calc R₁ = C (γ₁ - γ₂)⁻¹ * (C (γ₁ - γ₂) * R₁) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hγ, C_1, one_mul]
    _ = C (γ₁ - γ₂)⁻¹ *
        (g₁ * vanishingPoly dom S₁ - g₂ * vanishingPoly dom S₂ + (P₁ - P₂)) := by
        rw [hkey]

/-- **The type-(b) collapse**: equal witness data forces equal scalars when
the direction row has degree ≥ k. -/
theorem same_witness_data_same_gamma (hR₁ : k ≤ R₁.natDegree)
    {γ₁ γ₂ : F} {P₁ P₂ g₁ g₂ : F[X]} {S₁ S₂ : Finset (Fin n)}
    (hdP₁ : P₁.natDegree < k) (hdP₂ : P₂.natDegree < k)
    (hdata : g₁ * vanishingPoly dom S₁ = g₂ * vanishingPoly dom S₂)
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂) :
    γ₁ = γ₂ := by
  by_contra hne
  have hγ : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  have hkey : C (γ₁ - γ₂) * R₁ = P₁ - P₂ := by
    rw [C_sub]
    linear_combination hid₁ - hid₂ + hdata
  have hCne : (C (γ₁ - γ₂) : F[X]) ≠ 0 := C_ne_zero.mpr hγ
  have hR₁ne : R₁ ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hR₁
    have h1 : P₁.natDegree < 0 := lt_of_lt_of_le hdP₁ hR₁
    omega
  have hdeg : (C (γ₁ - γ₂) * R₁).natDegree = R₁.natDegree := by
    rw [Polynomial.natDegree_mul hCne hR₁ne, natDegree_C, zero_add]
  have hsub : (P₁ - P₂).natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdP₁ hdP₂)
  rw [hkey] at hdeg
  omega

/-- **Frame extraction**: a bad scalar whose witness meets an agreement set of
the direction row carries the shifted identity through the agreement
factorization `R₁ − q = m_A·h`: `(R₀ − r) + γ·(m_A·h) = g·m_S` with the frame
`r := P − γ·q` — the entry point of `frame_cross_disjoint`. -/
theorem frame_extraction
    {γ : F} {P q h g : F[X]} {A S : Finset (Fin n)}
    (hfac : R₁ - q = vanishingPoly dom A * h)
    (hid : R₀ + C γ * R₁ - P = g * vanishingPoly dom S) :
    (R₀ - (P - C γ * q)) + C γ * (vanishingPoly dom A * h)
      = g * vanishingPoly dom S := by
  rw [← hfac]
  linear_combination hid

end PoolSpan

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.pool_pair_span
#print axioms ProximityGap.WBPencil.same_witness_data_same_gamma
#print axioms ProximityGap.WBPencil.frame_extraction
