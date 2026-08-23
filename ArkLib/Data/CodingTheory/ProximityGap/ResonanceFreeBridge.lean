/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# Resonance-freeness ⟹ the worst-case incomplete-sum bound (#407 brick #8)

The #407 brick ledger resolves **resonance-freeness of the Gauss-sum phases** to `OPEN-equiv-BGK`: it is
the prize sup-norm `M(n) ≤ √(n log q)` written in the dual (multiplicative-character) basis, via the
EXACT completion identity `t·η_b = Σ_{j<t} g(χ^{dj}, ψ_b)` (`SubgroupGaussSumWorstCase.completion_identity`,
axiom-clean).  This file machine-checks the forward direction of that equivalence: a **resonance-free
bound** on the Gauss-sum side discharges `WorstCaseIncompleteSumBound` on the period side.

The point of the brick is that resonance-freeness is **not a strictly weaker** statement — the reduction
is an exact algebraic identity (`t·η_b = Σ g(χ^{dj})`), so a bound `R` on `max_b‖Σ_{j<t} g(χ^{dj},ψ_b)‖`
transfers losslessly (up to the explicit factor `1/t`) to a per-frequency period bound.  Hence "Gauss sums
don't conspire" `⟺` "the period sup-norm is small" `=` BGK; this file is the `⟹` half, the lossless
transfer, proven axiom-clean from the in-tree completion identity.

All elementary; **axiom-clean** (`propext, Classical.choice, Quot.sound`), no `sorry`.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.ResonanceFreeBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The resonance-free bound** at index `d` (the dual-basis form of the prize sup-norm).  `R` bounds
the worst-case Gauss-sum-side sum `‖Σ_{j<t} g(χ^{dj}, ψ_b)‖` over far frequencies `b ≠ 0`, where
`t = (q−1)/d` and `χ` is a generator of the character group.  By the completion identity this sum equals
`t·η_b`, so `R` is exactly `t·M(μ_d)` — "no frequency `b` aligns `Ω(t)` of the Gauss sums". -/
def ResonanceFreeBound {d : ℕ} {χ : MulChar F ℂ} (ψ : AddChar F ℂ) (R : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 →
    ‖∑ j ∈ Finset.range ((Fintype.card F - 1) / d),
        gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ ≤ R

/-- **Resonance-free ⟹ worst-case incomplete-sum bound (lossless transfer).**  Given the completion
identity hypotheses (`d ∣ q−1`, `χ` a full-order generator), a resonance-free bound `R` on the
Gauss-sum side discharges `WorstCaseIncompleteSumBound ψ (torsion F d) (R/t)²` on the period side, with
`t = (q−1)/d` the explicit transfer factor.  Proof: `t·η_b = Σ_{j<t} g(χ^{dj},ψ_b)` exactly
(`completion_identity`), so `t·‖η_b‖ = ‖Σ‖ ≤ R`, hence `‖η_b‖ ≤ R/t` and `‖η_b‖² ≤ (R/t)²`.

This is the `⟹` half of "resonance-free `⟺` `M(μ_d) ≤ √(n log q)`" — the exact algebraic reduction
that makes the brick `OPEN-equiv-BGK` (not strictly weaker): the open content `R = O(t·√(n log q))`
IS the BGK sup-norm in the dual basis. -/
theorem worstCaseIncompleteSumBound_of_resonanceFree
    {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) {R : ℝ} (hR : ResonanceFreeBound (d := d) (χ := χ) ψ R) :
    WorstCaseIncompleteSumBound ψ (torsion F d)
      ((R / ((Fintype.card F - 1) / d : ℕ)) ^ 2) := by
  set t : ℕ := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  intro b hb
  -- completion identity: (t:ℂ)·η_b = Σ_{j<t} g(χ^{dj}, ψ_b)
  have hcomp := completion_identity (F := F) hd hd0 hord ψ b
  -- take norms: t·‖η_b‖ = ‖Σ‖
  have hnorm : (t : ℝ) * ‖eta ψ (torsion F d) b‖
      = ‖∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ := by
    have := congrArg norm hcomp
    rwa [norm_mul, Complex.norm_natCast] at this
  -- resonance-free bound ⟹ ‖Σ‖ ≤ R
  have hsum_le : ‖∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ ≤ R :=
    hR b hb
  -- hence ‖η_b‖ ≤ R/t
  have heta_le : ‖eta ψ (torsion F d) b‖ ≤ R / (t : ℝ) := by
    rw [le_div_iff₀ htR, mul_comm]
    rw [hnorm]; exact hsum_le
  have heta_nonneg : (0 : ℝ) ≤ ‖eta ψ (torsion F d) b‖ := norm_nonneg _
  -- square both sides
  calc ‖eta ψ (torsion F d) b‖ ^ 2
      ≤ (R / (t : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ heta_nonneg heta_le
  _ = (R / ((Fintype.card F - 1) / d : ℕ)) ^ 2 := by norm_num [ht]

/-- **Worst-case incomplete-sum bound ⟹ resonance-free (the converse, same factor `t`).**  A
per-frequency period bound `‖η_b‖² ≤ M` transfers losslessly back to the Gauss-sum side:
`‖Σ_{j<t} g(χ^{dj},ψ_b)‖ = t·‖η_b‖ ≤ t·√M`, i.e. `ResonanceFreeBound` with `R = t·√M`.  Together with
`worstCaseIncompleteSumBound_of_resonanceFree` this gives the full equivalence — resonance-freeness is
**exactly** the BGK sup-norm in the dual basis, neither stronger nor weaker. -/
theorem resonanceFree_of_worstCaseIncompleteSumBound
    {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hW : WorstCaseIncompleteSumBound ψ (torsion F d) M) :
    ResonanceFreeBound (d := d) (χ := χ) ψ
      (((Fintype.card F - 1) / d : ℕ) * Real.sqrt M) := by
  set t : ℕ := (Fintype.card F - 1) / d with ht
  intro b hb
  have hcomp := completion_identity (F := F) hd hd0 hord ψ b
  have hnorm : ‖∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖
      = (t : ℝ) * ‖eta ψ (torsion F d) b‖ := by
    have := congrArg norm hcomp
    rw [norm_mul, Complex.norm_natCast] at this
    exact this.symm
  have hsq : ‖eta ψ (torsion F d) b‖ ^ 2 ≤ M := hW b hb
  have heta_le : ‖eta ψ (torsion F d) b‖ ≤ Real.sqrt M := by
    nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg M, norm_nonneg (eta ψ (torsion F d) b), hsq,
      sq_nonneg (‖eta ψ (torsion F d) b‖ - Real.sqrt M)]
  rw [hnorm]
  have htnn : (0 : ℝ) ≤ (t : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left heta_le htnn

end ArkLib.ProximityGap.ResonanceFreeBridge
