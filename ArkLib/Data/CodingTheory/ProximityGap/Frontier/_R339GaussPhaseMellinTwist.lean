/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

/-!
# R339: the Mellin/twist form of the completion identity (Gauss-phase PAPR bridge)

Session 2026-07-09 (#466). The completion identity
(`SubgroupGaussSumWorstCase.completion_identity`) writes `t·η_b` as a sum of `t`
complete Gauss sums against the shifted character `mulShift ψ b`. This file extracts
the shift as a multiplicative twist:

  `t·η_b = −1 + ∑_{j=1}^{t−1} (χ^{dj})⁻¹(b) · τ(χ^{dj}, ψ)`   (`mellin_identity`)

i.e. `η_b` is (up to the DC term `−1`) the discrete *Mellin/DFT transform* of the fixed
Gauss-phase vector `(τ(χ^{dj},ψ))_j`, evaluated at the frequency `χ(b) ∈ μ_t`. The
per-frequency wall (face 3 of the open core) is therefore *exactly* a deterministic
peak-to-average (PAPR) statement for the Gauss-phase sequence.

The PAPR bound itself — random-phase scale `A·√(q·t·log t)` for the Mellin peak —
is stated as the NAMED OPEN Prop `GaussPhasePAPRBound` (it is a unitary rewrite of the
open per-frequency core, NOT easier; see memory `issue466-gauss-phase-papr-reformulation`
and DISPROOF_LOG context: numerics over 4648 primes show ratio ≈1.29 flat, max 2.07,
extremes = small-2-power bad primes capped at O(log q)). The consumer
`norm_eta_le_of_papr` is PROVEN: PAPR at constant `A` yields the per-frequency bound
`‖η_b‖ ≤ (1 + A·√(q·t·log t))/t`, which at `q ≈ n·t` is the `√(n log t)`-scale target.

Identity numerically verified to ~1e-12 for (p,n) up to (3329,64) (papr_check.py).
Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.R339GaussPhaseMellinTwist

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Extracting a nonzero shift from a Gauss sum as a multiplicative twist:
`τ(χ', ψ_b) = χ'⁻¹(b) · τ(χ', ψ)`. -/
theorem gaussSum_mulShift_twist (χ' : MulChar F ℂ) (ψ : AddChar F ℂ) {b : F}
    (hb : b ≠ 0) :
    gaussSum χ' (AddChar.mulShift ψ b) = χ'⁻¹ b * gaussSum χ' ψ := by
  have hu : IsUnit b := isUnit_iff_ne_zero.mpr hb
  have h := gaussSum_mulShift χ' ψ hu.unit
  rw [IsUnit.unit_spec] at h
  have hne : χ' b ≠ 0 := by
    intro h0
    have hn := norm_mulChar_apply_unit χ' hb
    rw [h0, norm_zero] at hn
    norm_num at hn
  have hinv : χ'⁻¹ b * χ' b = 1 := by
    rw [MulChar.inv_apply_eq_inv' χ' b, inv_mul_cancel₀ hne]
  calc gaussSum χ' (AddChar.mulShift ψ b)
      = (χ'⁻¹ b * χ' b) * gaussSum χ' (AddChar.mulShift ψ b) := by rw [hinv, one_mul]
    _ = χ'⁻¹ b * (χ' b * gaussSum χ' (AddChar.mulShift ψ b)) := by ring
    _ = χ'⁻¹ b * gaussSum χ' ψ := by rw [h]

/-- **The Mellin identity** (Theorem 1 of the 2026-07-09 audit): for the `d`-torsion
subgroup, full-order `χ`, primitive `ψ`, and `b ≠ 0`,

  `t·η_b = −1 + ∑_{j ∈ (range t).erase 0} (χ^{dj})⁻¹(b) · τ(χ^{dj}, ψ)`,

with `t = (q−1)/d`. `η_b` is thus the Mellin/DFT transform of the Gauss-phase vector
evaluated at frequency `χ(b)`. -/
theorem mellin_identity {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ((Fintype.card F - 1) / d : ℕ) * eta ψ (torsion F d) b
      = -1 + ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
          (χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ := by
  set t := (Fintype.card F - 1) / d with ht
  have ht0 : 0 < t := by
    have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
    have hq1 : 0 < Fintype.card F - 1 := by
      have := Fintype.one_lt_card (α := F)
      omega
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have hcomp := completion_identity hd hd0 hord ψ b
  have hsplit : ∑ j ∈ Finset.range t, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)
      = gaussSum (χ ^ (d * 0)) (AddChar.mulShift ψ b)
        + ∑ j ∈ (Finset.range t).erase 0,
            gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b) :=
    (Finset.add_sum_erase _ _ (Finset.mem_range.mpr ht0)).symm
  have hzero : gaussSum (χ ^ (d * 0)) (AddChar.mulShift ψ b) = -1 := by
    rw [mul_zero, pow_zero]
    exact gaussSum_one_mulShift hψ hb
  have htwist : ∀ j ∈ (Finset.range t).erase 0,
      gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)
        = (χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ := fun j _ =>
    gaussSum_mulShift_twist (χ ^ (d * j)) ψ hb
  rw [hcomp, hsplit, hzero, Finset.sum_congr rfl htwist]

/-! ## The PAPR statement (NAMED OPEN — do not discharge) -/

/-- **The Gauss-phase PAPR bound** at constant `A` for the `d`-torsion subgroup of `F`:
the Mellin transform of the Gauss-phase vector has random-phase-scale peak
`A·√(q · t · log t)` at every nonzero frequency (each of the `t−1` summands has norm
`√q`; a random unimodular phase profile gives `≍ √(q·t·log t)`).

This is a NAMED OPEN hypothesis — a unitary rewrite of the per-frequency incomplete
character-sum wall (open-core face 3), equivalent in strength to it. Numerical status
2026-07-09: ratio to target flat ≈ 1.29 over 4648 primes, max 2.07 (p = 65537); the
only structured extremes are small-2-power-in-H bad primes, whose gain is capped at
O(log q) and cannot break this bound in the prize regime. -/
def GaussPhasePAPRBound (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (A : ℝ) : Prop :=
  ∀ (χ : MulChar F ℂ), orderOf χ = Fintype.card F - 1 →
  ∀ (ψ : AddChar F ℂ), ψ.IsPrimitive → ∀ b : F, b ≠ 0 →
    ‖∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
        (χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ‖
      ≤ A * Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ)))

/-- **PROVEN consumer**: the PAPR bound yields the per-frequency Gauss-period bound
`‖η_b‖ ≤ (1 + A·√(q·t·log t)) / t`. At `q ≈ n·t` this is the `√(n log t)`-scale
target of open-core face 3 (beating the `√q` completion anchor whenever
`t ≫ log t · n / …`, i.e. throughout the prize regime). -/
theorem norm_eta_le_of_papr {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {A : ℝ} (hpapr : GaussPhasePAPRBound F d A)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    (((Fintype.card F - 1) / d : ℕ) : ℝ) * ‖eta ψ (torsion F d) b‖
      ≤ 1 + A * Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ))) := by
  have hmell := mellin_identity hd hd0 hord hψ hb
  have hnorm : (((Fintype.card F - 1) / d : ℕ) : ℝ) * ‖eta ψ (torsion F d) b‖
      = ‖((((Fintype.card F - 1) / d : ℕ) : ℂ)) * eta ψ (torsion F d) b‖ := by
    rw [norm_mul, Complex.norm_natCast]
  rw [hnorm, hmell]
  calc ‖(-1 : ℂ) + ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
          (χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ‖
      ≤ ‖(-1 : ℂ)‖ + ‖∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
          (χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ‖ := norm_add_le _ _
    _ ≤ 1 + A * Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ))) := by
        rw [norm_neg, norm_one]
        exact add_le_add le_rfl (hpapr χ hord ψ hψ b hb)

/-! ## The moment→sup skeleton (Markov + union bound over frequencies) -/

/-- **Moment-to-sup**: if the depth-`k` moment sum of a finite family is at most `B^k`,
every member is at most `B`. This is the union-bound step that converts a Wick-type
moment bound at depth `k ≈ log t` into the PAPR sup bound: instantiate `f` with the
Mellin sum of the Gauss-phase vector, `s` with the nonzero frequencies, and
`B = A·√(q·t·log t)`. The remaining open content of `GaussPhasePAPRBound` is then
EXACTLY the DC-subtracted moment bound of dossier face 3 — nothing else. -/
theorem papr_of_momentSum {α : Type*} {s : Finset α} (f : α → ℂ) {k : ℕ} (hk : 0 < k)
    {B : ℝ} (hB : 0 ≤ B) (hmom : ∑ b ∈ s, ‖f b‖ ^ k ≤ B ^ k) :
    ∀ b ∈ s, ‖f b‖ ≤ B := by
  intro b hb
  have hsingle : ‖f b‖ ^ k ≤ ∑ b' ∈ s, ‖f b'‖ ^ k :=
    Finset.single_le_sum (fun b' _ => pow_nonneg (norm_nonneg _) k) hb
  have hle : ‖f b‖ ^ k ≤ B ^ k := hsingle.trans hmom
  exact le_of_pow_le_pow_left₀ hk.ne' hB hle

#print axioms gaussSum_mulShift_twist
#print axioms papr_of_momentSum
#print axioms mellin_identity
#print axioms norm_eta_le_of_papr

end ArkLib.ProximityGap.R339GaussPhaseMellinTwist
