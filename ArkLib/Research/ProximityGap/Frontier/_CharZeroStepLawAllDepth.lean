/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import ArkLib.Research.ProximityGap.Frontier._AvNT_CumulantAdditivityEngine
import ArkLib.Research.ProximityGap.Frontier._AvW0_BesselIdentity
import ArkLib.Research.ProximityGap.Frontier._CL_GeomLamLeung
import ArkLib.Research.ProximityGap.Frontier._CharZeroBackboneAntitone
import ArkLib.Research.ProximityGap.Frontier._NonTensorWrapCrossResidual
import ArkLib.Research.ProximityGap.Frontier._wf5M3_crossstep_ceiling
import ArkLib.Research.ProximityGap.Frontier._wf8B2_char0_logconcave

/-!
# The char-0 Gaussian step law at every depth

Three in-tree encodings of the coefficient `[t^r] I₀(2√t)^m` coexist:

* `PrizeWorkbench.besselCoeff m r`, the multinomial sum of `RungBesselEnergy`, on which
  `_wf8B2_char0_logconcave` builds the Wick-normalised moment `mNorm` and the step ratio `Rstep`;
* `AvW0.cpow AvW0.I0c m r`, the convolution power in `AvW0.Edef r m = (2r)!·[t^r] I₀(2√t)^m`,
  which `LamLeungGeometric.bessel_identity_halfBasis` identifies with the `2r`-term zero-sum
  count of `μ_n`, `n = 2^{μ'+1}`, i.e. with its char-0 additive energy `E_r`;
* `AvNTCumulantEngine.cpow AvNTCumulantEngine.besselCoeff m r`, on which
  `AvNTCumulantEngine.besselPow_logDerivIndex` proves `(r+1)·c_{r+1} ≤ m·c_r` for every `r`.

The engine module states that its link to the energy is not proved there. This file proves that
the three encodings agree (`avW0_cpow_eq_avNT_cpow`, `besselCoeff_eq_avW0_cpow`) and transports
the engine's bound to the other two. The consequences hold at every depth `r`:

* `besselCoeff_logDerivIndex`: `(r+1)·besselCoeff d (r+1) ≤ d·besselCoeff d r`;
* `rstep_le_one`: `Rstep d r ≤ 1` for `d ≥ 1`, which is the conclusion of
  `PrizeWorkbench.char0_W3anti_of_sharpNewton` without its hypothesis `SharpNewtonBessel d`;
* `edef_eq_wick_mul_mNorm` and `mNorm_succ_le`: `mNorm m r` is the deficit ratio `E_r / W_r`
  with `W_r = (2r−1)‼·(2m)^r`, and it is non-increasing in `r`, so the hypothesis `hdanti` of
  `CharZeroBackbone.energy_ratio_le_of_deficit_antitone` holds (`charZero_backbone`);
* `edef_succ_le` and `energy_succ_le_halfBasis`: `E_{r+1} ≤ (2r+1)·n·E_r` for the char-0 energy
  of `μ_n`, and `energy_eq_besselCoeff_halfBasis`: `E_r = (2r)!·besselCoeff (n/2) r`;
* `char0WickStep_halfBasis`: the named input `NT5WrapCrossSplit.Char0WickStep` holds for that
  energy ladder;
* `crossMass_le_of_charZero_faithful`: `crossMass G r ≤ 2r·(2r−1)‼·|G|^(r+1)` for a finite-field
  set `G` with `|G| = 2m` whose energies at depths `r` and `r+1` equal the char-0 values.

## Scope

These are characteristic-0 statements. `rstep_le_one` bounds the step ratio by `1`; it does not
prove the antitonicity `Rstep d (r+1) ≤ Rstep d r`, which still rests on `SharpNewtonBessel d`
(proved in-tree only for `d = 1` and for the first two steps). In
`crossMass_le_of_charZero_faithful` the two energy equalities are hypotheses. For the image of
`μ_n` in a prime field they say that no spurious signed relation of `2r + 2` roots vanishes
mod `p`, which is guaranteed only for `p` above a norm threshold far beyond the production
parameters (`_wf5M3_crossstep_ceiling`). Nothing here bounds the characteristic-`p` energy in the
production regime or proves `CrossStepCeiling.M3CrossStepBound`.
-/

set_option autoImplicit false

open Finset

namespace ProximityGap.Frontier.CharZeroStepLawAllDepth

open ArkLib.ProximityGap.Frontier

/-! ### The three encodings of `[t^r] I₀(2√t)^m` agree -/

/-- The `AvW0` and `AvNT` convolution powers coincide; they differ only in the side on which the
new factor enters the Cauchy product. -/
theorem avW0_cpow_eq_avNT_cpow (c : ℕ → ℚ) (m r : ℕ) :
    AvW0.cpow c m r = AvNTCumulantEngine.cpow c m r := by
  induction m generalizing r with
  | zero => simp only [AvW0.cpow, AvNTCumulantEngine.cpow]
  | succ m ih =>
    simp only [AvW0.cpow, AvNTCumulantEngine.cpow, AvNTCumulantEngine.conv, ih]
    rw [← Finset.sum_range_reflect (fun i ↦ AvNTCumulantEngine.cpow c m i * c (r - i)) (r + 1)]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show r + 1 - 1 - j = r - j by omega, Nat.sub_sub_self hj, mul_comm]

/-- The `I₀` atoms of `AvW0` and `AvNT` are the same sequence `k ↦ 1/(k!)²`. -/
theorem i0c_eq_besselCoeff : AvW0.I0c = AvNTCumulantEngine.besselCoeff := rfl

/-- `AvW0.Edef r m = (2r)!·c_r` with `c` the `AvNT` Bessel power `cpow besselCoeff m`. -/
theorem edef_eq_avNT (r m : ℕ) :
    AvW0.Edef r m =
      ((2 * r).factorial : ℚ) * AvNTCumulantEngine.cpow AvNTCumulantEngine.besselCoeff m r := by
  rw [AvW0.Edef, avW0_cpow_eq_avNT_cpow, i0c_eq_besselCoeff]

/-- With no coordinates, `besselCoeff 0 r` is the indicator of `r = 0`. -/
theorem besselCoeff_zero_left (r : ℕ) :
    PrizeWorkbench.besselCoeff 0 r = if r = 0 then 1 else 0 := by
  cases r <;> simp [PrizeWorkbench.besselCoeff]

/-- Splitting off the first coordinate:
`besselCoeff (d+1) r = Σ_{j ≤ r} I0c j · besselCoeff d (r − j)`. -/
theorem besselCoeff_succ_left (d r : ℕ) :
    PrizeWorkbench.besselCoeff (d + 1) r =
      ∑ j ∈ range (r + 1), AvW0.I0c j * PrizeWorkbench.besselCoeff d (r - j) := by
  unfold PrizeWorkbench.besselCoeff
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x ↦ ⟨x 0, Fin.tail x⟩) (fun p ↦ Fin.cons p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple, Fin.tail]
    exact ⟨by omega, by omega⟩
  · intro p hp
    rw [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] at hp
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_cons, hp.2]
    omega
  · intro x _
    exact Fin.cons_self_tail x
  · intro p _
    simp
  · intro x _
    rw [Fin.prod_univ_succ]
    rfl

/-- **The multinomial Bessel coefficient is the convolution power**:
`besselCoeff d r = cpow I0c d r`. -/
theorem besselCoeff_eq_avW0_cpow (d r : ℕ) :
    PrizeWorkbench.besselCoeff d r = AvW0.cpow AvW0.I0c d r := by
  induction d generalizing r with
  | zero => simp only [besselCoeff_zero_left, AvW0.cpow]
  | succ d ih =>
    rw [besselCoeff_succ_left, AvW0.decoupling_convolution]
    simp only [ih]

/-- `besselCoeff d r` in the `AvNT` encoding. -/
theorem besselCoeff_eq_avNT_cpow (d r : ℕ) :
    PrizeWorkbench.besselCoeff d r =
      AvNTCumulantEngine.cpow AvNTCumulantEngine.besselCoeff d r := by
  rw [besselCoeff_eq_avW0_cpow, avW0_cpow_eq_avNT_cpow, i0c_eq_besselCoeff]

/-- `AvW0.Edef r m = (2r)!·besselCoeff m r`. -/
theorem edef_eq_besselCoeff (r m : ℕ) :
    AvW0.Edef r m = ((2 * r).factorial : ℚ) * PrizeWorkbench.besselCoeff m r := by
  rw [besselCoeff_eq_avW0_cpow]
  rfl

/-! ### The step law on the multinomial coefficient and the Wick-normalised moment -/

/-- **The char-0 step law for the multinomial Bessel coefficient, every depth.**
`besselCoeff d` has log-derivative index `≤ d`: `(r+1)·besselCoeff d (r+1) ≤ d·besselCoeff d r`
for every `r`. -/
theorem besselCoeff_logDerivIndex (d : ℕ) :
    AvNTCumulantEngine.LogDerivIndex (PrizeWorkbench.besselCoeff d) d := by
  rw [show PrizeWorkbench.besselCoeff d =
      AvNTCumulantEngine.cpow AvNTCumulantEngine.besselCoeff d from
    funext (besselCoeff_eq_avNT_cpow d)]
  exact AvNTCumulantEngine.besselPow_logDerivIndex d

/-- **The step ratio is at most `1` at every depth.** For `d ≥ 1`, `Rstep d r ≤ 1` for every `r`,
the conclusion of `PrizeWorkbench.char0_W3anti_of_sharpNewton` without `SharpNewtonBessel d`.
This does not give the antitonicity `Rstep d (r+1) ≤ Rstep d r`. -/
theorem rstep_le_one {d : ℕ} (hd : 1 ≤ d) (r : ℕ) : PrizeWorkbench.Rstep d r ≤ 1 := by
  have hc := PrizeWorkbench.besselCoeff_pos hd r
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [PrizeWorkbench.R_eq hd r, div_le_one (mul_pos hd' hc)]
  have h := besselCoeff_logDerivIndex d r
  push_cast
  linarith

/-- The Wick-normalised moment is non-increasing in the depth: `mNorm d (r+1) ≤ mNorm d r`. -/
theorem mNorm_succ_le {d : ℕ} (hd : 1 ≤ d) (r : ℕ) :
    PrizeWorkbench.mNorm d (r + 1) ≤ PrizeWorkbench.mNorm d r := by
  have h := rstep_le_one hd r
  rwa [PrizeWorkbench.Rstep, div_le_one (PrizeWorkbench.mNorm_pos hd r)] at h

/-- `mNorm m r` is the deficit ratio of the char-0 energy:
`Edef r m = (2r−1)‼·(2m)^r·mNorm m r` for `m ≥ 1`. -/
theorem edef_eq_wick_mul_mNorm {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    AvW0.Edef r m =
      (Nat.doubleFactorial (2 * r - 1) : ℚ) * (2 * m) ^ r * PrizeWorkbench.mNorm m r := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hfac : ((2 * r).factorial : ℚ) =
      (Nat.doubleFactorial (2 * r - 1) : ℚ) * (2 ^ r * r.factorial) := by
    exact_mod_cast ArkLib.ProximityGap.NegationClosedWalk.two_mul_factorial_eq r
  rw [edef_eq_besselCoeff, PrizeWorkbench.mNorm, hfac]
  field_simp
  ring

/-- **`hdanti` holds for the char-0 energy.** For `m ≥ 1`, `E_k = Edef k m`, the Wick moment
`W_k = (2k−1)‼·(2m)^k` and the deficit `d_k = mNorm m k` satisfy every hypothesis of
`CharZeroBackbone.energy_ratio_le_of_deficit_antitone`; the deficit hypothesis `hdanti` is
`mNorm_succ_le`. The conclusion is `E_{r+1} ≤ (2r+1)·(2m)·E_r`. -/
theorem charZero_backbone {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (AvW0.Edef (r + 1) m : ℝ) ≤ (2 * (r : ℝ) + 1) * (2 * m) * (AvW0.Edef r m : ℝ) := by
  refine CharZeroBackbone.energy_ratio_le_of_deficit_antitone
    (fun k ↦ (AvW0.Edef k m : ℝ))
    (fun k ↦ (Nat.doubleFactorial (2 * k - 1) : ℝ) * (2 * m) ^ k)
    (fun k ↦ (PrizeWorkbench.mNorm m k : ℝ)) (2 * m) r ?_ ?_ ?_ ?_ ?_ ?_
  · intro k
    rw [edef_eq_wick_mul_mNorm hm k]
    push_cast
    ring
  · intro k
    rw [ArkLib.ProximityGap.CrossStepCeiling.doubleFactorial_step k]
    push_cast
    ring
  · positivity
  · positivity
  · exact_mod_cast (PrizeWorkbench.mNorm_pos hm (r + 1)).le
  · exact_mod_cast mNorm_succ_le hm r

/-! ### The step law on the char-0 energy -/

/-- **The char-0 Gaussian step law on `Edef`, every depth.**
`Edef (r+1) m ≤ (2r+1)·(2m)·Edef r m` for every `r` and `m`. -/
theorem edef_succ_le (r m : ℕ) :
    AvW0.Edef (r + 1) m ≤ (2 * (r : ℚ) + 1) * (2 * m) * AvW0.Edef r m := by
  rw [edef_eq_avNT, edef_eq_avNT, show 2 * (r + 1) = 2 * r + 2 by ring]
  exact AvNTCumulantEngine.besselPow_energyStep m r

section HalfBasis

open ArkLib.ProximityGap.NegationClosedWalk (zeroSumCount)
open ArkLib.ProximityGap.Frontier.Step1Bessel (unionFold)
open ArkLib.ProximityGap.Frontier.LamLeungGeometric
  (antipodalDir halfBasis bessel_identity_halfBasis)

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- The char-0 energy of `μ_n`, `n = 2^{μ'+1}`, written as the `2r`-term zero-sum count of the
union of its antipodal directions `{±ζ^j}`, is `(2r)!·besselCoeff (n/2) r`. -/
theorem energy_eq_besselCoeff_halfBasis {μ' : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1)))
    (r : ℕ) :
    (zeroSumCount (unionFold ((halfBasis ζ μ').map antipodalDir)) (2 * r) : ℚ) =
      ((2 * r).factorial : ℚ) * PrizeWorkbench.besselCoeff (2 ^ μ') r := by
  rw [bessel_identity_halfBasis hζ r, edef_eq_besselCoeff]

/-- **The char-0 Gaussian step law on the energy of `μ_n`, every depth.** With
`E_r = zeroSumCount (⋃_j {±ζ^j}) (2r)` and `n = 2^{μ'+1}`, `E_{r+1} ≤ (2r+1)·n·E_r`. -/
theorem energy_succ_le_halfBasis {μ' : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1)))
    (r : ℕ) :
    zeroSumCount (unionFold ((halfBasis ζ μ').map antipodalDir)) (2 * (r + 1)) ≤
      (2 * r + 1) * 2 ^ (μ' + 1) *
        zeroSumCount (unionFold ((halfBasis ζ μ').map antipodalDir)) (2 * r) := by
  have h := edef_succ_le r (2 ^ μ')
  rw [← bessel_identity_halfBasis hζ (r + 1), ← bessel_identity_halfBasis hζ r] at h
  have e : (2 * (r : ℚ) + 1) * (2 * ((2 ^ μ' : ℕ) : ℚ)) =
      (((2 * r + 1) * 2 ^ (μ' + 1) : ℕ) : ℚ) := by
    push_cast
    ring
  rw [e, ← Nat.cast_mul] at h
  exact_mod_cast h

/-- The named char-0 input `NT5WrapCrossSplit.Char0WickStep` holds at every depth for the char-0
energy ladder `E_k = zeroSumCount (⋃_j {±ζ^j}) (2k)` of `μ_n`, `n = 2^{μ'+1}`. -/
theorem char0WickStep_halfBasis {μ' : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (μ' + 1)))
    (r : ℕ) :
    NT5WrapCrossSplit.Char0WickStep (2 ^ (μ' + 1))
      (fun k ↦ zeroSumCount (unionFold ((halfBasis ζ μ').map antipodalDir)) (2 * k)) r := by
  have h : (zeroSumCount (unionFold ((halfBasis ζ μ').map antipodalDir)) (2 * (r + 1)) : ℤ) ≤
      (2 * r + 1) * 2 ^ (μ' + 1) *
        zeroSumCount (unionFold ((halfBasis ζ μ').map antipodalDir)) (2 * r) := by
    exact_mod_cast energy_succ_le_halfBasis hζ r
  unfold NT5WrapCrossSplit.Char0WickStep NT5WrapCrossSplit.crossC0
  push_cast
  linarith

end HalfBasis

/-! ### The cross-step rung at every depth -/

section CrossStep

open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The cross-step rung at every depth, under char-0 faithfulness.** Let `G` be a finite-field
set with `|G| = 2m` whose energies at depths `r` and `r+1` equal the char-0 values `Edef r m` and
`Edef (r+1) m`. Then `crossMass G r ≤ 2r·(2r−1)‼·|G|^(r+1)`, the depth-`r` instance of
`CrossStepCeiling.M3CrossStepBound`. The two energy equalities are hypotheses; this theorem
does not establish them in characteristic `p`. -/
theorem crossMass_le_of_charZero_faithful (G : Finset F) {m r : ℕ} (hG : G.card = 2 * m)
    (hE : (rEnergy G r : ℚ) = AvW0.Edef r m)
    (hE' : (rEnergy G (r + 1) : ℚ) = AvW0.Edef (r + 1) m) :
    crossMass G r ≤ 2 * r * Nat.doubleFactorial (2 * r - 1) * G.card ^ (r + 1) := by
  have hstep := edef_succ_le r m
  have hE0 : 0 ≤ AvW0.Edef r m := by
    rw [← hE]
    positivity
  have hcross : (crossMass G r : ℚ) = AvW0.Edef (r + 1) m - 2 * m * AvW0.Edef r m := by
    rw [← hE', ← hE, rEnergy_succ_crossMass G r, hG]
    push_cast
    ring
  have hle : (crossMass G r : ℚ) ≤ 2 * r * (2 * m) * AvW0.Edef r m := by
    rw [hcross]
    linarith
  have hfinal : (crossMass G r : ℚ) ≤
      ((2 * r * Nat.doubleFactorial (2 * r - 1) * G.card ^ (r + 1) : ℕ) : ℚ) := by
    calc (crossMass G r : ℚ) ≤ 2 * r * (2 * m) * AvW0.Edef r m := hle
      _ ≤ 2 * r * (2 * m) *
          ((Nat.doubleFactorial (2 * r - 1) : ℚ) * ((2 * m : ℕ) : ℚ) ^ r) :=
        mul_le_mul_of_nonneg_left (AvW0.charZero_wick_bound r m) (by positivity)
      _ = ((2 * r * Nat.doubleFactorial (2 * r - 1) * G.card ^ (r + 1) : ℕ) : ℚ) := by
        rw [hG]
        push_cast
        ring
  exact_mod_cast hfinal

end CrossStep

end ProximityGap.Frontier.CharZeroStepLawAllDepth

#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.avW0_cpow_eq_avNT_cpow
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.besselCoeff_eq_avW0_cpow
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.besselCoeff_logDerivIndex
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.rstep_le_one
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.mNorm_succ_le
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.edef_eq_wick_mul_mNorm
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.charZero_backbone
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.edef_succ_le
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.energy_eq_besselCoeff_halfBasis
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.energy_succ_le_halfBasis
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.char0WickStep_halfBasis
#print axioms ProximityGap.Frontier.CharZeroStepLawAllDepth.crossMass_le_of_charZero_faithful
