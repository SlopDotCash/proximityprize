/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# LANE RUNG3 (#466 round 18): the exact rung-3 (sixth-moment) decomposition of the
  diagonal-subtracted incidence tower

Setting: `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b s₀)`, rung 3 = `S₃^D ≤ q·15·Σ³`
(`Σ = ∑_{b∈H}‖η_b‖²`, Wick `(2·3−1)‼ = 15`), `D = {0} ∪ μ_n`.

## PROBE VERDICT (`probe_r18_rung3.py`, exact FFT, n = 8/16/32, deg = 2..256, β = 2..4)

* **Rung 3 holds in the β = 4 bulk (deg ≤ 64) with margin**: `S₃^D/(15qΣ³)` =
  0.08–0.44 at β = 4, deg ∈ {2,4}; rises with deg (0.74 at deg 8, 0.86 at deg 32) and
  **crosses 1 at deg = 128 (1.27) and deg = 256 (2.05), n = 16, p = 65537** — the same
  thin-`H` refutation regime R16 found for r = 2/3; constant-15 is bulk-only, like constant-3
  at r = 2.
* **The 2/5 diagonal law is exact**: matched-multiset sextuples contribute
  `q·(6Σ³ − 9Σ·Q₂ + 4Q₃)` (`Q_k = ∑_{b∈H}‖η_b‖^{2k}`), measured `/Wick → 0.4000` at every
  cell — the r = 3 mirror of R16's r = 2 `2/3` law: `r!/(2r−1)‼ = 6/15 = 2/5`.
* **The banked-`E₃(μ_n)` (all-equal-coset) slice is NEGLIGIBLE**: its Wick fraction decays
  like `~ M⁶·#cosets/(15Σ³)` (measured `10⁻⁴`–`10⁻⁸` at β ≥ 3.5). So the Problem-A fixed-r
  ladder (E₃(μ_n) banked) does NOT carry the rung: the open mass lives in CROSS-coset,
  non-matching coset patterns. The hoped-for reduction "rung r of B = E_r(μ_n) + Weil +
  small" FAILS quantitatively — the tower-welding hope is dead in this direct form.
* **The deficit is exactly a factor `n` at β = 4**: rung r is Weil-closable iff
  `n^r ≲ √p`; at r = 3 the non-degenerate-sextuple Weil error is `~ n⁶√p` against main
  `~ q·n³`, overshoot `n³/√p = n^{3−β/2} = n` at β = 4 (probe column: 7.97/16.00/32.00 for
  n = 8/16/32). r = 2 was the last Weil-closable rung (R17); rung 3 needs one full factor-n
  saving on the cross-coset sextuple set beyond square-root cancellation.

## What THIS file proves (all pure finite algebra, no analysis, no Weil)

* `parseval_offsets` — general offset-Parseval: for ANY weight `w : F → ℂ`,
  `∑_{s₀}‖∑_d w d·ψ(d s₀)‖² = q·∑_d ‖w d‖²` (the R13/R15 second-moment identity with the
  `H`-restricted `conj η` weight generalized to arbitrary weights; this is the engine).
* `incidenceSum_cube_eq` — `I_H(s₀)³ = ∑_{d∈F} cubeWeight(d)·ψ(d s₀)` where
  `cubeWeight(d) = ∑_{b₁,b₂,b₃∈H, b₁+b₂+b₃=d} conj(η_{b₁})conj(η_{b₂})conj(η_{b₃})` — the
  cube of the incidence field is itself a (weighted) character transform, with weight the
  η-weighted triple additive convolution of `H`.
* `sixthMoment_eq_cubeWeight_energy` — the EXACT rung-3 master identity
  `∑_{s₀∈F} ‖I_H(s₀)‖⁶ = q·∑_{d∈F} ‖cubeWeight(d)‖²`: the full sixth moment IS the
  η-weighted sextuple additive energy of `H`, with zero slack. Rung 3 is therefore exactly
  the statement `∑_d ‖cubeWeight d‖² ≤ 15·Σ³ + (diagonal mass)/q`.
* `sixthMomentAway_eq` — the diagonal-subtracted form:
  `S₃^D = q·∑_d ‖cubeWeight d‖² − ∑_{s₀∈D}‖I_H(s₀)‖⁶` for any `D ⊆ F`.
* `tripleCount_smul_eq` — dilation invariance of the all-equal-coset slice: for `t ≠ 0`
  the sextuple count on the coset `t·μ_n` equals `E₃(μ_n)` verbatim (why the banked
  Problem-A object appears at every coset with the SAME value).
* `wick_pairing_constants` — `3! = 6`, `(2·3−1)‼ = 15`: the diagonal fraction is `2/5`
  (the measured 0.4000).

## Honest scope

Nothing here bounds anything: these are exact reindexing identities that pin WHERE the
rung-3 analytic content lives (the cross-coset mass of `‖cubeWeight‖²` off the matched
multisets), plus probe calibration. The rung itself (constant 15, bulk) remains OPEN, and is
probe-FALSE for thin `H` (deg ≥ 128 at n = 16). Issue #466, round 18, LANE RUNG3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lane-local copy of the signed incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b·s₀)`
(kept local so this round-18 lane does not depend on frontier scratch oleans that carry
in-flight edits). Definitionally equal to the R15/R16/R17 `incidenceSum`. -/
noncomputable def incidenceSum (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) : ℂ :=
  ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

/-- The η-weighted triple additive convolution of `H`:
`cubeWeight(d) = ∑_{b₁,b₂,b₃ ∈ H, b₁+b₂+b₃ = d} conj(η_{b₁})·conj(η_{b₂})·conj(η_{b₃})`. -/
noncomputable def cubeWeight (ψ : AddChar F ℂ) (G H : Finset F) (d : F) : ℂ :=
  ∑ b₁ ∈ H, ∑ b₂ ∈ H, ∑ b₃ ∈ H,
    if b₁ + b₂ + b₃ = d then
      (starRingEnd ℂ) (eta ψ G b₁) * (starRingEnd ℂ) (eta ψ G b₂)
        * (starRingEnd ℂ) (eta ψ G b₃)
    else 0

/-! ### (1) The engine: offset-Parseval for an arbitrary weight. -/

/-- **General offset-Parseval.** For any weight `w : F → ℂ` and primitive `ψ`,
`∑_{s₀} ‖∑_d w d · ψ(d·s₀)‖² = q · ∑_d ‖w d‖²`. -/
theorem parseval_offsets {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (w : F → ℂ) :
    (∑ s₀ : F, ‖∑ d : F, w d * ψ (d * s₀)‖ ^ 2)
      = (Fintype.card F : ℝ) * ∑ d : F, ‖w d‖ ^ 2 := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  set T : F → ℂ := fun s₀ => ∑ d : F, w d * ψ (d * s₀) with hT
  have hconjT : ∀ s₀ : F, (starRingEnd ℂ) (T s₀) = ∑ d' : F, (starRingEnd ℂ) (w d') * ψ (-(d' * s₀)) := by
    intro s₀
    rw [hT, map_sum]
    refine Finset.sum_congr rfl (fun d' _ => ?_)
    rw [map_mul, hconj (d' * s₀)]
  have hcomplex : (∑ s₀ : F, T s₀ * (starRingEnd ℂ) (T s₀))
      = (Fintype.card F : ℂ) * ∑ d : F, w d * (starRingEnd ℂ) (w d) := by
    calc ∑ s₀ : F, T s₀ * (starRingEnd ℂ) (T s₀)
        = ∑ s₀ : F, ∑ d : F, ∑ d' : F,
            (w d * (starRingEnd ℂ) (w d')) * ψ (s₀ * (d - d')) := by
          refine Finset.sum_congr rfl (fun s₀ _ => ?_)
          rw [hconjT s₀, hT]
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          refine Finset.sum_congr rfl (fun d' _ => ?_)
          have hpsi : ψ (d * s₀) * ψ (-(d' * s₀)) = ψ (s₀ * (d - d')) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1; ring
          calc w d * ψ (d * s₀) * ((starRingEnd ℂ) (w d') * ψ (-(d' * s₀)))
              = (w d * (starRingEnd ℂ) (w d')) * (ψ (d * s₀) * ψ (-(d' * s₀))) := by ring
            _ = (w d * (starRingEnd ℂ) (w d')) * ψ (s₀ * (d - d')) := by rw [hpsi]
      _ = ∑ d : F, ∑ d' : F,
            (w d * (starRingEnd ℂ) (w d')) * ∑ s₀ : F, ψ (s₀ * (d - d')) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun d' _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ d : F, (w d * (starRingEnd ℂ) (w d)) * (Fintype.card F : ℂ) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          have hd' : ∀ d' ∈ (Finset.univ : Finset F),
              (w d * (starRingEnd ℂ) (w d')) * ∑ s₀ : F, ψ (s₀ * (d - d'))
                = (if d' = d then
                    (w d * (starRingEnd ℂ) (w d')) * (Fintype.card F : ℂ) else 0) := by
            intro d' _
            rw [AddChar.sum_mulShift (d - d') hψ]
            by_cases h : d = d'
            · subst h; simp
            · have hne : d - d' ≠ 0 := sub_ne_zero.mpr h
              rw [if_neg hne, if_neg (fun h' => h h'.symm)]
              simp
          rw [Finset.sum_congr rfl hd',
            Finset.sum_ite_eq' Finset.univ d
              (fun d' => (w d * (starRingEnd ℂ) (w d')) * (Fintype.card F : ℂ))]
          simp
      _ = (Fintype.card F : ℂ) * ∑ d : F, w d * (starRingEnd ℂ) (w d) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          ring
  have hcast : ((∑ s₀ : F, ‖T s₀‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * ∑ d : F, ((‖w d‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    rw [show (∑ s₀ : F, ((‖T s₀‖ ^ 2 : ℝ) : ℂ))
          = ∑ s₀ : F, T s₀ * (starRingEnd ℂ) (T s₀) from
      Finset.sum_congr rfl (fun s₀ _ => by rw [RCLike.mul_conj]; norm_cast)]
    rw [hcomplex]
    refine congrArg _ (Finset.sum_congr rfl (fun d _ => ?_))
    rw [RCLike.mul_conj]; norm_cast
  have hreal : ((∑ s₀ : F, ‖T s₀‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * ∑ d : F, ‖w d‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-! ### (2) The cube of the incidence field is a character transform. -/

/-- Cube expansion of a finite sum. -/
theorem sum_cube {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ b ∈ s, f b) ^ 3 = ∑ b₁ ∈ s, ∑ b₂ ∈ s, ∑ b₃ ∈ s, f b₁ * f b₂ * f b₃ := by
  rw [pow_succ, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b₁ _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b₂ _ => ?_)
  rw [Finset.mul_sum]

/-- **`I_H(s₀)³ = ∑_d cubeWeight(d)·ψ(d·s₀)`**: the cubed incidence field is the character
transform of the η-weighted triple additive convolution of `H`. -/
theorem incidenceSum_cube_eq (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) :
    incidenceSum ψ G H s₀ ^ 3 = ∑ d : F, cubeWeight ψ G H d * ψ (d * s₀) := by
  classical
  unfold incidenceSum
  rw [sum_cube]
  unfold cubeWeight
  symm
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b₂ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b₃ _ => ?_)
  rw [Finset.sum_ite_eq (Finset.univ : Finset F) (b₁ + b₂ + b₃)
    (fun d => (starRingEnd ℂ) (eta ψ G b₁) * (starRingEnd ℂ) (eta ψ G b₂)
      * (starRingEnd ℂ) (eta ψ G b₃) * ψ (d * s₀))]
  rw [if_pos (Finset.mem_univ _)]
  have hpsi : ψ (b₁ * s₀) * ψ (b₂ * s₀) * ψ (b₃ * s₀) = ψ ((b₁ + b₂ + b₃) * s₀) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [← hpsi]; ring

/-! ### (3) The rung-3 master identity. -/

/-- **EXACT rung-3 master identity**:
`∑_{s₀∈F} ‖I_H(s₀)‖⁶ = q · ∑_{d∈F} ‖cubeWeight(d)‖²`.
The full sixth moment of the incidence field equals `q` times the η-weighted SEXTUPLE
additive energy of `H` (in convolution form), with zero slack. Rung 3 (`Wick 15`) is
exactly `∑_d ‖cubeWeight d‖² ≤ 15·Σ³ + (deleted diagonal mass)/q`. -/
theorem sixthMoment_eq_cubeWeight_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H : Finset F) :
    (∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 6)
      = (Fintype.card F : ℝ) * ∑ d : F, ‖cubeWeight ψ G H d‖ ^ 2 := by
  have h6 : ∀ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 6 = ‖incidenceSum ψ G H s₀ ^ 3‖ ^ 2 := by
    intro s₀; rw [norm_pow, ← pow_mul]
  calc (∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 6)
      = ∑ s₀ : F, ‖∑ d : F, cubeWeight ψ G H d * ψ (d * s₀)‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun s₀ _ => ?_)
        rw [h6 s₀, incidenceSum_cube_eq]
    _ = (Fintype.card F : ℝ) * ∑ d : F, ‖cubeWeight ψ G H d‖ ^ 2 :=
        parseval_offsets hψ (cubeWeight ψ G H)

/-- The diagonal-subtracted rung-3 moment in closed form: for any deleted set `D`,
`S₃^D = q·∑_d ‖cubeWeight d‖² − ∑_{s₀∈D} ‖I_H(s₀)‖⁶`. -/
theorem sixthMomentAway_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H D : Finset F) :
    (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 6)
      = (Fintype.card F : ℝ) * (∑ d : F, ‖cubeWeight ψ G H d‖ ^ 2)
        - ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ 6 := by
  have hsplit := Finset.sum_sdiff (f := fun s₀ => ‖incidenceSum ψ G H s₀‖ ^ 6)
    (Finset.subset_univ D)
  have hfull := sixthMoment_eq_cubeWeight_energy hψ G H
  linarith [hsplit, hfull]

/-! ### (3b) The exact analytic target for rung 3. -/

/-- The rung-3 cube-weight energy target.  This is the precise analytic statement left by the
exact Parseval/cube decomposition: bounding the η-weighted triple convolution by Wick scale
`15·Σ³` up to the deleted diagonal credit. -/
def CubeWeightRung3Energy (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  (Fintype.card F : ℝ) * (∑ d : F, ‖cubeWeight ψ G H d‖ ^ 2)
    ≤ 15 * (Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 3
      + ∑ s₀ ∈ D, ‖incidenceSum ψ G H s₀‖ ^ 6

/-- The diagonal-subtracted rung-3 Wick target for the lane-local incidence sum. -/
def IncidenceRung3Wick (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 6)
    ≤ 15 * (Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 3

/-- The exact consumer: the cube-weight energy target is equivalent to the desired deleted
rung-3 Wick bound after the diagonal credit is subtracted.  This isolates the true open analytic
content in the cross-coset sextuple energy of `cubeWeight`. -/
theorem incidenceRung3Wick_of_cubeWeightEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G H D : Finset F} (hE : CubeWeightRung3Energy ψ G H D) :
    IncidenceRung3Wick ψ G H D := by
  unfold CubeWeightRung3Energy IncidenceRung3Wick at *
  rw [sixthMomentAway_eq hψ G H D]
  linarith

/-- Conversely, any deleted rung-3 Wick bound gives the cube-weight energy target with exactly the
deleted diagonal credit.  Thus the energy target is not a stronger reformulation; it is the same
problem in the Fourier/convolution variables. -/
theorem cubeWeightEnergy_of_incidenceRung3Wick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G H D : Finset F} (hW : IncidenceRung3Wick ψ G H D) :
    CubeWeightRung3Energy ψ G H D := by
  unfold CubeWeightRung3Energy IncidenceRung3Wick at *
  rw [sixthMomentAway_eq hψ G H D] at hW
  linarith

/-- Equivalence form: the deleted rung-3 Wick target is exactly the cube-weight energy target.
This is the compact residual statement for the next attack. -/
theorem incidenceRung3Wick_iff_cubeWeightEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H D : Finset F) :
    IncidenceRung3Wick ψ G H D ↔ CubeWeightRung3Energy ψ G H D :=
  ⟨cubeWeightEnergy_of_incidenceRung3Wick hψ,
    incidenceRung3Wick_of_cubeWeightEnergy hψ⟩

/-! ### (4) The all-equal-coset slice carries `E₃(μ_n)` verbatim (dilation invariance). -/

/-- **Dilation invariance of the sextuple count.** For `t ≠ 0`, the number of sextuple
solutions on the dilated set `t·G` equals `E₃(G)`: the banked Problem-A object `E₃(μ_n)`
appears at every `H/μ_n`-coset with the SAME value (the probe shows this slice is
nevertheless a negligible fraction of the Wick budget — the open mass is cross-coset). -/
theorem tripleCount_smul_eq (G : Finset F) {t : F} (ht : t ≠ 0) :
    ((G ×ˢ G ×ˢ G) ×ˢ (G ×ˢ G ×ˢ G)).filter
        (fun x => t * x.1.1 + t * x.1.2.1 + t * x.1.2.2
          = t * x.2.1 + t * x.2.2.1 + t * x.2.2.2)
      = ((G ×ˢ G ×ˢ G) ×ˢ (G ×ˢ G ×ˢ G)).filter
        (fun x => x.1.1 + x.1.2.1 + x.1.2.2 = x.2.1 + x.2.2.1 + x.2.2.2) := by
  refine Finset.filter_congr (fun x _ => ?_)
  constructor
  · intro h
    have h' : t * (x.1.1 + x.1.2.1 + x.1.2.2) = t * (x.2.1 + x.2.2.1 + x.2.2.2) := by
      rw [mul_add, mul_add, mul_add, mul_add]; exact h
    exact mul_left_cancel₀ ht h'
  · intro h
    rw [← mul_add, ← mul_add, ← mul_add, ← mul_add, h]

/-! ### (5) The Wick-pairing constants: the measured 2/5 diagonal law. -/

/-- `3! = 6` perfect matchings between the three conjugated and three unconjugated slots,
against Wick `(2·3−1)‼ = 15` pairings: the diagonal (matched-multiset) fraction of the
rung-3 Wick budget is `6/15 = 2/5` — the probe's exact `0.4000`, mirroring the r = 2 law
`2!/3‼ = 2/3`. -/
theorem wick_pairing_constants :
    Nat.factorial 3 = 6 ∧ Nat.doubleFactorial (2 * 3 - 1) = 15 ∧
      ((Nat.factorial 3 : ℚ) / (Nat.doubleFactorial (2 * 3 - 1) : ℚ) = 2 / 5) := by
  refine ⟨rfl, rfl, ?_⟩
  have h1 : Nat.factorial 3 = 6 := rfl
  have h2 : Nat.doubleFactorial (2 * 3 - 1) = 15 := rfl
  rw [h1, h2]
  norm_num

end ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.parseval_offsets
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.incidenceSum_cube_eq
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.sixthMoment_eq_cubeWeight_energy
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.sixthMomentAway_eq
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.incidenceRung3Wick_of_cubeWeightEnergy
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.cubeWeightEnergy_of_incidenceRung3Wick
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.incidenceRung3Wick_iff_cubeWeightEnergy
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.tripleCount_smul_eq
#print axioms ArkLib.ProximityGap.Frontier.R18RungThreeDecomposition.wick_pairing_constants
