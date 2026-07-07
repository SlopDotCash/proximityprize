/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# LANE RECURSION (#466 round 19): the first working rung recursion — exact, tight split,
  and the proof that ALL the loss is Chebyshev (the sup re-enters as the fixed point)

Setting (R15–R18): `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b s₀)`, rung `r` of the corrected-B tower is
`S_r^D ≤ (2r−1)‼·q·Σ^r` with `D = {0} ∪ μ_n`, `Σ = ∑_{b∈H}‖η_b‖²`. Round 18 showed the rung-`r`
weight is the `r`-fold additive convolution of `w(b) = 1_H(b)·conj(η_b)` and that its Fourier
transform is `I_H` itself (self-reference).

## PROBE VERDICT (`probe_r19_recursion.py`, exact FFT, 16 cells: n ∈ {8,16}, m ∈ {2,4},
   p up to 65537 incl. the Fermat cell)

* **The convolution split is a TAUTOLOGY**: because the F_p Fourier transform diagonalizes
  convolution, every spectral (spike/away) splitting of the weight `w` reproduces the s-space
  splitting `∑_{s∈D} + ∑_{s∉D}` EXACTLY (proved below: `energy_split_pointwise` +
  `hat_conv`). Young/Hausdorff-Young at ℓ¹ level loses a factor `|H|` (hopeless). The ONLY
  non-tautological recursion inequality available is the sup-split
  `S_{r+1}^D ≤ (sup_{s∉D}‖I‖²)·S_r^D`.
* **The sup-split is nearly TIGHT**: measured loss `ρ_r = M²_away·S_{r−1}^D/S_r^D` is
  1.03–2.70 across ALL 16 cells (ρ₃ ≤ 2.70, ρ₄ ≤ 1.95), essentially flat in `p`
  (2.52→2.70 from p=12289 to 65537). A working rung recursion EXISTS and it is not lossy.
* **ALL the divergence is Chebyshev**: the provable input `M²_away ≤ √(S₂^D)` loses the factor
  `√(S₂^D)/M²_away` = 2.3 → 36.0 (growing ~`√q/7`), while the true `M²_away/Σ` = 1.7–12.4
  (`= o(√q)`, column `Λ/√q` → 0.024 at the Fermat cell). Total provable chain loss
  `(S₂^D)^{3/2}/S₃^D` = 2.8 → 90.8 ≈ `√q`·const.
* **The measured per-rung Wick multiplier is L ≤ 1**: `L_r := (S_r^D/S_{r−1}^D)/((2r−1)Σ)`
  is 0.19–0.99 in all 16 cells (W₂ > W₃ > W₄ every row) — the truth is SUB-Wick per rung in
  the bulk. So the prompt's "constant-L recursion" is TRUE empirically with L ≤ 1, but the
  provable L is `√(3q W₂)·Σ`-sized: the gap between them is exactly the sup bound.

## STRUCTURAL CONCLUSION (the honest fixed point)

The recursion between rungs exists, is exact, and is tight to a factor ≤ 2.7 — but its one
input, `M²_away`, is the prize object itself. The tower does not bootstrap: rung r feeds rung
r+1 ONLY through the sup, and the sup is what the tower was built to bound. This upgrades
R18's "self-referential" observation to a quantitative fixed-point statement: the entire
corrected-B tower (all rungs ≥ 3) is EQUIVALENT, up to a per-rung constant ≤ 3, to the single
statement `AwaySupBound C` below (sup_away ‖I‖² ≤ C·Σ). Countermodel-side: nothing here is
refuted; the recursion machinery is banked as exact theorems.

## What THIS file proves (all axiom-clean, no analysis, no Weil)

* `hat_conv` — the exact convolution/product law over F: the transform of `f ⋆ g` is the
  product of transforms (the algebra that makes every rung weight a convolution power).
* `weightHat_eq_incidenceSum` — `ŵ = I_H`: the rung-1 weight transforms to the incidence
  field itself (the self-reference, as a one-line theorem).
* `incidenceSum_pow_eq_convIter_hat` — `I_H(s₀)^{r+1} = Σ_d (w^{⋆(r+1)})(d)·ψ(d s₀)` for ALL
  r: every rung's weight is a convolution power of the SAME `w` (the recursion object).
* `energy_split_pointwise` — the spectral split is tautological: if the two spectral parts
  have disjoint supports, the sixth-moment (or any) energy splits EXACTLY additively — no
  inequality, hence no new information beyond the s-space split.
* `sup_split_recursion` — the exact unconditional rung recursion:
  `∀ B, (∀ s∉D, ‖I‖² ≤ B) → S_{r+1}^D ≤ B·S_r^D`.
* `away_sq_le_sqrt_S2` — the Chebyshev input: `‖I s‖² ≤ √(S₂^D)` for every away `s`.
* `rung_recursion_sqrt` / `rung3_le_S2_pow` — the provable (√q-lossy) chain:
  `S_{r+1}^D ≤ √(S₂^D)·S_r^D`, hence `S₃^D ≤ (S₂^D)^{3/2}`; with rung 2 at constant `C`:
  `S₃^D ≤ (3CqΣ²)^{3/2}` — per-rung loss `√q`, measured to be pure Chebyshev.
* `AwaySupBound` + `tower_of_awaySupBound` — the fixed-point collapse: the single Prop
  `sup_away ‖I‖² ≤ C·Σ` implies EVERY rung `S_{r+2}^D ≤ (CΣ)^r·S₂^D`; with `C ≤ 2r+1`-type
  constants this is the whole tower. The tower IS the sup bound.

## Honest scope

No unconditional rung is closed here. The theorems are exact algebra + one Chebyshev step;
the quantitative claims (ρ ≤ 2.7, L ≤ 1, Chebyshev = all the loss) are probe measurements at
n ≤ 16, p ≤ 65537, not theorems. The wall is untouched: it now has the sharper name
`AwaySupBound C` with `C = O(polylog q)` — which is the prize statement. Issue #466,
round 19, LANE RECURSION.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R19RungRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lane-local incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b·s₀)` (definitionally the
R15–R18 object; kept local to avoid depending on frontier scratch oleans). -/
noncomputable def incidenceSum (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) : ℂ :=
  ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

/-- The rung-1 weight `w(b) = 1_H(b)·conj(η_b)` on all of `F`. -/
noncomputable def weight (ψ : AddChar F ℂ) (G H : Finset F) (b : F) : ℂ :=
  if b ∈ H then (starRingEnd ℂ) (eta ψ G b) else 0

/-- Additive convolution over `F`: `(f ⋆ g)(d) = ∑_a f(a)·g(d − a)`. -/
noncomputable def conv (f g : F → ℂ) (d : F) : ℂ := ∑ a : F, f a * g (d - a)

/-- Iterated convolution powers of the rung-1 weight: `convIter 0 = w`,
`convIter (r+1) = (convIter r) ⋆ w`. The rung-(r+1) weight of the tower. -/
noncomputable def convIter (ψ : AddChar F ℂ) (G H : Finset F) : ℕ → F → ℂ
  | 0 => weight ψ G H
  | r + 1 => conv (convIter ψ G H r) (weight ψ G H)

/-- The diagonal-deleted rung moment `S_r^D = ∑_{s₀∉D} ‖I_H(s₀)‖^{2r}`. -/
noncomputable def rungMoment (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : ℝ :=
  ∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)

/-! ### (1) The recursion algebra: transforms of convolutions are products. -/

/-- **Exact convolution/product law.** For any `f g : F → ℂ` and any character point `s`,
`∑_d (f ⋆ g)(d)·ψ(d·s) = (∑_a f(a)·ψ(a·s))·(∑_b g(b)·ψ(b·s))`. -/
theorem hat_conv (ψ : AddChar F ℂ) (f g : F → ℂ) (s : F) :
    (∑ d : F, conv f g d * ψ (d * s))
      = (∑ a : F, f a * ψ (a * s)) * (∑ b : F, g b * ψ (b * s)) := by
  classical
  unfold conv
  calc ∑ d : F, (∑ a : F, f a * g (d - a)) * ψ (d * s)
      = ∑ d : F, ∑ a : F, f a * g (d - a) * ψ (d * s) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ a : F, ∑ d : F, f a * g (d - a) * ψ (d * s) := by
          rw [Finset.sum_comm]
    _ = ∑ a : F, ∑ b : F, f a * g b * ψ ((a + b) * s) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          let e : F ≃ F :=
            { toFun := fun d => d - a
              invFun := fun b => a + b
              left_inv := by intro d; ring
              right_inv := by intro b; ring }
          refine Fintype.sum_equiv e _ _ (fun d => ?_)
          have harg : a + (d - a) = d := by ring
          simp [e, harg]
    _ = ∑ a : F, ∑ b : F, (f a * ψ (a * s)) * (g b * ψ (b * s)) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have hψ : ψ ((a + b) * s) = ψ (a * s) * ψ (b * s) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1
            ring
          rw [hψ]
          ring
    _ = (∑ a : F, f a * ψ (a * s)) * (∑ b : F, g b * ψ (b * s)) := by
          rw [Finset.sum_mul_sum]

theorem rungMoment_nonneg (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) :
    0 ≤ rungMoment ψ G H D r :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

/-- **`ŵ = I_H`**: the transform of the rung-1 weight is the incidence field itself — the
R18 self-reference as a one-line theorem. -/
theorem weightHat_eq_incidenceSum (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) :
    (∑ b : F, weight ψ G H b * ψ (b * s₀)) = incidenceSum ψ G H s₀ := by
  classical
  unfold weight incidenceSum
  rw [← show Finset.univ.filter (fun b : F => b ∈ H) = H by
    ext b
    simp]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : b ∈ H
  · simp [hb]
  · simp [hb]

/-- **Every rung weight is a convolution power of the same `w`**:
`I_H(s₀)^{r+1} = ∑_d (w^{⋆(r+1)})(d)·ψ(d·s₀)` for every `r`. Rung `r+1` of the tower is
`q·‖w^{⋆(r+1)}‖₂²` (by offset-Parseval, R18) — the recursion object exists at all rungs. -/
theorem incidenceSum_pow_eq_convIter_hat (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) :
    ∀ r : ℕ, incidenceSum ψ G H s₀ ^ (r + 1)
      = ∑ d : F, convIter ψ G H r d * ψ (d * s₀)
  | 0 => by
      rw [pow_one, ← weightHat_eq_incidenceSum ψ G H s₀]
      rfl
  | r + 1 => by
      rw [pow_succ, incidenceSum_pow_eq_convIter_hat ψ G H s₀ r,
        ← weightHat_eq_incidenceSum ψ G H s₀]
      simp only [convIter]
      exact (hat_conv ψ (convIter ψ G H r) (weight ψ G H) s₀).symm

/-! ### (2) The split tautology: disjoint-support spectral splits are exact. -/

/-- **Spectral splits carry no inequality.** If two spectral parts `U`, `V` have disjoint
supports (`∀ s, U s = 0 ∨ V s = 0` — e.g. `U = Î·1_D`, `V = Î·1_{D^c}`), then for ANY
multiplier field `A` and any moment exponent `k ≥ 1` the energy splits EXACTLY additively.
Applied with `A = I_H^r`, `U + V = I_H`: the convolution (spike/away) split of the
rung-(r+1) weight is the s-space diagonal split verbatim — a tautology, not a new bound. -/
theorem energy_split_pointwise (A U V : F → ℂ) (k : ℕ) (hk : k ≠ 0)
    (h : ∀ s : F, U s = 0 ∨ V s = 0) :
    (∑ s : F, ‖A s * (U s + V s)‖ ^ k)
      = (∑ s : F, ‖A s * U s‖ ^ k) + ∑ s : F, ‖A s * V s‖ ^ k := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rcases h s with h0 | h0 <;> rw [h0] <;> simp [zero_pow hk]

/-! ### (3) The working rung recursion (exact, unconditional). -/

/-- **The sup-split rung recursion.** For any bound `B` on the away sup of `‖I_H‖²`,
`S_{r+1}^D ≤ B·S_r^D`. Probe: this step is tight to a factor ≤ 2.7 at the true
`B = M²_away` — the recursion itself is NOT where the loss is. -/
theorem sup_split_recursion (ψ : AddChar F ℂ) (G H D : Finset F) (B : ℝ)
    (hB : ∀ s ∈ Finset.univ \ D, ‖incidenceSum ψ G H s‖ ^ 2 ≤ B) (r : ℕ) :
    rungMoment ψ G H D (r + 1) ≤ B * rungMoment ψ G H D r := by
  unfold rungMoment
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have h1 : ‖incidenceSum ψ G H s‖ ^ (2 * (r + 1))
      = ‖incidenceSum ψ G H s‖ ^ 2 * ‖incidenceSum ψ G H s‖ ^ (2 * r) := by
    rw [← pow_add]; congr 1; ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hB s hs) (pow_nonneg (norm_nonneg _) _)

/-- **The Chebyshev input** (the lossy step, measured to carry ~all the `√q`):
every away value satisfies `‖I_H(s)‖² ≤ √(S₂^D)`. -/
theorem away_sq_le_sqrt_rung2 (ψ : AddChar F ℂ) (G H D : Finset F) {s : F}
    (hs : s ∈ Finset.univ \ D) :
    ‖incidenceSum ψ G H s‖ ^ 2 ≤ Real.sqrt (rungMoment ψ G H D 2) := by
  have h4 : ‖incidenceSum ψ G H s‖ ^ (2 * 2) ≤ rungMoment ψ G H D 2 :=
    Finset.single_le_sum (f := fun s => ‖incidenceSum ψ G H s‖ ^ (2 * 2))
      (fun i _ => pow_nonneg (norm_nonneg _) _) hs
  have hsq : (‖incidenceSum ψ G H s‖ ^ 2) ^ 2 ≤ rungMoment ψ G H D 2 := by
    rw [← pow_mul]; exact h4
  have hx : (0 : ℝ) ≤ ‖incidenceSum ψ G H s‖ ^ 2 := pow_nonneg (norm_nonneg _) _
  calc ‖incidenceSum ψ G H s‖ ^ 2
      = Real.sqrt ((‖incidenceSum ψ G H s‖ ^ 2) ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (rungMoment ψ G H D 2) := Real.sqrt_le_sqrt hsq

/-- The provable (√q-lossy) per-rung multiplier: `S_{r+1}^D ≤ √(S₂^D)·S_r^D` for every `r`. -/
theorem rungMoment_succ_le_sqrt (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) :
    rungMoment ψ G H D (r + 1)
      ≤ Real.sqrt (rungMoment ψ G H D 2) * rungMoment ψ G H D r :=
  sup_split_recursion ψ G H D _ (fun _ hs => away_sq_le_sqrt_rung2 ψ G H D hs) r

/-- Rung 3 from rung 2 alone: `S₃^D ≤ √(S₂^D)·S₂^D = (S₂^D)^{3/2}`. -/
theorem rung3_le_rung2_pow (ψ : AddChar F ℂ) (G H D : Finset F) :
    rungMoment ψ G H D 3
      ≤ Real.sqrt (rungMoment ψ G H D 2) * rungMoment ψ G H D 2 :=
  rungMoment_succ_le_sqrt ψ G H D 2

/-- Conditional form: if rung 2 holds at budget `K` (e.g. `K = 3C·q·Σ²`), then
`S₃^D ≤ √K·K = K^{3/2}` — explicit `√q` per-rung loss against the Wick target `15qΣ³`. -/
theorem rung3_of_rung2_bound (ψ : AddChar F ℂ) (G H D : Finset F) {K : ℝ}
    (hK2 : rungMoment ψ G H D 2 ≤ K) :
    rungMoment ψ G H D 3 ≤ Real.sqrt K * K := by
  have h0 := rungMoment_nonneg ψ G H D 2
  calc rungMoment ψ G H D 3
      ≤ Real.sqrt (rungMoment ψ G H D 2) * rungMoment ψ G H D 2 :=
        rung3_le_rung2_pow ψ G H D
    _ ≤ Real.sqrt K * K :=
        mul_le_mul (Real.sqrt_le_sqrt hK2) hK2 h0 (Real.sqrt_nonneg K)

/-! ### (4) The fixed point: the tower collapses to the sup bound. -/

/-- **The fixed-point Prop.** `sup_{s∉D} ‖I_H(s)‖² ≤ C·Σ`. Probe: TRUE at
`C = Λ ∈ [1.7, 12.4]` in all measured cells, with `Λ/√q → 0.024` at the Fermat cell.
For `C = O(polylog q)` this IS the prize statement. -/
def AwaySupBound (ψ : AddChar F ℂ) (G H D : Finset F) (C : ℝ) : Prop :=
  ∀ s ∈ Finset.univ \ D,
    ‖incidenceSum ψ G H s‖ ^ 2 ≤ C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2

/-- **The tower IS the sup bound**: `AwaySupBound C` implies every rung,
`S_{r+2}^D ≤ (C·Σ)^r·S₂^D`. Combined with the probe's tightness of the sup-split
(ρ ≤ 2.7), the corrected-B tower at all rungs ≥ 3 is equivalent (up to a per-rung
constant) to the single away-sup statement — the recursion's fixed point. -/
theorem tower_of_awaySupBound (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ}
    (hC : 0 ≤ C) (h : AwaySupBound ψ G H D C) :
    ∀ r : ℕ, rungMoment ψ G H D (r + 2)
      ≤ (C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r * rungMoment ψ G H D 2
  := by
  intro r
  induction r with
  | zero =>
      rw [pow_zero, one_mul]
  | succ r ih =>
      have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
      have hCS : (0 : ℝ) ≤ C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := mul_nonneg hC hSig
      have hstep : rungMoment ψ G H D (r + 2 + 1)
          ≤ (C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D (r + 2) :=
        sup_split_recursion ψ G H D _ h (r + 2)
      calc rungMoment ψ G H D (r + 1 + 2)
          = rungMoment ψ G H D (r + 2 + 1) := by norm_num
        _ ≤ (C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D (r + 2) := hstep
        _ ≤ (C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
              * ((C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r * rungMoment ψ G H D 2) :=
            mul_le_mul_of_nonneg_left ih hCS
        _ = (C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ (r + 1) * rungMoment ψ G H D 2 := by
            ring

end ArkLib.ProximityGap.Frontier.R19RungRecursion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.hat_conv
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.weightHat_eq_incidenceSum
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.incidenceSum_pow_eq_convIter_hat
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.energy_split_pointwise
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.sup_split_recursion
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.away_sq_le_sqrt_rung2
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.rungMoment_succ_le_sqrt
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.rung3_le_rung2_pow
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.rung3_of_rung2_bound
#print axioms ArkLib.ProximityGap.Frontier.R19RungRecursion.tower_of_awaySupBound
