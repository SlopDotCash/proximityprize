/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26BoundedResidual
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19ExplicitCharacterRung

/-!
# LANE RESL2 (#466 round 26): the bounded-residual subfamily gate — exact L² cross
# identity + the honest fourth-moment deficit

The r25 audit (`_R25SubfamilyGate`) reduced the thin-subfamily r = 2 rung at the ORIGINAL
hyperplane to controlling the omitted-character residual
`Res(s₀) = ∑_{χ' ∈ chiFamily χ \ Y} g(χ')·T_{χ'}(s₀)` (exact vanishing REFUTED).  This lane
asks: do SECOND moments of `Res` suffice for the rung's `S₂^D = ∑ ‖I_H‖⁴` bookkeeping?

## PROVEN here (axiom-clean)

1. **A NEW exact cross-χ second-moment identity** (`cross_second_moment`), probe-validated to
   `1e-13` (`scripts/probes/probe_r26_bounded_residual.py`): for nontrivial `χ' ≠ χ''`,
   `∑_{s₀∈F} T_{χ'}(s₀)·conj T_{χ''}(s₀) = K(χ',χ'')·∑_{x,y∈G} (χ'·conj χ'')(x−y)`,
   where `K(χ',χ'') = ∑_t χ'(t−1)·conj(χ''(t)) = χ'(−1)·J(χ', χ''⁻¹)` is a Jacobi-type
   kernel of EXACT modulus `√q` (`norm_crossKernel`, via `jacobiSum_mul_nontrivial` +
   `norm_gaussSum_eq_sqrt_card`).  This is the cross analogue of the r17 diagonal identity
   `∑‖T_χ‖² = nq − n²`; hence `‖cross‖ ≤ n²√q` (`norm_cross_second_moment_le`).
2. **The residual L² bound** (`sum_sq_norm_chiSubfamilyResidual_le`):
   `∑_{s₀∈F} ‖Res(s₀)‖² ≤ M·n·q² + M²·n²·q^{3/2}`, `M = |chiFamily χ \ Y|`, `n = |G|` —
   diagonal from r17, cross terms from (1).  Probe: bound holds with ratio 0.74–0.92 at
   regime cells; the L² average `‖Res‖² ≈ M·n·q` per offset is EXACTLY at the scale the
   rung budget needs.
3. **The L²×sup fourth-moment route, exact cost** (`residualQuarticWickAt_of_l2_sup`):
   with the trivial sup `‖Res(s₀)‖ ≤ M√q·n` this gives the named target
   `ResidualQuarticWickAt` at constant `C = 2Mn` (in the regime `Mn ≤ √q`).

## THE HONEST DEFICIT (the lane's main finding; numerics in the probes)

The rung budget is Wick's `C = 3`: `∑_{s₀∉D}‖Res‖⁴ ≤ C·q·(Mnq)²` composed by L⁴-Minkowski
against the proven main part fires iff (asymptotically)
`C^{1/4}·√M + Cw^{1/4}·(m'−1) ≤ 3^{1/4}·√m`.  So:
* L²×sup gives `C = 2Mn` — misses by the sup-vs-typical factor `≈ Mn/2` (measured
  overshoot 52×–2060×).  **Second moments alone do NOT suffice.**
* The ACTUAL residual fourth moment is Wick-scale but with measured constant
  `C_R = 2.88–2.99 → 3.0` (p = 65537, 786433; conjugation-closed omitted family behaves
  real-Gaussian, fourth moment 3) — EQUAL to the budget constant.  At `C_R = 3` the
  Minkowski condition reads `3^{1/4}(√m − √(m−m')) ≥ Cw^{1/4}(m'−1)`, impossible under the
  gate `15(m'−1)² ≤ m`.  Even so the measured TRUE `m⁴S₂^D / (3qΣ²m⁴) = 0.87` — the rung
  statement itself HOLDS at these cells, but every per-part norm split spends more than the
  whole budget.  **The open content is pinned as Main–Res joint cancellation (a genuine
  mixed-moment statement), not any per-part residual bound**: the next open Prop is
  `ResidualQuarticWickAt … C` with `C < 3` STRICTLY (numerically refuted-approaching, the
  measured constant tends to exactly 3) or, equivalently honest, a cross-term bound on
  `∑_{s₀∉D} ‖Main‖²·‖Res‖²`-type mixed moments.  No closure claimed.

Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 26.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)
open ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
open ArkLib.ProximityGap.Frontier.R26BoundedResidual

namespace ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable local instance : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-! ## 1. The Jacobi-type cross kernel and its exact `√q` modulus -/

/-- The cross kernel `K(χ',χ'') = ∑_t χ'(t−1)·conj(χ''(t))`.  Equals
`χ'(−1)·J(χ', χ''⁻¹)`; for nontrivial `χ' ≠ χ''` it has exact modulus `√q`. -/
noncomputable def crossKernel (χ' χ'' : MulChar F ℂ) : ℂ :=
  ∑ t : F, χ' (t - 1) * conj' (χ'' t)

/-- The cross kernel is a unit times a Jacobi sum. -/
theorem crossKernel_eq_jacobiSum (χ' χ'' : MulChar F ℂ) :
    crossKernel χ' χ'' = χ' (-1) * jacobiSum χ' χ''⁻¹ := by
  unfold crossKernel jacobiSum
  have hre : ∑ t : F, χ' (t - 1) * conj' (χ'' t)
      = ∑ u : F, χ' ((1 - u) - 1) * conj' (χ'' (1 - u)) := by
    refine Fintype.sum_equiv (Equiv.subLeft 1) _ _ fun u => ?_
    simp only [Equiv.subLeft_apply]
    rw [sub_sub_cancel]
  rw [hre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [conj_mulChar]
  have h1 : (1 : F) - u - 1 = -1 * u := by ring
  rw [h1, map_mul]
  ring

/-- **Exact Jacobi-sum modulus** over ℂ: for `χ`, `φ`, `χφ` all nontrivial,
`‖J(χ,φ)‖ = √q`. -/
theorem norm_jacobiSum_eq_sqrt_card {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖jacobiSum χ φ‖ = Real.sqrt (Fintype.card F) := by
  have hrel := jacobiSum_mul_nontrivial hχφ ψ
  have hnorm : ‖gaussSum (χ * φ) ψ‖ * ‖jacobiSum χ φ‖ = ‖gaussSum χ ψ‖ * ‖gaussSum φ ψ‖ := by
    rw [← norm_mul, ← norm_mul, hrel]
  rw [norm_gaussSum_eq_sqrt_card hχφ hψ, norm_gaussSum_eq_sqrt_card hχ hψ,
    norm_gaussSum_eq_sqrt_card hφ hψ] at hnorm
  have hqpos : (0 : ℝ) < Real.sqrt (Fintype.card F) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  exact mul_left_cancel₀ (ne_of_gt hqpos) hnorm

/-- **Exact cross-kernel modulus**: `‖K(χ',χ'')‖ = √q` for nontrivial `χ' ≠ χ''`. -/
theorem norm_crossKernel {χ' χ'' : MulChar F ℂ} (h1 : χ' ≠ 1) (h2 : χ'' ≠ 1)
    (hne : χ' ≠ χ'') {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖crossKernel χ' χ''‖ = Real.sqrt (Fintype.card F) := by
  rw [crossKernel_eq_jacobiSum, norm_mul]
  have hm1 : (-1 : F) ≠ 0 := by
    simp
  rw [norm_mulChar_eq_one_of_ne_zero χ' hm1, one_mul]
  exact norm_jacobiSum_eq_sqrt_card h1 (by rwa [Ne, inv_eq_one])
    (by rwa [Ne, mul_inv_eq_one]) hψ

/-! ## 2. THE NEW EXACT IDENTITY: cross-χ second moment over all offsets -/

/-- The complete shifted pair sum factors through the cross kernel at EVERY shift `c`
(including `c = 0`, where both sides vanish): for `χ' ≠ χ''`,
`∑_a χ'(a−c)·conj(χ''(a)) = χ'(c)·conj(χ''(c))·K(χ',χ'')`. -/
theorem shifted_pair_sum {χ' χ'' : MulChar F ℂ} (hne : χ' ≠ χ'') (c : F) :
    ∑ a : F, χ' (a - c) * conj' (χ'' a)
      = (χ' c * conj' (χ'' c)) * crossKernel χ' χ'' := by
  by_cases hc : c = 0
  · subst hc
    have h0 : χ' (0 : F) = 0 := χ'.map_nonunit (by simp)
    simp only [sub_zero, h0, zero_mul]
    exact sum_mulChar_mul_conj_eq_zero hne
  · have hre : ∑ a : F, χ' (a - c) * conj' (χ'' a)
        = ∑ t : F, χ' (c * t - c) * conj' (χ'' (c * t)) := by
      refine (Fintype.sum_equiv (Equiv.mulLeft₀ c hc)
        (fun t => χ' (c * t - c) * conj' (χ'' (c * t)))
        (fun a => χ' (a - c) * conj' (χ'' a)) fun t => ?_).symm
      simp only [Equiv.mulLeft₀_apply]
    rw [hre]
    unfold crossKernel
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : c * t - c = c * (t - 1) := by ring
    rw [h1, map_mul, map_mul, map_mul]
    ring

/-- **THE CROSS SECOND-MOMENT IDENTITY** (probe-validated to `1e-13`): for `χ' ≠ χ''`,
`∑_{s₀∈F} T_{χ'}(s₀)·conj(T_{χ''}(s₀)) = K(χ',χ'')·∑_{x,y∈G} χ'(x−y)·conj(χ''(x−y))`.
The diagonal `x = y` contributes `0` automatically (`χ'(0) = 0`).  This is the exact
cross-χ analogue of the r17 diagonal identity `∑‖T_χ‖² = nq − n²`. -/
theorem cross_second_moment {χ' χ'' : MulChar F ℂ} (hne : χ' ≠ χ'') (G : Finset F) :
    ∑ s₀ : F, shiftedCharSum χ' G s₀ * conj' (shiftedCharSum χ'' G s₀)
      = crossKernel χ' χ''
          * ∑ x ∈ G, ∑ y ∈ G, χ' (x - y) * conj' (χ'' (x - y)) := by
  classical
  have expand : ∀ s₀ : F, shiftedCharSum χ' G s₀ * conj' (shiftedCharSum χ'' G s₀)
      = ∑ x ∈ G, ∑ y ∈ G, χ' (s₀ - x) * conj' (χ'' (s₀ - y)) := by
    intro s₀
    rw [shiftedCharSum, shiftedCharSum, map_sum, Finset.sum_mul_sum]
  calc ∑ s₀ : F, shiftedCharSum χ' G s₀ * conj' (shiftedCharSum χ'' G s₀)
      = ∑ s₀ : F, ∑ x ∈ G, ∑ y ∈ G, χ' (s₀ - x) * conj' (χ'' (s₀ - y)) :=
        Finset.sum_congr rfl fun s₀ _ => expand s₀
    _ = ∑ x ∈ G, ∑ y ∈ G, ∑ s₀ : F, χ' (s₀ - x) * conj' (χ'' (s₀ - y)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ G, ∑ y ∈ G, (χ' (x - y) * conj' (χ'' (x - y))) * crossKernel χ' χ'' := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        have hsub : ∑ s₀ : F, χ' (s₀ - x) * conj' (χ'' (s₀ - y))
            = ∑ a : F, χ' (a - (x - y)) * conj' (χ'' a) := by
          refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun s₀ => ?_
          simp only [Equiv.subRight_apply]
          rw [show s₀ - y - (x - y) = s₀ - x from by ring]
        rw [hsub, shifted_pair_sum hne (x - y)]
    _ = crossKernel χ' χ''
          * ∑ x ∈ G, ∑ y ∈ G, χ' (x - y) * conj' (χ'' (x - y)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring

/-- Norm consequence: `‖∑_{s₀} T_{χ'}·conj T_{χ''}‖ ≤ n²·√q` for nontrivial `χ' ≠ χ''`. -/
theorem norm_cross_second_moment_le {χ' χ'' : MulChar F ℂ} (h1 : χ' ≠ 1) (h2 : χ'' ≠ 1)
    (hne : χ' ≠ χ'') {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ‖∑ s₀ : F, shiftedCharSum χ' G s₀ * conj' (shiftedCharSum χ'' G s₀)‖
      ≤ (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F) := by
  rw [cross_second_moment hne G, norm_mul, norm_crossKernel h1 h2 hne hψ]
  have hsum : ‖∑ x ∈ G, ∑ y ∈ G, χ' (x - y) * conj' (χ'' (x - y))‖ ≤ (G.card : ℝ) ^ 2 := by
    calc ‖∑ x ∈ G, ∑ y ∈ G, χ' (x - y) * conj' (χ'' (x - y))‖
        ≤ ∑ x ∈ G, ‖∑ y ∈ G, χ' (x - y) * conj' (χ'' (x - y))‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ G, ∑ y ∈ G, ‖χ' (x - y) * conj' (χ'' (x - y))‖ :=
          Finset.sum_le_sum fun x _ => norm_sum_le _ _
      _ ≤ ∑ _x ∈ G, ∑ _y ∈ G, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul]
          have ha := norm_mulChar_le_one χ' (x - y)
          have hb : ‖conj' (χ'' (x - y))‖ ≤ 1 := by
            rw [RingHomIsometric.norm_map]
            exact norm_mulChar_le_one χ'' (x - y)
          nlinarith [norm_nonneg (χ' (x - y)), norm_nonneg (conj' (χ'' (x - y)))]
      _ = (G.card : ℝ) ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          ring
  have hs : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  calc Real.sqrt (Fintype.card F) * ‖∑ x ∈ G, ∑ y ∈ G, χ' (x - y) * conj' (χ'' (x - y))‖
      ≤ Real.sqrt (Fintype.card F) * ((G.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hs
    _ = (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F) := by ring

/-! ## 3. The residual L² bound -/

/-- Twisted thin sums are pointwise at most `n = |G|`. -/
theorem norm_twistedThinSum_le_card (χ' : MulChar F ℂ) (G : Finset F) (s₀ : F) :
    ‖twistedThinSum χ' G s₀‖ ≤ (G.card : ℝ) := by
  calc ‖twistedThinSum χ' G s₀‖
      ≤ ∑ x ∈ G, ‖conj' (χ' (s₀ - x))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ G, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [RingHomIsometric.norm_map]
        exact norm_mulChar_le_one χ' (s₀ - x)
    _ = (G.card : ℝ) := by simp

/-- The trivial sup bound on the omitted-character residual:
`‖Res(s₀)‖ ≤ M·√q·n`, `M = |chiFamily χ \ Y|`. -/
theorem norm_chiSubfamilyResidual_le_trivial (χ : MulChar F ℂ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (Y : Finset (MulChar F ℂ)) (s₀ : F) :
    ‖chiSubfamilyResidual χ ψ G Y s₀‖
      ≤ ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F) * (G.card : ℝ) :=
  norm_chiSubfamilyResidual_le_card_mul χ hψ G Y s₀
    fun χ' _ => norm_twistedThinSum_le_card χ' G s₀

/-- **The residual L² bound** (from the r17 diagonal identity + the NEW cross identity):
`∑_{s₀∈F} ‖Res(s₀)‖² ≤ M·n·q² + M²·n²·q·√q`.
Probe (`probe_r26_bounded_residual.py`, `probe_r26_bigcell.py`): holds with ratio
0.74–0.92 at regime cells — the L² average `‖Res‖² ≈ Mnq` per offset is exactly the scale
the rung budget needs; the deficit lives entirely in the fourth moment. -/
theorem sum_sq_norm_chiSubfamilyResidual_le (χ : MulChar F ℂ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (Y : Finset (MulChar F ℂ)) :
    ∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2
      ≤ ((chiFamily χ \ Y).card : ℝ) * (G.card : ℝ) * (Fintype.card F : ℝ) ^ 2
        + ((chiFamily χ \ Y).card : ℝ) ^ 2 * (G.card : ℝ) ^ 2
            * (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F) := by
  classical
  set Ω : Finset (MulChar F ℂ) := chiFamily χ \ Y with hΩdef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hq0 : (0 : ℝ) ≤ q := by rw [hqdef]; positivity
  have hn0 : (0 : ℝ) ≤ n := by rw [hndef]; positivity
  -- the ℂ-valued bilinear expansion of the summed square
  have hcast : ∀ s₀ : F,
      ((‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2 : ℝ) : ℂ)
        = chiSubfamilyResidual χ ψ G Y s₀ * conj' (chiSubfamilyResidual χ ψ G Y s₀) := by
    intro s₀
    rw [RCLike.mul_conj]
    norm_cast
  have hbil : ((∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2 : ℝ) : ℂ)
      = ∑ c' ∈ Ω, ∑ c'' ∈ Ω, (gaussSum c' ψ * conj' (gaussSum c'' ψ))
          * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀) := by
    rw [Complex.ofReal_sum]
    calc ∑ s₀ : F, ((‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2 : ℝ) : ℂ)
        = ∑ s₀ : F, chiSubfamilyResidual χ ψ G Y s₀
            * conj' (chiSubfamilyResidual χ ψ G Y s₀) :=
          Finset.sum_congr rfl fun s₀ _ => hcast s₀
      _ = ∑ s₀ : F, ∑ c' ∈ Ω, ∑ c'' ∈ Ω,
            (gaussSum c' ψ * conj' (gaussSum c'' ψ))
              * (twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)) := by
          refine Finset.sum_congr rfl fun s₀ _ => ?_
          unfold chiSubfamilyResidual
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c'' _ => ?_
          rw [map_mul]
          ring
      _ = ∑ c' ∈ Ω, ∑ c'' ∈ Ω, (gaussSum c' ψ * conj' (gaussSum c'' ψ))
            * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c'' _ => by rw [Finset.mul_sum]
  -- diagonal and off-diagonal norms
  have hdiag : ∀ c' ∈ Ω,
      ‖(gaussSum c' ψ * conj' (gaussSum c' ψ))
          * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c' G s₀)‖
        ≤ q * (n * q) := by
    intro c' hc'
    have hc'fam : c' ∈ chiFamily χ := (Finset.mem_sdiff.mp hc').1
    have hc'1 : c' ≠ 1 := chiFamily_ne_one χ hc'fam
    have hg : ‖gaussSum c' ψ‖ = Real.sqrt q := by
      rw [hqdef]
      exact_mod_cast norm_gaussSum_eq_sqrt_card hc'1 hψ
    have htw : ∀ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c' G s₀)
        = ((‖twistedThinSum c' G s₀‖ ^ 2 : ℝ) : ℂ) := by
      intro s₀
      rw [RCLike.mul_conj]
      norm_cast
    have hsumtw : ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c' G s₀)
        = ((∑ s₀ : F, ‖twistedThinSum c' G s₀‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun s₀ _ => htw s₀
    have hval : ∑ s₀ : F, ‖twistedThinSum c' G s₀‖ ^ 2 ≤ n * q := by
      -- use the exact r17 identity: ∑‖T‖² = nq − n² ≤ nq
      have hid := sum_shiftedCharSum_mul_conj hc'1 G
      have hidr : ∑ s₀ : F, ‖shiftedCharSum c' G s₀‖ ^ 2 = n * q - n ^ 2 := by
        have hcast2 : ∀ s₀ : F,
            shiftedCharSum c' G s₀ * conj' (shiftedCharSum c' G s₀)
              = ((‖shiftedCharSum c' G s₀‖ ^ 2 : ℝ) : ℂ) := by
          intro s₀
          rw [RCLike.mul_conj]
          norm_cast
        have h2 : ((∑ s₀ : F, ‖shiftedCharSum c' G s₀‖ ^ 2 : ℝ) : ℂ)
            = ((n * q - n ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum, Finset.sum_congr rfl fun s₀ _ => (hcast2 s₀).symm, hid,
            hndef, hqdef]
          push_cast
          ring
        exact_mod_cast h2
      have heqn : ∑ s₀ : F, ‖twistedThinSum c' G s₀‖ ^ 2
          = ∑ s₀ : F, ‖shiftedCharSum c' G s₀‖ ^ 2 :=
        Finset.sum_congr rfl fun s₀ _ => by
          rw [norm_twistedThinSum_eq_shiftedCharSum]
      rw [heqn, hidr]
      nlinarith [sq_nonneg n]
    have hgc : ‖conj' (gaussSum c' ψ)‖ = Real.sqrt q := by
      rw [RingHomIsometric.norm_map, hg]
    have hnn : (0 : ℝ) ≤ ∑ s₀ : F, ‖twistedThinSum c' G s₀‖ ^ 2 := by
      positivity
    rw [hsumtw, norm_mul, norm_mul, hg, hgc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnn, Real.mul_self_sqrt hq0]
    exact mul_le_mul_of_nonneg_left hval hq0
  have hoff : ∀ c' ∈ Ω, ∀ c'' ∈ Ω, c'' ≠ c' →
      ‖(gaussSum c' ψ * conj' (gaussSum c'' ψ))
          * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)‖
        ≤ q * (n ^ 2 * Real.sqrt q) := by
    intro c' hc' c'' hc'' hnecc
    have hc'fam : c' ∈ chiFamily χ := (Finset.mem_sdiff.mp hc').1
    have hc''fam : c'' ∈ chiFamily χ := (Finset.mem_sdiff.mp hc'').1
    have hc'1 : c' ≠ 1 := chiFamily_ne_one χ hc'fam
    have hc''1 : c'' ≠ 1 := chiFamily_ne_one χ hc''fam
    -- the inner sum is the conjugate of the cross second moment
    have hconj : ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)
        = conj' (∑ s₀ : F, shiftedCharSum c' G s₀ * conj' (shiftedCharSum c'' G s₀)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun s₀ _ => ?_
      rw [twistedThinSum_eq_star_shiftedCharSum, twistedThinSum_eq_star_shiftedCharSum]
      simp only [Complex.star_def, map_mul, Complex.conj_conj]
    have hcross := norm_cross_second_moment_le hc'1 hc''1
      (fun h => hnecc (h.symm ▸ rfl)) hψ G
    have hcross' :
        ‖∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)‖
          ≤ n ^ 2 * Real.sqrt q := by
      rw [hconj, RingHomIsometric.norm_map]
      rw [hndef, hqdef]
      exact_mod_cast hcross
    have hg' : ‖gaussSum c' ψ‖ = Real.sqrt q := by
      rw [hqdef]
      exact_mod_cast norm_gaussSum_eq_sqrt_card hc'1 hψ
    have hg'' : ‖conj' (gaussSum c'' ψ)‖ = Real.sqrt q := by
      rw [RingHomIsometric.norm_map, hqdef]
      exact_mod_cast norm_gaussSum_eq_sqrt_card hc''1 hψ
    rw [norm_mul, norm_mul, hg', hg'', Real.mul_self_sqrt hq0]
    exact mul_le_mul_of_nonneg_left hcross' hq0
  -- assemble
  have hnonneg : (0 : ℝ) ≤ ∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2 := by
    positivity
  have hnorm_eq : ∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2
      = ‖((∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc ∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2
      = ‖((∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2 : ℝ) : ℂ)‖ := hnorm_eq
    _ = ‖∑ c' ∈ Ω, ∑ c'' ∈ Ω, (gaussSum c' ψ * conj' (gaussSum c'' ψ))
          * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)‖ := by
        rw [hbil]
    _ ≤ ∑ c' ∈ Ω, ‖∑ c'' ∈ Ω, (gaussSum c' ψ * conj' (gaussSum c'' ψ))
          * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ c' ∈ Ω, (q * (n * q) + ((Ω.card : ℝ) - 1) * (q * (n ^ 2 * Real.sqrt q))) := by
        refine Finset.sum_le_sum fun c' hc' => ?_
        have hsplit : ∑ c'' ∈ Ω, (gaussSum c' ψ * conj' (gaussSum c'' ψ))
              * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)
            = ((gaussSum c' ψ * conj' (gaussSum c' ψ))
                * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c' G s₀))
              + ∑ c'' ∈ Ω.erase c', (gaussSum c' ψ * conj' (gaussSum c'' ψ))
                * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀) :=
          (Finset.add_sum_erase Ω _ hc').symm
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have h1 := hdiag c' hc'
        have h2 : ‖∑ c'' ∈ Ω.erase c', (gaussSum c' ψ * conj' (gaussSum c'' ψ))
              * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)‖
            ≤ ((Ω.card : ℝ) - 1) * (q * (n ^ 2 * Real.sqrt q)) := by
          refine le_trans (norm_sum_le _ _) ?_
          have hcard : ((Ω.erase c').card : ℝ) = (Ω.card : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem hc']
            have : 1 ≤ Ω.card := Finset.card_pos.mpr ⟨c', hc'⟩
            push_cast [Nat.cast_sub this]
            ring
          calc ∑ c'' ∈ Ω.erase c', ‖(gaussSum c' ψ * conj' (gaussSum c'' ψ))
                * ∑ s₀ : F, twistedThinSum c' G s₀ * conj' (twistedThinSum c'' G s₀)‖
              ≤ ∑ _c'' ∈ Ω.erase c', q * (n ^ 2 * Real.sqrt q) := by
                refine Finset.sum_le_sum fun c'' hc'' => ?_
                exact hoff c' hc' c'' (Finset.mem_of_mem_erase hc'')
                  (Finset.ne_of_mem_erase hc'')
            _ = ((Ω.erase c').card : ℝ) * (q * (n ^ 2 * Real.sqrt q)) := by
                simp only [Finset.sum_const, nsmul_eq_mul]
            _ = ((Ω.card : ℝ) - 1) * (q * (n ^ 2 * Real.sqrt q)) := by rw [hcard]
        linarith
    _ = (Ω.card : ℝ) * (q * (n * q))
        + (Ω.card : ℝ) * (((Ω.card : ℝ) - 1) * (q * (n ^ 2 * Real.sqrt q))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (Ω.card : ℝ) * n * q ^ 2 + (Ω.card : ℝ) ^ 2 * n ^ 2 * q * Real.sqrt q := by
        have hM0 : (0 : ℝ) ≤ (Ω.card : ℝ) := Nat.cast_nonneg _
        have hsq0 : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hq0 (mul_nonneg (mul_nonneg hn0 hn0) hsq0)) hM0]

/-! ## 4. The named fourth-moment target and the exact cost of the L²×sup route -/

/-- **The named open Prop of the bounded-residual route** (round-26 pin): the omitted
-character residual obeys a Wick-scale fourth moment off the deleted set,
`∑_{s₀∉D} ‖Res(s₀)‖⁴ ≤ C·q·(M·n·q)²`.  The probes measure the TRUE constant
`C_R = 2.88–2.99 → 3.0` at regime cells (`probe_r26_bigcell.py`) — exactly the Wick
budget constant `3`; the L⁴-Minkowski composition of the rung fires only at `C < 3`
STRICTLY, so this Prop at `C < 3` is the precise (numerically refuted-approaching) open
residual, and any discharge must instead exploit Main–Res joint cancellation. -/
def ResidualQuarticWickAt (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (G D : Finset F) (Y : Finset (MulChar F ℂ)) (C : ℝ) : Prop :=
  ∑ s₀ ∈ Finset.univ \ D, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 4
    ≤ C * (Fintype.card F : ℝ)
        * (((chiFamily χ \ Y).card : ℝ) * (G.card : ℝ) * (Fintype.card F : ℝ)) ^ 2

/-- Generic L²×sup fourth-moment interpolation over a restricted offset set. -/
theorem sum_pow_four_le_sup_sq_mul_sum_sq (f : F → ℂ) (S : Finset F) {B : ℝ}
    (hB : ∀ s ∈ S, ‖f s‖ ≤ B) :
    ∑ s ∈ S, ‖f s‖ ^ 4 ≤ B ^ 2 * ∑ s : F, ‖f s‖ ^ 2 := by
  classical
  have hstep : ∑ s ∈ S, ‖f s‖ ^ 4 ≤ B ^ 2 * ∑ s ∈ S, ‖f s‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    have h1 := hB s hs
    have h0 := norm_nonneg (f s)
    have hsq : ‖f s‖ * ‖f s‖ ≤ B * B := mul_le_mul h1 h1 h0 (le_trans h0 h1)
    nlinarith [mul_nonneg h0 h0, hsq]
  refine le_trans hstep ?_
  have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  refine mul_le_mul_of_nonneg_left ?_ hB2
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun s _ _ => by positivity

/-- **The exact cost of the L²×sup route** (the lane's quantified deficit): in the regime
`M·n ≤ √q`, the trivial sup and the L² bound give `ResidualQuarticWickAt` at constant
`C = 2·M·n` — versus the Wick budget constant `3`.  The gap factor `2Mn/3` is EXACTLY the
sup-vs-typical loss (probe: overshoot 52×–2060×); second moments alone cannot close the
rung.  Any strengthening must lower `C` below `3` STRICTLY — which the measured true
constant (`→ 3.0`) says is impossible per-part: the residual alone saturates the whole
Wick budget, pinning the open content as a Main–Res mixed-moment statement. -/
theorem residualQuarticWickAt_of_l2_sup (χ : MulChar F ℂ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G D : Finset F) (Y : Finset (MulChar F ℂ))
    (hreg : ((chiFamily χ \ Y).card : ℝ) * (G.card : ℝ)
      ≤ Real.sqrt (Fintype.card F)) :
    ResidualQuarticWickAt χ ψ G D Y
      (2 * ((chiFamily χ \ Y).card : ℝ) * (G.card : ℝ)) := by
  classical
  set M : ℝ := ((chiFamily χ \ Y).card : ℝ) with hMdef
  set n : ℝ := (G.card : ℝ) with hndef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq0 : (0 : ℝ) ≤ q := by rw [hqdef]; positivity
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hn0 : (0 : ℝ) ≤ n := by rw [hndef]; positivity
  have hsq0 : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hsqq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
  unfold ResidualQuarticWickAt
  have hsup : ∀ s ∈ Finset.univ \ D,
      ‖chiSubfamilyResidual χ ψ G Y s‖ ≤ M * Real.sqrt q * n := by
    intro s _
    rw [hMdef, hndef, hqdef]
    exact_mod_cast norm_chiSubfamilyResidual_le_trivial χ hψ G Y s
  have hL2 : ∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2
      ≤ M * n * q ^ 2 + M ^ 2 * n ^ 2 * q * Real.sqrt q := by
    rw [hMdef, hndef, hqdef]
    exact_mod_cast sum_sq_norm_chiSubfamilyResidual_le χ hψ G Y
  have hmain := sum_pow_four_le_sup_sq_mul_sum_sq
    (fun s => chiSubfamilyResidual χ ψ G Y s) (Finset.univ \ D) hsup
  have hchain : (M * Real.sqrt q * n) ^ 2
        * ∑ s₀ : F, ‖chiSubfamilyResidual χ ψ G Y s₀‖ ^ 2
      ≤ (M * Real.sqrt q * n) ^ 2
        * (M * n * q ^ 2 + M ^ 2 * n ^ 2 * q * Real.sqrt q) :=
    mul_le_mul_of_nonneg_left hL2 (by positivity)
  refine le_trans hmain (le_trans hchain ?_)
  have hexp : (M * Real.sqrt q * n) ^ 2
        * (M * n * q ^ 2 + M ^ 2 * n ^ 2 * q * Real.sqrt q)
      = M ^ 3 * n ^ 3 * q ^ 3 + M ^ 4 * n ^ 4 * q ^ 2 * Real.sqrt q := by
    linear_combination (M ^ 3 * n ^ 3 * q ^ 2 + M ^ 4 * n ^ 4 * q * Real.sqrt q) * hsqq
  rw [hexp]
  have htarget : 2 * M * n * q * (M * n * q) ^ 2 = 2 * M ^ 3 * n ^ 3 * q ^ 3 := by ring
  rw [htarget]
  have hMnsq : M * n * Real.sqrt q ≤ q := by
    calc M * n * Real.sqrt q ≤ Real.sqrt q * Real.sqrt q :=
          mul_le_mul_of_nonneg_right hreg hsq0
      _ = q := hsqq
  have h2nd : M ^ 4 * n ^ 4 * q ^ 2 * Real.sqrt q ≤ M ^ 3 * n ^ 3 * q ^ 3 := by
    have hq2 : (0 : ℝ) ≤ q ^ 2 := by positivity
    calc M ^ 4 * n ^ 4 * q ^ 2 * Real.sqrt q
        = (M ^ 3 * n ^ 3) * (M * n * Real.sqrt q) * q ^ 2 := by ring
      _ ≤ (M ^ 3 * n ^ 3) * q * q ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hq2
          exact mul_le_mul_of_nonneg_left hMnsq (by positivity)
      _ = M ^ 3 * n ^ 3 * q ^ 3 := by ring
  linarith

end ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.crossKernel_eq_jacobiSum
#print axioms
  ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.norm_jacobiSum_eq_sqrt_card
#print axioms ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.norm_crossKernel
#print axioms ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.shifted_pair_sum
#print axioms ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.cross_second_moment
#print axioms
  ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.norm_cross_second_moment_le
#print axioms
  ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.sum_sq_norm_chiSubfamilyResidual_le
#print axioms
  ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.norm_chiSubfamilyResidual_le_trivial
#print axioms
  ArkLib.ProximityGap.Frontier.R26ResidualL2CrossIdentity.residualQuarticWickAt_of_l2_sup
