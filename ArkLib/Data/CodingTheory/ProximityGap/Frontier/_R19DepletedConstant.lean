/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17QuadrupleWeilRung

/-!
# LANE DEPLETED (#466 round 19): the depleted-Wick constant — the exact quadruple-family
  expansion replaces the Hölder step; the r = 2 rung constant drops from `K ≍ m²` to
  `K ≍ m`, and the `m`-uniform constant is PROBE-REFUTED for every absolute-mass route

## The round-17 `K(m) ≍ m²` drift, diagnosed

Round 17 closed the r = 2 rung at explicit constant `K(m) = 32(Cw(m−1)⁴ + 1)/m²` — blowing up
like `m²`.  The blow-up enters at EXACTLY one step: Hölder over the `m − 1` characters,
`‖∑_χ g(χ)T_χ‖⁴ ≤ (m−1)³ ∑_χ ‖g T_χ‖⁴`.  Probe `probe_r19_crossmoment.py` measures the Hölder
overshoot at `7.4 / 36 / 143` for `m = 4 / 8 / 16` — i.e. the loss is `≈ (m−1)²` on the nose,
and the TRUE χ-family fourth moment `∑_t ‖∑_χ g T_χ‖⁴ ≈ 3(m−1)²q²·n²q` has FULL square-root
cancellation across the character family (Wick scaling in the family size).

This file replaces Hölder by the EXACT quadruple expansion

  `∑_t ‖∑_χ g(χ)T_χ(t)‖⁴ = ∑_{χ₁,χ₂,χ₃,χ₄} g(χ₁)g(χ₂)·conj(g(χ₃)g(χ₄))·M(χ₁,χ₂,χ₃,χ₄)`,

  `M(χ₁,χ₂,χ₃,χ₄) = ∑_t T_{χ₁}T_{χ₂}·conj(T_{χ₃}T_{χ₄})`   (the `crossMoment`),

proven UNCONDITIONALLY below (`familyFourth_expansion`) — an identity, no Weil, no regime.
Everything then rides on the total quadruple mass `∑_{quads} ‖M‖`.

## What the probes say about the quadruple mass (honesty first)

Exact totals, `probe_r19_c4_exact.py` (12 cells, n = 16/32, β = 3.5–4.2, m = 4–32):

* **Paired quadruples** (`{χ₃,χ₄} = {χ₁,χ₂}`): per-pair `‖M‖ ≤ Cw·n²q` PROVEN here from
  `FourthMomentTwistBound` by pointwise AM–GM (`norm_crossMoment_paired_le`); paired total
  measured `2.06–2.60 × |X|²n²q` — the paired diagonal is `|X|²`-Wick, machine-checked
  consistent (`pairedDiagonal_le`).
* **Off-paired quadruples**: the max single `‖M‖` SATURATES `n²q` (ratio 0.98–1.03 at every
  probed cell) — NOT the Weil scale `n⁴√q` (they coincide exactly at β = 4; below β = 4 the
  binding scale is `n²q`).  ⟹ **no per-quadruple bound can beat `|X|⁴·n²q` total.**
* **The off-paired TOTAL scales like `|X|³`, not `|X|²`**: measured `off/(|X|²n²q)` GROWS
  `0.85 / 2.2 / 5.8 / 18.6` at `m = 4/8/16/32` (n = 16, β = 4) — roughly `∝ m` — while
  `off/(|X|³n²q)` is FLAT: `0.18–0.75` across ALL cells (decreasing in n and β; `≤ 0.39` at
  every n ≥ 32 cell).  Total `∑‖M‖/(|X|³n²q) ∈ [0.49, 1.44]`, flat.
  ⟹ **the `m`-uniform constant is UNREACHABLE by any triangle-after-expansion route**: the
  absolute quadruple mass genuinely carries a factor `|X|³`; recovering the true `|X|²` Wick
  level requires keeping the SIGNED quadruple sum (phase cancellation ACROSS quadruples) —
  the wall's signature move, now visible at the character-family level.

## What THIS file proves unconditionally (axiom-clean, no probe input)

1. `crossMoment` + `crossMoment_paired_eq` — the paired cross moment is a nonnegative real.
2. `norm_crossMoment_paired_le` — per-pair AM–GM: `‖M(χ,χ',χ,χ')‖ ≤ (E₄(χ)+E₄(χ'))/2`.
3. `pairedDiagonal_le` — the paired diagonal of the family sum obeys the `|X|²` Wick-family
   scaling given only `FourthMomentTwistBound` (no new input).
4. **`familyFourth_expansion`** — the EXACT identity above (the Hölder-free bookkeeping).
5. **`sum_norm_familySum_pow_four_le`** — `∑_t ‖∑_χ gT_χ‖⁴ ≤ q²·∑_{quads}‖M‖` from
   `GaussSumSizeBound` (triangle inequality AFTER the exact expansion).
6. **`awayMoment_two_mul_le_of_familyQuartic`** — the master bound
   `m⁴·S₂^D ≤ 8(q·n⁴ + q²·B)` for ANY quadruple-mass bound `B`.
7. **`r19_linearK_rung`** — the lane deliverable: under `FamilyQuarticCubicBound C₄`
   (the honest `|X|³` scaling), `hSig : nq ≤ 2mΣ` (PROVEN in `_R18SigmaEquidistribution`
   for `q ≥ 16m²n²`), `n² ≤ q`, `|X| ≤ m`:  `S₂^D ≤ 32(C₄+1)·m·q·Σ²` — the constant drops
   from the round-17 `≍ Cw·m²` to `≍ m`, with the residual `m` isolated in the single named
   family input.

## Named input (NOT proven here)

* `FamilyQuarticCubicBound` — `∑_{χ₁,χ₂,χ₃,χ₄∈X} ‖M‖ ≤ C₄·|X|³·n²·q`.  Probe-flat
  (`C₄ = 1.5` covers all 12 exact cells).  Its paired diagonal is proven consistent here
  (`pairedDiagonal_le` gives the paired part at the even stronger `|X|²` level); the open
  content is the off-paired total at `|X|³` — a family-level statement, strictly beyond
  per-quadruple Weil (see the probe facts above), strictly weaker than the true signed
  cancellation.

## Honest scope

This does NOT close the r = 2 rung unconditionally, does NOT derive the depleted constant
`C = 3` (R18 `DepletedWickR2` stays open: this route yields `K ≈ 32(C₄+1)·m`, far above 3),
and does NOT touch rungs ≥ 3 (the wall).  The countermodel-grade finding is negative and
sharp: the `m`-uniform K via absolute quadruple mass is IMPOSSIBLE (off-mass `∝ |X|³`), so
the remaining `m`-drift of the r = 2 chain is exactly the signed-vs-absolute gap of the
off-paired quadruple family.  CORE OPEN, ON-BGK.

Issue #466, round 19, lane DEPLETED.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung

namespace ArkLib.ProximityGap.Frontier.R19DepletedConstant

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (1) The quadruple cross moment -/

/-- The quadruple cross moment of the thin twisted sums:
`M(χ₁,χ₂,χ₃,χ₄) = ∑_t T_{χ₁}(t)·T_{χ₂}(t)·conj(T_{χ₃}(t))·conj(T_{χ₄}(t))`. -/
noncomputable def crossMoment (χ₁ χ₂ χ₃ χ₄ : MulChar F ℂ) (G : Finset F) : ℂ :=
  ∑ t : F, twistedThinSum χ₁ G t * twistedThinSum χ₂ G t
    * (starRingEnd ℂ) (twistedThinSum χ₃ G t) * (starRingEnd ℂ) (twistedThinSum χ₄ G t)

/-- The paired cross moment is the (real, nonnegative) mixed fourth moment
`∑_t ‖T_χ‖²‖T_{χ'}‖²`. -/
theorem crossMoment_paired_eq (χ χ' : MulChar F ℂ) (G : Finset F) :
    crossMoment χ χ' χ χ' G
      = ((∑ t : F, ‖twistedThinSum χ G t‖ ^ 2 * ‖twistedThinSum χ' G t‖ ^ 2 : ℝ) : ℂ) := by
  unfold crossMoment
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have h1 : twistedThinSum χ G t * (starRingEnd ℂ) (twistedThinSum χ G t)
      = ((‖twistedThinSum χ G t‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.mul_conj]; norm_cast
  have h2 : twistedThinSum χ' G t * (starRingEnd ℂ) (twistedThinSum χ' G t)
      = ((‖twistedThinSum χ' G t‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.mul_conj]; norm_cast
  calc twistedThinSum χ G t * twistedThinSum χ' G t
        * (starRingEnd ℂ) (twistedThinSum χ G t) * (starRingEnd ℂ) (twistedThinSum χ' G t)
      = (twistedThinSum χ G t * (starRingEnd ℂ) (twistedThinSum χ G t))
        * (twistedThinSum χ' G t * (starRingEnd ℂ) (twistedThinSum χ' G t)) := by ring
    _ = ((‖twistedThinSum χ G t‖ ^ 2 : ℝ) : ℂ)
        * ((‖twistedThinSum χ' G t‖ ^ 2 : ℝ) : ℂ) := by rw [h1, h2]
    _ = ((‖twistedThinSum χ G t‖ ^ 2 * ‖twistedThinSum χ' G t‖ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring

/-- Per-pair AM–GM: the paired cross moment is controlled by the two straight fourth
moments, `‖M(χ,χ',χ,χ')‖ ≤ (∑_t‖T_χ‖⁴ + ∑_t‖T_{χ'}‖⁴)/2` — no Cauchy–Schwarz loss, no new
input. -/
theorem norm_crossMoment_paired_le (χ χ' : MulChar F ℂ) (G : Finset F) :
    ‖crossMoment χ χ' χ χ' G‖
      ≤ (∑ t : F, ‖twistedThinSum χ G t‖ ^ 4
          + ∑ t : F, ‖twistedThinSum χ' G t‖ ^ 4) / 2 := by
  rw [crossMoment_paired_eq, Complex.norm_real]
  have hnn : (0 : ℝ) ≤ ∑ t : F, ‖twistedThinSum χ G t‖ ^ 2 * ‖twistedThinSum χ' G t‖ ^ 2 := by
    positivity
  rw [Real.norm_of_nonneg hnn]
  have hpt : ∀ t : F, ‖twistedThinSum χ G t‖ ^ 2 * ‖twistedThinSum χ' G t‖ ^ 2
      ≤ (‖twistedThinSum χ G t‖ ^ 4 + ‖twistedThinSum χ' G t‖ ^ 4) / 2 := by
    intro t
    nlinarith [sq_nonneg (‖twistedThinSum χ G t‖ ^ 2 - ‖twistedThinSum χ' G t‖ ^ 2)]
  calc ∑ t : F, ‖twistedThinSum χ G t‖ ^ 2 * ‖twistedThinSum χ' G t‖ ^ 2
      ≤ ∑ t : F, (‖twistedThinSum χ G t‖ ^ 4 + ‖twistedThinSum χ' G t‖ ^ 4) / 2 :=
        Finset.sum_le_sum (fun t _ => hpt t)
    _ = (∑ t : F, (‖twistedThinSum χ G t‖ ^ 4 + ‖twistedThinSum χ' G t‖ ^ 4)) / 2 := by
        rw [Finset.sum_div]
    _ = (∑ t : F, ‖twistedThinSum χ G t‖ ^ 4 + ∑ t : F, ‖twistedThinSum χ' G t‖ ^ 4) / 2 := by
        rw [Finset.sum_add_distrib]

/-- **Paired-diagonal consistency**: given only the round-17 Weil input
`FourthMomentTwistBound`, the paired diagonal of the quadruple family sum already obeys the
`|X|²` Wick-family scaling.  This shows the named `FamilyQuarticCubicBound` below asks for
new content ONLY on the off-paired part. -/
theorem pairedDiagonal_le (G : Finset F) (X : Finset (MulChar F ℂ)) {Cw : ℝ}
    (h4 : FourthMomentTwistBound G X Cw) :
    ∑ χ ∈ X, ∑ χ' ∈ X, ‖crossMoment χ χ' χ χ' G‖
      ≤ Cw * (X.card : ℝ) ^ 2 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  have hbound : ∀ χ ∈ X, ∀ χ' ∈ X, ‖crossMoment χ χ' χ χ' G‖
      ≤ Cw * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
    intro χ hχ χ' hχ'
    refine (norm_crossMoment_paired_le χ χ' G).trans ?_
    have h1 := h4 χ hχ
    have h2 := h4 χ' hχ'
    linarith
  calc ∑ χ ∈ X, ∑ χ' ∈ X, ‖crossMoment χ χ' χ χ' G‖
      ≤ ∑ _χ ∈ X, ∑ _χ' ∈ X, Cw * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
        refine Finset.sum_le_sum (fun χ hχ => Finset.sum_le_sum (fun χ' hχ' => ?_))
        exact hbound χ hχ χ' hχ'
    _ = Cw * (X.card : ℝ) ^ 2 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ### (2) The exact quadruple-family expansion (the Hölder replacement) -/

/-- Product-of-four-sums expansion over a common index set, in the `(p,p,r,r)` shape used by
the fourth moment: `(∑p)·(∑p)·(∑r)·(∑r) = ∑_{i,j,k,l} p_i·p_j·r_k·r_l`. -/
theorem sum_pow_two_mul_sum_pow_two {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p r : ι → ℂ) :
    (∑ i ∈ s, p i) * (∑ j ∈ s, p j) * (∑ k ∈ s, r k) * (∑ l ∈ s, r l)
      = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s, p i * p j * r k * r l := by
  calc (∑ i ∈ s, p i) * (∑ j ∈ s, p j) * (∑ k ∈ s, r k) * (∑ l ∈ s, r l)
      = ((∑ i ∈ s, p i) * (∑ j ∈ s, p j)) * ((∑ k ∈ s, r k) * (∑ l ∈ s, r l)) := by ring
    _ = (∑ i ∈ s, ∑ j ∈ s, p i * p j) * (∑ k ∈ s, ∑ l ∈ s, r k * r l) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ k ∈ s, (∑ j ∈ s, p i * p j) * (∑ l ∈ s, r k * r l) :=
        Finset.sum_mul_sum s s _ _
    _ = ∑ i ∈ s, ∑ k ∈ s, ∑ j ∈ s, ∑ l ∈ s, (p i * p j) * (r k * r l) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
        rw [Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s, p i * p j * r k * r l := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun l _ => by ring)))

/-- **The exact χ-family fourth-moment expansion** — an identity, no regime, no Weil:
`∑_t ‖∑_{χ∈X} g(χ)T_χ(t)‖⁴
   = ∑_{χ₁,χ₂,χ₃,χ₄∈X} g(χ₁)g(χ₂)·conj(g(χ₃))·conj(g(χ₄))·M(χ₁,χ₂,χ₃,χ₄)`. -/
theorem familyFourth_expansion (G : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) :
    ∑ t : F, ((‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4 : ℝ) : ℂ)
      = ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
          g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
            * crossMoment χ₁ χ₂ χ₃ χ₄ G := by
  classical
  -- pointwise expansion
  have hpt : ∀ t : F,
      ((‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4 : ℝ) : ℂ)
        = ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
            g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
              * (twistedThinSum χ₁ G t * twistedThinSum χ₂ G t
                * (starRingEnd ℂ) (twistedThinSum χ₃ G t)
                * (starRingEnd ℂ) (twistedThinSum χ₄ G t)) := by
    intro t
    set A : ℂ := ∑ χ ∈ X, g χ * twistedThinSum χ G t with hA
    have hsq : A * (starRingEnd ℂ) A = ((‖A‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    have h4 : ((‖A‖ ^ 4 : ℝ) : ℂ) = A * A * (starRingEnd ℂ) A * (starRingEnd ℂ) A := by
      have hc : ((‖A‖ ^ 4 : ℝ) : ℂ) = ((‖A‖ ^ 2 : ℝ) : ℂ) * ((‖A‖ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hc, ← hsq]; ring
    have hconjA : (starRingEnd ℂ) A
        = ∑ χ ∈ X, (starRingEnd ℂ) (g χ) * (starRingEnd ℂ) (twistedThinSum χ G t) := by
      rw [hA, map_sum]
      exact Finset.sum_congr rfl (fun χ _ => by rw [map_mul])
    rw [h4, hconjA, hA]
    rw [sum_pow_two_mul_sum_pow_two X (fun χ => g χ * twistedThinSum χ G t)
      (fun χ => (starRingEnd ℂ) (g χ) * (starRingEnd ℂ) (twistedThinSum χ G t))]
    refine Finset.sum_congr rfl (fun χ₁ _ => Finset.sum_congr rfl (fun χ₂ _ =>
      Finset.sum_congr rfl (fun χ₃ _ => Finset.sum_congr rfl (fun χ₄ _ => by ring_nf))))
  -- sum over t, then interchange the offset sum into the quadruple sums
  calc ∑ t : F, ((‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4 : ℝ) : ℂ)
      = ∑ t : F, ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
          g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
            * (twistedThinSum χ₁ G t * twistedThinSum χ₂ G t
              * (starRingEnd ℂ) (twistedThinSum χ₃ G t)
              * (starRingEnd ℂ) (twistedThinSum χ₄ G t)) :=
        Finset.sum_congr rfl (fun t _ => hpt t)
    _ = ∑ χ₁ ∈ X, ∑ t : F, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
          g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
            * (twistedThinSum χ₁ G t * twistedThinSum χ₂ G t
              * (starRingEnd ℂ) (twistedThinSum χ₃ G t)
              * (starRingEnd ℂ) (twistedThinSum χ₄ G t)) := Finset.sum_comm
    _ = ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ t : F, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
          g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
            * (twistedThinSum χ₁ G t * twistedThinSum χ₂ G t
              * (starRingEnd ℂ) (twistedThinSum χ₃ G t)
              * (starRingEnd ℂ) (twistedThinSum χ₄ G t)) :=
        Finset.sum_congr rfl (fun χ₁ _ => Finset.sum_comm)
    _ = ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ t : F, ∑ χ₄ ∈ X,
          g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
            * (twistedThinSum χ₁ G t * twistedThinSum χ₂ G t
              * (starRingEnd ℂ) (twistedThinSum χ₃ G t)
              * (starRingEnd ℂ) (twistedThinSum χ₄ G t)) :=
        Finset.sum_congr rfl (fun χ₁ _ => Finset.sum_congr rfl (fun χ₂ _ =>
          Finset.sum_comm))
    _ = ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X, ∑ t : F,
          g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
            * (twistedThinSum χ₁ G t * twistedThinSum χ₂ G t
              * (starRingEnd ℂ) (twistedThinSum χ₃ G t)
              * (starRingEnd ℂ) (twistedThinSum χ₄ G t)) :=
        Finset.sum_congr rfl (fun χ₁ _ => Finset.sum_congr rfl (fun χ₂ _ =>
          Finset.sum_congr rfl (fun χ₃ _ => Finset.sum_comm)))
    _ = ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
          g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
            * crossMoment χ₁ χ₂ χ₃ χ₄ G := by
        refine Finset.sum_congr rfl (fun χ₁ _ => Finset.sum_congr rfl (fun χ₂ _ =>
          Finset.sum_congr rfl (fun χ₃ _ => Finset.sum_congr rfl (fun χ₄ _ => ?_))))
        rw [crossMoment, Finset.mul_sum]

/-- The family fourth moment is controlled by the total quadruple mass, at Gauss-sum size
`q²` per quadruple: `∑_t ‖∑_χ g T_χ‖⁴ ≤ q²·∑_{quads}‖M‖`.  Triangle inequality AFTER the
exact expansion — the only lossy step left in the chain. -/
theorem sum_norm_familySum_pow_four_le (G : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (hg : GaussSumSizeBound X g) :
    ∑ t : F, ‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4
      ≤ (Fintype.card F : ℝ) ^ 2
        * ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X, ‖crossMoment χ₁ χ₂ χ₃ χ₄ G‖ := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
  have hLHS : ∑ t : F, ‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4
      = ‖∑ t : F, ((‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4 : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sum, Complex.norm_real]
    have hnn : (0 : ℝ) ≤ ∑ t : F, ‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4 := by positivity
    rw [Real.norm_of_nonneg hnn]
  have hcoeff : ∀ χ₁ ∈ X, ∀ χ₂ ∈ X, ∀ χ₃ ∈ X, ∀ χ₄ ∈ X,
      ‖g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)‖ ≤ q ^ 2 := by
    intro χ₁ h₁ χ₂ h₂ χ₃ h₃ χ₄ h₄
    have s1 := hg χ₁ h₁
    have s2 := hg χ₂ h₂
    have s3 := hg χ₃ h₃
    have s4 := hg χ₄ h₄
    have hsn : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg q
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    have h12 : ‖g χ₁‖ * ‖g χ₂‖ ≤ Real.sqrt q * Real.sqrt q :=
      mul_le_mul s1 s2 (norm_nonneg _) hsn
    have h123 : ‖g χ₁‖ * ‖g χ₂‖ * ‖g χ₃‖ ≤ Real.sqrt q * Real.sqrt q * Real.sqrt q :=
      mul_le_mul h12 s3 (norm_nonneg _) (by positivity)
    have h1234 : ‖g χ₁‖ * ‖g χ₂‖ * ‖g χ₃‖ * ‖g χ₄‖
        ≤ Real.sqrt q * Real.sqrt q * Real.sqrt q * Real.sqrt q :=
      mul_le_mul h123 s4 (norm_nonneg _) (by positivity)
    have hval : Real.sqrt q * Real.sqrt q * Real.sqrt q * Real.sqrt q = q ^ 2 := by
      calc Real.sqrt q * Real.sqrt q * Real.sqrt q * Real.sqrt q
          = (Real.sqrt q * Real.sqrt q) * (Real.sqrt q * Real.sqrt q) := by ring
        _ = q * q := by rw [hsq]
        _ = q ^ 2 := by ring
    linarith
  rw [hLHS, familyFourth_expansion G X g]
  calc ‖∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
        g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
          * crossMoment χ₁ χ₂ χ₃ χ₄ G‖
      ≤ ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X,
        ‖g χ₁ * g χ₂ * (starRingEnd ℂ) (g χ₃) * (starRingEnd ℂ) (g χ₄)
          * crossMoment χ₁ χ₂ χ₃ χ₄ G‖ := by
        refine (norm_sum_le X _).trans (Finset.sum_le_sum (fun χ₁ _ => ?_))
        refine (norm_sum_le X _).trans (Finset.sum_le_sum (fun χ₂ _ => ?_))
        refine (norm_sum_le X _).trans (Finset.sum_le_sum (fun χ₃ _ => ?_))
        exact norm_sum_le X _
    _ ≤ ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X, q ^ 2 * ‖crossMoment χ₁ χ₂ χ₃ χ₄ G‖ := by
        refine Finset.sum_le_sum (fun χ₁ h₁ => Finset.sum_le_sum (fun χ₂ h₂ =>
          Finset.sum_le_sum (fun χ₃ h₃ => Finset.sum_le_sum (fun χ₄ h₄ => ?_))))
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hcoeff χ₁ h₁ χ₂ h₂ χ₃ h₃ χ₄ h₄) (norm_nonneg _)
    _ = q ^ 2 * ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X, ‖crossMoment χ₁ χ₂ χ₃ χ₄ G‖ := by
        simp only [Finset.mul_sum]

/-! ### (3) The named family-level input -/

/-- **The family-level quadruple-mass input (named OPEN Prop, the honest `|X|³` scaling)**:
`∑_{χ₁,χ₂,χ₃,χ₄∈X} ‖M(χ₁,χ₂,χ₃,χ₄)‖ ≤ C₄·|X|³·n²·q`.

Probe status (`probe_r19_c4_exact.py`, exact totals, 12 cells):
* total/(|X|³n²q) ∈ [0.49, 1.44], FLAT in `m` — `C₄ = 1.5` covers every probed cell;
* the paired diagonal is PROVEN ≤ `Cw·|X|²·n²·q` here (`pairedDiagonal_le`), i.e. at the
  even stronger `|X|²` level — the open content is the off-paired total only;
* the `|X|²` version of this Prop is PROBE-REFUTED: off-paired/(|X|²n²q) grows `∝ m`
  (`0.85/2.2/5.8/18.6` at `m = 4/8/16/32`); do not strengthen the exponent;
* per-quadruple bounds cannot prove it: the max single off-paired `‖M‖` saturates `n²q`. -/
def FamilyQuarticCubicBound (G : Finset F) (X : Finset (MulChar F ℂ)) (C₄ : ℝ) : Prop :=
  ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X, ‖crossMoment χ₁ χ₂ χ₃ χ₄ G‖
    ≤ C₄ * (X.card : ℝ) ^ 3 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)

/-- The family-level quartic input is monotone in the published cubic-mass constant. -/
theorem familyQuarticCubicBound_mono {G : Finset F} {X : Finset (MulChar F ℂ)} {C₄ C₄' : ℝ}
    (hC : C₄ ≤ C₄') (h : FamilyQuarticCubicBound G X C₄) :
    FamilyQuarticCubicBound G X C₄' := by
  unfold FamilyQuarticCubicBound at *
  have hscale :
      C₄ * (X.card : ℝ) ^ 3 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)
        ≤ C₄' * (X.card : ℝ) ^ 3 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hC
      (by positivity : 0 ≤ (X.card : ℝ) ^ 3 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ))
    linarith
  exact h.trans hscale

/-! ### (4) The master bound and the linear-K rung -/

/-- **The Hölder-free master bound**: for ANY total quadruple-mass bound `B`,
`m⁴·S₂^D ≤ 8(q·n⁴ + q²·B)`.  Compare round 17's
`m⁴·S₂^D ≤ 8(q·n⁴ + |X|⁴·Cw·n²·q³)`: the `|X|⁴` (Hölder) is replaced by whatever the
family-level mass actually is. -/
theorem awayMoment_two_mul_le_of_familyQuartic
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) {B : ℝ}
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (hfam : ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X, ‖crossMoment χ₁ χ₂ χ₃ χ₄ G‖ ≤ B) :
    (m : ℝ) ^ 4 * incidenceMomentAway ψ G H D 2
      ≤ 8 * ((Fintype.card F : ℝ) * (G.card : ℝ) ^ 4 + (Fintype.card F : ℝ) ^ 2 * B) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpt : ∀ s₀ ∈ Finset.univ \ D,
      (m : ℝ) ^ 4 * ‖incidenceSum ψ G H s₀‖ ^ (2 * 2)
        ≤ 8 * (n ^ 4 + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4) := by
    intro s₀ hs₀
    have hsD : s₀ ∉ D := (Finset.mem_sdiff.mp hs₀).2
    have hdecs := hdec s₀ hsD
    have hnorm : (m : ℝ) * ‖incidenceSum ψ G H s₀‖
        ≤ n + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by
      have heq : ‖(m : ℂ) * incidenceSum ψ G H s₀‖
          = ‖(-(G.card : ℂ)) + ∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by rw [hdecs]
      calc (m : ℝ) * ‖incidenceSum ψ G H s₀‖
          = ‖(m : ℂ) * incidenceSum ψ G H s₀‖ := by
            rw [norm_mul, Complex.norm_natCast]
        _ = ‖(-(G.card : ℂ)) + ∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := heq
        _ ≤ ‖(-(G.card : ℂ))‖ + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := norm_add_le _ _
        _ = n + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by
            rw [norm_neg, Complex.norm_natCast]
    have hW0 : (0 : ℝ) ≤ ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := norm_nonneg _
    have hmul : (m : ℝ) ^ 4 * ‖incidenceSum ψ G H s₀‖ ^ (2 * 2)
        = ((m : ℝ) * ‖incidenceSum ψ G H s₀‖) ^ 4 := by ring
    rw [hmul]
    calc ((m : ℝ) * ‖incidenceSum ψ G H s₀‖) ^ 4
        ≤ (n + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hnorm 4
      _ ≤ 8 * (n ^ 4 + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4) :=
          add_pow_four_le hn0 hW0
  unfold incidenceMomentAway
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hpt).trans ?_
  have hcard : ((Finset.univ \ D).card : ℝ) ≤ q := by
    have := Finset.card_le_card (Finset.subset_univ (Finset.univ \ D))
    simpa [hqdef, Finset.card_univ] using (Nat.cast_le.mpr this : _)
  have hcomplete : ∑ s₀ ∈ Finset.univ \ D, ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4
      ≤ ∑ t : F, ‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)
  have hfamily : ∑ t : F, ‖∑ χ ∈ X, g χ * twistedThinSum χ G t‖ ^ 4 ≤ q ^ 2 * B :=
    (sum_norm_familySum_pow_four_le G X g hg).trans
      (mul_le_mul_of_nonneg_left hfam (by positivity))
  have hsplit : ∑ s₀ ∈ Finset.univ \ D,
      8 * (n ^ 4 + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4)
      = 8 * (((Finset.univ \ D).card : ℝ) * n ^ 4
          + ∑ s₀ ∈ Finset.univ \ D, ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    let f : F → ℝ := fun s₀ => ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4
    change ((Finset.univ \ D).card : ℝ) * (8 * n ^ 4) + ∑ x ∈ Finset.univ \ D, 8 * f x =
      8 * (((Finset.univ \ D).card : ℝ) * n ^ 4) + 8 * ∑ x ∈ Finset.univ \ D, f x
    rw [Finset.mul_sum]
    ring
  rw [hsplit]
  have h1 : ((Finset.univ \ D).card : ℝ) * n ^ 4 ≤ q * n ^ 4 :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have h2 : ∑ s₀ ∈ Finset.univ \ D, ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4
      ≤ q ^ 2 * B := hcomplete.trans hfamily
  linarith

/-- **THE LINEAR-K r = 2 RUNG (lane deliverable)**: under `FamilyQuarticCubicBound C₄`
plus the PROVEN normalizations (`hSig` is `_R18SigmaEquidistribution` for `q ≥ 16m²n²`;
`n² ≤ q` is inside the Weil regime `q ≥ n⁴`):

  `S₂^D ≤ 32·(C₄ + 1)·m·q·Σ²`.

The constant drops from round 17's `K(m) = 32(Cw(m−1)⁴+1)/m² ≍ Cw·m²` to `≍ m` — the Hölder
`m²`-drift is repaired; the residual single factor `m` is EXACTLY the signed-vs-absolute gap
of the off-paired quadruple family (probe: `m`-uniform is impossible for any absolute-mass
route, see `FamilyQuarticCubicBound`). -/
theorem r19_linearK_rung
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) (hm : 1 ≤ m) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (hfam : FamilyQuarticCubicBound G X C₄)
    (hXm : (X.card : ℝ) ≤ (m : ℝ))
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
      ≤ 2 * (m : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :
    incidenceMomentAway ψ G H D 2
      ≤ 32 * (C₄ + 1) * (m : ℝ) * (Fintype.card F : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  set Sg : ℝ := ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 with hSgdef
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hq0 : (0 : ℝ) < q := by linarith
  have hSg0 : (0 : ℝ) ≤ Sg := by rw [hSgdef]; positivity
  have hXc0 : (0 : ℝ) ≤ (X.card : ℝ) := by positivity
  have hfam' : ∑ χ₁ ∈ X, ∑ χ₂ ∈ X, ∑ χ₃ ∈ X, ∑ χ₄ ∈ X, ‖crossMoment χ₁ χ₂ χ₃ χ₄ G‖
      ≤ C₄ * (m : ℝ) ^ 3 * n ^ 2 * q := by
    refine hfam.trans ?_
    have hcube : (X.card : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 :=
      pow_le_pow_left₀ hXc0 hXm 3
    have hnn : (0 : ℝ) ≤ n ^ 2 * q := by positivity
    calc C₄ * (X.card : ℝ) ^ 3 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)
        = C₄ * (X.card : ℝ) ^ 3 * (n ^ 2 * q) := by rw [← hndef, ← hqdef]; ring
      _ ≤ C₄ * (m : ℝ) ^ 3 * (n ^ 2 * q) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube hC₄) hnn
      _ = C₄ * (m : ℝ) ^ 3 * n ^ 2 * q := by ring
  have hmaster := awayMoment_two_mul_le_of_familyQuartic ψ G H D X g m hdec hg hfam'
  have hfirst : q * n ^ 4 ≤ (m : ℝ) ^ 3 * n ^ 2 * q ^ 3 := by
    have hn4 : n ^ 4 ≤ n ^ 2 * q := by
      have := mul_le_mul_of_nonneg_left hnq (sq_nonneg n)
      nlinarith [this]
    have hq23 : q ^ 2 ≤ q ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg q) (show (0 : ℝ) ≤ q - 1 by linarith)]
    have hm3 : (1 : ℝ) ≤ (m : ℝ) ^ 3 := one_le_pow₀ hm1
    calc q * n ^ 4 ≤ q * (n ^ 2 * q) := mul_le_mul_of_nonneg_left hn4 hq0.le
      _ = n ^ 2 * q ^ 2 := by ring
      _ ≤ n ^ 2 * q ^ 3 := mul_le_mul_of_nonneg_left hq23 (sq_nonneg n)
      _ = 1 * (n ^ 2 * q ^ 3) := by ring
      _ ≤ (m : ℝ) ^ 3 * (n ^ 2 * q ^ 3) := mul_le_mul_of_nonneg_right hm3 (by positivity)
      _ = (m : ℝ) ^ 3 * n ^ 2 * q ^ 3 := by ring
  have hS : (m : ℝ) ^ 4 * incidenceMomentAway ψ G H D 2
      ≤ 8 * (C₄ + 1) * ((m : ℝ) ^ 3 * n ^ 2 * q ^ 3) := by
    have hmas : (m : ℝ) ^ 4 * incidenceMomentAway ψ G H D 2
        ≤ 8 * (q * n ^ 4 + q ^ 2 * (C₄ * (m : ℝ) ^ 3 * n ^ 2 * q)) := hmaster
    nlinarith [hmas, hfirst]
  have hSig2 : n ^ 2 * q ^ 2 ≤ 4 * (m : ℝ) ^ 2 * Sg ^ 2 := by
    have h := hSig
    have hnq0 : (0 : ℝ) ≤ n * q := by positivity
    nlinarith [h, hnq0, hSg0, hm0.le]
  have hSig3 : n ^ 2 * q ^ 3 ≤ 4 * (m : ℝ) ^ 2 * q * Sg ^ 2 := by nlinarith [hSig2, hq0.le]
  have hfin : (m : ℝ) ^ 4 * incidenceMomentAway ψ G H D 2
      ≤ (m : ℝ) ^ 4 * (32 * (C₄ + 1) * (m : ℝ) * q * Sg ^ 2) := by
    have hc : (0 : ℝ) ≤ 8 * (C₄ + 1) := by linarith
    have hm3 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
    have hmono := mul_le_mul_of_nonneg_left hSig3 hm3
    have hstep : 8 * (C₄ + 1) * ((m : ℝ) ^ 3 * (n ^ 2 * q ^ 3))
        ≤ 8 * (C₄ + 1) * ((m : ℝ) ^ 3 * (4 * (m : ℝ) ^ 2 * q * Sg ^ 2)) :=
      mul_le_mul_of_nonneg_left hmono hc
    have heq1 : 8 * (C₄ + 1) * ((m : ℝ) ^ 3 * n ^ 2 * q ^ 3)
        = 8 * (C₄ + 1) * ((m : ℝ) ^ 3 * (n ^ 2 * q ^ 3)) := by ring
    have heq2 : 8 * (C₄ + 1) * ((m : ℝ) ^ 3 * (4 * (m : ℝ) ^ 2 * q * Sg ^ 2))
        = (m : ℝ) ^ 4 * (32 * (C₄ + 1) * (m : ℝ) * q * Sg ^ 2) := by ring
    linarith [hS, hstep, heq1.le, heq1.ge, heq2.le, heq2.ge]
  have hm4 : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
  exact le_of_mul_le_mul_left hfin hm4

#print axioms crossMoment_paired_eq
#print axioms norm_crossMoment_paired_le
#print axioms pairedDiagonal_le
#print axioms sum_pow_two_mul_sum_pow_two
#print axioms familyFourth_expansion
#print axioms familyQuarticCubicBound_mono
#print axioms sum_norm_familySum_pow_four_le
#print axioms awayMoment_two_mul_le_of_familyQuartic
#print axioms r19_linearK_rung

end ArkLib.ProximityGap.Frontier.R19DepletedConstant
