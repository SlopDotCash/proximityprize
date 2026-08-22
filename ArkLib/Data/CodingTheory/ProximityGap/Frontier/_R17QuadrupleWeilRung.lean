/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16IncidenceR2Rung
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16DiagonalExactValue
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17HighMomentSpikeGate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17TchiMomentIdentities
import Mathlib.Algebra.Order.Chebyshev

/-!
# LANE WEIL (#466 round 17): the r = 2 rung via completion + Weil at the quadruple level —
  a constant-K r = 2 rung, conditional on ONE classical Weil input, in the regime `p ≳ n⁴`

## The chain (probe-verified end to end, `probe_r17_quadweil.py`)

With `m = deg = [F^× : H]`, `n = |μ_n|`, `q = |F|`, and the R15 χ-decomposition

  `m·I_H(s₀∉D) = −n + ∑_{χ≠χ₀, χ^m=χ₀} g(χ)·T_χ(s₀)`,   `T_χ(t) = ∑_{x∈μ_n} χ̄(t−x)`

(exact; re-verified to 1e-8 at all probed cells), the r = 2 away moment is controlled by the
FOURTH moment over `t` of the thin twisted sums `T_χ`:

* **Second moment is EXACT**: `∑_t |T_χ(t)|² = n(p−n)` for every χ ≠ χ₀ (the R16 Legendre-lane
  identity generalizes verbatim to arbitrary order; two-point orthogonality
  `∑_u χ̄(u)χ(u+c) = −1`).  Probe: exact at every cell, every χ.
* **Fourth moment via Weil**: `∑_t |T_χ|⁴ = ∑_{x₁..x₄∈μ_n} ∑_t χ((t−x₃)(t−x₄)/((t−x₁)(t−x₂)))`.
  The inner sum is a complete character sum of a degree-4 rational function: it is `p + O(1)`
  exactly on the degenerate quadruples (`{x₁,x₂} = {x₃,x₄}`, count `2n²−n`; plus for `m = 2`
  the pattern `x₁=x₂, x₃=x₄`, total `3n²−2n`) and `≤ 3√p` otherwise (Weil 1948; cf.
  Schmidt, *Equations over finite fields*, Thm 2.2.C).  Hence
  `∑_t |T_χ|⁴ ≤ 3n²p + 3n⁴√p ≤ 6n²p` **whenever `p ≥ n⁴`** — an honest Wick-shaped fourth
  moment for the thin twisted sums, with the β = 4 prize regime EXACTLY at the boundary.
  Probe: measured `∑_t|T_χ|⁴/(n²p) ∈ [1.8, 3.5]` at every cell (≤ 6 even below the regime).
* **Bookkeeping** (Hölder over the `m−1` characters, `‖g(χ)‖ = √p`):
  `m⁴·S₂^D ≤ 8(q·n⁴ + (m−1)⁴·Cw·n²·q³)`, and with `Σ ≥ nq/(2m)` (true with huge room:
  probe ratio `Σ/(nq/m) ∈ [0.98, 1.08]` in-regime) this is
  `S₂^D ≤ K·q·Σ²` with **explicit `K = 32(Cw(m−1)⁴ + 1)/m²`** (for `deg = 2`, `Cw = 6`:
  `K = 56`; measured actual ratio ≤ 0.77 — enormous headroom).

## Where the wall is, exactly

* The r16 refuted cell `(n, deg, p) = (64, 8, 7681)` has `p/n⁴ ≈ 0.0005`: it violates the
  Weil regime `p ≥ n⁴`, PRECISELY as the bookkeeping predicts.  The regime restriction is
  not an artifact — it is where `n⁴√p` (non-degenerate Weil mass) overtakes `n²p` (diagonal).
* **r = 2 is the LAST Weil-closable rung.**  At rung `r` the `2r`-th moment of `T_χ` has
  non-degenerate Weil mass `n^{2r}·(2r−1)√p` versus diagonal `~r!·n^r·p`; closing needs
  `n^r ≲ √p`, i.e. `r ≤ 2` at β = 4.  The interchange bridge needs `r = ⌈ln q⌉`: the gap
  between 2 and `ln q` IS the wall, now measured in rungs.

## What THIS file proves (axiom-clean, real locked build)

Everything below the two named classical/structural inputs, i.e. the full analytic chain:
* `norm_sum_pow_four_le` — the Hölder/power-mean step `‖∑_X f‖⁴ ≤ |X|³·∑_X ‖f‖⁴`.
* `add_pow_four_le` — `(a+b)⁴ ≤ 8(a⁴+b⁴)`.
* `awayMoment_two_mul_le_of_chiDecomp` — the master quantitative bound
  `m⁴·S₂^D ≤ 8(q·n⁴ + |X|⁴·Cw·n²·q³)` from `ChiDecompositionOff` + `GaussSumSizeBound` +
  `FourthMomentTwistBound`.
* `r2Rung_of_weil` — the constant-K r = 2 rung `S₂^D ≤ K·q·Σ²`, `K = 32(Cw·|X|⁴+1)/m²`,
  under the probe-huge-room hypotheses `n·q ≤ 2m·Σ` and `n² ≤ q`.
* `wickAwayAtWithConstant_two_of_weil` — wiring into the round-16 consumer interface
  `WickAwayAtWithConstant … 2 (K/3)`.

## Named inputs (NOT proven here; both classical/probe-exact, neither is the wall)

* `ChiDecompositionOff` — the R15 Gauss-sum decomposition as a structural interface
  (probe-exact to 1e-8; formalizing it needs subgroup/character-group duality
  `1_H = (1/m)∑_{χ^m=χ₀} χ`, a Mathlib-gap, not a math-gap).
* `FourthMomentTwistBound` — `∑_t ‖T_χ‖⁴ ≤ Cw·n²·q`.  THE Weil input: a theorem of
  Weil (1948) for `p ≥ n⁴` with `Cw = 6` (not in Mathlib: multiplicative character sums of
  rational functions).  This is a PROVEN classical theorem being imported, not a conjecture.
* `GaussSumSizeBound` — `‖g(χ)‖ ≤ √q` (classical; Mathlib has the squared form for
  primitive characters; kept as an interface to stay generic over the char family).

## Honest scope

This does NOT close Problem B (needs rung `r ~ ln q`, provably beyond Weil — see above) and
does NOT touch Problem A.  It reduces the previously-open r = 2 rung, in the regime
`p ≥ max(n⁴, 16n²m²)` that contains the prize instance β = 4⁺, to textbook Weil plus a
character-duality formalization gap.  The genuinely-open content of the campaign is unchanged;
what moves is that `StrongR2Rung`-at-constant-K stops being open MATH in the prize regime and
becomes open FORMALIZATION (two named classical inputs).  CORE OPEN, ON-BGK.

Issue #466, round 17, lane WEIL.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) The thin twisted sums -/

/-- The thin twisted sum `T_χ(t) = ∑_{x∈G} conj(χ(t−x))` — the scalar family produced by the
R15 χ-decomposition of the incidence sum.  (`χ(0) = 0` in Mathlib's `MulChar`, so the diagonal
term `x = t` is automatically absent.) -/
noncomputable def twistedThinSum (χ : MulChar F ℂ) (G : Finset F) (t : F) : ℂ :=
  ∑ x ∈ G, (starRingEnd ℂ) (χ (t - x))

/-- The R17 Weil-lane twisted sum is exactly the complex conjugate of the common
`shiftedCharSum` API used by the Tχ moment files. -/
theorem twistedThinSum_eq_star_shiftedCharSum (χ : MulChar F ℂ) (G : Finset F) (t : F) :
    twistedThinSum χ G t = star (shiftedCharSum χ G t) := by
  simp [twistedThinSum, shiftedCharSum]

/-- Consequently the two APIs have identical norm moments. -/
theorem norm_twistedThinSum_eq_shiftedCharSum (χ : MulChar F ℂ) (G : Finset F) (t : F) :
    ‖twistedThinSum χ G t‖ = ‖shiftedCharSum χ G t‖ := by
  rw [twistedThinSum_eq_star_shiftedCharSum, norm_star]

/-- Full-line norm moments are identical for the `twistedThinSum` and `shiftedCharSum` APIs. -/
theorem sum_norm_twistedThinSum_pow_eq_shiftedCharMoment
    (χ : MulChar F ℂ) (G : Finset F) (r : ℕ) :
    ∑ t : F, ‖twistedThinSum χ G t‖ ^ (2 * r)
      = ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharMoment χ G r := by
  unfold ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharMoment
  exact Finset.sum_congr rfl fun t _ => by rw [norm_twistedThinSum_eq_shiftedCharSum]

/-- Deleted-line norm moments are identical for the `twistedThinSum` and `shiftedCharSum` APIs. -/
theorem sum_norm_twistedThinSum_away_pow_eq_shiftedCharMomentAway
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) :
    ∑ t ∈ Finset.univ \ D, ‖twistedThinSum χ G t‖ ^ (2 * r)
      = ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharMomentAway χ G D r := by
  unfold ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharMomentAway
  exact Finset.sum_congr rfl fun t _ => by rw [norm_twistedThinSum_eq_shiftedCharSum]

/-- A shifted-character away Wick bound immediately bounds the conjugated twisted sum used in the
χ-decomposition. -/
theorem twistedThinSum_pow_le_of_shifted_awayWickAt
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ)
    (hwick : ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ G D r)
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖twistedThinSum χ G s₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  rw [norm_twistedThinSum_eq_shiftedCharSum]
  exact ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharSum_pow_le_of_awayWickAt
    χ G D r hwick hs₀

/-- Direct `twistedThinSum` consumer of the high-moment rate gate.  This transfers the
shifted-character Markov last mile to the conjugated Tχ sums used by the R15 decomposition. -/
theorem twistedThinSum_le_of_shifted_awayWickAt_rate
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hr : 1 ≤ r)
    (hwick : ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖twistedThinSum χ G s₀‖ ≤ T := by
  rw [norm_twistedThinSum_eq_shiftedCharSum]
  exact ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.shiftedCharSum_le_of_awayWickAt_rate
    χ G D r hT hr hwick hrate hs₀

/-- Coarse rate version of `twistedThinSum_le_of_shifted_awayWickAt_rate`, using
`(2r-1)‼ ≤ (2r)^r`. -/
theorem twistedThinSum_le_of_coarse_shifted_awayWickAt_rate
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hr : 1 ≤ r)
    (hwick : ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ G D r)
    (hrate :
      (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖twistedThinSum χ G s₀‖ ≤ T := by
  rw [norm_twistedThinSum_eq_shiftedCharSum]
  exact
    ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.shiftedCharSum_le_of_coarse_awayWickAt_rate
      χ G D r hT hr hwick hrate hs₀

/-! ### (1) Named structural / classical inputs -/

/-- **The R15 Gauss-sum decomposition, as a structural interface** (probe-exact to `1e-8` at all
cells of `probe_r17_quadweil.py`): off the deleted diagonal,
`m·I_H(s₀) = −|G| + ∑_{χ∈X} g(χ)·T_χ(s₀)`, where `X` is the set of the `m−1` nontrivial
characters with `χ^m = χ₀` and `g` their Gauss sums.  Proving it in Lean needs the
subgroup/character duality `1_H = (1/m)∑_{χ^m=χ₀} χ` — a formalization gap, not a math gap. -/
def ChiDecompositionOff (ψ : AddChar F ℂ) (G H D : Finset F)
    (X : Finset (MulChar F ℂ)) (g : MulChar F ℂ → ℂ) (m : ℕ) : Prop :=
  ∀ s₀ : F, s₀ ∉ D →
    (m : ℂ) * incidenceSum ψ G H s₀
      = -(G.card : ℂ) + ∑ χ ∈ X, g χ * twistedThinSum χ G s₀

/-- Classical Gauss-sum size: `‖g(χ)‖ ≤ √q` for every χ in the family. -/
def GaussSumSizeBound (X : Finset (MulChar F ℂ)) (g : MulChar F ℂ → ℂ) : Prop :=
  ∀ χ ∈ X, ‖g χ‖ ≤ Real.sqrt (Fintype.card F)

/-- **THE Weil input**: the fourth moment of each thin twisted sum over the FULL offset line is
Wick-shaped, `∑_t ‖T_χ(t)‖⁴ ≤ Cw·|G|²·q`.  For `G = μ_n` and `q ≥ |G|⁴` this is a THEOREM
(Weil 1948 for character sums of degree-4 rational functions: degenerate quadruples
`≤ 3n²·p`, non-degenerate `≤ 3√p` each, total `≤ 3n²p + 3n⁴√p ≤ 6n²p`), with `Cw = 6`;
it is imported as a named Prop only because Weil for rational-function twists is not in
Mathlib.  Probe: measured `∑‖T_χ‖⁴/(n²q) ∈ [1.8, 3.5]` at every cell. -/
def FourthMomentTwistBound (G : Finset F) (X : Finset (MulChar F ℂ)) (Cw : ℝ) : Prop :=
  ∀ χ ∈ X, ∑ t : F, ‖twistedThinSum χ G t‖ ^ 4
    ≤ Cw * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)

/-! ### (2) The two analytic ingredients -/

/-- Hölder/power-mean at the fourth power: `‖∑_{i∈s} f i‖⁴ ≤ |s|³·∑_{i∈s} ‖f i‖⁴`. -/
theorem norm_sum_pow_four_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖f i‖ ^ 4 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 : (∑ i ∈ s, ‖f i‖) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖f i‖ ^ 4 := by
    simpa using pow_sum_le_card_mul_sum_pow
      (f := fun i => ‖f i‖) (fun i _ => norm_nonneg _) 3
  calc ‖∑ i ∈ s, f i‖ ^ 4 ≤ (∑ i ∈ s, ‖f i‖) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 4
    _ ≤ _ := h2

/-- Hölder/power-mean at arbitrary positive integer exponent, stated in the successor form used
by `pow_sum_le_card_mul_sum_pow`.  This is the reusable bookkeeping step for any future deep
moment rung: `‖∑ f‖^(k+1) ≤ |s|^k ∑ ‖f‖^(k+1)`. -/
theorem norm_sum_pow_succ_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) (k : ℕ) :
    ‖∑ i ∈ s, f i‖ ^ (k + 1) ≤ (s.card : ℝ) ^ k * ∑ i ∈ s, ‖f i‖ ^ (k + 1) := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 : (∑ i ∈ s, ‖f i‖) ^ (k + 1)
      ≤ (s.card : ℝ) ^ k * ∑ i ∈ s, ‖f i‖ ^ (k + 1) := by
    simpa using pow_sum_le_card_mul_sum_pow
      (f := fun i => ‖f i‖) (fun i _ => norm_nonneg _) k
  calc ‖∑ i ∈ s, f i‖ ^ (k + 1) ≤ (∑ i ∈ s, ‖f i‖) ^ (k + 1) :=
        pow_le_pow_left₀ (norm_nonneg _) h1 (k + 1)
    _ ≤ _ := h2

/-- Even-exponent version of `norm_sum_pow_succ_le`, the shape needed for the `2r`-moment
incidence ladder. -/
theorem norm_sum_pow_even_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) (r : ℕ) (hr : 1 ≤ r) :
    ‖∑ i ∈ s, f i‖ ^ (2 * r)
      ≤ (s.card : ℝ) ^ (2 * r - 1) * ∑ i ∈ s, ‖f i‖ ^ (2 * r) := by
  have hsucc : 2 * r - 1 + 1 = 2 * r := by omega
  simpa [hsucc] using norm_sum_pow_succ_le s f (2 * r - 1)

/-- General-`r` χ-family pointwise bookkeeping.  If every shifted character face in `X` satisfies
the corrected away Wick target at rung `r`, then the conjugated χ-sum appearing in the
Gauss-decomposition is controlled at the same exponent, up to the standard Hölder factor over
`X` and Gauss-sum sizes. -/
theorem twistedFamilySum_pow_even_le_of_shifted_awayWick
    (G D : Finset F) (X : Finset (MulChar F ℂ)) (g : MulChar F ℂ → ℂ)
    (r : ℕ) (hr : 1 ≤ r)
    (hg : GaussSumSizeBound X g)
    (hwick :
      ∀ χ ∈ X,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ G D r)
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ (2 * r)
      ≤ (X.card : ℝ) ^ (2 * r - 1)
          * ∑ χ ∈ X,
            (Real.sqrt (Fintype.card F : ℝ)) ^ (2 * r)
              * ((Fintype.card F : ℝ)
                * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  classical
  have hHolder :=
    norm_sum_pow_even_le X (fun χ => g χ * twistedThinSum χ G s₀) r hr
  refine le_trans hHolder ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun χ hχ => ?_
  rw [norm_mul, mul_pow]
  have hgpow : ‖g χ‖ ^ (2 * r) ≤ (Real.sqrt (Fintype.card F : ℝ)) ^ (2 * r) :=
    pow_le_pow_left₀ (norm_nonneg _) (hg χ hχ) (2 * r)
  have hTpow :
      ‖twistedThinSum χ G s₀‖ ^ (2 * r)
        ≤ (Fintype.card F : ℝ)
            * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
    twistedThinSum_pow_le_of_shifted_awayWickAt χ G D r (hwick χ hχ) hs₀
  exact mul_le_mul hgpow hTpow (by positivity) (by positivity)

/-- General deep-route pointwise incidence consumer.  If the χ-decomposition holds off `D`, the
Gauss coefficients have square-root size, and every shifted χ-face has crossed the corrected-away
Wick rate at threshold `T`, then the completed incidence sum obeys
`m‖I(s₀)‖ ≤ |G| + |X|√q T` at every non-deleted offset.  The remaining prize work is precisely to
produce the deep-rate `ShiftedCharAwayWickAt` hypotheses with a threshold `T` small enough for the
target `√Σ` scale. -/
theorem incidenceSum_mul_le_of_shifted_awayWickAt_rate
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) (r : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hr : 1 ≤ r)
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (hwick :
      ∀ χ ∈ X,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    (m : ℝ) * ‖incidenceSum ψ G H s₀‖
      ≤ (G.card : ℝ) + (X.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
  classical
  have hdecs := hdec s₀ hs₀
  have hnorm : (m : ℝ) * ‖incidenceSum ψ G H s₀‖
      ≤ (G.card : ℝ) + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by
    have : ‖(m : ℂ) * incidenceSum ψ G H s₀‖
        = ‖(-(G.card : ℂ)) + ∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by rw [hdecs]
    calc (m : ℝ) * ‖incidenceSum ψ G H s₀‖
        = ‖(m : ℂ) * incidenceSum ψ G H s₀‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖(-(G.card : ℂ)) + ∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := this
      _ ≤ ‖(-(G.card : ℂ))‖ + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := norm_add_le _ _
      _ = (G.card : ℝ) + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by
          rw [norm_neg, Complex.norm_natCast]
  have hsum : ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖
      ≤ (X.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
    calc ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖
        ≤ ∑ χ ∈ X, ‖g χ * twistedThinSum χ G s₀‖ := norm_sum_le X _
      _ ≤ ∑ _χ ∈ X, Real.sqrt (Fintype.card F : ℝ) * T := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          rw [norm_mul]
          have hgχ := hg χ hχ
          have hTχ : ‖twistedThinSum χ G s₀‖ ≤ T :=
            twistedThinSum_le_of_shifted_awayWickAt_rate χ G D r hT hr (hwick χ hχ) hrate hs₀
          exact mul_le_mul hgχ hTχ (norm_nonneg _) (by positivity)
      _ = (X.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  linarith

/-- `(a+b)⁴ ≤ 8(a⁴+b⁴)` for nonnegative reals. -/
theorem add_pow_four_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg ha hb, sq_nonneg (a * b)]

/-! ### (3) The master quantitative bound -/

/-- **The completion + Weil master bound for the r = 2 away moment**:
`m⁴·S₂^D ≤ 8·(q·n⁴ + |X|⁴·Cw·n²·q³)` (with `n = |G|`, `q = |F|`).  This is the entire
analytic content of the quadruple-level Weil route, made unconditional relative to the three
named inputs.  Probe: the inequality holds with ratio `≤ 0.125` at every cell. -/
theorem awayMoment_two_mul_le_of_chiDecomp
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (h4 : FourthMomentTwistBound G X Cw) :
    (m : ℝ) ^ 4 * incidenceMomentAway ψ G H D 2
      ≤ 8 * ((Fintype.card F : ℝ) * (G.card : ℝ) ^ 4
          + (X.card : ℝ) ^ 4 * Cw * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 3) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  have hq0 : 0 ≤ q := by positivity
  have hn0 : 0 ≤ n := by positivity
  -- pointwise: m⁴‖I(s₀)‖⁴ ≤ 8(n⁴ + |X|³·q²·∑_χ ‖T_χ(s₀)‖⁴) for s₀ ∉ D
  have hpt : ∀ s₀ ∈ Finset.univ \ D,
      (m : ℝ) ^ 4 * ‖incidenceSum ψ G H s₀‖ ^ (2 * 2)
        ≤ 8 * (n ^ 4 + (X.card : ℝ) ^ 3 * q ^ 2 * ∑ χ ∈ X, ‖twistedThinSum χ G s₀‖ ^ 4) := by
    intro s₀ hs₀
    have hsD : s₀ ∉ D := (Finset.mem_sdiff.mp hs₀).2
    have hdecs := hdec s₀ hsD
    -- ‖m·I‖ ≤ n + ‖∑ g T‖
    have hnorm : (m : ℝ) * ‖incidenceSum ψ G H s₀‖
        ≤ n + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by
      have : ‖(m : ℂ) * incidenceSum ψ G H s₀‖
          = ‖(-(G.card : ℂ)) + ∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by rw [hdecs]
      calc (m : ℝ) * ‖incidenceSum ψ G H s₀‖
          = ‖(m : ℂ) * incidenceSum ψ G H s₀‖ := by
            rw [norm_mul, Complex.norm_natCast]
        _ = ‖(-(G.card : ℂ)) + ∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := this
        _ ≤ ‖(-(G.card : ℂ))‖ + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := norm_add_le _ _
        _ = n + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := by
            rw [norm_neg, Complex.norm_natCast]
    -- fourth power + (a+b)⁴ ≤ 8(a⁴+b⁴)
    have hI0 : 0 ≤ ‖incidenceSum ψ G H s₀‖ := norm_nonneg _
    have hW0 : 0 ≤ ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ := norm_nonneg _
    have hp4 : ((m : ℝ) * ‖incidenceSum ψ G H s₀‖) ^ 4
        ≤ 8 * (n ^ 4 + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4) := by
      calc ((m : ℝ) * ‖incidenceSum ψ G H s₀‖) ^ 4
          ≤ (n + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hnorm 4
        _ ≤ 8 * (n ^ 4 + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4) :=
            add_pow_four_le hn0 hW0
    -- Hölder over χ, then ‖g χ‖⁴ ≤ q²
    have hHolder : ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4
        ≤ (X.card : ℝ) ^ 3 * q ^ 2 * ∑ χ ∈ X, ‖twistedThinSum χ G s₀‖ ^ 4 := by
      have h1 := norm_sum_pow_four_le X (fun χ => g χ * twistedThinSum χ G s₀)
      have h2 : ∑ χ ∈ X, ‖g χ * twistedThinSum χ G s₀‖ ^ 4
          ≤ ∑ χ ∈ X, q ^ 2 * ‖twistedThinSum χ G s₀‖ ^ 4 := by
        refine Finset.sum_le_sum (fun χ hχ => ?_)
        rw [norm_mul, mul_pow]
        have hgχ : ‖g χ‖ ^ 4 ≤ q ^ 2 := by
          have h := hg χ hχ
          have h4' : ‖g χ‖ ^ 4 ≤ (Real.sqrt q) ^ 4 :=
            pow_le_pow_left₀ (norm_nonneg _) h 4
          have : (Real.sqrt q) ^ 4 = q ^ 2 := by
            rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hq0]
          linarith [h4', this.le]
        exact mul_le_mul_of_nonneg_right hgχ (by positivity)
      calc ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4
          ≤ (X.card : ℝ) ^ 3 * ∑ χ ∈ X, ‖g χ * twistedThinSum χ G s₀‖ ^ 4 := h1
        _ ≤ (X.card : ℝ) ^ 3 * ∑ χ ∈ X, q ^ 2 * ‖twistedThinSum χ G s₀‖ ^ 4 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (X.card : ℝ) ^ 3 * q ^ 2 * ∑ χ ∈ X, ‖twistedThinSum χ G s₀‖ ^ 4 := by
            simp only [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun χ _ => by ring)
    have hmul : (m : ℝ) ^ 4 * ‖incidenceSum ψ G H s₀‖ ^ (2 * 2)
        = ((m : ℝ) * ‖incidenceSum ψ G H s₀‖) ^ 4 := by ring
    rw [hmul]
    calc ((m : ℝ) * ‖incidenceSum ψ G H s₀‖) ^ 4
        ≤ 8 * (n ^ 4 + ‖∑ χ ∈ X, g χ * twistedThinSum χ G s₀‖ ^ 4) := hp4
      _ ≤ 8 * (n ^ 4 + (X.card : ℝ) ^ 3 * q ^ 2 * ∑ χ ∈ X, ‖twistedThinSum χ G s₀‖ ^ 4) := by
          have := hHolder; linarith
  -- sum over s₀ ∈ univ \ D
  unfold incidenceMomentAway
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hpt).trans ?_
  have hcard : ((Finset.univ \ D).card : ℝ) ≤ q := by
    have := Finset.card_le_card (Finset.subset_univ (Finset.univ \ D))
    simpa [hq, Finset.card_univ] using (Nat.cast_le.mpr this : _)
  have hT : ∑ χ ∈ X, ∑ s₀ ∈ Finset.univ \ D, ‖twistedThinSum χ G s₀‖ ^ 4
      ≤ (X.card : ℝ) * (Cw * n ^ 2 * q) := by
    calc ∑ χ ∈ X, ∑ s₀ ∈ Finset.univ \ D, ‖twistedThinSum χ G s₀‖ ^ 4
        ≤ ∑ χ ∈ X, ∑ t : F, ‖twistedThinSum χ G t‖ ^ 4 := by
          refine Finset.sum_le_sum fun χ _ => ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by positivity)
      _ ≤ ∑ _χ ∈ X, Cw * n ^ 2 * q := Finset.sum_le_sum fun χ hχ => h4 χ hχ
      _ = (X.card : ℝ) * (Cw * n ^ 2 * q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : ∑ s₀ ∈ Finset.univ \ D,
      8 * (n ^ 4 + (X.card : ℝ) ^ 3 * q ^ 2 * ∑ χ ∈ X, ‖twistedThinSum χ G s₀‖ ^ 4)
      = 8 * (((Finset.univ \ D).card : ℝ) * n ^ 4
          + (X.card : ℝ) ^ 3 * q ^ 2
            * ∑ χ ∈ X, ∑ s₀ ∈ Finset.univ \ D, ‖twistedThinSum χ G s₀‖ ^ 4) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    rw [Finset.sum_comm]
    ring
  rw [hsplit]
  have hXq : (0 : ℝ) ≤ (X.card : ℝ) ^ 3 * q ^ 2 := by positivity
  have hstep : ((Finset.univ \ D).card : ℝ) * n ^ 4
      + (X.card : ℝ) ^ 3 * q ^ 2
        * ∑ χ ∈ X, ∑ s₀ ∈ Finset.univ \ D, ‖twistedThinSum χ G s₀‖ ^ 4
      ≤ q * n ^ 4 + (X.card : ℝ) ^ 4 * Cw * n ^ 2 * q ^ 3 := by
    have h1 : ((Finset.univ \ D).card : ℝ) * n ^ 4 ≤ q * n ^ 4 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have h2 : (X.card : ℝ) ^ 3 * q ^ 2
          * ∑ χ ∈ X, ∑ s₀ ∈ Finset.univ \ D, ‖twistedThinSum χ G s₀‖ ^ 4
        ≤ (X.card : ℝ) ^ 3 * q ^ 2 * ((X.card : ℝ) * (Cw * n ^ 2 * q)) :=
      mul_le_mul_of_nonneg_left hT hXq
    have h2' : (X.card : ℝ) ^ 3 * q ^ 2 * ((X.card : ℝ) * (Cw * n ^ 2 * q))
        = (X.card : ℝ) ^ 4 * Cw * n ^ 2 * q ^ 3 := by ring
    linarith [h2, h2'.le, h2'.ge, h1]
  linarith [hstep]

/-! ### (4) The constant-K r = 2 rung -/

/-- **The unconditional-modulo-Weil constant-K r = 2 rung.**  Under the three named inputs plus
the probe-huge-room normalizations `n·q ≤ 2m·Σ` (probe: `Σ/(nq/m) ∈ [0.98, 1.08]` in-regime)
and `n² ≤ q` (implied by the Weil regime `q ≥ n⁴`):

  `S₂^D ≤ K·q·Σ²`,   `K = 32·(Cw·|X|⁴ + 1)/m²`.

For `deg = m = 2` (`|X| = 1`, `Cw = 6`): `K = 56`.  Measured actual ratio ≤ 0.77: the
constant is generous, the point is that it is EXPLICIT and n, p-free. -/
theorem r2Rung_of_weil
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) (hm : 1 ≤ m) {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (h4 : FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (m : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :
    incidenceMomentAway ψ G H D 2
      ≤ (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2)
        * ((Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  set Sg : ℝ := ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 with hSgdef
  set Xc : ℝ := (X.card : ℝ) with hXcdef
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hSg0 : (0 : ℝ) ≤ Sg := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hXc0 : (0 : ℝ) ≤ Xc := by positivity
  have hmaster := awayMoment_two_mul_le_of_chiDecomp ψ G H D X g m hCw hdec hg h4
  -- (n·q)² ≤ (2mΣ)²
  have hSgsq : n ^ 2 * q ^ 2 ≤ 4 * (m : ℝ) ^ 2 * Sg ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ n * q) hSig
    nlinarith [h]
  -- key polynomial inequality
  have hkey : (m : ℝ) ^ 4 * incidenceMomentAway ψ G H D 2
      ≤ 32 * (Cw * Xc ^ 4 + 1) * (m : ℝ) ^ 2 * (q * Sg ^ 2) := by
    have h1 : 8 * (q * n ^ 4) ≤ 32 * (m : ℝ) ^ 2 * (q * Sg ^ 2) := by
      -- q·n⁴ ≤ n²·q² ≤ 4m²Σ² ≤ 4m²Σ²·q
      have hn2q : (0 : ℝ) ≤ n ^ 2 * q := by positivity
      have ha : q * n ^ 4 ≤ n ^ 2 * q ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hnq hn2q]
      have hb : n ^ 2 * q ^ 2 ≤ 4 * (m : ℝ) ^ 2 * Sg ^ 2 := hSgsq
      have hc4 : (0 : ℝ) ≤ 4 * (m : ℝ) ^ 2 * Sg ^ 2 := by positivity
      have hc : 4 * (m : ℝ) ^ 2 * Sg ^ 2 ≤ 4 * (m : ℝ) ^ 2 * Sg ^ 2 * q := by
        nlinarith [mul_le_mul_of_nonneg_left hq1 hc4]
      nlinarith [ha, hb, hc]
    have h2 : 8 * (Xc ^ 4 * Cw * n ^ 2 * q ^ 3)
        ≤ 32 * Cw * Xc ^ 4 * (m : ℝ) ^ 2 * (q * Sg ^ 2) := by
      -- n²q³ = q·(n²q²) ≤ q·4m²Σ²
      have ha : n ^ 2 * q ^ 3 ≤ 4 * (m : ℝ) ^ 2 * Sg ^ 2 * q := by nlinarith [hSgsq, hq0]
      have hcoef : (0 : ℝ) ≤ Cw * Xc ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left ha hcoef]
    nlinarith [hmaster, h1, h2]
  -- divide by m⁴
  have hm4 : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
  have hgoal : incidenceMomentAway ψ G H D 2
      ≤ 32 * (Cw * Xc ^ 4 + 1) * (m : ℝ) ^ 2 * (q * Sg ^ 2) / (m : ℝ) ^ 4 := by
    rw [le_div_iff₀ hm4]
    calc incidenceMomentAway ψ G H D 2 * (m : ℝ) ^ 4
        = (m : ℝ) ^ 4 * incidenceMomentAway ψ G H D 2 := by ring
      _ ≤ 32 * (Cw * Xc ^ 4 + 1) * (m : ℝ) ^ 2 * (q * Sg ^ 2) := hkey
  refine hgoal.trans_eq ?_
  field_simp

/-! ### (5) Wiring into the round-16 consumer interface -/

/-- The Weil route delivers the round-16 corrected rung interface
`WickAwayAtWithConstant … 2 C` at the explicit constant
`C = 32(Cw·|X|⁴+1)/(3m²)` (for `deg = 2`, `Cw = 6`: `C = 56/3 ≈ 18.7`; the probes calibrate
the TRUE C at ≤ 4/3, so the constant is lossy but finite and n, p-free). -/
theorem wickAwayAtWithConstant_two_of_weil
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) (hm : 1 ≤ m) {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (h4 : FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (m : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :
    WickAwayAtWithConstant ψ G H D 2
      (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2 / 3) := by
  unfold WickAwayAtWithConstant
  have h := r2Rung_of_weil ψ G H D X g m hm hCw hdec hg h4 hq1 hnq hSig
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by
    norm_num [Nat.doubleFactorial]
  rw [hdf]
  calc incidenceMomentAway ψ G H D 2
      ≤ (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2)
        * ((Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2) := h
    _ = 32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2 / 3
        * ((Fintype.card F : ℝ) * 3 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2) := by ring

/-! ### (6) Consumer forms for the r = 2 rung -/

/-- The quadruple-Weil r = 2 rung gives the honest fourth-root pointwise bound away from `D`.
This is the direct r = 2 consumer form; it deliberately does **not** pretend to supply the
high-depth `r = ⌈log(Cq)⌉` bridge needed for full approximate Problem B. -/
theorem incidence_sq_le_sqrt_of_weil_r2
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) (hm : 1 ≤ m) {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (h4 : FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (m : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ Real.sqrt ((32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2)
          * ((Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2)) := by
  have hwick :=
    r2Rung_of_weil ψ G H D X g m hm hCw hdec hg h4 hq1 hnq hSig
  have hpt : ‖incidenceSum ψ G H s₀‖ ^ (2 * 2)
      ≤ incidenceMomentAway ψ G H D 2 :=
    pow_le_incidenceMomentAway ψ G H D hs 2
  have hpow : ‖incidenceSum ψ G H s₀‖ ^ 4
      ≤ (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2)
          * ((Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2) := by
    simpa using hpt.trans hwick
  rw [show ‖incidenceSum ψ G H s₀‖ ^ 2 =
      Real.sqrt (‖incidenceSum ψ G H s₀‖ ^ 4) by
        rw [show ‖incidenceSum ψ G H s₀‖ ^ 4 =
          (‖incidenceSum ψ G H s₀‖ ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt hpow

/-- Sup-norm consumer form of `incidence_sq_le_sqrt_of_weil_r2`: if the Fourier coefficients on
`H` are bounded by `M`, the r = 2 Weil lane gives a fourth-root pointwise estimate. -/
theorem incidence_sq_le_sqrt_sup_of_weil_r2
    (ψ : AddChar F ℂ) (G H D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (m : ℕ) (hm : 1 ≤ m) {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hdec : ChiDecompositionOff ψ G H D X g m)
    (hg : GaussSumSizeBound X g)
    (h4 : FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (m : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ Real.sqrt ((32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2)
          * ((Fintype.card F : ℝ) * ((H.card : ℝ) * M ^ 2) ^ 2)) := by
  refine le_trans
    (incidence_sq_le_sqrt_of_weil_r2 ψ G H D X g m hm hCw hdec hg h4 hq1 hnq hSig hs)
    (Real.sqrt_le_sqrt ?_)
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hM b hb) 2
      _ = (H.card : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcoef : 0 ≤ (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / (m : ℝ) ^ 2)
      * (Fintype.card F : ℝ) := by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
    positivity
  nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum 2) hcoef]

end ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.norm_sum_pow_four_le
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.twistedThinSum_eq_star_shiftedCharSum
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.norm_twistedThinSum_eq_shiftedCharSum
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.sum_norm_twistedThinSum_pow_eq_shiftedCharMoment
#print axioms
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.sum_norm_twistedThinSum_away_pow_eq_shiftedCharMomentAway
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.twistedThinSum_pow_le_of_shifted_awayWickAt
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.twistedThinSum_le_of_shifted_awayWickAt_rate
#print axioms
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.twistedThinSum_le_of_coarse_shifted_awayWickAt_rate
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.norm_sum_pow_succ_le
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.norm_sum_pow_even_le
#print axioms
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.twistedFamilySum_pow_even_le_of_shifted_awayWick
#print axioms
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.incidenceSum_mul_le_of_shifted_awayWickAt_rate
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.add_pow_four_le
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.awayMoment_two_mul_le_of_chiDecomp
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.r2Rung_of_weil
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.wickAwayAtWithConstant_two_of_weil
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.incidence_sq_le_sqrt_of_weil_r2
#print axioms ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.incidence_sq_le_sqrt_sup_of_weil_r2
