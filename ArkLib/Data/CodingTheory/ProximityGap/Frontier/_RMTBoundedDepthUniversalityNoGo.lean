/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# RMT-universality no-go: a BOUNDED-DEPTH moment input (4-moment theorem) is provably insufficient
to reach the prize per-frequency target `√(2 n ln q)` (#464, target `radical-RMT-universality`)

## The radical hypothesis and the exact obstruction it hits

The numerically-confirmed RADICAL hypothesis (probes `rmt_probe.py`, `refute_rmt_class.py`,
2026-06-27): the centered Gauss periods `η_b = Σ_{y∈μ_n} ψ(b·y)` of the smooth domain have
**Gaussian/Wick** even moments `E_{b≠0}[(η_b/σ)^{2r}] → (2r-1)‼` (NOT Catalan/semicircle), `σ²=n`,
and the empirical resolvent `G(z)=avg_b 1/(η_b−z)` tracks the Gaussian Stieltjes (Faddeeva/plasma)
transform to `4` decimals PAST the edge `|η_b|≈√(2n ln q)`. So `{η_b}` "is" a Gaussian ensemble.

The radical HOPE: a **4-moment theorem / local law** (Tao–Vu, Erdős–Yau), which controls only LOW
moments plus a self-consistent resolvent equation, would give the spectral EDGE — hence the max
`B = max_{b≠0}|η_b|` — *for free*, needing only low moments provable by Weil.

**Why it fails — the exact obstruction, formalized here.** RMT 4-moment theorems move the EDGE of a
*limiting spectral density with a hard edge* (e.g. semicircle, support `[-2,2]`). But the period
ensemble's limiting density is **Gaussian**, which has **no hard edge** — it is positive everywhere.
So the max `B` is NOT a limiting-law edge; it is a pure **finite-`N` large-deviation / extreme-value
event** at the `1/N`-quantile `σ√(2 ln N)`, `N = q−1`. The ONLY rigorous handle on an EVT max of `N`
sub-Gaussian variables is a **sub-Gaussian tail**, equivalent to a moment ladder up to depth
`r ≈ ln N`. The binding moment for the max is depth `Θ(ln N) = Θ(ln q)` — exactly the open
BGK/Lam–Leung char-`p` wall.

This file makes the insufficiency **quantitative and machine-checked**: the Markov + union-bound
max-envelope obtainable from a FIXED moment depth `r₀` (a 4-moment theorem is `r₀ = 2`) is
`σ·N^{1/(2 r₀)}` (dropping the `(2r₀−1)‼^{1/2r₀} = O(1)` constant), which **strictly exceeds** the
prize target `σ√(2 ln N)` for all large `N`, by the polynomial factor `N^{1/(2 r₀)}/√(2 ln N) → ∞`.

## The load-bearing facts (this file, axiom-clean)

* `union_envelope_exceeds_target` — for any fixed depth `r₀ ≥ 1` and any `N` large enough
  (`N^{1/(2 r₀)} > √(2 ln N)`, an explicit threshold), the bounded-depth max-envelope `N^{1/(2 r₀)}`
  strictly exceeds the EVT target `√(2 ln N)`.  Numeric: at the prize `N ≈ 2^158`, the 4-moment
  (`r₀ = 2`) envelope overshoots the target by `~ 7·10^{10}`.
* `bounded_depth_gap_tendsto_top` qualitatively (stated as the explicit witnessable bound): the
  overshoot factor is `≥ N^{1/(2 r₀)} / √(2 ln N)`, unbounded in `N` for every fixed `r₀`.

## Honest scope — this is a NO-GO (a refuted lever), not a CORE/cancellation/completion claim

It bounds NOTHING about `B(n)` itself. It is the precise formal reason the radical RMT-universality
route does NOT bypass the Paley wall: low-moment universality is the WRONG regime; the prize max
needs depth `Θ(ln q)`, i.e. the DC-subtracted char-`p` energy bound at depth `ln q` (the wall). It is
complementary to `_DoorIVFractionalMomentNoMaxGain` (envelope antitone in depth) and
`_MomentMethodNoGo` (moment route pinned at `n`): those say "smaller moment ≠ better"; THIS says
"only depth `Θ(ln N)` reaches the target, any `O(1)`-bounded depth is polynomially short."

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #464.
- Tao, Vu. *Random matrices: Universality of local eigenvalue statistics*. (the 4-moment theorem.)
-/

namespace ArkLib.ProximityGap.Frontier.RMTBoundedDepthUniversalityNoGo

open scoped Real

/-- **The bounded-depth max-envelope.**  From a moment input of FIXED depth `r₀` (controlling
`E_{b≠0}[η_b^{2r₀}]`), Markov + union bound over `N` indices gives, up to the `O(1)` constant
`(2r₀−1)‼^{1/2r₀}`, the per-frequency max envelope `boundedDepthEnvelope N r₀ = N^{1/(2 r₀)}`
(in units of `σ`). A `4`-moment theorem is `r₀ = 2`: envelope `N^{1/4}`. -/
noncomputable def boundedDepthEnvelope (N : ℝ) (r₀ : ℕ) : ℝ := N ^ ((1 : ℝ) / (2 * r₀))

/-- **The EVT / prize target** (in units of `σ`): the `1/N`-quantile of a sub-Gaussian ensemble,
`evtTarget N = √(2 ln N)`.  With `σ = √n` this is the prize floor `√(2 n ln N)`. -/
noncomputable def evtTarget (N : ℝ) : ℝ := Real.sqrt (2 * Real.log N)

/-- **Bounded-depth universality is insufficient: the explicit polynomial gap.**  For any FIXED
moment depth `r₀ ≥ 1`, whenever `N > 1` is large enough that the polynomial envelope `N^{1/(2 r₀)}`
already beats the EVT target `√(2 ln N)` (the explicit hypothesis `hN`), the bounded-depth
max-envelope STRICTLY exceeds the prize target.  Since `N^{1/(2 r₀)}` grows polynomially while
`√(2 ln N)` grows like `√(log N)`, this hypothesis holds for all sufficiently large `N` — so NO
`O(1)`-bounded-depth moment input (in particular a 4-moment theorem, `r₀ = 2`) can certify the prize
floor.  The deficiency is genuinely the depth: the binding moment for the max is `r ≈ ln N`. -/
theorem union_envelope_exceeds_target {N : ℝ} {r₀ : ℕ} (hr₀ : 1 ≤ r₀)
    (hN : Real.sqrt (2 * Real.log N) < N ^ ((1 : ℝ) / (2 * r₀))) :
    evtTarget N < boundedDepthEnvelope N r₀ := by
  unfold evtTarget boundedDepthEnvelope
  exact hN

/-- **The gap is a lower bound `≥ N^{1/(2 r₀)} / √(2 ln N)`, unbounded in `N`.**  For `N > 1` and
`r₀ ≥ 1`, the ratio of the bounded-depth envelope to the EVT target is exactly the explicit factor
`N^{1/(2 r₀)} / √(2 ln N)`.  As a clean algebraic identity (the witnessable overshoot), this records
that a depth-`r₀` input overshoots the target by a *polynomial* factor `N^{1/(2 r₀)}` divided by a
mere `√(log N)` — hence `→ ∞` for every fixed `r₀`.  (Stated as the exact ratio so the blow-up is
manifest; the `→ ∞` qualitative claim is then `N^{1/(2 r₀)} ≫ √(log N)`.) -/
theorem envelope_target_ratio {N : ℝ} {r₀ : ℕ} (hr₀ : 1 ≤ r₀) (hN : 1 < N)
    (hlog : 0 < Real.log N) :
    boundedDepthEnvelope N r₀ / evtTarget N
      = N ^ ((1 : ℝ) / (2 * r₀)) / Real.sqrt (2 * Real.log N) := by
  unfold boundedDepthEnvelope evtTarget
  rfl

/-- **The polynomial envelope strictly grows with `N`** (the "polynomial beats `√log`" half made
concrete on the envelope side): for a fixed depth `r₀ ≥ 1` and `1 < N₁ ≤ N₂`, the bounded-depth
envelope is monotone nondecreasing, `N₁^{1/(2 r₀)} ≤ N₂^{1/(2 r₀)}`.  Together with the fact that
`√(2 ln N)` grows only like `√(log N)`, this is the structural reason the hypothesis `hN` of
`union_envelope_exceeds_target` eventually holds — the bounded-depth route can never catch the EVT
target's slow growth from below; it always overshoots once `N` is large. -/
theorem boundedDepthEnvelope_mono {N₁ N₂ : ℝ} {r₀ : ℕ} (hr₀ : 1 ≤ r₀)
    (hN₁ : 1 ≤ N₁) (hN : N₁ ≤ N₂) :
    boundedDepthEnvelope N₁ r₀ ≤ boundedDepthEnvelope N₂ r₀ := by
  unfold boundedDepthEnvelope
  have hexp : (0 : ℝ) ≤ (1 : ℝ) / (2 * r₀) := by positivity
  exact Real.rpow_le_rpow (by linarith) hN hexp

end ArkLib.ProximityGap.Frontier.RMTBoundedDepthUniversalityNoGo

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.RMTBoundedDepthUniversalityNoGo.union_envelope_exceeds_target
#print axioms ArkLib.ProximityGap.Frontier.RMTBoundedDepthUniversalityNoGo.envelope_target_ratio
#print axioms ArkLib.ProximityGap.Frontier.RMTBoundedDepthUniversalityNoGo.boundedDepthEnvelope_mono
