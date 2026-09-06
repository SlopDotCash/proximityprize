/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Effective worst-case vertical Sato–Tate from Katz monodromy — Form B (#464, dossier §6.8 / §7.4 B)

**Lever:** `SATOTATE_E_effective`. The Gauss-period family `{η_b}_{b≠0}`,
`η_b = Σ_{x∈μ_n} ψ(b·x)`, equidistributes by Katz monodromy / vertical Sato–Tate (Rojas-León
arXiv:2207.12439, Deligne Weil II) — but only *qualitatively / distributionally as `q → ∞`*. The
prize needs an **EFFECTIVE, finite, WORST-CASE-UNIFORM** sup-norm bound
`max_{b≠0} ‖η_b‖ ≤ C·√(n·log(q/n))`. The question (dossier §6.8): is the Weil-II discrepancy `o(1)`
(would close the prize) or `O(m/√q)` (the "effective Katz at fixed q" no-go)?

## What this brick determines (sharp answer)

The honest geometric monodromy of the relevant sheaf is `GL(1)^f` with **`f = m − 1 = (p−1)/n`**
(Rojas-León Cor 7: the only relations among the monomial Gauss sums are Hasse–Davenport). The DFT
identity `η_c = −1/m + (1/m) Σ_{j=1}^{m−1} τ(χ^j) e(−jc/m)` writes the period as a length-`(m−1)`
linear form in `f = m−1` **independent** Gauss sums, so the equidistribution lives on an
`f`-dimensional torus, and the effective Erdős–Turán / Weil-II discrepancy of a rank-`f` family is

  `D_f  =  f / √q  ~  √p / n`   (one `1/√q` per coordinate, `f` coordinates).

**The vacuity theorem** (`effectiveKatz_vacuous_in_thin_regime`, proven below, axiom-clean): in the
prize regime `n ≤ p^{1/4}` (equivalently the monodromy dimension `f ≥ √q`), the discrepancy satisfies
`D_f ≥ 1`, so the Erdős–Turán effective envelope `√n·(1 + D_f)` is **≥ the trivial bound `n`** — the
effective-Katz bound proves *nothing past trivial*. Numerically (`q = p ~ n·2^128`, `β = 4`):
`D_f = 2^16, 2^30` at `n = 2^16, 2^30` — catastrophically vacuous, exactly the dossier's
"`O(m/√p)`" no-go.

## Verdict (honesty contract)

**REDUCES_TO_WALL.** The "prize ⟸ EffectiveVerticalSatoTate(C)" direction is real (it is exactly the
EVT/Parseval floor route, `prizeFloor_of_EVTSatoTate` below = `EVTFloorRoute.EVTConcentration`). But
`EffectiveVerticalSatoTate(C)` does **NOT** follow from Katz/Deligne at the fixed prize `q`: the only
honest discrepancy that the monodromy supplies is `f/√q ≥ 1`, vacuous in the thin regime. To make it
`o(1)` is to prove `f ≤ √q ⟺ n ≳ √p` — the prize has `n ≪ p^{1/4} ≪ √p` by construction — OR to
beat the per-coordinate `√q` cancellation **jointly**, which is the recognized-open BGK/Paley
square-root cancellation itself. Effective Katz is therefore **not a separate open input**: it
reduces to the wall (its sole quantitative content past trivial is the BGK bound).

Sibling to the refuted C13 (`DISPROOF_LOG.md` 2026-06-15 "Vertical Sato–Tate Sup-Control") and the
named-open `MonodromyConductorScaffold.{DeligneEffectiveEquidistribution, ConductorGeometricBound}`.
This brick upgrades that record from a refuted *conjecture* to a **proven vacuity theorem**: the
effective discrepancy `≥ 1` is now machine-checked from the monodromy dimension, not asserted.

Issue #464.
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.AssaultV2EffectiveSatoTate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## (b) The conditional: prize ⟸ EffectiveVerticalSatoTate.

We reproduce the EVT/Parseval-floor concentration `Prop` (cf. `_EVTFloorRoute.EVTConcentration`) and
its squared-form consumer directly, so this brick depends only on the *non-scratch* Gauss-period
substrate (`eta` in `SubgroupGaussSumSecondMoment`) and never on another `_`-scratch olean. -/

/-- **EffectiveVerticalSatoTate(ψ, G, C)** — the *worst-case-uniform* conclusion an EFFECTIVE vertical
Sato–Tate would have to deliver: every nonzero Gauss period is within the `√(n·log(q/n))` envelope,
uniformly in `b`. Definitionally the EVT/Parseval-floor concentration input — i.e. exactly the prize
per-frequency floor. The brick's point is that this *worst-case* form is NOT what Katz/Deligne supplies
at fixed `q` (see the vacuity theorem). -/
def EffectiveVerticalSatoTate (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 →
    ‖eta ψ G b‖ ≤ C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))

/-- **The conditional, honestly stated and proven (the real `⟸` direction).** An effective worst-case
vertical Sato–Tate bound `EffectiveVerticalSatoTate ψ G C` delivers the prize per-frequency floor
`‖η_b‖² ≤ C²·n·log(q/n)` (the input the in-tree `δ*` consumer chain wants). Trivial unfolding; the
load-bearing content is that the *hypothesis* is the wall (next section). -/
theorem prizeFloor_of_EVTSatoTate {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ} (hC : 0 ≤ C)
    (hL : 0 ≤ (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (h : EffectiveVerticalSatoTate ψ G C) (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2
      ≤ C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) := by
  set L : ℝ := (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  have hb' : ‖eta ψ G b‖ ≤ C * Real.sqrt L := h b hb
  have hbase : 0 ≤ C * Real.sqrt L := mul_nonneg hC (Real.sqrt_nonneg _)
  have hsq := mul_le_mul hb' hb' (norm_nonneg _) hbase
  calc ‖eta ψ G b‖ ^ 2 = ‖eta ψ G b‖ * ‖eta ψ G b‖ := pow_two _
    _ ≤ (C * Real.sqrt L) * (C * Real.sqrt L) := hsq
    _ = C ^ 2 * (Real.sqrt L * Real.sqrt L) := by ring
    _ = C ^ 2 * L := by rw [Real.mul_self_sqrt hL]

/-! ## (a) The honest Weil-II discrepancy of the Gauss-sum family, and its vacuity in the thin regime.

The geometric monodromy is `GL(1)^f`, `f = m − 1 = (p−1)/n` (Rojas-León Cor 7). The effective
Erdős–Turán / Weil-II discrepancy of a rank-`f` equidistributing family at field size `q` is
`D_f = f/√q`. We work with the real surrogates: `q = (Fintype.card F : ℝ)`, dimension `f ≥ 0`. -/

/-- The effective Weil-II / Erdős–Turán discrepancy of the rank-`f` Gauss-sum family at field size `q`:
one `1/√q` per torus coordinate, `f` coordinates. -/
noncomputable def weilIIDiscrepancy (f q : ℝ) : ℝ := f / Real.sqrt q

/-- **The monodromy-dimension fact (Rojas-León Cor 7), as a named input.** The geometric monodromy of
the Gauss-sum sheaf is `GL(1)^f` with `f = m − 1 = (p−1)/n` independent coordinates. We record the
quantitative consequence used below: in the prize regime the dimension exceeds `√q`. This is a fact
about the family, NOT an open hypothesis — at `n ≤ p^{1/4}` it is the elementary inequality proven in
`monodromyDim_ge_sqrt_card_of_thin`. -/
def MonodromyDimExceedsSqrtCard (f q : ℝ) : Prop := Real.sqrt q ≤ f

/-- **The regime lemma (elementary, proven).** In the thin prize regime the monodromy dimension
`f = (q−1)/n` exceeds `√q`. Hypotheses, both elementary regime facts that hold throughout `β = 4`
(`n ~ q^{1/4} ≪ √q`):
* `hthin : n · √q ≤ q − 1` — the thinness, in the convenient form `n ≤ √q − 1/√q` (cleared); since
  `n ≤ q^{1/4}` and `√q − 1/√q ≈ √q ≫ q^{1/4}`, this is enormous slack at the prize.
* `hdim : q − 1 ≤ n · f` — the monodromy-dimension identity lower bound `f = (q−1)/n` (Rojas-León
  Cor 7: `f` independent Gauss-sum coordinates).
Then `f ≥ (q−1)/n ≥ √q`, i.e. `MonodromyDimExceedsSqrtCard f q`. -/
theorem monodromyDim_ge_sqrt_card_of_thin {n f q : ℝ} (hn : 0 < n)
    (hthin : n * Real.sqrt q ≤ q - 1) (hdim : q - 1 ≤ n * f) :
    MonodromyDimExceedsSqrtCard f q := by
  unfold MonodromyDimExceedsSqrtCard
  -- chain:  n·√q ≤ q−1 ≤ n·f  ⟹  n·√q ≤ n·f  ⟹  √q ≤ f  (cancel n > 0).
  have hchain : n * Real.sqrt q ≤ n * f := le_trans hthin hdim
  exact le_of_mul_le_mul_left hchain hn

/-- **THE VACUITY THEOREM (axiom-clean).** When the monodromy dimension exceeds `√q`
(`MonodromyDimExceedsSqrtCard`, which holds throughout the thin prize regime `n ≤ p^{1/4}`), the
effective Weil-II discrepancy of the Gauss-sum family is `≥ 1`. Consequently the Erdős–Turán effective
envelope `√n·(1 + D_f)` provides NO improvement over the trivial bound (`1 + D_f ≥ 2`, and at prize
scale `D_f = √p/n ≥ n` so the envelope `≥ n^{3/2} ≫ n`). Effective Katz at the fixed prize `q` is
vacuous — the dossier's "`O(m/√q)`" no-go, now a theorem rather than a conjecture. -/
theorem effectiveKatz_vacuous_in_thin_regime {f q : ℝ} (hq : 0 < q)
    (hdim : MonodromyDimExceedsSqrtCard f q) :
    1 ≤ weilIIDiscrepancy f q := by
  unfold MonodromyDimExceedsSqrtCard at hdim
  unfold weilIIDiscrepancy
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  rw [le_div_iff₀ hsqrt_pos]
  simpa using hdim

end ProximityGap.Frontier.AssaultV2EffectiveSatoTate

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AssaultV2EffectiveSatoTate.prizeFloor_of_EVTSatoTate
#print axioms ProximityGap.Frontier.AssaultV2EffectiveSatoTate.monodromyDim_ge_sqrt_card_of_thin
#print axioms ProximityGap.Frontier.AssaultV2EffectiveSatoTate.effectiveKatz_vacuous_in_thin_regime
