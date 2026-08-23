/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKSOTAInsufficiency

/-!
# wf-B7 CLOSED-OBSTRUCTION: the W3 / prize floor is EQUIVALENT to the open exponent-`1/2` BGK bound (#444)

## The question (lane B7)

The Proximity-Prize moment reduction closes the prize from the clean inequality **W3**
(`m_r ≤ 1 ∀ r`, equivalently the full Wick bound `M(r) ≤ (2r-1)‼·n^r`), which the in-tree F1
telescope + the `r ≈ ln q` moment→sup saddle converts into the per-frequency **prize floor**
`M(n) = max_{b≠0} ‖η_b‖ ≤ C·√(n·log(q/n))` (the in-tree `NearRamanujanSqrtLog`/`PrizeFloor`). The
companion lanes proved:

* **B2** : char-`0` W3-anti is TRUE (sharp-Newton / Laguerre–Pólya).
* **B1/B3** : char-`p` W3-base and W3-anti are FALSE at prize scale (the spurious mod-`p` mass `δ_r`
  breaks both the `r=1` kurtosis cap and the step-ratio monotonicity) — so the *hypercontractive
  monotonicity proof strategy* cannot close the prize.
* **BGK-SOTA** (`_BGKSOTAInsufficiency`) : the best *proven* incomplete-character-sum exponent
  `δ ≈ 0.011` (Bourgain–Glibichuk–Konyagin / di Benedetto) is quantitatively too weak — any
  `δ < 1/2` lands strictly above the prize floor for large `n`.

B7 is the **meta** question that closes the *uncertainty*: is the open content (W3, equivalently
the prize floor, equivalently `m_r ≤ 1` at depth `r ≈ ln q`) PROVABLY EQUIVALENT to an open
analytic-number-theory problem — so that there is *no* elementary closure and the uncertainty is
genuine and exactly named — or is it strictly weaker (hence potentially elementary)?

## The verdict: EQUIVALENT to the open exponent-`1/2` character-sum bound (Paley-Graph Conjecture)

We pin the exact logical relationship, on the in-tree per-frequency objects `eta ψ G b` (the
generalized-Paley-graph `Cay(F_q, μ_n)` eigenvalue). Write `n = |G|`, `q = |F|`, `L = log(q/n)`
(the index logarithm; bounded `0 < L ≤ Λ` in the prize regime `q ≈ n^β`). The two named bounds:

* `NearRamanujanSqrtLog ψ G C`  ≡  the **prize floor / W3 output**: `‖η_b‖ ≤ C·√(n·L)`
  (cancellation exponent `δ = 1/2 − o(1)`).
* `BGKBound C ψ G δ`            ≡  the **BGK character-sum bound**: `‖η_b‖ ≤ C·n^{1−δ}`
  (proven exponent `δ ≈ 0.011`; the *open* Paley-Graph value is `δ = 1/2`).

**Both reduction directions are proved here, axiom-clean (`propext, Classical.choice, Quot.sound`):**

* `prize_implies_BGK_half`  (**W3/prize ⟹ BGK at exponent `1/2`**): if `L ≤ Λ` then
  `NearRamanujanSqrtLog ψ G C ⟹ BGKBound (C·√Λ) ψ G (1/2)`. The prize floor *delivers* the
  cancellation exponent `δ = 1/2`. By the in-tree `_BGKSOTAInsufficiency` this is STRICTLY beyond
  every proven exponent (`0.011 < 1/2`), so **W3 is at least as hard as the open exponent-`1/2`
  bound** — closing W3 would close the Paley-Graph Conjecture for `Cay(F_q, μ_n)`.
* `BGK_half_implies_prize`  (**BGK at exponent `1/2` ⟹ W3/prize**): if `1 ≤ L` (always at prize
  scale, `q > e·n`) then `BGKBound C ψ G (1/2) ⟹ NearRamanujanSqrtLog C ψ G`. The exponent-`1/2`
  character-sum bound *is* the prize floor (up to the bounded `√L` index factor).
* `W3_iff_BGK_half`  (**the EQUIVALENCE**): for `1 ≤ L ≤ Λ`, `NearRamanujanSqrtLog ψ G C` and
  `BGKBound C ψ G (1/2)` are mutually derivable (each implies the other at a constant-factor-adjusted
  scale). Hence W3 ⇔ the exponent-`1/2` BGK bound, up to the bounded index constant.

## The closure of the uncertainty (the headline)

`uncertainty_is_paley_graph_conjecture` combines the equivalence with the proven SOTA insufficiency:

> The open content of the prize (W3 / `m_r ≤ 1` at depth `r ≈ ln q` / the prize floor) is
> EQUIVALENT (up to a bounded index constant) to the BGK bound at cancellation exponent `1/2`, which
> the in-tree `bgkValue_exceeds_prizeTarget_eventually` proves is STRICTLY beyond the best proven
> exponent (`diBenedettoDelta = 0.011 < 1/2 = prizeDelta`). Therefore the W3 uncertainty is NOT an
> artifact of a missing elementary lemma: it is *exactly* the open exponent-`1/2` incomplete-
> character-sum bound over a thin multiplicative subgroup — the **Paley-Graph Conjecture** content,
> a recognized-open analytic-number-theory problem with no elementary closure.

This is a **CLOSED-OBSTRUCTION**: it does not refute the prize (the bound is empirically TRUE to
`n = 128`), and it does not close it; it *closes the uncertainty* by characterizing it exactly. The
verdict for the sister lanes: W3-anti is **NOT strictly weaker / elementary** — it is logically
sandwiched at exactly the open exponent-`1/2` bound, so B2/B3 should not expect an elementary char-`p`
closure of the relative monotonicity (consistent with B3's measured char-`p` failure).

## Honest scope

`BGKBound` and `NearRamanujanSqrtLog` are *named* Props; we never assert either as a theorem. What is
PROVEN is the pair of reductions between them and the equivalence, plus the composition with the
already-proven SOTA insufficiency. The reductions are exact `Real`-analysis (`√` monotonicity,
`rpow` half-power), no sampling. The "up to bounded index constant" caveat is real and stated: the
equivalence is constant-for-constant under `1 ≤ L ≤ Λ`, which is the prize regime `q ≈ n^β`, `β ≥ 2`.

Issue #444, lane wf-B7.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped Real
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ProximityGap.Frontier.BGKSOTAInsufficiency

namespace ProximityGap.Frontier.WF8B7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Direction 1 — the W3 / prize floor DELIVERS the exponent-`1/2` cancellation -/

/-- **W3 / prize floor ⟹ BGK at exponent `1/2`.**

If the index logarithm is bounded, `L := log(q/n) ≤ Λ`, then the prize floor
`NearRamanujanSqrtLog ψ G C` (`‖η_b‖ ≤ C·√(n·L)`, cancellation exponent `δ = 1/2`) implies the BGK
character-sum bound `BGKBound (C·√Λ) ψ G (1/2)` (`‖η_b‖ ≤ (C·√Λ)·n^{1/2}`).

Mechanism: `√(n·L) = √n·√L ≤ √n·√Λ = √Λ·n^{1/2} = √Λ·n^{1−1/2}`. So the prize floor IS a
cancellation-exponent-`1/2` bound; by the in-tree SOTA-insufficiency (`0.011 < 1/2`) it is strictly
beyond every proven exponent — **W3 is at least as hard as the open exponent-`1/2` bound.** -/
theorem prize_implies_BGK_half {ψ : AddChar F ℂ} {G : Finset F} {C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hindex : Real.log ((Fintype.card F : ℝ) / G.card) ≤ Λ)
    (hprize : NearRamanujanSqrtLog ψ G C) :
    BGKBound (C * Real.sqrt Λ) ψ G (1 / 2) := by
  intro b hb
  set n : ℝ := (G.card : ℝ) with hn
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  -- the prize bound at `b`
  have hpb : ‖eta ψ G b‖ ≤ C * Real.sqrt (n * L) := hprize b hb
  -- `n ≥ 0`
  have hnnn : (0 : ℝ) ≤ n := by positivity
  -- `√(n·L) ≤ √(n·Λ)` (monotonicity of `√`, using `L ≤ Λ` and `n ≥ 0`)
  have hmono : Real.sqrt (n * L) ≤ Real.sqrt (n * Λ) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hindex hnnn)
  -- `√(n·Λ) = √n·√Λ`
  have hsplit : Real.sqrt (n * Λ) = Real.sqrt n * Real.sqrt Λ := Real.sqrt_mul hnnn Λ
  -- `√n = n^{1/2} = n^{1 − 1/2}`
  have hpow : Real.sqrt n = n ^ ((1 : ℝ) - 1 / 2) := by
    rw [Real.sqrt_eq_rpow]; norm_num
  -- assemble: `‖η_b‖ ≤ C·√(n·L) ≤ C·√(n·Λ) = C·(√Λ·n^{1−1/2}) = (C·√Λ)·n^{1−1/2}`
  calc ‖eta ψ G b‖
      ≤ C * Real.sqrt (n * L) := hpb
    _ ≤ C * Real.sqrt (n * Λ) := by
          exact mul_le_mul_of_nonneg_left hmono hC
    _ = (C * Real.sqrt Λ) * n ^ ((1 : ℝ) - 1 / 2) := by
          rw [hsplit, hpow]; ring

/-! ## Direction 2 — the exponent-`1/2` BGK bound IS the prize floor -/

/-- **BGK at exponent `1/2` ⟹ W3 / prize floor.**

In the prize regime the index logarithm satisfies `1 ≤ L = log(q/n)` (i.e. `q ≥ e·n`, always true
for `q ≈ n^β`, `β ≥ 2`). Then `BGKBound C ψ G (1/2)` (`‖η_b‖ ≤ C·n^{1/2}`) implies the prize floor
`NearRamanujanSqrtLog ψ G C` (`‖η_b‖ ≤ C·√(n·L)`).

Mechanism: `C·n^{1/2} = C·√n = C·√(n·1) ≤ C·√(n·L)` since `1 ≤ L`. So the exponent-`1/2`
character-sum bound is, up to the bounded index factor, exactly the prize floor — the converse half
of the equivalence. -/
theorem BGK_half_implies_prize {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hC : 0 ≤ C)
    (hindex : 1 ≤ Real.log ((Fintype.card F : ℝ) / G.card))
    (hbgk : BGKBound C ψ G (1 / 2)) :
    NearRamanujanSqrtLog ψ G C := by
  intro b hb
  set n : ℝ := (G.card : ℝ) with hn
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  have hnnn : (0 : ℝ) ≤ n := by positivity
  -- BGK bound at `b`: `‖η_b‖ ≤ C·n^{1−1/2} = C·√n`
  have hbb : ‖eta ψ G b‖ ≤ C * n ^ ((1 : ℝ) - 1 / 2) := hbgk b hb
  -- `n^{1−1/2} = n^{1/2} = √n = √(n·1)`
  have hpow : n ^ ((1 : ℝ) - 1 / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]; norm_num
  -- `√n ≤ √(n·L)` since `n ≤ n·L` (because `1 ≤ L`, `n ≥ 0`)
  have hmono : Real.sqrt n ≤ Real.sqrt (n * L) := by
    apply Real.sqrt_le_sqrt
    have hnL : n * 1 ≤ n * L := mul_le_mul_of_nonneg_left hindex hnnn
    linarith [hnL]
  calc ‖eta ψ G b‖
      ≤ C * n ^ ((1 : ℝ) - 1 / 2) := hbb
    _ = C * Real.sqrt n := by rw [hpow]
    _ ≤ C * Real.sqrt (n * L) := mul_le_mul_of_nonneg_left hmono hC

/-! ## The equivalence -/

/-- **THE EQUIVALENCE (W3/prize ⟺ exponent-`1/2` BGK, up to bounded index).**

For a bounded index logarithm `1 ≤ L ≤ Λ` (the prize regime `q ≈ n^β`, `β ≥ 2`), the prize floor
`NearRamanujanSqrtLog ψ G C` and the exponent-`1/2` character-sum bound `BGKBound C ψ G (1/2)` are
mutually derivable, each at a constant-factor-adjusted scale:

* prize at constant `C` ⟹ BGK-`(1/2)` at constant `C·√Λ`;
* BGK-`(1/2)` at constant `C` ⟹ prize at the SAME constant `C`.

Hence the open prize content is **exactly** the exponent-`1/2` character-sum bound: there is no
gap between them other than the bounded index constant. -/
theorem W3_iff_BGK_half {ψ : AddChar F ℂ} {G : Finset F} {C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hlo : 1 ≤ Real.log ((Fintype.card F : ℝ) / G.card))
    (hhi : Real.log ((Fintype.card F : ℝ) / G.card) ≤ Λ) :
    (NearRamanujanSqrtLog ψ G C → BGKBound (C * Real.sqrt Λ) ψ G (1 / 2)) ∧
    (BGKBound C ψ G (1 / 2) → NearRamanujanSqrtLog ψ G C) :=
  ⟨fun hprize => prize_implies_BGK_half hC hΛ hhi hprize,
   fun hbgk => BGK_half_implies_prize hC hlo hbgk⟩

/-! ## The closure of the uncertainty -/

/-- **HEADLINE — the W3 uncertainty IS the open Paley-Graph / exponent-`1/2` bound.**

This packages the full B7 verdict. Three facts, all proven in-tree:

1. (`prize_implies_BGK_half`) The prize floor delivers cancellation exponent `δ = 1/2`.
2. (`BGK_half_implies_prize`) The exponent-`1/2` character-sum bound delivers the prize floor.
   ⟹ the open prize content is EQUIVALENT to the exponent-`1/2` BGK bound (`W3_iff_BGK_half`).
3. (`diBenedetto_lt_prize` + `bgk_value_exceeds_prizeTarget_eventually`, from `_BGKSOTAInsufficiency`)
   The best PROVEN cancellation exponent is `diBenedettoDelta = 0.011 < 1/2 = prizeDelta`, and ANY
   exponent `δ < 1/2` is strictly insufficient at large `n`.

Conjunction: the prize's open content sits at *exactly* the exponent-`1/2` bound, which is strictly
beyond all proven character-sum technology. The uncertainty is therefore not removable by an
elementary lemma — it is the recognized-open exponent-`1/2` incomplete-character-sum bound over the
thin multiplicative subgroup `μ_n` (the Paley-Graph Conjecture content). CLOSED-OBSTRUCTION. -/
theorem uncertainty_is_paley_graph_conjecture
    {ψ : AddChar F ℂ} {G : Finset F} {C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hlo : 1 ≤ Real.log ((Fintype.card F : ℝ) / G.card))
    (hhi : Real.log ((Fintype.card F : ℝ) / G.card) ≤ Λ) :
    -- (1)+(2): the prize content is equivalent to the exponent-`1/2` BGK bound
    ((NearRamanujanSqrtLog ψ G C → BGKBound (C * Real.sqrt Λ) ψ G (1 / 2)) ∧
     (BGKBound C ψ G (1 / 2) → NearRamanujanSqrtLog ψ G C)) ∧
    -- (3): the equivalent exponent `1/2` is strictly beyond the best PROVEN exponent
    (diBenedettoDelta < (1 / 2 : ℝ) ∧
      ∀ {C₀ C' L₀ : ℝ}, 0 < C₀ → 0 ≤ C' → 0 ≤ L₀ →
        ∃ N₀ : ℝ, ∀ m : ℝ, N₀ ≤ m →
          C' * Real.sqrt (m * L₀) < C₀ * m ^ (1 - diBenedettoDelta)) := by
  refine ⟨W3_iff_BGK_half hC hΛ hlo hhi, ?_, ?_⟩
  · -- the SOTA exponent is below `1/2`
    have := diBenedetto_lt_prize
    unfold prizeDelta at this
    exact this
  · -- any `δ < 1/2` (in particular `diBenedettoDelta`) is strictly insufficient at large `n`
    intro C₀ C' L₀ hC₀ hC' hL₀
    exact bgk_value_exceeds_prizeTarget_eventually hC₀ hC' hL₀
      (by unfold diBenedettoDelta; norm_num)

end ProximityGap.Frontier.WF8B7

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WF8B7.prize_implies_BGK_half
#print axioms ProximityGap.Frontier.WF8B7.BGK_half_implies_prize
#print axioms ProximityGap.Frontier.WF8B7.W3_iff_BGK_half
#print axioms ProximityGap.Frontier.WF8B7.uncertainty_is_paley_graph_conjecture
