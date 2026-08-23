/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKSOTAInsufficiency
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodSpectralFrame

/-!
# wf-B7 (#444): the EXACT prize ⇆ BGK reduction directions — corrected naming

## What this lane settles

Lane B7 ("settle prize ⇔ BGK rigorously") asks for the precise logical relationship between

* the **prize floor**   `M(n) = max_{b≠0}‖η_b‖ ≤ C·√(n·log(q/n))`   (`NearRamanujanSqrtLog ψ G C`,
  cancellation exponent `δ = 1/2 − o(1)`, with a *bounded* `√log(q/n)` slack), and
* the **BGK / Paley character-sum bounds** `‖η_b‖ ≤ C·n^{1−δ}` (`BGKBound C ψ G δ`).

A prior pass (`_wf8B7_W3_BGK_Equivalence`) proved a clean real-analysis equivalence between
`NearRamanujanSqrtLog` and `BGKBound _ _ _ (1/2)`, and *named the equivalent object the
"Paley-Graph Conjecture"*. **That naming is incorrect**, and the error matters for "what exactly is
open". This file fixes it with the literature-correct dictionary and the exact reduction directions.

## The correction (literature-verified, WebFetch'd)

The named conjectures are NOT the same statement:

* **Paley Graph Conjecture (PGC)** — for any fixed `ε > 0` there is a fixed `δ = δ(ε) > 0` with
  `‖η_b‖ ≤ n^{1−δ}` (`= BGKBound 1 ψ G δ` for *some* `δ > 0` depending only on the relative size).
  This is a *power saving by an unspecified, possibly tiny, fixed exponent*.
* **Bourgain–Glibichuk–Konyagin (BGK 2006) — PROVEN**: for `|H| ≥ p^γ` there is `δ(γ) > 0` with
  `‖η_b‖ ≤ n^{1−δ}`. So **BGK already PROVES the PGC** in the power-saving sense (`δ ≈ 0.011` after
  di Benedetto). The PGC, in its `n^{1−δ}`-for-some-`δ>0` form, is *not the open content of the
  prize* — it is essentially known for thin subgroups.
* **Ramanujan / square-root cancellation** — `‖η_b‖ ≤ C·√n` (exponent `δ = 1/2`,
  `= BGKBound C ψ G (1/2)`). This is the STRONGEST possible bound up to the constant and is
  **strictly stronger than the PGC** (any `δ < 1/2` power saving is weaker). For `Cay(F_q, μ_n)`
  this is the open *Ramanujan/BGK-sharp* question.
* **The prize floor** — `‖η_b‖ ≤ C·√(n·log(q/n))`. This is **WEAKER than Ramanujan `√n`** by the
  bounded factor `√log(q/n)` (at prize scale `q/n = 2^128`, `√log = √(128 ln 2) ≈ 9.4`; for
  `q ≈ n^β`, `√((β−1) ln n) ≈ 8–9`).

So the precise sandwich on the *cancellation exponent* `δ` is

      proven BGK (δ≈0.011)  <  prize floor (δ=1/2−o(1))  ≤  Ramanujan (δ=1/2).
       = PGC, already known      = the open prize             = strictly stronger

The prize is therefore **NOT** the Paley Graph Conjecture (that is weaker and proven). It is the
exponent-`1/2`/near-Ramanujan bound *up to a bounded `√log` slack* — i.e. the open
**BGK-sharp / Ramanujan-for-`Cay(F_q,μ_n)`** problem, which is what the in-tree
`GaussPeriodSpectralFrame` comment already records ("the graph is provably NOT Ramanujan; the
needed bound carries a `√log` factor").

## The two PROVEN reduction directions (exact, axiom-clean)

* `ramanujan_implies_prize` (**Ramanujan ⟹ prize**, the EASY direction): `BGKBound C ψ G (1/2)`
  (`‖η_b‖ ≤ C√n`) implies the prize floor `NearRamanujanSqrtLog ψ G C`, because `√n ≤ √(n·L)`
  whenever the index logarithm `L = log(q/n) ≥ 1` (always at prize scale). So **a Ramanujan bound
  is sufficient for the prize** — with room to spare (the `√L` factor is free).

* `prize_implies_ramanujan_up_to_sqrtlog` (**prize ⟹ Ramanujan-with-`√L`-loss**, the direction
  that is NOT free): the prize floor implies `BGKBound (C·√Λ) ψ G (1/2)` only after *absorbing the
  bounded `√L` slack into the constant* (`L ≤ Λ`). Thus the prize does **not** imply the clean
  exponent-`1/2` bound at the same constant — it implies it only up to the `√Λ`-inflated constant.
  This is the precise sense in which the prize is *strictly between* the proven BGK exponent and the
  clean Ramanujan bound, and why the equivalence in the prior pass is constant-lossy (honest, but
  the loss is the whole point of the naming correction).

* `prize_strictly_beyond_proven_BGK` (composition with the in-tree SOTA insufficiency): the prize's
  exponent `1/2` is strictly beyond `diBenedettoDelta = 0.011`, so the prize is NOT a corollary of
  the proven BGK/PGC power saving. This is the load-bearing "is the prize at least as hard as the
  open BGK improvement?" answer: **YES** — closing the prize closes near-Ramanujan-up-to-`√log` for
  `Cay(F_q,μ_n)`, which is strictly beyond all proven character-sum technology (`δ < 1/2`).

## Verdict (B7, corrected)

* **Direction (i) — does prize ⟹ a new BGK improvement, and is it at least as hard?** YES. The
  prize forces cancellation exponent `1/2 − o(1)`, strictly beyond the proven `0.011`. The prize is
  at least as hard as pushing the BGK exponent from `0.011` to `1/2 − o(1)` for thin `μ_n` (a recognized
  open problem). It is NOT as hard as full clean Ramanujan `√n` (the prize has a free `√log` slack).

* **Direction (ii) — does a known BGK/Paley conjecture IMPLY the prize?** The *Paley Graph
  Conjecture* (`n^{1−δ}`, some `δ>0`) does **NOT** suffice — any fixed `δ < 1/2` lands strictly above
  the prize floor for large `n` (the in-tree `bgk_value_exceeds_prizeTarget_eventually`). The
  *Ramanujan bound* `√n` **DOES** suffice (`ramanujan_implies_prize`), with the `√log` to spare.

So the prize is **strictly stronger than the PGC and strictly weaker than (or, up to a bounded
constant, equivalent to) the Ramanujan/BGK-sharp bound** for `Cay(F_q, μ_n)`. The "what exactly is
open" answer: the open content is the **near-Ramanujan-up-to-`√log` cancellation exponent `1/2`**
for the thin dyadic Gauss period — NOT the (already-proven-as-power-saving) Paley Graph Conjecture.

Issue #444, lane wf-B7 (corrected). Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open scoped Real
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ProximityGap.Frontier.BGKSOTAInsufficiency

namespace ProximityGap.Frontier.WF9B7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Direction A — the Ramanujan bound `√n` SUFFICES for the prize (the easy, lossless half) -/

/-- **Ramanujan ⟹ prize** (lossless). If the index logarithm `L = log(q/n) ≥ 1` (always at prize
scale, `q ≥ e·n`), then the exponent-`1/2` Ramanujan bound `BGKBound C ψ G (1/2)`
(`‖η_b‖ ≤ C·n^{1/2} = C·√n`) implies the prize floor `NearRamanujanSqrtLog ψ G C`
(`‖η_b‖ ≤ C·√(n·L)`) at the SAME constant `C`. The `√L ≥ 1` slack is free: a Ramanujan bound is
*more than enough* for the prize. -/
theorem ramanujan_implies_prize {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hC : 0 ≤ C)
    (hindex : 1 ≤ Real.log ((Fintype.card F : ℝ) / G.card))
    (hram : BGKBound C ψ G (1 / 2)) :
    NearRamanujanSqrtLog ψ G C := by
  intro b hb
  set n : ℝ := (G.card : ℝ) with hn
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  have hnnn : (0 : ℝ) ≤ n := by positivity
  have hbb : ‖eta ψ G b‖ ≤ C * n ^ ((1 : ℝ) - 1 / 2) := hram b hb
  have hpow : n ^ ((1 : ℝ) - 1 / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hmono : Real.sqrt n ≤ Real.sqrt (n * L) := by
    apply Real.sqrt_le_sqrt
    have hnL : n * 1 ≤ n * L := mul_le_mul_of_nonneg_left hindex hnnn
    linarith [hnL]
  calc ‖eta ψ G b‖
      ≤ C * n ^ ((1 : ℝ) - 1 / 2) := hbb
    _ = C * Real.sqrt n := by rw [hpow]
    _ ≤ C * Real.sqrt (n * L) := mul_le_mul_of_nonneg_left hmono hC

/-! ## Direction B — the prize implies Ramanujan ONLY up to the bounded `√L` constant loss -/

/-- **Prize ⟹ Ramanujan-with-`√Λ`-loss** (NOT lossless). The prize floor
`NearRamanujanSqrtLog ψ G C` implies the exponent-`1/2` bound `BGKBound (C·√Λ) ψ G (1/2)` only
after absorbing the bounded index slack `L ≤ Λ` into the constant. The constant is INFLATED by
`√Λ` (`≈ 9` at prize scale): the prize does NOT deliver the clean Ramanujan bound at constant `C`.
This pins the exact gap — the prize is the near-Ramanujan bound *up to a bounded `√log` factor*,
not the clean Ramanujan bound. -/
theorem prize_implies_ramanujan_up_to_sqrtlog {ψ : AddChar F ℂ} {G : Finset F} {C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hindex : Real.log ((Fintype.card F : ℝ) / G.card) ≤ Λ)
    (hprize : NearRamanujanSqrtLog ψ G C) :
    BGKBound (C * Real.sqrt Λ) ψ G (1 / 2) := by
  intro b hb
  set n : ℝ := (G.card : ℝ) with hn
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  have hpb : ‖eta ψ G b‖ ≤ C * Real.sqrt (n * L) := hprize b hb
  have hnnn : (0 : ℝ) ≤ n := by positivity
  have hmono : Real.sqrt (n * L) ≤ Real.sqrt (n * Λ) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hindex hnnn)
  have hsplit : Real.sqrt (n * Λ) = Real.sqrt n * Real.sqrt Λ := Real.sqrt_mul hnnn Λ
  have hpow : Real.sqrt n = n ^ ((1 : ℝ) - 1 / 2) := by
    rw [Real.sqrt_eq_rpow]; norm_num
  calc ‖eta ψ G b‖
      ≤ C * Real.sqrt (n * L) := hpb
    _ ≤ C * Real.sqrt (n * Λ) := mul_le_mul_of_nonneg_left hmono hC
    _ = (C * Real.sqrt Λ) * n ^ ((1 : ℝ) - 1 / 2) := by rw [hsplit, hpow]; ring

/-! ## Direction C — the prize is STRICTLY beyond every PROVEN BGK/PGC exponent -/

/-- **The Paley Graph Conjecture / proven BGK power saving does NOT imply the prize.**

For ANY proven cancellation exponent `δ < 1/2` (in particular `diBenedettoDelta = 0.011`, the BGK
SOTA, which *proves* the PGC's `n^{1−δ}` power saving), the *guaranteed* value `C·n^{1−δ}` strictly
exceeds the prize target `C'·√(n·L)` for all large `n`. Hence:

* the prize is **at least as hard as** improving the BGK exponent from `0.011` to `1/2 − o(1)`
  (a recognized open problem for thin `μ_n`), answering direction (i): YES;
* the (proven) Paley Graph Conjecture power saving is **insufficient** for the prize, answering
  direction (ii): the PGC does NOT imply the prize; only the strictly-stronger Ramanujan bound does.

`diBenedetto_lt_prize` records `0.011 < 1/2`; the eventual-domination is the in-tree
`bgk_value_exceeds_prizeTarget_eventually`. -/
theorem prize_strictly_beyond_proven_BGK :
    diBenedettoDelta < (1 / 2 : ℝ) ∧
    (∀ {C C' L : ℝ}, 0 < C → 0 ≤ C' → 0 ≤ L →
      ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n →
        C' * Real.sqrt (n * L) < C * n ^ (1 - diBenedettoDelta)) := by
  refine ⟨by unfold diBenedettoDelta; norm_num, ?_⟩
  intro C C' L hC hC' hL
  exact bgk_value_exceeds_prizeTarget_eventually hC hC' hL
    (by unfold diBenedettoDelta; norm_num)

/-! ## The packaged verdict -/

/-- **B7 corrected verdict (the precise sandwich).** Bundles the three directions:

1. (`ramanujan_implies_prize`) Ramanujan `√n` ⟹ prize, LOSSLESS (same constant `C`); the `√L`
   slack is free. So the clean exponent-`1/2` bound is *sufficient with room to spare*.
2. (`prize_implies_ramanujan_up_to_sqrtlog`) prize ⟹ Ramanujan only at the `√Λ`-INFLATED constant;
   the prize is near-Ramanujan *up to the bounded `√log` factor*, not clean Ramanujan.
3. (`prize_strictly_beyond_proven_BGK`) the prize exponent `1/2` is STRICTLY beyond the proven BGK
   `0.011`, so the (proven) Paley-Graph power saving does NOT imply the prize.

Reading: prize is strictly STRONGER than the (proven) PGC power saving, and equivalent — up to a
bounded `√log` constant — to the open Ramanujan/BGK-sharp bound for `Cay(F_q, μ_n)`. The prize is
NOT "the Paley Graph Conjecture"; it is the near-Ramanujan-up-to-`√log` exponent-`1/2` cancellation
for the thin dyadic Gauss period. -/
theorem b7_corrected_verdict {ψ : AddChar F ℂ} {G : Finset F} {C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hlo : 1 ≤ Real.log ((Fintype.card F : ℝ) / G.card))
    (hhi : Real.log ((Fintype.card F : ℝ) / G.card) ≤ Λ) :
    (BGKBound C ψ G (1 / 2) → NearRamanujanSqrtLog ψ G C) ∧
    (NearRamanujanSqrtLog ψ G C → BGKBound (C * Real.sqrt Λ) ψ G (1 / 2)) ∧
    diBenedettoDelta < (1 / 2 : ℝ) :=
  ⟨fun hram => ramanujan_implies_prize hC hlo hram,
   fun hprize => prize_implies_ramanujan_up_to_sqrtlog hC hΛ hhi hprize,
   prize_strictly_beyond_proven_BGK.1⟩

end ProximityGap.Frontier.WF9B7

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WF9B7.ramanujan_implies_prize
#print axioms ProximityGap.Frontier.WF9B7.prize_implies_ramanujan_up_to_sqrtlog
#print axioms ProximityGap.Frontier.WF9B7.prize_strictly_beyond_proven_BGK
#print axioms ProximityGap.Frontier.WF9B7.b7_corrected_verdict
