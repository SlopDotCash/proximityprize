/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._BGKSOTAInsufficiency
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodSpectralFrame

/-!
# wf-B7 (#444): the EXACT prize ⇆ BGK reduction directions — corrected naming

## What this lane settles

Lane B7 ("settle prize ⇔ BGK rigorously") asks for the precise logical relationship between

* the **prize floor**   `M(n) = max_{b≠0}‖η_b‖ ≤ C·√(n·log(q/n))`   (`NearRamanujanSqrtLog ψ G C`,
  cancellation exponent `δ = 1/2 − o(1)`, with a *bounded* `√log(q/n)` slack), and
* the **BGK-type Gauss-period bounds** `‖η_b‖ ≤ C·n^{1−δ}` (`BGKBound C ψ G δ`).

A prior pass (`_wf8B7_W3_BGK_Equivalence`) proved a clean real-analysis equivalence between
`NearRamanujanSqrtLog` and `BGKBound _ _ _ (1/2)`, and *named the equivalent object the
"Paley-Graph Conjecture"*. **That naming is incorrect**, and the error matters for "what exactly is
open". This file fixes it with the literature-correct dictionary and the exact reduction directions.

## The correction (dictionary; audited 2026-10-28)

The named conjectures are NOT the same statement:

* **Paley Graph Conjecture (PGC)** — a statement about *bilinear* character sums: for every
  `ε > 0` there is `δ = δ(ε) > 0` with `|∑_{a∈A, b∈B} χ(a+b)| ≤ p^{−δ}·|A||B|` for ARBITRARY sets
  `A, B ⊆ F_p` with `|A|, |B| > p^ε` (multiplicative character `χ`). It is **OPEN**. It is NOT the
  Gauss-period bound `‖η_b‖ ≤ n^{1−δ}`, and nothing in this file is about the PGC.
* **Bourgain–Glibichuk–Konyagin (BGK 2006) — PROVEN**: for a multiplicative subgroup `H` with
  `|H| ≥ p^γ` there is `δ(γ) > 0` with `‖η_b‖ ≤ n^{1−δ}` (additive-character sums over `H`;
  `δ ≈ 0.011` after di Benedetto). This is the power-saving Gauss-period bound
  (`BGKBound 1 ψ G δ` for some `δ > 0`); it is known, and is *not the open content of the prize*.
* **Ramanujan / square-root cancellation** — `‖η_b‖ ≤ C·√n` (exponent `δ = 1/2`,
  `= BGKBound C ψ G (1/2)`). As a *bound*, it implies every `n^{1−δ}` bound with `δ ≤ 1/2` for
  large `n`. For `Cay(F_q, μ_n)` this is the open *Ramanujan/BGK-sharp* question.
* **The prize floor** — `‖η_b‖ ≤ C·√(n·log(q/n))`. As a bound this is weaker than Ramanujan `√n`
  by the factor `√log(q/n)` (at prize scale `q/n = 2^128`, `√log = √(128 ln 2) ≈ 9.4`; for
  `q ≈ n^β`, `√((β−1) ln n) ≈ 8–9`).

So, comparing the *bound values* (exponents) only,

      proven BGK (δ≈0.011)  <  prize floor (δ=1/2−o(1))  ≤  Ramanujan (δ=1/2).

This is an ordering of the guaranteed bounds, NOT a proven strict hierarchy of the statements:
no non-implication between the statements is proven here (e.g. nothing here rules out that some
argument derives the prize floor from the BGK statement plus other input, or that the prize floor
implies Ramanujan at the same constant for the specific family `μ_n`).

The prize is the exponent-`1/2`/near-Ramanujan bound *up to a `√log` slack*, i.e. close to the open
**BGK-sharp / Ramanujan-for-`Cay(F_q,μ_n)`** problem, which is what the in-tree
`GaussPeriodSpectralFrame` comment records ("the needed bound carries a `√log` factor").

## The PROVEN content (exact, axiom-clean)

* `ramanujan_implies_prize` (**Ramanujan ⟹ prize**): `BGKBound C ψ G (1/2)` (`‖η_b‖ ≤ C√n`) implies
  the prize floor `NearRamanujanSqrtLog ψ G C`, because `√n ≤ √(n·L)` whenever the index logarithm
  `L = log(q/n) ≥ 1`. So a Ramanujan bound is sufficient for the prize at the same constant.

* `prize_implies_ramanujan_up_to_sqrtlog` (**prize ⟹ Ramanujan with a `√Λ`-inflated constant**):
  the prize floor implies `BGKBound (C·√Λ) ψ G (1/2)` when `L ≤ Λ`. This is an upper-bound
  implication only; it is NOT proven here that the prize *fails* to imply the clean bound at
  constant `C` (no non-implication is formalized).

* `prize_strictly_beyond_proven_BGK`: `diBenedettoDelta = 0.011 < 1/2`, and for every `C, C', L`
  the BGK *bound value* `C·n^{1−0.011}` eventually exceeds the prize target `C'·√(n·L)`. So the
  known BGK *bound* is too weak to give the prize directly. This compares bound values; it does not
  prove that the prize statement is logically independent of / strictly stronger than BGK.

## Verdict (B7, corrected; informal reading of the proven bound comparisons)

* **Direction (i).** The prize asks for cancellation exponent `1/2 − o(1)`, beyond the proven
  `0.011`; so proving it via a Gauss-period bound means improving the BGK exponent for thin `μ_n`
  (a recognized open problem). This is a heuristic difficulty assessment, not a theorem.

* **Direction (ii).** The known BGK power-saving *bound* (`n^{1−δ}`, fixed `δ < 1/2`) does not by
  itself yield the prize floor for large `n` (`bgk_value_exceeds_prizeTarget_eventually` compares the
  bound values). The *Ramanujan bound* `√n` DOES suffice (`ramanujan_implies_prize`).

The open content is the near-Ramanujan-up-to-`√log` cancellation exponent `1/2` for the thin dyadic
Gauss period. The (open) Paley Graph Conjecture is a different, bilinear-sum statement and is not
what the prior pass's "PGC" label described.

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
after absorbing the bounded index slack `L ≤ Λ` into the constant, which is INFLATED by `√Λ`
(`≈ 9` at prize scale).  This is an upper-bound implication only: it is NOT proven here that the
prize fails to deliver the clean Ramanujan bound at constant `C`. -/
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

/-! ## Direction C — the proven BGK *bound value* is eventually above the prize target -/

/-- **The proven BGK bound value is too weak for the prize target.**

For `diBenedettoDelta = 0.011` (the BGK power-saving SOTA for Gauss periods over subgroups), the
*guaranteed* value `C·n^{1−δ}` strictly exceeds the prize target `C'·√(n·L)` for all large `n`.
So the known BGK *bound* does not by itself give the prize.  This compares bound values only: it
is NOT a proof that the BGK statement fails to imply the prize, nor that the prize is "at least as
hard" as improving the BGK exponent (that is an informal reading).  It says nothing about the
(open, bilinear) Paley Graph Conjecture.

The first conjunct records `0.011 < 1/2`; the eventual-domination is the in-tree
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

/-- **B7 corrected verdict (bundled implications).** Bundles:

1. (`ramanujan_implies_prize`) Ramanujan `√n` ⟹ prize at the same constant `C` (needs `L ≥ 1`).
2. (`prize_implies_ramanujan_up_to_sqrtlog`) prize ⟹ Ramanujan at the `√Λ`-inflated constant.
3. the numeric comparison `diBenedettoDelta = 0.011 < 1/2`.

Reading: up to a bounded `√log` constant the prize floor and the Ramanujan/BGK-sharp bound for
`Cay(F_q, μ_n)` imply each other.  No non-implication or strictness is proven here, and nothing
here concerns the (open, bilinear-sum) Paley Graph Conjecture. -/
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
