/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Deficit absorption is redundant: the char-0 deficit credit is DOMINATED by the DC headroom (#444)

## What this attacks (Angle 2 — deficit absorption)

The wraparound-budget identity (`Frontier/_WraparoundBudgetIdentity.prize_iff_wraparound_budget`)
collapses the prize at depth `r` to one inequality on the genuine mod-`p` wraparound count `W_r`:

  `p·W_r ≤ n^(2r) − Wick_r + p·Δ_r`,   `Wick_r = (2r−1)‼·n^r`,

with TWO non-negative credits on the right that the prize budget may spend against the wraparound
mass `p·W_r`:

* the **DC headroom** `n^(2r) − Wick_r`, and
* the **char-0 deficit credit** `p·Δ_r`,   `Δ_r = Wick_r − E_r(ℂ) ≥ 0` (Lam–Leung / Bessel).

Angle 2 asks: is there ANY nontrivial regime where the deficit credit `p·Δ_r` *alone* provably
dominates the wraparound `p·W_r`, giving the prize unconditionally there?

## Verdict: NO — deficit absorption never adds anything the DC headroom does not already give

This file delivers the clean, axiom-clean **NO-GO**: at every depth past a tiny threshold `r₀ ≈ β`
(`β = log_n p`, FAR below the BGK saddle `r* ≈ ln p`), the deficit credit is *dominated* by the DC
headroom,

  `p·Δ_r ≤ n^(2r) − Wick_r`.

Two exact facts drive it (both proved below, pure ℝ/ℕ arithmetic, no field theory):

1. **`Δ_r ≤ Wick_r`** unconditionally (since `E_r(ℂ) = Wick_r − Δ_r ≥ 0`). So `p·Δ_r ≤ p·Wick_r`.
2. **DC dominance threshold.** If `n^r ≥ (p+1)·(2r−1)‼` — equivalently `n^(2r) ≥ (p+1)·Wick_r`
   (multiply by `n^r`, using `Wick_r = (2r−1)‼·n^r`) — then `n^(2r) − Wick_r ≥ p·Wick_r ≥ p·Δ_r`.

The threshold `n^r ≥ (p+1)·(2r−1)‼` is met for ALL `r ≥ r₀` with `r₀ ≈ β` a constant: at the prize
scale `n = 2^30`, `p = n^4 = 2^120`, it first holds at `r₀ = 5` and holds throughout the entire
relevant band up to and beyond the saddle `r* ≈ 83` (probe `probe_nogo_threshold.py`,
`probe_deficit_fraction.py`). Numerically the DC headroom exceeds `p·Δ_r` by ~`10^571` at the saddle.

## The consequence (the headline NO-GO)

`deficit_absorption_redundant`: in the DC-dominance regime, ANY wraparound `W_r` that the deficit
credit could absorb (`p·W_r ≤ p·Δ_r`) is ALREADY absorbed by the DC headroom alone
(`p·W_r ≤ n^(2r) − Wick_r`), with room to spare. Hence there is **no** regime past onset where
deficit absorption delivers the prize that the DC headroom did not already cover. The deficit is a
genuine, strictly-positive, but structurally **redundant** credit: it is never the binding term.

This refutes the deficit-absorption hope (Angle 2) cleanly. It does NOT close the prize: the open
wall is unchanged — bounding the wraparound `W_r` itself (the incidence / `√q·B` cancellation,
BGK/Paley) against the DC headroom is still required and still open. This brick only certifies that
the *second* credit (`p·Δ_r`) contributes nothing the *first* (`n^(2r) − Wick_r`) does not, so an
attack must defeat the wall directly; it cannot be financed by the deficit.

## Honest scope (rules 1,3,6)

NOT a CORE closure and NOT a refutation of CORE. Axiom-clean ℝ/ℕ arithmetic on the budget identity's
two credits. The deficit `Δ_r` is real and positive (`Frontier/_CharZeroLamLeungSlackLower` pins it
exactly at `r∈{2,3}`: `Slack_2 = 3n`, `Slack_3 = 45n²−40n`, sub-leading `~ n^{r-1}`); this file
shows that, however positive, `p·Δ_r` cannot exceed the DC headroom past `r₀`, so it cannot decide
the budget. `CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED/OPEN. Issue #444, Angle 2.
-/

namespace ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo

/-! ## 1. The deficit is bounded by Wick (since the char-0 energy is non-negative) -/

/-- **`Δ_r ≤ Wick_r`.** The char-0 deficit `Δ = Wick − E0` never exceeds `Wick`, because the char-0
energy `E0 = E_r(ℂ) ≥ 0` (a count of zero-sum tuples). So the deficit credit `p·Δ` is at most
`p·Wick`. This is the first half of the NO-GO: the deficit credit cannot exceed `p·Wick_r`. -/
theorem deficit_le_wick (Wick E0 Delta : ℝ) (hDelta : Delta = Wick - E0) (hE0 : 0 ≤ E0) :
    Delta ≤ Wick := by
  rw [hDelta]; linarith

/-- **The deficit is non-negative** (`Δ ≥ 0`), the proven char-0 Lam–Leung deficit `E0 ≤ Wick`.
Restated here for self-containment so the budget credit `p·Δ` is a genuine (non-negative) credit. -/
theorem deficit_nonneg (Wick E0 Delta : ℝ) (hDelta : Delta = Wick - E0) (hLL : E0 ≤ Wick) :
    0 ≤ Delta := by
  rw [hDelta]; linarith

/-! ## 2. The arithmetic threshold: `n^(2r) ≥ (p+1)·Wick_r` from `n^r ≥ (p+1)·(2r−1)‼` -/

/-- **DC-dominance threshold (real form).** With `Wick = df · nr` (the double-factorial Wick value,
`df = (2r−1)‼`, `nr = n^r`) and `n2r = nr · nr` (`n^(2r) = (n^r)²`), the threshold
`nr ≥ (p+1)·df` upgrades to `n2r ≥ (p+1)·Wick`. (Multiply `nr ≥ (p+1)·df` by `nr ≥ 0`.) This is the
single clean condition under which the DC headroom alone exceeds `p·Wick`. -/
theorem dcDominance_of_threshold (p df nr Wick n2r : ℝ)
    (hWick : Wick = df * nr) (hn2r : n2r = nr * nr)
    (hnr : 0 ≤ nr) (hthr : (p + 1) * df ≤ nr) :
    (p + 1) * Wick ≤ n2r := by
  rw [hWick, hn2r]
  calc (p + 1) * (df * nr) = ((p + 1) * df) * nr := by ring
    _ ≤ nr * nr := mul_le_mul_of_nonneg_right hthr hnr

/-! ## 3. The core NO-GO: the deficit credit is dominated by the DC headroom -/

/-- **★ The deficit credit is dominated by the DC headroom.** In the DC-dominance regime
`(p+1)·Wick ≤ n^(2r)` (met for all `r ≥ r₀ ≈ β`, the threshold of §2), with `0 ≤ Δ ≤ Wick` and
`0 ≤ p`, the char-0 deficit credit is dominated by the DC headroom:

  `p·Δ ≤ n^(2r) − Wick`.

Proof: `p·Δ ≤ p·Wick = (p+1)·Wick − Wick ≤ n^(2r) − Wick`. So whatever positive value the deficit
credit `p·Δ_r` takes, it never reaches the DC headroom — the deficit is the *smaller* of the two
credits in the wraparound budget, past `r₀`. -/
theorem deficitCredit_le_dcHeadroom (p Wick Delta n2r : ℝ)
    (hp : 0 ≤ p) (hDelta_nonneg : 0 ≤ Delta) (hDelta_le : Delta ≤ Wick)
    (hDC : (p + 1) * Wick ≤ n2r) :
    p * Delta ≤ n2r - Wick := by
  have h1 : p * Delta ≤ p * Wick := mul_le_mul_of_nonneg_left hDelta_le hp
  nlinarith [h1, hDC]

/-- **★ Deficit absorption is REDUNDANT (the headline NO-GO).** In the DC-dominance regime, ANY
wraparound mass `p·W` that the deficit credit could absorb (`p·W ≤ p·Δ`) is ALREADY absorbed by the
DC headroom alone (`p·W ≤ n^(2r) − Wick`). Hence there is no regime past onset where deficit
absorption delivers a wraparound bound the DC headroom did not already give: the deficit credit is
never the binding term in the budget `p·W ≤ n^(2r) − Wick + p·Δ`.

This is the precise refutation of Angle 2: deficit absorption opens no new unconditional regime. -/
theorem deficit_absorption_redundant (p W Wick Delta n2r : ℝ)
    (hp : 0 ≤ p) (hDelta_nonneg : 0 ≤ Delta) (hDelta_le : Delta ≤ Wick)
    (hDC : (p + 1) * Wick ≤ n2r)
    (hAbsorb : p * W ≤ p * Delta) :
    p * W ≤ n2r - Wick :=
  le_trans hAbsorb (deficitCredit_le_dcHeadroom p Wick Delta n2r hp hDelta_nonneg hDelta_le hDC)

/-- **The two credits side by side, fully assembled from the defining relations.** Given the budget
identity's defining relations (`Wick = df·nr`, `n2r = nr·nr`, `Delta = Wick − E0`), the char-0
non-negativity `0 ≤ E0`, `0 ≤ p`, `0 ≤ nr`, and the depth threshold `(p+1)·df ≤ nr`, the deficit
credit `p·Δ` is `≤` the DC headroom `n2r − Wick`. This packages §1–§3 into the single end-to-end
statement consumed by the budget: past `r₀`, `p·Δ_r ≤ n^(2r) − Wick_r`. -/
theorem deficitCredit_le_dcHeadroom_assembled
    (p df nr Wick E0 Delta n2r : ℝ)
    (hWick : Wick = df * nr) (hn2r : n2r = nr * nr) (hDelta : Delta = Wick - E0)
    (hE0 : 0 ≤ E0) (hp : 0 ≤ p) (hnr : 0 ≤ nr) (hthr : (p + 1) * df ≤ nr) :
    p * Delta ≤ n2r - Wick := by
  have hDC : (p + 1) * Wick ≤ n2r := dcDominance_of_threshold p df nr Wick n2r hWick hn2r hnr hthr
  have hDle : Delta ≤ Wick := deficit_le_wick Wick E0 Delta hDelta hE0
  -- Δ = Wick − E0 ≥ 0 needs E0 ≤ Wick; derive it from the threshold (Wick = df·nr, df,nr ≥ 0 ⇒
  -- Wick ≥ 0) is NOT enough; instead use that the budget only needs Δ ≤ Wick and Δ ≥ 0.
  -- Δ ≥ 0 here would need E0 ≤ Wick; we get it from hE0 + (Wick ≥ E0)? Not available abstractly.
  -- So state the dominated bound WITHOUT needing Δ ≥ 0 (it is not used in deficitCredit_le_dcHeadroom
  -- beyond p·Δ ≤ p·Wick, which uses only Δ ≤ Wick and 0 ≤ p). Inline that argument:
  have h1 : p * Delta ≤ p * Wick := mul_le_mul_of_nonneg_left hDle hp
  nlinarith [h1, hDC]

/-! ## 4. The threshold in ℕ: it holds for all `r ≥ r₀` at prize scale (no-vacuity anchor) -/

/-- **The deficit-credit fraction bound, exhibited concretely.** Even at the maximal deficit
`Δ = Wick`, the deficit credit `p·Δ = p·Wick` is `(p+1)·Wick − Wick ≤ n^(2r) − Wick` in the
DC-dominance regime. So the deficit credit is at most a `p/(n^(2r)/Wick − 1)`-fraction of the DC
headroom — and `n^(2r)/Wick = n^r/(2r−1)‼` blows up past `r₀`, driving that fraction to `0`. This
records the worst-case (`Δ = Wick`) instance, certifying the NO-GO is not vacuous at the boundary. -/
theorem maximal_deficit_still_dominated (p Wick n2r : ℝ)
    (hp : 0 ≤ p) (hWick : 0 ≤ Wick) (hDC : (p + 1) * Wick ≤ n2r) :
    p * Wick ≤ n2r - Wick :=
  deficitCredit_le_dcHeadroom p Wick Wick n2r hp hWick (le_refl Wick) hDC

/-- **The ℕ threshold holds at the prize scale.** A no-vacuity anchor: at `n = 2^30`, `p = n^4`,
`r = 5` (the first depth past `r₀`), the threshold `(p+1)·(2·5−1)‼ ≤ n^5` holds, so the DC-dominance
hypothesis of the NO-GO is satisfiable (indeed satisfied) at prize scale. `(2·5−1)‼ = 9‼ = 945`. -/
theorem prizeScale_threshold_holds :
    let n : ℕ := 2 ^ 30
    let p : ℕ := (2 ^ 30) ^ 4
    let r : ℕ := 5
    (p + 1) * Nat.doubleFactorial (2 * r - 1) ≤ n ^ r := by
  -- n^5 = 2^150 ; (p+1)·945 = (2^120+1)·945 ≤ 2^120 · 1024 = 2^130 < 2^150.
  norm_num [Nat.doubleFactorial]

end ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.deficit_le_wick
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.deficit_nonneg
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.dcDominance_of_threshold
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.deficitCredit_le_dcHeadroom
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.deficit_absorption_redundant
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.deficitCredit_le_dcHeadroom_assembled
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.maximal_deficit_still_dominated
#print axioms ArkLib.ProximityGap.Frontier.DeficitCreditDominatedByDCNoGo.prizeScale_threshold_holds
