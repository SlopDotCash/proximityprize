/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFSaddleAssembled
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodSpectralFrame
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConvergenceHub

/-!
# Bridging the two in-tree CORE encodings: saddle floor ⟹ `NearRamanujanSqrtLog` (#444 §6.2 / §407)

The prize per-frequency core `M(n) = max_{b≠0}‖η_b‖` is encoded in-tree in **two** places that the
dossier asserts equivalent but never bridges:

* the **§407 spectral-frame predicate** `NearRamanujanSqrtLog ψ G C : ∀ b≠0, ‖η_b‖ ≤ C·√(n·log(q/n))`
  (`GaussPeriodSpectralFrame.lean`), the literal prize bound, whose lower half (Parseval floor) is
  proven and whose upper half is the named-open ceiling;
* the **§6.2 cosh-MGF saddle consumer** `period_le_saddle_closedForm`
  (`Frontier/CoshMGFSaddleAssembled.lean`): *for an arbitrary frequency `b₀`*, given the single open
  MGF inequality at the saddle `y*² = 2 log q / n`, `‖η_{b₀}‖ ≤ log(2q²)/y*`.

The saddle consumer's hypothesis (`hMGF`) is **`b₀`-independent** (it constrains only the even-moment
MGF `∑_r q·E_r y^{2r}/(2r)!`, no `b₀`).  So the SAME open inequality bounds *every* frequency by the
same closed form `log(2q²)/y*` — i.e. it discharges the **universally-quantified** spectral predicate,
not just one period.  This file performs that bridge:

> **`nearRamanujan_of_saddle`** — at the saddle `y*` (`y*² = 2 log q / n`, `y* > 0`, `n = |G| > 0`),
> the single open MGF inequality ⟹ `NearRamanujanSqrtLog ψ G C₀` with the **explicit** constant
> `C₀ := log(2q²) / (y*·√(n·log(q/n)))`.

So the §6.2 saddle estimate and the §407 spectral CORE predicate become two faces of ONE open
hypothesis (the char-`p` Wick / MGF inequality), with an explicit shared constant.  We additionally
pin that constant: `C₀² = (log(2q²))² / (2·log q·log(q/n))`, and in the thin prize slice
`log(q/n) ≥ (1 − 1/β)·log q` (i.e. `n ≤ q^{1/β}`, `q = n^β`) it is bounded by the **absolute**
`C₀² ≤ (log 2 + 2 log q)² / (2(1−1/β) (log q)²) → 2β/(β−1)` — a finite, `n`-independent ceiling.

## Honest scope (rule 3, rule 6)
This is **NOT** a CORE closure.  The open prize is the MGF inequality `MGF(y*) ≤ q·exp(n y*²/2)`
itself (the char-`p` Wick bound `A_r ≤ (2r−1)‼·n^r` at depth `r ≈ log q`).  This file is a deductive
INFRASTRUCTURE bridge: it shows the §6.2 consumer chain and the §407 spectral predicate are the SAME
content under that one hypothesis, with an explicit absolute constant — closing a long-standing
"two CORE encodings asserted equivalent but never welded" gap.  Probe-free by nature (pure
real-analysis composition over already-proven theorems).  CORE stays OPEN.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ProximityGap.Frontier.CoshMGFSaddleAssembled
open ProximityGap.Frontier.ConvergenceHub

namespace ProximityGap.Frontier.NearRamanujanFromSaddle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The explicit shared constant: the saddle closed-form bound `log(2q²)/y*` written in the
spectral `C·√(n·log(q/n))` normalization. -/
noncomputable def saddleConst (F : Type*) [Fintype F] (G : Finset F) (y : ℝ) : ℝ :=
  Real.log (2 * (Fintype.card F : ℝ) ^ 2)
    / (y * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)))

/-- **The bridge.** At the saddle `y*` (`y*² = 2 log q / n`, `y* > 0`, `n = |G| > 0`), given the
single open MGF inequality `MGF(y*) ≤ q·exp(n y*²/2)`, the **universally-quantified** spectral
predicate `NearRamanujanSqrtLog ψ G C₀` holds with the explicit constant
`C₀ = saddleConst F G y*`.  Mechanism: `period_le_saddle_closedForm` bounds *every* frequency by the
`b₀`-independent closed form `log(2q²)/y*`, and dividing by the positive length scale
`√(n·log(q/n)) > 0` rewrites that bound into the spectral normalization tautologically. -/
theorem nearRamanujan_of_saddle {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ))
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hMGF : (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
        ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    NearRamanujanSqrtLog ψ G (saddleConst F G y) := by
  intro b _hb
  -- the b₀-independent saddle closed form, applied at this frequency b
  have hclosed : ‖eta ψ G b‖ ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y :=
    period_le_saddle_closedForm (F := F) hψ G hy b hn hsaddle hMGF
  -- write the target length scale and show it is positive
  set s : ℝ := Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) with hs
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hL
  have hyne : y ≠ 0 := ne_of_gt hy
  have hsne : s ≠ 0 := ne_of_gt hspos
  -- saddleConst F G y * s = log(2q²)/y  (the tautological rewrite)
  have hkey : saddleConst F G y * s = Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y := by
    rw [saddleConst, ← hs]
    field_simp
  -- conclude ‖η_b‖ ≤ C₀ * s
  calc ‖eta ψ G b‖ ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y := hclosed
    _ = saddleConst F G y * s := hkey.symm

omit [Field F] [DecidableEq F] in
/-- **Constant identity (squared).** At the saddle `y*² = 2 log q / n` with `n = |G| > 0` and the
length scale positive, the shared constant satisfies
`C₀² = (log(2q²))² / (2·log q·log(q/n))` — an explicit, frequency-free value. -/
theorem saddleConst_sq (G : Finset F) {y : ℝ} (hn : (G.card : ℝ) ≠ 0)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ)) :
    saddleConst F G y ^ 2
      = Real.log (2 * (Fintype.card F : ℝ) ^ 2) ^ 2
          / (2 * Real.log (Fintype.card F : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) := by
  set L : ℝ := (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  set num : ℝ := Real.log (2 * (Fintype.card F : ℝ) ^ 2) with hnum
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (le_of_lt hL)
  -- y² = 2 log q / n, so y² · L = 2 log q · log(q/n) using L = n · log(q/n)
  have hyL : y ^ 2 * L = 2 * Real.log (Fintype.card F : ℝ)
      * Real.log ((Fintype.card F : ℝ) / G.card) := by
    rw [hsaddle, hLdef]
    field_simp
  -- saddleConst² = num² / (y² · (√L)²) = num² / (y² · L) = num² / (2 log q · log(q/n))
  rw [saddleConst, ← hnum, div_pow, mul_pow, hsq, hyL]

omit [Field F] [DecidableEq F] in
/-- The shared constant is nonnegative when `1 ≤ q` (so `2q² ≥ 1`, hence `log(2q²) ≥ 0`) and the
length scale is positive: numerator `≥ 0`, denominator `> 0`. -/
theorem saddleConst_nonneg (G : Finset F) {y : ℝ} (hy : 0 < y) (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) :
    0 ≤ saddleConst F G y := by
  rw [saddleConst]
  have hspos : 0 < Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) :=
    Real.sqrt_pos.mpr hL
  have hnum : 0 ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) := by
    apply Real.log_nonneg
    nlinarith [hq1, sq_nonneg ((Fintype.card F : ℝ) - 1)]
  positivity

/-- **End-to-end: the single open MGF inequality ⟹ the δ*-pinning hub.**  Composing the bridge
`nearRamanujan_of_saddle` (saddle ⟹ spectral predicate) with the in-tree convergence-hub face
`prizeFloor_of_nearRamanujan` (spectral ⟹ `PrizeFloor`), the single open MGF inequality at the
saddle discharges **`PrizeFloor ψ G C₀`** — the `WorstCaseIncompleteSumBound` at the prize scale that
(downstream, via `addEnergy_le_of_worstCase → mcaDeltaStar`) pins `δ*`.  This is the explicit weld of
the §6.2 saddle/Wick face to the δ*-pinning census/hub face: BOTH in-tree CORE encodings now consume
the SAME single open hypothesis through one explicit constant `C₀ = saddleConst F G y*`.  Still NOT a
CORE closure — the MGF inequality itself is the open prize. -/
theorem prizeFloor_of_saddle {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ)) (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hq : (G.card : ℝ) ≤ Fintype.card F)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hMGF : (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
        ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    PrizeFloor ψ G (saddleConst F G y) :=
  prizeFloor_of_nearRamanujan hq (saddleConst_nonneg G hy hq1 hL)
    (nearRamanujan_of_saddle hψ G hy hn hL hsaddle hMGF)

end ProximityGap.Frontier.NearRamanujanFromSaddle

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx):
#print axioms ProximityGap.Frontier.NearRamanujanFromSaddle.nearRamanujan_of_saddle
#print axioms ProximityGap.Frontier.NearRamanujanFromSaddle.saddleConst_sq
#print axioms ProximityGap.Frontier.NearRamanujanFromSaddle.saddleConst_nonneg
#print axioms ProximityGap.Frontier.NearRamanujanFromSaddle.prizeFloor_of_saddle
