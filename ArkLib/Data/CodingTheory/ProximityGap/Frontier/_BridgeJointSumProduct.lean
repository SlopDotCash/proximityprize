/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The JOINT sum-product lever at EXACT prize thinness `n = p^{0.19}` (#444, U1)

`_BridgeOneWall` proved that the additive↔multiplicative bridge is **tautological**: the additive
energy `E_r` and the worst-case sup-norm `M` are the SAME object (Parseval-dual,
`Σ_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`, no info gain). The ONLY non-tautological way to combine the
two pictures is the **joint** additive-multiplicative structure — a sum-product / additive-energy-
of-a-multiplicative-subgroup bound. This file is the machine-checked **prize-regime census** of
EVERY such bound, computing the exact `H`-exponent each delivers at the EXACT prize thinness, and
recording the precise **threshold gap** between what each bound needs and what the prize is.

## The exact prize parameters (verbatim, #444)

The prize object is the thin dyadic subgroup `μ_n ⊆ F_p^×` at
* `n = |H| = 2^30`,
* `p ≈ n · 2^128 = 2^158`,

so the thinness exponent is

> `α := log_p n = 30/158 = 15/79 ≈ 0.18987`,    `β := log_n p = 79/15 ≈ 5.2667`.

The prize is `α < 1/4`. We encode `α` and `β` exactly as rationals.

## The encoding (exact rational `H`-exponents)

Every sum-product subgroup bound has the shape `max_{a≠0}|S_a(H)| ≤ H^{1−s} · p^{c}` for a saving
`s` and a `p`-tax `c` (the Burgess/trilinear prefactor). As a pure power of `H = n` with `p = H^β`
this is `H^{(1−s) + c·β}`. The bound:

* **reaches the prize** iff its `H`-exponent is `≤ 1/2` (the Paley exponent, `M ≤ C√(n log m)`);
* is **trivial** (vanishes) iff its `H`-exponent is `≥ 1` (no improvement on the trivial `|S_a| ≤ |H|`).

Crucially, every bound is also gated by a **cardinality threshold** `H > p^{αThr}`: it is only
nontrivial when `α > αThr`. The census reads off, for each bound, both (a) its `H`-exponent at the
prize `β = 79/15`, and (b) its threshold gap `αThr − α` (positive ⟹ the bound's hypothesis FAILS
at the prize ⟹ it gives nothing better than trivial).

## The census verdict (PROVEN, exact arithmetic)

| bound (named, NOT proved)                       | `αThr` | prize deficit `αThr − α` | status at prize |
|-------------------------------------------------|:------:|:------------------------:|-----------------|
| BGK (Bourgain–Glibichuk–Konyagin)               |  `0`   |        `−15/79`          | nontrivial, but `n^{1−o(1)}`, NO power saving |
| di Benedetto–Garaev–Shparlinski Thm 3.1         | `1/4`  |         `19/316`         | OUT OF RANGE → `H`-exp `8699/8640 > 1` (trivial) |
| Petridis–Shparlinski trilinear (the engine)     | `1/4`  |         `19/316`         | `p^{1/4}` prefactor `= H` at edge → vanishes below |
| Heath-Brown–Konyagin (HBK)                       | `1/3`  |         `34/237`         | vacuous below `p^{1/3}` |
| Konyagin–Shkredov (energy-input variant)        | `1/4`  |         `19/316`         | same Burgess edge as di Benedetto |
| Bourgain–Garaev (sum-product subgroup)          | `1/4`  |         `19/316`         | same edge |
| Shkredov higher-energy `T_k` (feeds trilinear)  | `1/4`  |         `19/316`         | improves saving, NOT the edge |
| Murphy–Rudnev (point–line incidence energy)     | `1/4`  |         `19/316`         | energy input, same edge |
| Macourt / Kerr (2018–2020 refinements)          | `1/4`  |         `19/316`         | same Burgess barrier |
| classical Weil / Gauss `√p`                      | `1/2`  |         `49/158`         | vacuous for thin `μ_n` (`√p ≫ n`) |

**Every power-saving bound has `αThr ≥ 1/4 > α = 15/79`, so at the prize EVERY ONE is either
trivial (out of range) or non-power-saving (BGK).** The joint lever VANISHES at `p^{0.19}`. The sole
nontrivial survivor (BGK) carries no power saving, so it gives `n^{1−o(1)}`, not `√n`.

## The threshold gap, made precise

The closest power-saving bound (the di Benedetto / Petridis–Shparlinski edge) needs the subgroup to
be `p^{1/4}`; the prize is `p^{15/79}`. The gap is

> `1/4 − 15/79 = 19/316 ≈ 0.0601`.

I.e. the prize subgroup would have to be a factor `p^{19/316} = 2^{158·19/316} = 2^{9.5} ≈ 724`
times **larger** in cardinality just to ENTER the di Benedetto window — and even at that window the
edge exponent is only `1 − 31/2880 ≈ 0.989`, still a full constant above `1/2`. The prize lives a
power below the Burgess barrier, where the trilinear `p^{1/4}` prefactor (`= H` at `α = 1/4`)
inflates to `p^{1/4} = H^{β/4} = H^{79/60} ≫ H` — the bound is worse than trivial.

## The named residual (the sum-product exponent that WOULD close it)

`sumProductReachesPrize`: a saving `s` and tax `c` such that `(1−s) + c·β ≤ 1/2` at `β = 79/15` and
the bound holds for `α = 15/79`. We record the EXACT requirement
(`saving_needed_at_prize`): to reach the prize one needs `s − c·β ≥ 1/2`, i.e. a Paley-strength
power saving `s ≥ 1/2 + c·β` that survives BELOW `p^{1/4}` with a `c` small enough that `c·β` does
not eat it. No published bound has this; the existence of one is the open Paley-graph-strength input
named here.

**Honesty.** Every literature bound is NAMED, not proved. The PROVEN content is the exact rational
exponent/threshold arithmetic. The verdict is unambiguous and matches the campaign default: **the
joint sum-product lever VANISHES at the prize thinness `α = 15/79 < 1/4`.** No false closure; this
brick QUANTIFIES the SOTA frontier gap. Issue #444.

## References
* Bourgain, Glibichuk, Konyagin. *Estimates for the number of sums and products and for exponential
  sums in fields of prime order*. J. London Math. Soc. 73 (2006). (BGK, `n^{1−o(1)}`.)
* di Benedetto, Garaev, Shparlinski. *New estimates for exponential sums over multiplicative
  subgroups and intervals*. arXiv:2401.04756 / arXiv:2003.06165. (Thm 3.1, `H^{1−31/2880}`.)
* Petridis, Shparlinski. *Bounds of trilinear and quadrilinear exponential sums*. J. d'Anal. Math.
  138 (2019). (Trilinear `p^{1/4}` prefactor — the Burgess barrier.)
* Heath-Brown, Konyagin. *New bounds for Gauss sums derived from kth powers*. Q. J. Math. 51 (2000).
* Murphy, Rudnev, Shkredov, Shteinikov. *On the few products, many sums problem*. arXiv:1712.00410.
* Konyagin, Shkredov. *On sum sets of sets having small product set*. (energy `T_3`.)
* Macourt. *Incidence results and bounds of trilinear and quadrilinear exponential sums*. (2018.)
* Kerr. *Various estimates for exponential sums over multiplicative subgroups*. (2019–2020.)
-/

namespace ArkLib.ProximityGap.Frontier.BridgeJointSumProduct

/-! ### The exact prize parameters -/

/-- The prize **thinness exponent** `α = log_p n` at `n = 2^30`, `p = 2^158`: `α = 30/158 = 15/79`. -/
def prizeAlpha : ℚ := 15/79

/-- The prize **aspect ratio** `β = log_n p = 1/α = 79/15 ≈ 5.2667`. -/
def prizeBeta : ℚ := 79/15

/-- `α · β = 1` (the two encode the same point `n = p^α`, `p = n^β`). -/
theorem prizeAlpha_mul_prizeBeta : prizeAlpha * prizeBeta = 1 := by
  unfold prizeAlpha prizeBeta; norm_num

/-- The prize is **strictly below the Burgess edge** `1/4`: `α = 15/79 < 1/4`. -/
theorem prizeAlpha_lt_quarter : prizeAlpha < 1/4 := by
  unfold prizeAlpha; norm_num

/-- The prize aspect ratio is **strictly above** the di Benedetto upper bound `β = 4`:
    `β = 79/15 > 4`, so di Benedetto Thm 3.1 (`2 < β < 4`) is OUT OF RANGE. -/
theorem prizeBeta_gt_four : prizeBeta > 4 := by
  unfold prizeBeta; norm_num

/-! ### The generic sum-product `H`-exponent as a function of (saving, tax) -/

/-- The **`H`-exponent** of a sum-product bound `max|S_a| ≤ H^{1−s}·p^{c}` at `p = H^β`:
    `(1 − s) + c·β`. A bound reaches the prize iff this is `≤ 1/2`; it is trivial iff `≥ 1`. -/
def spExp (s c β : ℚ) : ℚ := (1 - s) + c * β

/-- The **prize target** `H`-exponent: `M(n) ≤ C·√(n·log m)` is `H^{1/2}` (the Paley exponent). -/
def prizeExp : ℚ := 1/2

/-! ### 1. di Benedetto / Petridis–Shparlinski (the SOTA engine) at the prize -/

/-- **di Benedetto–Garaev–Shparlinski Thm 3.1 at the EXACT prize aspect ratio.** The bound is
    `H^{2689/2880}·p^{1/72}`, i.e. saving `s = 191/2880` and tax `c = 1/72`. At `β = 79/15` its
    `H`-exponent is `8699/8640 ≈ 1.0068 > 1` — **WORSE THAN TRIVIAL**. The bound vanishes at the
    prize: it gives nothing. (At its own valid edge `β = 4` it is `1 − 31/2880 ≈ 0.989`; below the
    edge the `p^{1/72}` tax overwhelms the saving.) -/
theorem diBenedetto_exp_at_prize :
    spExp (191/2880) (1/72) prizeBeta = 8699/8640 := by
  unfold spExp prizeBeta; norm_num

/-- The di Benedetto bound at the prize is **trivial** (`H`-exponent `> 1`). -/
theorem diBenedetto_at_prize_trivial :
    spExp (191/2880) (1/72) prizeBeta > 1 := by
  unfold spExp prizeBeta; norm_num

/-- ...and a fortiori **does NOT reach the prize** (`> 1/2`). -/
theorem diBenedetto_at_prize_gt_half :
    spExp (191/2880) (1/72) prizeBeta > prizeExp := by
  unfold spExp prizeBeta prizeExp; norm_num

/-! ### 2. The cardinality threshold gap (the structural obstruction) -/

/-- The **cardinality threshold** `αThr` for the di Benedetto / Petridis–Shparlinski / Konyagin–
    Shkredov / Murphy–Rudnev / Macourt / Kerr family: the trilinear engine carries a `p^{1/4}`
    prefactor that equals `H` exactly at `α = 1/4`, so the bound is nontrivial only for `α > 1/4`. -/
def burgessThreshold : ℚ := 1/4

/-- **The prize threshold gap (the headline obstruction).** The prize thinness `α = 15/79` is below
    the Burgess edge `1/4` by exactly `19/316 ≈ 0.0601`. The prize subgroup is a power TOO THIN to
    enter ANY power-saving sum-product window. -/
theorem prize_threshold_gap :
    burgessThreshold - prizeAlpha = 19/316 := by
  unfold burgessThreshold prizeAlpha; norm_num

/-- The gap is strictly positive: the prize FAILS the Burgess hypothesis. -/
theorem prize_below_burgess : prizeAlpha < burgessThreshold := by
  unfold prizeAlpha burgessThreshold; norm_num

/-- **The HBK threshold gap.** Heath-Brown–Konyagin is vacuous below `p^{1/3}`; the prize deficit is
    `1/3 − 15/79 = 34/237 ≈ 0.143`, even larger. -/
theorem hbk_threshold_gap : (1/3 : ℚ) - prizeAlpha = 34/237 := by
  unfold prizeAlpha; norm_num

/-- **The classical Weil/Gauss threshold gap.** `√p` is vacuous unless `H > √p` (`α > 1/2`); the
    prize deficit is `1/2 − 15/79 = 49/158 ≈ 0.310`. (`√p ≫ n` for thin `μ_n` — the √p-vacuity face
    of the pincer.) -/
theorem weil_threshold_gap : (1/2 : ℚ) - prizeAlpha = 49/158 := by
  unfold prizeAlpha; norm_num

/-! ### 3. BGK is the only nontrivial survivor — but has NO power saving -/

/-- **BGK at the prize.** Bourgain–Glibichuk–Konyagin is nontrivial for ANY `α > 0` (threshold `0`,
    so the prize `α = 15/79 > 0` PASSES), but it delivers only `H^{1−o(1)}`: as a clean exponent its
    saving is `o(1)`, modelled here by saving `s = 0`, giving `H`-exponent `1` (no power saving).
    BGK clears the threshold but does NOT cross the Paley barrier. -/
theorem bgk_threshold_passes : (0 : ℚ) < prizeAlpha := by
  unfold prizeAlpha; norm_num

/-- BGK's `H`-exponent (`s = 0`, `c = 0`) is `1`: nontrivial in the `o(1)` sense, but no power
    saving — it does NOT reach the prize `1/2`. -/
theorem bgk_exp_eq_one : spExp 0 0 prizeBeta = 1 := by
  unfold spExp; ring

theorem bgk_at_prize_gt_half : spExp 0 0 prizeBeta > prizeExp := by
  unfold spExp prizeExp; norm_num

/-! ### 4. The census: NO known joint lever reaches the prize -/

/-- The **family threshold predicate**: a power-saving sum-product bound (saving `s > 0`, tax `c`
    with the Burgess `p^{1/4}` engine, `αThr = 1/4`) is *applicable* at thinness `α` iff
    `α > 1/4`. At the prize `α = 15/79`, this is FALSE for every member. -/
def applicableAtPrize (αThr : ℚ) : Prop := prizeAlpha > αThr

/-- **Census, line 1 (di Benedetto / Petridis–Shparlinski / Konyagin–Shkredov / Bourgain–Garaev /
    Shkredov-`T_k` / Murphy–Rudnev / Macourt / Kerr):** ALL share `αThr = 1/4` and are NOT
    applicable at the prize. -/
theorem burgessFamily_not_applicable : ¬ applicableAtPrize burgessThreshold := by
  unfold applicableAtPrize burgessThreshold prizeAlpha; norm_num

/-- **Census, line 2 (HBK):** `αThr = 1/3`, not applicable. -/
theorem hbk_not_applicable : ¬ applicableAtPrize (1/3) := by
  unfold applicableAtPrize prizeAlpha; norm_num

/-- **Census, line 3 (Weil/Gauss):** `αThr = 1/2`, not applicable. -/
theorem weil_not_applicable : ¬ applicableAtPrize (1/2) := by
  unfold applicableAtPrize prizeAlpha; norm_num

/-! ### 5. The named residual — the sum-product exponent that WOULD close the prize -/

/-- **The residual closing condition.** A hypothetical sum-product bound `H^{1−s}·p^{c}` *closes the
    prize* iff it (a) holds at the prize thinness `α = 15/79` — i.e. survives BELOW the Burgess edge
    `1/4` — and (b) reaches the prize exponent `spExp s c β ≤ 1/2` at `β = 79/15`. We name the
    exponent requirement (b); requirement (a) is the deeper "survives below `p^{1/4}`" condition. -/
def sumProductReachesPrize (s c : ℚ) : Prop := spExp s c prizeBeta ≤ prizeExp

/-- **The EXACT saving required at the prize.** `sumProductReachesPrize s c` holds iff
    `s − c·β ≥ 1/2`, i.e. `s ≥ 1/2 + c·(79/15)`. A Paley-strength saving `s = 1/2` with **zero**
    tax (`c = 0`) exactly reaches the prize; ANY positive Burgess tax `c > 0` pushes the required
    saving strictly above `1/2`. The open input named here: a power saving `s` that (i) is at least
    `1/2 + c·β` and (ii) survives below `p^{1/4}`. No published bound has either property. -/
theorem saving_needed_at_prize (s c : ℚ) :
    sumProductReachesPrize s c ↔ s - c * prizeBeta ≥ 1/2 := by
  unfold sumProductReachesPrize spExp prizeBeta prizeExp
  constructor <;> intro h <;> linarith

/-- **Paley with zero tax reaches the prize** — the only known sufficient exponent, and exactly the
    open input. `s = 1/2`, `c = 0` gives `H`-exponent exactly `1/2`. -/
theorem paley_zeroTax_reaches : sumProductReachesPrize (1/2) 0 := by
  unfold sumProductReachesPrize spExp prizeBeta prizeExp; norm_num

/-- **Any positive Burgess tax breaks even Paley saving at the prize.** With `s = 1/2` but the
    genuine trilinear tax `c = 1/72`, the `H`-exponent is `1/2 + (79/15)/72 = 1/2 + 79/1080 > 1/2`:
    the bound does NOT reach the prize. The prize requires the tax to be eliminated, not just the
    saving improved — quantifying why the `p^{1/4}` Burgess barrier is the true wall. -/
theorem paley_with_tax_fails : ¬ sumProductReachesPrize (1/2) (1/72) := by
  unfold sumProductReachesPrize spExp prizeBeta prizeExp; norm_num

/-- The exact shortfall of Paley-saving-with-trilinear-tax at the prize:
    `spExp (1/2) (1/72) β − 1/2 = 79/1080 ≈ 0.0731`. -/
theorem paley_with_tax_shortfall :
    spExp (1/2) (1/72) prizeBeta - prizeExp = 79/1080 := by
  unfold spExp prizeBeta prizeExp; norm_num

/-! ### 6. Consolidating verdict -/

/-- **THE VERDICT (U1).** At the EXACT prize thinness `α = 15/79 ≈ 0.19`:
    1. the prize is strictly below the Burgess edge (`prizeAlpha_lt_quarter`),
    2. the entire power-saving sum-product family (di Benedetto, Petridis–Shparlinski, Konyagin–
       Shkredov, Bourgain–Garaev, Shkredov-`T_k`, Murphy–Rudnev, Macourt, Kerr) is OUT OF RANGE
       (`burgessFamily_not_applicable`), and where forced to evaluate gives `> 1` (trivial,
       `diBenedetto_at_prize_trivial`),
    3. HBK and Weil are even further out (`hbk_not_applicable`, `weil_not_applicable`),
    4. the sole nontrivial survivor BGK carries no power saving (`bgk_exp_eq_one`),
    5. closing requires a tax-free Paley saving that survives below `p^{1/4}`
       (`saving_needed_at_prize`) — an unpublished input.

    The joint additive-multiplicative (sum-product) lever **VANISHES at the prize**. -/
theorem joint_lever_vanishes_at_prize :
    prizeAlpha < burgessThreshold ∧
    ¬ applicableAtPrize burgessThreshold ∧
    spExp (191/2880) (1/72) prizeBeta > 1 ∧
    spExp 0 0 prizeBeta = 1 ∧
    (∀ s c : ℚ, sumProductReachesPrize s c ↔ s - c * prizeBeta ≥ 1/2) :=
  ⟨prize_below_burgess, burgessFamily_not_applicable, diBenedetto_at_prize_trivial,
   bgk_exp_eq_one, saving_needed_at_prize⟩

end ArkLib.ProximityGap.Frontier.BridgeJointSumProduct

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointSumProduct.prizeAlpha_mul_prizeBeta
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointSumProduct.diBenedetto_exp_at_prize
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointSumProduct.prize_threshold_gap
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointSumProduct.saving_needed_at_prize
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointSumProduct.joint_lever_vanishes_at_prize
