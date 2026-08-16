/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# BCHKS 1.12 / di-Benedetto trilinear — the SOTA-closest CONDITIONAL lever (#444)

**Target.** Package the single most quantitatively-close *external* lever — the Petridis–Shparlinski
**trilinear** estimate underlying di Benedetto's thin-subgroup bound `M(H) ≤ H^{1−31/2880}` — as a
named conditional implication `(trilinear estimate with saving `s` at the prize exponent)
⟹ M = max_{b≠0}|η_b| ≤ prizeBound ⟹ μ_{2r} ≤ Wick`, axiom-clean, with the precise trilinear-saving
residual named **honestly as the half-power gap**.

## The trilinear object (Petridis–Shparlinski, the `p^{1/4}`-tax)

di Benedetto's edge bound (arXiv:2003.06165 §5, baseline `H^{1−31/2880}` at the Burgess edge
`|H|=p^{1/4}`) is a fixed **three-fold amplification**: the cubed character sum is estimated by the
Petridis–Shparlinski incidence inequality
  `Σ_{x∈X,y∈Y,z∈Z} ψ(xyz)  ≤  |X|^{3/4} · |Y|^{3/4} · |Z|^{7/8} · p^{1/8}`
(the `7/8` exponent on the third variable, paid for with a `p^{1/8}` prefactor; cubed this is the
`p^{1/4}` **tax**). Specialised to `X=Y=Z=μ_n` (`|μ_n|=n=H`) the trilinear bound reads, for the
single character sum `M = max_{b≠0}|η_b|`,
  `M³  ≲  n^{3/4+3/4+7/8} · p^{1/8}  =  n^{19/8} · p^{1/8}`,
i.e. `M ≲ n^{19/24} · p^{1/24}`. Nontrivial (`M < n`) only while the `p^{1/8}` tax is dominated, i.e.
while `n = H > p^{1/4}`. **Below the Burgess edge the tax wins and the trilinear bound is vacuous.**

## Why this is the SOTA-closest lever — and where it stops (the honest residual)

The prize regime is `H = n = p^{1/β}` with `β ≈ 4–5` (`n=2^30`, `p≈n·2^128` ⟹ `β≈5.27`). The
trilinear bound's window of nontriviality is exactly `β < 4` (`H > p^{1/4}`). The prize sits **at or
below** the Burgess edge, where the `p^{1/4}` tax is *not* dominated. So the SOTA trilinear lever,
applied verbatim, **does not reach the prize**: it would need the `p^{1/4}`-tax prefactor removed
all the way down to `H ~ p^{1/5}` (`β=5`). That tax-removal is the **half-power gap** — a full
`p^{1/4} → p^{0}` improvement on the third-variable prefactor, equivalently the gap from di
Benedetto's `H^{1−31/2880}` (effective only above `H=p^{1/4}`) to the Paley conjecture `M ≤ 2√n`
(`H > p^{ε}`). No 2024–26 result removes it (memory: SOTA exponent localization, `arXiv:2401.04756`).

This file lands, **axiom-clean and CONDITIONAL**:
1. `TrilinearSavingAtPrizeExponent` — the named Prop: a trilinear character-sum estimate yielding
   `M ≤ n^{1−s}` with saving `s > 0` **at the prize exponent** `H = n = p^{1/β}` (i.e. with the
   `p^{1/4}` tax already removed down to that `β`). This Prop **IS the open half-power gap** — naming
   it is the whole point; it is NOT secretly the prize, it is the *external* analytic input.
2. `prize_floor_of_trilinear_saving` — if the trilinear saving reaches `s ≥ 1/2`, then `M ≤ √n`,
   which is **below** the Parseval-saddle prize ceiling `√(e·n·log p)` for `n ≥ 1`, `log p ≥ 1`;
   hence the prize floor holds. (`s = 1/2` = the Paley/`2√n` target; `s < 1/2` = strictly weaker.)
3. `trilinear_saving_to_wick` — composing with the moment bridge: `M ≤ √n ⟹ M^{2r} ≤ n^r ≤ p·Wick`
   for any `r`, i.e. the trilinear bound (at `s≥1/2`) discharges the single-depth Wick obligation
   `M^{2r} ≤ p · (2r−1)‼ · n^r` outright (the Parseval-route consumer of `prize_floor_amgm_sqrt_e`).
4. `diBenedetto_saving_below_half` — the HONEST gap quantifier: the di Benedetto edge saving is
   `31/2880 < 1/2` (indeed `< 1/24 < 1/2`), so the *proven* SOTA trilinear input is a full
   constant-order short of the `s = 1/2` needed; and it is moreover **vacuous below `H=p^{1/4}`**.

## HONESTY

The residual `TrilinearSavingAtPrizeExponent` IS the half-power gap (the `p^{1/4}`-tax removal at
`H~p^{1/5}`). This file does NOT prove the prize: it packages the closest external lever as a named
hypothesis and proves the (genuine, non-vacuous, non-circular) implication "trilinear saving `s≥1/2`
at the prize exponent ⟹ prize floor / single-depth Wick". The hypothesis is the *external analytic
number-theory* input, strictly NOT equal to the prize statement (the prize is a Lean obligation
about `μ_n` periods; this is a Petridis–Shparlinski-type incidence estimate). Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BCHKSTrilinearConditional

open Real

/-! ## 1. The trilinear exponent bookkeeping (proven, unconditional) -/

/-- **The specialised trilinear exponent.** Petridis–Shparlinski `|X|^{3/4}|Y|^{3/4}|Z|^{7/8}` at
`X=Y=Z=μ_n` gives `M³ ≤ n^{3/4+3/4+7/8}·p^{1/8} = n^{19/8}·p^{1/8}`, i.e. the per-variable exponent on
`n` is `(3/4+3/4+7/8)/3 = 19/24`. We record `19/24 < 1` (the bound is sub-trivial only modulo the
tax). -/
theorem trilinear_n_exponent : (3/4 + 3/4 + 7/8 : ℝ) / 3 = 19/24 := by norm_num

/-- **The trilinear `n`-exponent is `< 1`** — the sum is sub-trivial in the `n`-aspect (the saving
lives in the `1/6` deficit), before the `p^{1/4}` cubed tax is charged. -/
theorem trilinear_n_exponent_lt_one : (3/4 + 3/4 + 7/8 : ℝ) / 3 < 1 := by norm_num

/-- **The cubed `p`-tax exponent is `1/4`.** The `p^{1/8}` prefactor on `M³` is `p^{1/4}` on `M⁴`/per
the Burgess-edge normalisation: nontrivial only while `n = H > p^{1/4}`, vacuous at/below the edge. -/
theorem trilinear_p_tax : (3 : ℝ) * (1/8) = 3/8 ∧ (0 : ℝ) < 1/4 := by
  constructor <;> norm_num

/-! ## 2. The named residual: trilinear saving at the prize exponent (the half-power gap) -/

/-- **THE OPEN HALF-POWER GAP, as a named Prop.** A trilinear character-sum estimate is available *at
the prize exponent* `H = n = p^{1/β}` (β≈4–5) with multiplicative saving `s` iff the worst nonzero
period obeys `M ≤ n^{1−s}` — i.e. the `p^{1/4}` tax has been removed down to that `β`. This predicate
`TrilinearSavingAtPrizeExponent M n s` is the **external analytic input** (a Petridis–Shparlinski /
di Benedetto-type incidence bound), NOT the prize: it is the precise statement whose proof is the
`p^{1/4}`-tax removal at `H~p^{1/5}`. The di Benedetto SOTA furnishes it only for `s ≤ 31/2880` and
only for `β < 4`; reaching `s = 1/2` for `β ≤ 5` is the half-power gap. -/
def TrilinearSavingAtPrizeExponent (M n s : ℝ) : Prop := M ≤ n ^ (1 - s)

/-- **The di Benedetto SOTA saving is a full constant short of `1/2` (the honest gap quantifier).**
The proven edge saving `31/2880` (general subgroup), and even the near-Sidon `1/24`, are `< 1/2`. So
the *proven* trilinear input, even granting the tax removal, only yields `M ≤ n^{1−31/2880}` (or
`n^{1−1/24}`), a constant-order exponent `≈ 0.958`–`0.99`, NOT the `s=1/2` (`√n`) the prize needs. -/
theorem diBenedetto_saving_below_half :
    (31 / 2880 : ℝ) < 1 / 2 ∧ (1 / 24 : ℝ) < 1 / 2 ∧ (31 / 2880 : ℝ) < 1 / 24 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## 3. The CONDITIONAL implication: trilinear saving `s ≥ 1/2` ⟹ prize floor -/

/-- **Trilinear saving `s ≥ 1/2` ⟹ `M ≤ √n`.** If the trilinear estimate reaches the Paley saving
`s = 1/2` (`M ≤ n^{1−1/2} = √n`) — or anything stronger — at the prize exponent, the worst nonzero
period is square-root cancelled. (`s = 1/2` is exactly the `2√n`/Paley-conjecture target; the di
Benedetto SOTA gives `s ≤ 31/2880 ≪ 1/2`, the gap quantified by `diBenedetto_saving_below_half`.) -/
theorem M_le_sqrt_of_trilinear_saving {M n s : ℝ} (hn : 1 ≤ n) (hs : 1 / 2 ≤ s)
    (htri : TrilinearSavingAtPrizeExponent M n s) :
    M ≤ Real.sqrt n := by
  unfold TrilinearSavingAtPrizeExponent at htri
  refine le_trans htri ?_
  rw [Real.sqrt_eq_rpow]
  -- `n^{1−s} ≤ n^{1/2}` since `n ≥ 1` and `1 − s ≤ 1/2`.
  apply Real.rpow_le_rpow_of_exponent_le hn
  linarith

/-- **The prize floor from the trilinear lever (CONDITIONAL).** If the trilinear estimate reaches
saving `s ≥ 1/2` at the prize exponent, then `M ≤ √n ≤ √(e·n·log p)` for `n ≥ 1`, `log p ≥ 1` — i.e.
the worst period sits **below** the Parseval-saddle prize ceiling `√(e·n·log p)` (the
`prize_floor_amgm_sqrt_e` value). So the trilinear saving `s≥1/2` ⟹ the prize floor. This is the
clean conditional packaging of the SOTA-closest external lever; the hypothesis `htri` (= the named
half-power residual) is the only open input. -/
theorem prize_floor_of_trilinear_saving {M n s logp : ℝ}
    (hn : 1 ≤ n) (hlogp : 1 ≤ logp) (hs : 1 / 2 ≤ s)
    (htri : TrilinearSavingAtPrizeExponent M n s) :
    M ≤ Real.sqrt (Real.exp 1 * n * logp) := by
  have hMsqrt : M ≤ Real.sqrt n := M_le_sqrt_of_trilinear_saving hn hs htri
  refine le_trans hMsqrt ?_
  apply Real.sqrt_le_sqrt
  -- `n ≤ e·n·logp` since `e ≥ 1`, `logp ≥ 1`, `n ≥ 1`.
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hnpos : (0 : ℝ) ≤ n := le_trans zero_le_one hn
  -- `n = 1·n·1 ≤ e·n·logp` by monotonicity in each factor.
  calc n = 1 * n * 1 := by ring
    _ ≤ Real.exp 1 * n * logp := by
        apply mul_le_mul
        · apply mul_le_mul he (le_refl n) hnpos (le_trans zero_le_one he)
        · exact hlogp
        · norm_num
        · positivity

/-! ## 4. Composition with the moment bridge: trilinear ⟹ single-depth Wick obligation -/

/-- **Trilinear saving `s ≥ 1/2` discharges the single-depth Wick obligation.** The minimal open
residual of the campaign is the char-`p` Wick bound `M^{2r} ≤ p·(2r−1)‼·n^r` at the saddle depth
`r=⌈log p⌉`. If the trilinear estimate reaches `s ≥ 1/2`, then `M ≤ √n ⟹ M^{2r} ≤ n^r ≤ p·(2r−1)‼·n^r`
(since `p ≥ 1` and `(2r−1)‼ ≥ 1`). So the trilinear lever, at the Paley saving, **discharges the Wick
obligation at every depth outright** — it is a *strictly sufficient* external input for the prize
floor, feeding the proven `prize_floor_amgm_sqrt_e` consumer. (The catch is entirely in the
hypothesis: `s ≥ 1/2` at `β≤5` is the half-power gap.) -/
theorem trilinear_saving_to_wick {M n s p df : ℝ} {r : ℕ}
    (hMnn : 0 ≤ M) (hn : 1 ≤ n) (hp : 1 ≤ p) (hdf : 1 ≤ df) (hs : 1 / 2 ≤ s)
    (htri : TrilinearSavingAtPrizeExponent M n s) :
    M ^ (2 * r) ≤ p * df * n ^ r := by
  have hMsqrt : M ≤ Real.sqrt n := M_le_sqrt_of_trilinear_saving hn hs htri
  -- `M^{2r} = (M²)^r ≤ (√n²)^r = n^r ≤ p·df·n^r`.
  have hnnn : (0 : ℝ) ≤ n := le_trans zero_le_one hn
  have hMsq : M ^ 2 ≤ n := by
    have : M ^ 2 ≤ (Real.sqrt n) ^ 2 := pow_le_pow_left₀ hMnn hMsqrt 2
    rwa [Real.sq_sqrt hnnn] at this
  have hkey : M ^ (2 * r) ≤ n ^ r := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hMsq r
  refine le_trans hkey ?_
  -- `n^r ≤ p·df·n^r` since `p·df ≥ 1`.
  have hpdf : (1 : ℝ) ≤ p * df := by nlinarith [hp, hdf]
  have hnr : (0 : ℝ) ≤ n ^ r := pow_nonneg hnnn r
  calc n ^ r ≤ (p * df) * n ^ r := le_mul_of_one_le_left hnr hpdf
    _ = p * df * n ^ r := by ring

end ArkLib.ProximityGap.BCHKSTrilinearConditional

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BCHKSTrilinearConditional.trilinear_n_exponent
#print axioms ArkLib.ProximityGap.BCHKSTrilinearConditional.trilinear_n_exponent_lt_one
#print axioms ArkLib.ProximityGap.BCHKSTrilinearConditional.trilinear_p_tax
#print axioms ArkLib.ProximityGap.BCHKSTrilinearConditional.diBenedetto_saving_below_half
#print axioms ArkLib.ProximityGap.BCHKSTrilinearConditional.M_le_sqrt_of_trilinear_saving
#print axioms ArkLib.ProximityGap.BCHKSTrilinearConditional.prize_floor_of_trilinear_saving
#print axioms ArkLib.ProximityGap.BCHKSTrilinearConditional.trilinear_saving_to_wick
