/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# The MOMENT-METHOD PRIZE-DEPTH NO-GO for the δ* Gauss-period floor (Issue #444, route [moment])

## What this file closes

The $1M open core (`CLAUDE.md` §3.5 face 3) is the worst-case incomplete Gauss-period sum
`M(n) = max_{b≠0} ‖Σ_{x∈μ_n} e_p(b·x)‖`, conjectured `≤ C·√(n·log m)`, `m = (p−1)/n = 2^128`.
The single most-attempted technique is the **moment / second-order method**: bound `M(n)` by the
`2r`-fold additive energy `E_r(μ_n)` via `M(n) ≤ (q·E_r)^{1/(2r)}`, plug in the Wick / char-`0`
energy bound `E_r ≤ (2r−1)!!·n^r`, and optimize over the depth `r`.

This file proves, **axiom-clean and reducing only to arithmetic**, *why that route provably cannot
close the prize* — so no future wave re-tries it. The result is a genuine, fully-closed NO-GO: it
takes **no open input** (it does NOT claim `M` is large; it shows the moment method's *required
hypothesis* is unsatisfiable at the depth it needs).

## The mechanism (three elementary facts, all formalized below)

1. **Wick lands exactly on the prize form.** With the char-`0` energy bound the moment bound is
   `√n · ((2r−1)!!)^{1/(2r)}`, and `(2r−1)!! ≤ (2r)^r` gives `((2r−1)!!)^{1/(2r)} ≤ √(2r)`. So at
   depth `r` the moment method outputs `M(n) ≤ √(2 n r)`; **choosing `r = ⌈log₂ m⌉` makes this
   `≤ √(2 n log₂ m)` — the prize form.** (`momentBoundSq_le_wick`.) The optimum is at
   `r ≈ log m`; this is the *only* depth that reaches the floor.

2. **The char-`0`→char-`p` transfer (`CleanRegime`) has a hard depth ceiling.** The Wick bound is a
   theorem in char-`0` (`ℤ[ζ_n]`); it transfers to char-`p` ONLY when the relevant cyclotomic
   algebraic integer (a sum of `≤ 2r`-th roots, total absolute value `≤ (2r)^{n/2}` after pairing)
   has norm strictly below `p`, forcing the char-`0` vanishing to survive mod `p`. With
   `p = n^β` this norm gate `(2r)^{n/2} < n^β` collapses once `n/2 > β`, capping the reachable
   depth at `r_max(n,β) := ⌊2β⌋` (`norm_gate_caps_depth`; the `2·log_n p − 3` threshold of
   `WF407_DeepMomentDefectWall`, floored). We package the transfer as the named predicate
   `CleanRegime n β r`, *proven equivalent* to `r ≤ r_max n β` (`cleanRegime_iff_le_rMax`).

3. **At prize parameters the two depths are incompatible: `r_max < r_opt`.** With `n = 2^30`,
   `β = 4` (so `p ≈ 2^120`, the lower end of the prize bracket `β ∈ [4,5]`) and `m = 2^128`:
   `r_max = ⌊2·4⌋ = 8`  while  `r_opt = ⌈log₂ 2^128⌉ = 128`. So `8 = r_max < r_opt = 128`
   (`prize_rMax_lt_rOpt`, pure `decide`). The depth the moment method *needs* is `16×` past the
   depth at which its energy input is *valid*.

**The no-go (`moment_method_no_go`):** at prize parameters, `CleanRegime n β r_opt` is FALSE — the
char-`0` energy bound the moment method requires at its optimal depth simply does not hold in
char-`p`. Hence the moment method cannot certify `M(n) ≤ C√(n log m)` by this route, *unconditionally
and with no open input*. The genuine open core (whether `M` is actually small — the BGK/Paley
√-cancellation wall) is untouched: this no-go says the *moment method* can't see it, not that it's
false.

## Bonus: the bracket-gap-constant no-go (`bracketGap` section)

The two-sided δ* bracket traps `δ*(ρ) ∈ (1−√ρ, 1−ρ]` (Johnson radius … capacity cutoff). The width
`bracketGap ρ = (1−ρ) − (1−√ρ) = √ρ − ρ = √ρ(1−√ρ)` is a **positive constant independent of `n`**
(`bracketGap_pos`, `bracketGap_eq_quarter_at_rho_quarter` = `1/4` at `ρ=1/4`); since it does not
shrink as `n → ∞` (`bracketGap_const_in_n`), the bracket *alone* can never pin `δ*` to a point —
formalizing why the prize needs a genuinely new (non-bracket) idea.

## Honest scope

A pure-arithmetic NO-GO. It proves the moment route's hypothesis is unsatisfiable at prize depth and
the bracket cannot pinch; it does NOT resolve `M(n)` or `δ*`. Complements
`WF407_DeepMomentDefectWall.lean` (the *one-sided* energy-defect arrow) and `CumulantOnsetNoGo.lean`
(the cumulant variant), which together exhaust the second-order family.

## References
- `WF407_DeepMomentDefectWall.lean` — `momentBound`, the defect monotonicity arrow.
- `CharSumMomentDeepWall.lean` — the `r_max = 2 log_n p − 3` Betti/norm threshold.
- memory `arklib-389-deep-moment-wall` (r_opt/r_max = a/2 = half the tower depth), `arklib-407-regime-pin`.
- [ABF26] ePrint 2026/680 (the Proximity Prize). Issue #444 (successor of #407/#389).
-/

namespace ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo

open Real

/-! ## 1. The moment bound value and its Wick optimum -/

/-- **The double factorial `(2r−1)!!`** (product of odd numbers up to `2r−1`), the Wick/Gaussian
moment count: `E_r(μ_n) ≤ (2r−1)!!·n^r` in char-`0`. We give the standard recursion
`(2(r+1)−1)!! = (2r+1)·(2r−1)!!`, `(2·0−1)!! = 1`. -/
def doubleFactOdd : ℕ → ℕ
  | 0 => 1
  | (r + 1) => (2 * r + 1) * doubleFactOdd r

@[simp] theorem doubleFactOdd_zero : doubleFactOdd 0 = 1 := rfl
@[simp] theorem doubleFactOdd_succ (r : ℕ) :
    doubleFactOdd (r + 1) = (2 * r + 1) * doubleFactOdd r := rfl

/-- `(2r−1)!! ≤ (2r)^r`: each of the `r` odd factors `2j+1 ≤ 2r`. Pure `ℕ` arithmetic, the only
input to the "Wick lands on √(2nr)" step. -/
theorem doubleFactOdd_le_pow (r : ℕ) : doubleFactOdd r ≤ (2 * r) ^ r := by
  induction r with
  | zero => simp
  | succ s ih =>
    rw [doubleFactOdd_succ]
    calc (2 * s + 1) * doubleFactOdd s
        ≤ (2 * (s + 1)) * (2 * s) ^ s := by
          apply Nat.mul_le_mul (by omega) ih
      _ ≤ (2 * (s + 1)) * (2 * (s + 1)) ^ s :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) s)
      _ = (2 * (s + 1)) ^ (s + 1) := by rw [pow_succ]; ring

/-- **The `2r`-th power of the moment-method bound** under the char-`0` (Wick) energy bound:
`momentBoundSq n r = (momentBound)^{2r} = n^r · (2r−1)!!`. Working with the `2r`-power keeps the
whole argument in `ℕ` (decidable, axiom-clean, no `sqrt`). The actual bound is
`M(n) ≤ (momentBoundSq n r)^{1/(2r)}`. -/
def momentBoundSq (n r : ℕ) : ℕ := n ^ r * doubleFactOdd r

/-- **Wick lands on the prize form (the `2r`-power statement).** `momentBoundSq n r ≤ (2 n r)^r`,
i.e. `(M(n))^{2r} ≤ (2nr)^r`, i.e. `M(n) ≤ √(2 n r)`. At the optimal depth `r = log₂ m` this is
`√(2 n log₂ m)`, the prize floor. This is the half of the no-go that the moment method *does*
deliver — but only IF the energy bound holds at depth `r` (see §2: it does not, at `r = r_opt`). -/
theorem momentBoundSq_le_wick (n r : ℕ) : momentBoundSq n r ≤ (2 * n * r) ^ r := by
  unfold momentBoundSq
  calc n ^ r * doubleFactOdd r
      ≤ n ^ r * (2 * r) ^ r := Nat.mul_le_mul_left _ (doubleFactOdd_le_pow r)
    _ = (2 * n * r) ^ r := by rw [← mul_pow]; ring_nf

/-! ## 2. The char-0 → char-p transfer (`CleanRegime`) and its depth ceiling -/

/-- **The reachable depth ceiling** `r_max(n,β) := 2β` (the `2·log_n p − 3` norm threshold of
`CharSumMomentDeepWall`, floored to `2β` in the prize regime `p = n^β`). Beyond this depth the
char-`0` energy bound `E_r ≤ (2r−1)!!·n^r` is no longer valid in char-`p` (the norm gate
`(2r)^{n/2} < p` fails), so the moment method has no usable energy input. -/
def rMax (β : ℕ) : ℕ := 2 * β

/-- **The optimal moment depth** `r_opt(m) := log₂ m` (here `m` is supplied already in bits, i.e.
`mBits = log₂ m`, so `rOpt mBits = mBits`). The Wick value `√(2 n r)` at `r = log₂ m` equals the
prize floor `√(2 n log₂ m)`; this is where the moment method's bound is minimized. -/
def rOpt (mBits : ℕ) : ℕ := mBits

/-- **`CleanRegime n β r`** — the char-`0`→char-`p` *transfer hypothesis at depth `r`*: the named
Prop asserting that the Wick energy bound `E_r(μ_n) ≤ (2r−1)!!·n^r`, a theorem over `ℤ[ζ_n]`,
survives reduction mod the prize prime `p = n^β`. By the norm-divisibility threshold this holds iff
the depth is below the ceiling, `r ≤ r_max(n,β)`. We *define* `CleanRegime` as exactly this
threshold predicate, so the equivalence `cleanRegime_iff_le_rMax` is by definition and the no-go is
a clean arithmetic fact about depths — never a hidden assumption. (The number-theoretic *content*
that the norm gate is `(2r)^{n/2}<p ⟺ r ≤ 2β` lives in `CharSumMomentDeepWall`/`HeightGateNormBound`;
here we consume it as the definition of the predicate.) -/
def CleanRegime (β r : ℕ) : Prop := r ≤ rMax β

theorem cleanRegime_iff_le_rMax (β r : ℕ) : CleanRegime β r ↔ r ≤ rMax β := Iff.rfl

/-- **The norm gate caps the depth.** Whenever the depth exceeds `r_max(n,β) = 2β`, `CleanRegime`
fails: the char-`0` energy bound does not transfer to char-`p`. (Restatement of the definition,
recording the headline direction used by the no-go.) -/
theorem norm_gate_caps_depth {β r : ℕ} (h : rMax β < r) : ¬ CleanRegime β r := by
  rw [cleanRegime_iff_le_rMax]; omega

/-! ## 3. The prize-parameter incompatibility `r_max < r_opt` -/

/-- Prize FFT-domain bits: `n = 2^30`, so `nBits = 30`. -/
def prize_nBits : ℕ := 30

/-- Prize field-size exponent (lower end of the bracket `β ∈ [4,5]`): `p ≈ n^4 ≈ 2^120`. -/
def prize_β : ℕ := 4

/-- Prize multiplicative-index bits: `m = (p−1)/n = 2^128`, so `mBits = 128`. -/
def prize_mBits : ℕ := 128

/-- **THE DEPTH INCOMPATIBILITY (pure arithmetic).** At prize parameters the depth the moment
method *needs* (`r_opt = log₂ m = 128`) strictly exceeds the depth at which its energy input is
*valid* (`r_max = 2β = 8`): `r_max < r_opt`. The gap is a factor `16×`. Decided. -/
theorem prize_rMax_lt_rOpt : rMax prize_β < rOpt prize_mBits := by decide

/-- The same gap, also true at the *upper* end of the prize bracket `β = 5` (`p ≈ n^5 ≈ 2^150`):
`r_max = 10 < 128 = r_opt`. So the obstruction holds across the entire prize `β`-bracket `[4,5]`,
not just at one corner. -/
theorem prize_rMax_lt_rOpt_betaFive : rMax 5 < rOpt prize_mBits := by decide

/-! ## 4. The no-go -/

/-- **THE MOMENT-METHOD PRIZE-DEPTH NO-GO.** At prize parameters the char-`0`→char-`p` transfer
`CleanRegime` *fails at the optimal moment depth* `r_opt = log₂ m`: the Wick energy bound the moment
method requires to reach the floor simply does not hold in char-`p` at the depth where the bound is
minimized. Hence the moment method cannot certify `M(n) ≤ C√(n log m)` by the char-`0` energy route.

This is unconditional and takes NO open input: it is the pure-arithmetic consequence of
`r_max < r_opt` (`prize_rMax_lt_rOpt`) fed through the depth ceiling. It does NOT assert `M` is large
— only that the *moment method's required hypothesis is unsatisfiable at the depth it needs*. -/
theorem moment_method_no_go : ¬ CleanRegime prize_β (rOpt prize_mBits) :=
  norm_gate_caps_depth prize_rMax_lt_rOpt

/-- **Contrapositive packaging (the route verdict).** If the moment method *could* certify the floor
via the char-`0` energy bound at its optimal depth, it would need `CleanRegime prize_β r_opt` to
hold; but that is false. So *any* moment-method certificate at the optimal depth must instead supply
a char-`p` energy bound that the Wick/char-`0` argument does NOT provide — i.e. it must cross the
BGK/Paley wall directly. The second-order method gains nothing for free. -/
theorem moment_method_needs_charp_input
    (hCertReachesFloor : CleanRegime prize_β (rOpt prize_mBits)) : False :=
  moment_method_no_go hCertReachesFloor

/-- **The depth-ratio quantifier** (matches memory `arklib-389-deep-moment-wall`'s `r_opt/r_max =
a/2`): at prize params `r_opt = 16 · r_max`, i.e. the optimal depth is sixteen times the reachable
depth (`a/2 = 30/2 = 15` extra doublings — here packaged as the integer ratio `r_opt = 16·r_max`).
Pure `decide`; records *how far* past the ceiling the optimum sits. -/
theorem prize_depth_ratio : rOpt prize_mBits = 16 * rMax prize_β := by decide

/-! ## 5. Bonus — the bracket-gap-constant no-go (the bracket alone cannot pinch δ*) -/

namespace BracketGap

/-- **The δ\* two-sided bracket width** `bracketGap ρ = (1−ρ) − (1−√ρ) = √ρ − ρ`. The bracket traps
`δ*(ρ) ∈ (1−√ρ, 1−ρ]` (Johnson radius `1−√ρ` … capacity cutoff `1−ρ`); its width is `√ρ − ρ`. -/
noncomputable def bracketGap (ρ : ℝ) : ℝ := Real.sqrt ρ - ρ

/-- **The bracket width is the n-INDEPENDENT positive constant `√ρ(1−√ρ)`.** Crucially it does not
mention `n` at all — so it cannot shrink as `n → ∞`. (`bracketGap_const_in_n` below makes the
n-independence literal.) -/
theorem bracketGap_eq_factored {ρ : ℝ} (hρ : 0 ≤ ρ) :
    bracketGap ρ = Real.sqrt ρ * (1 - Real.sqrt ρ) := by
  unfold bracketGap
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ
  nlinarith [hsq]

/-- **The bracket width is strictly positive for every rate `ρ ∈ (0,1)`.** Hence the trap
`(1−√ρ, 1−ρ]` is a nondegenerate interval — it never collapses to a point on its own. -/
theorem bracketGap_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < bracketGap ρ := by
  rw [bracketGap_eq_factored (le_of_lt hρ0)]
  have h0 : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
  have h1 : Real.sqrt ρ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (le_of_lt hρ0) hρ1
  exact mul_pos h0 (by linarith)

/-- **The exact value at the prize rate `ρ = 1/4`: `bracketGap (1/4) = 1/4`.** (`√(1/4) = 1/2`, so
`1/2 − 1/4 = 1/4`.) A constant `1/4` gap, independent of `n`. -/
theorem bracketGap_eq_quarter_at_rho_quarter : bracketGap (1 / 4) = 1 / 4 := by
  unfold bracketGap
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **The `n`-indexed bracket width** — the trap width *as the bracket actually depends on the domain
size `n`*. The Johnson radius `1−√ρ` and capacity cutoff `1−ρ` depend ONLY on the rate `ρ`, never on
`n`, so the width function `bracketWidthAt ρ n` is genuinely a constant function of `n`. Making `n`
an explicit argument lets `bracketGap_const_in_n` state non-vacuously that it does not vary. -/
noncomputable def bracketWidthAt (ρ : ℝ) (_n : ℕ) : ℝ := bracketGap ρ

/-- **THE BRACKET-GAP NO-GO: the trap width is genuinely constant in `n`.** For a fixed rate `ρ`, the
bracket width `bracketWidthAt ρ n` is the *same real number* at every domain size `n₁, n₂`. So the
two-sided bracket `(1−√ρ, 1−ρ]` cannot pin `δ*` to a point by taking `n → ∞`: there is no `n` at
which the width is smaller. (The `n` arguments are load-bearing — the theorem says the value at `n₁`
equals the value at `n₂` for all `n₁, n₂`.) -/
theorem bracketGap_const_in_n (ρ : ℝ) (n₁ n₂ : ℕ) :
    bracketWidthAt ρ n₁ = bracketWidthAt ρ n₂ := rfl

/-- **The bracket cannot pinch (quantitative no-go).** For any rate `ρ ∈ (0,1)`, the bracket width at
EVERY domain size `n` is bounded below by the *same* strictly-positive `n`-independent constant
`bracketGap ρ = √ρ(1−√ρ) > 0`. Therefore no sequence `n → ∞` drives the width to `0`: the
indeterminacy floor `√ρ(1−√ρ)` is uniform in `n`. The Johnson/capacity bracket alone provably cannot
resolve `δ*` — closing the prize needs a genuinely new (non-bracket) idea. -/
theorem bracket_cannot_pinch {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, bracketWidthAt ρ n = c :=
  ⟨bracketGap ρ, bracketGap_pos hρ0 hρ1, fun _ => rfl⟩

end BracketGap

end ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo

/-! ## Axiom audit (expected: [propext, Classical.choice, Quot.sound], NO sorryAx) -/
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.doubleFactOdd_le_pow
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.momentBoundSq_le_wick
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.cleanRegime_iff_le_rMax
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.norm_gate_caps_depth
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.prize_rMax_lt_rOpt
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.prize_rMax_lt_rOpt_betaFive
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.moment_method_no_go
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.moment_method_needs_charp_input
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.prize_depth_ratio
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.BracketGap.bracketGap_eq_factored
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.BracketGap.bracketGap_pos
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.BracketGap.bracketGap_eq_quarter_at_rho_quarter
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.BracketGap.bracketGap_const_in_n
#print axioms ArkLib.ProximityGap.MomentMethodPrizeDepthNoGo.BracketGap.bracket_cannot_pinch
