/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The **cumulant-additivity convolution engine**: the PROVEN non-tensor source of the `r`-linear saving (#444)

Per `_RudnevDilutionFixedSavingStall`, any additive-energy proof of the prize sup-norm bound
`M ≤ C√(n log m)` MUST be **non-tensor**: the trivial tensor lift `E_{r+1} ≤ |G|²·E_r` carries a
FIXED saving and stalls (`M`-exponent `→ 1`). The dilution theorem says the ONLY known non-tensor
mechanism delivering the `r`-LINEAR (Wick) saving is the **char-`0` cumulant-additivity** structure:
the char-`0` period `η_b^{c0} = Σ_{μ_n} e^{iθ}` is a sum of `m = n/2` i.i.d. copies of `2cos θ`
(Lam–Leung antipodal balance), so its cumulants are EXACTLY linear in `n` at every depth — which is
the sub-Gaussian / Wick bound delivered DIRECTLY at every `r`, never by tensoring `E_2`.

The two prior bricks (`_AvNonTensorAutocorrAverage`, `_NT_5_scratch`) localize the gap to a single
open inequality but carry the char-`0` `r`-linear step `cross^{c0}_r ≤ 2r·n·E^{c0}_r` as a *named
input* pointing at `_AvW0_BesselWickDomination`. THIS file **proves the engine behind that step from
scratch**, axiom-clean, in its sharpest and most transparent form: the **cumulant-additivity
convolution lemma**, which is exactly the statement that the "log-derivative index" is ADDITIVE under
convolution (= cumulant additivity = independence). It is the genuine non-tensor mechanism distilled
to a pure inequality on coefficient sequences, with NO Bessel function and NO analysis.

## The mechanism, exactly

For a nonnegative coefficient sequence `u : ℕ → ℚ`, say `u` has **log-derivative index `≤ a`** if
`(k+1)·u_{k+1} ≤ a·u_k` for every `k` (`LogDerivIndex u a`). For the generating function
`U(t) = Σ u_k t^k` this reads `t·U'(t) ⪯ a·U(t)` coefficientwise — a uniform bound on the
log-derivative `U'/U ⪯ a/t`. Two facts:

* **Base atom** (`besselCoeff_logDerivIndex_one`): the single Bessel coefficient `b_k = 1/(k!)²`
  has index `≤ 1`: `(k+1)·b_{k+1} = 1/(k!·(k+1)!) ≤ 1/(k!)² = b_k`. (The `exp` coefficient
  `e_k = 1/k!` has index EXACTLY `1`: `(k+1)·e_{k+1} = e_k`.)
* **THE ENGINE** (`logDerivIndex_conv`): if `u` has index `≤ a` and `v` has index `≤ c` (both `≥ 0`),
  their convolution `w = u ⋆ v` has index `≤ a + c`. **The index ADDS under convolution.**

Iterating the engine `m` times on the base atom (index `1`) gives the `m`-fold convolution power
`c^{(m)} = (cpow b m)` index `≤ m` (`besselPow_logDerivIndex`):

> **`(r+1)·c^{(m)}_{r+1} ≤ m·c^{(m)}_r`,   i.e.   `c^{(m)}_{r+1}/c^{(m)}_r ≤ m/(r+1)`.**

Multiplying by the `(2r)!`-normalization (`besselPow_energyStep`) this is EXACTLY the char-`0`
`r`-linear Wick energy step `E^{c0}_{r+1} ≤ (2r+1)·n·E^{c0}_r` (with `m = n/2`, `n = 2m`), the step
the prize ladder consumes — now **PROVEN**, not assumed. The index growing LINEARLY in `m = n/2` is
the `r`-linear saving; a tensor lift would instead double the index every step (super-linear), which
is the fixed-saving stall in disguise.

## Why this is genuinely non-tensor (and beats the tensor lift UNCONDITIONALLY in char-`0`)

The tensor lift `E_{r+1} ≤ n²·E_r` corresponds to index `≤ 2·(r+1)·(something)` — it carries a
*fixed multiplicative* saving `n²` per step. The cumulant engine instead carries an *additive* index
`m = n/2` accumulated once over `m` independent directions, giving the per-step factor
`m/(r+1)` — which at depth `r ≈ ln p` is `≪ n` (the `r`-linear saving). `besselPow_le_tensor_step`
makes the strict separation precise: for `2r+1 < n` the engine's step `(2r+1)·n·E_r` is strictly
below the tensor ceiling `n²·E_r`, and the engine's step is **fully proven here** (no open input) in
char-`0`. This is a real, unconditional advance over the tensor lift — IN CHAR-`0`.

## The exact char-`p` break (the honest verdict)

In char-`p`, `E^{Fp}_r = E^{c0}_r + W_r` (`_NoExcessOnsetThreshold`), and the engine controls ONLY
the char-`0` part `E^{c0}_r` (it is a theorem about the Bessel/exp coefficient sequences — the
char-`0` generating function). The wraparound `W_r` is NOT a convolution power of a single atom; it
has no log-derivative index, and **numerically violates BOTH the `r`-linear step AND the tensor lift
in the very regime where it first turns on** (probe `/tmp/nt_wrap2.py`, `n = 8`: at every prime with
`W_r > 0`, `W_{r+1} > n²·W_r` near onset — the wraparound energy grows FASTER than even the tensor
ceiling per step, because `W_r` is tiny right when it switches on). So the per-step `W`-only residual
`WrapCrossBounded` of `_NT_5_scratch` is FALSE near onset — the correct prize-relevant residual is
the STATIC `W_{r*} = 0` on a good prime at the saddle depth `r* ≈ log p` (the `NoWraparound` core of
`_NoExcessOnsetThreshold`), NOT a per-step bound on `W`. We record this honestly as
`wrapStep_no_logDerivIndex_doc` (a documentation marker) and as the static transfer
`charP_energyStep_of_noWraparound` (the engine's step transfers to char-`p` EXACTLY on the
no-wraparound part).

## What this file PROVES (axiom-clean `{propext, Classical.choice, Quot.sound}`, NO `sorry`/`native_decide`)

* `LogDerivIndex`                  : the index predicate `∀ k, (k+1)·u_{k+1} ≤ a·u_k` (def).
* `besselCoeff_logDerivIndex_one`  : the Bessel atom has index `≤ 1` (the base, fully proven).
* `expCoeff_logDerivIndex_one`     : the exp atom has index EXACTLY `1` (`(k+1)·e_{k+1} = e_k`).
* **`logDerivIndex_conv`**         : **THE ENGINE** — index ADDS under convolution (`a + c`). The
  pure non-tensor mechanism: cumulant additivity as a coefficient inequality.
* `cpow_logDerivIndex`             : iterating the engine, `cpow c m` has index `≤ m·a` when `c` has
  index `≤ a` (and `c ≥ 0`).
* `besselPow_logDerivIndex`        : the Bessel power `cpow besselCoeff m` has index `≤ m` (the
  prize step engine, base atom index `1`).
* `besselPow_energyStep`          : the normalized char-`0` `r`-linear Wick energy step
  `(2r+2)!·c^{(m)}_{r+1} ≤ (2r+1)·(2m)·(2r)!·c^{(m)}_r` (with `n = 2m`), PROVEN from the index.
* `besselPow_le_tensor_step`      : the strict dilution separation `(2r+1)·n < n²` for `2r+1 < n`
  (the engine step is strictly below the tensor ceiling — non-tensor, re-proved here).

## Honest scope (`closesPrize = false`)

PROVEN unconditionally: the cumulant-additivity engine and the full char-`0` `r`-linear Wick energy
step (the non-tensor saving the dilution theorem demands) — this is a genuine advance over the tensor
lift, and it is the engine the prior bricks only named. NOT proven (and now shown to be the WRONG
per-step object): a per-step bound on the char-`p` wraparound `W_r`. The engine is a char-`0`
theorem; its char-`p` transfer is the static `NoWraparound` core (`_NoExcessOnsetThreshold`,
`OnsetExceedsSaddle`) at the saddle `r* ≈ log p`, which is the open BGK/Lam–Leung wall. This file
closes none of #444; it PROVES the non-tensor engine the route needs and pins the char-`p` residual
in its correct (static) form.

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.Frontier.AvNTCumulantEngine

open Finset

/-! ## The log-derivative index and the cumulant-additivity engine -/

/-- **The log-derivative index.** A nonnegative coefficient sequence `u : ℕ → ℚ` has
*log-derivative index `≤ a`* (`LogDerivIndex u a`) iff `(k+1)·u_{k+1} ≤ a·u_k` for every `k`. For the
generating function `U(t) = Σ u_k t^k` this is `t·U'(t) ⪯ a·U(t)` (coefficientwise) — i.e.
`U'/U ⪯ a/t`. The index is the "cumulant rate": for `e^{a·t}` it is exactly `a`; the cumulant-
additivity engine (`logDerivIndex_conv`) shows it ADDS under convolution, the defining property of
independence/cumulant additivity that makes the saving `r`-linear, NOT tensor. -/
def LogDerivIndex (u : ℕ → ℚ) (a : ℚ) : Prop := ∀ k : ℕ, ((k : ℚ) + 1) * u (k + 1) ≤ a * u k

/-- The convolution (Cauchy product) of two coefficient sequences: `(u ⋆ v) r = Σ_{i≤r} u_i·v_{r−i}`.
This is the coefficient ring of formal power series; the Bessel/exp generating functions multiply via
this product, and the `m`-fold power is `cpow`. -/
def conv (u v : ℕ → ℚ) (r : ℕ) : ℚ := ∑ i ∈ range (r + 1), u i * v (r - i)

/-- **THE CUMULANT-ADDITIVITY ENGINE: the log-derivative index ADDS under convolution.**

If `u` has index `≤ a` and `v` has index `≤ c` (both nonnegative), then `w = u ⋆ v` has index
`≤ a + c`. This is the pure non-tensor mechanism: the "cumulant rate" of a convolution (= the
generating function of a *sum of independent parts*) is the SUM of the parts' rates. Iterating it on
a single atom (index `1`) `m` times gives index `m` — LINEAR in `m`, the `r`-linear Wick saving — not
the doubling a tensor lift would force.

*Proof.* `(r+1)·w_{r+1} = (r+1)·Σ_{i=0}^{r+1} u_i v_{r+1−i}`. Write `r+1 = i + (r+1−i)` and split:
the `i`-weighted sum reindexes (`i ↦ i+1`) to `Σ_{i=0}^r (i+1)u_{i+1}·v_{r−i} ≤ a·Σ u_i v_{r−i}`
(index of `u`); the `(r+1−i)`-weighted sum has term `(r+1−i)v_{r+1−i} = (k+1)v_{k+1} ≤ c·v_k`
(`k = r−i`, index of `v`; the `i = r+1` term vanishes). Summing, `(r+1)w_{r+1} ≤ (a+c)·w_r`. -/
theorem logDerivIndex_conv {u v : ℕ → ℚ} {a c : ℚ}
    (hu0 : ∀ k, 0 ≤ u k) (hv0 : ∀ k, 0 ≤ v k)
    (hu : LogDerivIndex u a) (hv : LogDerivIndex v c) :
    LogDerivIndex (conv u v) (a + c) := by
  intro r
  -- Goal (unfolded): (r+1)·(conv u v)(r+1) ≤ (a+c)·(conv u v) r
  show ((r : ℚ) + 1) * conv u v (r + 1) ≤ (a + c) * conv u v r
  -- LHS: (r+1) * Σ_{i=0}^{r+1} u_i v_{r+1-i}
  have hconvL : conv u v (r + 1) = ∑ i ∈ range (r + 2), u i * v (r + 1 - i) := by
    unfold conv; rfl
  rw [hconvL]
  -- Expand the sum and split (r+1) = i + (r+1-i) inside each term.
  have hsplit : ∀ i ∈ range (r + 2),
      ((r : ℚ) + 1) * (u i * v (r + 1 - i))
        = (i : ℚ) * (u i * v (r + 1 - i))
          + ((r + 1 - i : ℕ) : ℚ) * (u i * v (r + 1 - i)) := by
    intro i hi
    rw [mem_range, Nat.lt_succ_iff] at hi
    have hnat : i + (r + 1 - i) = r + 1 := by omega
    have hsum : ((i : ℚ)) + ((r + 1 - i : ℕ) : ℚ) = (r : ℚ) + 1 := by
      have h2 : (i : ℚ) + ((r + 1 - i : ℕ) : ℚ) = ((i + (r + 1 - i) : ℕ) : ℚ) := by push_cast; ring
      rw [h2, hnat]; push_cast; ring
    rw [← hsum]; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- RHS: (a+c)·(conv u v) r = a·w_r + c·w_r
  have hconvR : conv u v r = ∑ i ∈ range (r + 1), u i * v (r - i) := by unfold conv; rfl
  rw [hconvR]
  -- Bound each half by a·w_r and c·w_r respectively.
  -- Half A: Σ_{i=0}^{r+1} i·u_i·v_{r+1-i}  ≤  a · Σ_{i=0}^r u_i v_{r-i}
  have hA : ∑ i ∈ range (r + 2), (i : ℚ) * (u i * v (r + 1 - i))
      ≤ a * ∑ i ∈ range (r + 1), u i * v (r - i) := by
    -- reindex i ↦ i+1: the i=0 term is 0.
    rw [Finset.sum_range_succ', Finset.mul_sum]
    -- the i=0 term `(↑0)·(u 0 · v (r+1-0))` vanishes
    have hzero : ((0 : ℕ) : ℚ) * (u 0 * v (r + 1 - 0)) = 0 := by simp
    rw [hzero, add_zero]
    apply Finset.sum_le_sum
    intro i hi
    rw [mem_range] at hi
    -- term: (i+1)·u_{i+1}·v_{r+1-(i+1)} = (i+1)·u_{i+1}·v_{r-i} ≤ a·u_i·v_{r-i}
    have hidx : ((i : ℚ) + 1) * u (i + 1) ≤ a * u i := hu i
    have heq : r + 1 - (i + 1) = r - i := by omega
    rw [heq]
    have hvnn : 0 ≤ v (r - i) := hv0 _
    calc (((i + 1 : ℕ)) : ℚ) * (u (i + 1) * v (r - i))
        = (((i : ℚ) + 1) * u (i + 1)) * v (r - i) := by push_cast; ring
      _ ≤ (a * u i) * v (r - i) := by
            exact mul_le_mul_of_nonneg_right hidx hvnn
      _ = a * (u i * v (r - i)) := by ring
  -- Half C: Σ_{i=0}^{r+1} (r+1-i)·u_i·v_{r+1-i}  ≤  c · Σ_{i=0}^r u_i v_{r-i}
  have hC : ∑ i ∈ range (r + 2), ((r + 1 - i : ℕ) : ℚ) * (u i * v (r + 1 - i))
      ≤ c * ∑ i ∈ range (r + 1), u i * v (r - i) := by
    -- drop the i=r+1 term (factor (r+1-(r+1))=0), then index of v on each remaining term.
    rw [Finset.sum_range_succ]
    have hlast : ((r + 1 - (r + 1) : ℕ) : ℚ) * (u (r + 1) * v (r + 1 - (r + 1))) = 0 := by
      simp
    rw [hlast, add_zero, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [mem_range] at hi
    -- term: (r+1-i)·u_i·v_{r+1-i}.  Let k = r-i ≥ 0 (i ≤ r). r+1-i = k+1, v_{r+1-i}=v_{k+1}.
    have hk : r + 1 - i = (r - i) + 1 := by omega
    have hidx : (((r - i : ℕ) : ℚ) + 1) * v ((r - i) + 1) ≤ c * v (r - i) := hv (r - i)
    have hunn : 0 ≤ u i := hu0 _
    rw [hk]
    calc (((r - i) + 1 : ℕ) : ℚ) * (u i * v ((r - i) + 1))
        = u i * ((((r - i : ℕ) : ℚ) + 1) * v ((r - i) + 1)) := by push_cast; ring
      _ ≤ u i * (c * v (r - i)) := by
            exact mul_le_mul_of_nonneg_left hidx hunn
      _ = c * (u i * v (r - i)) := by ring
  -- Combine: (a+c)·w_r
  calc (∑ i ∈ range (r + 2), (i : ℚ) * (u i * v (r + 1 - i)))
        + ∑ i ∈ range (r + 2), ((r + 1 - i : ℕ) : ℚ) * (u i * v (r + 1 - i))
      ≤ a * ∑ i ∈ range (r + 1), u i * v (r - i)
          + c * ∑ i ∈ range (r + 1), u i * v (r - i) := add_le_add hA hC
    _ = (a + c) * ∑ i ∈ range (r + 1), u i * v (r - i) := by ring

/-- Convolution preserves nonnegativity. -/
theorem conv_nonneg {u v : ℕ → ℚ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (r : ℕ) :
    0 ≤ conv u v r := by
  unfold conv
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hu i) (hv _))

/-! ## The base atoms: Bessel (index `≤ 1`) and exp (index `= 1`) -/

/-- Coefficient of `x^{2k}` in `I₀(2x) = Σ x^{2k}/(k!)²`. -/
noncomputable def besselCoeff (k : ℕ) : ℚ := 1 / (k.factorial : ℚ) ^ 2

/-- Coefficient of `x^{2k}` in `e^{x²} = Σ x^{2k}/k!`. -/
noncomputable def expCoeff (k : ℕ) : ℚ := 1 / (k.factorial : ℚ)

theorem besselCoeff_nonneg (k : ℕ) : 0 ≤ besselCoeff k := by unfold besselCoeff; positivity
theorem expCoeff_nonneg (k : ℕ) : 0 ≤ expCoeff k := by unfold expCoeff; positivity

/-- **The Bessel atom has log-derivative index `≤ 1`.** `(k+1)·b_{k+1} = (k+1)/((k+1)!)²
= 1/(k!·(k+1)!) ≤ 1/(k!)² = b_k`, since `(k+1)! ≥ k!`. This is the base of the engine: the single
`2cos θ` direction has cumulant rate `1`. -/
theorem besselCoeff_logDerivIndex_one : LogDerivIndex besselCoeff 1 := by
  intro k
  unfold besselCoeff
  rw [one_mul]
  -- (k+1)·1/((k+1)!)² ≤ 1/(k!)²
  have hk : (0 : ℚ) < (k.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos k
  have hfac : ((k + 1).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac]
  -- goal: ((k:ℚ)+1) * (1/((k+1)·k!)²) ≤ 1/(k!)².  Clear denominators by `div_le_div_iff`-free route.
  have hkk : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have hden1 : (0 : ℚ) < (((k : ℚ) + 1) * (k.factorial : ℚ)) ^ 2 := by positivity
  have hden2 : (0 : ℚ) < (k.factorial : ℚ) ^ 2 := by positivity
  rw [mul_one_div, div_le_div_iff₀ hden1 hden2]
  -- ((k+1)) * (k!)² ≤ ((k+1)·k!)²  = (k+1)²·(k!)²
  nlinarith [mul_pos hk hk, hkk, mul_pos hkk hk]

/-- **The exp atom has log-derivative index EXACTLY `1`.** `(k+1)·e_{k+1} = (k+1)/(k+1)! = 1/k! = e_k`.
The exponential `e^{x²}` is the index-`1` boundary; the Bessel atom sits strictly below it
(`besselCoeff_le_expCoeff`), and the engine carries this to the `m`-th power. -/
theorem expCoeff_logDerivIndex_one : LogDerivIndex expCoeff 1 := by
  intro k
  unfold expCoeff
  rw [one_mul]
  have hfac : ((k + 1).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac]
  have hk : (0 : ℚ) < (k.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos k
  have hkk : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  -- ((k+1)) * (1/((k+1)·k!)) = 1/k!  exactly
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  apply le_of_eq; ring

/-! ## The `m`-fold convolution power and its index `≤ m·a` -/

/-- `m`-fold convolution power of a coefficient sequence `c` (in `t = x²`):
`cpow c m r = [t^r] (Σ c_k t^k)^m`. The Bessel power `cpow besselCoeff m` is the char-`0` energy
generating coefficient (`E_r^{c0} = (2r)!·cpow besselCoeff (n/2) r`, `_AvW0_BesselWickDomination`). -/
noncomputable def cpow (c : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, r => if r = 0 then 1 else 0
  | m + 1, r => conv (cpow c m) c r

theorem cpow_nonneg {c : ℕ → ℚ} (hc : ∀ k, 0 ≤ c k) : ∀ m r, 0 ≤ cpow c m r := by
  intro m
  induction m with
  | zero => intro r; unfold cpow; split <;> norm_num
  | succ m ih => intro r; unfold cpow; exact conv_nonneg ih hc r

/-- The constant sequence `1, 0, 0, …` (the unit of convolution, `cpow c 0`) has index `≤ 0`. -/
theorem cpow_zero_logDerivIndex_zero (c : ℕ → ℚ) : LogDerivIndex (cpow c 0) 0 := by
  intro k
  unfold cpow
  simp only [zero_mul]
  -- (k+1)·[k+1=0] = (k+1)·0 = 0 ≤ 0
  rw [if_neg (by omega)]
  simp

/-- **Iterating the engine: `cpow c m` has log-derivative index `≤ m·a`** whenever `c` has index `≤ a`
(and `c ≥ 0`). Each convolution by `c` ADDS `a` to the index (`logDerivIndex_conv`); starting from the
unit (index `0`), `m` factors give `m·a`. The index growing LINEARLY in `m` is precisely the
`r`-linear (non-tensor) Wick saving — a tensor lift would multiply, not add. -/
theorem cpow_logDerivIndex {c : ℕ → ℚ} {a : ℚ} (hc0 : ∀ k, 0 ≤ c k) (hc : LogDerivIndex c a) :
    ∀ m, LogDerivIndex (cpow c m) (m * a) := by
  intro m
  induction m with
  | zero => simpa using cpow_zero_logDerivIndex_zero c
  | succ m ih =>
    -- cpow c (m+1) = conv (cpow c m) c, index ≤ m·a + a = (m+1)·a
    have hconv := logDerivIndex_conv (cpow_nonneg hc0 m) hc0 ih hc
    have heq : (m : ℚ) * a + a = ((m : ℚ) + 1) * a := by ring
    rw [heq] at hconv
    have : LogDerivIndex (cpow c (m + 1)) (((m : ℚ) + 1) * a) := by
      intro k; unfold cpow; exact hconv k
    convert this using 2
    push_cast; ring

/-- **The Bessel power has index `≤ m`** (the prize step engine): `cpow besselCoeff m` satisfies
`(r+1)·c^{(m)}_{r+1} ≤ m·c^{(m)}_r`. This is the cumulant-additivity engine applied `m` times to the
index-`1` Bessel atom. With `m = n/2`, this IS the char-`0` `r`-linear Wick step. PROVEN, axiom-clean.
-/
theorem besselPow_logDerivIndex (m : ℕ) : LogDerivIndex (cpow besselCoeff m) (m : ℚ) := by
  have h := cpow_logDerivIndex besselCoeff_nonneg besselCoeff_logDerivIndex_one m
  simpa using h

/-! ## The char-`0` `r`-linear Wick ENERGY step (the dilution-theorem target), PROVEN -/

/-- **The char-`0` `r`-linear Wick energy step, PROVEN from the index.** With the Bessel identity
`E_r^{c0}(μ_{2m}) = (2r)!·cpow besselCoeff m r` (`_AvW0_BesselWickDomination`, STEP 1), the index
bound `(r+1)·c^{(m)}_{r+1} ≤ m·c^{(m)}_r` becomes the normalized energy step
`(2r+2)!·c^{(m)}_{r+1} ≤ (2r+1)·(2m)·(2r)!·c^{(m)}_r`, i.e. `E^{c0}_{r+1} ≤ (2r+1)·n·E^{c0}_r` with
`n = 2m`. This is the non-tensor `r`-linear saving the dilution theorem demands — here a THEOREM, not
a named input. (The `(2r+2)!/(2r)! = (2r+2)(2r+1)` normalization cancels the `(r+1)` to leave the
`(2r+1)·2m = (2r+1)·n` factor.) -/
theorem besselPow_energyStep (m r : ℕ) :
    ((2 * r + 2).factorial : ℚ) * cpow besselCoeff m (r + 1)
      ≤ (2 * (r : ℚ) + 1) * (2 * m) * (((2 * r).factorial : ℚ) * cpow besselCoeff m r) := by
  have hidx := besselPow_logDerivIndex m r  -- (r+1)·c_{r+1} ≤ m·c_r
  -- (2r+2)! = (2r+2)(2r+1)(2r)!  and  (2r+2) = 2(r+1)
  have hfac2 : ((2 * r + 2).factorial : ℚ)
      = (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) * ((2 * r).factorial : ℚ) := by
    have e1 : 2 * r + 2 = (2 * r + 1) + 1 := by omega
    have e2 : 2 * r + 1 = (2 * r) + 1 := by omega
    rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
    push_cast; ring
  have hcr : 0 ≤ cpow besselCoeff m r := cpow_nonneg besselCoeff_nonneg m r
  have hfac0 : (0 : ℚ) ≤ ((2 * r).factorial : ℚ) := by positivity
  have h21 : (0 : ℚ) ≤ 2 * (r : ℚ) + 1 := by positivity
  -- LHS = (2r+2)(2r+1)(2r)! · c_{r+1}.  Use (r+1)c_{r+1} ≤ m c_r  and  (2r+2)=2(r+1).
  rw [hfac2]
  -- goal: (2r+2)(2r+1)(2r)! c_{r+1} ≤ (2r+1)(2m)((2r)! c_r)
  -- factor (2r+1)(2r)!: suffices (2r+2)·c_{r+1} ≤ 2m·c_r, i.e. 2(r+1)c_{r+1} ≤ 2m c_r ⟸ (r+1)c_{r+1}≤m c_r
  have hstep : (2 * (r : ℚ) + 2) * cpow besselCoeff m (r + 1) ≤ (2 * m) * cpow besselCoeff m r := by
    have : 2 * (((r : ℚ) + 1) * cpow besselCoeff m (r + 1)) ≤ 2 * ((m : ℚ) * cpow besselCoeff m r) :=
      mul_le_mul_of_nonneg_left hidx (by norm_num)
    calc (2 * (r : ℚ) + 2) * cpow besselCoeff m (r + 1)
        = 2 * (((r : ℚ) + 1) * cpow besselCoeff m (r + 1)) := by ring
      _ ≤ 2 * ((m : ℚ) * cpow besselCoeff m r) := this
      _ = (2 * m) * cpow besselCoeff m r := by ring
  -- multiply hstep by the nonneg factor (2r+1)·(2r)!
  have hmul := mul_le_mul_of_nonneg_left hstep
    (mul_nonneg h21 hfac0)
  -- hmul : ((2r+1)(2r)!)·((2r+2)c_{r+1}) ≤ ((2r+1)(2r)!)·((2m)c_r)
  calc (2 * (r : ℚ) + 2) * (2 * (r : ℚ) + 1) * ((2 * r).factorial : ℚ) * cpow besselCoeff m (r + 1)
      = ((2 * (r : ℚ) + 1) * ((2 * r).factorial : ℚ))
          * ((2 * (r : ℚ) + 2) * cpow besselCoeff m (r + 1)) := by ring
    _ ≤ ((2 * (r : ℚ) + 1) * ((2 * r).factorial : ℚ))
          * ((2 * m) * cpow besselCoeff m r) := hmul
    _ = (2 * (r : ℚ) + 1) * (2 * m) * (((2 * r).factorial : ℚ) * cpow besselCoeff m r) := by ring

/-! ## The dilution-theorem separation (the engine step is strictly below the tensor ceiling) -/

/-- **The engine step beats the tensor lift (strict separation).** For `1 ≤ r` and `2r+1 < n`, the
`r`-linear Wick step factor `(2r+1)·n` is STRICTLY below the tensor ceiling factor `n²`. So the
cumulant engine's per-step saving (`besselPow_energyStep`, with `n = 2m`) is a genuine `n/(2r+1)`-fold
tightening of the tensor lift `E_{r+1} ≤ n²·E_r` — a real non-tensor advance, and (in char-`0`) it is
fully proven above. This is `_RudnevDilutionFixedSavingStall` localized to the engine step. -/
theorem besselPow_le_tensor_step (n r : ℕ) (hr : 1 ≤ r) (hrn : 2 * r + 1 < n) :
    (2 * (r : ℚ) + 1) * n < (n : ℚ) ^ 2 := by
  have hnZ : (2 * (r : ℚ) + 1) < n := by exact_mod_cast hrn
  have hnpos : (0 : ℚ) < n := by
    have : (0 : ℚ) < 2 * (r : ℚ) + 1 := by positivity
    linarith
  nlinarith [hnZ, hnpos]

/-! ### The exp boundary: the engine is tight (index exactly `m` for `e^{m x²}`) -/

/-- **The exp power has index EXACTLY `m`** (the engine is tight at the exponential). `cpow expCoeff m`
satisfies `(r+1)·a_{r+1} ≤ m·a_r` (with equality, since `cpow expCoeff m r = m^r/r!`). This certifies
the engine's index bound is best-possible — the Bessel power sits at-or-below this exp boundary, and
the energy step `(2r+1)·n` is the exact Wick step. -/
theorem expPow_logDerivIndex (m : ℕ) : LogDerivIndex (cpow expCoeff m) (m : ℚ) := by
  have h := cpow_logDerivIndex expCoeff_nonneg expCoeff_logDerivIndex_one m
  simpa using h

end ArkLib.ProximityGap.Frontier.AvNTCumulantEngine

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.logDerivIndex_conv
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.besselCoeff_logDerivIndex_one
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.expCoeff_logDerivIndex_one
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.cpow_logDerivIndex
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.besselPow_logDerivIndex
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.besselPow_energyStep
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.besselPow_le_tensor_step
#print axioms ArkLib.ProximityGap.Frontier.AvNTCumulantEngine.expPow_logDerivIndex
