/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# T11 — Spectral min-entropy / level-set count transfer (#444): REDUCES-TO-WALL (F0/F7)

## The candidate (architect G3-T1 / T11)

OBJECT: the spectral value-law of the generalized-Paley eigenvalues `|η_b|`, with the
**level-set count** `N(λ) := #{b ≠ 0 : |η_b| > λ·√n}` and the **spectral min-entropy at scale**
`H_∞^spec(λ) := −log₂(N(λ)/(p−1))`.

HYPOTHESIS (T11): a one-sided sub-Gaussian *level-set decay* — there are `c₀ > 0`, `λ₀` with
`N(λ) ≤ (p−1)·exp(−c₀·λ²)` for `λ₀ ≤ λ ≤ √(2 log m)`, equivalently
`H_∞^spec(λ) ≥ (c₀/log 2)·λ²` (a min-entropy lower bound = "flatness certificate").

CLAIM (T11): the hypothesis ⟹ the prize bound `M(n) = max_{b≠0} |η_b| ≤ √((2/c₀)·n·log m)`.

## Verdict: REDUCES-TO-WALL.  Two independent fences, machine-checked here.

### (1) The forward implication is the STANDARD sub-Gaussian-max union bound — and it is
ALREADY IN THE CODEBASE under a different name.

The architect's own absence-evidence grepped for `min-entropy`/`H_infty` and found 0 hits. But the
codebase states **the very same conditional bridge** as
`ArkLib.ProximityGap.I031SubGaussianMaxBridge.SubGaussianTailBound` /`subgaussian_max_le`
(file `I031SubGaussianMaxBridge.lean`): for a finset `S ⊆ ℝ`,

  `SubGaussianTailBound S C m := ∀ s > 0, #{v ∈ S : s < v} ≤ m·exp(−s²/(2C))`,
  `subgaussian_max_le : SubGaussianTailBound S C m → 1 ≤ m → 0 < C → ∀ v ∈ S, v ≤ √(2C·log m)`.

T11's hypothesis is *literally the same Prop reparametrized*.  Put `s = λ·√n`, `C = n/(2c₀)`,
`m = p−1`.  Then
  `m·exp(−s²/(2C)) = (p−1)·exp(−(λ²n)/(2·n/(2c₀))) = (p−1)·exp(−c₀·λ²)`,
i.e. `N(λ) ≤ m·exp(−s²/(2C))` ⟺ T11's `N(λ) ≤ (p−1)·exp(−c₀λ²)`.  And the conclusion
`v ≤ √(2C·log m) = √(2·(n/(2c₀))·log m) = √((1/c₀)·n·log m)` is T11's prize bound (T11's stated
`√((2/c₀)·n·log m)` carries a stray factor-2 in the sqrt, immaterial to `O(·)`).

So T11 is NOT novel and NOT absent: it is the existing I031 bridge with "sub-Gaussian tail"
renamed "min-entropy level-set decay".  `−log₂(N/(p−1)) ≥ (c₀/log 2)λ²` is the same inequality as
`N ≤ (p−1)·exp(−c₀λ²)` (take `2^{−·}` of both sides).  We re-prove the forward bound below
(`minEntropy_prize_bound`) self-contained, and machine-check the reparametrization identity
(`minEntropyDecay_iff_subGaussianTail`) — the explicit reduction map.

### (2) The HYPOTHESIS is the wall (F0 conservation + F7 Rényi), not a free or weaker input.

The architect argues the level-set count is a "rare-event / tail" object that F0 reserves, hence
not domain-2nd-order arithmetic.  TRUE that `N(λ)` is not the 2nd moment.  But a **sub-Gaussian
upper bound on `N(λ) uniformly in λ` up to `λ = √(2 log m)`** is, by Markov-in-reverse /
Cramér–Chernoff duality, EQUIVALENT to a uniform bound on all the moments/cumulants on that range:
a sub-Gaussian level-set decay with proxy `O(n)` is the Legendre dual of "all moments
`E_r ≤ (2r−1)!!·n^r` up to `r ≈ log m`", which is the in-tree `GaussianEnergyBound G r` —
**exactly the char-p energy transfer that is the open BGK wall** (F1/F7 conjugacy).  This is the
DISPROOF_LOG [I027] finding verbatim: "bounding `L^∞` ABOVE from a count/`L^p` datum requires the
sub-Gaussian flatness that IS the conjecture"; the C29 finding: "a sub-Gaussian tail with proxy
`O(n)` … is exactly the residual already isolated … the open BGK √-cancellation."  The min-entropy
LOWER bound `H_∞^spec(λ) ≥ c·λ²` is precisely the sub-Gaussian variance-proxy `= O(n)` claim that
DISPROOF_LOG C29 HORN B measured to *drift* (`proxy/n = 0.77→0.72`, never locking) at fixed prize
`q`.  So the hypothesis is not weaker than, not sideways to — it is conjugate-equal to — the wall.

CONCLUSION: T11 packages the open content into its hypothesis and proves only the free union-bound
forward step (already landed as `subgaussian_max_le`).  It does not escape; it reduces to the wall
via the explicit reparametrization map proved below.  Fences hit: **F0** (the load-bearing input is
not domain arithmetic — granted — but it is the *conjectural* tail flatness itself, the thing F0's
escape clause names as the open content, NOT a provided certificate), and **F7/F1** (uniform
sub-Gaussian level-set decay = Legendre-dual of the char-p energy bound `GaussianEnergyBound`,
the BGK wall).

This file is axiom-clean.  Both the forward bridge and the reduction identity are proven; NO new
mathematics, NO closure, is claimed.  The point is the machine-checked reduction.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.WfT11

/-! ## 1. T11's hypothesis, stated faithfully -/

/-- **T11's spectral min-entropy / level-set sub-Gaussian decay (the named open input).**
For a finset `S ⊆ ℝ` of magnitudes (the period magnitudes `{|η_b|}`), and the level-set count at
deviation `λ` measured in units of `√n`, i.e. threshold `λ·√n`:
`#{v ∈ S : λ√n < v} ≤ cardP · exp(−c₀·λ²)` for every `λ > 0`.
Here `cardP = p−1` is the number of frequencies (the union-bound count `m`), `n > 0` the subgroup
size, `c₀ > 0` the rate.  Equivalently the spectral min-entropy
`H_∞^spec(λ) = −log₂(N(λ)/cardP) ≥ (c₀/log 2)·λ²`.  This is the architect's hypothesis verbatim. -/
def MinEntropyLevelSetDecay (S : Finset ℝ) (c₀ n cardP : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    ((S.filter (fun v => lam * Real.sqrt n < v)).card : ℝ)
      ≤ cardP * Real.exp (-(c₀ * lam ^ 2))

/-- **The existing in-tree open Prop, re-stated** (matches
`I031SubGaussianMaxBridge.SubGaussianTailBound` byte-for-byte).  Restated here so the reduction is
self-contained / import-light; the real bridge is the named version. -/
def SubGaussianTailBound (S : Finset ℝ) (C m : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ((S.filter (fun v => s < v)).card : ℝ) ≤ m * Real.exp (-(s ^ 2) / (2 * C))

/-! ## 2. THE REDUCTION MAP (machine-checked): T11's hypothesis = the existing open Prop. -/

/-- **The explicit reduction map.** T11's `MinEntropyLevelSetDecay S c₀ n cardP` is *the same
proposition* as the already-in-codebase `SubGaussianTailBound S (n/(2c₀)) cardP`, under the
reparametrization `s = lam·√n`, `C = n/(2c₀)`, `m = cardP`.  Proving this biconditional is the
honest reduction: T11 contributes no new hypothesis, only a renaming of the recognized-open
sub-Gaussian-tail / energy wall (F7/F1).  (Requires `0 < n`, `0 < c₀` for the substitution to be a
bijection on thresholds.) -/
theorem minEntropyDecay_iff_subGaussianTail
    {S : Finset ℝ} {c₀ n cardP : ℝ} (hn : 0 < n) (hc₀ : 0 < c₀) :
    MinEntropyLevelSetDecay S c₀ n cardP ↔ SubGaussianTailBound S (n / (2 * c₀)) cardP := by
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsqrtn_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hC_pos : 0 < n / (2 * c₀) := by positivity
  constructor
  · -- forward: given the min-entropy decay, derive the tail bound at any s>0 via lam = s/√n.
    intro h s hs
    set lam := s / Real.sqrt n with hlam
    have hlam_pos : 0 < lam := by rw [hlam]; positivity
    have hthr : lam * Real.sqrt n = s := by
      rw [hlam]; field_simp
    have key := h lam hlam_pos
    rw [hthr] at key
    -- now match the exponents: c₀·lam² = s²/(2C)  with  C = n/(2c₀)
    have hexp : -(c₀ * lam ^ 2) = -(s ^ 2) / (2 * (n / (2 * c₀))) := by
      rw [hlam]
      have : (s / Real.sqrt n) ^ 2 = s ^ 2 / n := by
        rw [div_pow, hsqrtn_sq]
      rw [this]
      field_simp
    rwa [hexp] at key
  · -- backward: given the tail bound, derive the min-entropy decay at any lam>0 via s = lam·√n.
    intro h lam hlam
    set s := lam * Real.sqrt n with hs
    have hs_pos : 0 < s := by rw [hs]; positivity
    have key := h s hs_pos
    have hexp : -(s ^ 2) / (2 * (n / (2 * c₀))) = -(c₀ * lam ^ 2) := by
      rw [hs, mul_pow, hsqrtn_sq]
      field_simp
    rwa [hexp] at key

/-! ## 3. The forward bridge (the only free / provable part), self-contained.

This is `subgaussian_max_le` re-proven directly for the min-entropy phrasing: a clean contrapositive
"push past `s*`" argument, no `ε`-fudge.  It is the STANDARD `max of m sub-Gaussian values ≤
√(2C log m)` union bound (MIT 18.S997 Ch.1), nothing novel — it is the architect's "provable forward
direction", and it is exactly what the codebase already proves. -/

theorem subgaussian_max_le
    {S : Finset ℝ} {C m : ℝ} (hC : 0 < C) (hm : 1 ≤ m)
    (h : SubGaussianTailBound S C m) :
    ∀ v ∈ S, v ≤ Real.sqrt (2 * C * Real.log m) := by
  intro v hv
  by_contra hlt
  rw [not_le] at hlt
  set sstar := Real.sqrt (2 * C * Real.log m) with hsstar
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have h2C : 0 < 2 * C := by linarith
  have hrad : 0 ≤ 2 * C * Real.log m := by positivity
  have hsstar_nonneg : 0 ≤ sstar := Real.sqrt_nonneg _
  set s := (sstar + v) / 2 with hs
  have hs_lo : sstar < s := by rw [hs]; linarith
  have hs_hi : s < v := by rw [hs]; linarith
  have hs_pos : 0 < s := lt_of_le_of_lt hsstar_nonneg hs_lo
  have hsstar_sq : sstar ^ 2 = 2 * C * Real.log m := by
    rw [hsstar, Real.sq_sqrt hrad]
  have hs_sq_gt : 2 * C * Real.log m < s ^ 2 := by
    rw [← hsstar_sq]
    nlinarith [hsstar_nonneg, hs_lo, sq_nonneg (s - sstar)]
  have hexp_arg : -(s ^ 2) / (2 * C) < -Real.log m := by
    rw [div_lt_iff₀ h2C]
    nlinarith [hs_sq_gt, h2C]
  have hexp_lt : Real.exp (-(s ^ 2) / (2 * C)) < Real.exp (-Real.log m) :=
    Real.exp_lt_exp.mpr hexp_arg
  have hm_pos : 0 < m := lt_of_lt_of_le one_pos hm
  have hexp_neglog : Real.exp (-Real.log m) = m⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hm_pos]
  have hbound : m * Real.exp (-(s ^ 2) / (2 * C)) < 1 := by
    have hh : m * Real.exp (-(s ^ 2) / (2 * C)) < m * Real.exp (-Real.log m) :=
      mul_lt_mul_of_pos_left hexp_lt hm_pos
    rw [hexp_neglog, mul_inv_cancel₀ (ne_of_gt hm_pos)] at hh
    exact hh
  have htail := h s hs_pos
  have hcard_lt : ((S.filter (fun w => s < w)).card : ℝ) < 1 := lt_of_le_of_lt htail hbound
  have hv_mem : v ∈ S.filter (fun w => s < w) := by
    rw [Finset.mem_filter]; exact ⟨hv, hs_hi⟩
  have hcard_pos : 1 ≤ (S.filter (fun w => s < w)).card := Finset.card_pos.mpr ⟨v, hv_mem⟩
  have hc1 : (1 : ℝ) ≤ ((S.filter (fun w => s < w)).card : ℝ) := by exact_mod_cast hcard_pos
  linarith

/-- **T11's forward implication, in T11's own min-entropy language (PROVEN, axiom-clean).**
From the min-entropy level-set decay (`0 < c₀`, `0 < n`, `1 ≤ cardP`), every magnitude `v ∈ S`
satisfies `v ≤ √((1/c₀)·n·log cardP)` — the prize bound (up to the immaterial factor-2 noted in
the header).  Proof = reduce to the existing `SubGaussianTailBound` via the reduction map, then
apply the standard sub-Gaussian-max bridge.  This is the architect's "provable forward step"; it
is FREE and ALREADY IN THE CODEBASE.  The CONTENT lives entirely in the hypothesis. -/
theorem minEntropy_prize_bound
    {S : Finset ℝ} {c₀ n cardP : ℝ} (hn : 0 < n) (hc₀ : 0 < c₀) (hcardP : 1 ≤ cardP)
    (h : MinEntropyLevelSetDecay S c₀ n cardP) :
    ∀ v ∈ S, v ≤ Real.sqrt (2 * (n / (2 * c₀)) * Real.log cardP) := by
  have hC_pos : 0 < n / (2 * c₀) := by positivity
  exact subgaussian_max_le hC_pos hcardP
    ((minEntropyDecay_iff_subGaussianTail hn hc₀).mp h)

/-- Cosmetic restatement showing `2·(n/(2c₀)) = n/c₀`, so the prize bound reads
`v ≤ √((n/c₀)·log cardP) = √((1/c₀)·n·log(p−1)) = O(√(n·log(p/n)))` at `cardP = p−1`, `m = (p−1)/n`,
`log(p−1) ≍ log(p/n)` at `β = 4` (since `log p ≍ 4 log n`, `log m ≍ 3 log n`). -/
theorem minEntropy_prize_bound_clean
    {S : Finset ℝ} {c₀ n cardP : ℝ} (hn : 0 < n) (hc₀ : 0 < c₀) (hcardP : 1 ≤ cardP)
    (h : MinEntropyLevelSetDecay S c₀ n cardP) :
    ∀ v ∈ S, v ≤ Real.sqrt ((n / c₀) * Real.log cardP) := by
  intro v hv
  have := minEntropy_prize_bound hn hc₀ hcardP h v hv
  have hc₀' : c₀ ≠ 0 := ne_of_gt hc₀
  have hcoef : 2 * (n / (2 * c₀)) = n / c₀ := by field_simp
  rw [hcoef] at this
  exact this

end ArkLib.ProximityGap.Frontier.WfT11

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WfT11.minEntropyDecay_iff_subGaussianTail
#print axioms ArkLib.ProximityGap.Frontier.WfT11.subgaussian_max_le
#print axioms ArkLib.ProximityGap.Frontier.WfT11.minEntropy_prize_bound
#print axioms ArkLib.ProximityGap.Frontier.WfT11.minEntropy_prize_bound_clean
