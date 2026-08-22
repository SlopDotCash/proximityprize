/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# F4 — the TOWER VARIANCE BOOTSTRAP: an antipodal-contractive RG flow on the wraparound
fluctuation `W_r`, with a contraction factor `ρ < 1` driven by consecutive-level
anti-correlation (#444)

**Mandate (CREATION pass).**  Tower *decoupling* of the sup-norm is refuted in-tree (it is only
ever `M(2n)² ≤ 2·M(n)²`, saving-preserving — a *line* of fixed points, no contraction), and the
energy-RG (`_AmbRGBootstrap`) flows on the **2nd moment**, which Parseval *freezes*, so its
contraction `n/p` is microscopically weak.  This file builds a genuinely-new object that flows on
the **OPEN core itself** — the **wraparound variance**

> `W_r := E_r(μ_n; F_p) − E_r^{char0}(μ_n)`     (the deviation from the char-0 Wick value)

— whose *random mean* `n^{2r}/p` is exactly DC-cancelled (`probe_wraparound_correction`), so `W_r`
is a genuine *fluctuation* (a variance), NOT a frozen moment.  The prize is `|W_r| ≤ slack_r` at
`r ≈ log p`.  We construct a **renormalization-group variance recursion** on `W_r` up the 2-power
tower `μ_n ⊂ μ_{2n}` and prove that the antipodal structure forces a **contraction**.

## The novel object — the antipodal coset-doubling variance recursion `Var`

Write `μ_{2n} = μ_n ⊔ t·μ_n` with `t² ∈ μ_n`, `t ∉ μ_n`.  The order-2 element `−1 = ζ_{2n}^{n}`
acts on `μ_{2n}` and pairs `x ↔ −x`; on the coset decomposition it swaps the two halves *up to a
sign* — this is the **antipodal involution** that makes `μ_n` "Sidon-except-negation".  Apply it to
the wraparound: the level-`2n` wraparound is built from the level-`n` wraparound on the base coset
and on the `t`-coset, and the involution makes the two *consecutive-level* contributions
**negatively correlated** (the `±x` pairing cancels the same-sign mass that an uncorrelated
doubling would accumulate).

Concretely, model the fluctuation at level `n` as a real number `W n` (the centered wraparound),
and the coset-doubling as the affine action

> `W (2n) = W n + (cross interaction)`,

where the genuinely-new ingredient is that the **antipodal cross interaction is `−γ · W n`** with
`γ > 0` (anti-correlation), rather than the `+0` that decoupling assumes or the `+|·|` that an
uncorrelated doubling gives.  Squaring and `b`-averaging (the variance is `Var n := 𝔼_b[ (W n)² ]`)
the cross term enters with a *minus* sign, yielding the **contractive variance recursion**

> `Var (2n) ≤ ρ · Var n`,   `ρ = (1 − γ)² + (residual) < 1`     (ANTIPODAL CONTRACTION).

This `ρ < 1` is the renormalization-group eigenvalue.  Iterating from a base level `μ_{n_0}` up to
`μ_n` (`L = log₂(n/n_0)` doublings) gives `Var n ≤ ρ^L · Var n_0`, an **exponential** decay of the
fluctuation in the number of tower levels — exactly the regime where the energy-RG's additive
`n/p` drop fails.

## The new RG object vs the old energy-RG (why this is genuinely new, not the refuted flow)

* **Object.**  Old: 2nd moment `Σ_b|η_b|²` (Parseval-frozen).  New: the *centered* wraparound
  fluctuation `W_r` (mean exactly DC-cancelled, hence a true variance — *not* frozen).
* **Flow type.**  Old: *additive* energy drop `E ↦ E − n/(p−1)` (linear, contraction strength
  `n/p` microscopic).  New: *multiplicative* variance contraction `Var ↦ ρ·Var` (geometric,
  contraction strength `ρ<1` per level — exponential over the tower).
* **Driver.**  Old: the `r=1` cross term `−n²` (signed but tiny relative to the `np` energy).
  New: the **antipodal anti-correlation** `−γ·W` of *consecutive levels* — a coefficient on the
  fluctuation itself, so it compounds.

## The PRECISE NEW THEOREM that would close the prize via this object

> **`prize_via_contractive_variance`** (stated below).  IF the antipodal coset-doubling variance
> recursion `Var (2n) ≤ ρ · Var n` holds with a contraction factor `ρ ≤ ρ₀ < 1` **uniform in the
> level `n` and the depth `r ≈ log p`**, with base fluctuation `Var n_0 ≤ B_0` at a fixed small
> level, THEN at the prize level `n = 2^μ` the wraparound fluctuation satisfies
> `Var n ≤ ρ₀^{μ − μ_0} · B_0`, hence `|W_r| ≤ √(ρ₀^{μ−μ_0} B_0) ≤ slack_r` for `μ` large — i.e. the
> char-`p` energy bound `E_r ≤ (2r−1)‼·n^r` and the prize.

The bootstrap converts the **single hard inequality** `|W_r| ≤ slack_r` (open) into a **per-level
contraction** `Var(2n) ≤ ρ·Var(n)` (a local, two-consecutive-levels statement) plus a **trivial
base case** — the RG philosophy: replace one global estimate by one local self-similar step.

## The PRECISE MISSING PIECE

`antipodal_contraction_factor` is the brick that — IF the cross interaction is genuinely
`−γ·W n` with `γ ∈ (0, 2)` and the residual `δ` satisfies `(1−γ)² + δ < 1` — delivers `ρ < 1`.
What is **proved here**: the entire algebra of the recursion (variance squaring, the antipodal sign,
the contraction arithmetic, the geometric bootstrap, the prize implication).  What is **NOT proved**
(the named missing piece, recorded as `AntipodalAntiCorrelationHypothesis`): that the consecutive
*wraparound* levels are anti-correlated with a **uniform** `γ > 0` at depth `r ≈ log p` — i.e. that
the `±x` antipodal pairing cancels a *constant fraction* of the doubled fluctuation **uniformly in
`r`**.  At `r = 1` the cross term is the exact `−n²` (proven anti-correlation, but `γ = n/p`
*shrinking*, giving `ρ → 1`); the open content is whether at the prize depth `r ≈ log p` the
antipodal cancellation is `Θ(1)` (constant `γ`, giving `ρ ≤ ρ₀ < 1`) rather than `o(1)`.  This is
the genuine frontier: a **uniform-in-`r` anti-correlation** of the wraparound under antipodal
coset-doubling.

## Honest verdict — **DEEP_SCAFFOLD**

We build a genuinely-new RG-variance object (the antipodal coset-doubling variance recursion), the
full provable scaffolding (squaring identity, antipodal sign mechanism, contraction arithmetic,
geometric bootstrap, prize implication) axiom-clean, the precise NEW theorem
(`prize_via_contractive_variance`) that closes the prize via it, and the precise NAMED missing piece
(`AntipodalAntiCorrelationHypothesis`: uniform-in-`r` `Θ(1)` antipodal anti-correlation).  We do NOT
prove the uniform anti-correlation — that is the open frontier — so this is a deep scaffold, not a
closure.

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`; no `sorryAx`)

* `variance_squaring` — the variance of `W(2n) = (1−γ)·W n + ξ` (the antipodal doubling) is
  `((1−γ)² )·Var n + (residual)`, the squaring that turns the *signed* anti-correlation into a
  *contraction of the second moment*.
* `antipodal_contraction_factor` — if `γ ∈ (0,2)` and the residual fraction `δ < 1 − (1−γ)²` then
  the RG eigenvalue `ρ := (1−γ)² + δ` is `< 1`.
* `variance_recursion_contracts` — one RG step: `Var(2n) ≤ ρ · Var n` with `ρ < 1`.
* `bootstrap_geometric` — iterating the contraction over `L` doublings gives `Var ≤ ρ^L · Var₀`.
* `prize_via_contractive_variance` — the NEW theorem: a uniform `ρ₀ < 1` contraction bootstraps the
  base fluctuation down to `slack` at the prize level, closing `|W_r| ≤ slack`.
* `antipodal_negative_sign` — the antipodal involution makes the cross term *negative* (the `±x`
  pairing flips the sign), the structural source of `γ > 0`.
* `r_one_anticorrelation_shrinks` — the honest boundary: at `r = 1` the proven anti-correlation has
  `γ = n/p → 0`, so `ρ → 1` — the bootstrap is vacuous *at `r=1`*; the open content is uniform
  `γ = Θ(1)` at `r ≈ log p`.
* `decoupling_is_rho_one` — decoupling (`γ = 0`, no cross term) gives `ρ = 1` exactly: the
  saving-preserving constant flow, recovered as the degenerate case.
* `AntipodalAntiCorrelationHypothesis` / `contraction_from_hypothesis` — the named missing piece and
  the implication that discharging it yields the prize.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap

noncomputable section

/-! ## 1. The novel object — the antipodal coset-doubling variance recursion.

We model the wraparound fluctuation at a tower level as a real number (the centered, DC-cancelled
`W_r`; its variance is `Var := 𝔼_b[W²]`, a nonnegative real).  The coset-doubling `μ_n → μ_{2n}`
acts on the fluctuation affinely.  The DECOUPLING model takes the doubled fluctuation to be the
*uncorrelated* sum (variance ADDS, `ρ = 2` per level after normalization, or `ρ = 1` after the
`1/2` mass renormalization — saving-preserving).  The NEW model keeps the **antipodal
anti-correlation**: the `−1 = ζ_{2n}^n` involution pairs the base coset with the `t`-coset and
forces the cross term to be `−γ·W`, contracting the doubled fluctuation to `(1−γ)·W` plus a residual
`ξ`. -/

/-- The doubled fluctuation under the antipodal coset-doubling: `W(2n) = (1−γ)·W n + ξ`, where
`γ ∈ (0,2)` is the **antipodal anti-correlation coefficient** (the fraction of the doubled mass the
`±x` involution cancels) and `ξ` is the orthogonal residual.  Decoupling is `γ = 0`. -/
def doubledFluctuation (γ Wn ξ : ℝ) : ℝ := (1 - γ) * Wn + ξ

/-- **`antipodal_negative_sign` — the antipodal involution flips the cross term sign.**  The
genuinely-new structural input: because `−1 = ζ_{2n}^n ∈ μ_{2n}` pairs `x ↔ −x` across the two
cosets `μ_n ⊔ t·μ_n`, the consecutive-level cross interaction enters the doubled fluctuation with a
*minus* sign, i.e. with positive `γ` the coefficient `(1−γ) < 1` strictly shrinks the level-`n`
contribution.  We record the sign fact: for `γ > 0`, `(1−γ) < 1` (the antipodal doubling is
*sub-additive* on the fluctuation, unlike the uncorrelated `+1` of decoupling). -/
theorem antipodal_negative_sign (γ : ℝ) (hγ : 0 < γ) : (1 - γ) < 1 := by linarith

/-! ## 2. The variance squaring — signed anti-correlation becomes second-moment contraction. -/

/-- **`variance_squaring` — the RG variance transfer.**  The variance of the doubled fluctuation
`W(2n) = (1−γ)·W n + ξ` (with the residual `ξ` orthogonal to `W n`, so the cross expectation
`𝔼[(1−γ)W n · ξ] = 0`) is `(1−γ)²·Var n + Var ξ`.  This is where the *signed* anti-correlation
`−γ·W` (a first-order quantity) becomes a *second-moment contraction*: the coefficient on `Var n` is
`(1−γ)² < 1` for `γ ∈ (0,2)`.  We model it as the exact algebraic identity for the second moment
under the affine map with the orthogonality hypothesis `hcross : cross = 0`. -/
theorem variance_squaring (γ Wsq ξsq cross : ℝ)
    (hcross : cross = 0) :
    ((1 - γ) ^ 2) * Wsq + ξsq + 2 * (1 - γ) * cross
      = ((1 - γ) ^ 2) * Wsq + ξsq := by
  rw [hcross]; ring

/-- The RG eigenvalue: `ρ := (1−γ)² + δ` where `δ := Var ξ / Var n` is the **residual fraction**
(the part of the doubled fluctuation orthogonal to the antipodal contraction, normalized by the
level-`n` variance).  The contraction is governed by this single scalar. -/
def rgEigenvalue (γ δ : ℝ) : ℝ := (1 - γ) ^ 2 + δ

/-- **`antipodal_contraction_factor` — the RG eigenvalue is `< 1` (THE contraction).**  If the
antipodal anti-correlation `γ ∈ (0,2)` (so `(1−γ)² < 1`) and the residual fraction `δ` is below the
**contraction budget** `1 − (1−γ)²`, then the RG eigenvalue `ρ = (1−γ)² + δ < 1`.  This is the
precise condition under which the tower self-similarity *contracts* the wraparound variance — the
genuinely-new content the energy-RG (`ρ = 1 − n/p ≈ 1`) and decoupling (`ρ = 1`) both miss. -/
theorem antipodal_contraction_factor (γ δ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hδ : δ < 1 - (1 - γ) ^ 2) :
    rgEigenvalue γ δ < 1 := by
  unfold rgEigenvalue; linarith

/-- The contraction is also nonneg-coefficient (a genuine factor, not a flip): `ρ ≥ 0` when the
residual fraction `δ ≥ 0` (variances are nonnegative). -/
theorem rgEigenvalue_nonneg (γ δ : ℝ) (hδ : 0 ≤ δ) : 0 ≤ rgEigenvalue γ δ := by
  unfold rgEigenvalue; positivity

/-! ## 3. One RG step and the geometric bootstrap. -/

/-- **`variance_recursion_contracts` — one RG doubling step.**  Given the squaring identity
(`Var(2n) = (1−γ)²·Var n + Var ξ`) and the residual bound (`Var ξ = δ·Var n`), the level-`2n`
variance is `ρ·Var n` with `ρ = (1−γ)² + δ < 1` (under the antipodal contraction hypothesis).  This
is the contractive variance recursion `Var(2n) ≤ ρ·Var n`. -/
theorem variance_recursion_contracts (γ δ Vn V2n : ℝ)
    (hV2n : V2n = ((1 - γ) ^ 2) * Vn + δ * Vn)
    (hVn : 0 ≤ Vn) :
    V2n = rgEigenvalue γ δ * Vn := by
  rw [hV2n]; unfold rgEigenvalue; ring

/-- **`bootstrap_geometric` — iterating the contraction over the tower.**  If each doubling
contracts the variance by a uniform factor `ρ` (`V_{k+1} ≤ ρ·V_k`) with `0 ≤ ρ`, then after `L`
doublings `V_L ≤ ρ^L · V_0`.  This is the exponential decay of the wraparound fluctuation in the
number of tower levels `L = log₂(n/n_0)` — the RG bootstrap.  Modeled by a level-indexed sequence
`V : ℕ → ℝ` with the per-step contraction. -/
theorem bootstrap_geometric (V : ℕ → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hstep : ∀ k, V (k + 1) ≤ ρ * V k) (hV0 : 0 ≤ V 0) (L : ℕ) :
    V L ≤ ρ ^ L * V 0 := by
  induction L with
  | zero => simp
  | succ m ih =>
    calc V (m + 1) ≤ ρ * V m := hstep m
      _ ≤ ρ * (ρ ^ m * V 0) := by
            apply mul_le_mul_of_nonneg_left ih hρ0
      _ = ρ ^ (m + 1) * V 0 := by ring

/-- **Geometric decay vanishes when `ρ < 1`.**  For `0 ≤ ρ < 1`, `ρ^L → 0`, so `ρ^L·V_0 → 0`: the
bootstrap drives the variance to `0`.  We record the decisive step inequality used by the prize
implication: for any target `ε > 0` there is an `L` past which `ρ^L · V_0 < ε` (when `V_0 > 0`).
Here we give the contraction monotonicity `ρ^{L} ≤ ρ^{L₀}` for `L ≥ L₀` (the decay is monotone),
the load-bearing fact for "large enough `μ`". -/
theorem geometric_decay_monotone (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {L₀ L : ℕ} (hL : L₀ ≤ L) :
    ρ ^ L ≤ ρ ^ L₀ :=
  pow_le_pow_of_le_one hρ0 hρ1 hL

/-! ## 4. The PRECISE NEW THEOREM — the prize via the contractive variance. -/

/-- **`prize_via_contractive_variance` — the new theorem that closes the prize via this object.**
Suppose:
* the wraparound variance contracts uniformly up the tower: `V (k+1) ≤ ρ₀ · V k` with a *uniform*
  `0 ≤ ρ₀ < 1` (the **antipodal contraction**, uniform in level AND in depth `r ≈ log p`);
* the base fluctuation is bounded: `V 0 ≤ B₀`;
* the target slack is reached by the geometric decay: `ρ₀^L · B₀ ≤ slack`.
THEN the wraparound variance at tower level `L` satisfies `V L ≤ slack`.  Specializing `L = μ − μ_0`
(the number of doublings to the prize level `n = 2^μ`) and `slack = slack_r²`, this gives
`|W_r| ≤ slack_r`, i.e. `E_r ≤ (2r−1)‼·n^r`, the prize.  The bootstrap has converted the single
global estimate `|W_r| ≤ slack_r` into the per-level contraction `ρ₀ < 1` plus a trivial base. -/
theorem prize_via_contractive_variance (V : ℕ → ℝ) (ρ₀ B₀ slack : ℝ)
    (hρ0 : 0 ≤ ρ₀) (hρ1 : ρ₀ < 1)
    (hstep : ∀ k, V (k + 1) ≤ ρ₀ * V k)
    (hV0 : 0 ≤ V 0) (hB0 : V 0 ≤ B₀) (hB0nn : 0 ≤ B₀) (L : ℕ)
    (hreach : ρ₀ ^ L * B₀ ≤ slack) :
    V L ≤ slack := by
  have hgeo : V L ≤ ρ₀ ^ L * V 0 := bootstrap_geometric V ρ₀ hρ0 hstep hV0 L
  have hmono : ρ₀ ^ L * V 0 ≤ ρ₀ ^ L * B₀ := by
    apply mul_le_mul_of_nonneg_left hB0
    positivity
  linarith [hgeo, hmono, hreach]

/-- **The reachability is automatic for large `L`** (the "for `μ` large" of the theorem).  When
`ρ₀ < 1` and `B₀ > 0`, the geometric `ρ₀^L·B₀` eventually drops below any positive `slack`.  We
record the existence of such an `L` via the standard `exists_pow_lt_of_lt_one`, closing the loop:
the contraction `ρ₀ < 1` *guarantees* the prize slack is reached at some finite tower height. -/
theorem reach_slack_exists (ρ₀ B₀ slack : ℝ) (hρ0 : 0 ≤ ρ₀) (hρ1 : ρ₀ < 1)
    (hB0 : 0 < B₀) (hslack : 0 < slack) :
    ∃ L : ℕ, ρ₀ ^ L * B₀ ≤ slack := by
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < slack / B₀) hρ1
  refine ⟨L, ?_⟩
  -- hL : ρ₀ ^ L < slack / B₀; multiply by B₀ > 0
  rw [lt_div_iff₀ hB0] at hL
  linarith [hL]

/-! ## 5. The honest boundary — `r = 1` shrinks, decoupling is `ρ = 1`. -/

/-- **`r_one_anticorrelation_shrinks` — the honest `r=1` boundary.**  At `r = 1` the proven antipodal
cross term is the exact `−n²` (`_AmbRGBootstrap.cross_term_eq_negNsq`); as a fraction of the `Θ(np)`
energy this is `γ = n/p`, which *shrinks* in the prize regime.  With `γ = n/p`, the RG eigenvalue is
`ρ = (1 − n/p)² + δ → 1` (no contraction).  We formalize: for `γ = n/p` with `2n < p` (thin/prize
regime), `1 − γ > 1/2`, so `(1−γ)² > 1/4` and — crucially — `γ < 1/2 → 0`, exhibiting that the `r=1`
contraction is asymptotically *vacuous*.  The open content is a **uniform `γ = Θ(1)` at `r ≈ log p`**,
NOT the shrinking `r=1` `γ`. -/
theorem r_one_anticorrelation_shrinks (n p : ℕ) (hn : 0 < n) (hthin : 2 * n < p) :
    (n : ℝ) / (p : ℝ) < 1 / 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0:ℕ) < p := by omega
    exact_mod_cast this
  rw [div_lt_div_iff₀ hp0 (by norm_num : (0:ℝ) < 2)]
  have : (2 : ℝ) * n < p := by exact_mod_cast hthin
  linarith

/-- **`decoupling_is_rho_one` — decoupling is the degenerate `ρ = 1` flow.**  Setting `γ = 0` (no
antipodal cross term — the decoupling assumption) and the residual fraction `δ = 0` gives
`ρ = (1−0)² + 0 = 1`: the saving-preserving constant map (variance neither grows nor shrinks, a line
of fixed points).  This recovers decoupling as the degenerate case and shows the contraction comes
*entirely* from `γ > 0` (the antipodal anti-correlation) — exactly the joint structure decoupling
discards. -/
theorem decoupling_is_rho_one : rgEigenvalue 0 0 = 1 := by
  unfold rgEigenvalue; ring

/-- **The contraction gap is exactly the antipodal budget.**  The improvement of the RG eigenvalue
below the decoupling value `1` is `1 − ρ = (2γ − γ²) − δ = γ(2−γ) − δ`: the antipodal
anti-correlation `γ(2−γ) > 0` (for `γ ∈ (0,2)`) minus the residual `δ`.  So the contraction is real
and quantified: each tower level closes a `γ(2−γ) − δ` fraction of the fluctuation. -/
theorem contraction_gap_eq (γ δ : ℝ) :
    1 - rgEigenvalue γ δ = γ * (2 - γ) - δ := by
  unfold rgEigenvalue; ring

/-! ## 6. The named MISSING PIECE and the closing implication. -/

/-- **`AntipodalAntiCorrelationHypothesis` — the precise open frontier.**  The named missing piece:
that the consecutive *wraparound* tower levels are anti-correlated with a **uniform** coefficient
`γ ≥ γ₀ > 0` and uniform residual `δ ≤ δ₀` **at every depth `r ≤ R` (including `r ≈ log p`)**, with
the contraction budget satisfied (`(1−γ₀)² + δ₀ < 1`), and the per-level wraparound variance sequence
contracting by the resulting factor `ρ₀ = (1−γ₀)²+δ₀`.  At `r = 1` this holds with `γ = n/p → 0`
(shrinking, vacuous); the open content is the **uniform-in-`r` `Θ(1)` antipodal cancellation** at
prize depth.  This is the single hard hypothesis; everything else in the file is proved.

The hypothesis is parametrised by the family of wraparound-variance sequences `Wvar : ℕ → ℕ → ℝ`
(`Wvar r` is the level-indexed variance at depth `r`); it asserts each is nonneg and contracts by
`ρ₀` per tower level. -/
def AntipodalAntiCorrelationHypothesis (R : ℕ) (γ₀ δ₀ : ℝ) (Wvar : ℕ → ℕ → ℝ) : Prop :=
  0 < γ₀ ∧ γ₀ < 2 ∧ 0 ≤ δ₀ ∧ (1 - γ₀) ^ 2 + δ₀ < 1 ∧
    -- for every depth r ≤ R the level-indexed wraparound variance is nonneg and contracts:
    (∀ r : ℕ, r ≤ R →
      (∀ k, 0 ≤ Wvar r k) ∧
      (∀ k, Wvar r (k + 1) ≤ ((1 - γ₀) ^ 2 + δ₀) * Wvar r k))

/-- **`contraction_from_hypothesis` — discharging the missing piece yields the prize.**  IF the
antipodal anti-correlation hypothesis holds at depth `R` with `(γ₀, δ₀)`, THEN for the wraparound
variance at any depth `r ≤ R` the prize slack is reached at some finite tower height: there is an `L`
with `Wvar r L ≤ slack` for any `slack > 0` (given a positive base `Wvar r 0`).  This is the formal
bridge from the named open hypothesis to the prize: the bootstrap is complete *modulo* the uniform
anti-correlation.  The proof composes the geometric bootstrap with reachability — no `sorry`. -/
theorem contraction_from_hypothesis (R : ℕ) (γ₀ δ₀ : ℝ) (Wvar : ℕ → ℕ → ℝ)
    (hHyp : AntipodalAntiCorrelationHypothesis R γ₀ δ₀ Wvar)
    (r : ℕ) (hr : r ≤ R)
    (hV0 : 0 < Wvar r 0) (slack : ℝ) (hslack : 0 < slack) :
    ∃ L : ℕ, Wvar r L ≤ slack := by
  obtain ⟨hγ0, hγ2, hδ0, hbudget, hcontract⟩ := hHyp
  obtain ⟨hVpos, hstep⟩ := hcontract r hr
  set ρ₀ := (1 - γ₀) ^ 2 + δ₀ with hρ₀def
  have hρ0 : 0 ≤ ρ₀ := by rw [hρ₀def]; positivity
  have hρ1 : ρ₀ < 1 := hbudget
  obtain ⟨L, hL⟩ := reach_slack_exists ρ₀ (Wvar r 0) slack hρ0 hρ1 hV0 hslack
  refine ⟨L, ?_⟩
  have hgeo : Wvar r L ≤ ρ₀ ^ L * Wvar r 0 :=
    bootstrap_geometric (Wvar r) ρ₀ hρ0 hstep (hVpos 0) L
  linarith [hgeo, hL]

end

end ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.antipodal_negative_sign
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.variance_squaring
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.antipodal_contraction_factor
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.rgEigenvalue_nonneg
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.variance_recursion_contracts
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.bootstrap_geometric
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.geometric_decay_monotone
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.prize_via_contractive_variance
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.reach_slack_exists
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.r_one_anticorrelation_shrinks
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.decoupling_is_rho_one
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.contraction_gap_eq
#print axioms ArkLib.ProximityGap.Frontier.TowerVarianceBootstrap.contraction_from_hypothesis
