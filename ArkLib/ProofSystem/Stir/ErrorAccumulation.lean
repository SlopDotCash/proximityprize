/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

FRI/STIR soundness-error ACCOUNTING for Issue #24: elementary `ℝ≥0` / `ℝ` arithmetic about
sums of per-round error budgets.

  STATUS: built as part of the downstream `ArkLibExtensions` library (it is imported by the
  STIR checking-verifier modules, e.g. `Stir/CheckingVerifier.lean`). No `sorry` / `admit` /
  `axiom` / `native_decide` is used.

  SCOPE — what this file does and does NOT do. Every theorem here is a statement about
  abstract per-round numbers `e i : ℝ≥0`. Nothing in this file mentions a code, a received
  word, a random experiment, or a protocol, so nothing here proves (or isolates) any soundness
  fact. In particular the predicate `PerRoundProximityGap e B` of §4 is only the
  BUDGET-IDENTIFICATION equation `∀ i, e i = B i`: it says the accounting uses the numbers `B i`
  as its per-round budgets. It does NOT state the BCIKS20 correlated-agreement /
  proximity-gap theorem, and discharging it (e.g. by `PerRoundProximityGap.refl`) says nothing
  about whether `B i` bounds any protocol probability. The genuine per-round soundness content
  lives elsewhere and must be carried separately: the BCIKS20 statements
  `Combine.combine_theorem` / `STIR.proximity_gap` (consuming
  `ProximityGap.StrictCoeffPolysResidual`), and, for the declared STIR wire model, the
  round-by-round soundness route in `Stir/SubUnitRbr.lean` (see `docs/wiki/stir-issue-301.md`).

  WHAT THIS FILE ESTABLISHES:

    (A) The FRI/STIR total soundness budget shape
        `totalBudget = (∑ fold-round errors) + (∑ query-round errors)`
        (mirrors `Fri.Spec.totalError`, `Fri/Spec/Soundness.lean`).

    (B) LINEAR ACCUMULATION: if every per-round error is ≤ a uniform ε, the fold-phase
        budget is ≤ (#fold rounds) · ε; likewise for the query phase; hence the whole budget
        is ≤ (k + (k+1)) · ε. Reduced to `Finset.sum_le_card_nsmul`.

    (C) MONOTONE CONTRACTION: if the per-round proximity PARAMETER is nonincreasing and the
        per-round error is a monotone function of it, then each round's error is ≤ the first
        round's, giving the same linear bound with ε = round-0 error.

    (D) GEOMETRIC PREFIX BOUND: if the per-round errors are bounded by `e₀ · qⁱ` with
        `q < 1` (an explicit hypothesis `hbound`/`hgeo`; it is not derived here), every
        FINITE prefix sum is ≤ the closed form `e₀/(1-q)`, uniformly in the prefix length.
        No infinite-sum (`tsum`) theorem is stated in this file.

    (E) BUDGET-IDENTIFICATION ADAPTERS: `foldBudget_le_of_keystone` and
        `prefixBudget_le_of_keystone_geom` rewrite `e i = B i` before applying (B)/(D). They
        add no probabilistic content.

  Mathlib lemmas used: `Finset.sum_le_card_nsmul`, `Finset.sum_le_sum`, `Finset.mul_sum`,
  `geom_sum_eq`, `div_le_div_of_nonneg_right`, `NNReal.coe_le_coe`, `NNReal.coe_sub`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open scoped NNReal BigOperators
open Finset

namespace ArkLib.ProofSystem.Stir.ErrorAccumulation

/-! ## §0. The accounting model (mirror of `Fri.Spec`)

We work with an abstract per-round error function `e : Fin n → ℝ≥0`. In the real tree:
  * the FRI fold-phase errors are `Fri.Spec.roundError δ : Fin k → ℝ≥0`
    (`Fri/Spec/Soundness.lean:44`), each definitionally
    `errorBound δ degBoundᵢ domᵢ` — the BCIKS20 per-round bound;
  * the query-phase errors are `Fri.Spec.queryRoundError : Fin (k+1) → ℝ≥0`
    (`:54`), each `(Dᵢ / Nᵢ)^l`;
  * `Fri.Spec.totalError δ = (∑ i : Fin k, roundError δ i) + (∑ i : Fin (k+1), queryRoundError i)`
    (`:70`).

We reproduce `totalError`'s additive shape and prove the accumulation facts about it. -/

/-- Abstract fold-phase budget: sum of `k` per-round proximity-gap errors.
    Mirror of `∑ i : Fin k, Fri.Spec.roundError δ i`. -/
def foldBudget {k : ℕ} (e : Fin k → ℝ≥0) : ℝ≥0 := ∑ i, e i

/-- Abstract query-phase budget: sum of `k+1` per-round query errors.
    Mirror of `Fri.Spec.queryError = ∑ i : Fin (k+1), queryRoundError i`. -/
def queryBudget {k : ℕ} (q : Fin (k + 1) → ℝ≥0) : ℝ≥0 := ∑ i, q i

/-- Abstract total soundness budget. Mirror of `Fri.Spec.totalError`. -/
def totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) : ℝ≥0 :=
  foldBudget e + queryBudget q

/-- Sanity: the query phase is a projection of the additive total — the analogue of the
    in-tree `Fri.Spec.queryError_le_totalError` (`Fri/Spec/Soundness.lean:77`).
    PROVEN: `le_add_self` on `ℝ≥0` (`a ≤ b + a`). -/
theorem queryBudget_le_totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) :
    queryBudget q ≤ totalBudget e q := by
  unfold totalBudget
  exact le_add_self

/-- Symmetric projection for the fold phase. PROVEN: `le_self_add` (`a ≤ a + b`). -/
theorem foldBudget_le_totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) :
    foldBudget e ≤ totalBudget e q := by
  unfold totalBudget
  exact le_self_add

/-! ## §1. Linear accumulation (the core "errors accumulate over rounds" lemma)

This is the elementary content of "the soundness error accumulates across rounds":
a sum of per-round errors, each bounded by a uniform `ε`, is bounded by (#rounds)·ε.
We reduce it to `Finset.sum_le_card_nsmul`. -/

/-- **Linear accumulation over a `Fin n` index.**
    If `e i ≤ ε` for every round `i`, then `∑ i, e i ≤ n • ε = n * ε`.
    PROVEN via `Finset.sum_le_card_nsmul` (confirmed sig, see header) + `Finset.card_fin`.

    This is the per-phase form of "the proximity error accumulates linearly". -/
theorem sum_le_nsmul_of_forall_le {n : ℕ} (e : Fin n → ℝ≥0) (ε : ℝ≥0)
    (h : ∀ i, e i ≤ ε) : (∑ i, e i) ≤ (n : ℝ≥0) * ε := by
  have hcard :
      (∑ i, e i) ≤ (Finset.univ : Finset (Fin n)).card • ε :=
    Finset.sum_le_card_nsmul Finset.univ e ε (fun i _ => h i)
  -- `card_univ : (univ : Finset (Fin n)).card = Fintype.card (Fin n)`,
  -- `Fintype.card_fin : Fintype.card (Fin n) = n`, `nsmul_eq_mul : n • ε = ↑n * ε`.
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hcard

/-- **Fold-phase accumulation.** If each fold-round proximity-gap error is ≤ `ε`,
    the fold budget is ≤ `k * ε`. PROVEN (direct from `sum_le_nsmul_of_forall_le`). -/
theorem foldBudget_le {k : ℕ} (e : Fin k → ℝ≥0) (ε : ℝ≥0) (h : ∀ i, e i ≤ ε) :
    foldBudget e ≤ (k : ℝ≥0) * ε := by
  unfold foldBudget; exact sum_le_nsmul_of_forall_le e ε h

/-- **Query-phase accumulation.** If each query-round error is ≤ `ε`,
    the query budget is ≤ `(k+1) * ε`. PROVEN. -/
theorem queryBudget_le {k : ℕ} (q : Fin (k + 1) → ℝ≥0) (ε : ℝ≥0) (h : ∀ i, q i ≤ ε) :
    queryBudget q ≤ ((k : ℝ≥0) + 1) * ε := by
  unfold queryBudget
  have := sum_le_nsmul_of_forall_le q ε h
  -- `((k+1 : ℕ) : ℝ≥0) = (k : ℝ≥0) + 1` by `Nat.cast_add` + `Nat.cast_one`.
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- **Total accumulation (master accounting bound).**
    If every fold-round error is ≤ `εf` and every query-round error is ≤ `εq`,
    then the total soundness budget is ≤ `k·εf + (k+1)·εq`.

    This is the FRI/STIR sequential-composition accounting result reduced to its
    arithmetic core: the total soundness error is the linear accumulation of the
    per-round errors. Whether the per-round numbers `e`, `q` actually bound protocol
    probabilities is NOT addressed here (see the file header). PROVEN. -/
theorem totalBudget_le {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0)
    (εf εq : ℝ≥0) (hf : ∀ i, e i ≤ εf) (hq : ∀ i, q i ≤ εq) :
    totalBudget e q ≤ (k : ℝ≥0) * εf + ((k : ℝ≥0) + 1) * εq := by
  unfold totalBudget
  exact add_le_add (foldBudget_le e εf hf) (queryBudget_le q εq hq)

/-- Uniform specialisation: a single budget `ε` dominating *all* per-round errors
    (fold and query) gives a total ≤ `(2k+1)·ε`. PROVEN. -/
theorem totalBudget_le_uniform {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0)
    (ε : ℝ≥0) (hf : ∀ i, e i ≤ ε) (hq : ∀ i, q i ≤ ε) :
    totalBudget e q ≤ (2 * (k : ℝ≥0) + 1) * ε := by
  have h := totalBudget_le e q ε ε hf hq
  -- `k·ε + (k+1)·ε = (2k+1)·ε`.
  have hcomb : (k : ℝ≥0) * ε + ((k : ℝ≥0) + 1) * ε = (2 * (k : ℝ≥0) + 1) * ε := by ring
  rwa [hcomb] at h

/-! ## §2. Monotone contraction / telescoping

"Each round reduces the proximity parameter δᵢ; the per-round error is monotone in δᵢ."
If the parameters are nonincreasing and the error is monotone in the parameter, then
every round's error is dominated by round 0's, recovering the linear bound with ε = e 0. -/

/-- **Monotone-contraction accumulation.**
    Suppose the per-round proximity parameters `δ : Fin (n) → ℝ≥0` are antitone
    (each round contracts: `δ` is `Antitone`) and the per-round error is a monotone
    function `g : ℝ≥0 → ℝ≥0` of the parameter, `e i = g (δ i)`. Then every round's
    error is ≤ `g (δ 0)`, hence `∑ i, e i ≤ n * g (δ 0)`.

    PROVEN: monotonicity gives `e i = g (δ i) ≤ g (δ 0)` since `δ i ≤ δ 0`
    (from `Antitone` and `0 ≤ i`), then `sum_le_nsmul_of_forall_le`. -/
theorem contraction_accumulation {n : ℕ} (δ : Fin (n + 1) → ℝ≥0) (g : ℝ≥0 → ℝ≥0)
    (hδ : Antitone δ) (hg : Monotone g) :
    (∑ i, g (δ i)) ≤ ((n : ℝ≥0) + 1) * g (δ 0) := by
  have hbound : ∀ i : Fin (n + 1), g (δ i) ≤ g (δ 0) := by
    intro i
    -- `δ` antitone and `(0 : Fin (n+1)) ≤ i` ⇒ `δ i ≤ δ 0`; apply `g` monotone.
    exact hg (hδ (Fin.zero_le i))
  have := sum_le_nsmul_of_forall_le (fun i => g (δ i)) (g (δ 0)) hbound
  simpa [Nat.cast_add, Nat.cast_one] using this

/-! ## §3. Geometric decay (finite-prefix closed-form bound)

If the per-round errors are bounded by a geometric sequence `e₀ · qⁱ` with `q < 1`, every
finite prefix of the budget is bounded by the closed form `e₀/(1-q)`. The geometric decay is a
HYPOTHESIS here, not a consequence of the STIR/FRI parameter schedule: halving the degree bound
while shrinking the domain proportionally keeps the rate `Dᵢ/Nᵢ` (hence `(Dᵢ/Nᵢ)^l`) constant,
so geometric decay of `queryRoundError` needs a schedule whose rate actually decreases.
Only finite prefixes are treated; no infinite-sum statement is made. -/

/-- **Finite geometric prefix bound** (over `ℝ`).
    If `e i ≤ e₀ * q^i` for all `i < n` with `0 ≤ q < 1` and `0 ≤ e₀`, then
    `∑_{i<n} e i ≤ e₀ / (1 - q)`.

    This is the geometric refinement of §1: when the per-round errors are dominated by a
    geometric sequence (supplied as `hbound`; e.g. a schedule along which the rate in
    `Fri.Spec.queryRoundError = (Dᵢ/Nᵢ)^l` strictly decreases), every finite prefix of the
    budget is dominated by the closed-form geometric series, *uniformly in `n`*.

    Fully PROVEN with confirmed lemmas only:
    * `Finset.sum_le_sum`  — per-term bound (ArkLib uses it 119×);
    * `Finset.mul_sum`     — factor `e₀` out (standard mathlib);
    * `geom_sum_eq (q≠1) n : ∑ i∈range n, q^i = (q^n - 1)/(q - 1)` (ArkLib `Combine.lean:44`);
    * `neg_div_neg_eq`     — rewrite `(q^n-1)/(q-1) = (1-q^n)/(1-q)` (ArkLib `Combine.lean:44`);
    * `div_le_div_of_nonneg_right (a≤b) (0≤c) : a/c ≤ b/c` — confirmed sig at ArkLib
      `CZ25DimensionCountProof.lean:690`; here with `1 - q^n ≤ 1` and `0 ≤ 1 - q`. -/
theorem geom_prefix_le_real {n : ℕ} (e : ℕ → ℝ) (e₀ q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (he₀ : 0 ≤ e₀)
    (hbound : ∀ i, i < n → e i ≤ e₀ * q ^ i) :
    (∑ i ∈ Finset.range n, e i) ≤ e₀ / (1 - q) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  -- Step 1: per-term domination, then `Finset.sum_le_sum`.
  have step1 : (∑ i ∈ Finset.range n, e i) ≤ ∑ i ∈ Finset.range n, e₀ * q ^ i :=
    Finset.sum_le_sum (fun i hi => hbound i (Finset.mem_range.mp hi))
  -- Step 2: factor `e₀` out — `Finset.mul_sum`.
  have step2 : (∑ i ∈ Finset.range n, e₀ * q ^ i) = e₀ * ∑ i ∈ Finset.range n, q ^ i := by
    rw [Finset.mul_sum]
  -- Step 3: closed form via `geom_sum_eq`.
  have hqne : q ≠ 1 := ne_of_lt hq1
  have step3 : (∑ i ∈ Finset.range n, q ^ i) = (q ^ n - 1) / (q - 1) := geom_sum_eq hqne n
  -- Step 4: `(q^n - 1)/(q - 1) = (1 - q^n)/(1 - q)`.
  -- Negate numerator and denominator: `-(q^n - 1) = 1 - q^n`, `-(q - 1) = 1 - q`,
  -- and `neg_div_neg_eq : -a / -b = a / b`.
  -- `q - 1 < 0` and `1 - q > 0`, both nonzero; cross-multiply with `div_eq_div_iff`.
  have hq1ne : q - 1 ≠ 0 := by intro h; apply ne_of_lt hq1; linarith
  have h1qne : (1 : ℝ) - q ≠ 0 := ne_of_gt h1q
  have step4 : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [div_eq_div_iff hq1ne h1qne]; ring
  -- Step 5: `(1 - q^n)/(1 - q) ≤ 1/(1 - q)` since `1 - q^n ≤ 1` and `0 ≤ 1 - q`.
  have hqn : (0 : ℝ) ≤ q ^ n := pow_nonneg hq0 n
  have step5 : (1 - q ^ n) / (1 - q) ≤ 1 / (1 - q) :=
    div_le_div_of_nonneg_right (by linarith) h1q.le
  -- Assemble: `∑ e i ≤ e₀ * (1-q^n)/(1-q) ≤ e₀ * (1/(1-q)) = e₀/(1-q)`.
  calc (∑ i ∈ Finset.range n, e i)
      ≤ ∑ i ∈ Finset.range n, e₀ * q ^ i := step1
    _ = e₀ * ((q ^ n - 1) / (q - 1)) := by rw [step2, step3]
    _ = e₀ * ((1 - q ^ n) / (1 - q)) := by rw [step4]
    _ ≤ e₀ * (1 / (1 - q)) := by
          exact mul_le_mul_of_nonneg_left step5 he₀
    _ = e₀ / (1 - q) := by rw [mul_one_div]

/-- **Finite geometric prefix bound on `ℝ≥0`** (the form the FRI/STIR query budget uses).
    Mirrors `geom_prefix_le_real`, transported via `NNReal.coe_le_coe`. Per-round errors
    `e : ℕ → ℝ≥0` decaying as `e i ≤ e₀ * qⁱ` (with `q < 1`) accumulate to ≤ `e₀ / (1 - q)`
    regardless of the round count.

    PROVEN by `rw [← NNReal.coe_le_coe]` then `push_cast [NNReal.coe_sub hq1.le]`
    (the `coe_sub` rewrite needs `q ≤ 1`; `push_cast` discharges the standard
    sum/div/mul/pow/one casts), reducing to `geom_prefix_le_real`. -/
theorem geom_prefix_le_nnreal {n : ℕ} (e : ℕ → ℝ≥0) (e₀ q : ℝ≥0)
    (hq1 : q < 1) (hbound : ∀ i, i < n → e i ≤ e₀ * q ^ i) :
    (∑ i ∈ Finset.range n, e i) ≤ e₀ / (1 - q) := by
  -- Transport to `ℝ` via `NNReal.coe_le_coe`.
  rw [← NNReal.coe_le_coe]
  -- The only nonstandard cast is `↑(1 - q) = 1 - ↑q`, which needs `q ≤ 1`
  -- (`NNReal.coe_sub hq1.le`); all other casts (`coe_sum`, `coe_div`, `coe_mul`, `coe_pow`,
  -- `coe_one`) are handled by `push_cast`.
  push_cast [NNReal.coe_sub hq1.le]
  -- Now a pure-`ℝ` goal `∑ ↑(e i) ≤ ↑e₀ / (1 - ↑q)`: apply `geom_prefix_le_real`.
  refine geom_prefix_le_real (fun i => (e i : ℝ)) (e₀ : ℝ) (q : ℝ)
    q.coe_nonneg (by exact_mod_cast hq1) e₀.coe_nonneg (fun i hi => ?_)
  -- per-round bound: coerce `e i ≤ e₀ * q^i` into `ℝ` (`exact_mod_cast` handles
  -- `coe_mul`/`coe_pow`).
  have h := hbound i hi
  push_cast
  exact_mod_cast h

/-! ## §4. Budget identification (an equation between chosen numbers, NOT a soundness fact)

The accumulation results (§1–§3) take the per-round errors `e i` as given and bound their sum.
This section adds only the bookkeeping predicate `PerRoundProximityGap e B := ∀ i, e i = B i`
("the accounting uses the budgets `B`"), and adapters that rewrite along it. Despite its
historical name, the predicate contains no code, received word, degree, random experiment, or
agreement event, and is trivially satisfied by choosing `e := B` (`PerRoundProximityGap.refl`).
It does NOT encode, isolate, or discharge the BCIKS20 correlated-agreement / proximity-gap
theorem. That per-round soundness content (`Combine.combine_theorem`, `STIR.proximity_gap`,
the `ProximityGap.StrictCoeffPolysResidual` family, and the STIR round-by-round route in
`Stir/SubUnitRbr.lean`) must be supplied and cited separately by any consumer that wants a
probability bound. -/

/-- **Budget identification.** `PerRoundProximityGap e ProxGapBound` says only that the
    accounting per-round error `e i` is *the same number* as the chosen budget
    `ProxGapBound i`, for every round. In the intended instantiation the budget is
    `ProximityGap.errorBound δ degBoundᵢ domᵢ` (= `Fri.Spec.roundError`), but the predicate
    itself carries no information that this number bounds any probability: that is the
    separate content of `Combine.combine_theorem` / `STIR.proximity_gap`.

    The name is historical; read it as "per-round budget identification". -/
def PerRoundProximityGap {n : ℕ} (e ProxGapBound : Fin n → ℝ≥0) : Prop :=
  ∀ i, e i = ProxGapBound i

/-- Reflexive budget identification: choosing the accounting errors to be the budgets
themselves. This is the specialization used by the STIR front doors; it is discharged by `rfl`
and carries no soundness content. -/
theorem PerRoundProximityGap.refl {n : ℕ} (e : Fin n → ℝ≥0) : PerRoundProximityGap e e :=
  fun _ => rfl

/-- **Adapter: fold budget from a budget identification.**
    Given `PerRoundProximityGap e ProxGapBound` (i.e. `e i = ProxGapBound i`) and a uniform
    bound `ε` on the budgets, the accounting fold budget is ≤ `n·ε`.
    PROVEN: rewrite `e i = ProxGapBound i`, then apply `sum_le_nsmul_of_forall_le`.

    Pure arithmetic: it says nothing about whether the budgets bound any protocol
    probability. -/
theorem foldBudget_le_of_keystone {n : ℕ} (e ProxGapBound : Fin n → ℝ≥0) (ε : ℝ≥0)
    (hkey : PerRoundProximityGap e ProxGapBound)
    (hbound : ∀ i, ProxGapBound i ≤ ε) :
    foldBudget e ≤ (n : ℝ≥0) * ε := by
  unfold foldBudget
  refine sum_le_nsmul_of_forall_le e ε (fun i => ?_)
  rw [hkey i]; exact hbound i

/-- **Adapter: budget identification + geometric decay ⟹ closed-form prefix bound.**
    If `e i = ProxGapBound i` and the budgets are dominated by a geometric sequence
    (`hgeo : ProxGapBound i ≤ e₀ * qⁱ`, `q < 1`, an explicit hypothesis), then every finite
    prefix of the accounting budget is ≤ `e₀ / (1 - q)`, uniformly in the prefix length.
    PROVEN: rewrite along `hkey`, then `geom_prefix_le_nnreal`.

    The geometric decay is assumed, not derived from a STIR/FRI parameter schedule
    (proportional degree/domain shrinking keeps the rate constant; see §3). -/
theorem prefixBudget_le_of_keystone_geom {n : ℕ}
    (e ProxGapBound : ℕ → ℝ≥0) (e₀ q : ℝ≥0)
    (hkey : ∀ i, e i = ProxGapBound i) (hq1 : q < 1)
    (hgeo : ∀ i, i < n → ProxGapBound i ≤ e₀ * q ^ i) :
    (∑ i ∈ Finset.range n, e i) ≤ e₀ / (1 - q) := by
  refine geom_prefix_le_nnreal e e₀ q hq1 (fun i hi => ?_)
  rw [hkey i]; exact hgeo i hi

/-! ## §5. Summary / honest status

  PROVEN (elementary `ℝ≥0` / `ℝ` arithmetic):
    * `queryBudget_le_totalBudget`, `foldBudget_le_totalBudget` — additive-budget projections
      (analogue of `Fri.Spec.queryError_le_totalError`).
    * `sum_le_nsmul_of_forall_le`, `foldBudget_le`, `queryBudget_le`, `totalBudget_le`,
      `totalBudget_le_uniform` — linear accumulation of per-round budgets.
    * `contraction_accumulation` — antitone parameter + monotone error ⟹ every round's error is
      dominated by round 0's.
    * `geom_prefix_le_real`, `geom_prefix_le_nnreal` — finite prefixes of a sequence dominated
      by `e₀ · qⁱ` (`q < 1`, assumed) are ≤ `e₀/(1-q)`.
    * `PerRoundProximityGap.refl`, `foldBudget_le_of_keystone`,
      `prefixBudget_le_of_keystone_geom` — budget-identification bookkeeping.

  NOT IN THIS FILE: any per-round soundness statement. `PerRoundProximityGap` is an equation
  between chosen numbers, not the BCIKS20 proximity-gap theorem, and discharging it does not
  discharge any proximity-gap or protocol-soundness obligation. The genuine per-round content
  is `Combine.combine_theorem` / `STIR.proximity_gap` (consuming
  `ProximityGap.StrictCoeffPolysResidual`, whose Johnson-regime extraction remains a named
  residual), and the STIR round-by-round soundness route for the declared wire model is
  `Stir/SubUnitRbr.lean`; the multi-round STIR protocol objects live in
  `Stir/MultiRound.lean` and the checking-verifier modules. Retained STIR soundness/model
  debt is tracked in `docs/wiki/stir-issue-301.md` (audit L36); this file does not discharge
  it.

  CONCLUSION: the FRI/STIR error *accounting* (additive, monotone-contraction, and
  finite-prefix geometric bounds on sums of per-round budgets) is separable arithmetic and is
  fully proven here. The connection from these budgets to actual protocol probabilities is
  NOT made in this file. -/

end ArkLib.ProofSystem.Stir.ErrorAccumulation
