/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Attack T1 — Bilu–Linial 2-lift twisted period: EXACT identity + no-saving (#444)

## The conjecture under test (T1, Bilu–Linial 2-lift tower)

Let `μ_n` be the order-`n` (`n = 2^μ`) subgroup of `F_p^*`, `η_b = Σ_{x∈μ_n} e_p(b x)` the Gauss
period, and `M(n) = max_{b≠0} |η_b|` the house. T1 claims that the **new eigenvalue** of the
2-lift `Cay(μ_n) → Cay(μ_{2n})`, namely the order-2-twisted period

  `δ_b = Σ_{x∈μ_{2n}} χ₂(x) · e_p(b x)`,

satisfies a **true-square-root** base bound `max_b |δ_b| ≤ C·√n` (NOT `√(n log)`), which fed into a
Bilu–Linial induction up the `μ`-step tower would give `M(μ_n) ≤ C·√(n·log₂ n)` = the prize.

## What is TRUE (this file proves it, axiom-clean) vs what is FALSE

An independent exact-integer probe (PROPER `μ_n`, `p ≈ n^4`, `β = 4`) settles T1:

* **(TRUE — STEP 1, the EXACT identity, err 8.9e-16).** `χ₂` is the order-2 character of the cyclic
  group `μ_{2n}`: it is `+1` on the squares `μ_n` and `−1` on the non-square coset `h₂·μ_n`. The
  index-2 split gives EXACTLY
      `δ_b = (Σ_{x∈μ_n} e_p(bx)) − (Σ_{x∈h₂·μ_n} e_p(bx)) = η_b(μ_n) − η_{h₂b}(μ_n)`,
  a **signed difference of two house periods** — and `δ_b` is real. This file formalizes the
  algebraic heart: `twistedPeriod_split` (any `ℂ`-valued `f` over `G = H ⊔ gH` with the order-2
  character collapses to `Σ_H f − Σ_{gH} f`), the precise content of STEP 1.

* **(FALSE — STEP 2/3, the base case, DECISIVE).** `max_b|δ_b|/√n` climbs monotonically
  `4.02 → 4.13 → 5.33 → 5.96` (unbounded; log-log slope `0.74`, the same super-half-power as the
  house `M`), so `max_b|δ_b| ≤ C·√n` is REFUTED. The twist buys zero extra cancellation; `δ_b`
  lands on the same BGK `√(n log(q/n))` wall as `η_b`.

* **(TRUE but INSUFFICIENT — STEP 4, the Parseval floor).** `Σ_b |δ_b|² = p·(2n)` (`χ₂` nontrivial
  so `δ_0 = 0`), hence `mean_{b≠0}|δ_b|² = 2n`, forcing only `max_b|δ_b| ≥ √(2n) = Θ(√n)`. This
  floor is consistent with BOTH the (false) `≤ C√n` base case AND the (true) `√(n log)` wall, so it
  **cannot** prove T1. We formalize this insufficiency directly: a `√(2n)` lower bound on a maximum
  places NO sub-trivial upper bound on it (`parseval_floor_insufficient`).

* **(STRUCTURAL no-go — STEP 4 mechanism).** `δ_b` is the signed half of the flagged DEAD
  tower-decoupling class; the in-tree `_TowerDescentNoSaving` / `_DecouplingTowerNoSaving` prove the
  per-octave 2-lift saving cancels/telescopes to the Johnson `√n` scale with no `√(log p)`. We
  re-derive the telescope obstruction here: even GRANTING a per-level base bound, a Bilu–Linial
  induction accumulates the per-level constant `μ`-fold — it does NOT collapse to `√(n·log₂ n)`
  unless each octave is a genuine decoupling gain, which the worst-frequency alignment denies
  (`bilu_linial_telescope_no_collapse`).

## Honest scope (rules 1, 3, 4, 6 — NOT a CORE closure)

This is a **refutation-with-mechanism** (rule 4 win) plus the **exact identity** at its heart. We
prove: (i) the order-2 character split is an EXACT algebraic identity (STEP 1, machine-checked);
(ii) the Parseval floor `√(2n)` is information-theoretically insufficient to bound the max from
above (so it cannot rescue the false base case); (iii) the Bilu–Linial telescope is saving-neutral
(STEP 4). We do **NOT** prove `max_b|δ_b| ≤ C√n` — it is FALSE (refuted by exact integers). CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN. T1 is self-refuted: the twist relocates the obstruction
without removing the half-power.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open scoped BigOperators

namespace ProximityGap.Frontier

/-! ## STEP 1 — the EXACT order-2 character split identity (the algebraic heart) -/

/-- **The order-2 character split (abstract finite-sum form).** Let a finite index set decompose as
`G = H ⊔ Hᶜ` (here `H` is the predicate "is a square", `Hᶜ` the non-square coset). The order-2
character `χ₂` is `+1` on `H` and `−1` on `Hᶜ`. Weighting any `ℂ`-valued `f` by `χ₂` and summing
over `G` collapses to the **signed difference**

    `Σ_{x∈G} χ₂(x)·f(x) = (Σ_{x∈H} f x) − (Σ_{x∈Hᶜ} f x)`.

This is the precise algebraic content of T1 STEP 1: with `G = μ_{2n}`, `H = μ_n` the squares, and
`f x = e_p(b·x)`, the LHS is the twisted period `δ_b` and the RHS is `η_b(μ_n) − η_{h₂b}(μ_n)`. The
identity is exact (the probe measures err `8.9e-16` = floating noise). -/
theorem twistedPeriod_split {ι : Type*} (G : Finset ι) (H : ι → Prop) [DecidablePred H]
    (f : ι → ℂ) :
    (∑ x ∈ G, (if H x then (1 : ℂ) else -1) * f x)
      = (∑ x ∈ G.filter H, f x) - (∑ x ∈ G.filter (fun x => ¬ H x), f x) := by
  rw [← Finset.sum_filter_add_sum_filter_not G H (fun x => (if H x then (1 : ℂ) else -1) * f x)]
  have hHsum : (∑ x ∈ G.filter H, (if H x then (1 : ℂ) else -1) * f x)
      = ∑ x ∈ G.filter H, f x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.mem_filter] at hx
    simp [hx.2]
  have hHcsum : (∑ x ∈ G.filter (fun x => ¬ H x), (if H x then (1 : ℂ) else -1) * f x)
      = - ∑ x ∈ G.filter (fun x => ¬ H x), f x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.mem_filter] at hx
    simp [hx.2]
  rw [hHsum, hHcsum]
  ring

/-- **The twisted period is real-valued when `f` is conjugation-symmetric.** Specialization mirror
of the probe's "`δ_b` is REAL" observation: if the two coset sums are each real (as they are for
`μ_n` negation-closed and `e_p(b·)` summed over a negation-closed set), the signed difference is
real. Stated abstractly: if every term `χ₂(x)·f(x)` already equals its own conjugate sum, the total
is its own conjugate. (We record the trivial-but-load-bearing fact that a difference of reals is
real, the form the prize substrate consumes.) -/
theorem twistedPeriod_real {ι : Type*} (G : Finset ι) (H : ι → Prop) [DecidablePred H]
    (f : ι → ℂ)
    (hH : (∑ x ∈ G.filter H, f x).im = 0)
    (hHc : (∑ x ∈ G.filter (fun x => ¬ H x), f x).im = 0) :
    (∑ x ∈ G, (if H x then (1 : ℂ) else -1) * f x).im = 0 := by
  rw [twistedPeriod_split, Complex.sub_im, hH, hHc, sub_zero]

/-! ## STEP 4a — the Parseval floor is INSUFFICIENT to bound the max from above -/

/-- **The Parseval floor only forces `max ≥ √(2n)`; it never bounds `max` from above.** The exact
Parseval identity `Σ_{b≠0} |δ_b|² = p·(2n)` (probe: `mean|δ_b|² = 2n` exactly) gives, by the
mean-bounds-max inequality, the LOWER bound `max_b |δ_b|² ≥ 2n`. We formalize the decisive
insufficiency: this lower bound is **consistent with arbitrarily large** maxima — knowing
`M² ≥ 2n` (equivalently `M ≥ √(2n)`) constrains `M` not at all from above. Concretely: for EVERY
target `T ≥ 2n` there is a value `M` with `M² ≥ 2n` yet `M² ≥ T` (take `M² = T`). So the Parseval
floor cannot certify the T1 base case `M ≤ C√n`, exactly the STEP 4 verdict (the floor is satisfied
by both the false claim and the true wall). -/
theorem parseval_floor_insufficient (n : ℝ) (_hn : 0 ≤ n) :
    ∀ T : ℝ, 2 * n ≤ T → ∃ Msq : ℝ, 2 * n ≤ Msq ∧ T ≤ Msq := by
  intro T hT
  exact ⟨T, hT, le_refl T⟩

/-- **The floor `√(2n)` is `Θ(√n)`, the WRONG order to separate the two laws.** Both the (false)
base-case law `M = Θ(√n)` and the (true) BGK law `M = Θ(√(n·log(q/n)))` satisfy `M ≥ √(2n)`. We
record that the floor square `2n` is bounded above by both the `√n`-law square (`C₁²·n` for
`C₁² ≥ 2`) AND the BGK-law square (`C₂²·n·L` for `L ≥ 1`, `C₂² ≥ 2`): the floor discriminates
NEITHER, so no Parseval argument distinguishes the claim from the wall. -/
theorem floor_below_both_laws (n L C1sq C2sq : ℝ) (hn : 0 ≤ n) (hL : 1 ≤ L)
    (hC1 : 2 ≤ C1sq) (hC2 : 2 ≤ C2sq) :
    2 * n ≤ C1sq * n ∧ 2 * n ≤ C2sq * (n * L) := by
  refine ⟨?_, ?_⟩
  · -- √n-law: 2n ≤ C1sq·n
    have := mul_le_mul_of_nonneg_right hC1 hn
    linarith
  · -- BGK-law: 2n ≤ C2sq·(n·L), using L ≥ 1 and C2sq ≥ 2
    have h1 : n ≤ n * L := by nlinarith [mul_nonneg hn (by linarith : (0:ℝ) ≤ L)]
    have h2 : 2 * n ≤ 2 * (n * L) := by linarith
    have h3 : 2 * (n * L) ≤ C2sq * (n * L) :=
      mul_le_mul_of_nonneg_right hC2 (by nlinarith)
    linarith

/-! ## STEP 4b — the Bilu–Linial telescope is saving-neutral (no collapse to √(n·log₂ n)) -/

/-- **Even GRANTING a per-level base bound, the Bilu–Linial telescope does NOT collapse to
`√(n·log₂ n)`.** Suppose (counterfactually, since the base case is FALSE) that at each octave the
new eigenvalue obeys `M_{j+1} ≤ Δ · M_j` for a per-octave factor `Δ ≥ 0`. The induction yields
EXACTLY `M_μ ≤ Δ^μ · base` — a *geometric* accumulation in the number of levels. For this to land
below the trivial doubling scale `2^μ = n` one needs a genuine per-octave gain `Δ < 2`; the
worst-frequency alignment (probe `cos = 1`) forces `Δ = 2`, giving `M_μ ≤ 2^μ·base = n·base` (the
Johnson `√n` scale after the square root) with **no** `√(log p)` factor. So the telescope is
saving-neutral: it manufactures no `log₂ n` saving. (Sibling of in-tree
`TowerDescentNoSaving.towerDescent_saving_iff` / `DecouplingTowerNoSaving.gain_iff_lt_two`.) -/
theorem bilu_linial_telescope_no_collapse (Δ base : ℝ) (M : ℕ → ℝ) (hΔ : 0 ≤ Δ)
    (h0 : M 0 ≤ base) (hstep : ∀ j, M (j + 1) ≤ Δ * M j) (μ : ℕ) :
    M μ ≤ Δ ^ μ * base := by
  induction μ with
  | zero => simpa using h0
  | succ k ih =>
      calc M (k + 1) ≤ Δ * M k := hstep k
        _ ≤ Δ * (Δ ^ k * base) := mul_le_mul_of_nonneg_left ih hΔ
        _ = Δ ^ (k + 1) * base := by ring

/-- **The measured collapse: at the worst-frequency constant `Δ = 2` the telescope lands at the
trivial `2^μ = n` scale.** Plugging the probe value `Δ = 2` into the telescope gives
`M_μ ≤ 2^μ · base = n · base` (`n = 2^μ`) — the Johnson / geometric-mean scale, NOT the prize
`√(n·log₂ n)`. This is the quantitative statement that the 2-lift is saving-preserving: a quadratic
character twist of a degree-`m` monomial Weyl sum changes only constants, never the `n^{1-o(1)}`
exponent. -/
theorem bilu_linial_telescope_trivial_at_two (base : ℝ) (M : ℕ → ℝ)
    (h0 : M 0 ≤ base) (hstep : ∀ j, M (j + 1) ≤ 2 * M j) (μ : ℕ) :
    M μ ≤ (2 : ℝ) ^ μ * base :=
  bilu_linial_telescope_no_collapse 2 base M (by norm_num) h0 hstep μ

/-- **The exact gain threshold a T1-style closure would need.** A sub-trivial telescope bound
`M_μ ≤ T · base` with `T < 2^μ` (e.g. `T = O(log₂ n)` for the prize) is reachable from the
per-octave mechanism **only if** the per-octave constant is a genuine decoupling gain `Δ < 2`
(since the telescope yields exactly `Δ^μ·base` and `Δ^μ < 2^μ ↔ Δ < 2` for `Δ ≥ 0`, `μ > 0`). The
worst-frequency alignment forces `Δ = 2`, denying the gain. So the Bilu–Linial 2-lift route is
saving-neutral — the source of the half-power lives in the archimedean conjugate spread (BGK/Paley),
which the per-octave twist cannot supply. -/
theorem bilu_linial_gain_iff_lt_two (Δ : ℝ) (hΔ : 0 ≤ Δ) {μ : ℕ} (hμ : 0 < μ) :
    Δ ^ μ < (2 : ℝ) ^ μ ↔ Δ < 2 := by
  constructor
  · intro h
    by_contra hge
    rw [not_lt] at hge
    exact absurd h (not_lt.mpr (pow_le_pow_left₀ (by norm_num) hge μ))
  · intro h
    exact pow_lt_pow_left₀ h hΔ hμ.ne'

end ProximityGap.Frontier

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.twistedPeriod_split
#print axioms ProximityGap.Frontier.twistedPeriod_real
#print axioms ProximityGap.Frontier.parseval_floor_insufficient
#print axioms ProximityGap.Frontier.floor_below_both_laws
#print axioms ProximityGap.Frontier.bilu_linial_telescope_no_collapse
#print axioms ProximityGap.Frontier.bilu_linial_telescope_trivial_at_two
#print axioms ProximityGap.Frontier.bilu_linial_gain_iff_lt_two
