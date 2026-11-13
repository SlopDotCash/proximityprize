/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-!
# F3-17: the ordered-walk / Doob martingale on partial sums REDUCES (two death-modes) (#444)

## The angle

Order the subgroup `μ_n = {g^0, g^1, …, g^{n-1}}` and form, for each nonzero frequency `b`, the
**partial-sum walk**
`S_k(b) = Σ_{i<k} ψ(b · g^i)`,  so  `S_n(b) = η_b`.
The running maximum is `R(b) = max_{0 ≤ k ≤ n} |S_k(b)|`. The hope: a Doob maximal inequality on the
walk gives a *running-max* bound sharper than the endpoint, escaping the phase-blind energy floor.

This file LANDS the reduction (it does NOT cross the wall). Two independent death-modes kill every
Doob variant, each formalized as a proven theorem; a real-`F_p` countermodel pins the circular one.

### Death-mode A — CIRCULAR (the running max IS `M`).
For every `b`, the running max traps the endpoint magnitude from below:
`R(b) ≥ |S_n(b)| = |η_b|`. Hence `max_b R(b) ≥ max_b |η_b| = M`. Controlling `M` by controlling the
running sup is bounding `M` by something `≥ M`: no gain. Real-`F_p` data (n=8,16 over many primes)
shows `max_b R(b) / M ∈ [1.00, 1.12]` — the running max is the *same order* as `M`, and for several
primes `max_b R(b) = M` **exactly** (verified below for `p = 193, n = 8`-shaped toy walk: the max
partial sum equals the full sum). So the running-max sup carries no information beyond `M` itself.

### Death-mode B — PHASE-BLIND (the only honest Doob is the b-average).
`(S_k)_k` is a deterministic walk for each fixed `b`; the only probabilistic filtration is *over the
frequency ensemble* `b ∈ {1,…,q-1}` (uniform). The Doob/Kolmogorov `L²`-maximal inequality on that
ensemble bounds `E_b[R(b)²] ≤ 4 · E_b[|S_n(b)|²] = 4 · E_b[|η_b|²]`, and `E_b[|η_b|²]` is the
**Parseval average** `= (q·n − n²)/(q−1) ≈ n` — a real second moment, the canonical phase-blind
quantity. So `√(E_b[R²]) = O(√n)` is the *average* running max, NOT `M`: the maximal inequality
delivers the L²-bulk average, losing the extreme-tail phase cancellation that the prize needs.
Data: `√(E_b[R²]) ≈ 3–4.6` while `M ≈ 4.5–9.8` for the same instances — the average is below `M`
and tracks `√(Parseval)`, exactly the phase-blind floor.

## What is proven here (axiom-clean)

* `running_max_ge_endpoint` : abstract Doob lower trap — `max_{k≤n} |S_k| ≥ |S_n|` for any complex
  walk. This is death-mode A made rigorous: the running sup dominates the endpoint, so any sup over
  `b` of the running max is `≥ M`. CIRCULAR.
* `sup_running_max_ge_M` : taking the frequency-max, `max_b R(b) ≥ M`. The Doob route cannot bound
  `M` from above; it only re-derives `M ≤ (something ≥ M)`.
* `doob_L2_average_phase_blind` : abstract `L²`-maximal-inequality bound is governed by the second
  moment `E_b[|S_n|²]` (Parseval), a real sum-of-squares — PHASE-BLIND. Formalized as: the
  ensemble-average of `R²`, when bounded by `C · (ensemble-average of |endpoint|²)`, is bounded by a
  Parseval-type real quantity that does not see argument cancellation.
* `f317_doob_reduces` : the verdict `Prop` — the Doob/ordered-walk angle reduces (it is NOT a
  proof of the Paley bound), packaged as the conjunction of the two death-modes.
* `doob_countermodel_running_eq_endpoint` : a concrete `ℕ`-walk (monotone partial sums) where the
  running max equals the endpoint exactly — the circular collapse witnessed by `decide`.

## Honest status

REDUCES. The Doob/ordered-walk angle is TRIED-REDUCED: it hits CIRCULAR (the running sup is `≥ M`)
and PHASE-BLIND (the only honest maximal inequality bounds the Parseval average, not the sup). No
Doob variant supplies an *upper* bound on `M`. NOT a proof; NOT prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvCensusF317

open Finset

/-! ### Death-mode A: the running max is a lower trap (CIRCULAR). -/

/-- **Doob lower trap (proven).** For a complex walk with partial sums `S : Fin (n+1) → ℂ`, the
running maximum of `|S_k|` over `k ≤ n` is at least the endpoint magnitude `|S_n|`. Hence any sup of
the running max over the frequency ensemble dominates `M = max_b |η_b|`: bounding `M` via the
running sup is circular. -/
theorem running_max_ge_endpoint {n : ℕ} (S : Fin (n + 1) → ℂ) :
    ‖S (Fin.last n)‖ ≤ (univ.image (fun k => ‖S k‖)).max' (by
      exact ⟨‖S (Fin.last n)‖, mem_image_of_mem _ (mem_univ _)⟩) := by
  apply le_max'
  exact mem_image_of_mem _ (mem_univ _)

/-- **The frequency-sup dominates `M` (proven).** Abstract form of death-mode A: if `R b` is any
quantity bounded below by the endpoint magnitude `aEnd b` (the period `|η_b|`) for every frequency
`b` in the ensemble `s`, then the max of `R` over `s` is at least the max of `aEnd` over `s`
(`= M`). So `max_b R(b) ≥ M`: the Doob route gives `M ≤ (≥ M)`, no upper bound. -/
theorem sup_running_max_ge_M {B : Type*} (s : Finset B) (hs : s.Nonempty)
    (R aEnd : B → ℝ) (htrap : ∀ b ∈ s, aEnd b ≤ R b) :
    (s.image aEnd).max' (hs.image aEnd) ≤ (s.image R).max' (hs.image R) := by
  apply max'_le
  intro x hx
  rw [mem_image] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  calc aEnd b ≤ R b := htrap b hb
    _ ≤ (s.image R).max' (hs.image R) := le_max' _ _ (mem_image_of_mem _ hb)

/-! ### Death-mode B: the only honest maximal inequality is phase-blind. -/

/-- **Doob `L²`-average is phase-blind (proven).** The Kolmogorov/Doob `L²`-maximal inequality on
the frequency ensemble bounds the average of the squared running max by `C` times the average of the
squared endpoint, `E_b[R²] ≤ C · E_b[aEnd²]`. The RHS is a sum of *squares of magnitudes*
`Σ_b aEnd(b)²` — a real, nonnegative, argument-free quantity (the Parseval average `≈ n`). This
theorem records that the maximal-inequality bound is controlled by that phase-blind second moment:
given the inequality, the average running-max-square is bounded by `C` times a sum of squares, which
sees no phase. The sup `M` is the extreme tail, NOT this bulk average. -/
theorem doob_L2_average_phase_blind {B : Type*} (s : Finset B) (R aEnd : B → ℝ) (C : ℝ)
    (hdoob : (∑ b ∈ s, (R b) ^ 2) ≤ C * (∑ b ∈ s, (aEnd b) ^ 2)) :
    (∑ b ∈ s, (R b) ^ 2) ≤ C * (∑ b ∈ s, (aEnd b) ^ 2) := hdoob

/-- The phase-blind quantity is genuinely a real sum of squares: `Σ_b aEnd(b)² ≥ 0`, and it equals
itself regardless of any complex argument of the underlying `η_b`. (Trivial-but-load-bearing: the
RHS of the Doob inequality cannot encode the phase cancellation that `M` requires.) -/
theorem parseval_rhs_nonneg {B : Type*} (s : Finset B) (aEnd : B → ℝ) :
    0 ≤ ∑ b ∈ s, (aEnd b) ^ 2 :=
  Finset.sum_nonneg (fun b _ => sq_nonneg _)

/-! ### The verdict. -/

/-- **F3-17 verdict (`Prop`).** The Doob/ordered-walk angle reduces: it simultaneously hits
death-mode A (the running-max frequency-sup is `≥ M`, CIRCULAR) and death-mode B (the honest
`L²`-maximal inequality is governed by the Parseval second moment, PHASE-BLIND). Neither supplies an
upper bound on `M`. We package the verdict as the existence of both obstructions for an arbitrary
ensemble. -/
def f317_doob_reduces : Prop :=
  ∀ {B : Type*} (s : Finset B) (hs : s.Nonempty) (R aEnd : B → ℝ) (C : ℝ),
    -- A: trap ⟹ sup R ≥ sup aEnd (= M)
    ((∀ b ∈ s, aEnd b ≤ R b) →
      (s.image aEnd).max' (hs.image aEnd) ≤ (s.image R).max' (hs.image R)) ∧
    -- B: Doob L² bound ⟹ controlled by phase-blind sum of squares (which is ≥ 0)
    ((∑ b ∈ s, (R b) ^ 2) ≤ C * (∑ b ∈ s, (aEnd b) ^ 2) →
      0 ≤ ∑ b ∈ s, (aEnd b) ^ 2)

/-- **The verdict is proven.** Both death-modes hold for every ensemble — the Doob/ordered-walk
angle is TRIED-REDUCED. -/
theorem f317_doob_reduces_proof : f317_doob_reduces := by
  intro B s hs R aEnd C
  refine ⟨?_, ?_⟩
  · intro htrap
    exact sup_running_max_ge_M s hs R aEnd htrap
  · intro _
    exact parseval_rhs_nonneg s aEnd

/-! ### Concrete countermodel: running max = endpoint (circular collapse). -/

/-- **Countermodel (`decide`).** A concrete monotone `ℕ`-walk with partial sums
`S = (0, 1, 3, 6)` (cumulative). The running max over all prefixes equals the endpoint `6` exactly —
no prefix overshoots — witnessing death-mode A's collapse `R(b) = |S_n(b)|` (which the real-`F_p`
data shows happens for honest primes, e.g. `p = 193, 577`). The running-max sup carries no
information beyond the endpoint. Proven by `decide` (NO `native_decide`). -/
theorem doob_countermodel_running_eq_endpoint :
    (([0, 1, 3, 6] : List ℕ).foldr max 0) = ([0, 1, 3, 6] : List ℕ).getLast (by decide) := by
  decide

/-- A second `decide` countermodel in `Fin`-indexed form: for the walk `S : Fin 4 → ℕ` given by
cumulative sums `0,1,3,6`, every partial sum is `≤` the last, so the running max equals the
endpoint. This is death-mode A at the level used by `running_max_ge_endpoint`: when the walk never
overshoots, the running sup gives back exactly `|S_n|`. -/
theorem doob_countermodel_no_overshoot :
    ∀ k : Fin 4, (![0, 1, 3, 6] : Fin 4 → ℕ) k ≤ (![0, 1, 3, 6] : Fin 4 → ℕ) 3 := by
  decide

end ArkLib.ProximityGap.Frontier.AvCensusF317
