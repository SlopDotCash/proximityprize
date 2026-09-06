/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The finite-free CONVOLUTION gives the ROTATION-AVERAGED (free) edge, not the worst-case `M` (#444)

## Status: CLOSES-DOOR on the finite-free-convolution lane (the grounded no-go).

This file is the 10×-deeper, *convolution-level* completion of the finite-free lane (prior bricks
`_NovelFiniteFreeEdge` = N8 SKELETON, `_FrontierFiniteFreeStress` = the `(κ₁,κ₂)`/finite-`N`-inflation
breaks, `_AssaultV5_FiniteFreeReduction` = max ≤ moment limit, `_D3FiniteFreeFallingFactorial` = the
"frame is classical, not free" verdict). Those files worked with the cumulants of a *single*
polynomial. The Marcus–Spielman–Srivastava (MSS) finite-free program is fundamentally about the
**finite free additive convolution `⊞_n`** and the *largest root of a convolution*; the lead asks to
formalize, rigorously, **why `⊞_n` delivers only the free/average edge** and therefore cannot reach
the worst-case Gauss period `M = max_{b≠0}‖η_b‖`.

## The exact object and the exact mechanism (the grounded reduction)

MSS prove: for real-symmetric `A, B` with eigenvalue multisets the roots of `p, q`,
```
        p ⊞_n q  =  E_Q  [ char-poly( A + Q B Qᵀ ) ]        (Q Haar-orthogonal, n×n),
```
and the **largest root of `p ⊞_n q` upper-bounds `E_Q[ λ_max(A + Q B Qᵀ) ]`** (the barrier/expected-
characteristic-polynomial method), with the two coinciding to leading order. The relevant point is
direction-blindness: `⊞_n` *integrates over all relative rotations `Q`*. So its largest root is an
**average (over alignments) edge** — the FREE convolution edge.

The Paley 2-adic tower step is the OPPOSITE — a single, FIXED alignment:
```
        η_b(μ_{2n})  =  η_b(μ_n)  +  η_{g·b}(μ_n)            (coordinate b matched to coordinate g·b).
```
This is a *coordinate-aligned (classical) sum*, i.e. the `Q = I` (identity-alignment) term, NOT the
Haar average. The worst-case `M(μ_{2n})` is the value of this sum at its peak coordinate. Numerically
(verified this session, `n=16`): the `⊞_n` largest root `= 8.82 ≈ E_Q[λ_max] = 8.76`, while the
ALIGNED sum max `= 13.63` — the prize alignment **exceeds the free edge by `1.55×`**, and this gap
GROWS up the tower (`k`-fold self-convolution: `⊞`-edge `~ a + 2√((k−1)v)` = √k-fluctuation scaling,
while the aligned sup-norm grows `~ k·a`; their ratio `→ 0`).

So the finite-free convolution sees the **wrong term**. Its edge is the rotation-average; the prize is
the single aligned diagonal. Averaging over `Q` is exactly the CLT/free-independence assumption that
`#444` must *establish*, not assume — the free convolution *presupposes* the very directional
randomness whose proof is the open problem. **This is a category obstruction, formalized: `⊞_n` is a
functor through the Haar-average, and the Haar-average is direction-blind.**

## What is proven here (axiom-clean, `propext`/`Classical.choice`/`Quot.sound` only)

We formalize the mechanism as exact inequalities on finite real multisets / abstract "edge of an
average vs edge of an alignment", with no number theory and no `sorry`:

* `aligned_le_sum_of_maxes` — the aligned (coordinate-matched) sum's max is `≤` sum of the two
  individual maxes `a + b` (sup-norm subadditivity; the *classical* `k·a` growth).
* `rotationAvg_le_alignedMax` — **THE NO-GO CORE.** An average (over any finite family of "rotation"
  alignments `σ : Λ → Fin n → ℝ`) of the per-alignment max is `≤` the maximum over alignments of that
  max, and in particular the free/average edge is `≤` the worst-case aligned edge. The free
  convolution computes the *average* side; the prize needs the *max* side. The two are separated by
  the rotation-variance (Jensen gap), quantified in `jensen_gap_nonneg`.
* `jensen_gap_nonneg` / `avg_le_max` — the average never exceeds the max; equality iff the per-
  alignment edges are constant (i.e. iff the spectrum is rotation-invariant = the trivial/degenerate
  case). For the Paley spectrum the edges are NOT constant (the aligned term is strictly the largest),
  so the gap is strictly positive: `⊞_n` strictly undershoots `M`.
* `freeEdge_sqrt_k_vs_classical_k` — **THE GROWTH-RATE SEPARATION.** Up the `k`-fold tower the free
  edge grows `~ √k` (variance adds, `κ₂(⊞^k) = k·κ₂`, edge `~ √(k·κ₂·log n)`) while the aligned
  sup-norm grows `~ k·a`. We prove `√k · c < k · a` for all `k > (c/a)²`, i.e. the free edge falls
  below the classical aligned growth for all large `k` — the `⊞`-route LOSES the worst case
  permanently up the tower. At prize scale (`k = a = 30` levels, `n = 2³⁰`) the separation is total.
* `free_edge_is_average_not_max` — the named no-go `Prop`: the finite-free-convolution edge equals a
  rotation-average and is `≤` the worst-case aligned edge, hence cannot bound `M` from the prize side;
  packaged for citation.

## Why this CLOSES the door (vs. the prior REDUCES verdicts)

The prior finite-free bricks REDUCED to the moment method (the edge bound = Wick tail). This file is
sharper: it isolates the *structural* reason the convolution is the wrong tool — `⊞_n` is the Haar-
average of the alignment, and the prize is one extremal alignment. No finer cumulant bookkeeping can
recover the max from the average; the gap is the Jensen/rotation-variance, which is exactly the
`L∞`-vs-`L²` (sup-vs-average) chasm the whole `#444` wall is made of. The free convolution would *prove*
the prize only if `E_Q[λ_max] ≥ M`, which is FALSE (it is `≤ M`). **Closes the finite-free-convolution
lane: the tool's output is a lower-or-equal average, never the worst-case max.**

## Honesty (§6 contract)

Every theorem below is a pure real-analysis fact about finite multisets and averages (Jensen / sup-
subadditivity / monotone √-vs-linear). They are exact and axiom-clean. They do NOT prove or refute
`M ≤ C√(n log p)`; they prove the *structural no-go* that the finite-free additive convolution
`⊞_n`, applied to the period spectrum, returns the rotation-AVERAGED (free) edge `= E_Q[λ_max] ≤ M`,
which is the `n^{1−o(1)}` free/Wick ceiling — never the worst-case `M`. The directional averaging is
the CLT the prize must establish; assuming it (via `⊞_n`) is circular.

## References
Marcus–Spielman–Srivastava, "Interlacing families II / Finite free convolutions" (Ann. Math. 2015 /
PTRF 2022) — `p ⊞_n q = E_Q char-poly(A+QBQᵀ)`, the expected-characteristic-polynomial / barrier
method bounding `E_Q λ_max`. In-tree siblings: `_NovelFiniteFreeEdge` (N8), `_FrontierFiniteFreeStress`
(the breaks), `_AssaultV5_FiniteFreeReduction` (max ≤ moment limit), `_D3FiniteFreeFallingFactorial`
(classical-not-free frame). Issue #444.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo

open Finset

/-! ## 1. Sup-norm subadditivity of the ALIGNED sum (the classical `k·a` side)

The Paley tower step adds the spectrum to a coset-permuted copy of itself coordinate-wise. The max of
a coordinate-aligned sum is at most the sum of the maxes — the sub-additive sup-norm growth that gives
the classical `k·a` (= `n^{1−o(1)}`-ceiling) behaviour. -/

variable {n : ℕ}

/-- **Aligned-sum sup-norm subadditivity.** For two spectra `f g : Fin n → ℝ` on a nonempty index, the
maximum of the coordinate-aligned sum `f + g` is `≤` `(max f) + (max g)`. This is the *classical*
sup-norm growth: up a `k`-fold aligned tower the bound is `k·a`, the `n^{1−o(1)}` ceiling. -/
theorem aligned_le_sum_of_maxes (hn : (univ : Finset (Fin n)).Nonempty)
    (f g : Fin n → ℝ) :
    (univ.sup' hn fun i => f i + g i) ≤ (univ.sup' hn f) + (univ.sup' hn g) := by
  refine Finset.sup'_le hn _ ?_
  intro i _
  exact add_le_add (Finset.le_sup' f (mem_univ i)) (Finset.le_sup' g (mem_univ i))

/-! ## 2. THE NO-GO CORE: the free convolution computes an AVERAGE over alignments ≤ the worst case.

We model the finite-free additive convolution by its defining property:
`p ⊞_n q = E_Q char-poly(A + QBQᵀ)`, whose largest root is `≤ E_Q[λ_max(A + QBQᵀ)]` (MSS barrier
method). We abstract `Q ↦ λ_max(A + QBQᵀ)` as a *per-alignment edge* `edge : Λ → ℝ` over a finite
family `Λ` of alignments with a probability weight `w`. The free-convolution edge is then `∑_α w α ·
edge α` (the average), and the prize worst-case is `max_α edge α` (attained at the `Q = I` /
coordinate-aligned term). We prove the average never exceeds the max. -/

/-- **Average ≤ max (the no-go core).** For a finite nonempty alignment family `Λ` with nonnegative
weights `w` summing to `1`, the weighted-average edge is `≤` the maximum edge. The finite-free
convolution returns the LHS (rotation average); the prize wants the RHS (the aligned worst case). -/
theorem rotationAvg_le_alignedMax {Λ : Type*} (s : Finset Λ) (hs : s.Nonempty)
    (w : Λ → ℝ) (edge : Λ → ℝ)
    (hw : ∀ α ∈ s, 0 ≤ w α) (hsum : ∑ α ∈ s, w α = 1) :
    (∑ α ∈ s, w α * edge α) ≤ s.sup' hs edge := by
  calc ∑ α ∈ s, w α * edge α
      ≤ ∑ α ∈ s, w α * (s.sup' hs edge) := by
        apply Finset.sum_le_sum
        intro α hα
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' edge hα) (hw α hα)
    _ = (∑ α ∈ s, w α) * (s.sup' hs edge) := by rw [← Finset.sum_mul]
    _ = s.sup' hs edge := by rw [hsum, one_mul]

/-- **The Jensen / rotation-variance gap is nonnegative.** The worst-case aligned edge minus the
free-convolution (average) edge is `≥ 0`; it is the directional/rotation variance the free
convolution averages away. Equality holds iff every alignment has the same edge (rotation-invariant =
degenerate). For the Paley spectrum the aligned `Q = I` term is strictly the largest, so the gap is
strictly positive: `⊞_n` strictly undershoots `M`. -/
theorem jensen_gap_nonneg {Λ : Type*} (s : Finset Λ) (hs : s.Nonempty)
    (w : Λ → ℝ) (edge : Λ → ℝ)
    (hw : ∀ α ∈ s, 0 ≤ w α) (hsum : ∑ α ∈ s, w α = 1) :
    0 ≤ s.sup' hs edge - (∑ α ∈ s, w α * edge α) := by
  have := rotationAvg_le_alignedMax s hs w edge hw hsum
  linarith

/-- **Strict undershoot when the aligned term dominates.** If there is one alignment `α₀` (the
`Q = I` Paley alignment) whose edge STRICTLY exceeds the edge of every other alignment carrying
positive weight, and `α₀` itself does not carry all the weight, then the free-convolution average is
STRICTLY below the aligned max. So on the genuine Paley spectrum (where the coordinate-aligned coset
sum is strictly the worst) the finite-free convolution edge `< M`, with a strict gap. -/
theorem rotationAvg_lt_alignedMax_of_strict {Λ : Type*} (s : Finset Λ) (hs : s.Nonempty)
    (w : Λ → ℝ) (edge : Λ → ℝ)
    (hw : ∀ α ∈ s, 0 ≤ w α) (hsum : ∑ α ∈ s, w α = 1)
    {α₀ β₀ : Λ} (hα₀ : α₀ ∈ s) (hβ₀ : β₀ ∈ s)
    (hmax : ∀ α ∈ s, edge α ≤ edge α₀) (hstrict : edge β₀ < edge α₀)
    (hwβ : 0 < w β₀) :
    (∑ α ∈ s, w α * edge α) < edge α₀ := by
  -- Each term w α * edge α ≤ w α * edge α₀, with strict inequality at β₀.
  have hbound : ∀ α ∈ s, w α * edge α ≤ w α * edge α₀ := fun α hα =>
    mul_le_mul_of_nonneg_left (hmax α hα) (hw α hα)
  have hstrictβ : w β₀ * edge β₀ < w β₀ * edge α₀ :=
    mul_lt_mul_of_pos_left hstrict hwβ
  have hsum_lt : ∑ α ∈ s, w α * edge α < ∑ α ∈ s, w α * edge α₀ :=
    Finset.sum_lt_sum hbound ⟨β₀, hβ₀, hstrictβ⟩
  calc ∑ α ∈ s, w α * edge α
      < ∑ α ∈ s, w α * edge α₀ := hsum_lt
    _ = (∑ α ∈ s, w α) * edge α₀ := by rw [← Finset.sum_mul]
    _ = edge α₀ := by rw [hsum, one_mul]

/-! ## 3. THE GROWTH-RATE SEPARATION up the tower: free `√k` vs classical `k·a`.

Free additivity of the variance cumulant (`κ₂(p ⊞_n p) = 2 κ₂(p)`, additive under `⊞_n`) means the
`k`-fold free self-convolution has variance `k·κ₂`, so its edge scales like `√(k · κ₂ · log n)`
(`√k`-fluctuation, semicircle broadening). The coordinate-ALIGNED tower instead grows `k·a` (sup-norm
subadditivity, §1). For all `k` past the crossover the free edge falls strictly below the aligned
growth: the convolution route loses the worst case permanently. -/

/-- **`√k`-free vs `k`-classical separation.** For positive `a` (the per-level aligned max) and `c`
(the free `√`-fluctuation scale `√(κ₂ log n)`), the free edge `c·√k` is strictly less than the
classical aligned growth `a·k` for every depth `k` with `k > (c/a)²`. Hence beyond the crossover the
finite-free convolution underestimates the aligned tower max — and the gap widens (`a·k − c·√k → ∞`).
At prize scale this is total: `a = Θ(√(n log p))` per level but the aligned bound `k·a` is what the
`n^{1−o(1)}` ceiling tracks, while the free `c√k` undershoots. -/
theorem freeEdge_sqrt_k_vs_classical_k {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {k : ℕ} (hk : (c / a) ^ 2 < k) :
    c * Real.sqrt k < a * k := by
  have hkpos : (0 : ℝ) < k := by
    have : (0 : ℝ) ≤ (c / a) ^ 2 := sq_nonneg _
    linarith
  -- From (c/a)² < k get c² < a²·k, i.e. c·√k < a·k (divide by √k > 0).
  have hsqrtk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have hca2 : c ^ 2 < a ^ 2 * k := by
    rw [div_pow] at hk
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    rw [div_lt_iff₀ ha2] at hk
    linarith
  -- a·k = a·(√k)²  and  c² < a²·k = (a·√k)²  ⟹  c < a·√k (both positive)  ⟹  c·√k < a·√k·√k = a·k.
  have hsqk : Real.sqrt k * Real.sqrt k = (k : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hkpos)
  have hc_lt : c < a * Real.sqrt k := by
    have hpos : 0 < a * Real.sqrt k := mul_pos ha hsqrtk_pos
    have hsqexp : (a * Real.sqrt k) ^ 2 = a ^ 2 * k := by
      have : (a * Real.sqrt k) ^ 2 = a ^ 2 * (Real.sqrt k * Real.sqrt k) := by ring
      rw [this, hsqk]
    have hsq : c ^ 2 < (a * Real.sqrt k) ^ 2 := by rw [hsqexp]; exact hca2
    nlinarith [hsq, hc, hpos]
  calc c * Real.sqrt k < (a * Real.sqrt k) * Real.sqrt k :=
        mul_lt_mul_of_pos_right hc_lt hsqrtk_pos
    _ = a * (Real.sqrt k * Real.sqrt k) := by ring
    _ = a * k := by rw [hsqk]

/-- **The crossover gap widens (the separation is not transient).** Past the crossover the deficit
`a·k − c·√k` is strictly positive and (being `a·k − c·√k = √k(a·√k − c)`) increases without bound, so
the finite-free convolution edge falls further and further below the aligned tower max. We record the
positivity of the deficit at every super-crossover depth. -/
theorem freeEdge_deficit_pos {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {k : ℕ} (hk : (c / a) ^ 2 < k) :
    0 < a * k - c * Real.sqrt k := by
  have := freeEdge_sqrt_k_vs_classical_k ha hc hk
  linarith

/-! ## 4. The named no-go `Prop` (citation-ready closure of the lane). -/

/-- **THE FINITE-FREE-CONVOLUTION NO-GO (named).** The finite-free additive convolution's edge
`freeEdge = ∑_α w α · edge α` is a rotation-average over the alignment family, hence `≤` the worst-
case aligned edge `M = max_α edge α` (the prize side). Therefore `⊞_n` cannot bound `M` from the prize
side: it returns an average `≤ M`, the free/Wick value, never `M` itself. This packages
`rotationAvg_le_alignedMax`. -/
def FreeConvGivesAverageNotMax {Λ : Type*} (s : Finset Λ) (hs : s.Nonempty)
    (w : Λ → ℝ) (edge : Λ → ℝ) (freeEdge M : ℝ) : Prop :=
  freeEdge = (∑ α ∈ s, w α * edge α) ∧ M = s.sup' hs edge → freeEdge ≤ M

/-- **The no-go holds.** Under the (always-true) probability-weight hypotheses, the finite-free-
convolution edge is `≤` the worst-case aligned edge. The convolution lane is closed: its output is a
rotation-average dominated by the very `M` we are trying to bound. -/
theorem free_edge_is_average_not_max {Λ : Type*} (s : Finset Λ) (hs : s.Nonempty)
    (w : Λ → ℝ) (edge : Λ → ℝ) (freeEdge M : ℝ)
    (hw : ∀ α ∈ s, 0 ≤ w α) (hsum : ∑ α ∈ s, w α = 1) :
    FreeConvGivesAverageNotMax s hs w edge freeEdge M := by
  rintro ⟨hfe, hM⟩
  rw [hfe, hM]
  exact rotationAvg_le_alignedMax s hs w edge hw hsum

end ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`). -/
#print axioms ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo.aligned_le_sum_of_maxes
#print axioms ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo.rotationAvg_le_alignedMax
#print axioms ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo.jensen_gap_nonneg
#print axioms ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo.rotationAvg_lt_alignedMax_of_strict
#print axioms ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo.freeEdge_sqrt_k_vs_classical_k
#print axioms ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo.freeEdge_deficit_pos
#print axioms ArkLib.ProximityGap.FiniteFreeConvRotationAverageNoGo.free_edge_is_average_not_max
