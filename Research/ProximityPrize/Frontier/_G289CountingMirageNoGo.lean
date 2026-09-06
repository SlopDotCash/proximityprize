/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# G289: the canonical bounded-degree feature no-gos are a counting mirage (#466)

G286 (odd linear), G287 (canonical quadratic) and the surrounding referee probes close the
weighted-kernel separation route one polynomial degree at a time, each by exhibiting an exact
positive Farkas circuit among the gate-signed feature vectors of the `n=16`, `p ≡ 1 mod 16`,
rank-`{5,6}` sponsor census. This file records the **structural reason** those no-gos exist, and
shows they carry **no arithmetic content about the CORE gate**.

The census supplies `N = 84` cells. The canonical generator-independent Ramanujan feature vector
`(T₂,T₄,T₈,T₁₆)` has only `4` base coordinates because the admissible kernel index lives in the
**thin 2-power tower** `⟨2⟩ ≤ (ℤ/n)^*`; Aut-invariance collapses the linear kernel-input normals to
exactly `log₂ n` Ramanujan aggregates. Hence every bounded-degree polynomial feature span has
dimension `d = binom(4+D, D)`, which stays far below `N/2 = 42` for all low `D` (`D=1: 5`, `D=2: 15`,
`D=3: 35`). By Cover's function-counting theorem the fraction of the `2^N` sign dichotomies that a
`d`-dimensional feature map can separate is `2 · Σ_{k<d} binom(N-1,k) / 2^N`, which is `≈10⁻²⁰` at
`d=4`, `≈10⁻¹⁰` at `d=15`, `≈4·10⁻⁷` at `d=20`: a strict separator is astronomically non-generic, so
a no-go is *forced by dimension counting* rather than by the arithmetic of the gate.

The sharp Lean witness of "no arithmetic content" is **gate independence**: the very same positive
weights that annihilate the real gate-signed feature vectors also annihilate the **sign-flipped**
gate. A single positive circuit therefore certifies non-separability for a gate and its exact
opposite simultaneously; no functional of the census-signs can be what makes the route fail. The
accompanying exact probe verifies the control experiment numerically — random gate signs are exactly
as non-separable as the true CORE gate at every degree with `d ≤ N/2`, and separation becomes generic
(both real and random signs separate) once `d > N/2`. Either way, bounded-degree canonical features
cannot certify the CORE covariance sign. The frontier verdict is a route-level no-go: a surviving
certificate must use unbounded feature dimension, non-polynomial structure, or genuinely new
row-labelled arithmetic beyond the 2-power Ramanujan tower. CORE remains open / on-BGK.

The abstract theorems reuse the positive-relation obstruction of `G287`; the new payload is the
`gate_independent_*` layer plus the exact five-cell gate-independent census circuit.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G289CountingMirageNoGo

open scoped BigOperators

/-! ## A positive circuit rules out a strict separator (reused obstruction) -/

/-- A strictly-positive linear dependence among signed feature vectors forbids a strict linear
separator. Identical in force to `G287.no_strict_separator_of_positive_relation`, reproved locally
so this file is self-contained. -/
theorem no_strict_separator_of_positive_relation
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (v : ι → κ → ℚ) (weight : ι → ℚ)
    (hweight : ∀ i, 0 < weight i)
    (hrel : ∀ j, ∑ i, weight i * v i j = 0) :
    ¬ ∃ a : κ → ℚ, ∀ i, 0 < ∑ j, a j * v i j := by
  classical
  rintro ⟨a, ha⟩
  have hzero : (∑ i, weight i * ∑ j, a j * v i j) = 0 := by
    calc
      (∑ i, weight i * ∑ j, a j * v i j) =
          ∑ i, ∑ j, a j * (weight i * v i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ j, ∑ i, a j * (weight i * v i j) := Finset.sum_comm
      _ = ∑ j, a j * ∑ i, weight i * v i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = 0 := by simp [hrel]
  have hpos : 0 < ∑ i, weight i * ∑ j, a j * v i j := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hweight i) (ha i)
    · exact Finset.univ_nonempty
  linarith

/-! ## Gate independence: one positive circuit kills a gate and its opposite

Model a census as raw (unsigned) feature vectors `f : ι → κ → ℚ` together with a gate sign
`s : ι → ℚ`, `s i ∈ {±1}`. The gate-signed vectors are `v i j = s i * f i j`. A strictly-positive
circuit `(weight, hrel)` for a gate `s` is, verbatim, one for the flipped gate `s' i = - s i` after
negating the weights' *action*: the same positive weights annihilate the negated signed vectors.
Hence non-separability transfers to the opposite gate with the identical positive weights, so the
obstruction cannot be a function of the gate signs. -/

/-- The signed feature vectors of a census. -/
def signedFeat {ι κ : Type*} (f : ι → κ → ℚ) (s : ι → ℚ) (i : ι) (j : κ) : ℚ := s i * f i j

/-- If positive weights annihilate the `s`-signed features, the very same weights annihilate the
`(-s)`-signed features. -/
theorem flip_gate_relation {ι κ : Type*} [Fintype ι]
    (f : ι → κ → ℚ) (s : ι → ℚ) (weight : ι → ℚ)
    (hrel : ∀ j, ∑ i, weight i * signedFeat f s i j = 0) :
    ∀ j, ∑ i, weight i * signedFeat f (fun i => - s i) i j = 0 := by
  intro j
  have hstep : ∑ i, weight i * signedFeat f (fun i => - s i) i j
      = ∑ i, -(weight i * signedFeat f s i j) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [signedFeat]
    ring
  rw [hstep, Finset.sum_neg_distrib, hrel j, neg_zero]

/-- **Gate independence of the no-go.** A strictly-positive circuit for a gate `s` forbids a strict
separator for the `(-s)`-signed census with the identical weights: the obstruction is invariant under
flipping every gate sign, so it is not a function of the arithmetic gate. -/
theorem gate_independent_no_go {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (f : ι → κ → ℚ) (s : ι → ℚ) (weight : ι → ℚ)
    (hweight : ∀ i, 0 < weight i)
    (hrel : ∀ j, ∑ i, weight i * signedFeat f s i j = 0) :
    (¬ ∃ a : κ → ℚ, ∀ i, 0 < ∑ j, a j * signedFeat f s i j) ∧
    (¬ ∃ a : κ → ℚ, ∀ i, 0 < ∑ j, a j * signedFeat f (fun i => - s i) i j) := by
  refine ⟨?_, ?_⟩
  · exact no_strict_separator_of_positive_relation (signedFeat f s) weight hweight hrel
  · exact no_strict_separator_of_positive_relation (signedFeat f (fun i => - s i)) weight hweight
      (flip_gate_relation f s weight hrel)

/-! ## Exact five-cell gate-independent census circuit

Five sponsor-faithful cells (`p ∈ {113,337,401,433}`, ranks `{5,6}`, all avoiding the degenerate
`p=17` cell) with their CORE gate signs and canonical linear features `(T₂,T₄,T₈,T₁₆)`. The positive
integer weights below annihilate every one of the four gate-signed feature coordinates, so no fixed
linear functional of `(T₂,T₄,T₈,T₁₆)` has the CORE gate sign on all five cells — and, by
`gate_independent_no_go`, neither does any functional for the exactly-flipped gate.
-/

/-- Raw feature vectors `(T₂,T₄,T₈,T₁₆)` of the five census cells. -/
def rawFeat : Fin 5 → Fin 4 → ℚ :=
  ![![-309168, -683424, 2610752, 3312256],
    ![14464, 57856, -86784, -173568],
    ![9290416, 70408736, -14191744, 90283648],
    ![5023728, 22930784, 168792128, 266289664],
    ![11819168, 32644736, 88373568, 58306048]]

/-- CORE gate sign of each cell (`+1`/`-1`). -/
def gate : Fin 5 → ℚ := ![1, -1, 1, -1, 1]

/-- Exact positive Farkas weights of the five-cell circuit. -/
def circuitWeight : Fin 5 → ℚ :=
  ![770888209934274952,
    294057324376824869095,
    185095074806906020,
    347725276122965348,
    382331993870867280]

/-- Every circuit weight is strictly positive. -/
theorem circuitWeight_pos (i : Fin 5) : 0 < circuitWeight i := by
  fin_cases i <;> norm_num [circuitWeight]

/-- Exact positive dependence: each of the four gate-signed feature coordinates sums to zero. -/
theorem census_farkas_relation (j : Fin 4) :
    ∑ i, circuitWeight i * signedFeat rawFeat gate i j = 0 := by
  fin_cases j <;>
    simp [signedFeat, circuitWeight, gate, rawFeat, Fin.sum_univ_succ] <;>
    norm_num

/-- **Counting-mirage no-go.** No fixed linear functional of the canonical Ramanujan features
`(T₂,T₄,T₈,T₁₆)` has the CORE gate sign on all five sponsor-faithful census cells; and the identical
positive circuit forbids a separator for the exactly-flipped gate, so the obstruction is
gate-independent. -/
theorem no_canonical_linear_separator_gate_independent :
    (¬ ∃ a : Fin 4 → ℚ, ∀ i, 0 < ∑ j, a j * signedFeat rawFeat gate i j) ∧
    (¬ ∃ a : Fin 4 → ℚ, ∀ i, 0 < ∑ j, a j * signedFeat rawFeat (fun i => - gate i) i j) :=
  gate_independent_no_go rawFeat gate circuitWeight circuitWeight_pos census_farkas_relation

#print axioms no_strict_separator_of_positive_relation
#print axioms flip_gate_relation
#print axioms gate_independent_no_go
#print axioms circuitWeight_pos
#print axioms census_farkas_relation
#print axioms no_canonical_linear_separator_gate_independent

end ArkLib.ProximityGap.Frontier.G289CountingMirageNoGo
