/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MetaTheoremSecondOrderFloor

/-!
# The "no tighter bound from any direction" capstone (#407 / #444)

This file is the Lean delivery of the original #407 directive — *prove that the BGK/Paley
character-sum wall IS the bound on `δ*`, and that no tighter bound is reachable from any direction*.

After three independent grinds (≈46 reduce-to-wall verdicts across moment / energy / EVT / count /
uncertainty / 10 exotic-ANT lenses / 6 bold-conjecture fresh domains), the #444 synthesis is a
**3-property necessary condition**: any functional that bounds the per-frequency core
`M(n) = max_{b≠0} ‖η_b‖` of the Gauss-period family must be simultaneously

1. **b-sensitive** — it must depend on the frequency `b` (not a `b`-invariant statistic);
2. **deterministic-archimedean** — it must hold for the *deterministic* subgroup, not borrow an
   ensemble/independence/freeness the fixed subgroup lacks;
3. **genuinely `L∞`** — it must control the supremum, not merely an `L²`/RMS average.

Every classical and fresh tool fails at least one of the three. This file formalizes the two
machine-checkable faces of that condition and names the third:

- **Failure mode (3) — only `L²`/RMS.** `MetaTheoremSecondOrderFloor.momentDepth_method_floor`
  (re-exported): for *every* fixed depth `r`, a method reading only the depth-`r` moment is floored
  at the trivial `√S` by the spike — it cannot reach `√(n log m) ≪ √S`. (The per-frequency prize
  instantiation is `periods_secondMoment_method_floor`.)
- **Failure mode (1) — `b`-invariance.** `secondMoment_does_not_determine_sup` (NEW, proven here):
  two explicit real families with *identical first and second moments* but a strictly larger
  coordinate in one. So a `b`-symmetric statistic (anything determined by the moment data, which is
  permutation-invariant in `b`) **cannot determine the sup** — it is blind to the worst-case `b`.
- **Failure mode (2) — absent randomness.** Left as the named open `EVTConcentration`
  (`_EVTFloorRoute`): the i.i.d.-Gaussian extreme-value heuristic `M ≈ √(n log m)` is not a theorem
  for the *deterministic* Gauss periods; proving it is the BGK/Paley wall itself.

**Honest scope.** Nothing here closes the prize. The capstone is a *negative* structural statement:
the proven floors (failure modes 1, 3) show the symmetric-moment / `L²` directions provably cannot
reach the prize target, and the one open input (failure mode 2 = `EVTConcentration` = the char-`p`
`A_r ≤ Wick` validity at depth `r ≈ ln q` = `M(n) ≤ C√(n log m)`) is exactly the BGK/Paley
√-cancellation wall at the Burgess barrier. Axiom-clean. Issues #407, #444.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.NoTighterBoundCapstone

open ProximityGap.Frontier.MetaTheoremSecondOrderFloor

/-! ## Failure mode (1): `b`-invariance — symmetric moment data cannot determine the sup -/

/-- The "concentrated" witness `η = (√2, −√2, 0, 0)` on `Fin 4`. -/
noncomputable def etaConc : Fin 4 → ℝ := ![Real.sqrt 2, -Real.sqrt 2, 0, 0]

/-- The "spread" witness `η' = (1, 1, −1, −1)` on `Fin 4`. -/
def etaSpread : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- **`b`-invariance obstruction (failure mode 1).** There are two real families on the frequency
index set `Fin 4` with *identical first moments* (`∑ η = ∑ η'`) and *identical second moments*
(`∑ η² = ∑ η'²`), yet one has a coordinate strictly larger in absolute value than *every* coordinate
of the other. Concretely `η = (√2,−√2,0,0)` and `η' = (1,1,−1,−1)`: both have sum `0` and second
moment `4`, but `|η 0| = √2 > 1 = |η' j|` for all `j`.

Consequence: any functional determined by the first and second moments — i.e. any `b`-symmetric
statistic — assigns `η` and `η'` the *same* value and therefore **cannot determine the supremum**
`max_b |η_b|` (which is `√2` for `η` and `1` for `η'`). A bound on the worst-case frequency `b` must
genuinely depend on `b`; this is the formal content of "the method must be `b`-sensitive". -/
theorem secondMoment_does_not_determine_sup :
    ∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
      (∑ i, η i = ∑ i, η' i) ∧
      (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
      (∀ j, |η' j| < |η b₀|) := by
  refine ⟨etaConc, etaSpread, 0, ?_, ?_, ?_⟩
  · -- first moments both 0
    simp [etaConc, etaSpread, Fin.sum_univ_four]
  · -- second moments both 4
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [etaConc, etaSpread, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [neg_pow, h2]
    norm_num
  · -- |η 0| = √2 > 1 = |η' j| for every j
    have hsqrt2 : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hb0 : |etaConc 0| = Real.sqrt 2 := by
      simp [etaConc, abs_of_nonneg (Real.sqrt_nonneg 2)]
    intro j
    rw [hb0]
    fin_cases j <;> simp [etaSpread] <;> linarith [hsqrt2]

/-! ### Strengthening failure mode (1): even matching moments through order 4 (and 5) leaves the sup undetermined

The witness above matches only the first two moments.  A skeptic could ask whether *adding* the
fourth moment (the `r = 2` depth, `∑ η^4`) — or any fixed bundle of low-order symmetric power sums —
lets a `b`-symmetric statistic recover the sup.  It does not.  The pair below is an *ideal*
Prouhet-Tarry-Escott solution: two nonnegative families on `Fin 6` with **identical power sums of
orders 1, 2, 3, 4 and 5**, yet a strictly larger maximal coordinate in one.  Hence no functional
determined by the symmetric moment data up to order `5` (in particular the depth-`1` `∑η^2` *and*
depth-`2` `∑η^4` even-moment methods simultaneously) can determine `max_b |η_b|`. -/

/-- The PTE family `A = (0,5,6,16,17,22)` on `Fin 6`. -/
def etaPTEa : Fin 6 → ℝ := ![0, 5, 6, 16, 17, 22]

/-- The PTE family `B = (1,2,10,12,20,21)` on `Fin 6`. -/
def etaPTEb : Fin 6 → ℝ := ![1, 2, 10, 12, 20, 21]

/-- **Strengthened `b`-invariance obstruction (failure mode 1, through the 4th/5th moment).**
There are two nonnegative real families on `Fin 6` whose power sums of orders `1, 2, 3, 4, 5` all
coincide, yet one has a coordinate strictly larger in absolute value than *every* coordinate of the
other.  Concretely `A = (0,5,6,16,17,22)` and `B = (1,2,10,12,20,21)` (an ideal Prouhet-Tarry-Escott
pair): both share the power sums `66, 1090, 19998, 385234, 7632966` for exponents `1..5`, but
`|A 5| = 22 > 21 ≥ |B j|` for every `j`.

Consequence: **even a method that reads the full symmetric moment data up to order `5`** — in
particular *both* the second moment `∑η^2` (depth `r=1`) and the fourth moment `∑η^4` (depth `r=2`) —
assigns `A` and `B` the same value and therefore cannot determine the supremum `max_b |η_b|`
(`22` for `A`, `21` for `B`).  Adding more low-order moments does not rescue a `b`-symmetric statistic;
the sensitivity to the worst frequency `b` is genuinely beyond any fixed-order moment bundle.  This
strictly strengthens `secondMoment_does_not_determine_sup` (which matched only orders `1,2`). -/
theorem moments_through_five_do_not_determine_sup :
    ∃ (η η' : Fin 6 → ℝ) (b₀ : Fin 6),
      (∑ i, η i = ∑ i, η' i) ∧
      (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
      (∑ i, (η i) ^ 3 = ∑ i, (η' i) ^ 3) ∧
      (∑ i, (η i) ^ 4 = ∑ i, (η' i) ^ 4) ∧
      (∑ i, (η i) ^ 5 = ∑ i, (η' i) ^ 5) ∧
      (∀ j, |η' j| < |η b₀|) := by
  refine ⟨etaPTEa, etaPTEb, 5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [etaPTEa, etaPTEb, Fin.sum_univ_six, Matrix.cons_val]; norm_num
  · simp only [etaPTEa, etaPTEb, Fin.sum_univ_six, Matrix.cons_val]; norm_num
  · simp only [etaPTEa, etaPTEb, Fin.sum_univ_six, Matrix.cons_val]; norm_num
  · simp only [etaPTEa, etaPTEb, Fin.sum_univ_six, Matrix.cons_val]; norm_num
  · simp only [etaPTEa, etaPTEb, Fin.sum_univ_six, Matrix.cons_val]; norm_num
  · -- |A 5| = 22 > 21 ≥ |B j| for every j
    have hb0 : |etaPTEa 5| = 22 := by
      simp only [etaPTEa, Matrix.cons_val]; norm_num
    intro j
    rw [hb0]
    fin_cases j <;> (simp only [etaPTEb]; norm_num [Matrix.cons_val])

/-! ## Failure mode (3): only `L²`/RMS — re-export the moment-depth floor

For every fixed depth `r ≥ 1`, no method reading only the depth-`r` moment beats the trivial `√S`;
the spike saturates every rung. (Proof: `MetaTheoremSecondOrderFloor.momentDepth_method_floor`.) -/

/-- **Failure mode (3), re-exported.** A method certifying the sup from the depth-`r` moment alone is
floored at `√S` — it cannot reach the prize target. This is `momentDepth_method_floor`, restated at
the capstone so the three failure modes sit in one place. -/
theorem onlyL2_method_floor {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ}
    (hr : 1 ≤ r) (g : ℝ → ℝ) (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r)))
    {S : ℝ} (hS : 0 ≤ S) :
    Real.sqrt S ≤ g (S ^ r) :=
  momentDepth_method_floor (ι := ι) hr g hg hS

/-! ## The capstone statement

The three faces above are the formal "no tighter bound from any direction": failure modes (1) and
(3) are proven (symmetric-moment / `L²` methods provably overshoot), and failure mode (2) is the
single named open input `EVTConcentration` = the BGK/Paley wall. The prize floor is reachable only by
a method that is simultaneously `b`-sensitive, deterministic-archimedean, and genuinely `L∞` — and no
such method is known; producing one is the open analytic-number-theory core. -/

/-- **No-tighter-bound capstone (negative structural theorem).** Packaging the proven faces:

* there exist two families with identical first and second moments but different sup
  (`secondMoment_does_not_determine_sup`) — so a `b`-symmetric statistic cannot see the worst `b`
  (**failure mode 1**, `b`-invariance); and
* for every depth `r ≥ 1` and every depth-`r`-moment method `g`, `g` is floored at `√S`
  (`onlyL2_method_floor`) — so an `L²`/moment method cannot reach `√(n log m) ≪ √S`
  (**failure mode 3**, only-`L²`/RMS).

Together these certify that the symmetric-moment and `L²` directions are provably insufficient; the
remaining direction (a genuinely `b`-sensitive, deterministic, `L∞` method) is the open BGK/Paley
wall, carried elsewhere as the named `EVTConcentration` / `GaussianEnergyBound` char-`p` input. -/
theorem noTighterBound_from_symmetric_or_L2 :
    (∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
        (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
        (∀ j, |η' j| < |η b₀|)) ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ}, 1 ≤ r → ∀ (g : ℝ → ℝ),
        (∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r))) →
        ∀ {S : ℝ}, 0 ≤ S → Real.sqrt S ≤ g (S ^ r)) := by
  refine ⟨secondMoment_does_not_determine_sup, ?_⟩
  intro ι _ _ _ r hr g hg S hS
  exact onlyL2_method_floor hr g hg hS

/-- **No-tighter-bound capstone, STRENGTHENED at failure mode 1.**  Same negative structural statement
as `noTighterBound_from_symmetric_or_L2`, but with the `b`-invariance face sharpened to the
order-`5` Prouhet-Tarry-Escott witness: a `b`-symmetric statistic blind to the sup survives matching
*all* of the first five power sums (not merely the first two).  Bundled with the depth-`r` `L²` floor
for every `r`.  One citation surface for "the symmetric-moment direction provably fails even through
order 5, and the `L²`/RMS direction fails at every depth". -/
theorem noTighterBound_strengthened :
    (∃ (η η' : Fin 6 → ℝ) (b₀ : Fin 6),
        (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
        (∑ i, (η i) ^ 3 = ∑ i, (η' i) ^ 3) ∧ (∑ i, (η i) ^ 4 = ∑ i, (η' i) ^ 4) ∧
        (∑ i, (η i) ^ 5 = ∑ i, (η' i) ^ 5) ∧ (∀ j, |η' j| < |η b₀|)) ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ}, 1 ≤ r → ∀ (g : ℝ → ℝ),
        (∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r))) →
        ∀ {S : ℝ}, 0 ≤ S → Real.sqrt S ≤ g (S ^ r)) := by
  refine ⟨moments_through_five_do_not_determine_sup, ?_⟩
  intro ι _ _ _ r hr g hg S hS
  exact onlyL2_method_floor hr g hg hS

end ProximityGap.Frontier.NoTighterBoundCapstone

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.NoTighterBoundCapstone.secondMoment_does_not_determine_sup
#print axioms ProximityGap.Frontier.NoTighterBoundCapstone.onlyL2_method_floor
#print axioms ProximityGap.Frontier.NoTighterBoundCapstone.noTighterBound_from_symmetric_or_L2
#print axioms ProximityGap.Frontier.NoTighterBoundCapstone.noTighterBound_strengthened
