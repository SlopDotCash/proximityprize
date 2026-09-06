/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The second-order / single-moment no-go meta-theorem for the δ* floor (#407)

This is the **abstract, family-independent** core of the issue's "§3 meta-theorem" (comment
`STATE OF THE PRIZE`, and the consolidated `the open core is irreducibly a high-moment statement`):
**no method that bounds the sup-norm of a real family through a *single* even moment of that family
can beat the trivial second-moment bound `√S`** — so the prize floor cannot be proved by any such
method; it genuinely requires the cross-moment / additive-combinatorial (BGK) input.

Let `η : ι → ℝ` be a finite family with second moment `S = ∑_i (η i)²`. The standard ladder
(`MomentSupNormBridge.sup_le_moment_root`) gives, for every depth `r ≥ 1`,

    `max_i |η i| ≤ (∑_i (η i)^{2r})^{1/(2r)}`,                                (the moment route)

and at `r = 1` this is exactly the trivial second-moment bound `max ≤ √S`. The content here is the
**matching lower obstruction**: the *spike* family `η' = (√S, 0, …, 0)` has

    `∑_i (η' i)^{2r} = S^r`   for every `r ≥ 1`,   and   `max_i |η' i| = √S`,

so **every rung of the ladder is flat at `√S` for the spike**. Consequently:

* `secondMoment_method_floor` — any `g : ℝ → ℝ` with `∀ η b, |η b| ≤ g (∑ (η i)²)` satisfies
  `g S ≥ √S`. (No second-moment-only method beats `√S`.)
* `momentDepth_method_floor` — for *every* fixed depth `r ≥ 1`, any `g` with
  `∀ η b, |η b| ≤ g (∑ (η i)^{2r})` satisfies `g (S^r) ≥ √S`. (No *single*-depth moment method
  beats `√S`, at any order — the spike is the universal obstruction.)

The point for the prize: a moment bound helps **only** through the *smallness of the moment value*
(the family being far from a spike); for the Gauss periods that smallness IS the open char-`p`
BGK/Shkredov statement (`SubgroupGaussSumRawMoment`, `MomentMethodNoGo`). This file proves, with no
hypotheses on `η`, that depth alone never helps — formalizing "every route through one moment funnels
to the same √-cancellation wall."

Complementary already-proven facts (not re-proved here): the ladder is *valid*
(`MomentSupNormBridge.sup_le_moment_root`) and, for the periods, `(p·E_r)^{1/2r} ≥ n` always
(`Frontier.MomentMethodNoGo.moment_bound_ge_card`) — so even the *best* the ladder can give on the
periods is `≥ n`, never the target `√(n log q)`.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.MetaTheoremSecondOrderFloor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The per-term second-moment ceiling (the trivial `r = 1` bound) -/

/-- **The trivial second-moment ceiling.** Every term of a real family is bounded by the square
root of the second moment: `|η b| ≤ √(∑_i (η i)²)`. This is the `r = 1` rung of the moment ladder
and the strongest bound any *second-moment-only* method can hope for. -/
theorem abs_le_sqrt_secondMoment (η : ι → ℝ) (b : ι) :
    |η b| ≤ Real.sqrt (∑ i, (η i) ^ 2) := by
  have hterm : (η b) ^ 2 ≤ ∑ i, (η i) ^ 2 :=
    Finset.single_le_sum (f := fun i => (η i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ b)
  calc |η b| = Real.sqrt ((η b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, (η i) ^ 2) := Real.sqrt_le_sqrt hterm

/-! ### The spike family — the universal obstruction -/

/-- The single-support family `single b₀ v` with value `v` at `b₀` and `0` elsewhere. The *spike*
that saturates the second-moment bound is `single b₀ (√S)`. -/
def single (b₀ : ι) (v : ℝ) : ι → ℝ := fun i => if i = b₀ then v else 0

@[simp] theorem single_at (b₀ : ι) (v : ℝ) : single b₀ v b₀ = v := by simp [single]

/-- **Every positive power sum of the single-support family collapses to one term:**
`∑_i (single b₀ v i)^k = v^k` for `k ≥ 1`. -/
theorem single_pow_sum (b₀ : ι) (v : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ i, (single b₀ v i) ^ k = v ^ k := by
  rw [Finset.sum_eq_single b₀]
  · simp [single]
  · intro j _ hj
    simp only [single, if_neg hj]
    exact zero_pow (by omega)
  · intro h; exact absurd (Finset.mem_univ b₀) h

/-- **Spike second moment.** With `v = √S` and `S ≥ 0`, the spike has second moment exactly `S`. -/
theorem spike_secondMoment (b₀ : ι) {S : ℝ} (hS : 0 ≤ S) :
    ∑ i, (single b₀ (Real.sqrt S) i) ^ 2 = S := by
  rw [single_pow_sum b₀ _ (by norm_num), Real.sq_sqrt hS]

/-- **Spike depth-`r` moment.** With `v = √S`, `S ≥ 0` and `r ≥ 1`, the `2r`-th moment of the spike
is exactly `S^r` — independent of the depth `r`. This is the flat ladder: every rung sees `S^r`. -/
theorem spike_momentPow (b₀ : ι) {S : ℝ} (hS : 0 ≤ S) {r : ℕ} (hr : 1 ≤ r) :
    ∑ i, (single b₀ (Real.sqrt S) i) ^ (2 * r) = S ^ r := by
  rw [single_pow_sum b₀ _ (by omega)]
  rw [pow_mul, Real.sq_sqrt hS]

/-- **Spike sup-norm.** The spike attains `|·| = √S` at its support point. -/
theorem spike_abs (b₀ : ι) {S : ℝ} (hS : 0 ≤ S) :
    |single b₀ (Real.sqrt S) b₀| = Real.sqrt S := by
  rw [single_at]; exact abs_of_nonneg (Real.sqrt_nonneg S)

/-! ### The meta-theorem: no single-moment method beats `√S` -/

variable [Nonempty ι]

/-- **No second-moment-only method beats the trivial bound.** If `g : ℝ → ℝ` is *any* function such
that the second moment alone certifies the sup-norm bound — `∀ η b, |η b| ≤ g (∑_i (η i)²)` — then
necessarily `g S ≥ √S` for every `S ≥ 0`. So no method depending only on the second moment can prove
`max < √S`; in particular it cannot reach the prize target `√(n·log(q/n)) ≪ √S`. The witness is the
spike. -/
theorem secondMoment_method_floor (g : ℝ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ 2))
    {S : ℝ} (hS : 0 ≤ S) :
    Real.sqrt S ≤ g S := by
  obtain ⟨b₀⟩ := ‹Nonempty ι›
  have h := hg (single b₀ (Real.sqrt S)) b₀
  rwa [spike_abs b₀ hS, spike_secondMoment b₀ hS] at h

/-- **No single-depth moment method beats the trivial bound — at any order `r`.** For every fixed
depth `r ≥ 1`, if `g : ℝ → ℝ` certifies the sup-norm bound from the depth-`r` moment alone —
`∀ η b, |η b| ≤ g (∑_i (η i)^{2r})` — then `g (S^r) ≥ √S` for every `S ≥ 0`. Since the spike's
depth-`r` moment is `S^r` *for every* `r`, increasing the depth never lowers the achievable bound
below `√S`: a moment method can only help through the moment *value* being small (the family being
far from a spike), which for the Gauss periods is precisely the open BGK char-`p` input. -/
theorem momentDepth_method_floor {r : ℕ} (hr : 1 ≤ r) (g : ℝ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r)))
    {S : ℝ} (hS : 0 ≤ S) :
    Real.sqrt S ≤ g (S ^ r) := by
  obtain ⟨b₀⟩ := ‹Nonempty ι›
  have h := hg (single b₀ (Real.sqrt S)) b₀
  rwa [spike_abs b₀ hS, spike_momentPow b₀ hS hr] at h

/-! ### The prize instantiation: the second-moment method is `√q`-lossy on the Gauss periods -/

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodParsevalFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **No second-moment method pins the prize per-frequency core.** Feeding the Gauss-period family
`(‖η_b‖)_{b≠0}` to *any* valid second-moment method `g` (one obeying `|f c| ≤ g (∑ (f i)²)` for every
real family on the nonzero frequencies) returns a bound `≥ √(q·n − n²) ≈ √(n·q)`. Since the prize
floor target is `C·√(n·log(q/n)) ≪ √(n·q)` (off by the full `√q` factor in the prize regime
`q/n = 2¹²⁸`), the second-moment method provably **cannot** reach it. The periods themselves are flat
(`max ≈ √(n log q)`), but a method that sees only the second moment cannot tell them from the spike,
so it must pay `√S`. This is the per-frequency face of the issue's meta-theorem: the floor needs a
genuine cross-moment / BGK input, not any `L²` mass bound. -/
theorem periods_secondMoment_method_floor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 2 ≤ Fintype.card F)
    (hGF : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) * G.card)
    (g : ℝ → ℝ)
    (hg : ∀ (f : {b : F // b ≠ 0} → ℝ) (c : {b : F // b ≠ 0}), |f c| ≤ g (∑ i, (f i) ^ 2)) :
    Real.sqrt ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
      ≤ g (∑ i : {b : F // b ≠ 0}, ‖eta ψ G i.val‖ ^ 2) := by
  haveI : Nontrivial F := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : Nonempty {b : F // b ≠ 0} := by
    obtain ⟨b, hb⟩ := exists_ne (0 : F); exact ⟨⟨b, hb⟩⟩
  -- the period family's second moment over the nonzero frequencies is `q·n − n²`
  have hsum : ∑ i : {b : F // b ≠ 0}, ‖eta ψ G i.val‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    rw [← sum_sq_erase_zero hψ G]
    refine (Finset.sum_subtype (Finset.univ.erase (0 : F)) ?_ (fun b => ‖eta ψ G b‖ ^ 2)).symm
    intro x; simp [Finset.mem_erase]
  rw [hsum]
  exact secondMoment_method_floor (ι := {b : F // b ≠ 0}) g hg (by linarith [hGF])

end ProximityGap.Frontier.MetaTheoremSecondOrderFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.MetaTheoremSecondOrderFloor.abs_le_sqrt_secondMoment
#print axioms ProximityGap.Frontier.MetaTheoremSecondOrderFloor.secondMoment_method_floor
#print axioms ProximityGap.Frontier.MetaTheoremSecondOrderFloor.momentDepth_method_floor
#print axioms ProximityGap.Frontier.MetaTheoremSecondOrderFloor.periods_secondMoment_method_floor
