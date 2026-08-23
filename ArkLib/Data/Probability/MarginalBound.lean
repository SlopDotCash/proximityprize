/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Probability.Instances
import ArkLib.OracleReduction.Security.Basic

/-!
# Marginal domination bricks for run-marginal arguments (issue #13)

Two protocol-independent probability lemmas isolating the measure-theoretic core of the
"run-marginal" walls in the LogUp (and sumcheck) soundness analyses:

* `probEvent_bind_le_of_forall_support` — support-quantified bind domination: if every
  continuation satisfies `Pr[q] ≤ c`, so does the bind.  This is the outer-layer step that peels
  the prover prefix / state initialization off a soundness game.

* `probEvent_bind_le_uniform_marginal` — **uniform-marginal domination**: if the first stage's
  output distribution is dominated by the uniform one (`Pr[= x] ≤ 1/|F|`, true in particular for
  the uniform challenge draw itself), and the event is *supported inside* `L` through the drawn
  value (continuations at `x ∉ L` give the event probability `0`), then the whole game's event
  probability is at most the uniform measure of `L`.  This is exactly the inequality shape of the
  `OuterRunMarginalToUniform` / `hMarginal`-style residuals: the bad-accept probability of a run
  whose acceptance pins the drawn challenge into `L` is bounded by the uniform marginal of `L`.

* `probEvent_bind_le_prob_uniform` — the same bound with the right-hand side packaged as the
  `Pr_{ let x ←$ᵖ F }[ x ∈ L ]` notation used throughout the LogUp security files.

* the `_comap` variants generalize from "the first stage outputs the drawn value" to "the drawn
  value is *carried inside* the first stage's output" — the shape that actually arises when
  decomposing an interactive-protocol run around a challenge query (the stage ending at the
  challenge round outputs a transcript × prover-state pair *containing* the drawn challenge);
  `probEvent_comap_eq_le_of_support_preserve` supplies their `hunif` side condition from the
  uniformity of the middle draw.
-/

open OracleComp OracleSpec ProbabilityTheory
open scoped ENNReal NNReal

universe u v

section MarginalBound

variable {α β : Type u} {m : Type u → Type v} [Monad m] [HasEvalSPMF m]

/-- **Support-quantified bind domination.**  If every continuation reachable from the first stage
satisfies the event bound `≤ c`, then so does the bind. -/
lemma probEvent_bind_le_of_forall_support (mx : m α) (my : α → m β) (q : β → Prop) (c : ℝ≥0∞)
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ c) :
    Pr[ q | mx >>= my] ≤ c := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ q | my x]
      ≤ ∑' x, Pr[= x | mx] * c := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul' le_rfl (h x hx)
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = c := one_mul c

/-- **Uniform-marginal domination (card form).**  If the first stage's output distribution is
dominated by the uniform distribution on a fintype `F`, and the event is supported inside
`L ⊆ F` through the drawn value (the event has probability `0` after drawing any `x ∉ L`),
then the game's event probability is at most `|L| / |F|`. -/
lemma probEvent_bind_le_uniform_marginal {F : Type u} [Fintype F]
    (mx : m F) (k : F → m β) (q : β → Prop) (L : Set F) [DecidablePred (· ∈ L)]
    (hunif : ∀ x : F, Pr[= x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ x : F, x ∉ L → Pr[ q | k x] = 0) :
    Pr[ q | mx >>= k]
      ≤ ((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ q | k x]
      ≤ ∑' x : F, (if x ∈ L then (Fintype.card F : ℝ≥0∞)⁻¹ else 0) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ L
        · rw [if_pos hx]
          exact le_trans (mul_le_mul' (hunif x) probEvent_le_one) (by rw [mul_one])
        · rw [if_neg hx, hsupp x hx, mul_zero]
    _ = ∑ x : F, (if x ∈ L then (Fintype.card F : ℝ≥0∞)⁻¹ else 0) := tsum_fintype _
    _ = ((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [div_eq_mul_inv]

end MarginalBound

section ProbUniform

variable {β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- **Uniform-marginal domination (probability-notation form).**  The same bound as
`probEvent_bind_le_uniform_marginal`, with the right-hand side packaged as the uniform-sampling
probability `Pr_{ let x ←$ᵖ F }[ x ∈ L ]` consumed by the LogUp security interfaces
(`OuterRunMarginalToUniform`, `outerSoundness_sharp`, …). -/
lemma probEvent_bind_le_prob_uniform {F : Type} [Fintype F] [Nonempty F]
    (mx : m F) (k : F → m β) (q : β → Prop) (L : Set F) [DecidablePred (· ∈ L)]
    (hunif : ∀ x : F, Pr[= x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ x : F, x ∉ L → Pr[ q | k x] = 0) :
    Pr[ q | mx >>= k] ≤ Pr_{ let x ←$ᵖ F }[ x ∈ L ] := by
  refine le_trans
    (probEvent_bind_le_uniform_marginal mx k q L hunif hsupp) ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  exact le_refl _

end ProbUniform

section ComapMarginal

variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [HasEvalSPMF m]

/-- **Carried-value marginal domination.**  If the middle stage draws `c ← mc` and every outcome
of the continuation carries the drawn value (`f b = c` on the support), then the probability that
the carried value equals `x` is at most `Pr[= x | mc]`. -/
lemma probEvent_comap_eq_le_of_support_preserve
    (ma : m α) (mc : m γ) (g : α → γ → m β) (f : β → γ) (x : γ)
    (hg : ∀ a c, ∀ b ∈ support (g a c), f b = c) :
    Pr[ fun b => f b = x | ma >>= fun a => mc >>= g a]
      ≤ Pr[= x | mc] := by
  classical
  refine probEvent_bind_le_of_forall_support ma _ _ _ (fun a _ => ?_)
  rw [probEvent_bind_eq_tsum]
  have hz : ∀ c, c ≠ x → Pr[= c | mc] * Pr[ fun b => f b = x | g a c] = 0 := by
    intro c hc
    rw [probEvent_eq_zero (fun b hb => by rw [hg a c b hb]; exact hc), mul_zero]
  rw [tsum_eq_single x hz]
  exact le_trans (mul_le_mul' le_rfl probEvent_le_one) (by rw [mul_one])

/-- **Uniform-marginal domination through a projection (comap form).** -/
lemma probEvent_bind_le_uniform_marginal_comap {F : Type u} [Fintype F]
    (mx : m α) (f : α → F) (k : α → m β) (q : β → Prop) (L : Set F) [DecidablePred (· ∈ L)]
    (hunif : ∀ x : F, Pr[ fun a => f a = x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ a : α, f a ∉ L → Pr[ q | k a] = 0) :
    Pr[ q | mx >>= k]
      ≤ ((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  have hstep1 : Pr[ q | mx >>= k] ≤ Pr[ fun a => f a ∈ L | mx] := by
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases ha : f a ∈ L
    · rw [if_pos ha]
      exact le_trans (mul_le_mul' le_rfl probEvent_le_one) (by rw [mul_one])
    · rw [if_neg ha, hsupp a ha, mul_zero]
  have hpred : (fun a => f a ∈ L) =
      (fun a => ∃ x ∈ Finset.univ.filter (· ∈ L), f a = x) := by
    funext a
    simp only [eq_iff_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      exact ⟨f a, ha, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hstep2 : Pr[ fun a => f a ∈ L | mx]
      ≤ ∑ x ∈ Finset.univ.filter (· ∈ L), Pr[ fun a => f a = x | mx] := by
    rw [hpred]
    exact probEvent_exists_finset_le_sum _ mx _
  refine le_trans hstep1 (le_trans hstep2 ?_)
  calc ∑ x ∈ Finset.univ.filter (· ∈ L), Pr[ fun a => f a = x | mx]
      ≤ ∑ _x ∈ Finset.univ.filter (· ∈ L), (Fintype.card F : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum (fun x _ => hunif x)
    _ = ((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [div_eq_mul_inv]

end ComapMarginal

section ProbUniformComap

variable {α β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- **Uniform-marginal domination through a projection (probability-notation form).** -/
lemma probEvent_bind_le_prob_uniform_comap {F : Type} [Fintype F] [Nonempty F]
    (mx : m α) (f : α → F) (k : α → m β) (q : β → Prop) (L : Set F) [DecidablePred (· ∈ L)]
    (hunif : ∀ x : F, Pr[ fun a => f a = x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ a : α, f a ∉ L → Pr[ q | k a] = 0) :
    Pr[ q | mx >>= k] ≤ Pr_{ let x ←$ᵖ F }[ x ∈ L ] := by
  refine le_trans
    (probEvent_bind_le_uniform_marginal_comap mx f k q L hunif hsupp) ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  exact le_refl _

end ProbUniformComap

/-! ### Axiom audit (issue #13 marginal-domination bricks) -/

#print axioms probEvent_bind_le_of_forall_support
#print axioms probEvent_bind_le_uniform_marginal
#print axioms probEvent_bind_le_prob_uniform
#print axioms probEvent_comap_eq_le_of_support_preserve
#print axioms probEvent_bind_le_uniform_marginal_comap
#print axioms probEvent_bind_le_prob_uniform_comap
