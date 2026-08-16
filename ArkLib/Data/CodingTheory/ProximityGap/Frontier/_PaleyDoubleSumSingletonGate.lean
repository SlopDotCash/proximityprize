/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Double-sum Paley inputs do not directly bound a singleton period

Kim--Yip--Yoo's Paley-graph conjecture is a double-character-sum statement over two large
sets `A,B`.  The #464 Gauss-period core is a worst-case single period.  This file records the
elementary interface obstruction:

* using the double-sum theorem with `B` a singleton violates any nontrivial lower size threshold;
* using a large auxiliary `B` gives an averaged bound, and the best pointwise consequence pays
  the factor `#B`;
* that factor is sharp, by a one-point spike inside `B`.

So a double-sum Paley theorem needs an additional deconvolution/anti-spike theorem before it can
be used as a single-period sup bound.  This complements `_wf9B7_PrizeBGKReductionDirections.lean`,
which records that ordinary BGK/Paley power saving is exponent-wise too weak for the prize.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate

open Finset

/-! ## Size gate: a singleton is not a large second set -/

/-- Both sets in a double-sum input meet the same lower cardinality threshold. -/
def DoubleSumSizeEligible (threshold aCard bCard : Nat) : Prop :=
  threshold <= aCard /\ threshold <= bCard

/-- A single-period specialization has second-set cardinality `1`. -/
def SingletonSecondSetEligible (threshold aCard : Nat) : Prop :=
  DoubleSumSizeEligible threshold aCard 1

/-- If the double-sum theorem has any nontrivial threshold `threshold > 1`, it cannot be
instantiated with a singleton second set. -/
theorem not_singletonSecondSetEligible_of_one_lt_threshold {threshold aCard : Nat}
    (hthreshold : 1 < threshold) :
    ¬ SingletonSecondSetEligible threshold aCard := by
  intro h
  exact Nat.not_lt_of_ge h.2 hthreshold

/-- Integer model of a positive power threshold: `p^epsPow` is larger than `1` as soon as
`p > 1` and the exponent is positive. -/
theorem one_lt_power_threshold {p epsPow : Nat} (hp : 1 < p) (heps : 0 < epsPow) :
    1 < p ^ epsPow := by
  exact Nat.one_lt_pow heps.ne' hp

/-- A positive-power cardinality threshold cannot be used with a singleton second set. -/
theorem not_singletonSecondSetEligible_power_threshold {p epsPow aCard : Nat}
    (hp : 1 < p) (heps : 0 < epsPow) :
    ¬ SingletonSecondSetEligible (p ^ epsPow) aCard :=
  not_singletonSecondSetEligible_of_one_lt_threshold
    (one_lt_power_threshold hp heps)

/-! ## Averaging gate: a large auxiliary set costs its cardinality -/

/-- An averaged auxiliary-set bound at scale `T`: the total mass over `B` is at most
`#B * T`.  This is the abstract output shape of replacing a singleton by a large second set. -/
def AuxiliaryAverageBound {ι : Type*} (score : ι -> ℝ) (B : Finset ι) (T : ℝ) : Prop :=
  B.sum score <= (B.card : ℝ) * T

/-- From a nonnegative averaged auxiliary-set bound, the automatic pointwise consequence is only
`score b <= #B * T`.  The original scale `T` is not recovered. -/
theorem pointwise_le_card_mul_of_average_bound {ι : Type*}
    {score : ι -> ℝ} {B : Finset ι} {T : ℝ} {b : ι}
    (hnonneg : ∀ c : ι, c ∈ B -> 0 <= score c)
    (hb : b ∈ B)
    (havg : AuxiliaryAverageBound score B T) :
    score b <= (B.card : ℝ) * T := by
  have hterm : score b <= B.sum score :=
    Finset.single_le_sum (fun c hc => hnonneg c hc) hb
  exact le_trans hterm havg

/-- The cardinality loss is sharp.  If `B` has more than one point and `T > 0`, a spike at one
point satisfies the averaged bound at scale `T` but violates the pointwise bound at scale `T`. -/
theorem exists_average_bound_counterexample {ι : Type*}
    {B : Finset ι} {b : ι} {T : ℝ}
    (hb : b ∈ B) (hcard : 1 < B.card) (hT : 0 < T) :
    ∃ score : ι -> ℝ,
      (∀ c : ι, c ∈ B -> 0 <= score c) /\
      AuxiliaryAverageBound score B T /\
      T < score b := by
  classical
  let score : ι -> ℝ := fun c => if c = b then (B.card : ℝ) * T else 0
  refine ⟨score, ?_, ?_, ?_⟩
  · intro c _hc
    unfold score
    by_cases hcb : c = b
    · have hcard_nonneg : (0 : ℝ) <= (B.card : ℝ) := by exact_mod_cast Nat.zero_le B.card
      simp [hcb, mul_nonneg hcard_nonneg (le_of_lt hT)]
    · simp [hcb]
  · unfold AuxiliaryAverageBound score
    have hsum :
        B.sum (fun c => if c = b then (B.card : ℝ) * T else 0)
          = (B.card : ℝ) * T := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _hc hcb
        simp [hcb]
      · intro hbnot
        exact False.elim (hbnot hb)
    exact le_of_eq hsum
  · unfold score
    simp?
    have hcardR : (1 : ℝ) < (B.card : ℝ) := by exact_mod_cast hcard
    nlinarith

/-- Bundled gate: the two direct attempts to use a large-set double-sum input for one period fail
without an extra theorem.  Singleton specialization violates a nontrivial size threshold, while
large-set averaging has a sharp `#B` pointwise loss. -/
theorem doubleSumSingletonGate {ι : Type*}
    {threshold aCard : Nat} {B : Finset ι} {b : ι} {T : ℝ}
    (hthreshold : 1 < threshold)
    (hb : b ∈ B) (hcard : 1 < B.card) (hT : 0 < T) :
    (¬ SingletonSecondSetEligible threshold aCard) /\
      (∃ score : ι -> ℝ,
        (∀ c : ι, c ∈ B -> 0 <= score c) /\
        AuxiliaryAverageBound score B T /\
        T < score b) := by
  exact ⟨not_singletonSecondSetEligible_of_one_lt_threshold hthreshold,
    exists_average_bound_counterexample hb hcard hT⟩

end ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate.not_singletonSecondSetEligible_of_one_lt_threshold
#print axioms ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate.one_lt_power_threshold
#print axioms ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate.not_singletonSecondSetEligible_power_threshold
#print axioms ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate.pointwise_le_card_mul_of_average_bound
#print axioms ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate.exists_average_bound_counterexample
#print axioms ArkLib.ProximityGap.Frontier.PaleyDoubleSumSingletonGate.doubleSumSingletonGate
