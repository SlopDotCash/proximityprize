/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši
-/

import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform

/-!
  # Notation for probability sampling statements

  The goal is to be able to write readable statements like:
  ```
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ F × F }[ z = (x, y) ]
  ```
  which should parse as:
  ```
  (do let x ← ProximityPrize.Compatibility.uniformOfFintype F
      let y ← ProximityPrize.Compatibility.uniformOfFintype F
      let z ← ProximityPrize.Compatibility.uniformOfFintype (F × F)
      return z = (x, y)).val True
  ```
  The `.val True` is used to extract the probability of the condition holding.

  In general the `do` notation is more restrictive than `PMF.bind`, as the latter allows for
  changing universe levels. This should not be an issue in general if we always work over `Type`.

  We should also allow for non-uniform distributions, e.g.
  `Pr_{ let e ← discreteGaussian (ZMod p) }[ e = 0 ]`.
-/

open scoped ProbabilityTheory NNReal ENNReal

open Lean Elab Parser Term Meta PMF

/-! Mathlib 4.35 moved finite uniform distributions to measures. The historical downstream
PMF interface remains a different type, so construct it explicitly and bridge its events to the
canonical native sampler in `ProximityPrize.Compatibility.UniformProbability`.

The finite-PMF constructors and their elementary facts below retain Mathlib's pre-migration
implementation (Apache-2.0; authors Josha Dekker, Devon Tuma, Kexing Ying).
-/

namespace ProximityPrize.Compatibility

noncomputable section
open PMF
open scoped Finset MeasureTheory NNReal ENNReal
variable {α : Type*}

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, ite_false]

variable {s : Finset α} (hs : s.Nonempty) {a : α}

open scoped Classical in
@[simp]
theorem uniformOfFinset_apply (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl

theorem uniformOfFinset_apply_of_mem (ha : a ∈ s) : uniformOfFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]

theorem uniformOfFinset_apply_of_notMem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by simp [ha]

@[simp]
theorem support_uniformOfFinset : (uniformOfFinset s hs).support = s := by
  classical
  ext x
  rw [PMF.mem_support_iff, uniformOfFinset_apply]
  by_cases hx : x ∈ s <;> simp [hx]

theorem mem_support_uniformOfFinset_iff (a : α) : a ∈ (uniformOfFinset s hs).support ↔ a ∈ s := by
  simp

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_uniformOfFinset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = #{x ∈ s | x ∈ t} / #s :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then uniformOfFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_comm]
    _ = ∑ x ∈ s with x ∈ t, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_eq_sum fun _ hx => ite_eq_right fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ :=
      Finset.sum_congr rfl fun x hx => by
        have this : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, ite_true]
    _ = #{x ∈ s | x ∈ t} / #s := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
@[simp]
theorem toMeasure_uniformOfFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = #{x ∈ s | x ∈ t} / #s :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_uniformOfFinset_apply hs t)

end Measure

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

@[simp]
theorem support_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformOfFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]

theorem mem_support_uniformOfFintype (a : α) : a ∈ (uniformOfFintype α).support := by simp

section Measure

variable (s : Set α)

theorem toOuterMeasure_uniformOfFintype_apply [Fintype s] :
    (uniformOfFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [uniformOfFintype, toOuterMeasure_uniformOfFinset_apply, Fintype.card_subtype,
    Finset.card_univ]

theorem toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  classical
  simp [uniformOfFintype, Fintype.card_subtype, hs]

end Measure

end UniformOfFintype

end
end ProximityPrize.Compatibility

namespace ProbabilityTheory

/-- Notation for uniform sampling from a finite, non-empty type. Just converts to
  `ProximityPrize.Compatibility.uniformOfFintype`. -/
scoped notation "$ᵖ" => ProximityPrize.Compatibility.uniformOfFintype

/--
Syntax for probability expressions: `Pr_{...}[...]`

Expands `Pr_{e₁; e₂; ...; eₙ}[cond]` to `(do e₁; e₂; ...; eₙ; return cond).val True`.

The do-notation uses the `Bind` typeclass, which requires all sampled types to live in the same
universe. In practice this is not a restriction since all our probability distributions sample from
`Type` (finite fields, finite sets, etc.) and conditions are in `Prop`.

If you somehow need universe polymorphism (sampling from `Type u` and returning something in
`Type v`), you'd need to manually use `PMF.bind` instead of this notation. But this never happens
in cryptographic applications.

# Examples
```
Pr_{ let x ←$ᵖ F; let y ←$ᵖ F }[x = y]
```
expands to
```
(do
  let x ← ProximityPrize.Compatibility.uniformOfFintype F
  let y ← ProximityPrize.Compatibility.uniformOfFintype F
  return x = y).val True
```
-/
syntax (name := prStx) "Pr_{" doSeq "}[" term "]" : term

/--
Elaboration rule for `Pr_{...}[...]` notation.

Handles both `doSeqBracketed` (curly braces) and `doSeqIndent` (no braces) forms of do-sequences.
-/
scoped macro_rules (kind := prStx)
  -- `doSeqBracketed`
  | `(Pr_{{$items*}}[$t]) => `((((do $items:doSeqItem*
                                     return $t:term) True) : ENNReal))
  -- `doSeqIndent`
  | `(Pr_{$items*}[$t]) => `((((do $items:doSeqItem*
                                     return $t:term) True) : ENNReal))

/-- Unfold `Pr_{ let a ← p }[P a]` as the standard indicator-weighted PMF tsum,
for a `Prop`-valued predicate `P`. -/
lemma Pr_eq_tsum_indicator {α : Type} (p : PMF α) (P : α → Prop)
    [DecidablePred P] :
    Pr_{ let a ← p }[P a] = ∑' a, p a * (if P a then (1 : ENNReal) else 0) := by
  simp only [Bind.bind, Pure.pure, PMF.bind, PMF.pure, DFunLike.coe,
    eq_iff_iff, true_iff]

/-- Unfold `Pr_{ let a ← p }[(decide (P a) : Prop)]` as the standard
indicator-weighted PMF tsum. Specialisation of [`Pr_eq_tsum_indicator`]
that also peels off the `Bool ↪ Prop` coercion via `decide_eq_true_iff`. -/
lemma Pr_decide_eq_tsum_indicator {α : Type} (p : PMF α) (P : α → Prop)
    [DecidablePred P] :
    Pr_{ let a ← p }[(decide (P a) : Prop)] =
      ∑' a, p a * (if P a then (1 : ENNReal) else 0) := by
  simp only [Bind.bind, Pure.pure, PMF.bind, PMF.pure, DFunLike.coe,
    eq_iff_iff, true_iff, decide_eq_true_iff]

end ProbabilityTheory

example {F} [Fintype F] [Nonempty F] :
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ (F × F) }[z = (x, y)] =
  (do let x ← ProximityPrize.Compatibility.uniformOfFintype F
      let y ← ProximityPrize.Compatibility.uniformOfFintype F
      let z ← ProximityPrize.Compatibility.uniformOfFintype (F × F)
      return (z = (x, y))).val True := rfl

section

variable {F : Type} [Nonempty F] [Fintype F]

example :
  (do
    let x ← $ᵖ F
    let y ← $ᵖ F
    let z ← $ᵖ (F × F)
    return z = (x, y) : PMF Prop).1 True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by
  classical
  simp only [Bind.bind, Pure.pure, PMF.bind, PMF.pure,
    ProximityPrize.Compatibility.uniformOfFintype,
    ProximityPrize.Compatibility.uniformOfFinset, PMF.ofFinset, DFunLike.coe]
  simp only [Finset.mem_univ, ite_true, eq_iff_iff, true_iff, mul_ite, mul_one, mul_zero]
  simp [tsum_fintype, div_eq_mul_inv, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp : (Fintype.card F : ENNReal) ≠ 0)
      (ENNReal.natCast_ne_top _)]

example :
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ (F × F) }[ z = (x, y) ] =
  ((1 : ℝ≥0∞) / Fintype.card (F × F)) ↔
  (do
    let x ← $ᵖ F
    let y ← $ᵖ F
    let z ← $ᵖ (F × F)
    return z = (x, y)).val True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by
  rfl

end
