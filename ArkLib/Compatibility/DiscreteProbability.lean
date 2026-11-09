/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import VCVio

/-!
# Discrete support compatibility for the native probability semantics

The former `HasEvalSPMF` API coupled reachable outputs to positive probability. Native
`EvalDistSemantics` deliberately separates these concepts. `DiscreteSupportSemantics` records
only that former zero-event law, and its uniform-oracle and optional-computation instances are
proved from the canonical semantics. The failure-bind law is then derived using the canonical
native integral formula, rather than imposed as a new field.

`LosslessSemantics` records the probability-one law formerly supplied by `HasEvalPMF`; oracle
computations satisfy it under the native answer measure. Historical probability function names
are transparent wrappers around native `prEvent` and `prFail`.
-/

open OracleComp OracleSpec MeasureTheory
universe v

namespace ProximityPrize.Compatibility

/-- Reachable outputs have positive measure under the chosen native semantics. This law is
additional to lawful monad semantics: arbitrary continuous or zero-weight samplers need not
satisfy it. -/
class DiscreteSupportSemantics (m : Type → Type v) [Monad m] [MonadAttach m]
    [EvalDistSemantics m] : Prop where
  /-- Probability zero means the event avoids every reachable output. -/
  prEvent_eq_zero_iff {α : Type} (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 0 ↔ ∀ x ∈ support mx, ¬ p x

instance {ι : Type} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec] :
    DiscreteSupportSemantics (OracleComp spec) where
  prEvent_eq_zero_iff := OracleComp.prEvent_eq_zero_iff

instance {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [DiscreteSupportSemantics m] :
    DiscreteSupportSemantics (OptionT m) where
  prEvent_eq_zero_iff mx p := by
    rw [OptionT.prEvent_eq_run, DiscreteSupportSemantics.prEvent_eq_zero_iff]
    constructor
    · intro h x hx
      exact h (some x) ((MonadAttach.OptionT.canReturn_iff).1 hx)
    · intro h value hv
      cases value with
      | none => simp
      | some x => exact h x ((MonadAttach.OptionT.canReturn_iff).2 hv)

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] [DiscreteSupportSemantics m]
  {α β : Type}

/-- A bind is lossless exactly when its prefix and every reachable continuation are. -/
lemma prFail_bind_eq_zero_iff (mx : m α) (f : α → m β) :
    prFail (mx >>= f) = 0 ↔ prFail mx = 0 ∧ ∀ x ∈ support mx, prFail (f x) = 0 := by
  let : MeasurableSpace α := ⊤
  rw [prFail_bind_eq_add_lintegral_of_discrete, add_eq_zero]
  apply and_congr_right
  intro _
  rw [lintegral_eq_zero_iff Measurable.of_discrete]
  change 𝒟[mx] {x | ¬ prFail (f x) = 0} = 0 ↔ _
  rw [← prEvent_eq_evalDist_of_discrete,
    DiscreteSupportSemantics.prEvent_eq_zero_iff]
  simp only [not_not]


/-- Probability one includes losslessness and every reachable output satisfying the event. -/
lemma prEvent_eq_one_iff_lossless_and_support (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 1 ↔ prFail mx = 0 ∧ ∀ x ∈ support mx, p x := by
  have hpart := prEvent_add_prEvent_not_eq_prEvent_true mx p
  constructor
  · intro hp
    have htotal : Pr{let _ ← mx}[True] = 1 :=
      le_antisymm (prEvent_le_one _) (by
        rw [← hp]
        exact prEvent_mono mx p (fun _ => True) (fun _ _ => True.intro))
    have hn : Pr{let x ← mx}[¬ p x] = 0 := by
      apply (ENNReal.add_left_inj ENNReal.one_ne_top).mp
      simpa only [hp, htotal, add_zero, zero_add, add_comm] using hpart
    refine ⟨(prFail_eq_zero_iff mx).2 htotal, ?_⟩
    have hs := (DiscreteSupportSemantics.prEvent_eq_zero_iff mx (fun x => ¬ p x)).1 hn
    intro x hx
    exact not_not.mp (hs x hx)
  · rintro ⟨hf, hs⟩
    have hn : Pr{let x ← mx}[¬ p x] = 0 :=
      (DiscreteSupportSemantics.prEvent_eq_zero_iff mx (fun x => ¬ p x)).2
        (fun x hx => not_not.mpr (hs x hx))
    simpa only [hn, add_zero, (prFail_eq_zero_iff mx).1 hf] using hpart


omit [MonadAttach m] [DiscreteSupportSemantics m] in
/-- Wrapping an optional result adds exactly its `none` mass to failure. -/
lemma prFail_mk {α : Type} (mx : m (Option α)) :
    prFail (OptionT.mk mx) = prFail mx + Pr{let x ← mx}[x = none] := by
  have htotal := prEvent_add_prEvent_not_eq_prEvent_true mx (fun x => x = none)
  have hsome : Pr{let x ← mx}[¬ x = none] =
      Pr{let x ← OptionT.mk mx}[True] := by
    rw [OptionT.prEvent_mk]
    apply prEvent_congr
    intro x
    cases x <;> simp
  rw [hsome] at htotal
  have hsum : Pr{let x ← OptionT.mk mx}[True] +
      (prFail mx + Pr{let x ← mx}[x = none]) = 1 := by
    calc
      _ = (Pr{let x ← mx}[x = none] +
          Pr{let x ← OptionT.mk mx}[True]) + prFail mx := by ac_rfl
      _ = 1 := by rw [htotal, prEvent_true_add_prFail]
  rw [prFail_def]
  exact ENNReal.sub_eq_of_eq_add (prEvent_ne_top _) (by simpa [add_comm] using hsum.symm)


/-- Native successful-output mass is one for every computation, as in the former `HasEvalPMF`
interface. This is independent of reachable-output/positive-mass coherence. -/
class LosslessSemantics (m : Type → Type v) [Monad m] [EvalDistSemantics m] : Prop where
  /-- Every computation has failure probability zero. -/
  prFail_eq_zero {α : Type} (mx : m α) : prFail mx = 0

instance {ι : Type} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] :
    LosslessSemantics (OracleComp spec) where
  prFail_eq_zero := OracleComp.prFail_eq_zero

end ProximityPrize.Compatibility

/-- Historical failure probability, evaluated by the canonical native semantics. -/
noncomputable abbrev probFailure {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) : ENNReal := prFail mx

/-- Historical output probability, evaluated as a native equality event. -/
noncomputable abbrev probOutput {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (x : α) : ENNReal := Pr{let y ← mx}[y = x]

/-- Historical event probability, evaluated by the native event semantics. -/
noncomputable abbrev probEvent {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (p : α → Prop) (mx : m α) : ENNReal := Pr{let x ← mx}[p x]

/-- Historical losslessness predicate in the native semantics. -/
def NeverFail {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) : Prop := prFail mx = 0


/-- Historical spelling of the native probability-one and support characterization. -/
lemma probEvent_eq_one_iff {m : Type → Type v} [Monad m] [LawfulMonad m]
    [MonadAttach m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [ProximityPrize.Compatibility.DiscreteSupportSemantics m]
    {α : Type} (p : α → Prop) (mx : m α) :
    probEvent p mx = 1 ↔ probFailure mx = 0 ∧ ∀ x ∈ support mx, p x :=
  ProximityPrize.Compatibility.prEvent_eq_one_iff_lossless_and_support mx p

#print axioms ProximityPrize.Compatibility.prEvent_eq_one_iff_lossless_and_support
#print axioms probEvent_eq_one_iff
