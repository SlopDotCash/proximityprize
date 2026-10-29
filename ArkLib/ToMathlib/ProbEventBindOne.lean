/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.EvalDist.ProbabilityBounds

/-!
# Perfect-event composition under native probability semantics

A prefix event of probability one and continuation events of probability one imply that the
composed event has probability one. The canonical conditional lower bound proves this directly;
no positive-mass/support coherence or global discrete instance is needed. The probability-one
prefix hypothesis already accounts for failure mass.
-/

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}

/-- A probability-one prefix event followed by probability-one conditional events composes. -/
theorem probEvent_bind_eq_one (mx : m α) (my : α → m β) (P : α → Prop) (Q : β → Prop)
    (h1 : Pr{let a ← mx}[P a] = 1)
    (h2 : ∀ a, P a → Pr{let b ← my a}[Q b] = 1) :
    Pr{let b ← mx >>= my}[Q b] = 1 := by
  apply le_antisymm (prEvent_le_one _)
  have h := mul_le_prEvent_bind_of_forall mx my P Q (r := 1) (r' := 1)
    h1.ge (fun a ha => (h2 a ha).ge)
  simpa only [one_mul] using h

#print axioms probEvent_bind_eq_one
