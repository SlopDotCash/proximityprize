/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.EvalDist.Monad.Basic

/-!
# Two-stage perfect-event composition for monadic bind

`probEvent_bind_eq_one` is the perfect-completeness building block for sequential composition: if
the first computation produces a `P`-output with probability `1`, and from any `P`-output the
continuation produces a `Q`-output with probability `1`, then the bind produces a `Q`-output with
probability `1`. Proved from `probEvent_eq_one_iff` (probability `1` ⇔ never-fails and holds on the
whole support), `probFailure_bind_eq_zero_iff`, and `mem_support_bind_iff`. Intended for upstreaming
to VCVio's `EvalDist` API.
-/

open scoped ENNReal

universe u v

variable {m : Type u → Type v} [Monad m] [HasEvalSPMF m] {α β : Type u}

/-- **Two-stage perfect composition.** If `mx` produces an output satisfying `P` with probability 1,
and from any `P`-output the continuation `my` produces a `Q`-output with probability 1, then the
bind produces a `Q`-output with probability 1. -/
theorem probEvent_bind_eq_one (mx : m α) (my : α → m β) (P : α → Prop) (Q : β → Prop)
    (h1 : Pr[ P | mx] = 1) (h2 : ∀ a, P a → Pr[ Q | my a] = 1) :
    Pr[ Q | mx >>= my] = 1 := by
  rw [probEvent_eq_one_iff] at h1 ⊢
  obtain ⟨hf1, hs1⟩ := h1
  refine ⟨(probFailure_bind_eq_zero_iff mx my).mpr
      ⟨hf1, fun a ha => (probEvent_eq_one_iff.mp (h2 a (hs1 a ha))).1⟩, ?_⟩
  intro y hy
  obtain ⟨a, ha, hya⟩ := (mem_support_bind_iff mx my y).mp hy
  exact (probEvent_eq_one_iff.mp (h2 a (hs1 a ha))).2 y hya
