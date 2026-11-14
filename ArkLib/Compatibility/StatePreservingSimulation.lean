/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
The historical state-preservation lemmas retain their Apache 2.0 license as described in LICENSE.
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
New contributions are released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
-/

import VCVio

/-!
# State-preserving simulation and native commutation

A handler that preserves its state on every reachable answer preserves that state through an
entire simulated program. After fixing the state, independent finite-oracle computations commute
by the canonical uniform-oracle law. The historical `OptionTStateT` theorem names remain available;
no losslessness or additional program assumption is introduced. Measure observations require only
an arbitrary measurable structure on the observed result type.
-/

open OracleComp OracleSpec

namespace OptionTStateT

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **`simulateQ` preserves the `σ`-state on its support, when every query implementation does.**
Holds for `challengeQueryImpl` (which threads `σ` unchanged) and for empty `oSpec`. This is the
independence ingredient for the seam swap: a state-preserving prover stage cannot affect a later
verifier stage's `simulateQ` state, so the two stages commute distributionally
(`OracleComp.evalDist_bind_comm`). -/
theorem simulateQ_state_preserving
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s : σ) :
    ∀ x ∈ support ((simulateQ so X).run s), x.2 = s := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, MonadAttach.support_pure,
      Set.mem_singleton_iff] at hx
    subst hx; rfl
  | query_bind t oa ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.support_bind, Set.mem_iUnion] at hx
    obtain ⟨⟨u, s'⟩, hmem1, hmem2⟩ := hx
    have hs' : s' = s := hso t s ⟨u, s'⟩ hmem1
    exact hs' ▸ ih u s' x hmem2

#print axioms simulateQ_state_preserving

/-- When the implementation preserves `σ`, a simulated bind's continuation runs from the same
state `s`, because its prefix leaves that state unchanged. Independent stages can then commute
using the canonical uniform-oracle law. -/
theorem simulateQ_run_bind_state_fixed
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α β : Type} (A : OracleComp spec α) (g : α → OracleComp spec β) (s : σ) :
    (simulateQ so (A >>= g)).run s
      = (simulateQ so A).run s >>= fun p => (simulateQ so (g p.1)).run s := by
  rw [simulateQ_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ (fun p hp => ?_)
  obtain ⟨a, s'⟩ := p
  rw [show s' = s from simulateQ_state_preserving so hso A s ⟨a, s'⟩ hp]

#print axioms simulateQ_run_bind_state_fixed

/-- State-preserving simulation lets two stages commute in distribution. -/
theorem evalDistEq_simulateQ_swap
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α β γ : Type}
    (A : OracleComp spec α) (B : OracleComp spec β) (k : α → β → OracleComp spec γ) (s : σ) :
    (simulateQ so (A >>= fun a => B >>= fun b => k a b)).run' s =ᵈ
      (simulateQ so (B >>= fun b => A >>= fun a => k a b)).run' s := by
  rw [StateT.run'_eq, StateT.run'_eq]
  simpa only [simulateQ_run_bind_state_fixed so hso] using
    (OracleComp.EvalDistEq.bind_bind_swap ((simulateQ so A).run s)
      ((simulateQ so B).run s) (fun a b => (simulateQ so (k a.1 b.1)).run s)).map Prod.fst

/-- The historical stage-swap observation in any measurable output structure. -/
theorem evalDist_simulateQ_swap
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α β γ : Type} [MeasurableSpace γ]
    (A : OracleComp spec α) (B : OracleComp spec β) (k : α → β → OracleComp spec γ) (s : σ) :
    evalDist ((simulateQ so (A >>= fun a => B >>= fun b => k a b)).run' s)
      = evalDist ((simulateQ so (B >>= fun b => A >>= fun a => k a b)).run' s) :=
  (evalDistEq_simulateQ_swap so hso A B k s).evalDist_eq

/-- The same independent-stage swap remains valid after a common prefix. -/
theorem evalDistEq_simulateQ_swap_prefix
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α₀ α β γ : Type}
    (FST : OracleComp spec α₀) (A : α₀ → OracleComp spec α) (B : α₀ → OracleComp spec β)
    (k : α₀ → α → β → OracleComp spec γ) (s : σ) :
    (simulateQ so (FST >>= fun x => A x >>= fun a => B x >>= fun b => k x a b)).run' s =ᵈ
      (simulateQ so (FST >>= fun x => B x >>= fun b => A x >>= fun a => k x a b)).run' s := by
  rw [StateT.run'_eq, StateT.run'_eq]
  have h :
      (simulateQ so (FST >>= fun x => A x >>= fun a => B x >>= fun b => k x a b)).run s =ᵈ
      (simulateQ so (FST >>= fun x => B x >>= fun b => A x >>= fun a => k x a b)).run s := by
    simp only [simulateQ_run_bind_state_fixed so hso]
    apply EvalDistEq.bind_right
    intro p
    exact OracleComp.EvalDistEq.bind_bind_swap ((simulateQ so (A p.1)).run s)
      ((simulateQ so (B p.1)).run s) (fun a b => (simulateQ so (k p.1 a.1 b.1)).run s)
  exact h.map Prod.fst

/-- The historical prefixed stage-swap observation in any measurable output structure. -/
theorem evalDist_simulateQ_swap_prefix
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α₀ α β γ : Type} [MeasurableSpace γ]
    (FST : OracleComp spec α₀) (A : α₀ → OracleComp spec α) (B : α₀ → OracleComp spec β)
    (k : α₀ → α → β → OracleComp spec γ) (s : σ) :
    evalDist ((simulateQ so
        (FST >>= fun x => A x >>= fun a => B x >>= fun b => k x a b)).run' s)
      = evalDist ((simulateQ so
        (FST >>= fun x => B x >>= fun b => A x >>= fun a => k x a b)).run' s) :=
  (evalDistEq_simulateQ_swap_prefix so hso FST A B k s).evalDist_eq

#print axioms evalDistEq_simulateQ_swap
#print axioms evalDist_simulateQ_swap
#print axioms evalDistEq_simulateQ_swap_prefix
#print axioms evalDist_simulateQ_swap_prefix

end OptionTStateT
