/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.OracleReduction.Execution
import ArkLib.OracleReduction.ProcessRoundSupport
import ArkLib.Data.Probability.MarginalBound
import ArkLib.ToVCVio.OracleComp.SimSemantics.SubsingletonState

/-!
# The run prefix-marginal (the measure-side keystone of the rbr union bound; #348)

The rbr→soundness union-bound chain rule needs: the probability of a PREFIX-determined
event under the longer prover run is at most its probability under the truncated run.  This
file proves it, protocol- and implementation-agnostically, over plain `OracleComp`:

* `probEvent_bind_le_probEvent_of_fiber` — the generic fiber-constancy comparison: if on
  every support fiber of `my x` the event `q` agrees with `p x`, then
  `Pr[q | mx >>= my] ≤ Pr[p | mx]`;
* `continueFromTo_entry_eq` — the support backbone: the round-`k..j` continuation never
  rewrites transcript entries below `k` (induction over `continueFromTo`'s fold, composing
  `processRound_support_restrict`);
* **`probEvent_take_runToRound_le`** — the prefix-marginal: for `k ≤ j` and any event `E`
  on round-`k` transcripts,
  `Pr[E ∘ (take k) | runToRound j] ≤ Pr[E ∘ fst | runToRound k]`.

With the deterministic first-crossing (`RbrKnowledgeFlip`) and the per-round game matching
(the per-protocol `ChallengeCoherence`/collapse layer, as in `Stir/SubUnitRbr`), this
completes the generic skeleton: `Pr[accept] ≤ Σᵢ Pr[flip at i] ≤ Σᵢ ε i`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

open OracleComp OracleSpec ProtocolSpec ProbabilityTheory
open scoped ENNReal NNReal

namespace Prover

universe v

section Generic

variable {α β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Fiber-constancy comparison**: if the event `q` is constant (`= p x`) on every support
fiber of `my x`, the bound probability of `q` under the bind is at most that of `p` under
the base. -/
lemma probEvent_bind_le_probEvent_of_fiber [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (mx : m α) (my : α → m β)
    (q : β → Prop) (p : α → Prop)
    (h : ∀ x ∈ support mx, ∀ y ∈ support (my x), (q y ↔ p x)) :
    probEvent q (mx >>= my) ≤ probEvent p mx := by
  apply prEvent_bind_le_prEvent_of_support mx my p q
  intro x hx hp
  exact prEvent_eq_zero_of_forall_mem_support (my x) q
    (fun y hy hq => hp ((h x hx y hy).mp hq))

end Generic

section Backbone

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- **The continuation never rewrites entries below the start round**: every transcript
entry of index `< k` on the support of `continueFromTo k j rk` equals the corresponding
entry of `rk`. -/
theorem continueFromTo_entry_eq
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) (j : Fin (n + 1)) (hkj : k ≤ j)
    (rk : pSpec.Transcript k × prover.PrvState k)
    (out : pSpec.Transcript j × prover.PrvState j)
    (hout : out ∈ support (continueFromTo prover stmt wit k j rk)) :
    ∀ i : Fin k.val,
      out.1 (Fin.castLE (by omega) i) = rk.1 i := by
  induction j using Fin.induction with
  | zero =>
      -- `k ≤ 0` forces `k = 0`: no entries below `k`
      intro i
      have hk0 : (k : ℕ) ≤ 0 := hkj
      exact absurd i.isLt (by omega)
  | succ mj ih =>
      by_cases hke : (k : Fin (n + 1)) = mj.succ
      · -- diagonal: the continuation is `pure rk` (up to the cast)
        subst hke
        unfold continueFromTo at hout
        rw [Fin.induction_succ] at hout
        simp only [dif_pos rfl, support_pure, Set.mem_singleton_iff] at hout
        subst hout
        intro i
        rfl
      · -- genuine step: one more `processRound` on top of the round-`mj.castSucc` continuation
        rw [continueFromTo_succ_of_ne prover stmt wit k mj hke rk] at hout
        have hkj' : k ≤ mj.castSucc := by
          rcases lt_or_eq_of_le hkj with hlt | heq
          · have : (k : ℕ) ≤ (mj.castSucc : ℕ) := by
              have h1 : (k : ℕ) < (mj.succ : ℕ) := hlt
              simp only [Fin.val_succ] at h1
              simp only [Fin.val_castSucc]
              omega
            exact this
          · exact absurd heq hke
        obtain ⟨ts, hts, hpres⟩ := processRound_support_restrict mj prover
          (continueFromTo prover stmt wit k mj.castSucc rk) out hout
        intro i
        have hik : (i : ℕ) < (mj.castSucc : ℕ) := by
          have h1 := i.isLt
          have h2 : (k : ℕ) ≤ (mj.castSucc : ℕ) := hkj'
          omega
        have h1 := hpres ⟨(i : ℕ), hik⟩
        have h2 := ih hkj' ts hts i
        -- chain the two preservations (all indices are ⟨i.val, _⟩, definitionally equal)
        exact h1.trans h2

/-- **The prefix-marginal (simulated form, subsingleton state)**: for `k ≤ j` and an event
`E` on round-`k` transcripts, the probability — under any stateless-implementation
simulation of the round-`j` run — that the transcript satisfies `E` on its round-`k`
prefix is at most the probability that the simulated round-`k` run satisfies `E`.  This is
exactly the marginalization step of the rbr union bound (both fence settings are
`σ = Unit`). -/
theorem probEvent_take_simulated_runToRound_le {σ : Type} [Subsingleton σ]
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (s : σ)
    (stmt : StmtIn) (wit : WitIn) (k j : Fin (n + 1)) (hkj : k ≤ j)
    (E : pSpec.Transcript k → Prop) :
    probEvent (fun out : pSpec.Transcript j × prover.PrvState j =>
        E (fun i : Fin k.val => out.1 (Fin.castLE (by omega) i)))
      ((simulateQ impl (prover.runToRound j stmt wit)).run' s)
      ≤ probEvent (fun out : pSpec.Transcript k × prover.PrvState k => E out.1)
          ((simulateQ impl (prover.runToRound k stmt wit)).run' s) := by
  rw [runToRound_eq_bind_continueFromTo prover stmt wit k j hkj,
    simulateQ_run'_bind_of_subsingleton impl _ _ s]
  refine probEvent_bind_le_probEvent_of_fiber _ _ _ _ ?_
  intro x hx y hy
  -- the simulated continuation's support is contained in the plain continuation's support
  have hy' : y ∈ support (continueFromTo prover stmt wit k j x) := by
    have hsub := _root_.support_simulateQ_run'_subset impl
      (continueFromTo prover stmt wit k j x) s
    exact hsub hy
  have hent := continueFromTo_entry_eq prover stmt wit k j hkj x y hy'
  constructor
  · intro hq
    have heq : (fun i : Fin k.val => y.1 (Fin.castLE (by omega) i)) = x.1 := by
      funext i
      exact hent i
    rwa [heq] at hq
  · intro hp
    have heq : (fun i : Fin k.val => y.1 (Fin.castLE (by omega) i)) = x.1 := by
      funext i
      exact hent i
    rwa [heq]

end Backbone

section UnionBound

variable {α : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **The finite union bound**: the probability that some event in a finite family holds
is at most the sum of the individual probabilities (`probEvent_or_le`, iterated). -/
lemma probEvent_exists_finset_le_sum {κ : Type*} (T : Finset κ)
    (mx : m α) (E : κ → α → Prop) :
    probEvent (fun x => ∃ i ∈ T, E i x) mx ≤ ∑ i ∈ T, probEvent (E i) mx := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [probEvent]
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      have hevent : (fun x => ∃ i ∈ insert a S, E i x) =
          (fun x => E a x ∨ ∃ i ∈ S, E i x) := by
        funext x
        simp
      rw [hevent]
      exact (prEvent_or_le mx (E a) (fun x => ∃ i ∈ S, E i x)).trans
        (add_le_add le_rfl ih)

end UnionBound

end Prover

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Prover.probEvent_bind_le_probEvent_of_fiber
#print axioms Prover.continueFromTo_entry_eq
#print axioms Prover.probEvent_take_simulated_runToRound_le
#print axioms Prover.probEvent_exists_finset_le_sum
