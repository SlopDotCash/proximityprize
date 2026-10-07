/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessMsgKeystone

/-!
# Compatibility with the non-failing-initializer append interface

The message-seam completeness proof is owned by `AppendCompletenessMsgKeystone`.
This module retains the explicit game-totality lemma and the older initializer-bearing
interface under `Reduction.append_completeness_msg_of_neverFail`. Reusing the canonical
proof lets both public import paths coexist without duplicate declarations.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Discharged `hTot`.** The appended simulated honest game never *samples* a failure: its only
failure mode is the explicit `none` output (folded into the bad event). With a non-failing
initializer `init`, the bind `init >>= fun s => (…).run' s` is failure-free by
`simulateQ_run_neverFail` (the honest interactive implementation `impl.addLift challengeQueryImpl`
never fails, `addLift_neverFail`). -/
theorem append_game_neverFail
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁)
    (hInit : Pr[⊥ | init] = 0)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0 := by
  show Pr[⊥ | init >>= fun s =>
      StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
        (OptionT.run ((R₁.append R₂).run stmt wit))) s] = 0
  rw [probFailure_bind_eq_add_tsum, hInit, zero_add, ENNReal.tsum_eq_zero]
  intro s
  rw [mul_eq_zero]
  right
  rw [StateT.run'_eq, probFailure_map]
  exact simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s

/-- Compatibility wrapper retaining the explicit non-failing-initializer hypothesis.
The canonical message-seam theorem proves the result without needing that extra hypothesis. -/
theorem append_completeness_msg_of_neverFail
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : Pr[⊥ | init] = 0)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) :=
  append_completeness_msg R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

end Reduction
