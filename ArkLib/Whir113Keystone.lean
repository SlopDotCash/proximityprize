import ArkLib.OracleReduction.Composition.Sequential.AppendRun
import ArkLib.OracleReduction.Completeness

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- Residual for append perfect-completeness in the message-first case. The previous theorem body
ended in `sorry`; keep the exact target named without asserting it. -/
def reduction_append_perfectCompleteness_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (_h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (_h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (_hn : 0 < n)
    (_hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (_hDir₂ : pSpec₂.dir (⟨0, _hn⟩ : Fin n) = .P_to_V)
    (_hInit : NeverFail init)
    (_hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) : Prop :=
  (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃

end Reduction
