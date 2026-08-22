/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessMsg
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge

/-!
# Discharge of `Reduction.reductionAppendPerfectCompletenessResidual` (#367)

`Append.lean` names `reductionAppendPerfectCompletenessResidual` — the plain
reduction-level *perfect* append completeness `(R₁.append R₂).perfectCompleteness`
— as an open residual, threaded as a hypothesis by `reduction_append_perfectCompleteness`.
The existing `AppendResidualDischarges.lean` discharges the *error-bearing* reduction
completeness and the *oracle-level* perfect completeness, but not this plain
reduction-level perfect one, and only in the message-seam regime.

This file supplies the missing providers, each a direct application of a proven
seam keystone:

* `reductionAppendPerfectCompletenessResidual_msg` ← `append_perfectCompleteness_message`
  (message seam, `P_to_V`; lossless `init` + support-faithful `impl`).
* `reductionAppendPerfectCompletenessResidual_challenge` ← `append_perfectCompleteness_challenge`
  (challenge seam, `V_to_P`; state-preserving / never-failing `impl`).
* `reductionAppendPerfectCompletenessResidual_holds` — the **seam-direction-free**
  discharge: a total case split on the seam round's direction (the appended seam round
  `m` is `pSpec₂`'s round `0`, `append_dir_natAdd`) routes to whichever keystone applies,
  so only the union of the two honest-`impl` side conditions is needed — no `hDir` hypothesis.

No `sorry`, no new axioms: each proof is a keystone application.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Discharge (message seam).** Plain reduction-level perfect append completeness is a
theorem under the message-seam direction facts, lossless `init`, and support-faithful `impl`.
Direct from `append_perfectCompleteness_message`. -/
theorem reductionAppendPerfectCompletenessResidual_msg
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited]
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    reductionAppendPerfectCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_perfectCompleteness_message R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp

/-- **Discharge (challenge seam).** Plain reduction-level perfect append completeness is a
theorem under the challenge-seam direction facts and the state-preserving / never-failing
`impl` conditions. Direct from `append_perfectCompleteness_challenge`. -/
theorem reductionAppendPerfectCompletenessResidual_challenge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (hInit : NeverFail init) :
    reductionAppendPerfectCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_perfectCompleteness_challenge R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF hInit

/-- **Seam-direction-free discharge.** The appended seam round `m` is `pSpec₂`'s round `0`
(`append_dir_natAdd`), so a total case split on `pSpec₂.dir ⟨0, hn⟩` routes to the message
or challenge keystone with the seam direction supplied automatically — no `hDir` hypothesis,
only the union of the two honest-`impl` side conditions. -/
theorem reductionAppendPerfectCompletenessResidual_holds
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited]
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    reductionAppendPerfectCompletenessResidual R₁ R₂ h₁ h₂ := by
  have hidx : (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m (⟨0, hn⟩ : Fin n) := by
    ext; simp
  have hseam : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n))
      = pSpec₂.dir (⟨0, hn⟩ : Fin n) := by
    rw [hidx]; exact Prover.append_dir_natAdd (⟨0, hn⟩ : Fin n)
  rcases hd : pSpec₂.dir (⟨0, hn⟩ : Fin n) with _ | _
  · exact reductionAppendPerfectCompletenessResidual_msg R₁ R₂ h₁ h₂ hn (hseam.trans hd) hd
      hInit hImplSupp
  · exact reductionAppendPerfectCompletenessResidual_challenge R₁ R₂ h₁ h₂ hn (hseam.trans hd) hd
      himplSP himplNF hInit

end Reduction
