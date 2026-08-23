/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.ProcessRoundSupport

/-!
# Rounds 2–3 of a 4-round protocol preserve the round-1 entry (issue #13)

The concrete instantiation of `Prover.processRound_support_restrict` consumed by the LogUp outer
run-marginal `hsupp` chase: in any 4-round protocol, the continuation from round 2 to the end
(`continueFromTo 2 (last 4)`, i.e. rounds 2 and 3) is two `processRound` steps
(`continueFromTo_two_last_eq`), and on its support the round-1 transcript entry — the LogUp outer
challenge — is carried through unchanged (`continueFromTo_two_last_entry_one`).
-/

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {pSpec : ProtocolSpec 4}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- **The round-2-to-end continuation of a 4-round protocol is two `processRound` steps.** -/
theorem continueFromTo_two_last_eq
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (s : StmtIn) (w : WitIn)
    (rk : pSpec.Transcript (2 : Fin 5) × prover.PrvState (2 : Fin 5)) :
    prover.continueFromTo s w (2 : Fin 5) (Fin.last 4) rk
      = prover.processRound (⟨3, by omega⟩ : Fin 4)
          (prover.processRound (⟨2, by omega⟩ : Fin 4) (pure rk)) := by
  show prover.continueFromTo s w (2 : Fin 5) ((⟨3, by omega⟩ : Fin 4).succ) rk = _
  rw [continueFromTo_succ_of_ne prover s w (2 : Fin 5) (⟨3, by omega⟩ : Fin 4)
    (by decide) rk]
  congr 1

/-- **Rounds 2–3 preserve the round-1 entry on the support.**  Every support output of the
round-2-to-end continuation carries the input's round-1 transcript entry unchanged. -/
theorem continueFromTo_two_last_entry_one
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (s : StmtIn) (w : WitIn)
    (rk : pSpec.Transcript (2 : Fin 5) × prover.PrvState (2 : Fin 5))
    (out : pSpec.Transcript (Fin.last 4) × prover.PrvState (Fin.last 4))
    (hout : out ∈ support (prover.continueFromTo s w (2 : Fin 5) (Fin.last 4) rk)) :
    out.1 ⟨1, by decide⟩ = rk.1 ⟨1, by decide⟩ := by
  rw [continueFromTo_two_last_eq prover s w rk] at hout
  obtain ⟨ts₃, hts₃, h₃⟩ :=
    processRound_support_restrict (⟨3, by omega⟩ : Fin 4) prover _ out hout
  obtain ⟨ts₂, hts₂, h₂⟩ :=
    processRound_support_restrict (⟨2, by omega⟩ : Fin 4) prover _ ts₃ hts₃
  rw [support_pure, Set.mem_singleton_iff] at hts₂
  subst hts₂
  have e₃ := h₃ ⟨1, by decide⟩
  have e₂ := h₂ ⟨1, by decide⟩
  exact e₃.trans e₂

end Prover

/-! ### Axiom audit -/

#print axioms Prover.continueFromTo_two_last_eq
#print axioms Prover.continueFromTo_two_last_entry_one
