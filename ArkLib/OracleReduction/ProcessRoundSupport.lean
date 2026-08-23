/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Execution

/-!
# `processRound` preserves earlier transcript entries on the support (issue #13)

The support-level transcript-extension fact underlying the LogUp outer run-marginal `hsupp`
chase: each `processRound` step appends one entry (`Transcript.concat = Fin.snoc`) and leaves all
earlier entries unchanged.  Hence on the support of `processRound j prover cur`, every output
transcript restricts (on the first `j` rounds) to some input transcript from the support of
`cur` — in particular any fixed earlier entry (e.g. the LogUp outer round-1 challenge) survives
all later rounds of the run unchanged.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- **`processRound` preserves earlier transcript entries on the support.**  Every support output
of one `processRound` step restricts, on all earlier rounds, to a support input: the new round is
`Fin.snoc`-appended and earlier entries are untouched. -/
theorem processRound_support_restrict
    (j : Fin n) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc))
    (out : pSpec.Transcript j.succ × prover.PrvState j.succ)
    (hout : out ∈ support (prover.processRound j cur)) :
    ∃ ts ∈ support cur, ∀ i : Fin j.castSucc.val,
      out.1 (Fin.castLE (by simp only [Fin.val_castSucc, Fin.val_succ]; omega) i) = ts.1 i := by
  classical
  unfold processRound at hout
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hout
  obtain ⟨⟨tr, st⟩, hts, hout⟩ := hout
  refine ⟨⟨tr, st⟩, hts, ?_⟩
  split at hout
  · -- challenge round: out.1 = Fin.snoc tr challenge
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hout
    obtain ⟨chal, -, f, -, rfl⟩ := hout
    intro i
    exact Fin.snoc_castSucc
      (α := fun k : Fin (j.1 + 1) => pSpec.«Type» (Fin.castLE j.2 k)) chal tr i
  · -- message round: out.1 = Fin.snoc tr msg
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hout
    obtain ⟨⟨msg, st'⟩, -, rfl⟩ := hout
    intro i
    exact Fin.snoc_castSucc
      (α := fun k : Fin (j.1 + 1) => pSpec.«Type» (Fin.castLE j.2 k)) msg tr i

end Prover

/-! ### Axiom audit -/

#print axioms Prover.processRound_support_restrict
