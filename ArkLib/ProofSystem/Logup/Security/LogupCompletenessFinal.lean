/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessWired
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessUncond
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessMsgSeam
import ArkLib.ProofSystem.Logup.Security.LogupInitImplFacts

/-!
# LogUp Protocol 2 completeness — final end-to-end assembly (issue #13)

Combines the three proven pillars into a single end-to-end completeness statement:

* `logup_completeness_wired` (`LogupCompletenessWired.lean`) — the full LogUp oracle-reduction
  completeness from `{hInit, hSumcheck, seam-direction facts, honest-impl side conditions}`, with
  the append-composition residual discharged by the proven non-perfect message-seam append
  keystone (`append_completeness_msg`).
* `sumcheckCompletenessResidual_unconditional` (`SumcheckCompletenessUncond.lean`) — the
  embedded sumcheck phase's perfect completeness, **unconditional** in the protocol (the inner
  multi-round completeness via the proven `CubeFiber` faithfulness, and the `proj_complete`
  obligation via the claim-true `midRelation`), modulo only the standard data facts
  `hInit`/`hImplSupp`.
* the structural seam facts `logupSumcheck_length_pos` / `logup_seam_dir` /
  `logupSumcheckPSpec_first_dir` (`LogupSoundnessMsgSeam.lean`) — discharged outright from
  `0 < n`.

The result: the genuine `(logupOracleReduction).completeness init impl (inputRelation F n M)
outputRelation (logupCompletenessError F n)`, from only

* `hn : 0 < n` — non-degenerate table;
* `hInit : NeverFail init` and `hImplSupp` — standard data facts on the shared-oracle state; and
* `himplSP`/`himplNF`/`himplVB` — the standard honest-implementation side conditions
  (state-preserving, never-failing, value-state-blind), all vacuous for `oSpec = []ₒ`.

**De-larped (issue #13, dmvt audit):** the headline previously also consumed the honest-support
hypothesis `hHonest`, which was **unsatisfiable** — it quantified over *all* after-outer statements
and demanded an honest preimage and pole-freeness, but a statement with a corrupted `.multiplicity`
oracle has no honest preimage and an adversarial `xChallenge` hits poles. The theorem was therefore
uninstantiable. The embedded-sumcheck completeness is now taken from the claim-true `midRelation`
(its membership *is* the zero-sum claim the inner sumcheck needs), and `hHonest` is gone.

## Instantiability witness (the audit's acceptance gate)

`logup_completeness_final_instantiable` below instantiates **every** hypothesis of the headline on
a concrete example — `F = ZMod 5`, `n = M = 1`, `params = ⟨1, _, _⟩`, ambient oracle `[]ₒ`,
`init = pure ()`, the empty implementation — proving the hypothesis set is satisfiable and the
headline produces an actual completeness fact for a concrete LogUp instance.

No `sorry`, no new axioms; the axiom audit at the bottom must print
`[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Logup

noncomputable section

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **LogUp Protocol 2 completeness, end-to-end (issue #13).** The full LogUp oracle reduction is
complete with error `logupCompletenessError F n`, from only the non-degeneracy `0 < n` and the
standard data / honest-implementation side conditions. No honest-support hypothesis: the
embedded-sumcheck phase is complete from the claim-true `midRelation` unconditionally. -/
theorem logup_completeness_final
    (hn : 0 < n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_wired oSpec F n M params init impl hInit
    (sumcheckCompletenessResidual_unconditional oSpec F n M params init impl hInit hImplSupp)
    (logupSumcheck_length_pos n hn)
    (logup_seam_dir F n M params hn)
    (logupSumcheckPSpec_first_dir F n M params hn)
    himplSP himplNF himplVB

end

/-! ## Instantiability witness: a concrete `ZMod 5` LogUp instance

Discharges **all** hypotheses of `logup_completeness_final` on a concrete example, per the issue-#13
audit acceptance gate ("every headline theorem instantiable on a concrete example"). This is what
the deleted `hHonest`-based headline could never do. -/

section Witness

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `-1 ≠ 1` in `ZMod 5` (characteristic `5 ≠ 2`). -/
local instance : Fact ((-1 : ZMod 5) ≠ 1) := ⟨by decide⟩

/-- The empty ambient oracle spec is (vacuously) finite. -/
local instance instEmptySpecFintypeFinal : ([]ₒ : OracleSpec PEmpty).Fintype where
  fintype_B := fun q => q.elim

/-- The empty ambient oracle spec is (vacuously) inhabited. -/
local instance instEmptySpecInhabitedFinal : ([]ₒ : OracleSpec PEmpty).Inhabited where
  inhabited_B := fun q => q.elim

/-- Concrete protocol parameters for the witness: partial-sum size `ℓ = 1` at `M = 1`. -/
noncomputable def witnessParams : ProtocolParams 1 := ⟨1, Nat.one_pos, by omega⟩

/-- The (unique) query implementation over the empty ambient oracle spec: there are no queries. -/
noncomputable def emptyOracleImpl : QueryImpl []ₒ (StateT Unit ProbComp) :=
  fun t => t.elim

/-- **The headline is instantiable** (issue #13 audit acceptance gate): a concrete LogUp instance —
`F = ZMod 5`, table rows `n = 1`, columns `M = 1`, partial-sum size `ℓ = 1`, empty ambient oracle,
`init = pure ()` — discharges every hypothesis of `logup_completeness_final`, yielding the genuine
end-to-end completeness fact for this instance. All side conditions are *proved* (the `[]ₒ` ones
vacuously: `([]ₒ).Domain = PEmpty` has no inhabitants), none assumed. -/
theorem logup_completeness_final_instantiable :
    (logupOracleReduction []ₒ (ZMod 5) 1 1 witnessParams).completeness
      (pure () : ProbComp Unit) emptyOracleImpl
      (inputRelation (ZMod 5) 1 1) outputRelation
      (logupCompletenessError (ZMod 5) 1) :=
  logup_completeness_final []ₒ (ZMod 5) 1 1 witnessParams (pure ()) emptyOracleImpl
    Nat.one_pos
    (neverFail_pure_init ())
    (fun q _ => q.1.elim)
    (fun t => t.elim)
    (fun t => t.elim)
    (fun t => t.elim)

end Witness

end Logup

/- Axiom audit: must be [propext, Classical.choice, Quot.sound] with NO sorryAx. -/
#print axioms Logup.logup_completeness_final
#print axioms Logup.logup_completeness_final_instantiable
