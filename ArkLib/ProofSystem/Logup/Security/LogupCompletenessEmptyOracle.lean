/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessUncond

/-!
# LogUp Protocol 2 — completeness over the empty ambient oracle (issue #13)

The most-unconditional completeness keystone `logup_completeness_uncond`
(`Security/LogupCompletenessUncond.lean`) reduces full LogUp completeness to the named residual
surface `{hInit, hPerRound, hImplSupp, hAppend}` (the historical fifth member, the honest-support
hypothesis `hHonest`, was unsatisfiable and has been removed tree-wide; issue #13, dmvt audit).
One of those, `hImplSupp`, is a side condition purely on the ambient oracle implementation `impl`:

  `hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q)`.

At the canonical ambient specification `oSpec = []ₒ` (no shared oracles — the setting of the
self-contained interactive protocol, mirroring `logup_soundness_msgSeam_emptyOracle`), `hImplSupp`
is **vacuous**: every `OracleQuery []ₒ β` carries a domain index in `([]ₒ).Domain`, which projects to
the empty type `PEmpty`, so there are no queries to constrain.

This file packages that observation into `logup_completeness_emptyOracle`, dropping `hImplSupp` from
the residual surface at `[]ₒ`. The remaining obligations are the genuinely-deep completeness facts
`{hInit, hPerRound, hAppend}` — exactly the surface minus the trivial `impl` side condition.

No `sorry`/`sorryAx`/`admit`. The axiom audit at the bottom confirms axiom-cleanliness.
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section CompletenessEmptyOracle

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The empty ambient oracle spec is a probability spec (finite + inhabited oracle interfaces):
vacuously so, since it has no oracles (`[]ₒ.Domain = PEmpty`). -/
local instance instEmptySpecFintype : ([]ₒ : OracleSpec PEmpty).Fintype where
  fintype_B := fun q => q.elim

local instance instEmptySpecInhabited : ([]ₒ : OracleSpec PEmpty).Inhabited where
  inhabited_B := fun q => q.elim

/-- **The empty-oracle support-faithfulness side condition is vacuously true.** A query
`q : OracleQuery []ₒ β` carries a domain index `q.1 : ([]ₒ).Domain`, and `([]ₒ).Domain` is the empty
type (`[]ₒ = PEmpty →ₒ PEmpty`), so no such query exists. -/
theorem emptyOracle_hImplSupp (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ∀ {β} (q : OracleQuery []ₒ β) (s : σ),
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β) :=
  fun q _ => q.1.elim

/-- **LogUp Protocol 2 completeness over the empty ambient oracle: `hImplSupp` discharged.**

At `oSpec = []ₒ` the support-faithfulness side condition `hImplSupp` of `logup_completeness_uncond`
is vacuous (no queries), so it is supplied here automatically. The residual surface shrinks to the
genuinely-deep completeness facts `{hInit, hPerRound, hAppend}`. This mirrors
`logup_soundness_msgSeam_emptyOracle` on the soundness side. -/
theorem logup_completeness_emptyOracle
    (hInit : NeverFail init)
    (hPerRound : ∀ i,
      (Sumcheck.Spec.SingleRound.oracleReduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) []ₒ i).toReduction =
        Sumcheck.Spec.SingleRound.reduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) []ₒ i)
    (hAppend :
      AppendCompletenessResidual []ₒ F n M params init impl
        (outerCompletenessResidual_of_neverFail []ₒ F n M params init impl hInit)
        (sumcheckCompletenessResidual_of_perRound []ₒ F n M params init impl
          hPerRound hInit (emptyOracle_hImplSupp impl))) :
    (logupOracleReduction []ₒ F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_uncond []ₒ F n M params init impl hInit hPerRound
    (emptyOracle_hImplSupp impl) hAppend

end CompletenessEmptyOracle

end Logup

/- Axiom audit for the empty-ambient-oracle LogUp completeness corollary. -/
#print axioms Logup.emptyOracle_hImplSupp
#print axioms Logup.logup_completeness_emptyOracle
