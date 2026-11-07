/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.LiftContext.Lens

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.Basic
import PolyFun.PFunctor.Lens.Basic

/-!
  ## Lens between Input and Output Contexts of (Oracle) Reductions

  This file defines the different lenses required for the transformation / lifting of context for an
  (oracle) reduction, and the properties required for the transformation / lift to be complete /
  sound / knowledge sound (including an extra lens for the transformation / lifting of the
  extractor).

  We also define simpler examples of lenses, when we don't need the full generality. For instance,
  lenses where we have (only) an equivalence between the statements / witnesses, or lenses where the
  witnesses are trivial.
-/

open OracleSpec OracleComp PFunctor

namespace Statement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)

end Statement.Lens

namespace OracleStatement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
end OracleStatement.Lens

/-- An **oracle-routing lens** for lifting an *oracle verifier* from an inner oracle reduction to
  an outer one.

  Design note (#433): the value-level `OracleStatement.Lens` only transports the *values* of the
  oracle statements; it cannot express how the outer oracle verifier should *answer the inner
  verifier's oracle queries* using the outer oracles, nor which outer oracles/messages the output
  oracle statements are drawn from. Those two pieces of routing data are exactly what an oracle
  verifier needs (see `OracleVerifier` in `OracleReduction/Basic.lean`, whose `verify`/`embed`/`hEq`
  fields this lens supplies). This structure adds them on top of the value-level lens:

  - `simOStmt` : routes each inner *input* oracle query into an `OracleComp` over the outer input
    oracles (with access to the outer input statement via `ReaderT`). This realizes virtual /
    non-invertible oracle routing such as sum-check's "answer the inner univariate query at `x` by
    `∑` over `|D|^(n-i)` evaluation queries to the outer multivariate oracle".
  - `embedOStmt` / `hEqOStmt` : the *output*-side routing, mirroring `OracleVerifier.embed`/`hEq` —
    each outer output oracle index is drawn from an outer input oracle or a prover message, with a
    type-coherence proof. This supports index-type-changing output routing (e.g. Spartan).
  - `projStmt` / `liftStmt` : the non-oracle input projection and output lift, matching the
    `projStmt` / `liftStmt` interface documented in `LiftContext/Reduction.lean`.

  We deliberately do **not** add these fields to `OracleStatement.Lens` itself (that would break
  every construction site repo-wide). Instead this is a separate structure that carries a
  `toLens : OracleStatement.Lens` so that all the value-level soundness / completeness machinery
  (`IsSound`, `IsComplete`, …) continues to apply to `toLens`. -/
structure OracleStatement.OracleLens
    {ι : Type} (oSpec : OracleSpec ι)
    (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [Oₛᵢ : ∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [Oₛₒ : ∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    {n : ℕ} (pSpec : ProtocolSpec n) [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] where
  /-- The underlying value-level oracle-statement lens (used by all the soundness / completeness
    conditions, which are stated purely in terms of values). -/
  toLens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  /-- Non-oracle input-statement projection (outer → inner). -/
  projStmt : OuterStmtIn → InnerStmtIn
  /-- Non-oracle output-statement lift (inner output → outer output, relying on the outer input). -/
  liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut
  /-- Routing of each *inner input* oracle query into an `OracleComp` over the *outer input* oracles
    (plus the shared `oSpec`), with `ReaderT` access to the outer (non-oracle) input statement.

    This is the heart of virtual oracle reductions: it is allowed to be non-invertible (e.g. a sum
    over many outer queries answering a single inner query). -/
  simOStmt : QueryImpl [InnerOStmtIn]ₒ
    (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ)))
  /-- Output-side embedding: each outer *output* oracle index is derived either from an outer input
    oracle (`Sum.inl`) or from a prover message (`Sum.inr`). Mirrors `OracleVerifier.embed`. -/
  embedOStmt : Outer_ιₛₒ ↪ Outer_ιₛᵢ ⊕ pSpec.MessageIdx
  /-- Type coherence for `embedOStmt`, mirroring `OracleVerifier.hEq`. -/
  hEqOStmt : ∀ i, OuterOStmtOut i = match embedOStmt i with
    | Sum.inl j => OuterOStmtIn j
    | Sum.inr j => pSpec.Message j
  /-- The output oracle exposes the same query and answer interface as its selected source.
  Equality of the carrier types alone does not establish equality of their public interfaces. -/
  outputInterface_heq : ∀ i, match embedOStmt i with
    | Sum.inl j => HEq (Oₛₒ i)
        (Oₛᵢ j)
    | Sum.inr j => HEq (Oₛₒ i)
        (Oₘ j)

namespace OracleStatement.OracleLens

variable {ι : Type} {oSpec : OracleSpec ι}
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, OracleInterface (pSpec.Message i)]

/-- The native output representation of the legacy lens, with actual interface coherence. -/
def toOutputEmbedding
    (lens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec) :
    OracleOutputEmbedding OuterOStmtIn pSpec.Message OuterOStmtOut where
  embed := lens.embedOStmt
  hEq := by
    intro i
    cases h : lens.embedOStmt i with
    | inl j => simpa only [h] using lens.hEqOStmt i
    | inr j => simpa only [h] using lens.hEqOStmt i
  outputInterface_heq := by
    intro i
    cases h : lens.embedOStmt i with
    | inl j => simpa only [h] using lens.outputInterface_heq i
    | inr j => simpa only [h] using lens.outputInterface_heq i

/-- The identity oracle-routing lens (over a single oracle-statement family `OuterOStmtIn` used for
  both input and output): identity on values, routes each inner input oracle query to the
  identically-indexed outer input oracle, and draws each output oracle statement from the
  corresponding input oracle. Mirrors `OracleVerifier.id`. -/
@[inline]
protected def id :
    OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
      OuterOStmtIn OuterOStmtIn OuterOStmtIn OuterOStmtIn pSpec where
  toLens := PFunctor.Lens.id _
  projStmt := id
  liftStmt := fun _ s => s
  simOStmt := fun q => ReaderT.mk fun _ =>
    (OracleComp.lift <| OracleSpec.query (spec := [OuterOStmtIn]ₒ) q :
      OracleComp (oSpec + [OuterOStmtIn]ₒ) _)
  embedOStmt := Function.Embedding.inl
  hEqOStmt := fun _ => rfl
  outputInterface_heq := fun _ => HEq.rfl

end OracleStatement.OracleLens

namespace Witness.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
end Witness.Lens

namespace Context.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

end Context.Lens

namespace OracleContext.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
end OracleContext.Lens

namespace Witness.InvLens

variable {OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
  (lens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

end Witness.InvLens

namespace Extractor.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

end Extractor.Lens

namespace Extractor.Lens.IsKnowledgeSound

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)}
    {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

-- The canonical statement-soundness instance includes `Nonempty InnerWitIn`, needed for
-- the input-witness shortcut in its knowledge-soundness law. No duplicate instance is installed.

end Extractor.Lens.IsKnowledgeSound

section SpecialCases

-- Plan (do not delete)

-- 1. When the lens is over the input context only (keeping the output the same)
-- 1.1. Over the input statement only
-- 1.1.1. When the map is an equivalence
-- 1.2. Over the input witness only
-- 1.2.1. When the map is an equivalence

-- NOTE for oracle statements as we haven't figured it out

-- 2. When the lens is over the output context only (keeping the input the same)
-- 2.1. Over the output statement only
-- 2.1.1. When the map is an equivalence
-- 2.2. Over the output witness only
-- 2.2.1. When the map is an equivalence

-- When does this lead to secure protocols? Since one of input / output is trivial, this essentially
-- reduces to the security of the zero-round reduction (that is either the on the input or the
-- output context)

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

namespace Statement.Lens

end Statement.Lens

namespace OracleStatement.Lens

-- Oracle-statement lens utilities.

end OracleStatement.Lens

namespace Witness.Lens

end Witness.Lens

namespace Witness.InvLens

end Witness.InvLens

namespace Context.Lens

end Context.Lens

namespace OracleContext.Lens

end OracleContext.Lens

namespace Extractor.Lens

end Extractor.Lens

end SpecialCases
