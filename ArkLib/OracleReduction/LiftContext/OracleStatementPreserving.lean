/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.LiftContext.Reduction

/-!
  ## Oracle-statement-preserving context lifting

  `OracleVerifier.liftContext` (in `LiftContext/OracleReduction.lean`) cannot be
  implemented for a fully general oracle-statement lens: the lens transforms the
  *bundled* statements as data, but the `OracleVerifier` structure requires the
  output oracle statements to be a literal subset of the input oracle statements
  and prover messages (via `embed`/`hEq`), and a data-level bundle lens carries
  no map between the oracle *index* types from which such an embedding could be
  built. (See the design note in `LiftContext/Lens.lean`: the resolution is for
  oracle-statement lenses to carry query-simulation data — the upstream
  Interaction migration.)

  This file gives the honest, fully-proven construction for the common case that
  the missing data is trivial: the **oracle-statement-preserving** lift, where
  the lens transforms only the non-oracle statement and leaves the oracle
  statements (input and output) fixed. This covers the typical situation of
  embedding a sub-reduction (e.g. a sum-check) into a larger context where the
  oracle commitments are unchanged — `embed`/`hEq` then transport directly from
  the inner verifier.
-/

open OracleSpec OracleComp ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier

/-- The oracle-statement-preserving lift of an oracle verifier: transform only
the non-oracle statement (via a `Statement.Lens`), keeping the oracle statements
fixed. The output-oracle embedding and type-equalities are inherited unchanged
from the inner verifier. Fully implementable, in contrast to the fully general
`OracleVerifier.liftContext`. -/
def liftContextStmt
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut OStmtOut pSpec) :
    OracleVerifier oSpec OuterStmtIn OStmtIn OuterStmtOut OStmtOut pSpec where
  verify := fun outerStmtIn challenges =>
    (fun innerStmtOut => lens.lift outerStmtIn innerStmtOut) <$>
      V.verify (lens.proj outerStmtIn) challenges
  embed := V.embed
  hEq := V.hEq

@[simp]
lemma liftContextStmt_embed
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut OStmtOut pSpec) :
    (V.liftContextStmt lens).embed = V.embed := rfl

@[simp]
lemma liftContextStmt_verify
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut OStmtOut pSpec)
    (outerStmtIn : OuterStmtIn) (challenges : pSpec.Challenges) :
    (V.liftContextStmt lens).verify outerStmtIn challenges
      = (fun s => lens.lift outerStmtIn s) <$> V.verify (lens.proj outerStmtIn) challenges :=
  rfl

-- (An auxiliary / commutation lemma holds but
-- requires the OptionT/simulateQ map-distribution machinery; omitted here as
-- the security properties are inherited via the existing
-- ported lemmas in .)

end OracleVerifier

namespace OracleVerifier

variable {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
  [∀ i, OracleInterface (InnerOStmtOut i)]

/-- The output-oracle-reselecting lift of an oracle verifier: in addition to a
non-oracle statement lens, the outer output oracle statements are a reindexing
(`oₒ`, injective) of the inner ones, with matching types (`hOO`). The input
oracle statements are shared. This strictly generalises `liftContextStmt`
(which is the `oₒ = id` case) and covers the realistic protocol-composition
scenario where a lift never adds input oracles but may drop/reselect outputs.
Fully implementable: `embed` composes `oₒ` with the inner embedding, `hEq`
chains the type equalities. -/
def liftContextReselect
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (oₒ : ιₛₒ ↪ Inner_ιₛₒ)
    (hOO : ∀ i, OStmtOut i = InnerOStmtOut (oₒ i))
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut InnerOStmtOut pSpec) :
    OracleVerifier oSpec OuterStmtIn OStmtIn OuterStmtOut OStmtOut pSpec where
  verify := fun outerStmtIn challenges =>
    (fun innerStmtOut => lens.lift outerStmtIn innerStmtOut) <$>
      V.verify (lens.proj outerStmtIn) challenges
  embed := oₒ.trans V.embed
  hEq := fun i => by
    rw [hOO i]
    exact V.hEq (oₒ i)

@[simp]
lemma liftContextReselect_embed
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (oₒ : ιₛₒ ↪ Inner_ιₛₒ) (hOO : ∀ i, OStmtOut i = InnerOStmtOut (oₒ i))
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut InnerOStmtOut pSpec) :
    (V.liftContextReselect lens oₒ hOO).embed = oₒ.trans V.embed := rfl

@[simp]
lemma liftContextReselect_verify
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (oₒ : ιₛₒ ↪ Inner_ιₛₒ) (hOO : ∀ i, OStmtOut i = InnerOStmtOut (oₒ i))
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (outerStmtIn : OuterStmtIn) (challenges : pSpec.Challenges) :
    (V.liftContextReselect lens oₒ hOO).verify outerStmtIn challenges
      = (fun s => lens.lift outerStmtIn s) <$> V.verify (lens.proj outerStmtIn) challenges :=
  rfl

end OracleVerifier
