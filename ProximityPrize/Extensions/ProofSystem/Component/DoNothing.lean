/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Component.DoNothing

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.OracleZeroKnowledge

/-!
  # The Trivial (Oracle) Reduction: Do Nothing!

  This is a zero-round (oracle) reduction. Both the (oracle) prover and the (oracle) verifier simply
  pass on their inputs unchanged.

  We still define this as the base for realizing other zero-round reductions, via lens / lifting.

  NOTE: we have already defined these as trivial (oracle) reductions
-/

namespace DoNothing

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (Witness : Type)

section Reduction

variable {oSpec} {Statement} {Witness}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (rel : Set (Statement × Witness))

/-- The `DoNothing` reduction is perfectly HVZK for any relation. -/
@[simp]
theorem reduction_perfectHVZK :
    Reduction.perfectHVZK init impl rel (reduction oSpec Statement Witness)
      Reduction.idTranscriptSimulator :=
  Reduction.id_perfectHVZK init impl rel

/-- The `DoNothing` reduction is statistically HVZK for any relation and error budget. -/
@[simp]
theorem reduction_statisticalHVZK (ε : NNReal) :
    Reduction.statisticalHVZK init impl rel (reduction oSpec Statement Witness)
      Reduction.idTranscriptSimulator ε :=
  (reduction_perfectHVZK (oSpec := oSpec) (Statement := Statement)
    (Witness := Witness) (init := init) (impl := impl) rel).statisticalHVZK ε

/-- The `DoNothing` reduction has an explicit perfect-HVZK simulator for any relation. -/
@[simp]
theorem reduction_isHVZK :
    Reduction.isHVZK init impl rel (reduction oSpec Statement Witness) :=
  Reduction.id_isHVZK init impl rel

/-- The `DoNothing` reduction has statistical HVZK for any relation and error budget. -/
@[simp]
theorem reduction_isStatHVZK (ε : NNReal) :
    Reduction.isStatHVZK init impl rel (reduction oSpec Statement Witness) ε :=
  (reduction_isHVZK (oSpec := oSpec) (Statement := Statement)
    (Witness := Witness) (init := init) (impl := impl) rel).isStatHVZK ε

#print axioms DoNothing.reduction_perfectHVZK
#print axioms DoNothing.reduction_statisticalHVZK
#print axioms DoNothing.reduction_isHVZK
#print axioms DoNothing.reduction_isStatHVZK

end Reduction

section OracleReduction

variable {oSpec} {Statement} {OStatement} {Witness}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (rel : Set ((Statement × (∀ i, OStatement i)) × Witness))
  (relOut : Set ((Statement × Witness) × (∀ i, OStatement i)))

/-- The `DoNothing` oracle reduction, viewed as a plain reduction, is perfectly HVZK for any
relation. This avoids requiring the `OracleReduction`-specific ZK wrapper API at this import site. -/
@[simp]
theorem oracleReduction_toReduction_perfectHVZK :
    Reduction.perfectHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness).toReduction
      Reduction.idTranscriptSimulator :=
  Reduction.id_perfectHVZK init impl rel

/-- The `DoNothing` oracle reduction, viewed as a plain reduction, is statistically HVZK for any
relation and error budget. -/
@[simp]
theorem oracleReduction_toReduction_statisticalHVZK (ε : NNReal) :
    Reduction.statisticalHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness).toReduction
      Reduction.idTranscriptSimulator ε :=
  (oracleReduction_toReduction_perfectHVZK (oSpec := oSpec) (Statement := Statement)
    (OStatement := OStatement) (Witness := Witness) (init := init) (impl := impl)
    rel).statisticalHVZK ε

/-- The `DoNothing` oracle reduction, viewed as a plain reduction, has an explicit perfect-HVZK
simulator for any relation. -/
@[simp]
theorem oracleReduction_toReduction_isHVZK :
    Reduction.isHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness).toReduction :=
  Reduction.id_isHVZK init impl rel

/-- The `DoNothing` oracle reduction, viewed as a plain reduction, has statistical HVZK for any
relation and error budget. -/
@[simp]
theorem oracleReduction_toReduction_isStatHVZK (ε : NNReal) :
    Reduction.isStatHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness).toReduction ε :=
  (oracleReduction_toReduction_isHVZK (oSpec := oSpec) (Statement := Statement)
    (OStatement := OStatement) (Witness := Witness) (init := init) (impl := impl)
    rel).isStatHVZK ε

/-- The `DoNothing` oracle reduction is perfectly HVZK for any oracle-input relation. -/
@[simp]
theorem oracleReduction_perfectHVZK :
    OracleReduction.perfectHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness)
      Reduction.idTranscriptSimulator :=
  OracleReduction.id_perfectHVZK init impl rel

/-- The `DoNothing` oracle reduction is statistically HVZK for any oracle-input relation and error
budget. -/
@[simp]
theorem oracleReduction_statisticalHVZK (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness)
      Reduction.idTranscriptSimulator ε :=
  OracleReduction.id_statisticalHVZK init impl rel ε

/-- The `DoNothing` oracle reduction has an explicit perfect-HVZK simulator for any oracle-input
relation. -/
@[simp]
theorem oracleReduction_isHVZK :
    OracleReduction.isHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness) :=
  OracleReduction.id_isHVZK init impl rel

/-- The `DoNothing` oracle reduction has statistical HVZK for any oracle-input relation and error
budget. -/
@[simp]
theorem oracleReduction_isStatHVZK (ε : NNReal) :
    OracleReduction.isStatHVZK init impl rel
      (oracleReduction oSpec Statement OStatement Witness) ε :=
  OracleReduction.id_isStatHVZK init impl rel ε

#print axioms DoNothing.oracleReduction_toReduction_perfectHVZK
#print axioms DoNothing.oracleReduction_toReduction_statisticalHVZK
#print axioms DoNothing.oracleReduction_toReduction_isHVZK
#print axioms DoNothing.oracleReduction_toReduction_isStatHVZK
#print axioms DoNothing.oracleReduction_perfectHVZK
#print axioms DoNothing.oracleReduction_statisticalHVZK
#print axioms DoNothing.oracleReduction_isHVZK
#print axioms DoNothing.oracleReduction_isStatHVZK

end OracleReduction

end DoNothing
