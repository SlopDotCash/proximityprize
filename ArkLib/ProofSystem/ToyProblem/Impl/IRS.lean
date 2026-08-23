/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ProofSystem.ToyProblem.Spec.General
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Toy problem — interleaved Reed-Solomon instantiation (ABF26 §6.3.1)

The first concrete parametrisation of the §6 toy-problem IOR from
ABF26 §6.3.1: take the underlying code `C` to be the (interleaved)
Reed-Solomon code `IRS[F, L, k, s]`. For our `s = 1` spec, this
degenerates to a plain Reed-Solomon code `RS[F, L, k]`.

This file specialises the abstract `ToyProblem.Spec.reduction` (and the
simplified-IOR `ToyProblem.SimplifiedIOR.reduction`) by setting

  `encode := ReedSolomon.encode (·) domain`

where `domain : Fin n ↪ F` is a smooth multiplicative coset of size
`n = Fintype.card ι` (per §6.3 the "common case" instantiation).

## Layout

* `reductionIRS` — non-oracle C6.2 IRS instantiation.
* `oracleReductionIRS` — oracle-flavour C6.2 IRS instantiation.
* `simplifiedReductionIRS` — non-oracle C6.9 IRS instantiation.

C6.9 does not have an oracle flavour: the framework's
`OracleVerifier.embed` cannot express the combined output oracle
`f_new := f₁ + γ·f₂`. See `Spec/SimplifiedIOR.lean` for details.

Concrete soundness-error analysis (§6.3.1's parameter computation,
Tables 2–3 of the paper) lives in a separate downstream file; this
file only ships the protocol-level specialisation.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.3.1, Tables 2 and 3).
-/

namespace ToyProblem

namespace Impl.IRS

open ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n k t : ℕ}
variable (domain : Fin n ↪ F)

/-- The §6.3.1 IRS instantiation of Construction 6.2 (`s = 1` case,
matching the protocol-spec's single-row codeword shape). Sets the
encoding function to Reed-Solomon's `encode` over `domain`. -/
noncomputable def reductionIRS :
    Reduction []ₒ
      (ToyProblem.Spec.Statement (F := F) k ×
        (∀ i, ToyProblem.Spec.OracleStatement (Fin n) F i))
      (ToyProblem.Spec.Witness (F := F) k)
      ToyProblem.Spec.OutputStatement
      ToyProblem.Spec.OutputWitness
      (ToyProblem.Spec.pSpec (ι := Fin n) (F := F) k t) :=
  ToyProblem.Spec.reduction (ι := Fin n) (F := F) (k := k) (t := t)
    (fun msg ↦ ReedSolomon.encode msg domain)

/-- The §6.3.1 IRS instantiation of Construction 6.9 (the simplified
"attack target" IOR). -/
noncomputable def simplifiedReductionIRS :
    Reduction []ₒ
      (ToyProblem.Spec.Statement (F := F) k ×
        (∀ i, ToyProblem.Spec.OracleStatement (Fin n) F i))
      (ToyProblem.Spec.Witness (F := F) k)
      (ToyProblem.SimplifiedIOR.OutputStatement (F := F) k ×
        (∀ i, ToyProblem.SimplifiedIOR.OutputOracleStatement (Fin n) F i))
      (ToyProblem.SimplifiedIOR.OutputWitness (F := F) k)
      (ToyProblem.SimplifiedIOR.pSpec (F := F)) :=
  ToyProblem.SimplifiedIOR.reduction (ι := Fin n) (F := F) (k := k)

/-- Oracle-flavour C6.2 IRS instantiation. -/
noncomputable def oracleReductionIRS :
    OracleReduction []ₒ
      (ToyProblem.Spec.Statement (F := F) k)
      (ToyProblem.Spec.OracleStatement (Fin n) F)
      (ToyProblem.Spec.Witness (F := F) k)
      ToyProblem.Spec.OutputStatement
      ToyProblem.Spec.OutputOracleStatement
      ToyProblem.Spec.OutputWitness
      (ToyProblem.Spec.pSpec (ι := Fin n) (F := F) k t) :=
  ToyProblem.Spec.oracleReduction (ι := Fin n) (F := F) (k := k) (t := t)
    (fun msg ↦ ReedSolomon.encode msg domain)

end Impl.IRS

end ToyProblem
