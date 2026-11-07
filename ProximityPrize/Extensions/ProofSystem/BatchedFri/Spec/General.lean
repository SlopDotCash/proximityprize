/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.BatchedFri.Spec.General

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.General
import ProximityPrize.Extensions.OracleReduction.LiftContext.OracleReduction
import ProximityPrize.Extensions.ProofSystem.BatchedFri.Spec.SingleRound
import ProximityPrize.Extensions.ProofSystem.Fri.Spec.General


/-!
# The general Batched FRI protocol

We assemble the whole-protocol Batched FRI oracle reduction by composing the single-round batched
FRI reduction with the general FRI reduction. We fix the protocol parameters (field `F`, evaluation
domain of size `2 ^ n`, folding count `k`, per-round folding degrees `s`, final degree bound `d`,
number of consistency checks `l`, and number of batched polynomials `m`) and define the
whole-protocol input relation and its sequential composition.
-/

namespace BatchedFri

namespace Spec

open OracleSpec OracleComp ProtocolSpec NNReal BatchingRound Domain

/- Batched FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `l`, the number of round consistency checks to be run by the query round.
  - `m`, number of batched polynomials.
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l m : ℕ)
variable {ω : SmoothCosetFftDomain n F}

-- DEFINITION COMPLETED (2026-06-04): whole-protocol batched-FRI input relation. The protocol input
-- is a batch of `m + 1` purported codewords on the full evaluation domain `ω`, each committed to a
-- low-degree witness polynomial (degree `< 2 ^ (∑ s) * d`). Following [BCIKS20 §8]/[FRI1216] this
-- is the batched proximity relation: each oracle is the honest evaluation of its witness polynomial
-- AND
-- is within relative Hamming distance `δ` of the Reed–Solomon code on `ω` of degree `2 ^ (∑ s) * d`
-- (`δᵣ(fⱼ, RS) ≤ δ`). The witness/agreement half is exactly `BatchingRound.inputRelation`; the δ-
-- proximity half is the soundness target the batching+FRI reduction tests.

/-- The full-domain Reed–Solomon code on `ω` of degree `2 ^ (∑ s) * d`, the batched FRI degree
  bound; uses the `Subtype.val` embedding of `ω.toFinset` into `F`. -/
noncomputable def batchCode : Submodule F (ω.toFinset → F) :=
  ReedSolomon.code
    (⟨fun x => x.1, fun _ _ h => Subtype.ext h⟩ : ω.toFinset ↪ F)
    (2 ^ (∑ i, (s i).1) * d)

-- /- Input/Output relations for the Batched FRI protocol. -/
def liftingLens :
    OracleContext.Lens
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
    (Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
    (OracleStatement m ω) (Fri.Spec.FinalOracleStatement s ω)
    (Fri.Spec.OracleStatement s ω 0) (Fri.Spec.FinalOracleStatement s ω)
    (Fri.Spec.Witness F s d 0) (Fri.Spec.Witness F s d (Fin.last (k + 1)))
    (Fri.Spec.Witness F s d 0) (Fri.Spec.Witness F s d (Fin.last (k + 1))) where
  stmt := Witness.InvLens.ofOutputOnly <| fun ⟨⟨cs, stmt⟩, ostmt⟩ =>
    ⟨
      stmt,
      fun j v =>
          have : v.1 ∈ ω.toFinset := by {
            simp only [CosetFftDomainClass.mem_toFinset_iff_mem]
            rcases j with ⟨j, h⟩
            have : j = 0 := by simpa using h
            simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.reduceAdd] at v
            rcases v with ⟨v, h'⟩
            simp only
            subst this
            simp only [finRangeTo.eq_1, List.take_zero, List.toFinset_nil, Finset.sum_empty,
              Nat.sub_zero, CosetFftDomainClass.mem_toFinset_iff_mem] at h'
            rw [←CosetFftDomainClass.mem_subdomain_0_iff_mem]
            exact h'
          }
          (ostmt 0) ⟨v.1, this⟩ + ∑ j, cs j * ostmt j.succ ⟨v.1, this⟩
    ⟩
  wit  := Witness.Lens.id

/- The old coefficient-carrying `batchedFRIOracleLens` and `liftedFRI` are retired.
Canonical `batchedFRIreduction` materializes the generator-selected batching output before
appending the FRI reduction. The value-level projection above remains useful independently.
See `scripts/integration/batched-fri-tail-migration.json`. -/

end Spec

end BatchedFri
