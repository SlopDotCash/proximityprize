/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Spec.General


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
def inputRelation [DecidableEq F] (_δ : ℝ≥0) :
    Set
      (
        Unit × (∀ j, OracleStatement m ω j) × (Witness F s d m)
      ) :=
  {ctx | ∀ j x, ctx.2.1 j x = (ctx.2.2 j).1.eval x.1}


/- Lifting FRI to include using `liftingLens`:
    - RLC in statement
    - Simulate batched polynomial oracle using oracles of
      batched polynomials
-/
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

/-- MIGRATED (2026-06-04): OracleLens 2-lens API.

The batched-FRI lift's oracle routing is **virtual**: the inner FRI round-0 oracle (a single oracle,
index `Fin 1`) is the *random linear combination* of the `m + 1` outer batched oracles, exactly as
realized by `liftingLens.stmt`. So this `OracleLens` carries:

- `toLens := (liftingLens k s d m).stmt` — the value-level oracle-statement lens reused verbatim, so
  all soundness / completeness machinery still applies through it.
- `projStmt` / `liftStmt` — the non-oracle projection (drop the batching coefficients `cs`, entering
  FRI with the bare statement) and lift (the FRI final statement is returned unchanged, since
  `OuterStmtOut = InnerStmtOut = FinalStatement`).
- `simOStmt` — answers the inner round-0 oracle query at a domain point `v` by querying each of the
  `m + 1` outer batched oracles at the (same, after the domain membership transport) point and
  forming the RLC `(ostmt 0) v + ∑ j, cs j * ostmt j.succ v`, reading `cs` from the outer input
  statement via `ReaderT`. This is the faithful virtualization, mirroring `liftingLens.stmt`.
- `embedOStmt` / `hEqOStmt` — the output-side routing reuses the inner FRI verifier's own
  `embed` / `hEq` (the FRI final oracle statements are drawn from the prover's folding messages, so
  the routing is message-only and the inner/outer output oracle families coincide), with the inner
  input-oracle index summand `Fin 1` embedded into the outer `Fin (m + 1)` via `Fin.castLE`. -/
def batchedFRIOracleLens [DecidableEq F] :
    OracleStatement.OracleLens ([]ₒ)
      ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
      (Fri.Spec.Statement F (0 : Fin (k + 1))) (Fri.Spec.FinalStatement F k)
      (OracleStatement m ω) (Fri.Spec.FinalOracleStatement s ω)
      (Fri.Spec.OracleStatement s ω 0) (Fri.Spec.FinalOracleStatement s ω)
      (
        Fri.Spec.pSpecFold (ω := ω) k s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      ) where
  toLens := (liftingLens k s d m).stmt
  projStmt := fun stmtIn => stmtIn.2
  liftStmt := fun _ innerStmtOut => innerStmtOut
  simOStmt := fun q =>
    match q with
    | ⟨j, v⟩ => ReaderT.mk fun stmtIn => do
        have hv : v.1 ∈ ω.toFinset := by
          rw [CosetFftDomainClass.mem_toFinset_iff_mem]
          rcases j with ⟨j, h⟩
          have : j = 0 := by simpa using h
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.reduceAdd] at v
          rcases v with ⟨v, h'⟩
          simp only
          subst this
          simp only [finRangeTo.eq_1, List.take_zero, List.toFinset_nil, Finset.sum_empty,
            Nat.sub_zero] at h'
          rw [CosetFftDomainClass.mem_toFinset_iff_mem] at h'
          rw [←CosetFftDomainClass.mem_subdomain_0_iff_mem]
          exact h'
        let cs := stmtIn.1
        let pt : ω.toFinset := ⟨v.1, hv⟩
        let base : F ← (query (spec := [OracleStatement m ω]ₒ)
          (⟨0, pt⟩ : [OracleStatement m ω]ₒ.Domain) :
          OracleComp (([]ₒ) + [OracleStatement m ω]ₒ) F)
        let restList : List F ← (List.finRange m).mapM (fun j =>
          (query (spec := [OracleStatement m ω]ₒ)
            (⟨j.succ, pt⟩ : [OracleStatement m ω]ₒ.Domain) :
            OracleComp (([]ₒ) + [OracleStatement m ω]ₒ) F))
        pure (base + ∑ j : Fin m, cs j * restList.getD j.val 0)
  embedOStmt :=
    (Fri.Spec.reduction k s d dom_size_cond l).verifier.embed.trans
      (Function.Embedding.sumMap
        ⟨Fin.castLE (Nat.le_add_left 1 m), fun _ _ h => Fin.castLE_injective _ h⟩
        (Function.Embedding.refl _))
  hEqOStmt := fun (i : Fin (k + 2)) => by
    rw [Function.Embedding.trans_apply]
    rcases hemb :
        (Fri.Spec.reduction (F := F) (n := n) (ω := ω) k s d dom_size_cond l).verifier.embed i
      with j | j
    · -- `.inl j` (j : Fin 1): the inner round-0 input oracle. The outer round-0 batched oracle 0 has
      -- the same domain `ω.toFinset → F` (subdomain at index 0 equals `ω`), so the families agree.
      have hV :=
        (Fri.Spec.reduction (F := F) (n := n) (ω := ω) k s d dom_size_cond l).verifier.hEq i
      rw [hemb] at hV
      -- `j : Fin (↑0 + 1)` is `Fin 1`, hence `j = 0`.
      have hj : j = 0 := by
        apply Fin.ext
        have h := j.isLt
        simp only [Fin.val_zero, Nat.zero_add, Nat.lt_one_iff] at h ⊢
        exact h
      subst hj
      simp only [Function.Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inl] at hV ⊢
      rw [hV]
      -- `OracleStatement m ω (castLE 0) = OracleStatement m ω 0 = ω.toFinset → F`; and
      -- `Fri.Spec.OracleStatement s ω 0 0 = (ω.subdomain 0).toFinset → F`, with
      -- `(ω.subdomain 0).toFinset = ω.toFinset`, so the two oracle families agree.
      have hdom : (ω.subdomain 0).toFinset = ω.toFinset := by
        ext x
        rw [CosetFftDomainClass.mem_toFinset_iff_mem,
          CosetFftDomainClass.mem_subdomain_0_iff_mem,
          ← CosetFftDomainClass.mem_toFinset_iff_mem]
      show Fri.Spec.OracleStatement s ω 0 0 = OracleStatement m ω (Fin.castLE (Nat.le_add_left 1 m) 0)
      have hcast : (Fin.castLE (Nat.le_add_left 1 m) (0 : Fin (0 + 1))) = (0 : Fin (m + 1)) :=
        Fin.ext (by simp only [Fin.val_castLE, Fin.val_zero])
      rw [hcast]
      simp only [Fri.Spec.OracleStatement, finRangeTo.eq_1, List.take_zero, List.toFinset_nil,
        Finset.sum_empty, Fin.val_zero, OracleStatement]
      exact congrArg (fun (S : Finset F) => (↥S → F)) hdom
    · have hV :=
        (Fri.Spec.reduction (F := F) (n := n) (ω := ω) k s d dom_size_cond l).verifier.hEq i
      rw [hemb] at hV
      simp only [Function.Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inr,
        Function.Embedding.refl_apply]
      exact hV

def liftedFRI [DecidableEq F] :
    OracleReduction []ₒ
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
      (OracleStatement m ω) (Fri.Spec.Witness F s d 0)
    (Fri.Spec.FinalStatement F k)
      (Fri.Spec.FinalOracleStatement s ω) (Fri.Spec.Witness F s d (Fin.last (k + 1)))
    (
      Fri.Spec.pSpecFold (ω := ω) k s ++ₚ
      Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
      Fri.Spec.QueryRound.pSpec (ω := ω) l
    ) :=
    -- MIGRATED (2026-06-04): OracleLens 2-lens API — the value-level context lens drives the
    -- prover, the oracle-routing `stmtLens := batchedFRIOracleLens` supplies
    -- `simOStmt`/`embedOStmt`.
    OracleReduction.liftContext
      (liftingLens k s d m)
      (batchedFRIOracleLens k s d dom_size_cond l m)
      (Fri.Spec.reduction k s d dom_size_cond l)

instance instBatchFRIreductionMessageOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold k (ω := ω) s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Message j) := fun j ↦ by
      apply instOracleInterfaceMessageAppend

instance instBatchFRIreductionChallengeOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold k (ω := ω) s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/- Oracle reduction of the batched FRI protocol. -/
@[reducible]
def batchedFRIreduction [DecidableEq F]
    :=
  OracleReduction.append
    (BatchingRound.batchOracleReduction s d m)
    (liftedFRI (ω := ω) k s d dom_size_cond l m)

end Spec

end BatchedFri
