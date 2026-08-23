/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Basic
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Linear
import CompPoly.Univariate.ToPoly.Impl

/-!
# The Batched FRI protocol

  We describe the Batched FRI oracle reduction as a random linear combination round,
  and the FRI oracle reduction.

 -/

namespace BatchedFri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Fri NNReal Domain

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree", for `s = 1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `m` the number of polynomials batched
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (m : ℕ)
variable {ω : SmoothCosetFftDomain n F}


/-- An oracle for each batched polynomial. -/
@[reducible]
def OracleStatement (ω : SmoothCosetFftDomain n F) : Fin (m + 1) → Type :=
  fun _ => ω.toFinset → F

/-- The Batched FRI protocol has as witness for each batched polynomial
    that is supposed to correspond to the putative codewords in the oracle statement.
    We use `CompPoly.CPolynomial`, the computable representation, by way of the
    iso to Mathlib's `Polynomial`. -/
@[reducible]
def Witness (F : Type) [Zero F] {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+) (m : ℕ) :=
  Fin (m + 1) → CompPoly.CPolynomial.degreeLT (R := F) (2 ^ (∑ i, (s i).1) * d)

instance : ∀ j, OracleInterface (OracleStatement m ω j) :=
  fun _ => inferInstance

namespace BatchingRound

-- DEFINITION COMPLETED (2026-06-04): batching-round input relation. The batched-FRI input is a
-- collection of `m + 1` purported codewords on the full domain `ω`, each committed to its own
-- low-degree witness polynomial (degree `< 2 ^ (∑ s) * d`). Following [BCIKS20 §8]/[FRI1216], the
-- well-formed-input relation asserts every batched oracle is the honest evaluation of its witness
-- polynomial on `ω`. (No `δ`: the relation is stated on the witnessed polynomials directly; the
-- subsequent proximity claim is carried by the FRI round-0 relation after batching — see
-- `outputRelation`, which composes with `Fri.Spec.FoldPhase.inputRelation`.)
def inputRelation :
    Set
      (
        (Unit × (∀ j, OracleStatement m ω j)) ×
        Witness F s d m
      ) :=
  {ctx | ∀ j x, ctx.1.2 j x = (ctx.2 j).1.eval x.1}

-- DEFINITION COMPLETED (2026-06-04): batching-round output relation. After the verifier sends the
-- random batching coefficients, the protocol hands off to the FRI round-0 reduction on the single
-- batched codeword. The relation is the FRI round-0 well-formedness clause: the (single) round-0
-- oracle on `ω = subdomainNatReversed 0` is the honest evaluation of the batched witness
-- polynomial. This is exactly the witness/oracle-agreement half of
-- `Fri.Spec.FoldPhase.inputRelation` at `i = 0`, so the batching reduction composes with FRI (the
-- random-linear-combination batching of the `m + 1`
-- oracles is realised in `liftingLens.stmt`).
def outputRelation :
    Set
      (
        (Fri.Spec.Statement F (0 : Fin (k + 1)) ×
        (∀ j, Fri.Spec.OracleStatement s ω (0 : Fin (k + 1)) j)) ×
        Fri.Spec.Witness F s d (0 : Fin (k + 2))
      ) :=
  {ctx | ∀ x, ctx.1.2 0 x = ctx.2.1.eval x.1}

/-- The verifier send `m` field elements to batch the `m + 1` batched polynomials,
    the prover then returns the putative codeword corresponding to the batched polynomial -/
@[reducible]
def batchSpec (F : Type) (m : ℕ) : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Fin m → F]⟩

/- `OracleInterface` instance for `pSpec` of the non-final folding rounds. -/
instance : ∀ j, OracleInterface ((batchSpec F m).Message j)
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((batchSpec F m).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ j, Inhabited ((batchSpec F m).Challenge j) := by
  intro j
  letI : Inhabited F := ⟨0⟩
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 => exact j1.elim0
  subst h_j_eq_0
  simpa [batchSpec, Challenge] using (inferInstance : Inhabited (Fin m → F))

noncomputable instance : ∀ j, Fintype ((batchSpec F m).Challenge j) := by
  intro j
  letI : Fintype F := Fintype.ofFinite _
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 => exact j1.elim0
  subst h_j_eq_0
  simpa [batchSpec, Challenge] using (inferInstance : Fintype (Fin m → F))

/-- The batching round oracle prover. -/
def batchProver :
    OracleProver []ₒ
    Unit (OracleStatement m ω) (Witness F s d m)
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
      (OracleStatement m ω) (Fri.Spec.Witness F s d (0 : Fin (k + 2)))
    (batchSpec F m) where
  PrvState
  | 0 => (∀j, OracleStatement m ω j) × Witness F s d m
  | 1 => (Fin m → F) × (∀j, OracleStatement m ω j) × Fri.Spec.Witness F s d (0 : Fin (k + 2))

  input := fun i => ⟨i.1.2, i.2⟩

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨os, ps⟩ => pure <|
    fun (cs : Fin m → F) =>
      let q : CompPoly.CPolynomial F :=
        (ps 0).1 + ∑ i, CompPoly.CPolynomial.C (cs i) * (ps i.succ).1
      ⟨cs, os,
        ⟨
          q,
          by
            unfold Fri.Spec.Witness
            simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
            rw [CompPoly.CPolynomial.degreeLT_toPoly]
            change (((ps 0).1 + ∑ i, CompPoly.CPolynomial.C (cs i) * (ps i.succ).1)
              : CompPoly.CPolynomial F).toPoly ∈ _
            rw [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_sum]
            simp only [CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly]
            set q : F[X] :=
              (ps 0).1.toPoly + ∑ i, Polynomial.C (cs i) * (ps i.succ).1.toPoly with hq
            apply mem_degreeLT.mpr
            by_cases h : q = 0
            · rw [h]
              simp only [degree_zero, finRangeTo, List.take_zero, List.toFinset_nil, sum_empty,
                tsub_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
              exact compareOfLessAndEq_eq_lt.mp rfl
            · rw [Polynomial.degree_eq_natDegree h]
              norm_cast
              apply Nat.lt_of_le_pred (by simp)
              transitivity
              · exact Polynomial.natDegree_add_le _ _
              · apply Nat.max_le_of_le_of_le
                · have h_ps0 := mem_degreeLT.mp
                    ((CompPoly.CPolynomial.degreeLT_toPoly (R := F)).mp (ps 0).2)
                  by_cases h₀ : (ps 0).1.toPoly = 0
                  · rw [h₀]
                    simp
                  · erw
                      [
                        Polynomial.degree_eq_natDegree h₀,
                        WithBot.coe_lt_coe,
                        Nat.cast_id, Nat.cast_id
                      ] at h_ps0
                    exact Nat.le_pred_of_lt h_ps0
                · apply Polynomial.natDegree_sum_le_of_forall_le
                  intros i _
                  by_cases h : Polynomial.C (cs i) = 0
                  · rw [h]
                    simp
                  · by_cases h' : (ps i.succ).1.toPoly = 0
                    · rw [h']
                      simp
                    · rw [Polynomial.natDegree_mul h h', Polynomial.natDegree_C, zero_add]
                      have h_psi := mem_degreeLT.mp
                        ((CompPoly.CPolynomial.degreeLT_toPoly (R := F)).mp (ps i.succ).2)
                      erw
                        [
                          Polynomial.degree_eq_natDegree h',
                          WithBot.coe_lt_coe,
                          Nat.cast_id, Nat.cast_id
                        ] at h_psi
                      exact Nat.le_pred_of_lt h_psi
        ⟩
      ⟩

  output := fun ⟨cs, os, p⟩ => pure <|
    ⟨⟨⟨cs, Fin.elim0⟩, os⟩, p⟩

/-- The batching round oracle verifier. -/
def batchVerifier :
    OracleVerifier []ₒ
    Unit (OracleStatement m ω)
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
    (OracleStatement m ω)
    (batchSpec F m) where
  verify := fun _ chals => pure ⟨chals ⟨0, by simp⟩, Fin.elim0⟩
  embed :=
    ⟨
      fun i => Sum.inl i,
      by intros _; aesop
    ⟩
  hEq := by simp

/-- The batching round oracle reduction. -/
@[reducible]
def batchOracleReduction :
    OracleReduction []ₒ
    Unit (OracleStatement m ω) (Witness F s d m)
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
    (OracleStatement m ω)
    (Fri.Spec.Witness F s d (0 : Fin (k + 2)))
    (batchSpec F m) where
  prover := batchProver s d m
  verifier := batchVerifier (k := k) m

/-- The batching-round oracle verifier passes every output oracle through to the unchanged input
oracle (`embed = Sum.inl`, `OStmtIn = OStmtOut = OracleStatement m ω`, `hEq` by `simp`) and exposes
no message oracle, so its `AppendCoherent` coherence holds by `rfl`. Used to `.append` the batching
round onto the lifted FRI reduction. -/
instance instBatchVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (batchVerifier (k := k) m (ω := ω)) where
  hCohInl := fun a k h => by
    have : a = k := by
      simpa only [batchVerifier, Function.Embedding.coeFn_mk, Sum.inl.injEq] using h
    subst this; rfl
  hCohInr := fun a k h => by
    simp only [batchVerifier, Function.Embedding.coeFn_mk, reduceCtorEq] at h

instance instBatchOracleReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (Oₛ₁ := (inferInstance : ∀ j, OracleInterface (OracleStatement m ω j)))
      (Oₛ₂ := (inferInstance : ∀ j, OracleInterface (OracleStatement m ω j)))
      (Oₘ₁ := (inferInstance : ∀ j, OracleInterface ((batchSpec F m).Message j)))
      (batchOracleReduction s d m).verifier :=
  instBatchVerifierAppendCoherent (k := k) m (ω := ω)

end BatchingRound

end Spec

end BatchedFri
