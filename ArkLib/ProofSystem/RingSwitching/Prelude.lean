/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Algebra
import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import ArkLib.ProofSystem.RingSwitching.Packing.Profile
import ArkLib.ProofSystem.RingSwitching.Packing.ProfileCoordinates
import ProximityPrize.Extensions.Data.MvPolynomial.Multilinear
import ProximityPrize.Extensions.OracleReduction.Basic
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
import CompPoly.Fields.Binary.Tower.TensorAlgebra
import ArkLib.ProofSystem.RingSwitching.Profile
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Structured
import ArkLib.ToMathlib.PolynomialCombinatorialAuxiliary
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Ring-Switching IOP Prelude

This module contains the core definitions and infrastructure for the ring-switching IOP,
including tensor algebra operations, field extension handling, and basic protocol types.

## Main Components

1. **Tensor Algebra operations**: Operations for handling tensor products
between small field K and large field L, including embeddings `φ₀ : L → L ⊗[K] L`,
`φ₁ : L → L ⊗[K] L`, and row/column decompositions with respect to a `K`-basis `β`.
2. **Protocol Types**: Statement and witness types for each phase
3. **Security Definitions**: Relations & Kstate for security analysis
-/


noncomputable section

namespace RingSwitching

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial TensorProduct
open scoped NNReal
open Sumcheck.Structured

/- This section defines generic preliminaries for the ring-switching protocol. -/
section Preliminaries

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

section TensorAlgebraOps
/-!
## Enhanced Tensor Algebra Operations

Additional tensor algebra operations for the enhanced protocol specification.
Based on the tensor algebra theory from Section 2.1.
-/

open Module
end TensorAlgebraOps

section ProtocolTypes
/-!
## Enhanced Protocol Type Definitions (Interfaces between phases)

We define the Statement and Witness types at the boundaries of each phase
following the enhanced specification.
-/

structure BatchingWitIn where
  t : MultilinearPoly K ℓ
  t' : MultilinearPoly L ℓ'

structure BatchingStmtIn where
  t_eval_point : Fin ℓ → L -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L -- s = t(r) => the original claim to verify

structure RingSwitchingBaseContext (P : RingSwitchingProfile K L κ)
    extends (SumcheckBaseContext L ℓ) where
  -- context from batching phase
  s_hat : P.A -- ŝ
  r_batching : Fin κ → L -- r''

-- `SumcheckWitness` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured` (the data shape is
-- generic and degree-neutral; only the per-round prover/verifier in `SumcheckPhase.lean` consume
-- it). Binius ring-switching is the degree-2 case `H = m · t'`, so this Binius-local abbrev pins
-- `d := 2`. Other instantiations (e.g. Hachi at `d := 2b+1`) pin their own degree — no
-- instantiation is privileged by a default on the generic type. The packed polynomial `t'` and
-- round polynomial `H` (after fixing previous challenges) live in the same structure.
abbrev SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) :=
  Sumcheck.Structured.SumcheckWitness L ℓ i 2

section MLIOPCS
-- Define the specific Stmt/Wit types Π' expects.
structure MLIOPCSStmt where
  point : Fin ℓ' → L
  evaluation : L

/-- Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation -/
def MLPEvalRelation (ιₛᵢ : Type) (OStmtIn : ιₛᵢ → Type)
    (input : ((MLPEvalStatement L ℓ') × (∀ j, OStmtIn j)) × (WitMLP L ℓ')) : Prop :=
  let ⟨⟨stmt, _⟩, wit⟩ := input
  stmt.original_claim = wit.t.val.eval stmt.t_eval_point

/-- The strict variant of an `AbstractOStmtIn`: same oracle data, with the strict
compatibility installed as the (single-track) compatibility. Instantiating the generic
ring-switching phase relations/bricks at `aOStmtIn.strictVariant` yields the strict-track
(completeness-side) relation chain for free; all data projections are definitionally those
of `aOStmtIn`. -/
@[reducible]
def AbstractOStmtIn.strictVariant (aOStmtIn : AbstractOStmtIn L ℓ') : AbstractOStmtIn L ℓ' :=
  aOStmtIn.strictView

omit [Fintype L] [DecidableEq L] [NeZero ℓ'] in
@[simp]
lemma AbstractOStmtIn.strictVariant_toRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
    aOStmtIn.strictVariant.toRelInput = aOStmtIn.toStrictRelInput := rfl

end MLIOPCS

section OStmt
variable (aOStmtIn : AbstractOStmtIn L ℓ')

end OStmt

end ProtocolTypes
end Preliminaries

/- This section defines the specific relations for the ring-switching protocol, whereas
the basis of L over K has rank `2^κ` instead of `κ` as in the Preliminaries section.
-/
section Relations
open Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

/-- Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier. -/
def RingSwitching_SumcheckMultParam :
    SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ P) :=
{ multpoly := fun ctx => -- This is supposed to be (r_κ, …, r_{ℓ-1})
    compute_A_MLE κ L K P ℓ' (original_r_eval_suffix :=
      getEvaluationPointSuffix κ L ℓ ℓ' h_l (r := ctx.t_eval_point))
      (r''_batching := ctx.r_batching)
  -- Ring-switching is the plain degree-2 case `H = P · t'`: combinator `Q := X`, degree 1.
  combinator := fun _ => Polynomial.X
  degCombinator := 1
  combinator_natDegree_le := by intro _; exact Polynomial.natDegree_X_le
}

/-- This condition ensures that the witness polynomial `H` has the
correct structure `A(...) * t'(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ' + 1)}
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  wit.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t') (m :=
    (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly stmt.ctx)
    (i := i) (challenges := stmt.challenges)

def masterKStateCore (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx) : Prop :=
  witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit
  ∧ sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def masterKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop) : Prop :=
  localChecks ∧ masterKStateCore κ L K P ℓ ℓ' h_l aOStmtIn stmtIdx stmt oStmt wit

def sumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterKStateCore κ L K P ℓ ℓ' h_l aOStmtIn i stmt oStmt wit

/-- Input relation for single round: proper sumcheck statement -/
def sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
    Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l
    aOStmtIn i stmt oStmt wit }

end Relations

open Module in
/-- The Binius (binary-tower) instantiation of `RingSwitchingProfile`, built from the tensor-algebra
definitions above: `A := L ⊗[K] L`, embeddings `φ₀ = · ⊗ 1` / `φ₁ = 1 ⊗ ·`, and the decompositions
are the `K`-basis coordinates via the left/right `L`-module structures.

Marked `@[reducible]` so that, once the protocol code is rewired through the profile, references to
`(binaryTowerProfile …).A` (etc.) unfold to `L ⊗[K] L` at reducible transparency — preserving the
existing `rfl`/instance-driven Binius proofs (and the byte-identical `#print axioms`). -/
@[reducible] def binaryTowerProfile (κ : ℕ) [NeZero κ] (K L : Type)
    [Field K] [Field L] [Algebra K L] (β : Module.Basis (Fin κ → Fin 2) K L) :
    RingSwitchingProfile K L κ :=
  tensorProductProfile κ K L β


/-! ## Generic row-extraction helpers over an abstract `RingSwitchingProfile`

These are profile-level consequences of the two extraction laws `decomposeRows_add` /
`decomposeRows_φ₀_mul_φ₁`, derived once for *every* `P : RingSwitchingProfile B L κ`:
* `decomposeRows_zero` : row coordinates of `0` vanish (from `decomposeRows_add` by cancellation);
* `decomposeRows_finsetSum` : row coordinates are additive over finite sums (induction from the
  binary additivity law and the zero law).
The DP24 capstone below is then stated and proved over an abstract `P`, with `binaryTowerProfile`
recovering the concrete Binius statements by reducibility. -/
section GenericRowExtraction
open Module

variable {B L : Type*} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
variable (P : RingSwitchingProfile B L κ)

/-- Row coordinates are additive over finite sums: induction from the binary additivity law
`decomposeRows_add` (with `decomposeRows_zero` as the base case). -/
lemma RingSwitchingProfile.decomposeRows_finsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → P.A) (u : Fin κ → Fin 2) :
    P.decomposeRows (∑ i ∈ s, f i) u = ∑ i ∈ s, P.decomposeRows (f i) u := by
  induction s using Finset.induction with
  | empty => simp [P.decomposeRows_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.decomposeRows_add]
    simpa only [Pi.add_apply] using congrArg (fun z => P.decomposeRows (f a) u + z) ih

/-- Column coordinates are additive over finite sums: the column dual of `decomposeRows_finsetSum`,
by induction from `decomposeColumns_add` (with `decomposeColumns_zero` as base case). -/
lemma RingSwitchingProfile.decomposeColumns_finsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → P.A) (v : Fin κ → Fin 2) :
    P.decomposeColumns (∑ i ∈ s, f i) v = ∑ i ∈ s, P.decomposeColumns (f i) v := by
  induction s using Finset.induction with
  | empty => simp [P.decomposeColumns_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.decomposeColumns_add]
    simpa only [Pi.add_apply] using congrArg (fun z => P.decomposeColumns (f a) v + z) ih

end GenericRowExtraction


/-! ## DP24 Ring-Switching Algebra Layer

This sub-section develops the algebraic identities underlying the Diamond–Posen 2024
ring-switching packing/decomposition, following the dual-view tensor-algebra theory.

The key facts are:
* `embedded_MLP_eval_eq_sum` : the prover's tensor `ŝ = φ₁(t')(φ₀(r_suffix))` expands as
  `ŝ = Σ_{w ∈ {0,1}^ℓ'} φ₀(eq̃(w, r_suffix)) · φ₁(t'(w))`, i.e. the documented
  `Σ_w eq̃(r_suffix, w) ⊗ t'(w)`. The `eq`-factor lands entirely in the column embedding
  `φ₀` because `φ₀` and `φ₁` agree on the Boolean literals `{0,1} ⊆ image(algebraMap K L)`.
* `decompose_rows_packMLE` : the *row* components of `ŝ` recover the suffix-`eq`-weighted
  evaluations of `t`: for each `u ∈ {0,1}^κ`,
  `(decompose_rows ŝ)_u = Σ_{w ∈ {0,1}^ℓ'} t(u, w) · eq̃(w, r_suffix)`.
  This is the load-bearing identity for reconstructing `t(r)`.

Coordinate convention: upstream's canonical columns recover the packed right factor;
canonical rows recover the left evaluation-point factor. The historical helper identifiers
below retain their names, while their types use these authoritative coordinate operations.
The verifier's canonical column check therefore agrees with polynomial evaluation.
-/
section RingSwitchingAlgebra
open Module

variable {κ₀ : ℕ} [NeZero κ₀]
variable {L₀ : Type} [CommRing L₀] [IsDomain L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]
variable {K₀ : Type} [CommRing K₀] [IsDomain K₀] [Fintype K₀] [DecidableEq K₀]
variable [Algebra K₀ L₀]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- A single `eqPolynomial` factor, evaluated through the mixed embedding
`eval₂ φ₁ (φ₀ ∘ g)` at a Boolean coefficient, collapses to the column embedding `φ₀`,
because `φ₀` and `φ₁` agree on the Boolean literals `{0, 1}`. -/
private lemma singleEq_collapse {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2)
    (i : Fin ℓ_suf) :
    MvPolynomial.eval₂ (φ₁ L₀ K₀) (fun j => φ₀ L₀ K₀ (g j))
      (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))
    = φ₀ L₀ K₀ (eval g (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))) := by
  unfold singleEqPolynomial
  rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;>
    simp only [Fin.isValue, beq_iff_eq, reduceIte, zero_ne_one,
      MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_one, MvPolynomial.eval₂_X,
      MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      map_add, map_mul, map_sub, map_one, map_zero, sub_zero, mul_zero, zero_mul, add_zero,
      one_mul, mul_one]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its
ordinary evaluation, by multiplying the `singleEq_collapse` factors. -/
private lemma eqPoly_collapse {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2) :
    MvPolynomial.eval₂ (φ₁ L₀ K₀) (fun j => φ₀ L₀ K₀ (g j))
      (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))
    = φ₀ L₀ K₀ (eval g (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))) := by
  unfold eqPolynomial
  rw [← MvPolynomial.coe_eval₂Hom, map_prod, MvPolynomial.eval_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.coe_eval₂Hom]
  exact singleEq_collapse g w i

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `decompose_tensor_algebra_columns` is additive over finite sums of tensors. -/
lemma decompose_rows_sum {ι : Type} [Fintype ι] (β : Basis (Fin κ₀ → Fin 2) K₀ L₀)
    (f : ι → TensorAlgebra K₀ L₀) (u : Fin κ₀ → Fin 2) :
    decompose_tensor_algebra_columns (L := L₀) (K := K₀) (β := β) (∑ i, f i) u
      = ∑ i, decompose_tensor_algebra_columns (L := L₀) (K := K₀) (β := β) (f i) u := by
  unfold decompose_tensor_algebra_columns
  rw [map_sum, Finset.sum_apply']

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`:
the `u`-th row component represents the *right* (`φ₁`) factor `b`, scaled by `a`. -/
lemma decompose_rows_φ₀φ₁ (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (a b : L₀) (u : Fin κ₀ → Fin 2) :
    decompose_tensor_algebra_columns (L := L₀) (K := K₀) (β := β) (φ₀ L₀ K₀ a * φ₁ L₀ K₀ b) u
      = (β.repr b) u • a := by
  have h : φ₀ L₀ K₀ a * φ₁ L₀ K₀ b = a ⊗ₜ[K₀] b := by
    simp only [φ₀, φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  unfold decompose_tensor_algebra_columns
  rw [Basis.baseChange_repr_tmul]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- The basis coordinate of a packed evaluation recovers the small-field coefficient:
`β.repr (t'(w)) u = t(u, w)`, where `t' = packMLE β t`. -/
lemma packMLE_repr_eval (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (t : MultilinearPoly K₀ ℓ) (w : Fin ℓ' → Fin 2)
    (u : Fin κ₀ → Fin 2) :
    (β.repr (eval (fun i => (if w i == 1 then (1 : L₀) else 0))
        (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t).val)) u
      = MvPolynomial.eval (fun i =>
          ((if h : i.val < κ₀ then u ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
          t.val := by
  unfold packMLE
  simp only []
  rw [show (fun i => (if w i == 1 then (1 : L₀) else 0)) = ((w : Fin ℓ' → Fin 2) : Fin ℓ' → L₀)
      from ?_]
  · rw [MvPolynomial.MLE_eval_zeroOne, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  · funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `eqTilde` written as a product over coordinates of the symmetric Boolean factor. -/
lemma eqTilde_prod {ℓ_ : ℕ} (r r' : Fin ℓ_ → L₀) :
    eqTilde r r' = ∏ i, ((1 - r i) * (1 - r' i) + r i * r' i) := by
  unfold eqTilde eqPolynomial singleEqPolynomial
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_add, map_mul, map_sub, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the
product of the κ-prefix and ℓ'-suffix products. -/
lemma prod_concat_split {M : Type*} [CommMonoid M] (ℓ' : ℕ)
    (Fp : Fin κ₀ → M) (Fs : Fin ℓ' → M) :
    (∏ i : Fin (ℓ' + κ₀), if h : i.val < κ₀ then Fp ⟨i.val, h⟩
        else Fs ⟨i.val - κ₀, by omega⟩)
      = (∏ i, Fp i) * ∏ j, Fs j := by
  -- the index equiv `Fin κ₀ ⊕ Fin ℓ' ≃ Fin (ℓ' + κ₀)`, κ-block first
  let e : Fin κ₀ ⊕ Fin ℓ' ≃ Fin (ℓ' + κ₀) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← Equiv.prod_comp e
    (fun i : Fin (ℓ' + κ₀) => if h : i.val < κ₀ then Fp ⟨i.val, h⟩ else Fs ⟨i.val - κ₀, by omega⟩),
    Fintype.prod_sum_type]
  have he_inl : ∀ i : Fin κ₀, (e (Sum.inl i)).val = i.val := by
    intro i
    simp only [e, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast,
      Fin.val_castAdd]
  have he_inr : ∀ j : Fin ℓ', (e (Sum.inr j)).val = κ₀ + j.val := by
    intro j
    simp only [e, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have hlt : (e (Sum.inl i)).val < κ₀ := by rw [he_inl]; exact i.is_lt
    simp only [dif_pos hlt]
    congr 1
  · apply Finset.prod_congr rfl
    intro j _
    have hge : ¬ (e (Sum.inr j)).val < κ₀ := by rw [he_inr]; omega
    simp only [dif_neg hge]
    congr 1
    apply Fin.ext
    show (e (Sum.inr j)).val - κ₀ = j.val
    rw [he_inr]; omega

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split:
`eqTilde (concat fp fs) (concat gp gs) = eqTilde fp gp * eqTilde fs gs`. -/
lemma eqTilde_concat_split (ℓ' : ℕ)
    (fp : Fin κ₀ → L₀) (fs : Fin ℓ' → L₀) (gp : Fin κ₀ → L₀) (gs : Fin ℓ' → L₀) :
    eqTilde (fun i : Fin (ℓ' + κ₀) => if h : i.val < κ₀ then fp ⟨i.val, h⟩
          else fs ⟨i.val - κ₀, by omega⟩)
        (fun i : Fin (ℓ' + κ₀) => if h : i.val < κ₀ then gp ⟨i.val, h⟩
          else gs ⟨i.val - κ₀, by omega⟩)
      = eqTilde fp gp * eqTilde fs gs := by
  rw [eqTilde_prod, eqTilde_prod, eqTilde_prod]
  rw [← prod_concat_split (κ₀ := κ₀) ℓ'
    (fun i => (1 - fp i) * (1 - gp i) + fp i * gp i)
    (fun j => (1 - fs j) * (1 - gs j) + fs j * gs j)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i.val < κ₀ <;> simp only [h, dif_pos, dif_neg, not_false_iff]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`. -/
lemma aeval_eqPolynomial_zeroOne {ℓ_ : ℕ} (x : Fin ℓ_ → Fin 2) (r : Fin ℓ_ → L₀) :
    (MvPolynomial.aeval r) (eqPolynomial (fun i => ((x i : Fin 2) : K₀)))
      = eqTilde (fun i => (if x i == 1 then (1 : L₀) else 0)) r := by
  rw [eqTilde_prod, eqPolynomial, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  unfold singleEqPolynomial
  rcases Fin.exists_fin_two.mp ⟨x i, rfl⟩ with h | h <;> rw [h] <;>
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
      beq_iff_eq, zero_ne_one, reduceIte, one_ne_zero, map_add, map_mul, map_sub, map_one,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_zero, sub_zero, mul_zero, zero_mul,
      add_zero, one_mul, mul_one]

omit [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`,
its `L₀`-evaluation at `r` equals the suffix-`eq`-weighted sum of its Boolean evaluations:
`aeval r t = ∑_{b ∈ {0,1}^ℓ} algebraMap(t(b)) · eq̃(b, r)`. -/
lemma aeval_eq_sum_eqTilde {ℓ_ : ℕ} (t : MultilinearPoly K₀ ℓ_) (r : Fin ℓ_ → L₀) :
    (MvPolynomial.aeval r) t.val
      = ∑ b : Fin ℓ_ → Fin 2,
          (algebraMap K₀ L₀) (MvPolynomial.eval (fun i => ((b i : Fin 2) : K₀)) t.val)
            * eqTilde (fun i => (if b i == 1 then (1 : L₀) else 0)) r := by
  conv_lhs => rw [← MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t.property]
  rw [MvPolynomial.MLE, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_mul, MvPolynomial.aeval_C, aeval_eqPolynomial_zeroOne]
  rw [mul_comm]
  congr 1

/-- The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)`
otherwise — matching `packMLE` / `decompose_rows_packMLE`. Packaged as an `Equiv`. -/
def hypercubeSplitEquiv (ℓ ℓ' : ℕ) (h_l : ℓ = ℓ' + κ₀) :
    (Fin κ₀ → Fin 2) × (Fin ℓ' → Fin 2) ≃ (Fin ℓ → Fin 2) where
  toFun := fun p => fun i => if h : i.val < κ₀ then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - κ₀, by omega⟩
  invFun := fun b => (fun i => b ⟨i.val, by omega⟩, fun j => b ⟨j.val + κ₀, by omega⟩)
  left_inv := fun ⟨v, w⟩ => by
    apply Prod.ext
    · funext i; simp only [Fin.is_lt, dif_pos]
    · funext j
      have : ¬ (j.val + κ₀ < κ₀) := by omega
      simp only [this, dif_neg, not_false_iff]
      congr 1
      apply Fin.ext; simp
  right_inv := fun b => by
    funext i
    by_cases h : i.val < κ₀
    · simp only [h, dif_pos]
    · simp only [h, dif_neg, not_false_iff]
      congr 1
      apply Fin.ext; simp only []; omega

/-! ### Generic DP24 capstone over an abstract `RingSwitchingProfile`

The lemmas above are stated for the concrete `binaryTowerProfile`; here we lift them to an abstract
`P : RingSwitchingProfile K₀ L₀ κ₀`, using only the structure's embeddings (`P.φ₀`, `P.φ₁`), basis
(`P.basis`), row decomposition (`P.decomposeColumns`), and its extraction laws (`decomposeRows_add` /
`decomposeRows_φ₀_mul_φ₁`, via the generic helper `decomposeRows_sum`). The Boolean-literal collapse
of the `eq`-factor (`singleEq_collapse'` / `eqPoly_collapse'`) holds for *any* pair of ring homs
because both agree on `{0, 1}`. These need only `CommRing + IsDomain` (not `Field`), so they apply
in the batching phase. Each reduces to its concrete counterpart at `P := binaryTowerProfile β`. -/

variable (P : RingSwitchingProfile K₀ L₀ κ₀)

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- Generic `singleEq_collapse`: a single `eqPolynomial` factor evaluated through the mixed
embedding `eval₂ P.φ₁ (P.φ₀ ∘ g)` at a Boolean coefficient collapses to `P.φ₀` of its ordinary
evaluation, since `P.φ₀` and `P.φ₁` agree on the Boolean literals `{0, 1}` (both are ring homs). -/
private lemma singleEq_collapse' {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2)
    (i : Fin ℓ_suf) :
    MvPolynomial.eval₂ P.φ₁ (fun j => P.φ₀ (g j))
      (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))
    = P.φ₀ (eval g (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))) := by
  unfold singleEqPolynomial
  rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;>
    simp only [Fin.isValue, beq_iff_eq, reduceIte, zero_ne_one,
      MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_one, MvPolynomial.eval₂_X,
      MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      map_add, map_mul, map_sub, map_one, map_zero, sub_zero, mul_zero, zero_mul, add_zero,
      one_mul, mul_one]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- Generic `eqPoly_collapse`: the full `eqPolynomial` collapses through the mixed embedding to
`P.φ₀` of its ordinary evaluation, by multiplying the `singleEq_collapse'` factors. -/
private lemma eqPoly_collapse' {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2) :
    MvPolynomial.eval₂ P.φ₁ (fun j => P.φ₀ (g j))
      (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))
    = P.φ₀ (eval g (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))) := by
  unfold eqPolynomial
  rw [← MvPolynomial.coe_eval₂Hom, map_prod, MvPolynomial.eval_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.coe_eval₂Hom]
  exact singleEq_collapse' P g w i

omit [CharP L₀ 2] in
/-- **Generic DP24 packing expansion** over an abstract `P`. The prover's tensor
`ŝ := P.φ₁(t')(P.φ₀(r_κ), …, P.φ₀(r_{ℓ-1}))` expands over the suffix hypercube as
`ŝ = Σ_{w ∈ {0,1}^ℓ'} P.φ₀(eq̃(w, r_suffix)) · P.φ₁(t'(w))`. -/
lemma embedded_MLP_eval_eq_sum' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t' : MultilinearPoly L₀ ℓ') (r : Fin ℓ → L₀) :
    embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        (P.φ₀ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
            (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)))
          * (P.φ₁ (eval (fun i => (if w i == 1 then (1 : L₀) else 0)) t'.val)) := by
  unfold embedded_MLP_eval componentWise_embed_MLE embedCoeffs getEvaluationPointSuffix
  simp only []
  rw [← MvPolynomial.eval₂_eq_eval_map]
  conv_lhs => rw [← MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t'.property]
  unfold MvPolynomial.MLE
  rw [← MvPolynomial.coe_eval₂Hom, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  congr 1
  · have hcoe : (fun i => ((w i : Fin 2) : L₀))
        = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
      funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp
    rw [hcoe]
    exact eqPoly_collapse' P (fun i => r ⟨i.val + κ₀, by rw [h_l]; omega⟩) w
  · unfold MvPolynomial.toEvalsZeroOne
    have hpt : (fun i => ((w i : Fin 2) : L₀)) = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
      funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp
    rw [show ((w : Fin ℓ' → L₀)) = (fun i => ((w i : Fin 2) : L₀)) from rfl, hpt]

omit [CharP L₀ 2] in
/-- **Generic row extraction for an embedded large-field multilinear polynomial.**

For arbitrary `t' : L⦃≤1⦄[X Fin ℓ']`, the row coordinates of
`embedded_MLP_eval t' r` extract the basis coordinates of the `t'` value at each Boolean suffix,
weighted by the suffix equality factor. This is the raw orientation lemma behind
`decompose_rows_packMLE'`; specializing to `t' = packMLE P.basis t` and using
`packMLE_repr_eval` recovers the small-field evaluation form. -/
lemma decomposeRows_embedded_MLP_eval' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (h_l : ℓ = ℓ' + κ₀) (t' : MultilinearPoly L₀ ℓ') (r : Fin ℓ → L₀)
    (u : Fin κ₀ → Fin 2) :
    P.decomposeColumns
        (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l t' r) u
      = ∑ w : Fin ℓ' → Fin 2,
          P.basis.repr
              (eval (fun i => (if w i == 1 then (1 : L₀) else 0)) t'.val) u •
            (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
              (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)) := by
  rw [embedded_MLP_eval_eq_sum', P.decomposeColumns_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  rw [P.decomposeColumns_φ₀_mul_φ₁]
  exact (Algebra.smul_def _ _).symm

omit [CharP L₀ 2] in
/-- **Generic column extraction for an embedded large-field multilinear polynomial** (the dual of
`decomposeRows_embedded_MLP_eval'`). For arbitrary `t' : L⦃≤1⦄[X Fin ℓ']`, the column coordinates
of `embedded_MLP_eval t' r` extract the basis coordinates of the *suffix equality factor*, scaled
into the `t'` value at each Boolean suffix:
`(columns ŝ)_u = Σ_w β.repr(eq̃(w, r_suffix))_u • t'(w)`.
This is the load-bearing orientation lemma behind the batched-sumcheck target `compute_s0`
(`compute_s0_eq_sum_A_func`): the column form puts `β.repr` on the verifier-known `eq`-factor, so
it matches the witness-independent batching multiplier `compute_A_func`. -/
lemma decomposeColumns_embedded_MLP_eval' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (h_l : ℓ = ℓ' + κ₀) (t' : MultilinearPoly L₀ ℓ') (r : Fin ℓ → L₀)
    (u : Fin κ₀ → Fin 2) :
    P.decomposeRows
        (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l t' r) u
      = ∑ w : Fin ℓ' → Fin 2,
          P.basis.repr
              (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
                (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)) u •
            (eval (fun i => (if w i == 1 then (1 : L₀) else 0)) t'.val) := by
  rw [embedded_MLP_eval_eq_sum', P.decomposeRows_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  rw [P.decomposeRows_φ₀_mul_φ₁]
  exact (Algebra.smul_def _ _).symm

omit [CharP L₀ 2] in
/-- **Generic row recovery of `t`-evaluations** over an abstract `P` whose basis is `P.basis`.
The row components of `ŝ = embedded_MLP_eval (packMLE P.basis t) r` carry the suffix-`eq`-weighted
evaluations of `t`. Routes through `embedded_MLP_eval_eq_sum'`, the generic row additivity
`P.decomposeColumns_sum`, the atomic extraction law `P.decomposeColumns_φ₀_mul_φ₁`, and the
profile-independent `packMLE_repr_eval`. -/
lemma decompose_rows_packMLE' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) (u : Fin κ₀ → Fin 2) :
    P.decomposeColumns
        (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l P.basis t) r) u
      = ∑ w : Fin ℓ' → Fin 2,
          (MvPolynomial.eval (fun i =>
              ((if h : i.val < κ₀ then u ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
              t.val)
            • (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
                (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)) := by
  rw [embedded_MLP_eval_eq_sum', P.decomposeColumns_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  rw [P.decomposeColumns_φ₀_mul_φ₁]
  dsimp only
  rw [packMLE_repr_eval]
  exact (Algebra.smul_def _ _).symm

omit [CharP L₀ 2] in
/-- **Generic DP24 ring-switching capstone (sum form)** over an abstract `P`. The verifier's
row-decomposition check sum, applied to the honest tensor `ŝ = embedded_MLP_eval (packMLE P.basis t)
r`, reconstructs exactly `t(r) = aeval r t`. -/
lemma check_rows_sum_eq_aeval' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    (∑ v : Fin κ₀ → Fin 2,
        eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
          * P.decomposeColumns
              (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l
                (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l P.basis t) r) v)
      = (MvPolynomial.aeval r) t.val := by
  subst h_l
  rw [aeval_eq_sum_eqTilde]
  rw [← Equiv.sum_comp (hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [decompose_rows_packMLE', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Algebra.smul_def]
  rw [show (fun i => ((hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i : Fin 2) : K₀))
      = (fun i => ((if h : i.val < κ₀ then v ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
      from by funext i; rfl]
  rw [show (getEvaluationPointSuffix κ₀ L₀ (ℓ' + κ₀) ℓ' rfl r)
      = (fun i => r ⟨i.val + κ₀, by omega⟩) from by funext i; rfl]
  have hfuse :
      eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
        * eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val + κ₀, by omega⟩)
      = eqTilde
          (fun i => (if hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i == 1 then
            (1 : L₀) else 0)) r := by
    rw [← eqTilde_concat_split (κ₀ := κ₀) ℓ'
        (fun i => (if v i == 1 then (1 : L₀) else 0))
        (fun i => (if w i == 1 then (1 : L₀) else 0))
        (fun i => r ⟨i.val, by omega⟩)
        (fun i => r ⟨i.val + κ₀, by omega⟩)]
    congr 1
    · funext i
      by_cases h : i.val < κ₀
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_pos]
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_neg, not_false_iff]
    · funext i
      by_cases h : i.val < κ₀
      · rw [dif_pos h]
      · rw [dif_neg h]
        congr 1
        apply Fin.ext
        simp only []
        omega
  rw [← hfuse]
  ring

omit [CharP L₀ 2] in
/-- **Generic DP24 ring-switching capstone (decision form)** over an abstract `P`. The verifier's
Step-2 check on the honest tensor `ŝ = embedded_MLP_eval (packMLE P.basis t) r` accepts exactly when
the original claim equals `t(r) = aeval r t`. This is the soundness/completeness pivot consumed by
the batching phase for an arbitrary profile. -/
lemma performCheckOriginalEvaluation_packMLE_iff (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (h_l : ℓ = ℓ' + κ₀) (s : L₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    performCheckOriginalEvaluation κ₀ L₀ K₀ P ℓ ℓ' h_l s r
        (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l P.basis t) r) = true
      ↔ s = (MvPolynomial.aeval r) t.val := by
  unfold performCheckOriginalEvaluation eqWeightedCoordSum
  simp only [decide_eq_true_eq]
  rw [check_rows_sum_eq_aeval']

/-! ### DP24 §2.5 `A_MLE` final-evaluation identity

The final sumcheck step's verifier check compares the carried sumcheck target against
`compute_final_eq_value · s'`, where `s' = t'(challenges)`. The sumcheck target, in turn, equals the
round polynomial `H = A_MLE · t'` evaluated at all `ℓ'` challenges, i.e. `A_MLE(challenges) ·
t'(challenges)`. Completeness therefore hinges on the algebraic identity
`A_MLE(challenges) = compute_final_eq_value`, i.e. the multilinear extension `A_MLE` of
`compute_A_func` evaluated at the (arbitrary, non-Boolean) challenge point equals the
row-decomposition value of the final eq-tensor `e := eq̃(φ₀(r_suffix), φ₁(challenges))`.

The two helper lemmas below (MLE evaluation as an `eq̃`-weighted sum over the Boolean hypercube, and
the `φ₀/φ₁`-tensor expansion of `e`) reduce the identity to the row-extraction laws
`P.decomposeColumns_φ₀_mul_φ₁` / `P.decomposeColumns_sum`, exactly as in
`decompose_rows_packMLE'`. -/

omit [IsDomain L₀] [CharP L₀ 2] [IsDomain K₀] [Fintype K₀] [DecidableEq K₀] in
/-- **MLE evaluation as an `eq̃`-weighted hypercube sum.** Evaluating the multilinear extension
`MLE f` at an arbitrary (not necessarily Boolean) point `r` equals the `eq̃`-weighted sum of the
hypercube values `f x`, with weight `eq̃(x, r)`. This is the standard multilinear-extension
evaluation formula, here phrased with the Boolean-literal embedding `x ↦ (if x = 1 then 1 else 0)`
used throughout the ring-switching algebra layer. -/
lemma MLE_eval_eq_sum_eqTilde {ℓ_ : ℕ} (f : (Fin ℓ_ → Fin 2) → L₀) (r : Fin ℓ_ → L₀) :
    MvPolynomial.eval r (MvPolynomial.MLE f)
      = ∑ x : Fin ℓ_ → Fin 2,
          eqTilde (fun i => (if x i == 1 then (1 : L₀) else 0)) r * f x := by
  rw [MvPolynomial.MLE, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul, MvPolynomial.eval_C]
  congr 1
  -- `eval r (eqPolynomial (x : Fin ℓ_ → L₀)) = eqTilde (boolEmbed x) r`
  rw [show ((x : Fin ℓ_ → L₀)) = (fun i => ((x i : Fin 2) : L₀)) from rfl]
  rw [show (fun i => ((x i : Fin 2) : L₀)) = (fun i => (if x i == 1 then (1 : L₀) else 0))
      from by funext i; rcases Fin.exists_fin_two.mp ⟨x i, rfl⟩ with h | h <;> rw [h] <;> simp]
  rw [eqTilde]

omit [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- **`φ₀/φ₁`-tensor expansion of an eq-tensor.** The mixed eq-tensor
`eq̃(φ₀ ∘ g, φ₁ ∘ h) ∈ P.A` expands over the Boolean hypercube as
`∑_w φ₀(eq̃(w, g)) · φ₁(eq̃(w, h))`. Proven by collapsing each `eqPolynomial` factor through the
`eval₂ φ₁ (φ₀ ∘ ·)` mixed embedding (the same Boolean-literal-agreement argument as
`embedded_MLP_eval_eq_sum'`, instantiated with the multilinear `eqPolynomial h`). -/
lemma eqTilde_tensor_expand {ℓ_ : ℕ} (g h : Fin ℓ_ → L₀) :
    eqTilde (fun i => P.φ₀ (g i)) (fun i => P.φ₁ (h i))
      = ∑ w : Fin ℓ_ → Fin 2,
          P.φ₀ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) g)
            * P.φ₁ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) h) := by
  -- LHS: `eval (φ₁ ∘ h) (eqPolynomial (φ₀ ∘ g))`. Rewrite `eqPolynomial (φ₀ ∘ g)` as the
  -- `φ₀`-image of `eqPolynomial g`, then as the multilinear MLE of its Boolean evaluations, and
  -- push through `eval₂`.
  rw [eqTilde, eqPolynomial_symm]
  -- now LHS = eval (φ₀ ∘ g) (eqPolynomial (φ₁ ∘ h))
  -- View eqPolynomial (φ₁ ∘ h) as map φ₁ of the multilinear eqPolynomial h, evaluated at φ₀ ∘ g.
  have hmap : (eqPolynomial (fun i => P.φ₁ (h i)) : MvPolynomial (Fin ℓ_) P.A)
      = MvPolynomial.map (P.φ₁) (eqPolynomial h) := by
    unfold eqPolynomial singleEqPolynomial
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_add, map_mul, map_sub, map_one, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [hmap, ← MvPolynomial.eval₂_eq_eval_map]
  -- Expand the multilinear `eqPolynomial h` as `MLE` of its Boolean evaluations.
  conv_lhs => rw [show (eqPolynomial h : MvPolynomial (Fin ℓ_) L₀)
      = MvPolynomial.MLE (eqPolynomial h).toEvalsZeroOne from
        (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp
          (eqPolynomial_mem_restrictDegree h)).symm]
  unfold MvPolynomial.MLE
  rw [← MvPolynomial.coe_eval₂Hom, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  have hcoe : (fun i => (((w i : Fin 2) : L₀))) = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
    funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with hh | hh <;> rw [hh] <;> simp
  congr 1
  · -- φ₀ factor: collapse eqPolynomial through the mixed embedding eval₂ φ₁ (φ₀ ∘ g)
    rw [show (fun i => ((w i : Fin 2) : L₀)) = (fun i => (if w i == 1 then (1 : L₀) else 0))
        from hcoe]
    rw [eqPoly_collapse' P g w]
    rfl
  · -- φ₁ factor: the Boolean evaluation of eqPolynomial h is eqTilde (boolEmbed w) h
    congr 1
    unfold MvPolynomial.toEvalsZeroOne
    rw [hcoe, eqTilde, eqPolynomial_symm]

omit [IsDomain L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]
  [IsDomain K₀] [Fintype K₀] [DecidableEq K₀] in
/-- **`eqTilde` symmetry.** `eq̃(r, r') = eq̃(r', r)`: a direct corollary of `eqPolynomial_symm`
(`eval r' (eqPolynomial r) = eval r (eqPolynomial r')`). -/
lemma eqTilde_comm {ℓ_ : ℕ} (r r' : Fin ℓ_ → L₀) : eqTilde r r' = eqTilde r' r := by
  unfold eqTilde
  exact eqPolynomial_symm r r'

omit [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- **DP24 §2.5 `A_MLE` final-evaluation identity (defect #10, column form).** The multilinear
extension `A_MLE` of `compute_A_func` — the sumcheck multiplier `(RingSwitching_SumcheckMultParam
…).multpoly` — evaluated at the (arbitrary, non-Boolean) sumcheck challenges equals the verifier's
`compute_final_eq_value`, which reads the **column** components of the final eq-tensor
`e := eq̃(φ₀ ∘ r_suffix, φ₁ ∘ challenges)`.

Term-by-term derivation: the LHS expands by `MLE_eval_eq_sum_eqTilde` into a sum over the Boolean
hypercube of `eq̃(x, challenges) · A_func(x)`, with `A_func(x) = ∑_u β.repr(eq̃(suffix, x))_u •
eq̃(u, r'')`. The RHS expands by `eqTilde_tensor_expand` (e = ∑_w φ₀(eq̃(w, suffix))·φ₁(eq̃(w,
challenges))) followed by column additivity (`decomposeColumns_sum`) and the column atomic
extraction law (`decomposeColumns_φ₀_mul_φ₁`: columns of `φ₀ a · φ₁ b` are `β.repr a • b`), giving
`∑_u eq̃(u, r'') · ∑_w β.repr(eq̃(w, suffix))_u • eq̃(w, challenges)`. After `eqTilde` symmetry
(`eq̃(suffix, x) = eq̃(x, suffix)`) the two double sums agree summand-wise (`Finset.sum_comm` +
`smul`/`mul` commutation), so the column orientation is the one that makes the identity TRUE — the
row orientation yields the transposed pairing and is false. -/
lemma A_MLE_eval_eq_compute_final_eq_value (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (h_l : ℓ = ℓ' + κ₀) (r_eval : Fin ℓ → L₀) (challenges : Fin ℓ' → L₀)
    (r''_batching : Fin κ₀ → L₀) :
    (compute_A_MLE κ₀ L₀ K₀ P ℓ'
        (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r_eval) r''_batching).val.eval challenges
      = compute_final_eq_value κ₀ L₀ K₀ P ℓ ℓ' h_l r_eval challenges r''_batching := by
  -- LHS: unfold to `eval challenges (MLE (compute_A_func suffix r''))` and expand by MLE formula.
  unfold compute_A_MLE compute_final_eq_value compute_final_eq_tensor compute_A_func
    getEvaluationPointSuffix eqWeightedCoordSum
  simp only []
  rw [MLE_eval_eq_sum_eqTilde]
  -- RHS: expand the eq-tensor and push `decomposeColumns` through the sum + atomic extraction.
  rw [eqTilde_tensor_expand P (fun j => r_eval ⟨j.val + κ₀, by rw [h_l]; omega⟩) challenges]
  -- Push `decomposeColumns` through the hypercube sum + atomic extraction (under the ∑_u binder).
  simp only [P.decomposeRows_sum, P.decomposeRows_φ₀_mul_φ₁, Finset.sum_apply]
  -- Distribute the scalar prefix into the inner hypercube sum on both sides:
  -- `∑ x, c_x * ∑ y, d_{x,y} = ∑ x, ∑ y, c_x * d_{x,y}`.
  simp only [Finset.sum_apply, Finset.mul_sum]
  -- Both sides are now double sums over the Boolean hypercube. Reindex the RHS (swap the two
  -- sum binders) so its outer index pairs with the LHS inner index, then match summand-wise.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  -- After `sum_comm` the summand is, with `c := β.repr(eq̃(u,suffix)) x`,
  --   `eq̃(u,ch) * (c • eq̃(x,r''))  =  eq̃(x,r'') * (c • eq̃(u,ch))`.
  -- Align the `repr` arguments by `eqTilde` symmetry, then commute `•` past `*`.
  rw [eqTilde_comm (fun j => r_eval ⟨j.val + κ₀, by rw [h_l]; omega⟩)
      (fun i => (if u i == 1 then (1 : L₀) else 0))]
  simp only [Algebra.smul_def]
  ring

end RingSwitchingAlgebra

section RingSwitchingAlgebraBinius
-- Concrete Binius (`binaryTowerProfile`) specializations of the DP24 capstone chain. These need
-- `Field K₀`/`Field L₀` to *build* the profile (its `decompose*`/`φ` fields and `rfl`/instance
-- proofs), so they live in this `Field` section, separate from the `CommRing + IsDomain` generic
-- chain above (which is what the batching phase consumes). Each reuses the profile-independent
-- helpers above; the abstract-`P` chain specializes to these at `P := binaryTowerProfile β`.
open Module

variable {κ₀ : ℕ} [NeZero κ₀]
variable {L₀ : Type} [Field L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]
variable {K₀ : Type} [Field K₀] [Fintype K₀] [DecidableEq K₀]
variable [Algebra K₀ L₀]

omit [Fintype K₀] [DecidableEq K₀] in
/-- **DP24 packing expansion.** The prover's tensor
`ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over the suffix hypercube as
`ŝ = Σ_{w ∈ {0,1}^ℓ'} φ₀(eq̃(w, r_suffix)) · φ₁(t'(w))`, i.e. `Σ_w eq̃(r_suffix, w) ⊗ t'(w)`. -/
lemma embedded_MLP_eval_eq_sum (β : Module.Basis (Fin κ₀ → Fin 2) K₀ L₀)
    (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t' : MultilinearPoly L₀ ℓ') (r : Fin ℓ → L₀) :
    embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        (φ₀ L₀ K₀ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
            (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)))
          * (φ₁ L₀ K₀ (eval (fun i => (if w i == 1 then (1 : L₀) else 0)) t'.val)) := by
  unfold embedded_MLP_eval componentWise_embed_MLE embedCoeffs getEvaluationPointSuffix
  simp only []
  rw [← MvPolynomial.eval₂_eq_eval_map]
  conv_lhs => rw [← MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t'.property]
  unfold MvPolynomial.MLE
  rw [← MvPolynomial.coe_eval₂Hom, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  congr 1
  · have hcoe : (fun i => ((w i : Fin 2) : L₀))
        = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
      funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp
    rw [hcoe]
    exact eqPoly_collapse (fun i => r ⟨i.val + κ₀, by rw [h_l]; omega⟩) w
  · unfold MvPolynomial.toEvalsZeroOne
    have hpt : (fun i => ((w i : Fin 2) : L₀)) = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
      funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp
    rw [show ((w : Fin ℓ' → L₀)) = (fun i => ((w i : Fin 2) : L₀)) from rfl, hpt]

/-- **Row recovery of `t`-evaluations.** The row components of the prover's tensor
`ŝ = embedded_MLP_eval (packMLE β t) r` carry the suffix-`eq`-weighted evaluations of `t`:
`(decompose_rows ŝ)_u = Σ_{w ∈ {0,1}^ℓ'} t(u, w) · eq̃(w, r_suffix)`.

This is the load-bearing identity for reconstructing `t(r)` from `ŝ`. It uses the *row*
decomposition (which represents the `t'`/`φ₁` factor); the verifier's
`performCheckOriginalEvaluation` instead uses the *column* decomposition — see the module
note above. -/
lemma decompose_rows_packMLE (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀)
    (u : Fin κ₀ → Fin 2) :
    decompose_tensor_algebra_columns (L := L₀) (K := K₀) (β := β)
        (embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t) r) u
      = ∑ w : Fin ℓ' → Fin 2,
          (MvPolynomial.eval (fun i =>
              ((if h : i.val < κ₀ then u ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
              t.val)
            • (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
                (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)) := by
  rw [embedded_MLP_eval_eq_sum, decompose_rows_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [decompose_rows_φ₀φ₁, packMLE_repr_eval]

/-- **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum,
applied to the prover's honest tensor `ŝ = embedded_MLP_eval (packMLE β t) r`, reconstructs
exactly `t(r) = aeval r t`:
`∑_v eq̃(v, r_prefix) · (rows ŝ)_v = aeval r t`. -/
lemma check_rows_sum_eq_aeval (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    (∑ v : Fin κ₀ → Fin 2,
        eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
          * decompose_tensor_algebra_columns (L := L₀) (K := K₀) (β := β)
              (embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l
                (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t) r) v)
      = (MvPolynomial.aeval r) t.val := by
  subst h_l
  rw [aeval_eq_sum_eqTilde]
  -- reindex `∑_b` over `Fin (ℓ'+κ₀)` to `∑_{(v,w)}`, then `Fintype.sum_prod_type`
  rw [← Equiv.sum_comp (hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  -- expand the row component and distribute the prefix `eq̃`
  rw [decompose_rows_packMLE, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  -- `•` → `algebraMap * `
  rw [Algebra.smul_def]
  -- the `t`-evaluation point on both sides is `split (v, w)` (definitional)
  rw [show (fun i => ((hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i : Fin 2) : K₀))
      = (fun i => ((if h : i.val < κ₀ then v ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
      from by funext i; rfl]
  rw [show (getEvaluationPointSuffix κ₀ L₀ (ℓ' + κ₀) ℓ' rfl r)
      = (fun i => r ⟨i.val + κ₀, by omega⟩) from by funext i; rfl]
  -- the two `eq̃` factors fuse along the κ/ℓ' split into `eq̃(split(v,w)_as_L, r)`
  have hfuse :
      eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
        * eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val + κ₀, by omega⟩)
      = eqTilde
          (fun i => (if hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i == 1 then
            (1 : L₀) else 0)) r := by
    rw [← eqTilde_concat_split (κ₀ := κ₀) ℓ'
        (fun i => (if v i == 1 then (1 : L₀) else 0))
        (fun i => (if w i == 1 then (1 : L₀) else 0))
        (fun i => r ⟨i.val, by omega⟩)
        (fun i => r ⟨i.val + κ₀, by omega⟩)]
    congr 1
    · funext i
      by_cases h : i.val < κ₀
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_pos]
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_neg, not_false_iff]
    · funext i
      by_cases h : i.val < κ₀
      · rw [dif_pos h]
      · rw [dif_neg h]
        congr 1
        apply Fin.ext
        simp only []
        omega
  rw [← hfuse]
  ring

/-- **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's
honest tensor `ŝ = embedded_MLP_eval (packMLE β t) r` accepts exactly when the original claim
equals `t(r) = aeval r t`. This is the soundness/completeness pivot for the batching phase. -/
lemma performCheckOriginalEvaluation_packMLE_iff_binaryTower (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (h_l : ℓ = ℓ' + κ₀) (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (s : L₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    performCheckOriginalEvaluation κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l s r
        (embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t) r) = true
      ↔ s = (MvPolynomial.aeval r) t.val := by
  unfold performCheckOriginalEvaluation eqWeightedCoordSum
  simp only [decide_eq_true_eq]
  rw [check_rows_sum_eq_aeval]

end RingSwitchingAlgebraBinius


/-! ## DP24 Batching-Phase Sumcheck Orientation (gap analysis)

The batching phase's round-2 knowledge-state and its completeness require the **sumcheck
consistency** identity (`sumcheckConsistencyProp`)

  `compute_s0 κ L K β ŝ r'' = ∑ x ∈ (univ.map 𝓑) ^ᶠ ℓ', H.eval x`,

with `H = projectToMidSumcheckPoly t' (A_MLE …) 0 Fin.elim0` (so `H = A_MLE · t'` at round 0).

The left-hand side `compute_s0` is a sum over `{0,1}^κ` of `eqTilde`-weighted **row components**
and is **independent of the evaluation domain `𝓑 : Fin 2 ↪ L`**. The right-hand side is the
sumcheck sum over the 2-element domain `{𝓑 0, 𝓑 1}^{ℓ'}` and is genuinely **`𝓑`-dependent**
(the variable `𝓑` is declared free in `BatchingPhase`/`SumcheckPhase`, with no constraint pinning
it to the Boolean embedding `𝓑 0 = 0, 𝓑 1 = 1`).

The two lemmas below make this concrete: the consistency sum of the linear polynomial `X 0`
equals `𝓑 0 + 𝓑 1`, so no single `𝓑`-free target can satisfy consistency simultaneously for two
domains with different element sums. Consequently the round-2
`batchingKStateProp`/`batchingReduction_perfectCompleteness` sumcheck-consistency obligation is
**not satisfiable for a free `𝓑`**; honestly closing it requires either pinning `𝓑` to the
Boolean embedding or reorienting `compute_s0`/`sumcheckConsistencyProp` — both of which would
alter the existing free declarations. See the module report. -/
section SumcheckOrientation
open Module Finset

variable {L₀ : Type} [Field L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.**
The single-variable sumcheck consistency sum of the linear polynomial `X 0` over the
2-element domain `{𝓑 0, 𝓑 1}` equals `𝓑 0 + 𝓑 1`. -/
lemma sumcheckSum_X0_eq (𝓑 : Fin 2 ↪ L₀) :
    (∑ x ∈ (univ.map 𝓑) ^ᶠ (1),
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) L₀).eval x) = 𝓑 0 + 𝓑 1 := by
  rw [Finset.sum_bij' (t := univ.map 𝓑) (g := fun a => a)
    (fun x _ => x 0) (fun a _ => (fun _ => a))
    (fun a ha => by simp only [Fintype.mem_piFinset] at ha; exact ha 0)
    (fun a ha => by simp only [Fintype.mem_piFinset]; exact fun i => ha)
    (fun a ha => by funext i; rw [Fin.fin_one_eq_zero i])
    (fun a ha => rfl)
    (fun a ha => by simp only [MvPolynomial.eval_X])]
  rw [Finset.sum_map]; simp [Fin.sum_univ_two]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.**
If a single value `c` (independent of `𝓑`) equals the sumcheck consistency sum of `X 0`
for two embeddings `𝓑₁`, `𝓑₂`, then `𝓑₁ 0 + 𝓑₁ 1 = 𝓑₂ 0 + 𝓑₂ 1`. Contrapositive: whenever two
domains have different element sums (e.g. `{0,1}` vs `{0,ω}` in `GF(4)`, where `1 ≠ ω`), no
`𝓑`-free target can be consistent with both. Since `compute_s0` does not depend on `𝓑`, this
obstructs `sumcheckConsistencyProp (compute_s0 …) H` for a free `𝓑`. -/
lemma sumcheckTarget_domain_indep (c : L₀) (𝓑₁ 𝓑₂ : Fin 2 ↪ L₀)
    (h₁ : c = ∑ x ∈ (univ.map 𝓑₁) ^ᶠ (1),
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) L₀).eval x)
    (h₂ : c = ∑ x ∈ (univ.map 𝓑₂) ^ᶠ (1),
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) L₀).eval x) :
    𝓑₁ 0 + 𝓑₁ 1 = 𝓑₂ 0 + 𝓑₂ 1 := by
  rw [sumcheckSum_X0_eq] at h₁ h₂
  rw [← h₁, ← h₂]

/-! ### Boolean-domain (pinned-`𝓑`) regime of DP24

The two lemmas above show the sumcheck consistency identity is `𝓑`-dependent and hence
unsatisfiable for a *free* `𝓑`. The lemmas below pin `𝓑` to the Boolean embedding
`{𝓑 0 = 0, 𝓑 1 = 1}` (the regime DP24 actually instantiates) and re-express the `𝓑`-domain
hypercube sum `∑ x ∈ (univ.map 𝓑) ^ᶠ k, f x` as the canonical Boolean hypercube sum over
`Fin k → Fin 2`. This is the bridge that turns the `𝓑`-dependent right-hand side of
`sumcheckConsistencyProp` into a `𝓑`-free form matching `compute_s0`, and is the load-bearing
reindexing step for closing `batchingReduction_perfectCompleteness` once `𝓑` is pinned. -/

/-- The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element
domain embedding `𝓑`, sending `b ↦ (j ↦ 𝓑 (b j))`. -/
def boolHypercubeEmb (𝓑 : Fin 2 ↪ L₀) (k : ℕ) : (Fin k → Fin 2) ↪ (Fin k → L₀) where
  toFun b := fun j => 𝓑 (b j)
  inj' := by intro a b hab; funext j; exact 𝓑.injective (congrFun hab j)

omit [Field L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`,
summing `f` over the `k`-fold product domain `{𝓑 0, 𝓑 1}^k` equals summing `f ∘ (𝓑 ∘ ·)` over
the Boolean hypercube `Fin k → Fin 2`. (No pinning required — `𝓑` only needs to be an embedding.) -/
lemma boolHypercube_sum_eq (𝓑 : Fin 2 ↪ L₀) {k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin k → L₀) → M) :
    (∑ x ∈ (univ.map 𝓑) ^ᶠ k, f x) = ∑ b : Fin k → Fin 2, f (fun j => 𝓑 (b j)) := by
  have hset : (univ.map 𝓑) ^ᶠ k
      = (univ : Finset (Fin k → Fin 2)).map (boolHypercubeEmb 𝓑 k) := by
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_map, Finset.mem_univ, true_and, boolHypercubeEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hx; choose c hc using hx; exact ⟨c, funext hc⟩
    · rintro ⟨b, rfl⟩ j; exact ⟨b j, rfl⟩
  rw [hset, Finset.sum_map]
  rfl

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding
(`𝓑 c = if c = 1 then 1 else 0`, i.e. `𝓑 0 = 0`, `𝓑 1 = 1`), the `𝓑`-domain hypercube sum equals
the canonical sum over `Fin k → Fin 2` with the Boolean-literal evaluation point
`j ↦ (if b j = 1 then 1 else 0)`. This is the `𝓑`-free right-hand side of `sumcheckConsistencyProp`
in the regime DP24 instantiates. -/
lemma boolHypercube_sum_pinned (𝓑 : Fin 2 ↪ L₀)
    (h𝓑 : ∀ c, (𝓑 c : L₀) = if c = 1 then 1 else 0)
    {k : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin k → L₀) → M) :
    (∑ x ∈ (univ.map 𝓑) ^ᶠ k, f x)
      = ∑ b : Fin k → Fin 2, f (fun j => (if b j == 1 then (1 : L₀) else 0)) := by
  rw [boolHypercube_sum_eq]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext j
  rw [h𝓑 (b j)]
  rcases Fin.exists_fin_two.mp ⟨b j, rfl⟩ with h | h <;> rw [h] <;> simp

end SumcheckOrientation


/-! ## `simOracle2` message-query support

These lemmas reduce `simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (…)` applied to a single
query to the *right* (message) oracle family `[T₂]ₒ` of the combined spec
`oSpec + ([T₁]ₒ + [T₂]ₒ)`. They are the load-bearing infrastructure for verifier-side
`toFun_full` proofs whose `OracleVerifier.verify` body *queries a prover message*: under
`simulateQ (simOracle2 …)` the message query (read via the per-message `OracleInterface`) routes,
through `QueryImpl.addLift`/`QueryImpl.add`, to `OracleInterface.answer` of the message value.

These are stated over fully general spec/oracle parameters and are candidates for upstreaming to
`OracleReduction/OracleInterface.lean` (which owns `simOracle2`); they live here for now so that
the analogous message-querying `toFun_full`s in `SumcheckPhase` and `BinaryBasefold/Steps` can
import them. -/
section SimOracle2MessageQuery

open OracleInterface

/-- **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via
`simOracle2 oSpec t₁ t₂`, the lift into the combined spec `oSpec + ([T₁]ₒ + [T₂]ₒ)` of a single
query `qm` to the *right* (message) oracle family `[T₂]ₒ` collapses to `pure` of that oracle's
`answer`, with all queries routed to `t₂`. -/
lemma simulateQ_simOracle2_messageQuery {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) := by
  -- `liftM` of the message query into the combined spec is `liftM ((…).query (inr (inr qm)))`.
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inr qm)))) = _
  rw [simulateQ_spec_query]
  -- `simOracle2` routes `inr (inr …)` to `(simOracle0 T₂ t₂).liftTarget`, i.e. `answer (t₂ …)`.
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₂ t₂ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as
`simulateQ_simOracle2_messageQuery`, phrased for the `query`/`monadLift` form that appears verbatim
in an `OracleVerifier.verify` body (a query in `OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)))`).
This is the form consumed by the verifier-run collapse in message-querying `toFun_full` proofs. -/
lemma simulateQ_simOracle2_query {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
      = (OptionT.lift (pure (OracleInterface.answer (t₂ qm.1) qm.2))
          : OptionT (OracleComp oSpec) _) := by
  -- The OptionT query is `OptionT.lift (liftM (message query))`; `simulateQ` commutes with `lift`.
  rw [show (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
        = OptionT.lift (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_simOracle2_messageQuery]
  rfl

end SimOracle2MessageQuery

/-! ## `fixFirstVariablesOfMQP` evaluation bridge

The final sumcheck step's completeness needs to evaluate the round polynomial
`H = projectToMidSumcheckPoly t' m (Fin.last ℓ') challenges` (= `fixFirstVariablesOfMQP` of
`m · t'` at *all* `ℓ'` variables) at the 0-variate point and recognise it as `(m · t')(challenges)`.
The two lemmas below provide that bridge generically. -/
section FixVarsEval
open MvPolynomial

/-- **`sumAlgEquiv` evaluation.** Evaluating the curried polynomial `sumAlgEquiv p` by `eval x` on
the outer (`S₁`) variables and `eval challenges` on the inner (`S₂`) coefficient ring equals
evaluating `p` directly at the combined point `Sum.elim x challenges`. Proven by `induction_on`,
using the canonical `sumAlgEquiv` equations on the generators. -/
theorem sumAlgEquiv_eval₂ {L : Type} [CommRing L] {S₁ S₂ : Type} [Fintype S₁]
    (x : S₁ → L) (challenges : S₂ → L) (p : MvPolynomial (S₁ ⊕ S₂) L) :
    eval₂ (eval challenges) x ((sumAlgEquiv L S₁ S₂) p) = eval (Sum.elim x challenges) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval₂_mul, hp]
    congr 1
    cases i <;> simp

/-- Evaluation after fixing the canonical prefix of variables. -/
theorem fixFirstVariablesOfMQP_eval {L : Type} [CommRing L] (ℓ : ℕ) (v : Fin (ℓ + 1))
    (poly : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) (x : Fin (ℓ - v) → L) :
    eval x (fixFirstVariablesOfMQP ℓ v poly challenges) =
      eval (fun j => if hj : j.val < v.val then challenges ⟨j.val, hj⟩
        else x ⟨j.val - v, by omega⟩) poly :=
  MvPolynomial.eval_fixFirstVariablesOfMQP v poly challenges x

end FixVarsEval

/-! ## Round-transition algebra for the iterated sumcheck

The authoritative `fixFirstVariablesOfMQP` fixes the first `i` variables. Extending a fixed
prefix by the next challenge therefore uses `Fin.snoc challenges r'`. The following wrappers
reuse the canonical substitution, evaluation and successor theorems. Historical suffix-fixing
formulations and their original proof sources are recorded in the integration migration audit.
-/
section RoundTransition
open MvPolynomial Finset Sumcheck.Structured

variable {L : Type} [CommRing L]

/-- Value-form of `finSumFinEquiv.symm`: classify the index by whether its value is `< m`. -/
theorem finSumFinEquiv_symm_dite {m n : ℕ} (x : Fin (m + n)) :
    finSumFinEquiv.symm x
      = if h : (x : ℕ) < m then Sum.inl ⟨x, h⟩
        else Sum.inr ⟨(x : ℕ) - m, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  by_cases h : (x : ℕ) < m
  · rw [dif_pos h, finSumFinEquiv_apply_left]
    apply Fin.ext; simp
  · rw [dif_neg h, finSumFinEquiv_apply_right]
    apply Fin.ext; simp; omega

/-- The canonical prefix-fixing operation is its explicit partial substitution. -/
theorem fixVars_eq_bind₁ (ℓ : ℕ) (v : Fin (ℓ + 1)) (poly : MvPolynomial (Fin ℓ) L)
    (challenges : Fin v → L) :
    fixFirstVariablesOfMQP ℓ v poly challenges =
      bind₁ (MvPolynomial.fixFirstVariablesSubst v challenges) poly :=
  MvPolynomial.fixFirstVariablesOfMQP_eq_bind₁ v poly challenges

/-- The next prefix value appends to the previous challenges with `Fin.snoc`. -/
theorem fixVars_step (ℓ : ℕ) (poly : MvPolynomial (Fin ℓ) L) (v : Fin (ℓ + 1))
    (hv : (v : ℕ) < ℓ) (challenges : Fin v → L) (r' : L) :
    fixFirstVariablesOfMQP (ℓ - v) ⟨1, by omega⟩
        (fixFirstVariablesOfMQP ℓ v poly challenges) (fun _ => r') =
      rename (finCongr (show ℓ - ((v : ℕ) + 1) = ℓ - v - 1 by omega))
        (fixFirstVariablesOfMQP ℓ ⟨(v : ℕ) + 1, by omega⟩ poly (Fin.snoc challenges r')) := by
  have h := MvPolynomial.fixFirstVariablesOfMQP_succ (⟨v.val, hv⟩ : Fin ℓ)
    poly challenges r' (show ℓ - v - 1 = ℓ - (v + 1) by omega)
  have hh := congrArg (MvPolynomial.rename
    (finCongr (show ℓ - (v + 1) = ℓ - v - 1 by omega))) h
  have hid : ((finCongr (show ℓ - (v + 1) = ℓ - v - 1 by omega)) ∘
      (Fin.cast (show ℓ - v - 1 = ℓ - (v + 1) by omega)) :
      Fin (ℓ - v - 1) → Fin (ℓ - v - 1)) = id := by
    funext j
    apply Fin.ext
    rfl
  rw [MvPolynomial.rename_rename, hid, MvPolynomial.rename_id_apply] at hh
  exact hh



/-- `projectToMidSumcheckPoly` is `fixFirstVariablesOfMQP` applied to the initial round polynomial
`m · t`, at the same number of fixed variables `i`. -/
theorem projectToMidSumcheckPoly_eq_fixVars (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin (ℓ + 1)) (challenges : Fin i → L) :
    (projectToMidSumcheckPoly ℓ t m i challenges).val
      = fixFirstVariablesOfMQP ℓ ⟨i, by omega⟩ (m.val * t.val) challenges := by
  unfold projectToMidSumcheckPoly
  exact congrArg (fun q : MvPolynomial (Fin ℓ) L =>
    fixFirstVariablesOfMQP ℓ ⟨i, by omega⟩ q challenges)
    (coe_computeInitialSumcheckPoly ℓ t m)

/-- Fixing the next surviving prefix variable advances the projected round polynomial.
The challenge vector appends the new value with `Fin.snoc`; the remaining dimensions are
identified by the canonical `finCongr`. -/
theorem fixFirstVariablesOfMQP_projectToMid_step (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r' : L) :
    fixFirstVariablesOfMQP (ℓ - i.castSucc)
        ⟨1, by have := i.isLt; simp only [Fin.val_castSucc]; omega⟩
        (projectToMidSumcheckPoly ℓ t m i.castSucc challenges).val (fun _ => r')
      = rename (finCongr (show ℓ - (i.succ : ℕ) = ℓ - i.castSucc - 1 by
          have := i.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega))
          (projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r')).val := by
  rw [projectToMidSumcheckPoly_eq_fixVars, projectToMidSumcheckPoly_eq_fixVars]
  -- `fixVars_step` at `v := i.castSucc`. Its `⟨↑v + 1⟩` matches `⟨↑i.succ⟩` (both `↑i + 1`).
  have hstep := fixVars_step (L := L) ℓ (m.val * t.val) i.castSucc
    (by have := i.isLt; simp only [Fin.val_castSucc]; omega) challenges r'
  rw [hstep]
  -- Both sides are `rename (finCongr …) (fixFirstVariablesOfMQP ℓ ⟨_⟩ (m·t) (Fin.snoc ch r'))`;
  -- the only difference is the fixed-variable count index `⟨↑i.castSucc + 1⟩` vs `⟨↑i.succ⟩`,
  -- which are equal `Fin (ℓ+1)` values (`↑i.succ = ↑i + 1 = ↑i.castSucc + 1`), hence defeq.
  rfl

/-- Renaming a polynomial along the canonical `finCongr` of a (propositional) dimension equality is
heterogeneously equal to the original (after `subst`, `finCongr` is `Equiv.refl` and `rename id` is
the identity). -/
private lemma rename_finCongr_heq_projectToMid {a b : ℕ} (h : a = b) (p : MvPolynomial (Fin a) L) :
    HEq (rename (finCongr h) p) p := by
  subst h
  rw [finCongr_refl, Equiv.coe_refl, rename_id_apply]

/-- **Structural-invariant round transition (un-renamed cast-wall form, `#29` per-round
completeness conjunct 2).** Fixing the round-`i` survivor variable to the verifier challenge `r'`
advances the projected sumcheck polynomial from round `i.castSucc` to round `i.succ`, *as an honest
equality of `MvPolynomial (Fin (ℓ - i.succ)) L`*: the index types `Fin (ℓ - i.succ)` and
`Fin (ℓ - i.castSucc - 1)` are definitionally equal (`Nat.sub_succ`), so the canonical `finCongr`
rename produced by `fixFirstVariablesOfMQP_projectToMid_step` collapses to the identity
(`rename_finCongr_heq_projectToMid`). This is the missing conjunct-2 algebra for the structured
per-round completeness output relation `witnessStructuralInvariant`; the matching conjunct-3
(sum-consistency) transition is `SumcheckPhase.getSumcheckRoundPoly_eval_eq_cube_succ`. -/
theorem fixFirstVariablesOfMQP_projectToMid_succ (ℓ : ℕ) [NeZero ℓ]
    (t m : MultilinearPoly L ℓ) (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r' : L) :
    fixFirstVariablesOfMQP (ℓ - ↑i.castSucc)
        ⟨1, by have := i.2; simp only [Fin.val_castSucc]; omega⟩
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
          (i := i.castSucc) (challenges := challenges)).val
        (fun _ => r')
      = (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
          (i := i.succ) (challenges := Fin.snoc challenges r')).val := by
  rw [fixFirstVariablesOfMQP_projectToMid_step (L := L) (ℓ := ℓ) t m i challenges r']
  exact eq_of_heq (rename_finCongr_heq_projectToMid _ _)

/-- **Round-polynomial marginal identity (core of target (b)).** Evaluating, at `r'`, the sum over a
finite set `S` of the partial evaluations `Polynomial.map (eval (pt x)) (finSuccEquivNth L 0 H)`
equals the sum over `S` of the full evaluations of `H` with variable `0` fixed to `r'` (the rest set
by `pt x`). This is the marginal that `getSumcheckRoundPoly` computes: it keeps variable `0` as the
round indeterminate (`finSuccEquivNth L 0`, i.e. `Fin.insertNth 0 = Fin.cons`). Generic in the index
type/point function so it can absorb the `Fin.append (∅) · ∘ Fin.cast` reindexing of the round code.

The identity follows directly from `eval_eq_eval_mv_eval_finSuccEquivNth` and
`Fin.insertNth_zero`; it agrees with the canonical prefix-fixing convention.
-/
theorem roundPoly_eval_eq_sum_cons {k : ℕ} {ι : Type*} (S : Finset ι) (pt : ι → (Fin k → L))
    (H : MvPolynomial (Fin (k + 1)) L) (r' : L) :
    Polynomial.eval r' (∑ x ∈ S, Polynomial.map (eval (pt x)) (finSuccEquivNth L 0 H))
      = ∑ x ∈ S, eval (Fin.cons r' (pt x)) H := by
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← eval_eq_eval_mv_eval_finSuccEquivNth, Fin.insertNth_zero']

/-- The independent last-variable marginal identity: evaluating the partial univariate
polynomial at `r'` is evaluation at `Fin.snoc (pt x) r'`, summed over the finite index set. -/
theorem roundPoly_eval_eq_sum_snoc {k : ℕ} {ι : Type*} (S : Finset ι) (pt : ι → (Fin k → L))
    (H : MvPolynomial (Fin (k + 1)) L) (r' : L) :
    Polynomial.eval r' (∑ x ∈ S, Polynomial.map (eval (pt x)) (finSuccEquivNth L (Fin.last k) H))
      = ∑ x ∈ S, eval (Fin.snoc (pt x) r') H := by
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← eval_eq_eval_mv_eval_finSuccEquivNth, Fin.insertNth_last']

end RoundTransition


/-! ## Schwartz–Zippel root-counting bridge

The single-round / batching RBR-knowledge-soundness proofs bound the probability that a uniformly
sampled field challenge falls in the agreement set of two polynomials (equivalently: is a root of
their nonzero difference). The lemmas below are the reusable bridge from a degree bound to that
probability bound, via `Polynomial.card_le_degree_of_subset_roots` (`#{roots} ≤ natDegree`). They
are field/`IsDomain`-generic and plug directly into the `probEvent_uniformSample` endgame of an
`rbrKnowledgeSoundness` proof over a uniform challenge `r ← ($ᵗ L)`. -/
section SchwartzZippelRootBound

open Polynomial Finset OracleComp

/-- **Root-set cardinality bound.** Over an integral domain `L`, the number of field elements at
which a nonzero univariate polynomial `p` vanishes is at most `p.natDegree`. This is the finite,
`Fintype`-indexed form of `Polynomial.card_roots'` (`#{x | p.eval x = 0} ≤ natDegree p`), the core
of the Schwartz–Zippel argument. -/
theorem card_filter_eval_zero_le {L : Type*} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] (p : L[X]) (hp : p ≠ 0) :
    (Finset.univ.filter (fun x => p.eval x = 0)).card ≤ p.natDegree :=
  _root_.Polynomial.card_filter_eval_zero_le p hp

/-- **Schwartz–Zippel probability bound (uniform-challenge / `probEvent` form).** For a nonzero
univariate `p` over a finite integral domain `L` with `p.natDegree ≤ d`, the probability that a
uniformly sampled `x ← ($ᵗ L)` is a root of `p` is at most `d / |L|`. This is the form that plugs
directly into the `rbrKnowledgeSoundness` probability endgame after the verifier-run/challenge
plumbing has reduced the goal to `Pr{let x ← $ᵗ L}[p.eval x = 0] ≤ d / Fintype.card L`. -/
theorem probEvent_eval_zero_le {L : Type} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] [SampleableType L]
    (p : L[X]) (hp : p ≠ 0) (d : ℕ) (hd : p.natDegree ≤ d) :
    Pr{let x ← $ᵗ L}[p.eval x = 0] ≤ (d : ENNReal) / (Fintype.card L) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  apply ENNReal.div_le_div_right
  exact le_trans (Nat.cast_le.mpr ((card_filter_eval_zero_le p hp).trans hd)) le_rfl

/-- **Agreement-set form of the Schwartz–Zippel bound.** Two univariate polynomials `p q` over a
finite integral domain `L` agree at a uniformly sampled `x ← ($ᵗ L)` with probability at most
`d / |L|`, provided `p ≠ q` and `(p - q).natDegree ≤ d`. This is the shape that arises when the bad
event compares a (claimed) prover polynomial against the (ground-truth) witness polynomial at the
challenge point. -/
theorem probEvent_eval_eq_le {L : Type} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] [SampleableType L]
    (p q : L[X]) (hpq : p ≠ q) (d : ℕ) (hd : (p - q).natDegree ≤ d) :
    Pr{let x ← $ᵗ L}[p.eval x = q.eval x] ≤ (d : ENNReal) / (Fintype.card L) := by
  have hsub : p - q ≠ 0 := sub_ne_zero_of_ne hpq
  have hev : (fun x => p.eval x = q.eval x) = (fun x => (p - q).eval x = 0) := by
    funext x; rw [Polynomial.eval_sub, sub_eq_zero]
  rw [hev]
  exact probEvent_eval_zero_le (p - q) hsub d hd

/-- **Degree-2 agreement bound for weakened KState (issue #29).**
The iterated ring-switching sumcheck round compares two degree-`≤ 2` univariate polynomials:
the prover message `h_i` and the ground-truth round polynomial `h_star`. This specialization packages
the reusable Schwartz-Zippel bridge in exactly that bad-event shape, leaving only the verifier-run
plumbing that extracts `hp`, `hq`, and `hpq` from the KState branch. -/
theorem probEvent_eval_eq_degree_two_le {L : Type} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] [SampleableType L]
    (p q : L[X]) (hpq : p ≠ q) (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    Pr{let x ← $ᵗ L}[p.eval x = q.eval x] ≤ (2 : ENNReal) / (Fintype.card L) := by
  exact probEvent_eval_eq_le p q hpq 2
    (le_trans (Polynomial.natDegree_sub_le p q) (max_le hp hq))

/-- **Bad-agreement event bound from a difference-degree budget.**
This is the exact doom-escape event described by the weakened KState design: the prover's round
polynomial is not the ground truth, but both agree at the verifier's fresh challenge. The theorem
separates the event-level weakening from the source of the degree bound, so later KState plumbing can
use either a direct bound on `(p - q).natDegree` or one derived from common polynomial carriers. -/
theorem probEvent_badAgreement_of_sub_degree_le {L : Type} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] [SampleableType L]
    (p q : L[X]) (d : ℕ) (hd : (p - q).natDegree ≤ d) :
    Pr{let x ← $ᵗ L}[p ≠ q ∧ p.eval x = q.eval x] ≤
      (d : ENNReal) / (Fintype.card L) := by
  by_cases hpq : p = q
  · rw [SampleableType.prEvent_uniformSample]
    have hfilter :
        (Finset.univ.filter (fun x => p ≠ q ∧ p.eval x = q.eval x)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x _ hbad
      exact hbad.1 hpq
    rw [hfilter]
    simp
  · have hmono : Pr{let x ← $ᵗ L}[p ≠ q ∧ p.eval x = q.eval x] ≤
        Pr{let x ← $ᵗ L}[p.eval x = q.eval x] := by
      rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample]
      apply ENNReal.div_le_div_right
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2.2⟩
    exact le_trans hmono (probEvent_eval_eq_le p q hpq d hd)

/-- **Bad-agreement event bound from common degree budgets.**
If both polynomials have degree at most `d`, then the weakened-KState bad-agreement event has
probability at most `d / |L|`. -/
theorem probEvent_badAgreement_le {L : Type} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] [SampleableType L]
    (p q : L[X]) (d : ℕ) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    Pr{let x ← $ᵗ L}[p ≠ q ∧ p.eval x = q.eval x] ≤
      (d : ENNReal) / (Fintype.card L) := by
  exact probEvent_badAgreement_of_sub_degree_le p q d
    (le_trans (Polynomial.natDegree_sub_le p q) (max_le hp hq))

/-- **Degree-2 bad-agreement event bound for weakened KState (issue #29).**
The degree-`≤ 2` specialization for ring-switching round polynomials. -/
theorem probEvent_badAgreement_degree_two_le {L : Type} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] [SampleableType L]
    (p q : L[X]) (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    Pr{let x ← $ᵗ L}[p ≠ q ∧ p.eval x = q.eval x] ≤
      (2 : ENNReal) / (Fintype.card L) := by
  exact probEvent_badAgreement_le p q 2 hp hq

#print axioms RingSwitching.probEvent_eval_eq_degree_two_le
#print axioms RingSwitching.probEvent_badAgreement_of_sub_degree_le
#print axioms RingSwitching.probEvent_badAgreement_le
#print axioms RingSwitching.probEvent_badAgreement_degree_two_le

end SchwartzZippelRootBound

/-! ### Axiom audit (issue #29 batching row-orientation frontier) -/

#print axioms RingSwitching.decomposeRows_embedded_MLP_eval'

end RingSwitching

#print axioms RingSwitching.binaryTowerProfile

#print axioms RingSwitching.performCheckOriginalEvaluation_packMLE_iff

#print axioms RingSwitching.A_MLE_eval_eq_compute_final_eq_value

#print axioms RingSwitching.fixVars_step

#print axioms RingSwitching.fixFirstVariablesOfMQP_projectToMid_succ
