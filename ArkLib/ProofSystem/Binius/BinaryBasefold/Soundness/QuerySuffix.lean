/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
import ProximityPrize.Compatibility.BiniusFolding
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Prelude
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.Data.Misc.Basic
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Relations
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.UDRCongruence

/-!
# Binary Basefold query suffix bounds

Alignment of iterated quotient maps with fiber indices, query-phase bounds, and folding transport.
-/

section SuffixAlignCore

/-!
## Quotient-map alignment at a fiber index.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

set_option linter.unusedSectionVars false

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Transport an `sDomain` point across a propositional index equality by underlying value. -/
def suffixLiftIdx (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i₁) : sDomain 𝔽q β h_ℓ_add_R_rate i₂ :=
  ⟨x.val, h ▸ x.property⟩

lemma suffixLiftIdx_val (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i₁) :
    (suffixLiftIdx 𝔽q β i₁ i₂ h x).val = x.val := by
  cases h
  rfl

/-- `Subtype.val` of a `cast` between two `sDomain` types over equal indices. -/
lemma val_of_cast_sDomain (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (hty : ↥(sDomain 𝔽q β h_ℓ_add_R_rate i₁) = ↥(sDomain 𝔽q β h_ℓ_add_R_rate i₂))
    (z : sDomain 𝔽q β h_ℓ_add_R_rate i₁) :
    (cast hty z).val = z.val := by
  cases h
  rfl

/-- Basis-coefficient congruence across (propositionally) equal `sDomain` indices. -/
lemma sDomain_repr_congr (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (h_i₁ : i₁.val < ℓ + 𝓡) (h_i₂ : i₂.val < ℓ + 𝓡)
    (x₁ : sDomain 𝔽q β h_ℓ_add_R_rate i₁) (x₂ : sDomain 𝔽q β h_ℓ_add_R_rate i₂)
    (hx : x₁.val = x₂.val)
    (j₁ : Fin (ℓ + 𝓡 - i₁.val)) (j₂ : Fin (ℓ + 𝓡 - i₂.val)) (hj : j₁.val = j₂.val) :
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate i₁ h_i₁).repr x₁) j₁ =
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate i₂ h_i₂).repr x₂) j₂ := by
  subst h
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  obtain rfl : j₁ = j₂ := Fin.ext hj
  rfl

/-- Value-level suffix/fiber alignment, allowing an opaque but equal destination point.
The source remains the historical `Fin ℓ` index; the canonical quotient uses explicit `Fin r`
destination indices. -/
lemma iteratedQuotientMap_val_eq_qMap_total_fiber_extractMiddleFinMask
    (i : Fin ℓ) (steps : ℕ) (h_bound : i.val + steps ≤ ℓ)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, Nat.pos_of_neZero r⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩)
    (hy : y.val = (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨0, Nat.pos_of_neZero r⟩) (destIdx := ⟨i.val + steps, by omega⟩)
      (k := i.val + steps) (h_destIdx := by simp only [Fin.val_mk, zero_add])
      (h_destIdx_le := h_bound) v).val) :
    (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero r⟩)
      (destIdx := ⟨i.val, by omega⟩) (k := i.val)
      (h_destIdx := by simp only [Fin.val_mk, zero_add])
      (h_destIdx_le := by simp only; omega) v).val =
    (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, by omega⟩) (steps := steps)
      (h_i_add_steps := by have := Nat.pos_of_neZero 𝓡; simp only; omega) y
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v
        ⟨i.val, by omega⟩ steps)).val := by
  have h := iteratedQuotientMap_eq_quotientFiber_extractMiddleFinMask
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i.val, by omega⟩) (steps := steps)
    (destIdx := ⟨i.val + steps, by omega⟩) (h_destIdx := rfl)
    (h_destIdx_le := h_bound) v
  have hy' : y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨0, Nat.pos_of_neZero r⟩) (destIdx := ⟨i.val + steps, by omega⟩)
      (k := i.val + steps) (h_destIdx := by simp only [Fin.val_mk, zero_add])
      (h_destIdx_le := h_bound) v := Subtype.ext hy
  subst y
  by_cases hs : steps = 0
  · subst steps
    simpa [quotientFiber, qMap_total_fiber] using congrArg Subtype.val h
  · simpa only [quotientFiber, qMap_total_fiber, hs, ↓reduceDIte] using
      congrArg Subtype.val h

/-- Suffix/fiber alignment with explicit canonical destinations. These remove the former
casts from `0+i` and `0+(i+steps)` to their equal destination indices. -/
lemma cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask_core
    (i steps : ℕ) (h_i_lt_ℓ : i < ℓ) (h_le : i + steps ≤ ℓ)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, Nat.pos_of_neZero r⟩) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero r⟩)
      (destIdx := ⟨i, by omega⟩) (k := i)
      (h_destIdx := by simp only [Fin.val_mk, zero_add]) (h_destIdx_le := by simp only; omega) v =
    qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by have := Nat.pos_of_neZero 𝓡; simp only; omega)
      (y := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero r⟩)
        (destIdx := ⟨i + steps, by omega⟩) (k := i + steps)
        (h_destIdx := by simp only [Fin.val_mk, zero_add]) (h_destIdx_le := h_le) v)
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v ⟨i, by omega⟩ steps) := by
  apply Subtype.ext
  exact iteratedQuotientMap_val_eq_qMap_total_fiber_extractMiddleFinMask
    𝔽q β ⟨i, h_i_lt_ℓ⟩ steps h_le v _ rfl

end

end Binius.BinaryBasefold

end SuffixAlignCore

section QueryPhaseSuffix

/-!
## Suffix alignment for the query phase.
-/

/-!
## Binary Basefold Query-Phase Suffix Helpers

This module isolates the challenge-suffix/fiber alignment layer from the heavier query-phase
soundness helper file.  It provides the small public surface needed by later query-phase proofs
and by the issue #317 suffix/fiber alignment audit.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

noncomputable section

namespace QueryPhase

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1
  [NeZero r] [NeZero 𝓡] in
/-- For a block index `k < ℓ / ϑ` (with `ϑ ∣ ℓ`), the block end `k * ϑ + ϑ`
is `≤ ℓ`. -/
lemma k_succ_mul_ϑ_le_ℓ_₂ (k : Fin (ℓ / ϑ)) : k.val * ϑ + ϑ ≤ ℓ := by
  have hk : k.val + 1 ≤ ℓ / ϑ := k.isLt
  have h_div_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_mul_le : (k.val + 1) * ϑ ≤ (ℓ / ϑ) * ϑ := Nat.mul_le_mul_right ϑ hk
  rw [h_div_mul] at h_mul_le
  have h_expand : (k.val + 1) * ϑ = k.val * ϑ + ϑ := by ring
  omega

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1
  [NeZero r] [NeZero 𝓡] in
/-- For a block index `k < ℓ / ϑ` (with `ϑ ∣ ℓ`), the block start `k * ϑ`
is `< ℓ`. -/
lemma k_mul_ϑ_lt_ℓ (k : Fin (ℓ / ϑ)) : k.val * ϑ < ℓ := by
  have hϑ : 0 < ϑ := Nat.pos_of_neZero ϑ
  have h := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  omega

def challengeSuffixToFin (k : Fin (ℓ / ϑ))
    (suffix : sDomain 𝔽q β h_ℓ_add_R_rate ⟨k.val * ϑ + ϑ, by
    have := k_succ_mul_ϑ_le_ℓ_₂ (k := k); omega⟩) : Fin (2 ^ (ℓ + 𝓡 - (k.val * ϑ + ϑ))) :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  sDomainToFin 𝔽q β h_ℓ_add_R_rate (i := ⟨k.val * ϑ + ϑ, by omega⟩) (h_i := by
    simp only [k_succ_mul_ϑ_le_ℓ_₂, Nat.lt_add_of_pos_right_of_le]) suffix

end QueryPhase

section QueryPhaseSuffixLemmas

open QueryPhase

lemma getFiberPoint_eq_qMap_total_fiber
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (u : Fin (2 ^ ϑ)) :
    getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u =
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
        (steps := ϑ)
        (h_i_add_steps := by
          have h_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
          simp only [Fin.val_mk]; omega)
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) u := by
  simp only [getFiberPoint, oraclePositionToDomainIndex, id_eq,
    quotientFiber, qMap_total_fiber, NeZero.ne ϑ, ↓reduceDIte]

/-- The challenge suffix at block source `j * ϑ` equals the fiber point at the
`extractMiddleFinMask` index. -/
lemma previousSuffix_eq_getFiberPoint_extractMiddleFinMask
    (j : Fin (ℓ / ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨j.val * ϑ, by
        exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := k_mul_ϑ_lt_ℓ (k := j))⟩)
      (h_destIdx_le := Nat.le_of_lt (k_mul_ϑ_lt_ℓ (k := j))) =
      getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (i := ⟨j.val * ϑ, by have := k_mul_ϑ_lt_ℓ (k := j); omega⟩)
          (steps := ϑ)) := by
  exact extractSuffixFromChallenge_eq_getFiberPoint_extractMiddleFinMask 𝔽q β j v

end QueryPhaseSuffixLemmas

end

end Binius.BinaryBasefold

end QueryPhaseSuffix

section QueryPhasePrelims

/-!
## Query-phase preliminary bounds.
-/

/-!
## Binary Basefold Soundness Query Phase Preliminaries

Shared helper definitions and alignment lemmas for the query phase of Binary Basefold soundness.
This file packages:
1. challenge-suffix extraction and transport lemmas
2. monadic query-phase helper functions for oracle access and folding checks
3. logical counterparts used later in the final query-phase soundness proof

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering below follows the archived revision of [DP24].
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

namespace QueryPhase

/-!
## Common Proximity Check Helpers

These functions extract the shared logic between `queryOracleVerifier`
and `queryKnowledgeStateFunction` for proximity testing, allowing code reuse
and ensuring both implementations follow the same logic.
-/

/-- Decompose challenge v at position i into (fiberIndex, suffix).
    This is the inverse of `Nat.joinBits` in some sense.
    Uses loose indexing with `Fin r`. -/
def decomposeChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (i : Fin ℓ) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx_le : destIdx ≤ ℓ) :
    Fin (2^steps) × sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v:=v) (i:=⟨i.val, by have := i.isLt; omega⟩) (steps:=steps),
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v:=v)
      (destIdx:=destIdx) (h_destIdx_le:=h_destIdx_le))

-- Future work: KEY LEMMA for connecting fiber queries to challenge decomposition
-- Future work: Lemma connecting queryFiberPoints to extractMiddleFinMask

/-- Legacy spelling of the canonical one-repetition query error. -/
abbrev queryRbrKnowledgeError_singleRepetition : ℝ≥0 :=
  queryRbrKnowledgeErrorSingleRepetition (𝓡 := 𝓡)

section FinalQueryRoundIOR

/-!
### IOR Implementation for the Final Query Round
-/

section MonadicOracleVerification
/-!
### Helper Functions for Verifier Logic

These functions break down the verifier's proximity checking logic into composable blocks,
making it easier to prove properties about each component separately.
-/

end MonadicOracleVerification

section LogicalOracleVerification

/-!
### Proximity check spec: logical defs (mirror monadic verifier exactly)

Logical (non-monadic) versions that capture 100% of the monadic definitions.

Key property from docstring:
  if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
  `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
  `V` requires `c_ℓ ?= c`.

The logical definitions mirror this exactly:
- `logical_queryFiberPoints` → Queries all `u` for a given step `k` (where `i = k·ϑ`)
- `logical_computeFoldedValue` → Computes `c_{i+ϑ}` via folding
- `logical_checkSingleFoldingStep` → Performs the guard check when `i > 0`
- `logical_checkSingleRepetition` → Enforces all guard checks and the final equality
- `logical_proximityChecksSpec` → Lifts to all `γ` repetitions

### Correspondence with Monadic Implementation

Each monadic function has a logical counterpart:
- `queryFiberPoints` ↔ `logical_queryFiberPoints`
- The snake_case logical checks retain the historical newest-first compatibility view.
  Canonical monadic checks use chronological challenges; they require an explicit input conversion.
- `checkSingleRepetition` ↔ `logical_checkSingleRepetition`
-/

/-- Fiber evals for all u (logical; same as monadic `queryFiberPoints`). -/
def logical_queryFiberPoints
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) : Fin (2 ^ ϑ) → L :=
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k.val, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
      add_zero, Fin.is_lt]⟩
  fun u => oStmt k_th_oracleIdx (getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u)

/-- Historical newest-first folded value at step `k`.
This takes `f_i_on_fiber` - the list of `2^ϑ` fiber evaluations on oracle domain
`k*ϑ`, folds them into a single oracle evaluation on oracle domain `(k+1)*ϑ`, i.e. `c_{i+ϑ}`. -/
def logical_computeFoldedValue
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f_i_on_fiber : Fin (2 ^ ϑ) → L) : L :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  let next_suffix_of_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
    getChallengeSuffix (k := k) (v := v)
  let cur_challenge_batch : Fin ϑ → L := fun j =>
    foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmt.challenges ⟨i + j.val, by simp only [Fin.val_last]; omega⟩
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := ϑ) (destIdx := destIdx) (h_destIdx := by dsimp only [destIdx])
    (h_destIdx_le := by omega) (r_challenges := cur_challenge_batch) (y := next_suffix_of_v)
    (fiber_eval_mapping := f_i_on_fiber)

/-- Check a historical newest-first folding step at `k`.

    Captures the guard check from docstring:
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`
    Where c_i is the fold value from step k-1, and f^(i)(v_i,...) is the oracle
    at position k evaluated at the "overlap" point.
    Note: h_i_pos implies k > 0, so k-1 is valid. -/
def logical_checkSingleFoldingStep
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) : Prop :=
  -- Index k represents
  let i := k.val * ϑ
  -- `k ∈ {0, 1, ..., ℓ/ϑ-1}`, `i ∈ {0, ϑ, 2ϑ, ..., ℓ-ϑ}`
  -- **NOTE**: this definition is the
    -- `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})` check at inner repetition `k`
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let f_i_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k v
  -- Actually we only need value of one point of `f_i_on_fiber` for this check
  -- This matches monadic: `guard (c_cur = f_i_val)`
  if h_i_pos : i > 0 then
    -- h_i_pos implies k > 0 (since i = k * ϑ and ϑ > 0)
    have h_k_pos : k.val > 0 := Nat.pos_of_mul_pos_right h_i_pos
    let k_prev : Fin (ℓ / ϑ) := ⟨k.val - 1, by omega⟩
    -- c_cur = fold value from step k-1
    let f_prev_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k_prev v
    -- In logical specification, we look backwards at oracle domain `(k-1)*ϑ` to query
    -- the fiber evaluations `f_prev_on_fiber`, fold them to create `c_cur`.
    -- In the monadic `checkSingleFoldingStep`, `c_cur` is automatically available.
    let c_cur := logical_computeFoldedValue 𝔽q β k_prev v stmt f_prev_on_fiber
    -- f_i_val = oracle value at overlap point
    let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (i := ⟨i, by have := k_mul_ϑ_lt_ℓ (k := k); dsimp only [i]; omega⟩) (steps := ϑ)
    let f_i_val := f_i_on_fiber oracle_point_idx
    c_cur = f_i_val
  else True

/-- Logical check specific to step k.
    If k is an intermediate index, it is the consistency of the folding step.
    If k is the terminal index, it is the constant check. -/
def logical_stepCondition (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ + 1)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  if h_k_lt : k.val < (ℓ / ϑ) then
    -- Condition for `k ∈ {0, 1, ..., ℓ/ϑ-1}`
    logical_checkSingleFoldingStep 𝔽q β oStmt ⟨k.val, h_k_lt⟩ v stmt
  else
    -- Condition for the final state k = `ℓ/ϑ`
    have h_div_pos : ℓ / ϑ > 0 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
    let k_last : Fin (ℓ / ϑ) := ⟨ℓ / ϑ - 1, by omega⟩
    let f_last_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k_last v
    logical_computeFoldedValue 𝔽q β k_last v stmt f_last_on_fiber = final_constant

/-- Check a single repetition using the historical newest-first input convention.
    Captures:
    1. All guard checks pass: ∀ k, logical_checkSingleFoldingStep
    2. Final check: c_ℓ = final_constant (fold at last step equals final constant) -/
def logical_checkSingleRepetition
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  ∀ k : Fin (ℓ / ϑ + 1),
    logical_stepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt) (k := k) (v := v) (stmt := stmt) (final_constant := final_constant)

/-- Proximity checks spec: for all γ repetitions, `logical_checkSingleRepetition` holds. -/
def logical_proximityChecksSpec
    (γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  ∀ rep : Fin γ_repetitions,
    logical_checkSingleRepetition 𝔽q β oStmt (γ_challenges rep) stmt final_constant

end LogicalOracleVerification

end FinalQueryRoundIOR

end QueryPhase

end

end Binius.BinaryBasefold

end QueryPhasePrelims



section QueryPhaseFoldBridge

/-!
## Bridge between query values and folding.
-/

/-!
## Binary Basefold Query-Phase Logical Fold Bridge

Logical query-phase functions are defined in `QueryPhasePrelims`; this module contains the
heavier bridge lemmas relating them to the generic fiber-evaluation and iterated-fold APIs.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

namespace QueryPhase

set_option maxHeartbeats 1600000 in
lemma logical_queryFiberPoints_eq_fiberEvaluations
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt k v =
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩) (steps := ϑ)
        (h_destIdx := by rfl) (h_destIdx_le := by
          exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
        (f := oStmt ⟨k.val, by
          simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
            Fin.is_lt]⟩)
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) := by
  funext u
  rw [fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨k.val * ϑ,
      lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
        (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
    (steps := ϑ)
    (h_i_add_steps_le := by
      simpa only [Fin.val_mk] using k_succ_mul_ϑ_le_ℓ_₂ (k := k))
    (h_i_add_steps_lt_r := by
      exact
        lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
            (i := Fin.last ℓ) (j := ⟨k.val, by
              simp only [toOutCodewordsCount_last]
              exact k.isLt⟩)))
    (f := oStmt ⟨k.val, by
      simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
        Fin.is_lt]⟩)
    (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v))
    (idx := u)]
  simp only [logical_queryFiberPoints]
  rw [getFiberPoint_eq_qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u]

end QueryPhase

end

end Binius.BinaryBasefold

end QueryPhaseFoldBridge

section QueryPhaseFoldedValue

/-!
## Folded-value query bounds.
-/

/-!
## Binary Basefold Query-Phase Folded-Value Bridge

This module isolates the folded-value-to-`iterated_fold` equality from the lighter
query-fiber bridge so the query-phase soundness dependencies can cache incrementally.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

namespace QueryPhase

lemma logical_computeFoldedValue_eq_iterated_fold
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v stmt
      (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt k v)
      =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨k.val * ϑ,
        lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
          (h := k_mul_ϑ_lt_ℓ (k := k))⟩) (steps := ϑ)
      (h_destIdx := by rfl) (h_destIdx_le := by
        exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
      (f := oStmt ⟨k.val, by
        simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
          Fin.is_lt]⟩)
      (r_challenges :=
        Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
          stmt.challenges (k := k.val * ϑ) (h := k_succ_mul_ϑ_le_ℓ_₂ (k := k)))
      (getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) := by
  simp only [logical_computeFoldedValue]
  rw [logical_queryFiberPoints_eq_fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    oStmt k v]
  convert single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨k.val * ϑ,
      lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
        (h := k_mul_ϑ_lt_ℓ (k := k))⟩) (steps := ϑ)
    (h_destIdx := by rfl) (h_destIdx_le := by exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
    (h_i_lt := by exact k_mul_ϑ_lt_ℓ (k := k))
    (f := oStmt ⟨k.val, by
      simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
        Fin.is_lt]⟩)
    (Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        stmt.challenges (k := k.val * ϑ) (h := k_succ_mul_ϑ_le_ℓ_₂ (k := k)))
    (getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v))
  -- The only congruence residue is the challenge-batch slot: `logical_computeFoldedValue`
  -- writes it as a `foldOrderChallenges` lambda while the bridge lemma packages the same
  -- function as the newest-first adapter; they agree definitionally (delta + proof irrelevance).
  all_goals
    first
      | rfl
      | (simp only [Compatibility.newestFirstFoldingChallenges, getFoldingChallenges, foldOrderChallenges])
      | (funext cId; simp only [Compatibility.newestFirstFoldingChallenges, getFoldingChallenges, foldOrderChallenges])
      | (simp [Compatibility.newestFirstFoldingChallenges, getFoldingChallenges, foldOrderChallenges])

/-- Fiber values have the canonical ordering; only the challenge convention changes. -/
lemma logical_queryFiberPoints_eq_canonical
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    logical_queryFiberPoints 𝔽q β oStmt k v = logicalQueryFiberPoints 𝔽q β oStmt k v := rfl

/-- Explicit statement conversion makes historical and canonical carried values agree.
This compares their actions on actual oracle fibers, not their different raw matrix layouts. -/
lemma logical_computeFoldedValue_reverse_eq_canonical
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    logical_computeFoldedValue 𝔽q β k v (Compatibility.reverseFinalChallenges stmt)
        (logical_queryFiberPoints 𝔽q β oStmt k v) =
      logicalComputeFoldedValue 𝔽q β k v stmt (logicalQueryFiberPoints 𝔽q β oStmt k v) := by
  rw [logical_computeFoldedValue_eq_iterated_fold,
    Compatibility.iterated_fold_eq_canonical, logicalComputeFoldedValue_eq_iteratedFold]
  congr 2
  funext j
  simp only [Compatibility.newestFirstFoldingChallenges, getFoldingChallenges,
    Compatibility.reverseFinalChallenges, Fin.rev_rev]

/-- The historical guard on a converted statement is exactly the canonical guard. -/
lemma logical_checkSingleFoldingStep_reverse_eq_canonical
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    logical_checkSingleFoldingStep 𝔽q β oStmt k v (Compatibility.reverseFinalChallenges stmt) =
      LogicalCheckSingleFoldingStep 𝔽q β oStmt k v stmt := by
  dsimp only [logical_checkSingleFoldingStep, LogicalCheckSingleFoldingStep]
  split_ifs
  · rw [logical_computeFoldedValue_reverse_eq_canonical]
    rfl
  · rfl

/-- Explicit conversion preserves each guard and the terminal constant comparison. -/
lemma logical_stepCondition_reverse_eq_canonical
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ + 1)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (c : L) :
    logical_stepCondition 𝔽q β oStmt k v (Compatibility.reverseFinalChallenges stmt) c =
      LogicalStepCondition 𝔽q β oStmt k v stmt c := by
  dsimp only [logical_stepCondition, LogicalStepCondition]
  split_ifs
  · exact logical_checkSingleFoldingStep_reverse_eq_canonical 𝔽q β oStmt _ v stmt
  · rw [logical_computeFoldedValue_reverse_eq_canonical]

/-- A whole historical repetition on the converted statement is the canonical check. -/
lemma logical_checkSingleRepetition_reverse_eq_canonical
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (c : L) :
    logical_checkSingleRepetition 𝔽q β oStmt v (Compatibility.reverseFinalChallenges stmt) c =
      LogicalCheckSingleRepetition 𝔽q β oStmt v stmt c := by
  simp only [logical_checkSingleRepetition, LogicalCheckSingleRepetition,
    logical_stepCondition_reverse_eq_canonical]


/-- The conversion preserves every repetition in the full logical proximity check. -/
lemma logical_proximityChecksSpec_reverse_eq_canonical (γ : ℕ)
    (points : Fin γ → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (c : L) :
    logical_proximityChecksSpec 𝔽q β (γ_repetitions := γ) points oStmt
        (Compatibility.reverseFinalChallenges stmt) c =
      LogicalProximityChecksSpec 𝔽q β (γ_repetitions := γ) points oStmt stmt c := by
  simp only [logical_proximityChecksSpec, LogicalProximityChecksSpec,
    logical_checkSingleRepetition_reverse_eq_canonical]


end QueryPhase

end

end Binius.BinaryBasefold

end QueryPhaseFoldedValue

#print axioms Binius.BinaryBasefold.QueryPhase.logical_computeFoldedValue_reverse_eq_canonical
#print axioms Binius.BinaryBasefold.QueryPhase.logical_checkSingleFoldingStep_reverse_eq_canonical
#print axioms Binius.BinaryBasefold.QueryPhase.logical_stepCondition_reverse_eq_canonical
#print axioms Binius.BinaryBasefold.QueryPhase.logical_checkSingleRepetition_reverse_eq_canonical

#print axioms Binius.BinaryBasefold.iteratedQuotientMap_val_eq_qMap_total_fiber_extractMiddleFinMask
#print axioms Binius.BinaryBasefold.cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask_core
#print axioms Binius.BinaryBasefold.previousSuffix_eq_getFiberPoint_extractMiddleFinMask
#print axioms Binius.BinaryBasefold.QueryPhase.logical_proximityChecksSpec_reverse_eq_canonical
