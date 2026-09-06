/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.Data.Misc.Basic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
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

set_option maxHeartbeats 1600000 in
/-- **Value-level suffix/fiber alignment (current CompPoly API), y-opaque form.**
The `i.val`-step iterated quotient of `v ∈ S⁽⁰⁾` equals (by underlying value) the
`qMap_total_fiber` preimage of any point `y` whose value is the `(i.val + steps)`-step
iterated quotient of `v`, taken at fiber index `extractMiddleFinMask v i steps`. -/
lemma iteratedQuotientMap_val_eq_qMap_total_fiber_extractMiddleFinMask
    (i : Fin ℓ) (steps : ℕ) (h_bound : i.val + steps ≤ ℓ)
    (v : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, Nat.pos_of_neZero r⟩)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by
      have h𝓡 := Nat.pos_of_neZero 𝓡; have hr := h_ℓ_add_R_rate; omega⟩)
    (hy : y.val = (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
      (k := i.val + steps)
      (h_bound := by show 0 + (i.val + steps) ≤ ℓ; omega)
      (x := v)).val) :
    (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
      (h_bound := by show 0 + i.val ≤ ℓ; have hi := i.isLt; omega)
      (x := v)).val =
    (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, by have hi := i.isLt; have hr := h_ℓ_add_R_rate; omega⟩)
      (steps := steps)
      (h_i_add_steps := by
        show i.val + steps < ℓ + 𝓡; have h𝓡 := Nat.pos_of_neZero 𝓡; omega)
      (y := y)
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps)).val := by
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
  have hi : i.val < ℓ := i.isLt
  have hmain :
      suffixLiftIdx 𝔽q β
        ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val + i.val, by
          show 0 + i.val < r; have hr := h_ℓ_add_R_rate; omega⟩
        ⟨i.val, by have hr := h_ℓ_add_R_rate; omega⟩
        (by apply Fin.eq_of_val_eq; show 0 + i.val = i.val; omega)
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
          (h_bound := by show 0 + i.val ≤ ℓ; omega)
          (x := v)) =
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i.val, by have hr := h_ℓ_add_R_rate; omega⟩)
        (steps := steps)
        (h_i_add_steps := by show i.val + steps < ℓ + 𝓡; omega)
        (y := y)
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) := by
    apply (sDomain_basis 𝔽q β h_ℓ_add_R_rate
      ⟨i.val, by have hr := h_ℓ_add_R_rate; omega⟩
      (by show i.val < ℓ + 𝓡; omega)).repr.injective
    ext jj
    have hjj : jj.val < ℓ + 𝓡 - i.val := jj.isLt
    -- RHS: multi-step fiber coefficient extraction
    have hRjj := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_i_add_steps := h_bound)
      (y := y)
      (k := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps)
      (j := jj)
    refine Eq.trans ?_ hRjj.symm
    -- LHS step 1: move from the lifted point at level i.val to the raw iterated
    -- quotient at level 0 + i.val
    refine Eq.trans (sDomain_repr_congr 𝔽q β _ _
      (by apply Fin.eq_of_val_eq; show i.val = 0 + i.val; omega)
      (by show i.val < ℓ + 𝓡; omega)
      (by show 0 + i.val < ℓ + 𝓡; omega)
      _
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
        (h_bound := by show 0 + i.val ≤ ℓ; omega)
        (x := v))
      (suffixLiftIdx_val 𝔽q β _ _ _ _)
      jj
      ⟨jj.val, by show jj.val < ℓ + 𝓡 - (0 + i.val); omega⟩
      rfl) ?_
    -- LHS step 2: coefficient shift of the iterated quotient map (k := i.val)
    refine Eq.trans (getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
      (h_bound := by show 0 + i.val ≤ ℓ; omega)
      (x := v)
      ⟨jj.val, by show jj.val < ℓ + 𝓡 - (0 + i.val); omega⟩) ?_
    -- Now: level-0 coefficient of v at (shifted) index = fiber_coeff ...
    by_cases h_j : jj.val < steps
    · -- masked-bit regime
      unfold fiber_coeff
      rw [dif_pos h_j]
      -- normalize the level-0 coefficient index to ⟨jj.val + i.val, _⟩
      refine Eq.trans (sDomain_repr_congr 𝔽q β _ _
        rfl
        (by show 0 < ℓ + 𝓡; omega)
        (by show 0 < ℓ + 𝓡; omega)
        _ v rfl
        _
        ⟨jj.val + i.val, by show jj.val + i.val < ℓ + 𝓡 - 0; omega⟩
        rfl) ?_
      -- identify the level-0 coefficients of v with the bits of sDomainToFin v
      have h_coeff := finToBinaryCoeffs_sDomainToFin 𝔽q β h_ℓ_add_R_rate
        (i := ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val, by show 0 < r; omega⟩)
        (h_i := by show 0 < ℓ + 𝓡; omega) (x := v)
      simp only at h_coeff
      have h_cj := congrFun h_coeff
        ⟨jj.val + i.val, by show jj.val + i.val < ℓ + 𝓡 - 0; omega⟩
      simp only [finToBinaryCoeffs] at h_cj
      rw [← h_cj]
      -- the middle-bit of the mask is the (jj + i)-th bit of v
      have h_middle :
          Nat.getBit (k := jj.val)
            (n := (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              v i steps).val) =
          Nat.getBit (k := jj.val + i.val)
            (n := (sDomainToFin 𝔽q β h_ℓ_add_R_rate
              ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val, by show 0 < r; omega⟩
              (by show 0 < ℓ + 𝓡; omega) v).val) := by
        dsimp only [extractMiddleFinMask]
        rw [Nat.getBit_of_middleBits]
        simp only [h_j, ↓reduceIte]
        rfl
      rw [h_middle]
      rcases Nat.getBit_eq_zero_or_one (k := jj.val + i.val)
        (n := (sDomainToFin 𝔽q β h_ℓ_add_R_rate
          ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val, by show 0 < r; omega⟩
          (by show 0 < ℓ + 𝓡; omega) v).val) with hb | hb
      · rw [hb]; norm_num
      · rw [hb]; norm_num
    · -- shifted-suffix regime
      unfold fiber_coeff
      rw [dif_neg h_j]
      -- normalize the level-0 coefficient index to ⟨jj.val - steps + (i.val + steps), _⟩
      refine Eq.trans (sDomain_repr_congr 𝔽q β _ _
        rfl
        (by show 0 < ℓ + 𝓡; omega)
        (by show 0 < ℓ + 𝓡; omega)
        _ v rfl
        _
        ⟨jj.val - steps + (i.val + steps), by
          show jj.val - steps + (i.val + steps) < ℓ + 𝓡 - 0; omega⟩
        (by show jj.val + i.val = jj.val - steps + (i.val + steps); omega)) ?_
      -- coefficient shift of the iterated quotient map (k := i.val + steps), reversed
      refine Eq.trans (getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val + steps)
        (h_bound := by show 0 + (i.val + steps) ≤ ℓ; omega)
        (x := v)
        ⟨jj.val - steps, by
          show jj.val - steps < ℓ + 𝓡 - (0 + (i.val + steps)); omega⟩).symm ?_
      -- transport from the (0 + (i.val + steps))-level iterate to the opaque y
      exact sDomain_repr_congr 𝔽q β _ _
        (by apply Fin.eq_of_val_eq; show 0 + (i.val + steps) = i.val + steps; omega)
        (by show 0 + (i.val + steps) < ℓ + 𝓡; omega)
        (by show i.val + steps < ℓ + 𝓡; omega)
        _ y hy.symm
        _ _ rfl
  refine Eq.trans ?_ (congrArg Subtype.val hmain)
  exact (suffixLiftIdx_val 𝔽q β _ _ _ _).symm

/-- **Iterated quotient map vs. multi-step fiber, cast form.**

This is the exact equality shape used by query-phase suffix extraction: the quotient from level
`0` to level `i` is transported from the raw `0 + i` index to the canonical `i` index, and the
deeper quotient used as the fiber base is transported in the same way. -/
lemma cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask_core
    (i steps : ℕ) (h_i_lt_ℓ : i < ℓ) (h_le : i + steps ≤ ℓ)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
        (show (⟨0 + i, by omega⟩ : Fin r) = ⟨i, by omega⟩ from
          Fin.eq_of_val_eq (Nat.zero_add i)))
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
        (h_bound := by show 0 + i ≤ ℓ; omega) (x := v)) =
    qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by
        show i + steps < ℓ + 𝓡
        have := Nat.pos_of_neZero 𝓡
        omega)
      (y := cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
          (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)))
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v ⟨i, by omega⟩ steps) := by
  apply Subtype.ext
  have hy :
      (cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
          (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v))).val =
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
        (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)).val := by
    exact val_of_cast_sDomain 𝔽q β
      (i₁ := ⟨0 + (i + steps), by omega⟩) (i₂ := ⟨i + steps, by omega⟩)
      (h := Fin.eq_of_val_eq (Nat.zero_add (i + steps)))
      (hty := congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
        (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
          Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
      (z := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
        (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v))
  have hleft :
      (cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + i, by omega⟩ : Fin r) = ⟨i, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add i)))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
          (h_bound := by show 0 + i ≤ ℓ; omega) (x := v))).val =
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
        (h_bound := by show 0 + i ≤ ℓ; omega) (x := v)).val := by
    exact val_of_cast_sDomain 𝔽q β
      (i₁ := ⟨0 + i, by omega⟩) (i₂ := ⟨i, by omega⟩)
      (h := Fin.eq_of_val_eq (Nat.zero_add i))
      (hty := congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
        (show (⟨0 + i, by omega⟩ : Fin r) = ⟨i, by omega⟩ from
          Fin.eq_of_val_eq (Nat.zero_add i)))
      (z := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
        (h_bound := by show 0 + i ≤ ℓ; omega) (x := v))
  exact hleft.trans
    (iteratedQuotientMap_val_eq_qMap_total_fiber_extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, h_i_lt_ℓ⟩) (steps := steps)
      (h_bound := h_le) (v := v)
      (y := cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
          (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)))
      hy)

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

/-- Number of oracle blocks at the end of the protocol. -/
abbrev nBlocks : ℕ := toOutCodewordsCount ℓ ϑ (Fin.last ℓ)

/-- Extract suffix starting at position `destIdx` from a full challenge. -/
def extractSuffixFromChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ) :
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  have h_bound : (⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val + destIdx.val ≤ ℓ := by
    change 0 + destIdx.val ≤ ℓ
    rw [Nat.zero_add]; exact h_destIdx_le
  have h_idx_eq :
      (⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val + destIdx.val, by omega⟩ : Fin r) =
        destIdx := by
    apply Fin.eq_of_val_eq
    change 0 + destIdx.val = destIdx.val
    rw [Nat.zero_add]
  cast (congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx_eq)
    (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
      (k := destIdx.val) (h_bound := h_bound) (x := v))

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
/-- Congruence lemma for challenge suffixes across equal destination indices. -/
lemma extractSuffixFromChallenge_congr_destIdx
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    {destIdx destIdx' : Fin r}
    (h_idx_eq : destIdx = destIdx')
    (h_le : destIdx ≤ ℓ)
    (h_le' : destIdx' ≤ ℓ) :
    extractSuffixFromChallenge 𝔽q β v destIdx h_le =
    cast (by rw [h_idx_eq]) (extractSuffixFromChallenge 𝔽q β v destIdx' h_le') := by
  subst h_idx_eq
  rw [cast_eq]

def getChallengeSuffix (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    let i := k.val * ϑ
    have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    let destIdx : Fin r := ⟨i + ϑ, by omega⟩
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  have h_i_add_ϑ_le_ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by omega)

def challengeSuffixToFin (k : Fin (ℓ / ϑ))
    (suffix : sDomain 𝔽q β h_ℓ_add_R_rate ⟨k.val * ϑ + ϑ, by
    have := k_succ_mul_ϑ_le_ℓ_₂ (k := k); omega⟩) : Fin (2 ^ (ℓ + 𝓡 - (k.val * ϑ + ϑ))) :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  sDomainToFin 𝔽q β h_ℓ_add_R_rate (i := ⟨k.val * ϑ + ϑ, by omega⟩) (h_i := by
    simp only [k_succ_mul_ϑ_le_ℓ_₂, Nat.lt_add_of_pos_right_of_le]) suffix

/-- Return the point `f^(i)(u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})`
for a fiber index `u ∈ B_ϑ`. -/
noncomputable def getFiberPoint
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) (u : Fin (2 ^ ϑ)) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
      (positionIdx := ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩),
        lt_r_of_lt_ℓ (x := k.val * ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := k_mul_ϑ_lt_ℓ (k := k))⟩) :=
  by
    exact
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
        (steps := ϑ)
        (h_i_add_steps := by
          have h_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
          simp only [Fin.val_mk]; omega)
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v))
        u

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
  unfold getFiberPoint
  simp only [oraclePositionToDomainIndex, id_eq]

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
          (i := ⟨j.val * ϑ, k_mul_ϑ_lt_ℓ (k := j)⟩)
          (steps := ϑ)) := by
  rw [getFiberPoint_eq_qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j v]
  exact cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask_core 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := j.val * ϑ) (steps := ϑ)
    (h_i_lt_ℓ := k_mul_ϑ_lt_ℓ (k := j))
    (h_le := k_succ_mul_ϑ_le_ℓ_₂ (k := j))
    (v := v)

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
  (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v:=v) (i:=i) (steps:=steps),
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v:=v)
      (destIdx:=destIdx) (h_destIdx_le:=h_destIdx_le))

-- Future work: KEY LEMMA for connecting fiber queries to challenge decomposition
-- Future work: Lemma connecting queryFiberPoints to extractMiddleFinMask

def queryRbrKnowledgeError_singleRepetition := ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡))

/-- RBR knowledge error for the query phase.
Proximity testing error rate: `(1/2 + 1/(2 * 2^𝓡))^γ` -/
def queryRbrKnowledgeError := fun _ : (pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx =>
  (queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡))^γ_repetitions

/-- Oracle query helper: query a committed codeword at a given domain point.
    Restricted to codeword indices where the oracle range is L. -/
def queryCodeword (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (point : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩) :
  OptionT (OracleComp ([]ₒ +
    ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ( Fin.last ℓ)]ₒ +
    [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L :=
    query (spec := [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ)
      ⟨⟨j, by omega⟩, point⟩

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

/-- Query all fiber points for a given folding step.
    Returns a list of evaluations `f^(i)(u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})`
    for all `u ∈ B_ϑ`.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context. -/
noncomputable def queryFiberPoints
    (k : Fin (ℓ / ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
  OptionT
        (OracleComp
          ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
            [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ)))
        (Vector L (2^ϑ)) := do
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
      Fin.is_lt]⟩
  -- 2. Map over the Vector monadically
  let results : Vector L (2^ϑ) ← (⟨Array.finRange (2^ϑ), by simp only [Array.size_finRange]⟩
    : Vector (Fin (2^ϑ)) (2^ϑ)).mapM (fun (u : Fin (2^ϑ)) => do
    queryCodeword 𝔽q β (γ_repetitions := γ_repetitions) (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (j := k_th_oracleIdx) (point :=
        getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v) (u := u))
  )
  pure results

/-- Check a single folding step: query fiber points, verify consistency, and compute next value.
    Returns `(c_next, all_checks_passed)` where `c_next` is the computed folded value
    and `all_checks_passed` indicates if all consistency checks passed.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context. -/
noncomputable def checkSingleFoldingStep
    (k_val : Fin (ℓ / ϑ)) (c_cur : L) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    OptionT (OracleComp ([]ₒ + ([OracleStatement 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ + [(pSpecQuery 𝔽q β
      γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L := do
  let i := k_val.val * ϑ
  have h_k: k_val ≤ (ℓ/ϑ - 1) := by omega
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := by
    calc i + ϑ = k_val * ϑ + ϑ := by omega
      _ ≤ (ℓ/ϑ - 1) * ϑ + ϑ := by
        apply Nat.add_le_add_right; apply Nat.mul_le_mul_right; omega
      _ = ℓ/ϑ * ϑ := by
        rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel];
        conv_lhs => rw [←one_mul ϑ]
        apply Nat.mul_le_mul_right; omega
      _ ≤ ℓ := by apply Nat.div_mul_le_self;
  have h_i_lt_ℓ : i < ℓ := by
    calc i ≤ ℓ - ϑ := by omega
      _ < ℓ := by
        apply Nat.sub_lt (by exact Nat.pos_of_neZero ℓ) (by exact Nat.pos_of_neZero ϑ)
  let f_i_on_fiber ← queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k_val v
  -- Check consistency if i > 0
  if h_i_pos : i > 0 then
    let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v:=v) (i:=⟨i, by omega⟩) (steps:=ϑ)
    let f_i_val := f_i_on_fiber.get oracle_point_idx
    guard (c_cur = f_i_val)
  -- Compute next folded value
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  let next_suffix_of_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
    getChallengeSuffix (k := k_val) (v := v)
  let cur_challenge_batch : Fin ϑ → L := fun j =>
    foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmt.challenges
      ⟨i + j.val, by simp only [Fin.val_last]; omega⟩
  -- c_next = folded value at step k (logical counterpart: `logical_computeFoldedValue`)
  let c_next : L := single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i:=⟨i, by omega⟩) (steps:=ϑ) (destIdx:=destIdx) (h_destIdx:=by dsimp only [destIdx])
    (h_destIdx_le:=by omega) (r_challenges:=cur_challenge_batch) (y:=next_suffix_of_v)
    (fiber_eval_mapping := f_i_on_fiber.get)
  return c_next

/-- Check a single repetition: iterate through all folding steps and verify final consistency.
    Returns `true` if all checks pass, `false` otherwise.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context.
    Uses `mut` + `for` loop for true early termination (stops immediately on first failure).
    For proofs, we'll need to reason about the loop invariant that `c_cur` maintains the
    correct accumulated value through iterations. -/
noncomputable def checkSingleRepetition
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) :
    OptionT (OracleComp ([]ₒ + ([OracleStatement 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ + [(pSpecQuery 𝔽q β
      γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) Unit := do
  let mut c_cur : L := 0 -- Will be initialized in first iteration
  -- Iterate through the `ℓ/ϑ` adjacent pairs of oracles & validate local folding consistency
  -- Early termination: stops immediately on first failure via `return false`
  for k_val in List.finRange (ℓ / ϑ) do
    let c_next ← checkSingleFoldingStep 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (γ_repetitions := γ_repetitions)
        ⟨k_val, by omega⟩ c_cur v stmt
    c_cur := c_next
  -- Final check: c_ℓ ?= final_constant
  guard (c_cur = final_constant)

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
- `checkSingleFoldingStep` ↔ `logical_checkSingleFoldingStep` + `logical_computeFoldedValue`
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

/-- Compute folded value at step `k` (same as `c_next` in monadic `checkSingleFoldingStep`).
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

/-- Check a single folding step at k (logical; mirrors monadic `checkSingleFoldingStep`).

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
      (v := v) (i := ⟨i, k_mul_ϑ_lt_ℓ (k := k)⟩) (steps := ϑ)
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

/-- Check a single repetition (logical; mirrors monadic `checkSingleRepetition`).
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

section QueryPhaseFirstOracle

/-!
## First-oracle query bounds.
-/

/-!
## Binary Basefold Query-Phase First-Oracle Alignment

This module keeps the zero-step first-oracle consequence of
`strictOracleFoldingConsistencyProp` separate from the core query-phase preliminaries.
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
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [hdiv : Fact (ϑ ∣ ℓ)]

namespace QueryPhase

private lemma iterated_fold_congr_steps_fun
    (i : Fin r) {destIdx : Fin r} {s₁ s₂ : ℕ} (h : s₁ = s₂)
    (hd₁ : destIdx.val = i.val + s₁) (hd₂ : destIdx.val = i.val + s₂)
    (h_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (c : Fin s₁ → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s₂)
      (destIdx := destIdx) (h_destIdx := hd₂) (h_destIdx_le := h_le) f
      (fun j => c (Fin.cast h.symm j)) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s₁)
      (destIdx := destIdx) (h_destIdx := hd₁) (h_destIdx_le := h_le) f c := by
  subst h
  rfl

private lemma iterated_fold_zero_steps_fun
    (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin 0 → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
      (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := r_challenges) =
    fun y => f (Eq.mp (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type))
      (Fin.eq_of_val_eq h_destIdx)) y) := by
  funext y
  exact iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f := f) (r_challenges := r_challenges) y

private lemma getFirstOracle_apply_zero {i : Fin (ℓ + 1)}
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    getFirstOracle 𝔽q β oStmt y =
      oStmt ⟨0, (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos⟩
        ⟨y.val, by simpa only [Fin.val_mk, zero_mul, Nat.zero_mod] using y.property⟩ := by
  unfold getFirstOracle
  rfl

set_option maxHeartbeats 2000000 in
-- The final equality crosses two dependent `sDomain` transports introduced by `getFirstOracle`
-- and the zero-step fold; the extra budget keeps the proof local to this bridge lemma.
/-- **First Oracle Equals Polynomial Oracle Function**:
When `strictOracleFoldingConsistencyProp` holds, the first oracle (`getFirstOracle`) equals
the polynomial oracle function `f₀` derived from the multilinear polynomial `t`.
This follows from the consistency property for `j = 0`, where `iterated_fold` with 0 steps
is the identity function. -/
lemma polyToOracleFunc_eq_getFirstOracle
    (t : MultilinearPoly L ℓ)
    (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j)
    (h_consistency : strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := i)
      (challenges := challenges) (oStmt := oStmt)) :
    let P₀ : Polynomial.degreeLT L (2 ^ ℓ) :=
      polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
        (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    f₀ = getFirstOracle 𝔽q β oStmt := by
  intro P₀ f₀
  let h_pos : 0 < toOutCodewordsCount ℓ ϑ i :=
    (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos
  have h_first_oracle := h_consistency ⟨0, h_pos⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_first_oracle
  dsimp only [f₀, P₀] at h_first_oracle ⊢
  simp only [id_eq] at h_first_oracle ⊢
  funext y
  rw [getFirstOracle_apply_zero 𝔽q β oStmt y]
  let j0 : Fin (toOutCodewordsCount ℓ ϑ i) := ⟨0, h_pos⟩
  let firstIdx : Fin r := ⟨j0.val * ϑ, by
    simp only [j0, Fin.val_mk, zero_mul]
    exact Nat.lt_trans (Nat.pos_of_neZero ℓ) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩
  have h_firstIdx_zero : firstIdx = (0 : Fin r) := by
    apply Fin.ext
    simp only [firstIdx, j0, Fin.val_mk, zero_mul, Fin.val_zero]
  let y0 : sDomain 𝔽q β h_ℓ_add_R_rate firstIdx :=
    ⟨y.val, h_firstIdx_zero.symm ▸ y.property⟩
  change f₀ y = oStmt ⟨0, h_pos⟩ y0
  rw [h_first_oracle]
  -- The three side conditions below are stated against whatever normal form the
  -- `strictOracleFoldingConsistencyProp` instance currently exposes (`↑⟨0, _⟩ * ϑ` vs `0 * ϑ`
  -- vs `0`); sibling refactors keep shifting that normal form, so each proof is a `first`
  -- ladder over the defeq-equivalent shapes instead of a single brittle `simp only`.
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps' := 0)
      (h_destIdx := by
        first
          | (simp only [Fin.val_mk, zero_mul, Fin.val_zero, add_zero]; rfl)
          | (simp only [Fin.val_mk, zero_mul, Fin.val_zero, add_zero])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, Fin.val_zero, zero_mul,
              add_zero, zero_add])
          | rfl
          | omega)
      (h_destIdx_le := by
        first
          | (simp only [zero_mul, zero_le])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, zero_mul, zero_le])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, zero_mul];
              exact Nat.zero_le _)
          | exact Nat.zero_le _
          | simp)
      (h_steps_eq_steps' := by
        first
          | (simp only [zero_mul])
          | (simp only [Fin.val_mk, zero_mul])
          | exact Nat.zero_mul _
          | simp)]
  rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (h_destIdx := by
        first
          | (simp only [firstIdx, j0, Fin.val_mk, zero_mul, Fin.val_zero])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, Fin.val_zero, zero_mul])
          | rfl
          | simp)]
  have h_y0_to_y :
      (cast (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type))
        h_firstIdx_zero) y0) = y := by
    apply Subtype.ext
    exact (val_of_cast_sDomain 𝔽q β firstIdx (0 : Fin r) h_firstIdx_zero
      (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type)) h_firstIdx_zero)
      y0).trans rfl
  simp only [polyToOracleFunc]
  change P₀.val.eval y.val =
    P₀.val.eval (cast (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type))
      h_firstIdx_zero) y0).val
  rw [h_y0_to_y]

end QueryPhase

end

end Binius.BinaryBasefold

end QueryPhaseFirstOracle

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
        getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
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
    (getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        stmt.challenges (k := k.val * ϑ) (h := k_succ_mul_ϑ_le_ℓ_₂ (k := k)))
    (getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v))
  -- The only congruence residue is the challenge-batch slot: `logical_computeFoldedValue`
  -- writes it as a `foldOrderChallenges` lambda while the bridge lemma packages the same
  -- function as `getFoldingChallenges`; they agree definitionally (delta + proof irrelevance).
  all_goals
    first
      | rfl
      | (simp only [getFoldingChallenges, foldOrderChallenges])
      | (funext cId; simp only [getFoldingChallenges, foldOrderChallenges])
      | (simp [getFoldingChallenges, foldOrderChallenges])

end QueryPhase

end

end Binius.BinaryBasefold

end QueryPhaseFoldedValue
