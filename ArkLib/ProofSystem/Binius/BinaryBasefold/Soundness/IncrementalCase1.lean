/-
Issue #317 — Proposition 4.21.2 case-1 content, proven against the honest per-fiber
disagreement surface (`fiberwiseDisagreementSetPerFiber`).

Brick A: `qMap_total_fiber_succ_peel_first` — bottom-peel analogue of
`qMap_total_fiber_succ_peel_last` (LSB selects the first quotient level).

Brick B: `prop_4_21_2_case_1_residual_holds` — the per-quotient-point
Schwartz–Zippel bound (degree ≤ 1 fold difference, butterfly-matrix
non-degeneracy) summed by a union bound over the disagreement set.
-/
import ArkLib.Data.CodingTheory.ProximityGap.DG25
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.IncrementalHelpers
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.BaseFoldDetBrick
import CompPoly.Fields.Binary.Tower.Prelude

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false

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

noncomputable section

/-! ### Brick A: bottom-peel of the iterated quotient fiber -/

/-- Transport of `sDomain_basis` coefficients across a propositional equality of the
(ℕ-level) domain index. Both sides are the same data up to proof irrelevance + eta. -/
lemma sDomain_repr_coeff_transport {a b : ℕ} (hab : a = b)
    (ha : a < ℓ + 𝓡) (hb : b < ℓ + 𝓡) (har : a < r) (hbr : b < r)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨a, har⟩)
    (xb : sDomain 𝔽q β h_ℓ_add_R_rate ⟨b, hbr⟩)
    (hx : x.val = xb.val)
    (ma : Fin (ℓ + 𝓡 - a)) (mb : Fin (ℓ + 𝓡 - b)) (hm : ma.val = mb.val) :
    (sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨a, har⟩ ha).repr x ma
      = (sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨b, hbr⟩ hb).repr xb mb := by
  subst hab
  obtain rfl : x = xb := Subtype.ext hx
  obtain rfl : ma = mb := Fin.ext hm
  rfl

/-- Bit shift: for `1 ≤ j`, bit `j` of `nn` is bit `j - 1` of `nn / 2`. -/
lemma getBit_eq_getBit_pred_div_two {j nn : ℕ} (hj : 1 ≤ j) :
    Nat.getBit j nn = Nat.getBit (j - 1) (nn / 2) := by
  unfold Nat.getBit
  rw [← Nat.shiftRight_one, ← Nat.shiftRight_add]
  congr 2
  omega

/-- Bit 0 of `nn % 2` is bit 0 of `nn`. -/
lemma getBit_zero_mod_two {nn : ℕ} :
    Nat.getBit 0 (nn % 2) = Nat.getBit 0 nn := by
  unfold Nat.getBit
  simp only [Nat.shiftRight_zero, Nat.and_one_is_mod]
  omega

/-- **Fiber composition (first level peeled).**
The `(n+1)`-step fiber of `y' ∈ S^(i+(n+1))` at index `idx`, with `idx` split into the
low bit `idx % 2` (selecting the FIRST quotient `q^(i)`) and the high `n` bits
`idx / 2`, equals the single-step fiber (at level `i`) of the `n`-step preimage
`w := qMap_total_fiber(i+1, n, y')(idx / 2)` at index `idx % 2`. Bottom-peel analogue
of `qMap_total_fiber_succ_peel_last`, matching the LSB = first-quotient convention of
`qMap_total_fiber`. -/
lemma qMap_total_fiber_succ_peel_first (i : Fin ℓ) (n : ℕ)
    (h_i_add_steps : i.val + (n + 1) ≤ ℓ)
    (y' : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + (n + 1), by omega⟩))
    (idx : Fin (2 ^ (n + 1))) :
    qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := n + 1)
      (h_i_add_steps := by
        simp only; exact fin_ℓ_steps_lt_ℓ_add_R i (n + 1) h_i_add_steps)
      (y := y') idx =
    qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
      (h_i_add_steps := by
        simp only; exact fin_ℓ_steps_lt_ℓ_add_R i 1 (by omega))
      (y := qMap_total_fiber 𝔽q β (i := ⟨i.val + 1, by omega⟩) (steps := n)
        (h_i_add_steps := by
          simp only
          have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
          omega)
        (y := ⟨y'.val, by
          have := y'.property
          simpa only [Nat.add_assoc, Nat.add_comm 1 n] using this⟩)
        ⟨idx.val / 2, by
          have hb : idx.val < 2 * 2 ^ n :=
            Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm])
          omega⟩)
      ⟨idx.val % 2, by
        have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
        rw [h2]
        exact Nat.mod_lt _ (by norm_num)⟩ := by
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
  -- Abbreviations for the split index.
  set bLow : Fin (2 ^ 1) := ⟨idx.val % 2, by
    have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h2]; exact Nat.mod_lt _ (by norm_num)⟩ with hbLow_def
  set cHigh : Fin (2 ^ n) := ⟨idx.val / 2, by
    have hb : idx.val < 2 * 2 ^ n :=
      Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm])
    omega⟩ with hcHigh_def
  -- The lifted point at level (i+1)+n.
  set y'_lift : sDomain 𝔽q β h_ℓ_add_R_rate
      (i := ⟨(⟨i.val + 1, by omega⟩ : Fin r).val + n, by simp only; omega⟩) :=
    ⟨y'.val, by
      have := y'.property
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using this⟩ with hy'_lift_def
  -- Both sides are points of S^i; compare basis coefficients via repr injectivity.
  apply (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (by simp only; omega)).repr.injective
  ext j
  have hjlt : j.val < ℓ + 𝓡 - i.val := j.isLt
  -- LHS coefficient via the (n+1)-step extraction lemma.
  have hL := qMap_total_fiber_repr_coeff 𝔽q β i (steps := n + 1) h_i_add_steps y' idx (j := j)
  -- RHS coefficient via the 1-step extraction lemma over w.
  set w := qMap_total_fiber 𝔽q β (i := ⟨i.val + 1, by omega⟩) (steps := n)
    (h_i_add_steps := by simp only; omega)
    (y := y'_lift) cHigh with hw_def
  have hR := qMap_total_fiber_repr_coeff 𝔽q β i (steps := 1) (by omega) w bLow (j := j)
  simp only at hL hR ⊢
  rw [hL, hR]
  unfold fiber_coeff
  by_cases hj0 : j.val < 1
  · -- Low bit: both read bit 0 of idx.
    have hjn1 : j.val < n + 1 := by omega
    simp only [hj0, hjn1, ↓reduceDIte]
    have hj_eq : j.val = 0 := by omega
    rw [hj_eq, hbLow_def]
    simp only
    rw [getBit_zero_mod_two]
  · by_cases hj_mid : j.val < n + 1
    · -- Middle region: LHS reads bit j of idx; RHS reads bit (j-1) of idx/2 through w.
      simp only [hj0, hj_mid, ↓reduceDIte]
      -- Compute w's (j-1)-th coefficient via the n-step extraction at level i+1.
      have hi1ℓ : i.val + 1 < ℓ := by omega
      have hW := qMap_total_fiber_repr_coeff 𝔽q β (⟨i.val + 1, hi1ℓ⟩ : Fin ℓ)
        (steps := n) (by simp only; omega) y'_lift cHigh
        (j := ⟨j.val - 1, by simp only; omega⟩)
      simp only at hW
      rw [hW]
      unfold fiber_coeff
      have hj_sub : j.val - 1 < n := by omega
      simp only [hj_sub, ↓reduceDIte]
      rw [hcHigh_def]
      simp only
      rw [getBit_eq_getBit_pred_div_two (by omega : 1 ≤ j.val)]
    · -- High region: both read y''s shifted coefficients.
      simp only [hj0, hj_mid, ↓reduceDIte]
      by_cases hn0 : n = 0
      · -- n = 0: w is the 0-step fiber of y'_lift, i.e. y'_lift itself.
        subst hn0
        -- w's coefficients are y'_lift's coefficients (and the index shifts agree).
        have hW : (sDomain_basis 𝔽q β h_ℓ_add_R_rate
            (i := ⟨i.val + 1, by omega⟩) (by simp only; omega)).repr w
            ⟨j.val - 1, show j.val - 1 < ℓ + 𝓡 - (i.val + 1) by omega⟩
            = (sDomain_basis 𝔽q β h_ℓ_add_R_rate
            (i := ⟨i.val + 1, by omega⟩) (by simp only; omega)).repr y'_lift
            ⟨j.val - 1, show j.val - 1 < ℓ + 𝓡 - (i.val + 1) by omega⟩ := rfl
        rw [hW]
      · -- n ≥ 1: use the n-step extraction at level i+1 in its high region.
        have hi1ℓ' : i.val + 1 < ℓ := by omega
        have hW := qMap_total_fiber_repr_coeff 𝔽q β (⟨i.val + 1, hi1ℓ'⟩ : Fin ℓ)
          (steps := n) (by simp only; omega) y'_lift cHigh
          (j := ⟨j.val - 1, show j.val - 1 < ℓ + 𝓡 - (i.val + 1) by omega⟩)
        simp only at hW
        rw [hW]
        unfold fiber_coeff
        have hj_sub : ¬ (j.val - 1 < n) := by omega
        simp only [hj_sub, ↓reduceDIte]
        exact sDomain_repr_coeff_transport 𝔽q β
          (a := i.val + (n + 1)) (b := i.val + 1 + n)
          (by omega) (by omega) (by omega) (by omega) (by omega) y' y'_lift rfl
          (ma := ⟨j.val - (n + 1),
            show j.val - (n + 1) < ℓ + 𝓡 - (i.val + (n + 1)) by omega⟩)
          (mb := ⟨j.val - 1 - n,
            show j.val - 1 - n < ℓ + 𝓡 - (i.val + 1 + n) by omega⟩)
          (show j.val - (n + 1) = j.val - 1 - n by omega)

/-! ### Congruence helpers (transport across propositionally-equal step counts) -/

/-- `fiberEvaluations` congruence in the step count. -/
lemma fiberEvaluations_congr_steps (i : Fin r) {destIdx : Fin r} {s₁ s₂ : ℕ} (h : s₁ = s₂)
    (hd₁ : destIdx.val = i.val + s₁) (hd₂ : destIdx.val = i.val + s₂) (h_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) (idx : Fin (2 ^ s₁)) :
    fiberEvaluations 𝔽q β (i := i) (steps := s₁) (destIdx := destIdx) hd₁ h_le f y idx =
    fiberEvaluations 𝔽q β (i := i) (steps := s₂) (destIdx := destIdx) hd₂ h_le f y
      (Fin.cast (congrArg (fun s => 2 ^ s) h) idx) := by
  subst h
  rfl

/-- `iterated_fold` congruence in the step count (with the challenge re-indexing
appearing in the `k = ϑ` branch of `incrementalFoldingBadEvent`). -/
lemma iterated_fold_congr_steps (i : Fin r) {destIdx : Fin r} {s₁ s₂ : ℕ} (h : s₁ = s₂)
    (hd₁ : destIdx.val = i.val + s₁) (hd₂ : destIdx.val = i.val + s₂) (h_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) (c : Fin s₁ → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s₂)
      (destIdx := destIdx) (h_destIdx := hd₂) (h_destIdx_le := h_le) f
      (fun j => c (Fin.cast h.symm j)) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s₁)
      (destIdx := destIdx) (h_destIdx := hd₁) (h_destIdx_le := h_le) f c := by
  subst h
  rfl

/-- **Per-fiber bottom peel at the `fiberEvaluations` level.**
The `(n+1)`-step fiber evaluation of `f` over `y` at `idx` is the single-step fiber
evaluation at the `n`-step intermediate fiber point `w` (over `midSucc`), at the low
bit `idx % 2`. -/
lemma fiberEvaluations_peel_first (midIdx : Fin r) {midSucc destIdx : Fin r} (n : ℕ)
    (h_ms : midSucc.val = midIdx.val + 1) (h_ms_le : midSucc ≤ ℓ)
    (h_dest : destIdx.val = midIdx.val + (n + 1)) (h_dest_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) (idx : Fin (2 ^ (n + 1))) :
    fiberEvaluations 𝔽q β (i := midIdx) (steps := n + 1) (destIdx := destIdx)
      h_dest h_dest_le f y idx =
    fiberEvaluations 𝔽q β (i := midIdx) (steps := 1) (destIdx := midSucc)
      h_ms h_ms_le f
      (qMap_total_fiber 𝔽q β (i := midSucc) (steps := n)
        (h_i_add_steps := by
          have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
          omega)
        (y := ⟨y.val, by
          have hidx : (⟨midSucc.val + n, by omega⟩ : Fin r) = destIdx :=
            Fin.eq_of_val_eq (show midSucc.val + n = destIdx.val by omega)
          rw [hidx]
          exact y.property⟩)
        ⟨idx.val / 2, by
          have h1 : idx.val < 2 ^ (n + 1) := idx.isLt
          have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
          omega⟩)
      ⟨idx.val % 2, by
        have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
        omega⟩ := by
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
  have h_bound_ms : midIdx.val + 1 < r := by omega
  have h_eq_ms : midSucc = ⟨midIdx.val + 1, h_bound_ms⟩ := Fin.eq_of_val_eq h_ms
  subst h_eq_ms
  have h_bound_dest : midIdx.val + (n + 1) < r := by omega
  have h_eq_dest : destIdx = ⟨midIdx.val + (n + 1), h_bound_dest⟩ := Fin.eq_of_val_eq h_dest
  subst h_eq_dest
  have h_dest_le' : midIdx.val + (n + 1) ≤ ℓ := h_dest_le
  have h_mid_lt_ℓ : midIdx.val < ℓ := by omega
  unfold fiberEvaluations
  exact congrArg f (qMap_total_fiber_succ_peel_first 𝔽q β ⟨midIdx.val, h_mid_lt_ℓ⟩ n
    (by omega)
    (y' := ⟨y.val, by exact y.property⟩) idx)

/-- Membership in the same-index `disagreementSet` is plain pointwise disagreement. -/
lemma mem_disagreementSet_self {dIdx : Fin r}
    (F G : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) dIdx)
    (z : sDomain 𝔽q β h_ℓ_add_R_rate dIdx) :
    z ∈ disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := dIdx)
      (destIdx := dIdx) (h_destIdx := rfl) F G ↔ F z ≠ G z := by
  unfold disagreementSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]

/-! ### The Schwartz–Zippel core: at most one bad challenge per quotient point -/

/-- **Per-point Schwartz–Zippel bound.** If `g, g'` disagree somewhere on the single-step
fiber of `w`, then the single-step folds of `g` and `g'` agree at `w` for at most one
challenge value: the fold difference is an affine polynomial `a + c·r` in the challenge
with `(a, c) ≠ (0, 0)` by invertibility of the butterfly matrix
(`det = x₁ - x₀ = basis_x 0 ≠ 0`). -/
lemma card_filter_fold_eq_le_one (midIdx : Fin r) {midSucc : Fin r}
    (h_ms : midSucc.val = midIdx.val + 1) (h_ms_le : midSucc ≤ ℓ)
    (g g' : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx)
    (w : sDomain 𝔽q β h_ℓ_add_R_rate midSucc)
    (h_dis : ∃ b : Fin (2 ^ 1),
      fiberEvaluations 𝔽q β (i := midIdx) (steps := 1) (destIdx := midSucc)
        h_ms h_ms_le g w b ≠
      fiberEvaluations 𝔽q β (i := midIdx) (steps := 1) (destIdx := midSucc)
        h_ms h_ms_le g' w b) :
    (Finset.univ.filter (fun r_new : L =>
      fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := midSucc)
        h_ms h_ms_le g r_new w =
      fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := midSucc)
        h_ms h_ms_le g' r_new w)).card ≤ 1 := by
  classical
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
  have h_bound : midIdx.val + 1 < r := by omega
  have h_eq : midSucc = ⟨midIdx.val + 1, h_bound⟩ := Fin.eq_of_val_eq h_ms
  subst h_eq
  have h_le' : midIdx.val + 1 ≤ ℓ := h_ms_le
  have h_i : midIdx.val + 1 < ℓ + 𝓡 := by omega
  -- Fiber points and their separation.
  set fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
    (h_i_add_steps := h_i) (y := w) with hfiberMap_def
  set x₀ := fiberMap 0 with hx₀_def
  set x₁ := fiberMap 1 with hx₁_def
  set Δ₀ := g x₀ - g' x₀ with hΔ₀_def
  set Δ₁ := g x₁ - g' x₁ with hΔ₁_def
  -- (Δ₀, Δ₁) ≠ (0, 0) from the fiber disagreement.
  have h_Δ_ne_zero : Δ₀ ≠ 0 ∨ Δ₁ ≠ 0 := by
    obtain ⟨b, hb⟩ := h_dis
    have hb' : g (fiberMap b) ≠ g' (fiberMap b) := hb
    have hb01 : b.val = 0 ∨ b.val = 1 := by
      have := b.isLt
      have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
      omega
    rcases hb01 with h0 | h1
    · left
      have hbeq : b = (0 : Fin (2 ^ 1)) := Fin.ext (by simpa using h0)
      rw [hbeq] at hb'
      exact sub_ne_zero.mpr hb'
    · right
      have hbeq : b = (1 : Fin (2 ^ 1)) := Fin.ext (by simpa using h1)
      rw [hbeq] at hb'
      exact sub_ne_zero.mpr hb'
  -- Fiber separation: x₁ - x₀ = basis_x 0 ≠ 0, hence x₀.val ≠ x₁.val in L.
  have h_x₀_ne_x₁ : (x₀ : L) ≠ (x₁ : L) := by
    have hsub := qMap_total_fiber_one_sub 𝔽q β midIdx h_i h_le' w
    have h_basis_ne : (sDomain_basis 𝔽q β h_ℓ_add_R_rate midIdx (by omega)
        ⟨0, by omega⟩ : sDomain 𝔽q β h_ℓ_add_R_rate midIdx) ≠ 0 :=
      (sDomain_basis 𝔽q β h_ℓ_add_R_rate midIdx (by omega)).ne_zero _
    intro hcontra
    apply h_basis_ne
    rw [← hsub]
    rw [← hx₀_def, ← hx₁_def] at *
    exact sub_eq_zero.mpr (Subtype.ext hcontra.symm)
  -- The fold difference at w is the affine polynomial in the challenge.
  have h_fold_diff : ∀ rc : L,
      fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx)
        (destIdx := ⟨midIdx.val + 1, h_bound⟩) h_ms h_ms_le g rc w -
      fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx)
        (destIdx := ⟨midIdx.val + 1, h_bound⟩) h_ms h_ms_le g' rc w
      = Δ₀ * ((1 - rc) * (x₁ : L) - rc) + Δ₁ * (rc - (1 - rc) * (x₀ : L)) := by
    intro rc
    show (g x₀ * ((1 - rc) * (x₁ : L) - rc) + g x₁ * (rc - (1 - rc) * (x₀ : L)))
      - (g' x₀ * ((1 - rc) * (x₁ : L) - rc) + g' x₁ * (rc - (1 - rc) * (x₀ : L)))
      = Δ₀ * ((1 - rc) * (x₁ : L) - rc) + Δ₁ * (rc - (1 - rc) * (x₀ : L))
    rw [hΔ₀_def, hΔ₁_def]
    ring
  -- Char-2 rewrite of the polynomial: P(r) = (Δ₀x₁ + Δ₁x₀) + r·(Δ₀(x₁+1) + Δ₁(x₀+1)).
  have h_poly_char2 : ∀ r_val : L,
      Δ₀ * ((1 - r_val) * (x₁ : L) - r_val) + Δ₁ * (r_val - (1 - r_val) * (x₀ : L)) =
      (Δ₀ * (x₁ : L) + Δ₁ * (x₀ : L)) +
      r_val * (Δ₀ * ((x₁ : L) + 1) + Δ₁ * ((x₀ : L) + 1)) := by
    intro r_val
    simp only [CharTwo.sub_eq_add]
    ring
  have char2_add_zero : ∀ (u v : L), u + v = 0 ↔ u = v :=
    sum_zero_iff_eq_of_self_sum_zero (F := L) (h_self_sum_eq_zero := by
      intro x; exact CharTwo.add_self_eq_zero x)
  -- The affine polynomial has at most one root.
  have h_at_most_one_root : ∀ r₁ r₂ : L,
      (Δ₀ * ((1 - r₁) * (x₁ : L) - r₁) + Δ₁ * (r₁ - (1 - r₁) * (x₀ : L)) = 0) →
      (Δ₀ * ((1 - r₂) * (x₁ : L) - r₂) + Δ₁ * (r₂ - (1 - r₂) * (x₀ : L)) = 0) →
      r₁ = r₂ := by
    intro r₁ r₂ h1 h2
    rw [h_poly_char2] at h1 h2
    have h_sub : (r₁ + r₂) * (Δ₀ * ((x₁ : L) + 1) + Δ₁ * ((x₀ : L) + 1)) = 0 := by
      have h1' := (char2_add_zero _ _).mp h1
      have h2' := (char2_add_zero _ _).mp h2
      rw [add_mul, ← h1', ← h2', CharTwo.add_self_eq_zero]
    rcases mul_eq_zero.mp h_sub with h_diff | h_coeff
    · exact (char2_add_zero r₁ r₂).mp h_diff
    · exfalso
      have h_a_eq_0 : Δ₀ * (x₁ : L) + Δ₁ * (x₀ : L) = 0 := by
        rw [h_coeff, mul_zero, add_zero] at h1; exact h1
      have h_Δ_eq : Δ₀ = Δ₁ := by
        have hc : Δ₀ * ((x₁ : L) + 1) + Δ₁ * ((x₀ : L) + 1) =
          (Δ₀ * (x₁ : L) + Δ₁ * (x₀ : L)) + (Δ₀ + Δ₁) := by ring
        rw [h_a_eq_0, zero_add] at hc
        rw [hc] at h_coeff
        exact (char2_add_zero Δ₀ Δ₁).mp h_coeff
      have h_Δ₀_mul : Δ₀ * ((x₁ : L) + (x₀ : L)) = 0 := by
        have : Δ₀ * (x₁ : L) + Δ₀ * (x₀ : L) = 0 := h_Δ_eq ▸ h_a_eq_0
        rwa [← mul_add] at this
      have h_sum_ne : (x₁ : L) + (x₀ : L) ≠ 0 := by
        rwa [Ne, ← CharTwo.sub_eq_add, sub_eq_zero, eq_comm]
      have h_Δ₀_zero := (mul_eq_zero.mp h_Δ₀_mul).resolve_right h_sum_ne
      exact h_Δ_ne_zero.elim (absurd h_Δ₀_zero) (absurd (h_Δ_eq ▸ h_Δ₀_zero))
  -- Conclude: the agreement set has at most one element.
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h_zero_a : Δ₀ * ((1 - a) * (x₁ : L) - a) + Δ₁ * (a - (1 - a) * (x₀ : L)) = 0 := by
    rw [← h_fold_diff a, sub_eq_zero]
    exact ha
  have h_zero_b : Δ₀ * ((1 - b) * (x₁ : L) - b) + Δ₁ * (b - (1 - b) * (x₀ : L)) = 0 := by
    rw [← h_fold_diff b, sub_eq_zero]
    exact hb
  exact h_at_most_one_root a b h_zero_a h_zero_b

/-! ### Union bound over the disagreement set -/

/-- Generic union-bound closing step: if event `P` forces some `y ∈ Δ` to drop out of
`D r`, and each `y` drops out for at most one challenge, then
`Pr[P] ≤ |S| / |L|`. -/
lemma pr_le_card_div_of_witness {S : Type} [Fintype S] [DecidableEq S]
    (P : L → Prop) (Δ : Finset S) (D : L → Finset S)
    (h_imp : ∀ rc : L, P rc → ∃ y ∈ Δ, y ∉ D rc)
    (h_pery : ∀ y ∈ Δ, (Finset.univ.filter (fun rc : L => y ∉ D rc)).card ≤ 1) :
    Pr_{ let r_new ← $ᵖ L }[ P r_new ] ≤
      ((Fintype.card S : ENNReal) / (Fintype.card L : ENNReal)) := by
  classical
  refine le_trans
    (Pr_le_Pr_of_implies ($ᵖ L) P (fun rc => ∃ y ∈ Δ, y ∉ D rc) h_imp) ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  refine Nat.cast_le.mpr ?_
  calc (Finset.univ.filter (fun rc : L => ∃ y ∈ Δ, y ∉ D rc)).card
      ≤ (Δ.biUnion (fun y => Finset.univ.filter (fun rc : L => y ∉ D rc))).card := by
        apply Finset.card_le_card
        intro rc hrc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrc
        obtain ⟨y, hyΔ, hyD⟩ := hrc
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, hyΔ, hyD⟩
    _ ≤ ∑ y ∈ Δ, (Finset.univ.filter (fun rc : L => y ∉ D rc)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Δ, 1 := Finset.sum_le_sum h_pery
    _ = Δ.card := by simp
    _ ≤ Fintype.card S := Finset.card_le_univ Δ

/-! ### k = 0 degenerate case: the 0-step fold preserves the disagreement set -/

/-- For `k = 0` the consumed-prefix disagreement set condition holds unconditionally:
the `0`-step fold is the identity, so `Δ_fiber ⊆ D_0`. -/
lemma delta_subset_Dk_of_k_eq_zero (block_start_idx : Fin r)
    {midIdx_i destIdx : Fin r} (k : ℕ) (hk0 : k = 0)
    (h_mid : midIdx_i.val = block_start_idx.val + k)
    (h_dest : destIdx.val = block_start_idx.val + ϑ) (h_dest_le : destIdx ≤ ℓ)
    (hDk_dest : destIdx.val = midIdx_i.val + (ϑ - k))
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (rs : Fin k → L) :
    fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (destIdx := destIdx) h_dest h_dest_le f g ⊆
    fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx_i) (steps := ϑ - k) (destIdx := destIdx) hDk_dest h_dest_le
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
        (steps := k) (destIdx := midIdx_i) (h_destIdx := h_mid)
        (h_destIdx_le := by omega) f rs)
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
        (steps := k) (destIdx := midIdx_i) (h_destIdx := h_mid)
        (h_destIdx_le := by omega) g rs) := by
  subst hk0
  have h_eq : block_start_idx = midIdx_i := Fin.eq_of_val_eq (by omega)
  subst h_eq
  have hf0 : ∀ F : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx,
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
        (steps := 0) (destIdx := block_start_idx) (h_destIdx := h_mid)
        (h_destIdx_le := by omega) F rs = F := by
    intro F
    funext z
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (h_destIdx := h_mid) (h_destIdx_le := by omega)]
    rfl
  rw [hf0 f, hf0 g]
  intro y hy
  rw [mem_fiberwiseDisagreementSetPerFiber] at hy ⊢
  obtain ⟨idx, hne⟩ := hy
  exact ⟨idx, hne⟩

/-! ### The main theorem: Prop 4.21.2, Case 1 (FiberwiseClose) -/

open Classical in
set_option maxHeartbeats 4000000 in
/-- **Proposition 4.21.2, Case 1 (FiberwiseClose), incremental bad-event bound.**
This is the formerly isolated case-1 theorem, now proven against the honest per-fiber
disagreement surface. -/
theorem prop_4_21_2_case_1_residual_holds
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ)
    (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    Pr_{ let r_new ← $ᵖ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx)
          (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i) (h_destIdx := h_destIdx)
          (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ) (destIdx := destIdx)
        (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) / Fintype.card L) := by
  classical
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
  -- Shared index-arithmetic facts.
  have hk_mid : midIdx_i.val = block_start_idx.val + k := by omega
  have hk_mid_le : midIdx_i.val ≤ ℓ := by omega
  have h_ms : midIdx_i_succ.val = midIdx_i.val + 1 := by omega
  have h_ms_le : midIdx_i_succ.val ≤ ℓ := by omega
  have h_bsi_le : block_start_idx.val ≤ ℓ := by omega
  have hDk_dest : destIdx.val = midIdx_i.val + (ϑ - k) := by omega
  have hK1d : midIdx_i_succ.val = block_start_idx.val + (k + 1) := by omega
  -- The block-level closest codeword.
  set f_bar : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx :=
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
      (h_i := h_bsi_le) (f := f_block_start)
      (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx) (steps := ϑ)
        (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        f_block_start h_block_close) with hf_bar_def
  -- The k-step folds (deterministic: no dependence on the fresh challenge).
  set fold_k_f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx_i :=
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
      (steps := k) (destIdx := midIdx_i) (h_destIdx := hk_mid)
      (h_destIdx_le := hk_mid_le) f_block_start r_prefix with hfkf_def
  set fold_k_f_bar : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx_i :=
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
      (steps := k) (destIdx := midIdx_i) (h_destIdx := hk_mid)
      (h_destIdx_le := hk_mid_le) f_bar r_prefix with hfkfb_def
  -- The block-level fiberwise disagreement set.
  set Δ_fiber : Finset (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
    fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (destIdx := destIdx)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      f_block_start f_bar with hΔ_def
  -- Case on whether the deterministic ¬E(k) condition holds.
  by_cases h_sub : Δ_fiber ⊆ fiberwiseDisagreementSetPerFiber 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx_i) (steps := ϑ - k) (destIdx := destIdx)
      (h_destIdx := hDk_dest) (h_destIdx_le := h_destIdx_le)
      fold_k_f fold_k_f_bar
  case neg =>
    -- ¬E(k) fails (so the conjunction is empty): k ≠ 0 since the k = 0 subset holds
    -- unconditionally, hence E(k) holds.
    have hk0 : ¬ (k = 0) := fun hkeq =>
      h_sub (delta_subset_Dk_of_k_eq_zero 𝔽q β block_start_idx k hkeq hk_mid
        (by omega) h_destIdx_le hDk_dest f_block_start f_bar r_prefix)
    have hEk : incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx)
        (k := k)
        (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start) (r_challenges := r_prefix) := by
      unfold incrementalFoldingBadEvent
      rw [dif_neg hk0, dif_neg (show ¬ k = ϑ by omega), dif_pos h_block_close]
      exact h_sub
    refine le_trans
      (Pr_le_Pr_of_implies ($ᵖ L) _ (fun _ => False) (fun rc h => h.1 hEk)) ?_
    change (PMF.bind ($ᵖ L) (fun _ => PMF.pure False)) True ≤ _
    rw [PMF.bind_const, PMF.pure_apply]
    simp
  case pos =>
  -- The deterministic condition holds; bound Pr[E(k+1)] by the union bound.
  by_cases hk1ϑ : k + 1 = ϑ
  · -- Final step: E(k+1) = foldingBadEvent; D_{k+1} is the plain disagreement set.
    have hTHd : destIdx.val = block_start_idx.val + ϑ := by omega
    refine pr_le_card_div_of_witness (S := sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
      _ Δ_fiber
      (fun rc => disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
          (steps := ϑ) (destIdx := destIdx) (h_destIdx := hTHd)
          (h_destIdx_le := h_destIdx_le) f_block_start
          (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j)))
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
          (steps := ϑ) (destIdx := destIdx) (h_destIdx := hTHd)
          (h_destIdx_le := h_destIdx_le) f_bar
          (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j))))
      ?_ ?_
    · -- The event implies some y ∈ Δ_fiber drops out of the folded disagreement set.
      intro rc hrc
      have hE2 : ¬ (Δ_fiber ⊆ disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
            (steps := ϑ) (destIdx := destIdx) (h_destIdx := hTHd)
            (h_destIdx_le := h_destIdx_le) f_block_start
            (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j)))
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
            (steps := ϑ) (destIdx := destIdx) (h_destIdx := hTHd)
            (h_destIdx_le := h_destIdx_le) f_bar
            (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j)))) := by
        have h := hrc.2
        unfold incrementalFoldingBadEvent at h
        rw [dif_neg (Nat.succ_ne_zero k), dif_pos hk1ϑ] at h
        unfold foldingBadEvent at h
        rw [dif_pos h_block_close] at h
        exact h
      rw [Finset.not_subset] at hE2
      obtain ⟨y, hyΔ, hyD⟩ := hE2
      exact ⟨y, hyΔ, hyD⟩
    · -- Per-point bound: at most one challenge drops y.
      intro y hyΔ
      have hyDk := h_sub hyΔ
      rw [mem_fiberwiseDisagreementSetPerFiber] at hyDk
      obtain ⟨idx, hne⟩ := hyDk
      have hsteps1 : ϑ - k = 1 := by omega
      have h_ms' : destIdx.val = midIdx_i.val + 1 := by omega
      have e1 := fiberEvaluations_congr_steps 𝔽q β (i := midIdx_i) (destIdx := destIdx)
        (h := hsteps1) (hd₁ := hDk_dest) (hd₂ := h_ms') (h_le := h_destIdx_le)
        fold_k_f y idx
      have e2 := fiberEvaluations_congr_steps 𝔽q β (i := midIdx_i) (destIdx := destIdx)
        (h := hsteps1) (hd₁ := hDk_dest) (hd₂ := h_ms') (h_le := h_destIdx_le)
        fold_k_f_bar y idx
      have h_dis : ∃ b : Fin (2 ^ 1),
          fiberEvaluations 𝔽q β (i := midIdx_i) (steps := 1) (destIdx := destIdx)
            h_ms' h_destIdx_le fold_k_f y b ≠
          fiberEvaluations 𝔽q β (i := midIdx_i) (steps := 1) (destIdx := destIdx)
            h_ms' h_destIdx_le fold_k_f_bar y b := by
        refine ⟨Fin.cast (congrArg (fun s => 2 ^ s) hsteps1) idx, ?_⟩
        rw [← e1, ← e2]
        exact hne
      refine le_trans (Finset.card_le_card ?_)
        (card_filter_fold_eq_le_one 𝔽q β midIdx_i (midSucc := destIdx) h_ms'
          h_destIdx_le fold_k_f fold_k_f_bar y h_dis)
      -- The drop event implies fold agreement at y.
      intro rc hrc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrc ⊢
      have hlast : ∀ F : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          block_start_idx,
          iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
            (steps := ϑ) (destIdx := destIdx) (h_destIdx := hTHd)
            (h_destIdx_le := h_destIdx_le) F
            (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j)) =
          fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
            (destIdx := destIdx) h_ms' h_destIdx_le
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k) (destIdx := midIdx_i)
              (h_destIdx := hk_mid) (h_destIdx_le := hk_mid_le) F r_prefix) rc := by
        intro F
        have hcongr := iterated_fold_congr_steps 𝔽q β (i := block_start_idx)
          (destIdx := destIdx) (h := hk1ϑ) (hd₁ := by omega) (hd₂ := hTHd)
          (h_le := h_destIdx_le) F (Fin.snoc r_prefix rc)
        rw [hcongr]
        have h := iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k) (midIdx := midIdx_i) (destIdx := destIdx)
          (h_midIdx := hk_mid) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
          (f := F) (r_challenges := Fin.snoc r_prefix rc)
        simp only [Fin.init_snoc, Fin.snoc_last] at h
        exact h
      have hagree : (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := ϑ) (destIdx := destIdx) (h_destIdx := hTHd)
          (h_destIdx_le := h_destIdx_le) f_block_start
          (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j))) y =
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := ϑ) (destIdx := destIdx) (h_destIdx := hTHd)
          (h_destIdx_le := h_destIdx_le) f_bar
          (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j))) y := by
        by_contra hne2
        exact hrc ((mem_disagreementSet_self 𝔽q β _ _ y).mpr hne2)
      calc fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
            (destIdx := destIdx) h_ms' h_destIdx_le fold_k_f rc y
          = (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := ϑ) (destIdx := destIdx)
              (h_destIdx := hTHd) (h_destIdx_le := h_destIdx_le) f_block_start
              (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j))) y := by
            rw [hlast f_block_start]
        _ = (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := ϑ) (destIdx := destIdx)
              (h_destIdx := hTHd) (h_destIdx_le := h_destIdx_le) f_bar
              (fun j => (Fin.snoc r_prefix rc : Fin (k + 1) → L) (Fin.cast hk1ϑ.symm j))) y := hagree
        _ = fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
              (destIdx := destIdx) h_ms' h_destIdx_le fold_k_f_bar rc y := by
            rw [hlast f_bar]
  · -- Intermediate step: E(k+1) is the per-fiber subset condition at steps ϑ-(k+1).
    have hDk1_dest : destIdx.val = midIdx_i_succ.val + (ϑ - (k + 1)) := by omega
    refine pr_le_card_div_of_witness (S := sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
      _ Δ_fiber
      (fun rc => fiberwiseDisagreementSetPerFiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx_i_succ) (steps := ϑ - (k + 1)) (destIdx := destIdx)
        (h_destIdx := hDk1_dest) (h_destIdx_le := h_destIdx_le)
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
          (steps := k + 1) (destIdx := midIdx_i_succ) (h_destIdx := hK1d)
          (h_destIdx_le := h_ms_le) f_block_start (Fin.snoc r_prefix rc))
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
          (steps := k + 1) (destIdx := midIdx_i_succ) (h_destIdx := hK1d)
          (h_destIdx_le := h_ms_le) f_bar (Fin.snoc r_prefix rc)))
      ?_ ?_
    · -- The event implies some y ∈ Δ_fiber drops out of D_{k+1}.
      intro rc hrc
      have hE2 : ¬ (Δ_fiber ⊆ fiberwiseDisagreementSetPerFiber 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := midIdx_i_succ) (steps := ϑ - (k + 1)) (destIdx := destIdx)
          (h_destIdx := hDk1_dest) (h_destIdx_le := h_destIdx_le)
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
            (steps := k + 1) (destIdx := midIdx_i_succ) (h_destIdx := hK1d)
            (h_destIdx_le := h_ms_le) f_block_start (Fin.snoc r_prefix rc))
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
            (steps := k + 1) (destIdx := midIdx_i_succ) (h_destIdx := hK1d)
            (h_destIdx_le := h_ms_le) f_bar (Fin.snoc r_prefix rc))) := by
        have h := hrc.2
        unfold incrementalFoldingBadEvent at h
        rw [dif_neg (Nat.succ_ne_zero k), dif_neg hk1ϑ, dif_pos h_block_close] at h
        exact h
      rw [Finset.not_subset] at hE2
      obtain ⟨y, hyΔ, hyD⟩ := hE2
      exact ⟨y, hyΔ, hyD⟩
    · -- Per-point bound via the bottom fiber peel + Schwartz–Zippel.
      intro y hyΔ
      have hyDk := h_sub hyΔ
      rw [mem_fiberwiseDisagreementSetPerFiber] at hyDk
      obtain ⟨idx, hne⟩ := hyDk
      have hsteps : ϑ - k = (ϑ - (k + 1)) + 1 := by omega
      have h_dest' : destIdx.val = midIdx_i.val + ((ϑ - (k + 1)) + 1) := by omega
      have h_ms'' : midIdx_i_succ.val = midIdx_i.val + 1 := h_ms
      -- Step-count congruence on the witness.
      have e1 := fiberEvaluations_congr_steps 𝔽q β (i := midIdx_i) (destIdx := destIdx)
        (h := hsteps) (hd₁ := hDk_dest) (hd₂ := h_dest') (h_le := h_destIdx_le)
        fold_k_f y idx
      have e2 := fiberEvaluations_congr_steps 𝔽q β (i := midIdx_i) (destIdx := destIdx)
        (h := hsteps) (hd₁ := hDk_dest) (hd₂ := h_dest') (h_le := h_destIdx_le)
        fold_k_f_bar y idx
      -- The intermediate fiber point of y over midIdx_i_succ.
      have hp1 := fiberEvaluations_peel_first 𝔽q β midIdx_i (midSucc := midIdx_i_succ)
        (destIdx := destIdx) (n := ϑ - (k + 1)) h_ms'' (by omega) h_dest' h_destIdx_le
        fold_k_f y (Fin.cast (congrArg (fun s => 2 ^ s) hsteps) idx)
      have hp2 := fiberEvaluations_peel_first 𝔽q β midIdx_i (midSucc := midIdx_i_succ)
        (destIdx := destIdx) (n := ϑ - (k + 1)) h_ms'' (by omega) h_dest' h_destIdx_le
        fold_k_f_bar y (Fin.cast (congrArg (fun s => 2 ^ s) hsteps) idx)
      -- Name the intermediate fiber point (the same term as in `hp1`/`hp2`, up to
      -- proof irrelevance).
      set W : sDomain 𝔽q β h_ℓ_add_R_rate midIdx_i_succ :=
        qMap_total_fiber 𝔽q β (i := midIdx_i_succ) (steps := ϑ - (k + 1))
          (h_i_add_steps := by omega)
          (y := ⟨y.val, by
            have hidx2 : (⟨midIdx_i_succ.val + (ϑ - (k + 1)), by omega⟩ : Fin r)
                = destIdx := Fin.eq_of_val_eq
                  (show midIdx_i_succ.val + (ϑ - (k + 1)) = destIdx.val by omega)
            rw [hidx2]
            exact y.property⟩)
          ⟨idx.val / 2, by
            have h1 : idx.val < 2 ^ (ϑ - k) := idx.isLt
            have h2 : (2 : ℕ) ^ (ϑ - k) = 2 * 2 ^ (ϑ - (k + 1)) := by
              rw [hsteps, pow_succ, Nat.mul_comm]
            omega⟩ with hW_def
      have h_dis : ∃ b : Fin (2 ^ 1),
          fiberEvaluations 𝔽q β (i := midIdx_i) (steps := 1) (destIdx := midIdx_i_succ)
            h_ms'' (by omega) fold_k_f W b ≠
          fiberEvaluations 𝔽q β (i := midIdx_i) (steps := 1) (destIdx := midIdx_i_succ)
            h_ms'' (by omega) fold_k_f_bar W b := by
        refine ⟨⟨idx.val % 2, by
          have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
          omega⟩, ?_⟩
        intro hcontra
        apply hne
        rw [e1, e2, hp1, hp2]
        exact hcontra
      refine le_trans (Finset.card_le_card ?_)
        (card_filter_fold_eq_le_one 𝔽q β midIdx_i (midSucc := midIdx_i_succ) h_ms''
          (by omega) fold_k_f fold_k_f_bar W h_dis)
      -- The drop event implies fold agreement at W.
      intro rc hrc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrc ⊢
      rw [mem_fiberwiseDisagreementSetPerFiber] at hrc
      have hag : ∀ idx2 : Fin (2 ^ (ϑ - (k + 1))),
          fiberEvaluations 𝔽q β (i := midIdx_i_succ) (steps := ϑ - (k + 1))
            (destIdx := destIdx) hDk1_dest h_destIdx_le
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1) (destIdx := midIdx_i_succ)
              (h_destIdx := hK1d) (h_destIdx_le := h_ms_le) f_block_start
              (Fin.snoc r_prefix rc)) y idx2 =
          fiberEvaluations 𝔽q β (i := midIdx_i_succ) (steps := ϑ - (k + 1))
            (destIdx := destIdx) hDk1_dest h_destIdx_le
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1) (destIdx := midIdx_i_succ)
              (h_destIdx := hK1d) (h_destIdx_le := h_ms_le) f_bar
              (Fin.snoc r_prefix rc)) y idx2 :=
        fun idx2 => not_not.mp (not_exists.mp hrc idx2)
      have hagW : (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k + 1) (destIdx := midIdx_i_succ)
          (h_destIdx := hK1d) (h_destIdx_le := h_ms_le) f_block_start
          (Fin.snoc r_prefix rc)) W =
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k + 1) (destIdx := midIdx_i_succ)
          (h_destIdx := hK1d) (h_destIdx_le := h_ms_le) f_bar
          (Fin.snoc r_prefix rc)) W :=
        by
          have h := hag ⟨idx.val / 2, by
            have h1 : idx.val < 2 ^ (ϑ - k) := idx.isLt
            have h2 : (2 : ℕ) ^ (ϑ - k) = 2 * 2 ^ (ϑ - (k + 1)) := by
              rw [hsteps, pow_succ, Nat.mul_comm]
            omega⟩
          have hs : ϑ - (k + 1) ≠ 0 := by omega
          have h_bound_dest : midIdx_i_succ.val + (ϑ - (k + 1)) < r := by
            rw [← hDk1_dest]
            exact destIdx.isLt
          have h_eq_dest : destIdx =
              (⟨midIdx_i_succ.val + (ϑ - (k + 1)), h_bound_dest⟩ : Fin r) :=
            Fin.eq_of_val_eq hDk1_dest
          subst h_eq_dest
          simpa only [fiberEvaluations, quotientFiber, qMap_total_fiber, hs, ↓reduceDIte,
            W, Fin.eta, Subtype.coe_eta] using h

      have hlast : ∀ F : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          block_start_idx,
          iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := block_start_idx)
            (steps := k + 1) (destIdx := midIdx_i_succ) (h_destIdx := hK1d)
            (h_destIdx_le := h_ms_le) F (Fin.snoc r_prefix rc) =
          fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
            (destIdx := midIdx_i_succ) h_ms'' (by omega)
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k) (destIdx := midIdx_i)
              (h_destIdx := hk_mid) (h_destIdx_le := hk_mid_le) F r_prefix) rc := by
        intro F
        have h := iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k) (midIdx := midIdx_i)
          (destIdx := midIdx_i_succ)
          (h_midIdx := hk_mid) (h_destIdx := by omega) (h_destIdx_le := by omega)
          (f := F) (r_challenges := Fin.snoc r_prefix rc)
        simp only [Fin.init_snoc, Fin.snoc_last] at h
        exact h
      calc fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
            (destIdx := midIdx_i_succ) h_ms'' (by omega) fold_k_f rc W
          = (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1) (destIdx := midIdx_i_succ)
              (h_destIdx := hK1d) (h_destIdx_le := h_ms_le) f_block_start
              (Fin.snoc r_prefix rc)) W := by rw [hlast f_block_start]
        _ = (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1) (destIdx := midIdx_i_succ)
              (h_destIdx := hK1d) (h_destIdx_le := h_ms_le) f_bar
              (Fin.snoc r_prefix rc)) W := hagW
        _ = fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
              (destIdx := midIdx_i_succ) h_ms'' (by omega) fold_k_f_bar rc W := by
            rw [hlast f_bar]


end

end Binius.BinaryBasefold
