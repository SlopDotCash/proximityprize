/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.CodingTheory.Prelims
import ProximityPrize.Extensions.Data.Fin.BigOperators
import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT
import ProximityPrize.Extensions.Data.MvPolynomial.Multilinear
import ArkLib.Data.MvPolynomial.RestrictDegree
import CompPoly.Data.Vector.Basic
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Spec.SingleRound
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Structured.SingleRound
import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic.IndexAndSumcheck

/-!
# Binary Basefold Preliminaries

Supporting lemmas and definitions for the Binary Basefold formalization: Hamming-distance bounds
under composition with injective maps, index-bound arithmetic over `Fin` (`fin_ℓ_lt_r` and
friends), and the fiber-coefficient maps (`fiber_coeff`, `qMap_total_fiber`) relating evaluation
points across folding levels.
-/

set_option linter.style.longFile 2800

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

section Preliminaries

/-- Hamming distance is non-increasing under inner composition with an injective function.
NOTE : we can prove strict equality given `g` being an equivalence instead of injection.
-/
theorem hammingDist_le_of_outer_comp_injective {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {β : ι₂ → Type*} [∀ i, DecidableEq (β i)] [DecidableEq ι₂]
    (x y : ∀ i, β i) (g : ι₁ → ι₂) (hg : Function.Injective g) :
    hammingDist (fun i => x (g i)) (fun i => y (g i)) ≤ hammingDist x y := by
  -- Let D₂ be the set of disagreeing indices for x and y.
  let D₂ := Finset.filter (fun i₂ => x i₂ ≠ y i₂) Finset.univ
  -- The Hamming distance of the composed functions is the card of the preimage of D₂.
  suffices (Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ).card ≤ D₂.card by
    unfold hammingDist; simp only [this, D₂]
  -- The cardinality of a preimage is at most the cardinalit
    -- of the original set for an injective function.
  -- ⊢ #{i₁ | x (g i₁) ≠ y (g i₁)} ≤ #D₂
   -- First, we state that the set on the left is the `preimage` of D₂ under g.
  have h_preimage : Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ
    = D₂.preimage g (by exact hg.injOn) := by
    -- Use `ext` to prove equality by showing the membership conditions are the same.
    ext i₁
    -- Now `simp` can easily unfold `mem_filter` and `mem_preimage` and see they are equivalent.
    simp only [ne_eq, mem_filter, mem_univ, true_and, mem_preimage, D₂]

  -- Now, rewrite the goal using `preimage`.
  rw [h_preimage]
  set D₁ := D₂.preimage g (by exact hg.injOn)
  -- ⊢ #D₁ ≤ #D₂
  -- Step 1 : The size of a set is at most the size of its image under an injective function.
  have h_card_le_image : D₁.card ≤ (D₁.image g).card := by
    -- This follows directly from the fact that `g` is injective on the set D₁.
    apply Finset.card_le_card_of_injOn (f := g)
    · -- Goal 1 : Prove that `g` maps `D₁` to `D₁.image g`. This is true by definition of image.
      have res := Set.mapsTo_image (f := g) (s := D₁)
      convert res
      simp only [coe_image]
      -- (D₁.image g : Set ι₂)
    · -- Goal 2 : Prove that `g` is injective on the set `D₁`.
      -- This is true because our main hypothesis `hg` states that `g` is injective everywhere.
      exact Function.Injective.injOn hg

  -- Step 2 : The image of the preimage of a set is always a subset of the original set.
  have h_image_subset : D₁.image g ⊆ D₂ := by
    simp [D₁, Finset.image_preimage]

  -- Step 3 : By combining these two facts, we get our result.
  -- |D₁| ≤ |image g(D₁)| (from Step 1)
  -- and |image g(D₁)| ≤ |D₂| (since it's a subset)
  exact h_card_le_image.trans (Finset.card_le_card h_image_subset)

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]

-- `fixFirstVariablesOfMQP` and `fixFirstVariablesOfMQP_degreeLE` (plus three private
-- helper lemmas) were lifted to `ArkLib.Data.MvPolynomial.RestrictDegree`, and
-- `getSumcheckRoundPoly` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`,
-- so the structured sumcheck (`ArkLib.ProofSystem.Sumcheck.Structured`) and any future
-- ring-switching protocol can use them without depending on `Binius.BinaryBasefold`.
-- They are accessible here unqualified via `open MvPolynomial` / `open Sumcheck.Structured`
-- above; we also export them under the `Binius.BinaryBasefold` namespace for any
-- fully-qualified callers.
export MvPolynomial (fixFirstVariablesOfMQP fixFirstVariablesOfMQP_degreeLE)
export Sumcheck.Structured (getSumcheckRoundPoly)

end Preliminaries

noncomputable section -- expands with 𝔽q in front
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}

section Essentials
-- In this section, we ue notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

omit [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
/-- Domain carriers at propositionally equal indices are equal types. -/
lemma sDomain_eq_of_eq {i j : Fin r} (h : i = j) :
    (↥(sDomain 𝔽q β h_ℓ_add_R_rate i) : Type) = ↥(sDomain 𝔽q β h_ℓ_add_R_rate j) := by
  rw [h]

omit [NeZero ℓ] in
lemma fin_ℓ_lt_ℓ_add_one (i : Fin ℓ) : i < ℓ + 1 :=
  Nat.lt_of_lt_of_le i.isLt (Nat.le_succ ℓ)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_ℓ_add_R (i : Fin ℓ)
    : i.val < ℓ + 𝓡 := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ)
    : i.val < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_add_one_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin (ℓ + 1))
    : i.val < r := by omega

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_one (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < ℓ + 1 :=
  Nat.lt_of_le_of_lt h (Nat.lt_succ_self ℓ)

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_R (i : Fin ℓ) (steps : ℕ) (h : i.val + steps ≤ ℓ)
    : i.val + steps < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_steps_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < r := by
  apply Nat.lt_of_le_of_lt (n := i + steps) (k := r) (m := ℓ) (h₁ := h)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
    : ℓ < r := by omega

omit [NeZero ℓ] [NeZero r] in
lemma Sdomain_bound {x : ℕ} (h : x ≤ ℓ) : x < ℓ + 𝓡 := by
  have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
  omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_r_succ_bound {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin r) (h_i : i + 1 < ℓ + 𝓡)
    : i + 1 < r := by omega

/-!
### The Fiber of the Quotient Map `qMap`

Utilities for constructing fibers and defining the fold operations used by Binary Basefold.
-/

def Fin2ToF2 (𝔽q : Type*) [Ring 𝔽q] (k : Fin 2) : 𝔽q :=
  if k = 0 then 0 else 1

/-! Standalone helper for the fiber coefficients used in `qMap_total_fiber`. -/
noncomputable def fiber_coeff
    (i : Fin r) (steps : ℕ)
    (j : Fin (ℓ + 𝓡 - i)) (elementIdx : Fin (2 ^ steps))
    (y_coeffs : Fin (ℓ + 𝓡 - (i + steps)) →₀ 𝔽q) : 𝔽q :=
  if hj : j.val < steps then
    if Nat.getBit (k := j) (n := elementIdx) = 0 then 0 else 1
  else y_coeffs ⟨j.val - steps, by -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑⟨↑i + steps, ⋯⟩
    rw [←Nat.sub_sub]; -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑i - steps
    apply Nat.sub_lt_sub_right;
    · exact Nat.le_of_not_lt hj
    · exact j.isLt⟩

/-- Get the full fiber list `(x₀, ..., x_{2 ^ steps-1})` which represents the
joined fiber `(q⁽ⁱ⁺steps⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾)⁻¹({y}) ⊂ S⁽ⁱ⁾` over `y ∈ S^(i+steps)`,
in which the LSB repsents the FIRST qMap `q⁽ⁱ⁾`, and the MSB represents the LAST `q⁽ⁱ⁺steps⁻¹⁾`
-/
noncomputable def qMap_total_fiber
    -- S^i is source domain, S^{i + steps} is the target domain
      (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
        (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fin (2 ^ steps) → sDomain 𝔽q β h_ℓ_add_R_rate i :=
  if h_steps : steps = 0 then by
    -- Base case : 0 steps, the fiber is just the point y itself.
    subst h_steps
    simp only [add_zero, Fin.eta] at y
    exact fun _ => y
  else by
    -- fun (k : 𝔽q) =>
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i+steps,by omega⟩) (by omega)
    let y_coeffs : Fin (ℓ + 𝓡 - (↑i + steps)) →₀ 𝔽q := basis_y.repr y

    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    exact fun elementIdx => by
      let x_coeffs : Fin (ℓ + 𝓡 - i) → 𝔽q := fun j =>
        if hj_lt_steps : j.val < steps then
          if Nat.getBit (k := j) (n := elementIdx) = 0 then (0 : 𝔽q)
          else (1 : 𝔽q)
        else
          y_coeffs ⟨j.val - steps, by
            rw [←Nat.sub_sub]; apply Nat.sub_lt_sub_right;
            · exact Nat.le_of_not_lt hj_lt_steps
            · exact j.isLt
          ⟩ -- Shift indices to match y's basis
      exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

omit [CharP L 2] [NeZero ℓ] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
/-- Canonical destination-keyed fibers agree with the broader legacy rate-tail fiber. -/
private lemma quotientFiber_eq_legacy (i : Fin r) (steps : ℕ)
    (h_le : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩) :
    quotientFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
      (h_destIdx := rfl) (h_destIdx_le := h_le) y =
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
        (by have hR := Nat.pos_of_neZero 𝓡; omega) y := by
  by_cases h : steps = 0
  · subst steps
    simp [quotientFiber, qMap_total_fiber]
  · simp only [quotientFiber, qMap_total_fiber, h, ↓reduceDIte]

/- Note: state that the fiber of y is the set of all 2 ^ steps points in the
larger domain S⁽ⁱ⁾ that get mapped to y by the series of quotient maps q⁽ⁱ⁾, ..., q⁽ⁱ⁺steps⁻¹⁾. -/

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction**.
The coefficients of `x = qMap_total_fiber(y, k)` with respect to `basis_x` are exactly
the function that puts binary coeffs corresponding to bits of `k` in
the first `steps` positions, and shifts `y`'s coefficients.
This is the multi-step counterpart of `qMap_fiber_repr_coeff`.
-/
lemma qMap_total_fiber_repr_coeff (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)
      (h_i := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
    let y_coeffs := basis_y.repr y
    ∀ j, -- j refers to bit index of the fiber point x
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (by simp only; omega)).repr x) j
      = fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k)
        (y_coeffs := y_coeffs) := by
  unfold fiber_coeff
  simp only
  intro j
  -- have h_steps_ne_0 : steps ≠ 0 := by exact?
  by_cases h_steps_eq_0 : steps = 0
  · subst h_steps_eq_0
    simp only [qMap_total_fiber, ↓reduceDIte, Nat.add_zero, eq_mp_eq_cast, cast_eq, not_lt_zero',
      tsub_zero, Fin.eta]
  · simp only [qMap_total_fiber, h_steps_eq_0, ↓reduceDIte, Module.Basis.repr_symm_apply,
    Module.Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_apply]

/-- `b` and `2 ^ n * c` have disjoint bit supports when `b < 2 ^ n`: low `n` bits live in
`b`, bits `≥ n` live in `2 ^ n * c`. -/
lemma and_lt_two_pow_mul_eq_zero {n c b : ℕ} (hb : b < 2 ^ n) :
    b &&& (2 ^ n * c) = 0 := by
  apply Nat.and_eq_zero_iff_and_each_getBit_eq_zero.mpr
  intro k
  rw [Nat.getBit_of_multiple_of_power_of_two]
  by_cases hk : k < n
  · simp only [hk, ↓reduceIte, Nat.and_zero]
  · -- `k ≥ n` ⇒ bit `k` of `b` is `0` since `b < 2 ^ n`.
    have h_b_bit : Nat.getBit k b = 0 := by
      simp only [Nat.getBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega)
        (Nat.le_of_not_lt hk)))]
    simp only [hk, ↓reduceIte, h_b_bit, Nat.zero_and]

/-- Low-bit decomposition: for `b < 2 ^ n`, `c < 2`, the low `n` bits of `c * 2 ^ n + b`
are exactly the bits of `b`. -/
lemma getBit_low_of_add_mul_two_pow {n c b j : ℕ} (hb : b < 2 ^ n) (hj : j < n) :
    Nat.getBit j (c * 2 ^ n + b) = Nat.getBit j b := by
  -- `b` and `c * 2 ^ n` have disjoint bit supports below `n`, so bits agree there.
  have h_and : (2 ^ n * c) &&& b = 0 := by
    rw [Nat.and_comm]; exact and_lt_two_pow_mul_eq_zero hb
  rw [Nat.mul_comm c (2 ^ n)]
  rw [Nat.getBit_of_add_distrib (h_n_AND_m := h_and)]
  rw [Nat.getBit_of_multiple_of_power_of_two]
  simp only [hj, ↓reduceIte, Nat.zero_add]

/-- High-bit decomposition: for `b < 2 ^ n`, `c < 2`, bit `n` of `c * 2 ^ n + b` is `c`. -/
lemma getBit_high_of_add_mul_two_pow {n c b : ℕ} (hb : b < 2 ^ n) (hc : c < 2) :
    Nat.getBit n (c * 2 ^ n + b) = c := by
  have h_and : (2 ^ n * c) &&& b = 0 := by
    rw [Nat.and_comm]; exact and_lt_two_pow_mul_eq_zero hb
  rw [Nat.mul_comm c (2 ^ n)]
  rw [Nat.getBit_of_add_distrib (h_n_AND_m := h_and)]
  rw [Nat.getBit_of_multiple_of_power_of_two]
  simp only [lt_irrefl, ↓reduceIte, Nat.sub_self]
  -- bit `n` of `b` is `0` since `b < 2 ^ n`; bit `0` of `c` is `c` since `c < 2`.
  have h_b_bit : Nat.getBit n b = 0 := by
    simp only [Nat.getBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
    rw [Nat.div_eq_of_lt hb]
  rw [h_b_bit, add_zero]
  simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
  omega

omit [CharP L 2] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Fiber composition (last level peeled).**
The `(n+1)`-step fiber of `y' ∈ S^(i+(n+1))` at index `idx`, with `idx` split into the
high bit `c := idx / 2^n` (selecting the last quotient `q^(i+n)`) and the low `n` bits
`b := idx % 2^n`, equals the `n`-step fiber of the single-step preimage
`z_c := qMap_total_fiber(i+n, 1, y')(c)` at index `b`. This is the geometric fact pinning
the recursive `foldMatrixNat` construction. -/
lemma qMap_total_fiber_succ_peel_last (i : Fin ℓ) (n : ℕ) (h_i_add_steps : i.val + (n + 1) ≤ ℓ)
    (y' : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + (n + 1), by omega⟩))
    (idx : Fin (2 ^ (n + 1))) :
    qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := n + 1)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i (n + 1) h_i_add_steps)
      (y := y') idx =
    qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := n)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i n (by omega))
      (y := qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
        (h_i_add_steps := by
          simp only
          exact Nat.lt_of_le_of_lt (by omega)
            (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (NeZero.ne 𝓡))))
        (y := ⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩)
        ⟨idx.val / 2 ^ n, by
          have hb : idx.val < 2 ^ n * 2 := Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ])
          exact Nat.div_lt_of_lt_mul hb⟩)
      ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ := by
  -- Both points live in `S^i`; compare their `basis_x` coefficients via `repr` injectivity.
  set c : Fin 2 := ⟨idx.val / 2 ^ n, by
    have hb : idx.val < 2 ^ n * 2 := Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ])
    exact Nat.div_lt_of_lt_mul hb⟩ with hc_def
  set b : Fin (2 ^ n) := ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ with hb_def
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
  have h_z_bound : (⟨i.val + n, by omega⟩ : Fin r).val + 1 < ℓ + 𝓡 := by simp only; omega
  let y'_lift : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨(⟨i.val + n, by omega⟩ : Fin r).val + 1, by
    omega⟩) := ⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩
  -- `idx = c * 2^n + b` as naturals.
  have h_idx_split : idx.val = c.val * 2 ^ n + b.val := by
    simp only [hc_def, hb_def]
    exact (Nat.div_add_mod' idx.val (2 ^ n)).symm
  apply (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (by simp only; omega)).repr.injective
  ext j
  -- LHS coefficient via the `(n+1)`-step extraction lemma.
  have hL := qMap_total_fiber_repr_coeff 𝔽q β i (steps := n + 1) (by omega) y' idx (j := j)
  -- RHS coefficient via the `n`-step extraction lemma over `z_c`.
  set zc := qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
    (h_i_add_steps := h_z_bound)
    (y := y'_lift) c with hzc_def
  have hR := qMap_total_fiber_repr_coeff 𝔽q β i (steps := n) (by omega) zc b (j := j)
  simp only at hL hR ⊢
  rw [hL, hR]
  -- Now compare the two `fiber_coeff` values bit-by-bit, using the bit decomposition of `idx`.
  unfold fiber_coeff
  by_cases hj_lt_n : j.val < n
  · -- Low region: both pick up bit `j` of `idx`, which equals bit `j` of `b`.
    have hjn1 : j.val < n + 1 := by omega
    simp only [hj_lt_n, hjn1, ↓reduceDIte]
    rw [h_idx_split, getBit_low_of_add_mul_two_pow b.isLt hj_lt_n]
  · by_cases hj_eq_n : j.val = n
    · -- Boundary: LHS picks up bit `n` of `idx` (= `c`); RHS reads the `0`-th coeff of `z_c`,
      -- which is bit `0` of `c`.
      have hjn1 : j.val < n + 1 := by omega
      have hjn_not : ¬ j.val < n := by omega
      simp only [hjn1, hjn_not, ↓reduceDIte]
      rw [h_idx_split]
      have h_getbit : Nat.getBit j.val (c.val * 2 ^ n + b.val) = c.val := by
        simpa [hj_eq_n] using getBit_high_of_add_mul_two_pow b.isLt c.isLt
      rw [h_getbit]
      -- RHS: `(j - n)`-th coeff of `z_c`'s `basis_y` repr; with `j = n` this is its `0`-th coeff.
      have hRc := qMap_total_fiber_repr_coeff 𝔽q β (⟨i.val + n, by omega⟩ : Fin ℓ) (steps := 1)
        (by simp only; omega)
        (⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩) c
        (j := ⟨j.val - n, by
          have hj_ge_n : n ≤ j.val := Nat.le_of_not_lt hjn_not
          have hsub : j.val - n < (ℓ + 𝓡 - i.val) - n :=
            Nat.sub_lt_sub_right hj_ge_n j.isLt
          simp only
          omega⟩)
      rw [← hzc_def] at hRc
      have hj_sub : j.val - n = 0 := by omega
      have h_c_bit : Nat.getBit 0 c.val = c.val := by
        simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
        omega
      simp only [fiber_coeff, hj_sub, zero_lt_one, ↓reduceDIte, h_c_bit] at hRc
      simpa [hj_sub] using hRc.symm
    · -- High region (`j > n`): both read `y'`'s shifted coefficients; indices agree.
      have hjn1_not : ¬ j.val < n + 1 := by omega
      have hjn_not : ¬ j.val < n := by omega
      simp only [hjn1_not, hjn_not, ↓reduceDIte]
      have hRc := qMap_total_fiber_repr_coeff 𝔽q β (⟨i.val + n, by omega⟩ : Fin ℓ) (steps := 1)
        (by simp only; omega)
        (⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩) c
        (j := ⟨j.val - n, by
          have hj_ge_n : n ≤ j.val := Nat.le_of_not_lt hjn_not
          have hsub : j.val - n < (ℓ + 𝓡 - i.val) - n :=
            Nat.sub_lt_sub_right hj_ge_n j.isLt
          simp only
          omega⟩)
      rw [← hzc_def] at hRc
      have hj_sub_not : ¬ j.val - n < 1 := by omega
      simp only [fiber_coeff, hj_sub_not, ↓reduceDIte] at hRc
      convert hRc.symm using 1 <;> omega

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- When ϑ = 1, qMap_total_fiber maps k = 0 to an element with first coefficient 0
and k = 1 to an element with first coefficient 1. -/
lemma qMap_total_fiber_one_level_eq (i : Fin ℓ) (h_i_add_1 : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i + 1, by omega⟩)) (k : Fin 2) :
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    let x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := 1) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k
    let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := sDomain.lift 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (h_j := by apply Nat.lt_add_of_pos_right_of_le; omega)
      (h_le := by apply Fin.mk_le_mk.mpr (by omega)) y
    let free_coeff_term : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ :=
      (Fin2ToF2 𝔽q k) • (basis_x ⟨0, by simp only; omega⟩)
    x = free_coeff_term + y_lifted
    := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
  apply basis_x.repr.injective
  simp only [map_add, map_smul]
  simp only [Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, basis_x]
  ext j
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := 1) (by omega)
    (y := y) (k := k) (j := j)
  simp only [h_repr_x, Finsupp.coe_add, Pi.add_apply]
  simp only [fiber_coeff, lt_one_iff, reducePow, Fin2ToF2, Fin.isValue]

  by_cases hj : j = ⟨0, by omega⟩
  · simp only [hj, ↓reduceDIte, Fin.isValue, Finsupp.single_eq_same]
    by_cases hk : k = 0
    · simp only [getBit, hk, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, shiftRight_zero,
      and_one_is_mod, ↓reduceIte, zero_add]
      -- => Now use basis_repr_of_sDomain_lift
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
    · have h_k_eq_1 : k = 1 := by omega
      simp only [getBit, h_k_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, shiftRight_zero,
        Nat.and_self, one_ne_zero, ↓reduceIte, left_eq_add]
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
  · have hj_ne_zero : j ≠ ⟨0, by omega⟩ := by omega
    have hj_val_ne_zero : j.val ≠ 0 := by
      change j.val ≠ ((⟨0, by omega⟩ : Fin (ℓ + 𝓡 - ↑i)).val)
      apply Fin.val_ne_of_ne
      exact hj_ne_zero
    simp only [hj_val_ne_zero, ↓reduceDIte, Finsupp.single, Fin.isValue, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not, Pi.single, Finsupp.coe_mk, Function.update,
      hj_ne_zero, Pi.zero_apply, zero_add]
    simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, lt_one_iff, right_eq_dite_iff]
    intro hj_eq_zero
    exact False.elim (hj_val_ne_zero hj_eq_zero)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] in
/-- `x` is in the fiber of `y` under `qMap_total_fiber` iff `y` is the iterated
quotient of `x`. That is, for binary field, the fiber of `y` is exactly the set of
all `x` that map to `y` under the iterated quotient map. -/
theorem generates_quotient_point_if_is_fiber_of_y
    (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (hx_is_fiber : ∃ (k : Fin (2 ^ steps)), x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := by
        simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k) :
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val, by omega⟩)
      (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
      (h_destIdx := rfl) (h_destIdx_le := h_i_add_steps) x := by
  apply eq_iteratedQuotientMap_of_mem_quotientFiber_range 𝔽q β
    (i := ⟨i.val, by omega⟩) (steps := steps) (h_destIdx := rfl)
    (h_destIdx_le := h_i_add_steps) (x := x) (y := y)
  obtain ⟨k, hk⟩ := hx_is_fiber
  refine ⟨k, ?_⟩
  rw [quotientFiber_eq_legacy 𝔽q β ⟨i.val, by omega⟩ steps h_i_add_steps y]
  exact hk

omit [CharP L 2] [NeZero ℓ] in
/-- State the corrrespondence between the forward qMap and the backward qMap_total_fiber -/
theorem is_fiber_iff_generates_quotient_point (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    let qMapFiber := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y)
    let k := pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
      (destIdx := ⟨i.val + steps, by omega⟩) (h_destIdx := rfl) (h_destIdx_le := h_i_add_steps) (x := x)
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val, by omega⟩)
      (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
      (h_destIdx := rfl) (h_destIdx_le := h_i_add_steps) x ↔
    qMapFiber k = x := by
  simpa only [quotientFiber_eq_legacy] using
    (eq_iteratedQuotientMap_iff_quotientFiber_apply_eq 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, by omega⟩) (steps := steps)
      (h_destIdx := rfl) (h_destIdx_le := h_i_add_steps) (x := x) (y := y))

omit [CharP L 2] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- the pointToIterateQuotientIndex of qMap_total_fiber -/
lemma pointToIterateQuotientIndex_qMap_total_fiber_eq_self (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)) (k : Fin (2 ^ steps)) :
    pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
      (destIdx := ⟨i.val + steps, by omega⟩) (h_destIdx := rfl) (h_destIdx_le := by omega)
      (x := ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k):
          sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))) = k := by
  simpa only [quotientFiber_eq_legacy] using
    (pointToIterateQuotientIndex_quotientFiber_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, by omega⟩) (steps := steps)
      (h_destIdx := rfl) (h_destIdx_le := h_i_add_steps) (y := y) (k := k))

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction** -/
lemma qMap_total_fiber_basis_sum_repr (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := qMap_total_fiber 𝔽q β
      (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by
        apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    let y_coeffs := basis_y.repr y
    x = ∑ j : Fin (ℓ + 𝓡 - i), (
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    ) • (basis_x j)
     := by
    set basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by
      simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    set basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    set y_coeffs := basis_y.repr y
    -- Let `x` be the element from the fiber for brevity.
    set x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    simp only;
    -- Express `(x:L)` using its basis representation, which is built from `x_coeffs_fn`.
    set x_coeffs_fn := fun j : Fin (ℓ + 𝓡 - i) =>
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    have hx_val_sum : (x : L) = ∑ j, (x_coeffs_fn j) • (basis_x j) := by
      rw [←basis_x.sum_repr x]
      rw [Submodule.coe_sum, Submodule.coe_sum]
      congr; funext j;
      simp_rw [Submodule.coe_smul]
      congr; unfold x_coeffs_fn
      have h := qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y := y) (k := k) (j := j)
      rw [h]
    apply Subtype.ext -- convert to equality in Subtype embedding
    rw [hx_val_sum]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
theorem card_qMap_total_fiber (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fintype.card (Set.image (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      (y := y)) Set.univ) = 2 ^ steps := by
  -- The cardinality of the image of a function equals the cardinality of its domain
  -- if it is injective.
  rw [Set.card_image_of_injective Set.univ]
  -- The domain is `Fin (2 ^ steps)`, which has cardinality `2 ^ steps`.
  · -- ⊢ Fintype.card ↑Set.univ = 2 ^ steps
    simp only [Fintype.card_setUniv, Fintype.card_fin]
  · -- prove that `qMap_total_fiber` is an injective function.
    intro k₁ k₂ h_eq
    -- Assume two indices `k₁` and `k₂` produce the same point `x`.
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    -- If the points are equal, their basis representations must be equal.
    set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    have h_coeffs_eq : basis_x.repr (fiberMap k₁) = basis_x.repr (fiberMap k₂) := by
      rw [h_eq]
    -- The first `steps` coefficients are determined by the bits of `k₁` and `k₂`.
    -- If the coefficients are equal, the bits must be equal.
    have h_bits_eq : ∀ j : Fin steps,
        Nat.getBit (k := j) (n := k₁.val) = Nat.getBit (k := j) (n := k₂.val) := by
      intro j
      have h_coeff_j_eq : basis_x.repr (fiberMap k₁) ⟨j, by simp only; omega⟩
        = basis_x.repr (fiberMap k₂) ⟨j, by simp only; omega⟩ := by rw [h_coeffs_eq]
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (k := k₂) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      simp only [fiber_coeff, Fin.is_lt, ↓reduceDIte] at h_coeff_j_eq
      by_cases hbitj_k₁ : Nat.getBit (k := j) (n := k₁.val) = 0
      · simp only [hbitj_k₁, ↓reduceIte, left_eq_ite_iff, zero_ne_one, imp_false,
        Decidable.not_not] at ⊢ h_coeff_j_eq
        simp only [h_coeff_j_eq]
      · simp only [hbitj_k₁, ↓reduceIte, right_eq_ite_iff, one_ne_zero,
        imp_false] at ⊢ h_coeff_j_eq
        have b1 : Nat.getBit (k := j) (n := k₁.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₁.val)
          simp only [hbitj_k₁, false_or] at h
          exact h
        have b2 : Nat.getBit (k := j) (n := k₂.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₂.val)
          simp only [h_coeff_j_eq, false_or] at h
          exact h
        simp only [b1, b2]
      -- Extract the j-th coefficient from h_coeffs_eq and show it implies the bits are equal.
    -- If all the bits of two numbers are equal, the numbers themselves are equal.
    apply Fin.eq_of_val_eq
    -- ⊢ ∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
    apply eq_iff_eq_all_getBits.mpr
    intro k
    by_cases h_k : k < steps
    · simp only [h_bits_eq ⟨k, by omega⟩]
    · -- The bits at positions ≥ steps must be deterministic
      conv_lhs => rw [Nat.getBit_of_lt_two_pow]
      conv_rhs => rw [Nat.getBit_of_lt_two_pow]
      simp only [h_k, ↓reduceIte]
omit [CharP L 2] [NeZero ℓ] in
/-- The images of `qMap_total_fiber` over distinct quotient points `y₁ ≠ y₂` are
disjoint -/
theorem qMap_total_fiber_disjoint
    (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
  {y₁ y₂ : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩}
  (hy_ne : y₁ ≠ y₂) :
  Disjoint
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₁ '' Set.univ).toFinset)
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₂ '' Set.univ).toFinset)
    := by
  simpa only [quotientFiber_eq_legacy] using
    (quotientFiber_disjoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, by omega⟩) (steps := steps) (h_destIdx := rfl)
      (h_destIdx_le := h_i_add_steps) hy_ne)

/-- Single-step fold (LEGACY signature). Given `f : S⁽ⁱ⁾ → L` and challenge `r`, produce
`S⁽ⁱ⁺¹⁾ → L`, where
`f⁽ⁱ⁺¹⁾ = fold(f⁽ⁱ⁾, r) : y ↦ [1-r, r] · [[x₁, -x₀], [-1, 1]] · [f⁽ⁱ⁾(x₀), f⁽ⁱ⁾(x₁)]`.

DEPRECATED naming: this is the pre-split single-step fold keyed only on `(h_i : i + 1 < ℓ + 𝓡)`
with output index hard-wired to `⟨i + 1, _⟩`. The canonical, externally-consumed entry point is
`fold` (below), which takes `{destIdx : Fin r} (h_destIdx : destIdx = i + 1) (h_destIdx_le)`.
All Prelude-internal recursion/proofs continue to use `fold_legacy`; external callers
(`Code`/`Compliance`/`Relations`/`QueryPhase`/`Soundness`) use the new `fold` (defined just
below this legacy version). -/
def fold_legacy (i : Fin r) (h_i : i + 1 < ℓ + 𝓡) (f : (sDomain 𝔽q β
    h_ℓ_add_R_rate) i → L) (r_chal : L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i + 1, by omega⟩) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y)
    let x₀ := fiberMap 0
    let x₁ := fiberMap 1
    let f_x₀ := f x₀
    let f_x₁ := f x₁
    exact f_x₀ * ((1 - r_chal) * x₁.val - r_chal) + f_x₁ * (r_chal - (1 - r_chal) * x₀.val)

def baseFoldMatrix (i : Fin r) (h_i : i + 1 < ℓ + 𝓡)
    (y : ↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩)) : Matrix (Fin 2) (Fin 2) L :=
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y)
  let x₀ := fiberMap 0
  let x₁ := fiberMap 1
  fun i j => match i, j with
  | 0, 0 => x₁
  | 0, 1 => -x₀
  | 1, 0 => -1
  | 1, 1 => 1

/-- The fold matrix as a `Nat`-indexed structural recursion on `steps`.

This is the explicit recursive construction used by the raw single-point matrix form. Peeling the
**last** fold (`Fin.dfoldl_succ_last`) at level `i + steps`,
`iterated_fold (steps + 1)` is one extra single-step `fold` applied to `iterated_fold steps`.
Translating that one step into matrix form yields the block/composition law:
`M_{steps+1}(y)[a][b] = baseFoldMatrix(i+steps, y)[a % 2][b / 2^steps]`
`  * M_{steps}(z_{b / 2^steps})[a / 2][b % 2^steps]`,
where `z_c = qMap_total_fiber(i+steps, 1, y)(c)` are the two single-step preimages of `y`,
the new (last) challenge occupies the **low** bit of the row index `a` (matching
`challengeTensorProduct`'s recursion), and the last quotient level occupies the **high**
bits of the column/fiber index `b` (matching `qMap_total_fiber`'s MSB convention).
The base case `steps = 0` is the `1 × 1` identity scalar `1`. -/
noncomputable def foldMatrixNat (i : Fin r) :
    (steps : ℕ) → (h_i_add_steps : i.val + steps < ℓ + 𝓡) →
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) →
    Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L
  | 0, _, _ => fun _ _ => 1
  | (n + 1), h, y =>
      let baseM : Matrix (Fin 2) (Fin 2) L :=
        baseFoldMatrix 𝔽q β ⟨i.val + n, by omega⟩ (h_i := by simp only; omega)
          (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
      let zMap : Fin 2 → (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + n, by omega⟩ :=
        qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
          (h_i_add_steps := by simp only; omega)
          (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
      fun a b =>
        let cBit : Fin 2 := ⟨b.val / 2 ^ n, by
          have hb : b.val < 2 ^ n * 2 :=
            Nat.lt_of_lt_of_eq b.isLt (by rw [pow_succ])
          exact Nat.div_lt_of_lt_mul hb⟩
        let bLow : Fin (2 ^ n) := ⟨b.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩
        let aBit : Fin 2 := ⟨a.val % 2, Nat.mod_lt _ (by omega)⟩
        let aHigh : Fin (2 ^ n) := ⟨a.val / 2, by
          have ha : a.val < 2 * 2 ^ n :=
            Nat.lt_of_lt_of_eq a.isLt (by rw [pow_succ, Nat.mul_comm])
          exact Nat.div_lt_of_lt_mul ha⟩
        baseM aBit cBit * foldMatrixNat i n (by omega) (zMap cBit) aHigh bLow

/-- `M_y` matrix which depends only on `y ∈ S^(i+ϑ)` (LEGACY `steps : Fin (ℓ + 1)` form).
The destination-keyed canonical `foldMatrix` uses a different row-bit convention. This compatibility
form retains the low-row-bit ordering of `foldMatrixNat`. -/
def foldMatrix_steps (i : Fin r) (steps : Fin (ℓ + 1)) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨↑i + steps, by apply Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩)
    : Matrix (Fin (2 ^ steps.val)) (Fin (2 ^ steps.val)) L :=
  foldMatrixNat 𝔽q β i steps.val h_i_add_steps y

/-- Agreement of the single-step `foldMatrixNat` with `baseFoldMatrix`: the recursion's
`steps = 1` value is exactly the base matrix (its old special-case branch). -/
lemma foldMatrixNat_one (i : Fin r) (h_i_add_steps : i.val + 1 < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + 1, by omega⟩)
    (a b : Fin (2 ^ 1)) :
    foldMatrixNat 𝔽q β i 1 h_i_add_steps y a b =
      baseFoldMatrix 𝔽q β i (h_i := by simpa using h_i_add_steps) y
        (Fin.cast (by norm_num) a) (Fin.cast (by norm_num) b) := by
  -- Unfold one recursion step; the `steps = 0` tail collapses to the scalar `1`.
  simp only [foldMatrixNat, pow_zero, Nat.div_one, Nat.mod_one, mul_one]
  -- Both sides are `baseFoldMatrix` of the same data; reconcile `i + 0 = i`, the `y`
  -- subtype lift, and the `Fin 2` indices (`a % 2 = a`, `b / 1 = b` for `a, b < 2`).
  congr 1
  all_goals apply Fin.ext
  all_goals simp only [Fin.coe_cast]
  all_goals omega

/-- Iterated fold over `steps` steps starting at domain index `i` (LEGACY signature, keyed on
`steps : Fin (ℓ + 1)` and `h_i_add_steps : i.val + steps < ℓ + 𝓡`).

DEPRECATED naming: the canonical, externally-consumed entry point is `iterated_fold` (below),
which takes `(steps : ℕ) {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps)
(h_destIdx_le : destIdx ≤ ℓ)`. All Prelude-internal recursion/proofs continue to use
`iterated_fold_steps`; external callers use the new `iterated_fold`. -/
def iterated_fold_steps (i : Fin r) (steps : Fin (ℓ + 1)) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin steps → L) :
    sDomain 𝔽q β h_ℓ_add_R_rate
      (⟨i + steps.val, Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩) → L := by
  let domain_type := sDomain 𝔽q β h_ℓ_add_R_rate
  let fold_func := fold_legacy 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let α (j : Fin (steps + 1)) := domain_type (⟨i + j.val, by omega⟩) → L
  let fold_step (j : Fin steps) (f_acc : α ⟨j, by omega⟩) : α j.succ := by
    unfold α domain_type at *
    intro x
    have fold_func := fold_func (i := ⟨i + j.val, by omega⟩) (h_i := by
      simp only
      omega
    ) (f_acc) (r_challenges j)
    exact fold_func x
  exact Fin.dfoldl (n := steps) (α := α) (f := fun i (accF : α ⟨i, by omega⟩) =>
    have fSucc : α ⟨i.succ, by omega⟩ := fold_step i accF
    fSucc) (init := f)

/-- **Iterated fold (destination-keyed compatibility form).** Public iterated fold with a natural step count
and explicit destination index `destIdx.val = i + steps`. The entry point consumed by
`Code`/`Compliance`/`Relations`/`QueryPhase`/`Soundness`; it packs `steps : ℕ` into
`Fin (ℓ + 1)` and re-indexes the legacy `iterated_fold_steps` result (via `cast`) to the
propositionally-equal `destIdx`. (Conflict resolution: adopted the `fork/main` `cast`-based
version.) -/
def iterated_fold (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin steps → L) :
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L := by
  have h_steps_le : steps < ℓ + 1 := by
    have hle : i.val + steps ≤ ℓ := by
      rw [← h_destIdx]
      exact h_destIdx_le
    omega
  have h_i_add_steps : i.val + steps < ℓ + 𝓡 := by
    have hle : i.val + steps ≤ ℓ := by
      rw [← h_destIdx]
      exact h_destIdx_le
    exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡))
  have hidx :
      (⟨i.val + steps, Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩ : Fin r) = destIdx :=
    Fin.ext h_destIdx.symm
  exact cast (congrArg (fun j => sDomain 𝔽q β h_ℓ_add_R_rate j → L) hidx)
    (iterated_fold_steps 𝔽q β (i := i) (steps := ⟨steps, h_steps_le⟩)
      (h_i_add_steps := h_i_add_steps) (f := f)
      (r_challenges := fun j => r_challenges ⟨j.val, by simpa using j.isLt⟩))

/-- **Congruence in the source index** of `iterated_fold`: transporting the start index `i = i'`
across the (equal-`.val`) domain re-casts the input function accordingly. -/
lemma iterated_fold_congr_source_index
    {i i' : Fin r} (h : i = i')
    (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx' : destIdx.val = i'.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) steps h_destIdx h_destIdx_le f r_challenges =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i') steps h_destIdx' h_destIdx_le
      (fun x => f (cast (h := by rw [h]) x)) r_challenges := by
  subst h
  simp only [cast_eq]

omit h_β₀_eq_1 in
/-- **Congruence in the destination index** of `iterated_fold`: transporting the destination index
`destIdx = destIdx'` across the (equal-`.val`) domain re-casts the evaluation point accordingly. -/
lemma iterated_fold_congr_dest_index
    {i : Fin r} (steps : ℕ) {destIdx destIdx' : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_destIdx_eq_destIdx' : destIdx = destIdx')
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
      (i := i) steps h_destIdx h_destIdx_le f r_challenges y =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx')
      (i := i) steps (by rw [← h_destIdx_eq_destIdx']; exact h_destIdx)
      (h_destIdx_le := by rw [← h_destIdx_eq_destIdx']; exact h_destIdx_le)
      f r_challenges (cast (h := by rw [h_destIdx_eq_destIdx']) y) := by
  subst h_destIdx_eq_destIdx'; rfl

omit h_β₀_eq_1 in
/-- **Congruence in the step count** of `iterated_fold`: transporting an equal step count
`steps = steps'` re-indexes the challenge function accordingly. -/
lemma iterated_fold_congr_steps_index
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_steps_eq_steps' : steps = steps')
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
      (i := i) steps h_destIdx h_destIdx_le f r_challenges y =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
      (i := i) steps' (by rw [← h_steps_eq_steps']; exact h_destIdx)
      (h_destIdx_le := h_destIdx_le)
      f (fun (cIdx : Fin steps') => r_challenges ⟨cIdx, by omega⟩) y := by
  subst h_steps_eq_steps'; rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **Peel the last fold step from `iterated_fold`.** Folding `n + 1` steps starting at
level `i` equals one single-step `fold` (at level `i + n`, with the last challenge
`r_challenges (last n)`) applied to the `n`-step iterated fold over the truncated
challenges. This is the structural `Fin.dfoldl` peel (`Fin.dfoldl_succ_last`) that drives
the inductive proof of Lemma 4.9. -/
theorem iterated_fold_succ_last (i : Fin ℓ) (n : ℕ)
    (h_i_add_steps : i.val + (n + 1) ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) → L)
    (r_challenges : Fin (n + 1) → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + (n + 1), by omega⟩)) :
    iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := ⟨n + 1, by omega⟩)
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i (n + 1) h_i_add_steps) f r_challenges y =
    fold_legacy 𝔽q β (i := ⟨i.val + n, by omega⟩)
      (h_i := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
      (f := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
        (steps := ⟨n, by omega⟩)
        (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i n (by omega)) f
        (fun j => r_challenges j.castSucc))
      (r_chal := r_challenges (Fin.last n))
      ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ := by
  unfold iterated_fold_steps
  simp only [Fin.val_mk]
  rw [Fin.dfoldl_succ_last]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- Generic peel of the **last** fold step from `iterated_fold`, for a general start
index `i : Fin r` (the `Fin ℓ`-restricted `iterated_fold_succ_last` is the `Fin ℓ`
specialization). Folding `n + 1` steps equals one single-step `fold` (at level `i + n`,
with the last challenge `r_challenges (last n)`) applied to the `n`-step iterated fold
over the truncated challenges. This is the structural `Fin.dfoldl_succ_last` peel. -/
theorem iterated_fold_succ_last_gen (i : Fin r) (n : ℕ)
    (h_steps : n + 1 < ℓ + 1)
    (h_i_add_steps : i.val + (n + 1) < ℓ + 𝓡)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin (n + 1) → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i.val + (n + 1), Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩)) :
    iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := ⟨n + 1, h_steps⟩) h_i_add_steps f r_challenges y =
    fold_legacy 𝔽q β (i := ⟨i.val + n, by omega⟩)
      (h_i := by simp only; omega)
      (f := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (steps := ⟨n, by omega⟩)
        (by simp only; omega) f
        (fun j => r_challenges j.castSucc))
      (r_chal := r_challenges (Fin.last n))
      ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ := by
  unfold iterated_fold_steps
  simp only [Fin.val_mk]
  rw [Fin.dfoldl_succ_last]
  rfl

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- Congruence for `fold` across a propositional start-index equality: aligning the two
applications by `Fin.ext`/`Subtype.ext` (proof-irrelevant `Fin`/membership components). -/
theorem fold_congr (i₁ i₂ : Fin r) (hidx : i₁.val = i₂.val)
    (h₁ : i₁.val + 1 < ℓ + 𝓡) (h₂ : i₂.val + 1 < ℓ + 𝓡)
    (f₁ : sDomain 𝔽q β h_ℓ_add_R_rate (i := i₁) → L)
    (f₂ : sDomain 𝔽q β h_ℓ_add_R_rate (i := i₂) → L)
    (hf : ∀ (x₁ : sDomain 𝔽q β h_ℓ_add_R_rate (i := i₁))
            (x₂ : sDomain 𝔽q β h_ℓ_add_R_rate (i := i₂)),
            x₁.val = x₂.val → f₁ x₁ = f₂ x₂)
    (c : L)
    (y₁ : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i₁.val + 1, by omega⟩))
    (y₂ : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i₂.val + 1, by omega⟩))
    (hy : y₁.val = y₂.val) :
    fold_legacy 𝔽q β (i := i₁) (h_i := h₁) f₁ c y₁ =
      fold_legacy 𝔽q β (i := i₂) (h_i := h₂) f₂ c y₂ := by
  have hi : i₁ = i₂ := Fin.ext hidx
  subst hi
  have hyeq : y₁ = y₂ := Subtype.ext hy
  subst hyeq
  have hfeq : f₁ = f₂ := by funext x; exact hf x x rfl
  subst hfeq
  rfl

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- Apply a `cast` of an `sDomain`-indexed function to a point at the (equal-`.val`) other
index: the cast on the function type is absorbed into lifting the argument's underlying value. -/
theorem sDomain_fn_cast_apply (a b : ℕ) (ha : a < r) (hb : b < r) (h : a = b)
    {hcast : (sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨a, ha⟩) → L)
           = (sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨b, hb⟩) → L)}
    (g : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨a, ha⟩) → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨b, hb⟩))
    (z : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨a, ha⟩))
    (hz : z.val = y.val) :
    cast hcast g y = g z := by
  subst h
  have : y = z := Subtype.ext hz.symm
  subst this
  simp only [cast_eq]

set_option maxHeartbeats 4000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- Cast-free core of `iterated_fold_transitivity`: both folds land in the **same** index
type `⟨i + s₁ + s₂, _⟩`, compared pointwise at a `y` whose underlying value matches. The
`Fin.dfoldl` append/split law, by induction on the second segment `s2`. -/
lemma iterated_fold_transitivity_castfree
    (i : Fin r) (s1 s2 : ℕ)
    (hs1 : s1 < ℓ + 1) (hs2 : s2 < ℓ + 1) (hs12 : s1 + s2 < ℓ + 1)
    (h_bounds : i.val + s1 + s2 ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges₁ : Fin s1 → L) (r_challenges₂ : Fin s2 → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + s1 + s2, by omega⟩)) :
    iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val + s1, by omega⟩) (steps := ⟨s2, hs2⟩)
      (h_i_add_steps := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
      (iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := ⟨s1, hs1⟩)
        (h_i_add_steps := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega) f r_challenges₁) r_challenges₂ y =
    iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := ⟨s1 + s2, hs12⟩)
      (h_i_add_steps := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
      f (Fin.append r_challenges₁ r_challenges₂)
      ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ := by
  induction s2 with
  | zero =>
    -- LHS: the outer 0-step fold collapses to its init.
    conv_lhs => unfold iterated_fold_steps; rw [Fin.dfoldl_zero]
    -- Both sides become `Fin.dfoldl s1 …` over the same motive (`s1 + 0 ≡ s1` defeq); the
    -- challenge functions agree since `Fin.append r₁ r₂ j = r₁ j` for `j : Fin (s1 + 0)`.
    conv_rhs => unfold iterated_fold_steps
    have happ : (Fin.append r_challenges₁ r_challenges₂ : Fin (s1 + 0) → L) = r_challenges₁ := by
      funext j
      rw [Fin.append_right_nil r_challenges₁ r_challenges₂ rfl]
      rfl
    rw [happ]
    rfl
  | succ n ih =>
    -- Peel the last step of the LHS via the generic `Fin r` peel.
    rw [iterated_fold_succ_last_gen 𝔽q β (i := ⟨i.val + s1, by
          apply Nat.lt_of_le_of_lt (m := ℓ) (by omega) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩)
        (n := n)
        (h_steps := by omega)
        (h_i_add_steps := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)]
    -- Peel the RHS, viewing `⟨s1+(n+1)⟩` as `⟨(s1+n)+1⟩` (defeq via `Nat.add_succ`). The
    -- equation's LHS is stated as the goal's RHS term verbatim so `rw [hrhs]` matches; the
    -- `iterated_fold_succ_last_gen` proof goes through by defeq (`s1+(n+1) ≡ (s1+n)+1`).
    have hrhs :
        iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
          (steps := ⟨s1 + (n + 1), hs12⟩)
          (by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
          f (Fin.append r_challenges₁ r_challenges₂)
          ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ =
        fold_legacy 𝔽q β (i := ⟨i.val + (s1 + n), by omega⟩)
          (h_i := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
          (f := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
            (steps := ⟨s1 + n, by omega⟩)
            (by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega) f
            (fun j => (Fin.append r_challenges₁ r_challenges₂) j.castSucc))
          (r_chal := (Fin.append r_challenges₁ r_challenges₂) (Fin.last (s1 + n)))
          ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ :=
      iterated_fold_succ_last_gen 𝔽q β (i := i) (n := s1 + n)
        (h_steps := by omega)
        (h_i_add_steps := by have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
        (f := f)
        (r_challenges := (Fin.append r_challenges₁ r_challenges₂ : Fin (s1 + (n + 1)) → L))
        (y := ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩)
    rw [hrhs]
    -- The two `fold`s are at the same level (`(i+s1)+n ≡ i+(s1+n)`). Reconcile the last
    -- challenge `r₂ (last n) = (append r₁ r₂) (last (s1+n))` and the inner fold (via the IH).
    have happ_last :
        (Fin.append r_challenges₁ r_challenges₂ : Fin (s1 + (n + 1)) → L) (Fin.last (s1 + n)) =
          r_challenges₂ (Fin.last n) := by
      have h := Fin.append_right r_challenges₁ r_challenges₂ (Fin.last n)
      rw [← h]
      rfl
    -- Truncation of the appended challenge agrees with appending the truncated tail.
    have happ_trunc :
        (fun j : Fin (s1 + n) =>
            (Fin.append r_challenges₁ r_challenges₂ : Fin (s1 + (n + 1)) → L) j.castSucc) =
          Fin.append r_challenges₁ (fun j => r_challenges₂ j.castSucc) := by
      funext j
      refine Fin.addCases (fun l => ?_) (fun rr => ?_) j
      · rw [Fin.append_left]
        rw [show (Fin.castAdd n l : Fin (s1 + n)).castSucc
              = (Fin.castAdd (n + 1) l : Fin (s1 + (n + 1))) from by apply Fin.ext; simp]
        rw [Fin.append_left]
      · rw [Fin.append_right]
        rw [show (Fin.natAdd s1 rr : Fin (s1 + n)).castSucc
              = (Fin.natAdd s1 rr.castSucc : Fin (s1 + (n + 1))) from by apply Fin.ext; simp]
        rw [Fin.append_right]
    rw [happ_last, happ_trunc]
    apply fold_congr 𝔽q β (hidx := by simp only; omega)
    · -- hf: pointwise inner-fold equality via the IH
      intro x₁ x₂ hx
      rw [ih (by omega) (by omega) (by omega) (fun j => r_challenges₂ j.castSucc)
        ⟨x₁.val, by have := x₁.property; simpa only [Nat.add_assoc] using this⟩]
      congr 1
      apply Subtype.ext
      simpa only using hx
    · -- hy
      rfl

set_option maxHeartbeats 4000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/--
Transitivity of iterated_fold : folding for `steps₁` and then for `steps₂`
equals folding for `steps₁ + steps₂` with concatenated challenges.
-/
lemma iterated_fold_steps_transitivity
    (i : Fin r) (steps₁ steps₂ : Fin (ℓ + 1))
    (h_bounds : i.val + steps₁ + steps₂ ≤ ℓ) -- A single, sufficient bounds check
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges₁ : Fin steps₁ → L) (r_challenges₂ : Fin steps₂ → L) :
    -- LHS : The nested fold (folding twice)
    have hi1 : i.val + steps₁ ≤ ℓ := by exact le_of_add_right_le h_bounds
    have hi2 : i.val + steps₂ ≤ ℓ := by
      rw [Nat.add_assoc, Nat.add_comm steps₁ steps₂, ←Nat.add_assoc] at h_bounds
      exact le_of_add_right_le h_bounds
    have hi12 : steps₁ + steps₂ < ℓ + 1 := by
      apply Nat.lt_succ_of_le; rw [Nat.add_assoc] at h_bounds;
      exact Nat.le_of_add_left_le h_bounds
    let lhs := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val + steps₁, by -- ⊢ ↑i + ↑steps₁ < r
        apply Nat.lt_of_le_of_lt (m := ℓ) (hi1) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩)
      (steps := steps₂)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := by
        exact iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps₁)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; exact hi1) (f := f)
          (r_challenges := r_challenges₁)
      ) r_challenges₂
    let rhs := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := ⟨steps₁ + steps₂, hi12⟩)
      (h_i_add_steps := by
        simp only; rw [←Nat.add_assoc]; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := f) (r_challenges := Fin.append r_challenges₁ r_challenges₂)
    lhs = by
      simp only [←Nat.add_assoc] at ⊢ rhs
      exact rhs := by
  simp only
  funext y
  -- Reduce the LHS to the cast-free core (`iterated_fold_transitivity_castfree`).
  rw [iterated_fold_transitivity_castfree 𝔽q β i steps₁.val steps₂.val steps₁.isLt steps₂.isLt
    (by apply Nat.lt_succ_of_le; rw [Nat.add_assoc] at h_bounds;
        exact Nat.le_of_add_left_le h_bounds)
    h_bounds f r_challenges₁ r_challenges₂ y]
  -- The RHS still carries the `id (h.mp …)` transport on the function type. Normalize
  -- `id (Eq.mp h ·)` to `cast h ·` with a *targeted* `conv` (avoids traversing the heavy
  -- fold term, which a full `simp only` would do), then discharge the `cast` pointwise.
  conv_rhs => rw [id_eq, eq_mp_eq_cast]
  exact Eq.symm (sDomain_fn_cast_apply 𝔽q β
    (a := i.val + (steps₁.val + steps₂.val))
    (b := i.val + steps₁.val + steps₂.val)
    (ha := by omega) (hb := by omega) (h := by omega) (g := _) (y := _)
    (z := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
    (hz := rfl))

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/--
Transitivity of the public `iterated_fold` API: folding for `steps₁` and then for `steps₂`
equals folding once for `steps₁ + steps₂` with appended challenges.
-/
lemma iterated_fold_transitivity
    (i : Fin r) {midIdx destIdx : Fin r} (steps₁ steps₂ : ℕ)
    {h_midIdx : midIdx.val = i.val + steps₁} {h_midIdx_le : midIdx ≤ ℓ}
    (h_destIdx : destIdx.val = midIdx.val + steps₂) {h_destIdx_le : destIdx ≤ ℓ}
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges₁ : Fin steps₁ → L) (r_challenges₂ : Fin steps₂ → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := steps₂) (destIdx := destIdx)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps₁) (destIdx := midIdx)
        (h_destIdx := h_midIdx) (h_destIdx_le := h_midIdx_le)
        (f := f) (r_challenges := r_challenges₁))
      (r_challenges := r_challenges₂) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps₁ + steps₂) (destIdx := destIdx)
      (h_destIdx := by rw [h_destIdx, h_midIdx, Nat.add_assoc])
      (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := Fin.append r_challenges₁ r_challenges₂) := by
  have h_full : destIdx.val = i.val + steps₁ + steps₂ := by
    rw [h_destIdx, h_midIdx, Nat.add_assoc]
  have h_mid_bound : i.val + steps₁ < r := by
    rw [← h_midIdx]
    exact midIdx.isLt
  have h_dest_bound : i.val + steps₁ + steps₂ < r := by
    rw [← h_full]
    exact destIdx.isLt
  have h_mid_eq : midIdx = (⟨i.val + steps₁, h_mid_bound⟩ : Fin r) :=
    Fin.eq_of_val_eq h_midIdx
  have h_dest_eq : destIdx = (⟨i.val + steps₁ + steps₂, h_dest_bound⟩ : Fin r) :=
    Fin.eq_of_val_eq h_full
  subst h_mid_eq
  subst h_dest_eq
  funext y
  unfold iterated_fold
  simp only [Fin.val_mk, id_eq, eq_mp_eq_cast, eq_mpr_eq_cast, eqRec_eq_cast, cast_cast,
    cast_eq]
  rw [iterated_fold_steps_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps₁ := ⟨steps₁, by
      have hle : i.val + steps₁ ≤ ℓ := le_of_add_right_le h_destIdx_le
      omega⟩)
    (steps₂ := ⟨steps₂, by
      have hle : i.val + steps₁ + steps₂ ≤ ℓ := h_destIdx_le
      omega⟩)
    (h_bounds := h_destIdx_le)
    (f := f) (r_challenges₁ := r_challenges₁) (r_challenges₂ := r_challenges₂)]
  conv_lhs => rw [id_eq, eq_mp_eq_cast]

/-- Tensor product of challenge vectors : for a local fold length `steps`,
⨂_{j=0}^{steps-1}(1-r_j, r_j). -/
def challengeTensorProduct (steps : ℕ) (r_challenges : Fin steps → L) : Vector L (2 ^ steps) :=
  if h_steps_zero : steps = 0 then
    -- Base case : steps = 0, return single element vector [1]
    by
      rw [h_steps_zero, pow_zero]
      exact ⟨#[1], rfl⟩
  else
    -- Recursive case : compute tensor product iteratively
    Nat.rec
      (motive := fun k => k ≤ steps → Vector L (2^k))
      (fun _ => ⟨#[1], rfl⟩) -- Base : empty tensor product = [1]
      (fun k ih h_k_le =>
        -- Inductive step : extend tensor product by one more challenge
        let prev_vec := ih (Nat.le_trans (Nat.le_succ k) h_k_le)
        let r_k := r_challenges ⟨k, by omega⟩
        -- Each element of prev_vec gets multiplied by both (1-r_k) and r_k
        Vector.ofFn (fun idx : Fin (2^k.succ) =>
          let prev_idx : Fin (2^k) := ⟨idx.val / 2, by
            have h_succ : 2^k.succ = 2 * 2^k := by rw [pow_succ, mul_comm]
            rw [h_succ] at idx
            have : idx.val < 2 * 2^k := idx.isLt
            apply Nat.div_lt_of_lt_mul;
            omega⟩
          let bit := idx.val % 2
          let prev_val := prev_vec.get prev_idx
          if bit = 0 then (1 - r_k) * prev_val else r_k * prev_val))
      steps (le_refl steps)

/-- The inner `Nat.rec` accumulator of `challengeTensorProduct` (for nonzero outer `steps`),
exposed as a structural recursion so we can reason about it compositionally. -/
def ctpAux (m : ℕ) (r_challenges : Fin m → L) : (k : ℕ) → k ≤ m → Vector L (2 ^ k)
  | 0, _ => ⟨#[1], rfl⟩
  | (k + 1), hk =>
      Vector.ofFn (fun idx : Fin (2 ^ (k + 1)) =>
        let prev_idx : Fin (2 ^ k) := ⟨idx.val / 2, by
          exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩
        if idx.val % 2 = 0
          then (1 - r_challenges ⟨k, by omega⟩) * (ctpAux m r_challenges k (by omega)).get prev_idx
          else r_challenges ⟨k, by omega⟩ * (ctpAux m r_challenges k (by omega)).get prev_idx)

/-- The raw inner `Nat.rec` accumulator equals the named `ctpAux`, at every level `k ≤ m`. -/
theorem natRec_ctp_eq_ctpAux (m : ℕ) (r_challenges : Fin m → L) :
    ∀ (k : ℕ) (hk : k ≤ m),
      (Nat.rec (motive := fun k => k ≤ m → Vector L (2 ^ k)) (fun _ => ⟨#[1], rfl⟩)
        (fun k ih h_k_le =>
          let prev_vec := ih (Nat.le_trans (Nat.le_succ k) h_k_le)
          let r_k := r_challenges ⟨k, by omega⟩
          Vector.ofFn (fun idx : Fin (2 ^ k.succ) =>
            let prev_idx : Fin (2 ^ k) := ⟨idx.val / 2, by
              have h_succ : 2 ^ k.succ = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
              rw [h_succ] at idx
              have : idx.val < 2 * 2 ^ k := idx.isLt
              apply Nat.div_lt_of_lt_mul
              omega⟩
            let bit := idx.val % 2
            let prev_val := prev_vec.get prev_idx
            if bit = 0 then (1 - r_k) * prev_val else r_k * prev_val))
        k hk)
      = ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r_challenges k hk := by
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
    intro hk
    show (Vector.ofFn _ : Vector L (2 ^ (k + 1))) = _
    simp only [ctpAux]
    congr 1
    funext idx
    rw [ih (by omega)]

/-- `challengeTensorProduct` (nonzero `steps`) is exactly its named inner recursion. -/
theorem challengeTensorProduct_eq_ctpAux (m : ℕ) (hm : m ≠ 0) (r_challenges : Fin m → L) :
    challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r_challenges
      = ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r_challenges m (le_refl m) := by
  rw [challengeTensorProduct]
  simp only [hm, ↓reduceDIte]
  exact natRec_ctp_eq_ctpAux m r_challenges m (le_refl m)

/-- `ctpAux` get only depends on the challenges at indices `< k`. -/
theorem ctpAux_congr (m m' : ℕ) (r' : Fin m → L) (r'' : Fin m' → L) :
    ∀ (k : ℕ), (∀ (j : ℕ) (hm : j < m) (hm' : j < m'), j < k → r' ⟨j, hm⟩ = r'' ⟨j, hm'⟩) →
      ∀ (hk : k ≤ m) (hk' : k ≤ m') (idx : Fin (2 ^ k)),
        (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r' k hk).get idx
          = (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m' r'' k hk').get idx := by
  intro k
  induction k with
  | zero => intro _ _ _ idx; fin_cases idx; rfl
  | succ k ih =>
    intro hagree hk hk' idx
    simp only [ctpAux, Vector.get_ofFn]
    have hrk : r' ⟨k, by omega⟩ = r'' ⟨k, by omega⟩ := hagree k (by omega) (by omega) (by omega)
    have hprev : (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r' k (by omega)).get ⟨idx.val / 2, by
        exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩
      = (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m' r'' k (by omega)).get ⟨idx.val / 2, by
        exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩ :=
      ih (fun j hmj hm'j hjk => hagree j hmj hm'j (by omega)) (by omega) (by omega) _
    rw [hrk, hprev]

set_option maxHeartbeats 2000000 in
/-- Tensor product recursion (entry form): low bit selects last challenge, high bits index the
`n`-step tensor over truncated challenges. -/
theorem challengeTensorProduct_succ_get (n : ℕ) (r_challenges : Fin (n + 1) → L)
    (idx : Fin (2 ^ (n + 1))) :
    (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) (n + 1) r_challenges).get idx =
      (if idx.val % 2 = 0 then (1 - r_challenges (Fin.last n)) else r_challenges (Fin.last n)) *
        (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) n
          (fun j => r_challenges j.castSucc)).get
          ⟨idx.val / 2, by
            exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩ := by
  rw [challengeTensorProduct_eq_ctpAux (n + 1) (by omega) r_challenges]
  simp only [ctpAux, Vector.get_ofFn]
  have hlast : r_challenges ⟨n, by omega⟩ = r_challenges (Fin.last n) := rfl
  rw [hlast]
  by_cases hn : n = 0
  · subst hn
    fin_cases idx <;> split <;> rfl
  · rw [challengeTensorProduct_eq_ctpAux n hn (fun j => r_challenges j.castSucc)]
    have hidxlt : idx.val / 2 < 2 ^ n :=
      Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))
    have hbridge :
        (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) (n + 1) r_challenges n (by omega)).get ⟨idx.val / 2, hidxlt⟩
        = (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) n (fun j => r_challenges j.castSucc) n (by omega)).get
            ⟨idx.val / 2, hidxlt⟩ := by
      apply ctpAux_congr
      intro j hmj hm'j hjk
      rfl
    rw [hbridge]
    split <;> rfl

/-- Evaluation vector [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T -/
def fiberEvaluationMapping (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨↑i + steps, by apply Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩)
    : Fin (2 ^ steps) → L :=
  -- Get the fiber points
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (y := y)

  -- Evaluate f at each fiber point
  fun idx => f (fiberMap idx)

/-- Matrix-vector multiplication form of iterated fold : For a local `steps > 0`,
`∀ i ∈ {0, ..., l-steps}`,
`y ∈ S^(i+steps)`,
`fold(f^(i), r_0, ..., r_{steps-1})(y) = [⨂_{j=0}^{steps-1}(1-r_j, r_j)] • M_y`
`• [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`,
where the right-hand vector's values `(x_0, ..., x_{2 ^ steps-1})` represent the fiber
`(q^(i+steps-1) ∘ ... ∘ q^(i))⁻¹({y}) ⊂ S^(i)`.
-/
def localized_fold_matrix_form_legacy (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (r_challenges : Fin steps → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩)
  (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  L := by
    let challenge_vec : Vector L (2 ^ steps) := challengeTensorProduct (L := L)
      (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps r_challenges
    let fold_mat := foldMatrix_steps 𝔽q β (i := ⟨i, by omega⟩) ⟨steps, by omega⟩
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping
    let intermediate_vec := Vector.ofFn intermediate_fn
    simp only at intermediate_vec
    exact Vector.dotProduct challenge_vec intermediate_vec

/-- Wrapper of `localized_fold_matrix_form` with `fiber_eval_mapping` being specified
explicitly. -/
def localized_fold_eval (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) : L := by
    let fiber_eval_mapping := fiberEvaluationMapping 𝔽q β (steps := steps)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f y
    exact localized_fold_matrix_form_legacy 𝔽q β (i := i) steps h_i_add_steps r_challenges y
      fiber_eval_mapping

/-- Split a sum over `Fin (2^(n+1))` into the high bit `c ∈ Fin 2` and the low `n` bits
`b ∈ Fin (2^n)`, where `idx = c * 2^n + b`. -/
theorem sum_fin_pow_succ_split {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : Fin (2 ^ (n + 1)) → M) :
    ∑ idx : Fin (2 ^ (n + 1)), g idx =
      ∑ c : Fin 2, ∑ b : Fin (2 ^ n),
        g ⟨c.val * 2 ^ n + b.val, by
          have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
          have hc : c.val < 2 := c.isLt
          have hb : b.val < 2 ^ n := b.isLt
          rw [h2]; nlinarith [Nat.mul_le_mul_right (2 ^ n) (Nat.le_pred_of_lt hc)]⟩ := by
  have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (i := fun idx => (⟨idx.val / 2 ^ n, by
        have : idx.val < 2 ^ n * 2 := by rw [← h2]; exact idx.isLt
        exact Nat.div_lt_of_lt_mul (by omega)⟩,
      ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩))
    (j := fun p => ⟨p.1.val * 2 ^ n + p.2.val, by
        have hc : p.1.val < 2 := p.1.isLt
        have hb : p.2.val < 2 ^ n := p.2.isLt
        rw [h2]; nlinarith [Nat.mul_le_mul_right (2 ^ n) (Nat.le_pred_of_lt hc)]⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro idx _; exact Finset.mem_univ _
  · intro p _; exact Finset.mem_univ _
  · intro idx _
    apply Fin.ext; simp only
    have hdm := Nat.div_add_mod idx.val (2 ^ n)
    have hc : idx.val / 2 ^ n * 2 ^ n = 2 ^ n * (idx.val / 2 ^ n) := Nat.mul_comm _ _
    omega
  · intro p _
    apply Prod.ext
    · apply Fin.ext; simp only
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
        Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]
    · apply Fin.ext; simp only
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2.isLt]
  · intro idx _
    congr 1
    apply Fin.ext; simp only
    have hdm := Nat.div_add_mod idx.val (2 ^ n)
    have hc : idx.val / 2 ^ n * 2 ^ n = 2 ^ n * (idx.val / 2 ^ n) := Nat.mul_comm _ _
    omega

set_option maxHeartbeats 2000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- `localized_fold_eval` as an explicit double sum over the challenge tensor and fold matrix. -/
theorem localized_fold_eval_eq_sum (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) :
    localized_fold_eval 𝔽q β i (steps := steps) (h_i_add_steps := h_i_add_steps) f r_challenges y =
      ∑ a : Fin (2 ^ steps),
        (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps r_challenges).get a *
          ∑ b : Fin (2 ^ steps),
            foldMatrixNat 𝔽q β ⟨i, by omega⟩ steps
              (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y a b *
              f (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
                (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := y) b) := by
  unfold localized_fold_eval localized_fold_matrix_form_legacy fiberEvaluationMapping foldMatrix_steps
  simp only
  rw [Vector.dotProduct_eq_root_dotProduct]
  unfold _root_.dotProduct
  simp only [Vector.get_ofFn]
  rfl

/-- Split a sum over `Fin (2^(n+1))` into the low bit `lo ∈ Fin 2` and the high `n` bits
`hi ∈ Fin (2^n)`, where `idx = lo + 2 * hi`. -/
theorem sum_fin_pow_succ_split_low {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : Fin (2 ^ (n + 1)) → M) :
    ∑ idx : Fin (2 ^ (n + 1)), g idx =
      ∑ lo : Fin 2, ∑ hi : Fin (2 ^ n),
        g ⟨lo.val + 2 * hi.val, by
          have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
          have hlo : lo.val < 2 := lo.isLt
          have hhi : hi.val < 2 ^ n := hi.isLt
          rw [h2]; omega⟩ := by
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (i := fun idx => (⟨idx.val % 2, Nat.mod_lt _ (by omega)⟩, ⟨idx.val / 2, by
        have : idx.val < 2 * 2 ^ n := by rw [← h2]; exact idx.isLt
        exact Nat.div_lt_of_lt_mul (by omega)⟩))
    (j := fun p => ⟨p.1.val + 2 * p.2.val, by
        have hlo : p.1.val < 2 := p.1.isLt
        have hhi : p.2.val < 2 ^ n := p.2.isLt
        rw [h2]; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro idx _; exact Finset.mem_univ _
  · intro p _; exact Finset.mem_univ _
  · intro idx _
    apply Fin.ext; simp only
    omega
  · intro p _
    apply Prod.ext
    · apply Fin.ext; simp only
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt p.1.isLt
    · apply Fin.ext; simp only
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2), Nat.div_eq_of_lt p.1.isLt, Nat.zero_add]
  · intro idx _
    congr 1
    apply Fin.ext; simp only
    omega

set_option maxHeartbeats 2000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- One-step recursion of `foldMatrixNat` at an entry. -/
theorem foldMatrixNat_succ_apply (i : Fin r) (n : ℕ) (h : i.val + (n + 1) < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + (n + 1), by omega⟩)
    (a b : Fin (2 ^ (n + 1))) :
    foldMatrixNat 𝔽q β i (n + 1) h y a b =
      baseFoldMatrix 𝔽q β ⟨i.val + n, by omega⟩ (h_i := by simp only; omega)
        (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
        ⟨a.val % 2, Nat.mod_lt _ (by omega)⟩
        ⟨b.val / 2 ^ n, Nat.div_lt_of_lt_mul (by have e : 2 ^ (n + 1) = 2 * 2 ^ n := (by rw [pow_succ, Nat.mul_comm]); have := b.isLt; omega)⟩ *
      foldMatrixNat 𝔽q β i n (show i.val + n < ℓ + 𝓡 by omega)
        (qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
          (h_i_add_steps := by simp only; omega)
          (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
          ⟨b.val / 2 ^ n, Nat.div_lt_of_lt_mul (by have e : 2 ^ (n + 1) = 2 * 2 ^ n := (by rw [pow_succ, Nat.mul_comm]); have := b.isLt; omega)⟩)
        ⟨a.val / 2, Nat.div_lt_of_lt_mul (by have e : 2 ^ (n + 1) = 2 * 2 ^ n := (by rw [pow_succ, Nat.mul_comm]); have := a.isLt; omega)⟩
        ⟨b.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ := by
  rfl

set_option maxHeartbeats 4000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- RHS recursion of `localized_fold_eval`: the `(n+1)`-step localized fold evaluation at `y`
equals one single-step `fold` (at level `i + n`, last challenge `r_challenges (last n)`) applied
to the `n`-step localized fold evaluation over the truncated challenges. -/
theorem localized_fold_eval_succ (i : Fin ℓ) (n : ℕ) (h_i_add_steps : i.val + (n + 1) ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
    (r_challenges : Fin (n + 1) → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + (n + 1), by omega⟩) :
    localized_fold_eval 𝔽q β i (steps := n + 1) (h_i_add_steps := h_i_add_steps) f
        r_challenges y =
      fold_legacy 𝔽q β (i := ⟨i.val + n, by omega⟩)
        (h_i := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
        (f := localized_fold_eval 𝔽q β i (steps := n) (h_i_add_steps := by omega) f
              (fun j => r_challenges j.castSucc))
        (r_chal := r_challenges (Fin.last n))
        ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ := by
  rw [localized_fold_eval_eq_sum]
  conv_rhs => unfold fold_legacy
  simp only
  rw [localized_fold_eval_eq_sum, localized_fold_eval_eq_sum]
  rw [sum_fin_pow_succ_split_low (r := r) (ℓ := ℓ) (𝓡 := 𝓡) n]
  conv_lhs =>
    enter [2, lo, 2, hi]
    rw [challengeTensorProduct_succ_get, sum_fin_pow_succ_split (n := n)]
    enter [2, 2, c, 2, bL]
    rw [foldMatrixNat_succ_apply,
      qMap_total_fiber_succ_peel_last 𝔽q β (i := i) (n := n) (h_i_add_steps := h_i_add_steps)]
  have e1 : ∀ x : Fin (2^n), (2 * (x:ℕ)) / 2 = (x:ℕ) := fun x => by omega
  have e2 : ∀ x : Fin (2^n), (1 + 2 * (x:ℕ)) / 2 = (x:ℕ) := fun x => by omega
  have e3 : ∀ x : Fin (2^n), (2^n + (x:ℕ)) / 2^n = 1 := fun x => by
    rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos n), Nat.div_eq_of_lt x.isLt]
  have e4 : ∀ x : Fin (2^n), (2^n + (x:ℕ)) % 2^n = (x:ℕ) := fun x => by
    rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt x.isLt
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    Nat.zero_mul, Nat.one_mul, Nat.zero_add,
    Nat.add_mul_mod_self_left,
    Nat.mul_mod_right, e1, e2, e3, e4,
    Nat.div_eq_of_lt (Fin.is_lt _), Nat.mod_eq_of_lt (Fin.is_lt _),
    if_true, Nat.one_ne_zero, if_false]
  simp only [baseFoldMatrix, Fin.eta, neg_mul, one_mul]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, mul_neg, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x_1 _
  simp only [Fin.mk_zero, Fin.mk_one]
  ring

set_option maxHeartbeats 2000000 in
seal sDomain normalizedW intermediateEvaluationPoly in
/-- Base case of the localized fold evaluation: zero steps is just `f` at `y`. -/
theorem localized_fold_eval_zero (i : Fin ℓ) (h_i_add_steps : i.val + 0 ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
    (r_challenges : Fin 0 → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + 0, by omega⟩) :
    localized_fold_eval 𝔽q β i (steps := 0) (h_i_add_steps := h_i_add_steps) f r_challenges y
      = f ⟨y.val, by have := y.property; simpa only [Nat.add_zero] using this⟩ := by
  have hsub : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
  rw [localized_fold_eval_eq_sum]
  rw [Fintype.sum_subsingleton _ (0 : Fin (2^0))]
  rw [Fintype.sum_subsingleton _ (0 : Fin (2^0))]
  have hctp : (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) 0 r_challenges).get
      (0 : Fin (2 ^ 0)) = 1 := rfl
  have hfm : foldMatrixNat 𝔽q β ⟨↑i, by omega⟩ 0
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i 0 h_i_add_steps) y (0 : Fin (2^0)) (0 : Fin (2^0)) = 1 := rfl
  have hfib : qMap_total_fiber 𝔽q β (i := ⟨↑i, by omega⟩) (steps := 0)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i 0 h_i_add_steps)
      (y := y) (0 : Fin (2^0)) = ⟨y.val, by have := y.property; simpa only [Nat.add_zero] using this⟩ := by
    simp only [qMap_total_fiber, ↓reduceDIte]
    apply Subtype.ext
    simp
  rw [hctp, hfm, hfib, one_mul, one_mul]

set_option maxHeartbeats 4000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **Lemma 4.9 (LEGACY form).** The legacy iterated fold equals the localized fold evaluation
via matmul form. This remains the proved matrix statement for the legacy `challengeTensorProduct`
row order. -/
theorem iterated_fold_steps_eq_matrix_form (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) :
    (iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by apply Nat.lt_succ_of_le; exact Nat.le_of_add_left_le h_i_add_steps⟩)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f
      r_challenges ⟨y, by exact Submodule.coe_mem y⟩) =
    localized_fold_eval 𝔽q β i (steps := steps) (h_i_add_steps := h_i_add_steps) f
      r_challenges (y := ⟨y, by exact Submodule.coe_mem y⟩) := by
  induction steps with
  | zero =>
    rw [localized_fold_eval_zero]
    unfold iterated_fold_steps
    rw [Fin.dfoldl_zero]
  | succ n ih =>
    rw [iterated_fold_succ_last 𝔽q β i n h_i_add_steps,
      localized_fold_eval_succ 𝔽q β i n h_i_add_steps]
    congr 1
    funext y'
    exact ih (by omega) f (fun j => r_challenges j.castSucc) y'

/-!
### Canonical intermediate-basis reconstruction

Pinned CompPoly now owns this change-of-basis API. Keep the historical Binius names as aliases
and preserve the bounded-index wrappers below. Provenance is recorded in
`scripts/integration/binius-basis-consolidation.json`.
-/

export AdditiveNTT (
    natDegree_qMap
    qMap_ne_zero
    degree_qMap
    degree_intermediateNovelBasisX
    degree_intermediateEvaluationPoly_lt
    intermediateBasisVectors
    IntermediateCoeffVecSpace
    intermediateToCoeffsVec
    intermediateChangeOfBasisMatrix
    intermediateChangeOfBasisMatrix_lower_triangular
    intermediateChangeOfBasisMatrix_diag_ne_zero
    intermediateChangeOfBasisMatrix_det_ne_zero
    intermediateChangeOfBasisMatrix_invertible
    monomialToINovelCoeffs
    iNovelToMonomialCoeffs
    getINovelCoeffs
    monomialToINovel_iNovelToMonomial_inverse
    iNovelToMonomial_monomialToINovel_inverse
    intermediateEvaluationPoly_from_inovel_coeffs_eq_self)

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Compatibility form using the historical bounded source and step indices. -/
lemma natDegree_intermediateNormVpoly_nat
    (i : Fin (ℓ + 1)) {k : ℕ} (hk : k < ℓ - i.val + 1) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val, by omega⟩)
      (k := k) (h_k := by change i.val + k ≤ ℓ; omega)).natDegree = 2 ^ k := by
  exact AdditiveNTT.natDegree_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
    ⟨i.val, by omega⟩ (h_k := by change i.val + k ≤ ℓ; omega)

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Compatibility form of the canonical intermediate-degree theorem. -/
lemma degree_intermediateNormVpoly
    (i : Fin (ℓ + 1)) (k : Fin (ℓ - i.val + 1)) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val, by omega⟩)
      (k := k.val) (h_k := by change i.val + k.val ≤ ℓ; omega)).degree = (2 ^ k.val : WithBot ℕ) := by
  exact AdditiveNTT.degree_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
    ⟨i.val, by omega⟩ (h_k := by change i.val + k ≤ ℓ; omega)



omit [CharP L 2] [NeZero ℓ] in
/-- Lemma 4.13 (LEGACY form): if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾, then
`fold_legacy(f⁽ⁱ⁾, r_chal)` is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾. The new-API
`fold_advances_evaluation_poly` (below) is the `{destIdx}`-keyed restatement consumed by `Code`. -/
theorem fold_advances_evaluation_poly_legacy
    (i : Fin (ℓ)) (h_i_succ_lt : i + 1 < ℓ + 𝓡)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_chal : L) :
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by
    omega
  ⟩) (h_i := by change i.val ≤ ℓ; omega) coeffs
  let f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_trans (n := i) (k := r) (m := ℓ) (h₁ := by omega) (by omega)⟩) =>
    P_i.eval (x.val : L)
  let f_i_plus_1 := fold_legacy 𝔽q β (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  let new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      rw [←Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 0) (by omega) (by omega)
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 1) (by omega) (by omega)
    ⟩)
  let P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) (h_i := by change i.val + 1 ≤ ℓ; omega) new_coeffs
  ∀ (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i+1, by omega⟩), f_i_plus_1 y = P_i_plus_1.eval y.val := by
  simp only
  intro y
  have h := congrFun (fold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, by omega⟩)
    (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := rfl)
    (h_destIdx_le := by change i.val + 1 ≤ ℓ; omega) coeffs r_chal) y
  simpa only [fold_legacy, fold, quotientFiber_eq_legacy, polyToOracleFunc] using h

/-- **Challenge tensor expansion** `⨂_{j}(1 - r_j, r_j)` as a function `Fin (2^n) → L`. This is
exactly `multilinearWeight`; the `Soundness/Lift` indicator lemmas `unfold` it to that form. -/
def challengeTensorExpansion (n : ℕ) (rc : Fin n → L) : Fin (2 ^ n) → L :=
  multilinearWeight (F := L) (ϑ := n) (r := rc)

/-- The single-step `n = 1` tensor expansion is `![1 - c, c]`. -/
lemma challengeTensorExpansion_one (c : L) :
    challengeTensorExpansion 1 (rc := fun _ => c) = ![1 - c, c] := by
  unfold challengeTensorExpansion multilinearWeight
  funext i
  fin_cases i <;>
    simp [Fin.prod_univ_one, Nat.testBit]

-- NOTE: the entrywise identity `challengeTensorProduct.get idx = challengeTensorExpansion idx`
-- is *false as stated*: the legacy `challengeTensorProduct` recursion places the last challenge in
-- the LSB (`idx % 2` selects `r (last n)`), whereas
-- `challengeTensorExpansion = multilinearWeight` places it in the MSB (`testBit idx j` ↔ challenge
-- `j`). The single-point matrix evaluator therefore uses `challengeTensorProduct` directly; the
-- multilinear-weight tensor remains available as `challengeTensorExpansion` for the soundness
-- polynomial basis.

/-- The (in-range) arithmetic bound `i.val + steps < ℓ + 𝓡` derived from a destination index
`destIdx.val = i.val + steps` with `destIdx ≤ ℓ`. Shared by the new-API matrix/fiber definitions
to lift the `{destIdx}`-keyed point `y` to the legacy `⟨i + steps, _⟩` index. -/
private lemma newAPI_i_add_steps_lt {i : Fin r} {destIdx : Fin r} {steps : ℕ}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ) :
    i.val + steps < ℓ + 𝓡 := by
  have hle : i.val + steps ≤ ℓ := by rw [← h_destIdx]; exact h_destIdx_le
  exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡))

/-- Lift a `{destIdx}`-keyed domain point `y : S⁽ᵈᵉˢᵗ⁾` to the legacy `⟨i + steps, _⟩`-keyed index.
Both indices are equal as `Fin r` (`destIdx.val = i.val + steps`), so the two `sDomain` submodules
coincide; the lift is `y` transported across that index equality. -/
private def newAPI_liftPoint {i : Fin r} {destIdx : Fin r} {steps : ℕ}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    (sDomain 𝔽q β h_ℓ_add_R_rate)
      (⟨i.val + steps, Nat.lt_trans (newAPI_i_add_steps_lt h_destIdx h_destIdx_le)
        h_ℓ_add_R_rate⟩ : Fin r) :=
  ⟨y.val, by
    have hidx : (⟨i.val + steps, Nat.lt_trans (newAPI_i_add_steps_lt h_destIdx h_destIdx_le)
        h_ℓ_add_R_rate⟩ : Fin r) = destIdx := Fin.eq_of_val_eq h_destIdx.symm
    rw [hidx]; exact y.property⟩

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ in
/-- Evaluation of `fiberEvaluations` at the canonical destination index `i + steps`.

This is the public, cast-free form of the definition; it hides the private new-API lift used to
bridge from `{destIdx}` to the legacy `⟨i + steps, _⟩` fiber API. -/
lemma fiberEvaluations_apply_eq_qMap_total_fiber
    (i : Fin r) (steps : ℕ) (h_i_add_steps_le : i.val + steps ≤ ℓ)
    (h_i_add_steps_lt_r : i.val + steps < r)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (⟨i.val + steps, h_i_add_steps_lt_r⟩ : Fin r))
    (idx : Fin (2 ^ steps)) :
    fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (destIdx := ⟨i.val + steps, h_i_add_steps_lt_r⟩) (steps := steps)
      (h_destIdx := rfl) (h_destIdx_le := by simpa only [Fin.val_mk] using h_i_add_steps_le)
      (f := f) (y := y) idx =
    f (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps)
      (h_i_add_steps := Nat.lt_of_le_of_lt h_i_add_steps_le
        (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡)))
      (y := y) idx) := by
  unfold fiberEvaluations
  rw [quotientFiber_eq_legacy]

/-- **Congruence in the source index** of `qMap_total_fiber` (new-API, applied form): transporting
the start index `sourceIdx₁ = sourceIdx₂` re-casts the fiber point accordingly. -/
lemma qMap_total_fiber_congr_source_apply
    {sourceIdx₁ sourceIdx₂ : Fin r} (steps : ℕ) {destIdx : Fin r}
    (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
    (h_destIdx : destIdx.val = sourceIdx₁.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) (x : Fin (2 ^ steps)) :
    qMap_total_fiber 𝔽q β (i := sourceIdx₁) (steps := steps)
      (h_i_add_steps := newAPI_i_add_steps_lt h_destIdx h_destIdx_le)
      (y := newAPI_liftPoint 𝔽q β h_destIdx h_destIdx_le y) x =
    cast (by rw [h_sourceIdx_eq])
      (qMap_total_fiber 𝔽q β (i := sourceIdx₂) (steps := steps)
        (h_i_add_steps := newAPI_i_add_steps_lt
          (h_destIdx := by rw [h_sourceIdx_eq] at h_destIdx; exact h_destIdx) h_destIdx_le)
        (y := newAPI_liftPoint 𝔽q β
          (h_destIdx := by rw [h_sourceIdx_eq] at h_destIdx; exact h_destIdx) h_destIdx_le y)
        x) := by
  subst h_sourceIdx_eq; rfl

/-- **Congruence in the destination index** of `qMap_total_fiber` (new-API): transporting the
destination index `destIdx₁ = destIdx₂` re-casts the fiber source point accordingly. -/
lemma qMap_total_fiber_congr_dest
    {sourceIdx : Fin r} (steps : ℕ) {destIdx₁ destIdx₂ : Fin r}
    (h_destIdx_congr : destIdx₁ = destIdx₂)
    (h_destIdx : destIdx₁.val = sourceIdx.val + steps)
    (h_destIdx_le : destIdx₁ ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx₁)) :
    qMap_total_fiber 𝔽q β (i := sourceIdx) (steps := steps)
      (h_i_add_steps := newAPI_i_add_steps_lt h_destIdx h_destIdx_le)
      (y := newAPI_liftPoint 𝔽q β h_destIdx h_destIdx_le y) =
    qMap_total_fiber 𝔽q β (i := sourceIdx) (steps := steps)
      (h_i_add_steps := newAPI_i_add_steps_lt
        (h_destIdx := by rw [h_destIdx_congr] at h_destIdx; exact h_destIdx)
        (by rw [h_destIdx_congr] at h_destIdx_le; exact h_destIdx_le))
      (y := newAPI_liftPoint 𝔽q β
        (h_destIdx := by rw [h_destIdx_congr] at h_destIdx; exact h_destIdx)
        (by rw [h_destIdx_congr] at h_destIdx_le; exact h_destIdx_le)
        (cast (by rw [h_destIdx_congr]) y)) := by
  subst h_destIdx_congr; rfl

/-- **Congruence in the step count** of `qMap_total_fiber` (new-API): transporting an equal step
count `steps = steps'` re-indexes the fiber accordingly. -/
lemma qMap_total_fiber_congr_steps
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (h_steps_eq : steps = steps')
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    (fun (x : Fin (2 ^ steps)) => qMap_total_fiber 𝔽q β (i := i) (steps := steps)
      (h_i_add_steps := newAPI_i_add_steps_lt h_destIdx h_destIdx_le)
      (y := newAPI_liftPoint 𝔽q β h_destIdx h_destIdx_le y) x) =
    fun (x : Fin (2 ^ steps)) => qMap_total_fiber 𝔽q β (i := i) (steps := steps')
      (h_i_add_steps := newAPI_i_add_steps_lt (h_destIdx := by omega) h_destIdx_le)
      (y := newAPI_liftPoint 𝔽q β (h_destIdx := by omega) h_destIdx_le y)
      ⟨x.val, by subst h_steps_eq; exact x.isLt⟩ := by
  subst h_steps_eq; rfl

/-- **Single-point localized fold matrix form** (legacy row-bit convention):
the fold-order challenge tensor dotted with the legacy matrix applied to `fiber_eval_mapping`. The tensor is
`challengeTensorProduct`, not `challengeTensorExpansion`, because `foldMatrixNat` peels the last fold
step into the low row bit. -/
noncomputable def single_point_localized_fold_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    (fiber_eval_mapping : Fin (2 ^ steps) → L) : L :=
  let challenge_vec : Fin (2 ^ steps) → L :=
    fun idx => (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r)
      steps r_challenges).get idx
  let fold_mat : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
    foldMatrixNat 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
      (newAPI_i_add_steps_lt h_destIdx h_destIdx_le)
      (newAPI_liftPoint 𝔽q β h_destIdx h_destIdx_le y)
  dotProduct challenge_vec (Matrix.mulVec fold_mat fiber_eval_mapping)

/-- **Localized fold matrix form** (destination-keyed compatibility API).

The raw single-point matrix expression remains available as
`single_point_localized_fold_matrix_form`. At the oracle level this exported form is definitionally
the iterated fold, avoiding an unsound identity between the legacy `challengeTensorProduct` row order
and the `challengeTensorExpansion`/`multilinearWeight` row order. -/
noncomputable def localized_fold_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
    (r_challenges := r_challenges)

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- Bridge from the canonical `Nat`/`destIdx` API back to the legacy `Fin (ℓ + 1)` fold.
Discharges the `cast` in `iterated_fold`'s definition pointwise (the destination index here is the
canonical `⟨i + steps, _⟩`, so the `cast` is `cast rfl`). -/
lemma iterated_fold_eq_iterated_fold_steps (i : Fin r) (steps : ℕ)
    (h_steps : steps < ℓ + 1) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (h_destIdx_le : (⟨i.val + steps, Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩ : Fin r) ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      (⟨i.val + steps, Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩ : Fin r)) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (destIdx := ⟨i.val + steps, Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩)
      (h_destIdx := rfl) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := r_challenges) y =
    iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := ⟨steps, h_steps⟩) (h_i_add_steps := h_i_add_steps) (f := f)
      (r_challenges := fun j => r_challenges ⟨j.val, by simpa using j.isLt⟩) y := by
  -- `iterated_fold` is `cast (congrArg … hidx) (iterated_fold_steps …)` with `hidx : ⟨i+steps,_⟩ =
  -- destIdx`; here `destIdx = ⟨i+steps,_⟩`, so `hidx = rfl` and the `cast` is `cast rfl`.
  unfold iterated_fold
  simp only [cast_eq]

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- The `{destIdx}` single-point matrix evaluator is the legacy localized-fold evaluator when the
destination is the canonical `i + steps` index. -/
private lemma single_point_localized_fold_matrix_form_eq_localized_fold_eval (i : Fin ℓ)
    (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩) :
    single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (destIdx := ⟨i.val + steps, by omega⟩)
      (h_destIdx := rfl) (h_destIdx_le := by omega) (r_challenges := r_challenges)
      (y := y)
      (fiber_eval_mapping := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (steps := steps) (destIdx := ⟨i.val + steps, by omega⟩)
        (h_destIdx := rfl) (h_destIdx_le := by omega) (f := f) (y := y)) =
    localized_fold_eval 𝔽q β i (steps := steps) (h_i_add_steps := h_i_add_steps)
      f r_challenges y := by
  unfold single_point_localized_fold_matrix_form localized_fold_eval
    localized_fold_matrix_form_legacy fiberEvaluationMapping foldMatrix_steps
  have hfiber : fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) steps rfl
      (by change i.val + steps ≤ ℓ; omega) f y =
      fun idx => f (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨i.val, by omega⟩ steps (by change i.val + steps < ℓ + 𝓡; have hR := Nat.pos_of_neZero 𝓡; omega) y idx) := by
    funext idx
    exact fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β _ steps (by omega) _ f y idx
  have hy : newAPI_liftPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i.val, by omega⟩ : Fin r)) (destIdx := ⟨i.val + steps, by omega⟩)
      (steps := steps) (h_destIdx := rfl) (h_destIdx_le := by change i.val + steps ≤ ℓ; omega)
      y = y := Subtype.ext rfl
  rw [hfiber, hy, Vector.dotProduct_eq_root_dotProduct]
  dsimp only
  unfold _root_.dotProduct
  simp only [Vector.get_ofFn]

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **Base case (new-API):** `iterated_fold` with `0` steps is the identity (returning the initial
function `f` evaluated at the index-transported point). Discharged from `iterated_fold`'s `cast`
definition and `Fin.dfoldl_zero` on the underlying `iterated_fold_steps`. -/
lemma iterated_fold_zero_steps (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin 0 → L) (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := r_challenges) y =
    f (Eq.mp (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type))
      (Fin.eq_of_val_eq h_destIdx)) y) := by
  -- `destIdx = i` (both `Fin r` with equal `.val`); substitute and collapse the casts.
  have h_eq : destIdx = i := Fin.eq_of_val_eq h_destIdx
  subst h_eq
  -- Now both `cast`s are on `rfl`; `iterated_fold_steps` over `0` steps is `Fin.dfoldl 0 = f`.
  unfold iterated_fold iterated_fold_steps
  simp only [Fin.dfoldl_zero, Fin.eta, Subtype.coe_eta, id_eq, cast_eq, eq_mp_eq_cast]

/-- **Peel the last step (new-API):** `iterated_fold (steps+1)` is one `fold` (at `midIdx`) applied
to `iterated_fold steps`. This is the new-API cast wrapper around
`iterated_fold_succ_last_gen`. -/
theorem iterated_fold_last (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx.val = i.val + steps) (h_destIdx : destIdx.val = i.val + steps + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin (steps + 1) → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps + 1)
        (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := r_challenges) =
    fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        (h_destIdx := by omega) (h_destIdx_le := by omega) (f := f)
        (r_challenges := Fin.init r_challenges))
      (r_chal := r_challenges (Fin.last steps)) := by
  have h_mid_bound : i.val + steps < r := by
    have hle : i.val + steps + 1 ≤ ℓ := by
      rw [← h_destIdx]
      exact h_destIdx_le
    have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    omega
  have h_dest_bound : i.val + steps + 1 < r := by
    rw [← h_destIdx]
    exact destIdx.isLt
  have h_mid_eq : midIdx = (⟨i.val + steps, h_mid_bound⟩ : Fin r) :=
    Fin.eq_of_val_eq h_midIdx
  have h_dest_eq : destIdx = (⟨i.val + steps + 1, h_dest_bound⟩ : Fin r) :=
    Fin.eq_of_val_eq h_destIdx
  subst h_mid_eq
  subst h_dest_eq
  funext y
  unfold iterated_fold fold
  simp only [cast_eq]
  rw [iterated_fold_succ_last_gen 𝔽q β (i := i) (n := steps)
    (h_steps := by omega)
    (h_i_add_steps := by
      -- after the `subst`s, `h_destIdx_le : ↑(⟨i.val + steps + 1, _⟩ : Fin r) ≤ ℓ` is
      -- definitionally the bare arithmetic bound (mk-projection reduction).
      have hle : i.val + steps + 1 ≤ ℓ := h_destIdx_le
      have h𝓡 : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
      omega)]
  -- Both sides are now the same `fold_legacy` of the `steps`-fold: the challenge
  -- reindexings (`castSucc`-of-`mk` vs `mk`-of-`castSucc`), the `Fin.last` instances,
  -- and the subtype re-`mk` of `y` are all definitional.
  rfl

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **Lemma 4.9 (new-API single-point form).** When the source index is an actual quotient level
`i < ℓ`, the raw single-point matrix evaluator over the fiber evaluations of `f` equals the
`steps`-fold of `f`. -/
theorem single_point_localized_fold_matrix_form_eq_iterated_fold
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (h_i_lt : i.val < ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (r_challenges := r_challenges) (y := y)
      (fiber_eval_mapping := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (f := f) (y := y)) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := r_challenges) y := by
  rcases i with ⟨iVal, hiVal⟩
  simp only [Fin.val_mk] at h_destIdx h_i_lt
  let iℓ : Fin ℓ := ⟨iVal, h_i_lt⟩
  have hsrc : (⟨iℓ, by omega⟩ : Fin r) = (⟨iVal, hiVal⟩ : Fin r) :=
    Fin.eq_of_val_eq rfl
  cases hsrc
  rcases destIdx with ⟨destVal, hdestVal⟩
  simp only [Fin.val_mk] at h_destIdx h_destIdx_le
  have hdest :
      (⟨destVal, hdestVal⟩ : Fin r) =
        (⟨iℓ.val + steps, by
          have hlt : iℓ.val + steps < ℓ + 𝓡 := by
            have hle : iℓ.val + steps ≤ ℓ := by
              rw [← h_destIdx]
              exact h_destIdx_le
            exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡))
          exact Nat.lt_trans hlt h_ℓ_add_R_rate⟩ : Fin r) := by
    exact Fin.eq_of_val_eq (by simpa [iℓ] using h_destIdx)
  cases hdest
  calc
    single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨iℓ, by omega⟩ : Fin r)) (steps := steps)
        (destIdx := ⟨iℓ.val + steps, by omega⟩)
        (h_destIdx := rfl) (h_destIdx_le := by omega) (r_challenges := r_challenges)
        (y := y)
        (fiber_eval_mapping := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨iℓ, by omega⟩ : Fin r)) (steps := steps)
          (destIdx := ⟨iℓ.val + steps, by omega⟩)
          (h_destIdx := rfl) (h_destIdx_le := by omega) (f := f) (y := y))
        = localized_fold_eval 𝔽q β iℓ (steps := steps)
            (h_i_add_steps := by
              have hle : iℓ.val + steps ≤ ℓ := by
                simpa using h_destIdx_le
              exact hle)
            f r_challenges y := by
          exact single_point_localized_fold_matrix_form_eq_localized_fold_eval 𝔽q β iℓ
            (steps := steps) (h_i_add_steps := by simpa using h_destIdx_le)
            (f := f) (r_challenges := r_challenges) (y := y)
    _ = iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨iℓ, by omega⟩ : Fin r)) (steps := ⟨steps, by
            have hle : iℓ.val + steps ≤ ℓ := by simpa using h_destIdx_le
            omega⟩)
          (h_i_add_steps := by
            have hle : iℓ.val + steps ≤ ℓ := by simpa using h_destIdx_le
            exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡)))
          (f := f) (r_challenges := r_challenges) y := by
        exact (iterated_fold_steps_eq_matrix_form 𝔽q β iℓ (steps := steps)
          (h_i_add_steps := by simpa using h_destIdx_le)
          (f := f) (r_challenges := r_challenges) (y := y)).symm
    _ = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨iℓ, by omega⟩ : Fin r)) (steps := steps)
          (destIdx := ⟨iℓ.val + steps, by omega⟩) (h_destIdx := rfl)
          (h_destIdx_le := by omega) (f := f) (r_challenges := r_challenges) y := by
        exact (iterated_fold_eq_iterated_fold_steps 𝔽q β
          (i := (⟨iℓ, by omega⟩ : Fin r)) (steps := steps)
          (h_steps := by
            have hle : iℓ.val + steps ≤ ℓ := by simpa using h_destIdx_le
            omega)
          (h_i_add_steps := by
            have hle : iℓ.val + steps ≤ ℓ := by simpa using h_destIdx_le
            exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡)))
          (h_destIdx_le := by omega) (f := f) (r_challenges := r_challenges)
          (y := y)).symm

/-- **Lemma 4.9 (new-API).** The exported new-API localized fold form is definitionally the
new-API iterated fold. The raw matrix expression is kept separately as
`single_point_localized_fold_matrix_form`; its legacy low-row-bit convention is proved by
`single_point_localized_fold_matrix_form_eq_iterated_fold`. -/
theorem iterated_fold_eq_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := r_challenges) =
    localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := r_challenges) := by
  rfl

end Essentials

section SoundnessTools
-- In this section, we use the generic notation `steps` instead of `ϑ` to avoid conflicts

/-!
### Binary Basefold Specific Code Definitions

Definitions specific to the Binary Basefold protocol based on the fundamentals document.
-/

-- NOTE (module split): the pre-split "Binary Basefold specific code" content that used to
-- live here — `BBF_Code`, `BBF_CodeDistance`, `disagreementSet`, `fiberwiseDisagreementSet`,
-- `fiberwiseDistance`, `fiberwiseClose`, `uniqueClosestCodeword`, `hammingClose`,
-- `fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius`, `isCompliant`,
-- `farness_implies_non_compliance`, and `foldingBadEvent` — was REMOVED. These caused
-- duplicate-declaration errors against the canonical post-split versions, which now live in
-- `ArkLib.ProofSystem.Binius.BinaryBasefold.Code` (code/distance/disagreement/fiberwise +
-- `BBF_Code (i : Fin r)` / `BBF_CodeDistance (i : Fin r)`) and
-- `ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance` (`isCompliant`,
-- `fold_error_containment`, `foldingBadEvent`, `farness_implies_non_compliance`).
-- Prelude now only provides the folding/fiber primitives those modules build on.

end SoundnessTools
end
end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.fold_advances_evaluation_poly_legacy
#print axioms Binius.BinaryBasefold.fold_advances_evaluation_poly
#print axioms Binius.BinaryBasefold.iterated_fold_eq_matrix_form
#print axioms Binius.BinaryBasefold.natDegree_intermediateNormVpoly_nat
#print axioms Binius.BinaryBasefold.degree_intermediateNormVpoly
#print axioms Binius.BinaryBasefold.is_fiber_iff_generates_quotient_point
