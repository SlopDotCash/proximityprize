/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilAbsorption
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The window pencil matrix (#371, WB-4 stage i)

The coefficient-level linear pencil of the window regime.  For WB data
`(ℓ₀, R₀, ℓ₁, R₁)` (any representations — no reduced form, no coprimality, no
nonvanishing hypotheses), a scalar `γ` whose line `u₀ + γ·u₁` is explainable at
slack `w` produces a kernel vector of the matrix `M(γ)` whose rows are the
coefficients `0 … 3w+k−1` of the polynomial identity

  `(ℓ₁R₀ + γ·ℓ₀R₁) · Z  =  ℓ₀ℓ₁ · Q  +  Z_D · h`

in the unknowns `Z` (deg ≤ w, the error locator `Z_E`), `Q` (deg ≤ w+k−1, the
product `P·Z_E` with the explaining codeword), and `h` (deg ≤ 3w+k−1−n, the
cofactor of the discrepancy).  `γ` enters only the `w+1` locator columns, so all
square sub-determinants have `γ`-degree ≤ w+1 — the root-counting input for the
window law (`WBPencilWindowLaw`).

Validated numerically before formalization: `scripts/probes/probe_wb_window_pencil_crt.py`
(550 genuine rational pairs at two window instances, zero mismatches between
brute-force explainability and split-kernel membership).

Contents:
* `domVanish`, `windowPencil` — the domain vanishing polynomial and the pencil;
* `wzPoly/wqPoly/whPoly`, `coeffVec` — the block decomposition of kernel vectors;
* `windowPencil_mulVec_coeff` — `M(γ)·v` row `r` = coefficient `r` of the identity;
* `identity_of_agreement` — the geometric core: a codeword agreeing with the line
  on `S` (with the WB relations) yields the identity with `Z = Z_{univ∖S}`;
* `natDegree_det_le_sum_colBound` + `windowPencil_natDegree_le` — every square
  sub-determinant of the pencil has `γ`-degree ≤ w+1.
-/

open Finset Polynomial Matrix

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- The vanishing polynomial of the entire evaluation domain. -/
noncomputable def domVanish (dom : Fin n ↪ F) : F[X] :=
  ∏ i : Fin n, (X - C (dom i))

/-- The column index of the window pencil: locator block `Z` (deg ≤ w), product
block `Q = P·Z` (deg ≤ w+k−1), cofactor block `h` (deg ≤ 3w+k−1−n; empty below
the window). -/
abbrev WCol (n k w : ℕ) := Fin (w + 1) ⊕ Fin (w + k) ⊕ Fin (3 * w + k - n)

/-- **The window pencil.**  Row `r` = coefficient `r` of the identity
`(ℓ₁R₀ + γ·ℓ₀R₁)·Z − ℓ₀ℓ₁·Q − Z_D·h`; the matrix entry is an `F[γ]`-polynomial of
degree ≤ 1, with `γ` appearing only in the `w+1` locator columns. -/
noncomputable def windowPencil (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X]) :
    Matrix (Fin (3 * w + k)) (WCol n k w) F[X] :=
  fun r => Sum.elim
    (fun t => C ((ℓ₁ * R₀ * X ^ (t : ℕ)).coeff r)
      + X * C ((ℓ₀ * R₁ * X ^ (t : ℕ)).coeff r))
    (Sum.elim
      (fun s => C (-((ℓ₀ * ℓ₁ * X ^ (s : ℕ)).coeff r)))
      (fun m => C (-((domVanish dom * X ^ (m : ℕ)).coeff r))))

/-! ## Block polynomials of a coefficient vector -/

/-- The locator polynomial of a column vector. -/
noncomputable def wzPoly {n k w : ℕ} (v : WCol n k w → F) : F[X] :=
  ∑ t : Fin (w + 1), C (v (Sum.inl t)) * X ^ (t : ℕ)

/-- The product-block polynomial of a column vector. -/
noncomputable def wqPoly {n k w : ℕ} (v : WCol n k w → F) : F[X] :=
  ∑ s : Fin (w + k), C (v (Sum.inr (Sum.inl s))) * X ^ (s : ℕ)

/-- The cofactor polynomial of a column vector. -/
noncomputable def whPoly {n k w : ℕ} (v : WCol n k w → F) : F[X] :=
  ∑ m : Fin (3 * w + k - n), C (v (Sum.inr (Sum.inr m))) * X ^ (m : ℕ)

/-- The coefficient vector of a triple of polynomials. -/
def coeffVec (n k w : ℕ) (Z Q h : F[X]) : WCol n k w → F :=
  Sum.elim (fun t => Z.coeff t) (Sum.elim (fun s => Q.coeff s) (fun m => h.coeff m))

/-- Truncated coefficient sums reproduce the polynomial when the tail vanishes. -/
theorem sum_C_coeff_mul_X_pow_eq {N : ℕ} {p : F[X]}
    (hp : ∀ j, N ≤ j → p.coeff j = 0) :
    (∑ t : Fin N, C (p.coeff (t : ℕ)) * X ^ (t : ℕ)) = p := by
  ext j
  rw [finset_sum_coeff]
  by_cases hj : j < N
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin N)]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro t _ hne
      rw [coeff_C_mul, coeff_X_pow, if_neg (by
        intro h
        exact hne (Fin.ext h.symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hp j (by omega)]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [coeff_C_mul, coeff_X_pow, if_neg (by
      intro h
      have := t.2
      omega), mul_zero]

theorem wzPoly_coeffVec {n k w : ℕ} {Z Q h : F[X]} (hZ : Z.natDegree ≤ w) :
    wzPoly (coeffVec n k w Z Q h) = Z :=
  sum_C_coeff_mul_X_pow_eq fun j hj =>
    coeff_eq_zero_of_natDegree_lt (by omega)

theorem wqPoly_coeffVec {n k w : ℕ} {Z Q h : F[X]} (hQ : Q.natDegree < w + k) :
    wqPoly (coeffVec n k w Z Q h) = Q :=
  sum_C_coeff_mul_X_pow_eq fun j hj =>
    coeff_eq_zero_of_natDegree_lt (by omega)

theorem whPoly_coeffVec {n k w : ℕ} {Z Q h : F[X]}
    (hh : ∀ j, 3 * w + k - n ≤ j → h.coeff j = 0) :
    whPoly (coeffVec n k w Z Q h) = h :=
  sum_C_coeff_mul_X_pow_eq hh

theorem wzPoly_zero {n k w : ℕ} : wzPoly (n := n) (k := k) (w := w) (0 : WCol n k w → F) = 0 := by
  simp [wzPoly]

/-! ## The coefficient bridge -/

/-- A product against a block polynomial expands coefficientwise. -/
theorem coeff_mul_blockSum {N : ℕ} (A : F[X]) (c : Fin N → F) (r : ℕ) :
    (A * ∑ t : Fin N, C (c t) * X ^ (t : ℕ)).coeff r
      = ∑ t : Fin N, c t * (A * X ^ (t : ℕ)).coeff r := by
  rw [Finset.mul_sum, finset_sum_coeff]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show A * (C (c t) * X ^ (t : ℕ)) = C (c t) * (A * X ^ (t : ℕ)) by ring,
    coeff_C_mul]

/-- **The coefficient bridge**: the evaluated pencil times a coefficient vector
computes, row by row, the coefficients of the polynomial identity. -/
theorem windowPencil_mulVec_coeff (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (γ : F) (v : WCol n k w → F) (r : Fin (3 * w + k)) :
    ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v r
      = ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * wzPoly v - ℓ₀ * ℓ₁ * wqPoly v
          - domVanish dom * whPoly v).coeff r := by
  classical
  have hRHS : ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * wzPoly v - ℓ₀ * ℓ₁ * wqPoly v
        - domVanish dom * whPoly v).coeff r
      = (∑ t : Fin (w + 1), v (Sum.inl t) * (ℓ₁ * R₀ * X ^ (t : ℕ)).coeff r)
        + γ * (∑ t : Fin (w + 1), v (Sum.inl t) * (ℓ₀ * R₁ * X ^ (t : ℕ)).coeff r)
        - (∑ s : Fin (w + k), v (Sum.inr (Sum.inl s))
            * (ℓ₀ * ℓ₁ * X ^ (s : ℕ)).coeff r)
        - (∑ m : Fin (3 * w + k - n), v (Sum.inr (Sum.inr m))
            * (domVanish dom * X ^ (m : ℕ)).coeff r) := by
    rw [coeff_sub, coeff_sub, add_mul, coeff_add,
      show (C γ * (ℓ₀ * R₁)) * wzPoly v = C γ * ((ℓ₀ * R₁) * wzPoly v) by ring,
      coeff_C_mul, wzPoly, coeff_mul_blockSum, coeff_mul_blockSum, wqPoly,
      coeff_mul_blockSum, whPoly, coeff_mul_blockSum]
  have hLHS : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v r
      = (∑ t : Fin (w + 1), ((ℓ₁ * R₀ * X ^ (t : ℕ)).coeff r
            + γ * (ℓ₀ * R₁ * X ^ (t : ℕ)).coeff r) * v (Sum.inl t))
        + ((∑ s : Fin (w + k), -(ℓ₀ * ℓ₁ * X ^ (s : ℕ)).coeff r
              * v (Sum.inr (Sum.inl s)))
          + (∑ m : Fin (3 * w + k - n), -(domVanish dom * X ^ (m : ℕ)).coeff r
              * v (Sum.inr (Sum.inr m)))) := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply,
      windowPencil, Sum.elim_inl, Sum.elim_inr, eval_add, eval_mul, eval_C, eval_X]
  rw [hLHS, hRHS]
  have h1 : ∑ t : Fin (w + 1), ((ℓ₁ * R₀ * X ^ (t : ℕ)).coeff r
        + γ * (ℓ₀ * R₁ * X ^ (t : ℕ)).coeff r) * v (Sum.inl t)
      = (∑ t : Fin (w + 1), v (Sum.inl t) * (ℓ₁ * R₀ * X ^ (t : ℕ)).coeff r)
        + γ * (∑ t : Fin (w + 1), v (Sum.inl t) * (ℓ₀ * R₁ * X ^ (t : ℕ)).coeff r) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have h2 : ∑ s : Fin (w + k), -(ℓ₀ * ℓ₁ * X ^ (s : ℕ)).coeff r
        * v (Sum.inr (Sum.inl s))
      = -(∑ s : Fin (w + k), v (Sum.inr (Sum.inl s))
          * (ℓ₀ * ℓ₁ * X ^ (s : ℕ)).coeff r) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have h3 : ∑ m : Fin (3 * w + k - n), -(domVanish dom * X ^ (m : ℕ)).coeff r
        * v (Sum.inr (Sum.inr m))
      = -(∑ m : Fin (3 * w + k - n), v (Sum.inr (Sum.inr m))
          * (domVanish dom * X ^ (m : ℕ)).coeff r) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h1, h2, h3]
  ring

/-- A polynomial identity puts its coefficient vector in the kernel of the
evaluated pencil. -/
theorem windowPencil_mulVec_eq_zero (dom : Fin n ↪ F) (k w : ℕ)
    {ℓ₀ R₀ ℓ₁ R₁ : F[X]} {γ : F} {Z Q h : F[X]}
    (hZ : Z.natDegree ≤ w) (hQ : Q.natDegree < w + k)
    (hh : ∀ j, 3 * w + k - n ≤ j → h.coeff j = 0)
    (hid : (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z = ℓ₀ * ℓ₁ * Q + domVanish dom * h) :
    ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec
      (coeffVec n k w Z Q h) = 0 := by
  funext r
  rw [windowPencil_mulVec_coeff, wzPoly_coeffVec hZ, wqPoly_coeffVec hQ,
    whPoly_coeffVec hh, Pi.zero_apply]
  rw [show (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z - ℓ₀ * ℓ₁ * Q - domVanish dom * h
      = (ℓ₀ * ℓ₁ * Q + domVanish dom * h) - ℓ₀ * ℓ₁ * Q - domVanish dom * h by
    rw [hid], coeff_sub, coeff_sub, coeff_add]
  ring

/-! ## The geometric core: agreement yields the identity -/

/-- **The identity from a line explanation.**  If a degree-`< k` codeword agrees
with the line `u₀ + γ·u₁` on `S` and the WB relations `ℓ_j(x_i)·u_j(x_i) = R_j(x_i)`
hold at every domain point, then the cleared identity holds with locator
`Z = ∏_{i ∈ univ∖S}(X − x_i)` — with NO hypotheses on the representations beyond
the degree caps: vanishing denominators are absorbed by the relations themselves. -/
theorem identity_of_agreement (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {ℓ₀ R₀ ℓ₁ R₁ : F[X]} (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    {u₀ u₁ : Fin n → F}
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {γ : F} {S : Finset (Fin n)} (hS : n - w ≤ S.card)
    {P : F[X]} (hPdeg : P.degree < k)
    (hag : ∀ i ∈ S, P.eval (dom i) = u₀ i + γ * u₁ i) :
    ∃ Q h : F[X], Q.natDegree < w + k ∧ (∀ j, 3 * w + k - n ≤ j → h.coeff j = 0) ∧
      (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * (∏ i ∈ Finset.univ \ S, (X - C (dom i)))
        = ℓ₀ * ℓ₁ * Q + domVanish dom * h := by
  classical
  have hPnd : P.natDegree ≤ k - 1 := by
    by_cases hP0 : P = 0
    · subst hP0
      simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      omega
  set G : F[X] := ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁) with hGdef
  -- G vanishes on S: substitute the WB relations
  have hGroot : ∀ i ∈ S, G.eval (dom i) = 0 := by
    intro i hi
    have h₀ := hrel₀ i
    have h₁ := hrel₁ i
    have hP := hag i hi
    simp only [hGdef, eval_sub, eval_add, eval_mul, eval_C]
    calc ℓ₁.eval (dom i) * R₀.eval (dom i)
          + γ * (ℓ₀.eval (dom i) * R₁.eval (dom i))
          - P.eval (dom i) * (ℓ₀.eval (dom i) * ℓ₁.eval (dom i))
        = ℓ₁.eval (dom i) * (ℓ₀.eval (dom i) * u₀ i)
          + γ * (ℓ₀.eval (dom i) * (ℓ₁.eval (dom i) * u₁ i))
          - (u₀ i + γ * u₁ i) * (ℓ₀.eval (dom i) * ℓ₁.eval (dom i)) := by
          rw [h₀, h₁, hP]
      _ = 0 := by ring
  -- the vanishing set divides G
  have hdvd : (∏ i ∈ S, (X - C (dom i))) ∣ G := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      have hne : dom i ≠ dom j := fun h => hij (dom.injective h)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    · intro i hi
      exact dvd_iff_isRoot.mpr (hGroot i hi)
  obtain ⟨h, hGh⟩ := hdvd
  -- degree bookkeeping for the cofactor
  have hZScard : (∏ i ∈ S, (X - C (dom i))).natDegree = S.card := by
    rw [Polynomial.natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (dom i)]
    simp
  have hGdeg : G.natDegree ≤ 2 * w + k - 1 := by
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans natDegree_mul_le (by omega)
      · refine le_trans natDegree_mul_le ?_
        rw [natDegree_C]
        exact le_trans (by omega : 0 + (ℓ₀ * R₁).natDegree ≤ (ℓ₀ * R₁).natDegree)
          (le_trans natDegree_mul_le (by omega))
    · refine le_trans natDegree_mul_le ?_
      have : (ℓ₀ * ℓ₁).natDegree ≤ 2 * w := le_trans natDegree_mul_le (by omega)
      omega
  have hhcoeff : ∀ j, 3 * w + k - n ≤ j → h.coeff j = 0 := by
    intro j hj
    by_cases hG0 : G = 0
    · have hZS0 : (∏ i ∈ S, (X - C (dom i))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (dom i)
      have : h = 0 := by
        have := hGh
        rw [hG0] at this
        rcases mul_eq_zero.mp this.symm with h1 | h1
        · exact absurd h1 hZS0
        · exact h1
      rw [this]
      simp
    · have hh0 : h ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hGh
        exact hG0 hGh
      have hZS0 : (∏ i ∈ S, (X - C (dom i))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (dom i)
      have hdegmul : G.natDegree = S.card + h.natDegree := by
        rw [hGh, Polynomial.natDegree_mul hZS0 hh0, hZScard]
      have hScard : S.card ≤ n := le_trans (Finset.card_le_card (Finset.subset_univ S))
        (by simp)
      refine coeff_eq_zero_of_natDegree_lt ?_
      omega
  -- assemble: multiply G = Z_S·h by Z_E and use Z_S·Z_E = Z_D
  refine ⟨P * (∏ i ∈ Finset.univ \ S, (X - C (dom i))), h, ?_, hhcoeff, ?_⟩
  · have hEcard : (Finset.univ \ S).card ≤ w := by
      have h1 : (Finset.univ \ S).card = n - S.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simp
      have hScard : S.card ≤ n := le_trans (Finset.card_le_card (Finset.subset_univ S))
        (by simp)
      omega
    have hZEdeg : (∏ i ∈ Finset.univ \ S, (X - C (dom i))).natDegree
        = (Finset.univ \ S).card := by
      rw [Polynomial.natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (dom i)]
      simp
    calc (P * ∏ i ∈ Finset.univ \ S, (X - C (dom i))).natDegree
        ≤ P.natDegree + (∏ i ∈ Finset.univ \ S, (X - C (dom i))).natDegree :=
          natDegree_mul_le
      _ ≤ (k - 1) + w := by
          rw [hZEdeg]
          exact Nat.add_le_add hPnd hEcard
      _ < w + k := by omega
  · have hsplit : (∏ i ∈ Finset.univ \ S, (X - C (dom i)))
        * (∏ i ∈ S, (X - C (dom i))) = domVanish dom := by
      rw [domVanish, Finset.prod_sdiff (Finset.subset_univ S)]
    calc (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * (∏ i ∈ Finset.univ \ S, (X - C (dom i)))
        = (P * (ℓ₀ * ℓ₁) + G) * (∏ i ∈ Finset.univ \ S, (X - C (dom i))) := by
          rw [hGdef]
          ring
      _ = ℓ₀ * ℓ₁ * (P * (∏ i ∈ Finset.univ \ S, (X - C (dom i))))
          + (∏ i ∈ Finset.univ \ S, (X - C (dom i))) * G := by ring
      _ = ℓ₀ * ℓ₁ * (P * (∏ i ∈ Finset.univ \ S, (X - C (dom i))))
          + domVanish dom * h := by
          rw [hGh, ← hsplit]
          ring

/-! ## Degree bounds for sub-determinants -/

/-- Generic column-capped determinant degree bound. -/
theorem natDegree_det_le_sum_colBound {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F[X]) (d : ι → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ j, d j := by
  classical
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  have hprod : (∏ j : ι, A (σ j) j).natDegree ≤ ∑ j, d j :=
    le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun j _ => hA (σ j) j)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
    exact hprod
  · rw [h, Units.neg_smul, one_smul, natDegree_neg]
    exact hprod

/-- The pencil's entries have `γ`-degree ≤ 1 in the locator block and 0 elsewhere. -/
theorem windowPencil_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (r : Fin (3 * w + k)) (c : WCol n k w) :
    ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁) r c).natDegree
      ≤ Sum.elim (fun _ : Fin (w + 1) => 1)
          (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)) c := by
  rcases c with t | s | m
  · simp only [windowPencil, Sum.elim_inl]
    refine le_trans (natDegree_add_le _ _) (max_le (by simp) ?_)
    refine le_trans natDegree_mul_le ?_
    simp
  · simp only [windowPencil, Sum.elim_inr, Sum.elim_inl, natDegree_C, le_refl]
  · simp only [windowPencil, Sum.elim_inr, natDegree_C, le_refl]

/-- The column-cap sum of the pencil is `w + 1`. -/
theorem windowPencil_colBound_sum (n k w : ℕ) :
    (∑ c : WCol n k w, Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)) c)
      = w + 1 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.windowPencil_mulVec_coeff
#print axioms ProximityGap.WBPencil.windowPencil_mulVec_eq_zero
#print axioms ProximityGap.WBPencil.identity_of_agreement
#print axioms ProximityGap.WBPencil.natDegree_det_le_sum_colBound
