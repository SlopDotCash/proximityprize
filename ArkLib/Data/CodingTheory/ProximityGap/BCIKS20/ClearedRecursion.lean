/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StructuredWeightInduction

/-!
# The repaired (A.1) cell coefficient: the paper's W-cleared, δ-adjusted `B_{i1,λ}`

Finding 14 (machine-checked in `Finding14Countermodel.lean`) established that the in-tree
`B_coeff` — the un-cleared `Y ↦ T` lift — diverges from [BCIKS20]'s
`B_{i1,λ} = W^{d−δ−Σλ}·A_{i1,λ}` (A.4, lines 4060–4080). This file defines the FAITHFUL
cell coefficient `B_coeffC`:

* for `i1 ≥ 1` the clearing power is `d_R − Σλ` (every `(T/W)`-denominator cleared);
* for `i1 = 0` the paper's δ-saving applies: the top coefficient of the specialized Hasse
  polynomial is `W`-divisible (the PROVEN `leadingCoeff_dvd_evalX_hasseDerivY_top`), so the
  exact quotient `c_top/W` rides at the top index and the rest clears at `d_R − 1 − Σλ`.

The anchored weight budgets — `(D_R−Σλ−i1) + (d_R−δ−Σλ)·degW`, exactly the paper's — are
proven here from the landed suppliers (`hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored`
+ the exact-division top-term estimate). Under these budgets the anchored per-term ledger
closes at EVERY cell (finding 13's verified cell arithmetic), which is what makes this the
correct recursion to thread through the (P1) weight induction and the Claim-5.10 chain.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
  [Fact (0 < H.natDegree)]

/-- **The paper-faithful cell coefficient** `B_{i1,λ}` (BCIKS20 A.4): the W-cleared,
δ-adjusted lift of the iterated Hasse coefficient, with the partition-multinomial
prefactor. At `i1 = 0` the top coefficient is divided exactly by `W` (the δ-saving);
at `i1 ≥ 1` the full clearing power `d_R − Σλ` is used. -/
noncomputable def B_coeffC (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) : 𝒪 H :=
  if i1 = 0 then
    (prefactor R.natDegree i1 lam) •
      Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        ((if sigmaLambda lam + 1 ≤ Bivariate.natDegreeY R then
            hasseCoeffRepr𝒪_cleared H x₀ R i1 (sigmaLambda lam)
              (Bivariate.natDegreeY R - 1 - sigmaLambda lam)
          else 0)
          + Polynomial.C
              ((Polynomial.Bivariate.evalX (Polynomial.C x₀)
                  (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R))).coeff
                  (Bivariate.natDegreeY R - sigmaLambda lam)
                / H.leadingCoeff)
            * Polynomial.X ^ (Bivariate.natDegreeY R - sigmaLambda lam))
  else
    (prefactor R.natDegree i1 lam) •
      Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (hasseCoeffRepr𝒪_cleared H x₀ R i1 (sigmaLambda lam)
          (Bivariate.natDegreeY R - sigmaLambda lam))

/-- A single-monomial weight bound: `Λ(C c · X^b) ≤ b·(D+1−d_H) + deg c`. -/
theorem weight_Λ_C_mul_X_pow_le (c : F[X]) (b : ℕ) (D : ℕ) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ b) H D
      ≤ WithBot.some (b * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) := by
  rw [weight_Λ]
  refine Finset.sup_le fun n hn => ?_
  have hcoeff : (Polynomial.C c * Polynomial.X ^ b).coeff n
      = if n = b then c else 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [eq_comm]
  by_cases hnb : n = b
  · subst hnb
    rw [hcoeff, if_pos rfl]
  · exfalso
    have : (Polynomial.C c * Polynomial.X ^ b).coeff n = 0 := by
      rw [hcoeff, if_neg hnb]
    exact (Polynomial.mem_support_iff.mp hn) this

/-- **The anchored budget for `i1 ≥ 1` cells:** `Λ(B_{i1,λ}) ≤ (D_R−Σλ−i1) + (d_R−Σλ)·degW`
— the paper's general cell budget, from the landed cleared-form supplier. -/
theorem B_coeffC_weight_le_anchored_pos
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ Bivariate.natDegreeY H + (H.leadingCoeff).natDegree)
    (x₀ : F) (R : F[X][X][Y]) {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    {i1 : ℕ} (hi1 : i1 ≠ 0) {m : ℕ} (lam : Nat.Partition m) :
    weight_Λ_over_𝒪 hH (B_coeffC (H := H) x₀ R i1 lam) D
      ≤ WithBot.some ((DR - sigmaLambda lam - i1)
          + (Bivariate.natDegreeY R - sigmaLambda lam) * (H.leadingCoeff).natDegree) := by
  rw [B_coeffC, if_neg hi1]
  refine le_trans (weight_Λ_over_𝒪_nsmul_le H hH hDH _ _) ?_
  exact hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored hH hDH htight x₀ R
    htotal hvanish i1 (sigmaLambda lam) _

/-- **The anchored SAVED budget for `i1 = 0` cells:**
`Λ(B_{0,λ}) ≤ (D_R−Σλ) + (d_R−1−Σλ)·degW` — the paper's δ-saved budget. The truncated
part is the landed cleared supplier at power `d_R−1−Σλ`; the top term saves exactly one
`degW` through the exact division `c_top/W` (provided by the W-divisibility of the top
Hasse coefficient). -/
theorem B_coeffC_weight_le_anchored_zero
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ Bivariate.natDegreeY H + (H.leadingCoeff).natDegree)
    (hWne : H.leadingCoeff ≠ 0)
    (x₀ : F) (R : F[X][X][Y]) {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    {m : ℕ} (lam : Nat.Partition m)
    (hdvd : H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY (sigmaLambda lam) R))).coeff
        (Bivariate.natDegreeY R - sigmaLambda lam))
    (hdRm : sigmaLambda lam + 1 ≤ Bivariate.natDegreeY R)
    (hdRDR : Bivariate.natDegreeY R ≤ DR) :
    weight_Λ_over_𝒪 hH (B_coeffC (H := H) x₀ R 0 lam) D
      ≤ WithBot.some ((DR - sigmaLambda lam)
          + (Bivariate.natDegreeY R - 1 - sigmaLambda lam)
            * (H.leadingCoeff).natDegree) := by
  rw [B_coeffC, if_pos rfl, if_pos hdRm]
  refine le_trans (weight_Λ_over_𝒪_nsmul_le H hH hDH _ _) ?_
  rw [map_add]
  refine le_trans (weight_Λ_over_𝒪_add_le H hH hDH _ _) ?_
  rw [max_le_iff]
  constructor
  · -- the truncated cleared part, at power d_R − 1 − Σλ
    refine le_trans (hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored hH hDH htight
      x₀ R htotal hvanish 0 (sigmaLambda lam) _) ?_
    refine WithBot.coe_le_coe.mpr ?_
    omega
  · -- the exact-division top term
    obtain ⟨c', hc'⟩ := hdvd
    have hdivval : (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY (sigmaLambda lam) R))).coeff
          (Bivariate.natDegreeY R - sigmaLambda lam) / H.leadingCoeff = c' := by
      rw [hc']
      exact mul_div_cancel_left₀ c' hWne
    rw [hdivval]
    rcases eq_or_ne c' 0 with hc0 | hc0
    · -- a vanishing top term contributes nothing
      subst hc0
      rw [map_zero, zero_mul, map_zero, weight_Λ_over_𝒪_zero]
      exact bot_le
    · refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
      refine le_trans (weight_Λ_C_mul_X_pow_le c' _ D) ?_
      refine WithBot.coe_le_coe.mpr ?_
      -- the exact quotient saves one degW: deg c' + degW ≤ shape budget at the top index
      have hdeg : c'.natDegree + (H.leadingCoeff).natDegree
          ≤ DR - sigmaLambda lam - (Bivariate.natDegreeY R - sigmaLambda lam) := by
        have hshape := specializedHasse_coeff_natDegree_le_of_total (x₀ := x₀) htotal 0
          (sigmaLambda lam) (Bivariate.natDegreeY R - sigmaLambda lam)
        have hmul : ((H.leadingCoeff) * c').natDegree
            = (H.leadingCoeff).natDegree + c'.natDegree :=
          Polynomial.natDegree_mul hWne hc0
        rw [hc', hmul] at hshape
        omega
      have hanchor : D + 1 - Bivariate.natDegreeY H
          ≤ (H.leadingCoeff).natDegree + 1 := by
        omega
      have hb := Nat.mul_le_mul_left
        (Bivariate.natDegreeY R - sigmaLambda lam) hanchor
      have hb1 : (Bivariate.natDegreeY R - sigmaLambda lam)
          * ((H.leadingCoeff).natDegree + 1)
          = (Bivariate.natDegreeY R - sigmaLambda lam) * (H.leadingCoeff).natDegree
            + (Bivariate.natDegreeY R - sigmaLambda lam) := by
        rw [Nat.mul_add, Nat.mul_one]
      have hsplit : (Bivariate.natDegreeY R - sigmaLambda lam)
            * (H.leadingCoeff).natDegree
          = (Bivariate.natDegreeY R - 1 - sigmaLambda lam) * (H.leadingCoeff).natDegree
            + (H.leadingCoeff).natDegree := by
        have h1 : Bivariate.natDegreeY R - sigmaLambda lam
            = (Bivariate.natDegreeY R - 1 - sigmaLambda lam) + 1 := by omega
        rw [h1, Nat.add_mul, Nat.one_mul]
      omega

/-! ## The repaired recursion -/

/-- **The repaired (A.1) recursion `βHenselC`:** identical engine exponents to the paper
(and to the in-tree `βHensel`), with the paper-faithful cleared cell coefficient
`B_coeffC` in place of the divergent un-cleared `B_coeff` (finding 14). -/
noncomputable def βHenselC (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ℕ → 𝒪 H :=
  fun t => Nat.strongRecOn t (fun n ih =>
    match n with
    | 0 => Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y])
    | (k + 1) =>
        - ∑ i1 ∈ Finset.range (k + 2),
            ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (k + 1 - i1))).filter
                      (fun lam => (k + 1) ∉ lam.parts),
              (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
                * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                * B_coeffC (H := H) x₀ R i1 lam
                * partitionProd lam (fun l => if h : l < k + 1 then ih l (by omega) else 0))

/-- Base case: `βHenselC 0 = mk X = T mod H̃` — identical to the original. -/
theorem βHenselC_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHenselC (H := H) x₀ R hHyp 0 =
      Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) := by
  unfold βHenselC
  rw [Nat.strongRecOn_eq]

/-- Successor unfolding: the literal repaired `(A.1)` sum. -/
theorem βHenselC_succ (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (k : ℕ) :
    βHenselC (H := H) x₀ R hHyp (k + 1) =
      - ∑ i1 ∈ Finset.range (k + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (k + 1 - i1))).filter
                    (fun lam => (k + 1) ∉ lam.parts),
            (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * B_coeffC (H := H) x₀ R i1 lam
              * partitionProd lam
                  (fun l => if _h : l < k + 1 then βHenselC (H := H) x₀ R hHyp l
                    else 0) := by
  conv_lhs => rw [βHenselC, Nat.strongRecOn_eq]
  rfl

/-- **The anchored closing arithmetic for the `i1 = 0` cells** (the cell class the
original engine could not close): with the SAVED budget
`nB = (D_R−m) + (d_R−1−m)·w` the raw per-term ledger closes at the anchor for every
genuine `i1 = 0` cell (`m ≥ 2`, `m < d_R`). -/
theorem harith_anchored_zero {k m DR dR dH w D Lξ nB : ℕ}
    (hm2 : 2 ≤ m) (hms : m ≤ k + 1) (hmdR : m + 1 ≤ dR)
    (hdR2 : 2 ≤ dR) (hdH1 : 1 ≤ dH) (hdHdR : dH ≤ dR) (hdRDR : dR ≤ DR)
    (hD : D = dH + w) (hDR : DR ≤ D)
    (hnB : nB = (DR - m) + (dR - 1 - m) * w)
    (hLξ : Lξ = (dR - 1) * (w + 1)) :
    (0 + 1 - 1) * w + (2 * 0 + m - 2) * Lξ + nB
      + (m + ((k + 1 - 0) + m) * w + (2 * (k + 1 - 0) - m) * Lξ)
    ≤ 1 + (k + 2) * w + (2 * (k + 1) - 1) * Lξ := by
  have hxi : (2 * 0 + m - 2) * Lξ + (2 * (k + 1 - 0) - m) * Lξ = (2 * k) * Lξ := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hW : (dR - 1 - m) * w + ((k + 1 - 0) + m) * w = (k + dR) * w := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hWsplit : (k + dR) * w = (k + 2) * w + (dR - 2) * w := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hxisplit : (2 * (k + 1) - 1) * Lξ = (2 * k) * Lξ + Lξ := by
    have h21 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h21, Nat.add_mul, Nat.one_mul]
  have hLexp : Lξ = (dR - 1) * w + (dR - 1) := by
    rw [hLξ, Nat.mul_add, Nat.mul_one]
  have hmerge : (dR - 2) * w + w = (dR - 1) * w := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  calc (0 + 1 - 1) * w + (2 * 0 + m - 2) * Lξ + nB
        + (m + ((k + 1 - 0) + m) * w + (2 * (k + 1 - 0) - m) * Lξ)
      = ((dR - 1 - m) * w + ((k + 1 - 0) + m) * w)
          + ((2 * 0 + m - 2) * Lξ + (2 * (k + 1 - 0) - m) * Lξ)
          + ((DR - m) + m) := by
        rw [hnB]; ring
    _ = (k + dR) * w + (2 * k) * Lξ + ((DR - m) + m) := by rw [hW, hxi]
    _ = (k + 2) * w + (dR - 2) * w + (2 * k) * Lξ + ((DR - m) + m) := by rw [hWsplit]
    _ ≤ (k + 2) * w + (dR - 2) * w + (2 * k) * Lξ + (dH + w) := by
        have : (DR - m) + m ≤ dH + w := by omega
        omega
    _ ≤ 1 + (k + 2) * w + (2 * k) * Lξ + Lξ := by
        have h1 : (dR - 2) * w + (dH + w) ≤ 1 + Lξ := by
          have h2 : (dR - 2) * w + w = (dR - 1) * w := hmerge
          rw [hLexp]
          omega
        omega
    _ = 1 + (k + 2) * w + (2 * (k + 1) - 1) * Lξ := by rw [hxisplit]; ring

/-! ## The anchored induction for the repaired recursion -/

/-- The specialized Hasse polynomial vanishes once the order exceeds the `Y`-degree. -/
theorem specializedHasse_eq_zero_of_natDegreeY_lt (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ)
    {m : ℕ} (hm : Bivariate.natDegreeY R < m) :
    Polynomial.Bivariate.evalX (Polynomial.C x₀)
      (hasseDerivX i1 (hasseDerivY m R)) = 0 := by
  rw [hasseDerivY_eq_zero_of_natDegreeY_lt R hm]
  have hX : hasseDerivX i1 (0 : F[X][X][Y]) = 0 := by
    rw [hasseDerivX]
    exact Polynomial.sum_zero_index _
  rw [hX, Polynomial.Bivariate.evalX_eq_map, Polynomial.map_zero]

/-- The repaired cell coefficient vanishes at the zero cells (`Σλ > d_R`). -/
theorem B_coeffC_eq_zero_of_natDegreeY_lt (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) (hm : Bivariate.natDegreeY R < sigmaLambda lam) :
    B_coeffC (H := H) x₀ R i1 lam = 0 := by
  have hp0 := specializedHasse_eq_zero_of_natDegreeY_lt x₀ R i1 hm
  have hcl : ∀ kk, hasseCoeffRepr𝒪_cleared H x₀ R i1 (sigmaLambda lam) kk = 0 := by
    intro kk
    refine Polynomial.ext fun b => ?_
    rw [hasseCoeffRepr𝒪_cleared_coeff, hp0]
    simp
  rw [B_coeffC]
  by_cases hi1 : i1 = 0
  · subst hi1
    rw [if_pos rfl, if_neg (by omega), hp0]
    simp
  · rw [if_neg hi1, hcl, map_zero]
    exact smul_zero _

/-- The `i1 = 0` cells have at least two parts (the single-part partition of `k+1` is the
excluded indiscrete one). -/
theorem two_le_sigmaLambda_of_i1_zero {k : ℕ} (lam : Nat.Partition (k + 1 - 0))
    (hlam : (k + 1) ∉ lam.parts) : 2 ≤ sigmaLambda lam := by
  rw [sigmaLambda]
  by_contra hcon
  push_neg at hcon
  interval_cases h : Multiset.card lam.parts
  · -- no parts: the sum cannot be k+1
    have hsum := lam.parts_sum
    rw [Multiset.card_eq_zero.mp h] at hsum
    simp at hsum
  · -- one part: it must be k+1, which is excluded
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
    have hsum := lam.parts_sum
    rw [ha] at hsum
    simp at hsum
    rw [ha, hsum] at hlam
    exact hlam (by simpa using Multiset.mem_singleton_self (k + 1))

/-- **The `m = d_R` saved budget** (the top cell of the `i1 = 0` column): there the
repaired coefficient is just the exact quotient `c₀/W`, with
`Λ ≤ (D_R − d_R) − degW` (the division saves a full `degW`). -/
theorem B_coeffC_weight_le_anchored_zero_top
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hWne : H.leadingCoeff ≠ 0)
    (x₀ : F) (R : F[X][X][Y]) {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    {m : ℕ} (lam : Nat.Partition m)
    (hdvd : H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY (sigmaLambda lam) R))).coeff
        (Bivariate.natDegreeY R - sigmaLambda lam))
    (htop : sigmaLambda lam = Bivariate.natDegreeY R) :
    weight_Λ_over_𝒪 hH (B_coeffC (H := H) x₀ R 0 lam) D
      ≤ WithBot.some ((DR - Bivariate.natDegreeY R) - (H.leadingCoeff).natDegree) := by
  rw [B_coeffC, if_pos rfl, if_neg (by omega), zero_add]
  refine le_trans (weight_Λ_over_𝒪_nsmul_le H hH hDH _ _) ?_
  obtain ⟨c', hc'⟩ := hdvd
  have hdivval : (Polynomial.Bivariate.evalX (Polynomial.C x₀)
      (hasseDerivX 0 (hasseDerivY (sigmaLambda lam) R))).coeff
        (Bivariate.natDegreeY R - sigmaLambda lam) / H.leadingCoeff = c' := by
    rw [hc']
    exact mul_div_cancel_left₀ c' hWne
  rw [hdivval]
  rcases eq_or_ne c' 0 with hc0 | hc0
  · subst hc0
    rw [map_zero, zero_mul, map_zero, weight_Λ_over_𝒪_zero]
    exact bot_le
  · refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
    refine le_trans (weight_Λ_C_mul_X_pow_le c' _ D) ?_
    refine WithBot.coe_le_coe.mpr ?_
    have hshape := specializedHasse_coeff_natDegree_le_of_total (x₀ := x₀) htotal 0
      (sigmaLambda lam) (Bivariate.natDegreeY R - sigmaLambda lam)
    have hmul : ((H.leadingCoeff) * c').natDegree
        = (H.leadingCoeff).natDegree + c'.natDegree :=
      Polynomial.natDegree_mul hWne hc0
    rw [hc', hmul] at hshape
    have hb0 : Bivariate.natDegreeY R - sigmaLambda lam = 0 := by omega
    rw [hb0]
    simp only [Nat.zero_mul, Nat.zero_add]
    omega

/-- **The anchored closing arithmetic for the `i1 = 0` TOP cell (`m = d_R`)**: the
exact-quotient budget closes the raw ledger. -/
theorem harith_anchored_zero_top {k m DR dR dH w D Lξ nB : ℕ}
    (hm2 : 2 ≤ m) (hms : m ≤ k + 1) (hmdR : m = dR)
    (hdR2 : 2 ≤ dR) (hdH1 : 1 ≤ dH) (hdHdR : dH ≤ dR)
    (hD : D = dH + w) (hDR : DR ≤ D)
    (hnB : nB = (DR - dR) - w)
    (hLξ : Lξ = (dR - 1) * (w + 1)) :
    (0 + 1 - 1) * w + (2 * 0 + m - 2) * Lξ + nB
      + (m + ((k + 1 - 0) + m) * w + (2 * (k + 1 - 0) - m) * Lξ)
    ≤ 1 + (k + 2) * w + (2 * (k + 1) - 1) * Lξ := by
  subst hmdR
  have hxi : (2 * 0 + m - 2) * Lξ + (2 * (k + 1 - 0) - m) * Lξ = (2 * k) * Lξ := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hW : ((k + 1 - 0) + m) * w = (k + 2) * w + (m - 1) * w := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hxisplit : (2 * (k + 1) - 1) * Lξ = (2 * k) * Lξ + Lξ := by
    have h21 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h21, Nat.add_mul, Nat.one_mul]
  have hLexp : Lξ = (m - 1) * w + (m - 1) := by
    rw [hLξ, Nat.mul_add, Nat.mul_one]
  calc (0 + 1 - 1) * w + (2 * 0 + m - 2) * Lξ + nB
        + (m + ((k + 1 - 0) + m) * w + (2 * (k + 1 - 0) - m) * Lξ)
      = ((k + 1 - 0) + m) * w
          + ((2 * 0 + m - 2) * Lξ + (2 * (k + 1 - 0) - m) * Lξ)
          + (nB + m) := by ring
    _ = (k + 2) * w + (m - 1) * w + (2 * k) * Lξ + (nB + m) := by
        rw [hW, hxi]
    _ ≤ 1 + (k + 2) * w + (2 * k) * Lξ + Lξ := by
        have h1 : (m - 1) * w + (nB + m) ≤ 1 + Lξ := by
          rw [hLexp, hnB]
          omega
        omega
    _ = 1 + (k + 2) * w + (2 * (k + 1) - 1) * Lξ := by rw [hxisplit]; ring

/-- **Generic structured partition-product bound** (any family `β`): the proven
multiset telescoping, family-abstracted so it applies to `βHenselC`. -/
theorem partitionProd_family_weight_le
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (k i1 : ℕ) (B0 wW xξ : ℕ)
    (β : ℕ → 𝒪 H)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (β l) D
        ≤ WithBot.some (B0 + (l + 1) * wW + (2 * l - 1) * xξ))
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts) :
    weight_Λ_over_𝒪 hH
        (partitionProd lam (fun l => if _h : l < k + 1 then β l else 0)) D
      ≤ WithBot.some
          (sigmaLambda lam * B0 + ((k + 1 - i1) + sigmaLambda lam) * wW
            + (2 * (k + 1 - i1) - sigmaLambda lam) * xξ) := by
  classical
  have hcongr : partitionProd lam (fun l => if _h : l < k + 1 then β l else 0)
      = partitionProd lam (fun l => β l) :=
    partitionProd_surviving_guard lam hlam (fun l => β l) 0
  rw [hcongr]
  refine le_trans (partitionProd_weight_le H hH hDH lam (fun l => β l)) ?_
  have hkey : (lam.parts.map (fun l => weight_Λ_over_𝒪 hH (β l) D)).sum
      ≤ WithBot.some
          ((lam.parts.map (fun l => B0 + (l + 1) * wW + (2 * l - 1) * xξ)).sum) := by
    have hmem : ∀ l ∈ lam.parts,
        weight_Λ_over_𝒪 hH (β l) D
          ≤ WithBot.some (B0 + (l + 1) * wW + (2 * l - 1) * xξ) :=
      fun l hl => hIH l (surviving_parts_lt lam hlam hl)
    revert hmem
    generalize lam.parts = ms
    intro hmem
    induction ms using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
        rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
          WithBot.coe_add]
        refine add_le_add (hmem a (Multiset.mem_cons_self a s)) ?_
        exact ih (fun l hl => hmem l (Multiset.mem_cons_of_mem hl))
  refine le_trans hkey ?_
  rw [sum_map_structured_general lam.parts B0 wW xξ (fun l hl => lam.parts_pos hl)]
  rw [lam.parts_sum, sigmaLambda, show Multiset.card lam.parts = lam.parts.card from rfl]

/-- **The per-term discharge for the repaired recursion** — EVERY cell, no per-cell
hypothesis: zero cells vanish; live cells route through the matching budget + closing
arithmetic (`i1 ≥ 1` general, `i1 = 0` saved, `i1 = 0` top). -/
theorem anchoredSuccTermBoundC (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (hDRD : DR ≤ D) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (hdvd : ∀ mm : ℕ, H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY mm R))).coeff (Bivariate.natDegreeY R - mm))
    (k : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHenselC (H := H) x₀ R hHyp l) D
        ≤ WithBot.some (structuredBound H R D l))
    (i1 : ℕ) (hi1 : i1 ∈ Finset.range (k + 2))
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts) :
    weight_Λ_over_𝒪 hH
        ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
          * B_coeffC (H := H) x₀ R i1 lam
          * partitionProd lam
              (fun l => if _h : l < k + 1 then βHenselC (H := H) x₀ R hHyp l else 0)) D
      ≤ WithBot.some (structuredBound H R D (k + 1)) := by
  classical
  by_cases hzero : Bivariate.natDegreeY R < sigmaLambda lam
  · -- zero cell
    rw [B_coeffC_eq_zero_of_natDegreeY_lt x₀ R i1 lam hzero, mul_zero, zero_mul,
      weight_Λ_over_𝒪_zero]
    exact bot_le
  push_neg at hzero
  -- shared facts
  have hi1le : i1 ≤ k + 1 := by
    have := Finset.mem_range.mp hi1
    omega
  have hdY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hdH1 : 1 ≤ Bivariate.natDegreeY H := by omega
  have hw : D - Bivariate.natDegreeY H = (H.leadingCoeff).natDegree := by omega
  have hWne : H.leadingCoeff ≠ 0 := by
    intro h0
    have : H = 0 := Polynomial.leadingCoeff_eq_zero.mp h0
    rw [this] at hH
    simp at hH
  have hmS : sigmaLambda lam ≤ k + 1 - i1 := by
    rw [sigmaLambda]
    calc Multiset.card lam.parts
        = (lam.parts.map (fun _ => 1)).sum := by simp
      _ ≤ (lam.parts.map id).sum := Multiset.sum_map_le_sum_map _ _
          (fun l hl => lam.parts_pos hl)
      _ = lam.parts.sum := by simp
      _ = k + 1 - i1 := lam.parts_sum
  have hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
      ≤ WithBot.some
        ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) :=
    ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hD_Rx0
  -- the four factor bounds
  have hW : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)) D
      ≤ WithBot.some ((i1 + deltaSave i1 - 1) * (H.leadingCoeff).natDegree) := by
    refine le_trans (weight_Λ_over_𝒪_pow_le H hH hDH _ _) ?_
    exact nsmul_withBot_le _ _ (weight_Λ_over_𝒪_W H hH hDH)
  have hXi : weight_Λ_over_𝒪 hH
      ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)) D
      ≤ WithBot.some ((2 * i1 + sigmaLambda lam - 2)
          * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
    refine le_trans (weight_Λ_over_𝒪_pow_le H hH hDH _ _) ?_
    exact nsmul_withBot_le _ _ hξ
  have hPi : weight_Λ_over_𝒪 hH
      (partitionProd lam
        (fun l => if _h : l < k + 1 then βHenselC (H := H) x₀ R hHyp l else 0)) D
      ≤ WithBot.some (sigmaLambda lam * 1
          + ((k + 1 - i1) + sigmaLambda lam) * (H.leadingCoeff).natDegree
          + (2 * (k + 1 - i1) - sigmaLambda lam)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
    refine partitionProd_family_weight_le hH hDH k i1 1 (H.leadingCoeff).natDegree
      ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))
      (βHenselC (H := H) x₀ R hHyp) ?_ lam hlam
    intro l hl
    have := hIH l hl
    unfold structuredBound at this
    exact this
  -- decompose the product into the four factors
  refine le_trans (weight_Λ_over_𝒪_mul_le H hH hDH _ _) ?_
  refine le_trans (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) le_rfl) ?_
  refine le_trans (add_le_add
    (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) le_rfl) le_rfl) ?_
  -- dispatch by cell class through the matching budget
  rcases Nat.eq_zero_or_pos i1 with hi0 | hi1pos
  · -- i1 = 0
    subst hi0
    have hm2 : 2 ≤ sigmaLambda lam := two_le_sigmaLambda_of_i1_zero lam hlam
    rcases Nat.lt_or_ge (sigmaLambda lam) (Bivariate.natDegreeY R) with hlt | hge
    · -- saved budget, 2 ≤ m < d_R
      have hB := B_coeffC_weight_le_anchored_zero hH hDH (by omega) hWne x₀ R htotal
        hvanish lam (hdvd (sigmaLambda lam)) (by omega) hdRDR
      refine le_trans (add_le_add (add_le_add (add_le_add hW hXi) hB) hPi) ?_
      rw [show ∀ a b c d : ℕ, (WithBot.some a + WithBot.some b + WithBot.some c
          + WithBot.some d) = WithBot.some (a + b + c + d) from fun _ _ _ _ => rfl]
      refine WithBot.coe_le_coe.mpr ?_
      unfold structuredBound
      rw [Nat.mul_one, hw]
      exact harith_anchored_zero hm2 (by omega) (by omega) hdR2 (by omega) hdHdR hdRDR
        (by omega) hDRD rfl rfl
    · -- top cell, m = d_R
      have htopeq : sigmaLambda lam = Bivariate.natDegreeY R := by omega
      have hB := B_coeffC_weight_le_anchored_zero_top hH hDH hWne x₀ R htotal lam
        (hdvd (sigmaLambda lam)) htopeq
      refine le_trans (add_le_add (add_le_add (add_le_add hW hXi) hB) hPi) ?_
      rw [show ∀ a b c d : ℕ, (WithBot.some a + WithBot.some b + WithBot.some c
          + WithBot.some d) = WithBot.some (a + b + c + d) from fun _ _ _ _ => rfl]
      refine WithBot.coe_le_coe.mpr ?_
      unfold structuredBound
      rw [Nat.mul_one, hw]
      exact harith_anchored_zero_top hm2 (by omega) htopeq hdR2 (by omega) hdHdR
        (by omega) hDRD rfl rfl
  · -- i1 ≥ 1 (including the top m = 0 cell)
    have hδ : deltaSave i1 = 0 := by
      rw [deltaSave, if_neg (by omega : ¬ i1 = 0)]
    have hB := B_coeffC_weight_le_anchored_pos hH hDH (by omega) x₀ R htotal hvanish
      (by omega : i1 ≠ 0) lam
    refine le_trans (add_le_add (add_le_add (add_le_add hW hXi) hB) hPi) ?_
    rw [show ∀ a b c d : ℕ, (WithBot.some a + WithBot.some b + WithBot.some c
        + WithBot.some d) = WithBot.some (a + b + c + d) from fun _ _ _ _ => rfl]
    refine WithBot.coe_le_coe.mpr ?_
    unfold structuredBound
    rw [Nat.mul_one, hδ, hw]
    exact harith_anchored hi1pos hi1le hmS hzero hdR2 (by omega) hdHdR hdRDR (by omega)
      hDRD rfl rfl

/-- **THE REPAIRED ANCHORED (P1) STRUCTURED BOUND — NO per-cell hypotheses.** Every
Hensel numerator of the repaired recursion satisfies the paper's structured invariant at
the anchor, with all cells discharged. -/
theorem βHenselC_weight_bound_anchored (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (hDRD : DR ≤ D) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (hdvd : ∀ mm : ℕ, H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY mm R))).coeff (Bivariate.natDegreeY R - mm))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHenselC (H := H) x₀ R hHyp t) D
      ≤ WithBot.some (structuredBound H R D t) := by
  classical
  induction t using Nat.strong_induction_on with
  | _ t hIH =>
    match t with
    | 0 =>
        rw [βHenselC_zero]
        refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
        have hweq : weight_Λ (Polynomial.X : F[X][Y]) H D
            = WithBot.some (D + 1 - Bivariate.natDegreeY H) := by
          rw [weight_Λ, Polynomial.support_X (by norm_num)]
          simp
        rw [hweq]
        refine WithBot.coe_le_coe.mpr ?_
        unfold structuredBound
        have hdY : Bivariate.natDegreeY H = H.natDegree := rfl
        omega
    | (k + 1) =>
        rw [βHenselC_succ]
        refine le_trans (weight_Λ_over_𝒪_neg H hH hDH _) ?_
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun i1 hi1 => ?_)
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun lam hlam => ?_)
        exact anchoredSuccTermBoundC x₀ R hHyp hH hDH htight hWdeg hD_Rx0 hdR2 hdHdR
          htotal hvanish hDRD hdRDR hdvd k (fun l hl => hIH l (by omega)) i1 hi1 lam
          (Finset.mem_filter.mp hlam).2

/-- **The repaired anchored (P1) LOOSE bound** `(2t+1)·d_R·D` — all cells discharged,
via the proven structured collapse. -/
theorem βHenselC_weight_bound_anchored_loose (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hWdeg : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHdR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    (hDRD : DR ≤ D) (hdRDR : Bivariate.natDegreeY R ≤ DR)
    (hdvd : ∀ mm : ℕ, H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY mm R))).coeff (Bivariate.natDegreeY R - mm))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHenselC (H := H) x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine le_trans (βHenselC_weight_bound_anchored x₀ R hHyp hH hDH htight hWdeg hD_Rx0
    hdR2 hdHdR htotal hvanish hDRD hdRDR hdvd t) ?_
  unfold structuredBound
  exact_mod_cast structured_weight_collapse
    (Bivariate.natDegreeY R) (Bivariate.natDegreeY H) D t (H.leadingCoeff).natDegree
    hdR2 (by simpa using hH) hdHdR hWdeg

/-! ## Source audit -/

#print axioms weight_Λ_C_mul_X_pow_le
#print axioms B_coeffC_weight_le_anchored_pos
#print axioms B_coeffC_weight_le_anchored_zero
#print axioms βHenselC_zero
#print axioms βHenselC_succ
#print axioms harith_anchored_zero
#print axioms B_coeffC_eq_zero_of_natDegreeY_lt
#print axioms two_le_sigmaLambda_of_i1_zero
#print axioms B_coeffC_weight_le_anchored_zero_top
#print axioms harith_anchored_zero_top
#print axioms partitionProd_family_weight_le
#print axioms anchoredSuccTermBoundC
#print axioms βHenselC_weight_bound_anchored
#print axioms βHenselC_weight_bound_anchored_loose

end BCIKS20.HenselNumerator
