/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The agreement-threshold curve list bound (B2 / GG25 curve-decodability) (#389, #334)

The affine-line list bound (`LineListBound.line_agreement_card_le`) and the fleet's
`RootCounting.card_le_of_eFamily` (the `≥ 1`-coordinate / UDR form, `|G| ≤ (L−1)·#moving`) both
count the parameters at which a low-degree curve meets a target.  This file proves the
**agreement-threshold** generalization needed for the *list-decoding* (beyond-UDR) regime that the
δ\* window lives in: the number of parameters at which `≥ a` of `n` degree-`≤D` polynomials vanish,
weighted by `(a − b)`, is at most `D · n` (`b` = the identically-zero polynomials).

`curve_agreement_card_le` is the degree-`D` generalization of `line_agreement_card_le` (`D = 1`):
each nonzero `P i` has `≤ D` roots, so a double count over the moving positions gives
`|{γ : ≥ a of the Pᵢ vanish}| · (a − b) ≤ D · n`.  Specializing `b = a − 1` recovers the
`card_le_of_eFamily` shape; the general `(a − b)` factor is the curve-decodability list-size
tradeoff (a degree-`D` curve agreeing with a received word on `≥ a` positions occurs at
`≤ D·n/(a−b)` parameters).  For the curve `γ ↦ ∑ⱼ γʲ·gⱼ` agreeing with `y`, take
`P i = ∑ⱼ gⱼ(i)·Xʲ − y(i)`.  Axiom-clean.
-/

open Finset Polynomial

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **The curve list bound (degree-`D` generalization of the line list bound).**
Given `n` polynomials `P i` of degree `≤ D` over a field, the number of field elements `γ` that are
common roots of at least `a` of them (equivalently: at which at least `a` of the `P i` vanish) times
`(a − b)` is at most `D · n`, where `b` counts the identically-zero `P i`.  Each nonzero `P i` has
`≤ D` roots, so each "moving" position votes for `≤ D` parameters; double counting gives the bound.
For `D = 1` this is the affine line list bound; for the degree-`D` curve `γ ↦ ∑ⱼ γʲ·gⱼ` agreeing
with a received word `y`, take `P i = ∑ⱼ gⱼ(i)·Xʲ − y(i)`. -/
theorem curve_agreement_card_le {D : ℕ} (P : ι → Polynomial F)
    (hdeg : ∀ i, (P i).natDegree ≤ D) {a b : ℕ}
    (hb : (univ.filter (fun i => P i = 0)).card = b) (hab : b < a) :
    (univ.filter (fun γ : F => a ≤ (univ.filter (fun i => (P i).eval γ = 0)).card)).card * (a - b)
      ≤ D * Fintype.card ι := by
  classical
  set Heavy := univ.filter (fun γ : F => a ≤ (univ.filter (fun i => (P i).eval γ = 0)).card)
    with hHeavy
  set M := univ.filter (fun i => P i ≠ 0) with hM
  -- each heavy `γ` vanishes at `≥ a − b` of the moving positions
  have hlower : ∀ γ ∈ Heavy, a - b ≤ (M.filter (fun i => (P i).eval γ = 0)).card := by
    intro γ hγ
    have hagree : a ≤ (univ.filter (fun i => (P i).eval γ = 0)).card := by
      simpa [hHeavy] using (mem_filter.mp hγ).2
    -- split the agreement set by whether `P i = 0`
    have hsplit : (univ.filter (fun i => (P i).eval γ = 0)).card
        = b + (M.filter (fun i => (P i).eval γ = 0)).card := by
      rw [← Finset.card_filter_add_card_filter_not
        (s := univ.filter (fun i => (P i).eval γ = 0)) (p := fun i => P i = 0)]
      congr 1
      · rw [← hb]
        congr 1
        ext i
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨by rw [h]; simp, h⟩⟩
      · congr 1
        ext i
        simp only [hM, mem_filter, mem_univ, true_and]
        tauto
    omega
  -- each moving position contributes `≤ D` roots
  have hupper : ∀ i ∈ M, (univ.filter (fun γ => (P i).eval γ = 0)).card ≤ D := by
    intro i hi
    have hPne : P i ≠ 0 := (mem_filter.mp hi).2
    calc (univ.filter (fun γ => (P i).eval γ = 0)).card
        ≤ (P i).roots.toFinset.card := by
          apply Finset.card_le_card
          intro γ hγ
          rw [Multiset.mem_toFinset, Polynomial.mem_roots']
          exact ⟨hPne, (mem_filter.mp hγ).2⟩
      _ ≤ Multiset.card (P i).roots := Multiset.toFinset_card_le _
      _ ≤ (P i).natDegree := Polynomial.card_roots' _
      _ ≤ D := hdeg i
  -- double count the incidences `{(γ, i) : γ ∈ Heavy, i ∈ M, (P i).eval γ = 0}`
  have hcomm : ∑ i ∈ M, (Heavy.filter (fun γ => (P i).eval γ = 0)).card
      = ∑ γ ∈ Heavy, (M.filter (fun i => (P i).eval γ = 0)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  calc Heavy.card * (a - b)
      = ∑ _γ ∈ Heavy, (a - b) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ Heavy, (M.filter (fun i => (P i).eval γ = 0)).card := Finset.sum_le_sum hlower
    _ = ∑ i ∈ M, (Heavy.filter (fun γ => (P i).eval γ = 0)).card := hcomm.symm
    _ ≤ ∑ i ∈ M, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)))
          (hupper i hi)
    _ = D * M.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ D * Fintype.card ι := by
        apply Nat.mul_le_mul_left
        exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)

