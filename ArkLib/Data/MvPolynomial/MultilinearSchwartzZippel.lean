/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# Multilinear Schwartz–Zippel bound (sum-check round soundness)

Specialising `MvPolynomial.schwartz_zippel_counting` to **multilinear** polynomials via the
total-degree bound `totalDegree_le_card_of_mem_restrictDegree_one` (a multilinear polynomial in
`s` variables has total degree `≤ s`):

  **a nonzero multilinear `p : MvPolynomial (Fin s) F` has at most `s · |F|^{s-1}` zeros in
  `F^s`** — equivalently, a uniformly random point is a zero with probability `≤ s/|F|`.

This is exactly the soundness of one sum-check round (and of multilinear identity testing): two
distinct multilinear polynomials agree at a uniformly random point with probability `≤ s/|F|`.
-/

namespace MvPolynomial

open Finset

variable {s : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Multilinear Schwartz–Zippel (count form).**  A nonzero multilinear polynomial over `Fin s`
has at most `s · |F|^{s-1}` zeros, i.e. `|zeros| · |F| ≤ s · |F|^s`. -/
theorem multilinear_zeros_card_mul_le
    {p : MvPolynomial (Fin s) F} (hp : p ∈ F⦃≤ 1⦄[X (Fin s)]) (hp0 : p ≠ 0) :
    (Finset.univ.filter (fun x : Fin s → F => eval x p = 0)).card * Fintype.card F
      ≤ s * (Fintype.card F) ^ s := by
  classical
  have hFpos : 0 < Fintype.card F := Fintype.card_pos
  -- total degree of a multilinear polynomial is ≤ s
  have hdeg : p.totalDegree ≤ s := by
    have := totalDegree_le_card_of_mem_restrictDegree_one (σ := Fin s) (R := F) hp
    simpa using this
  -- Schwartz–Zippel over the full grid `S i = univ`
  have hsz := schwartz_zippel_counting p hp0 (fun _ => (Finset.univ : Finset F))
    s (Fintype.card F) hdeg hFpos (fun i => by simp)
  -- `piFinset (fun _ => univ) = univ` and `∏ i, |univ| = |F|^s`
  have hpi : (Fintype.piFinset (fun _ : Fin s => (Finset.univ : Finset F)))
      = (Finset.univ : Finset (Fin s → F)) := by
    ext x; simp
  have hprod : (∏ _i : Fin s, (Finset.univ : Finset F).card) = (Fintype.card F) ^ s := by
    simp [Finset.card_univ]
  rw [hpi, hprod] at hsz
  exact hsz

/-- **Multilinear identity testing.**  Two distinct multilinear polynomials over `Fin s` agree at
at most `s · |F|^{s-1}` points: `|{x : eval x p = eval x q}| · |F| ≤ s · |F|^s`. -/
theorem multilinear_agree_card_mul_le
    {p q : MvPolynomial (Fin s) F}
    (hp : p ∈ F⦃≤ 1⦄[X (Fin s)]) (hq : q ∈ F⦃≤ 1⦄[X (Fin s)]) (hpq : p ≠ q) :
    (Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card * Fintype.card F
      ≤ s * (Fintype.card F) ^ s := by
  classical
  have hsub : p - q ∈ F⦃≤ 1⦄[X (Fin s)] := Submodule.sub_mem _ hp hq
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hmain := multilinear_zeros_card_mul_le hsub hne
  -- `eval x p = eval x q ↔ eval x (p - q) = 0`
  have hfilter : (Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q))
      = (Finset.univ.filter (fun x : Fin s → F => eval x (p - q) = 0)) := by
    apply Finset.filter_congr
    intro x _
    simp [map_sub, sub_eq_zero]
  rw [hfilter]
  exact hmain

/-- **Multilinear identity testing, probability-ratio form.**  Two distinct multilinear
polynomials over `Fin s` agree at a uniformly random point with probability at most `s/|F|`:
`|{x : eval x p = eval x q}| / |F|^s ≤ s / |F|`.  This is the soundness bound of one sum-check
round in directly-usable ratio form. -/
theorem multilinear_agree_prob_le
    {p q : MvPolynomial (Fin s) F}
    (hp : p ∈ F⦃≤ 1⦄[X (Fin s)]) (hq : q ∈ F⦃≤ 1⦄[X (Fin s)]) (hpq : p ≠ q) :
    ((Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card : ℝ)
        / (Fintype.card F : ℝ) ^ s
      ≤ (s : ℝ) / Fintype.card F := by
  have hFpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcount := multilinear_agree_card_mul_le hp hq hpq
  have hcountR :
      ((Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card : ℝ)
          * Fintype.card F
        ≤ (s : ℝ) * (Fintype.card F) ^ s := by exact_mod_cast hcount
  rw [div_le_div_iff₀ (by positivity) hFpos]
  -- |agree| · |F| ≤ s · |F|^s  ⟹  |agree| · |F| ≤ s · |F|^s  (rearranged)
  calc ((Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card : ℝ)
        * Fintype.card F
      ≤ (s : ℝ) * (Fintype.card F) ^ s := hcountR
    _ = (s : ℝ) * (Fintype.card F) ^ s := rfl

end MvPolynomial
