/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# Low-degree multivariate agreement soundness (Schwartz–Zippel)

The general-degree multivariate agreement bound, specialising
`MvPolynomial.schwartz_zippel_counting` to the full grid `F^s`:

  **two distinct polynomials over `Fin s` of total degree `≤ d` agree at at most `d · |F|^{s-1}`
  points** — a uniformly random point witnesses agreement with probability `≤ d/|F|`.

This is the soundness primitive behind low-degree testing (FRI / STIR / DEEP) and the general
sum-check round: it strictly generalises the multilinear bound `multilinear_agree_*` (take
`d = s`).  Proven directly from `schwartz_zippel_counting` over `S i = univ`.
-/

namespace MvPolynomial

open Finset

variable {s : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Low-degree zeros bound.**  A nonzero polynomial of total degree `≤ d` over `Fin s` has at
most `d · |F|^{s-1}` zeros in `F^s`: `|zeros| · |F| ≤ d · |F|^s`. -/
theorem lowDegree_zeros_card_mul_le {p : MvPolynomial (Fin s) F} {d : ℕ}
    (hdeg : p.totalDegree ≤ d) (hp0 : p ≠ 0) :
    (Finset.univ.filter (fun x : Fin s → F => eval x p = 0)).card * Fintype.card F
      ≤ d * (Fintype.card F) ^ s := by
  classical
  have hFpos : 0 < Fintype.card F := Fintype.card_pos
  have hsz := schwartz_zippel_counting p hp0 (fun _ => (Finset.univ : Finset F))
    d (Fintype.card F) hdeg hFpos (fun i => by simp)
  have hpi : (Fintype.piFinset (fun _ : Fin s => (Finset.univ : Finset F)))
      = (Finset.univ : Finset (Fin s → F)) := by ext x; simp
  have hprod : (∏ _i : Fin s, (Finset.univ : Finset F).card) = (Fintype.card F) ^ s := by
    simp [Finset.card_univ]
  rw [hpi, hprod] at hsz
  exact hsz

/-- **Low-degree agreement bound (count form).**  Two distinct polynomials over `Fin s` of total
degree `≤ d` agree at at most `d · |F|^{s-1}` points. -/
theorem lowDegree_agree_card_mul_le {p q : MvPolynomial (Fin s) F} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) (hpq : p ≠ q) :
    (Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card * Fintype.card F
      ≤ d * (Fintype.card F) ^ s := by
  classical
  have hdeg : (p - q).totalDegree ≤ d := by
    rw [sub_eq_add_neg]
    refine le_trans (totalDegree_add p (-q)) ?_
    rw [totalDegree_neg]
    exact max_le hp hq
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hmain := lowDegree_zeros_card_mul_le hdeg hne
  have hfilter : (Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q))
      = (Finset.univ.filter (fun x : Fin s → F => eval x (p - q) = 0)) := by
    apply Finset.filter_congr
    intro x _
    simp [map_sub, sub_eq_zero]
  rw [hfilter]
  exact hmain

/-- **Low-degree agreement bound (probability-ratio form).**  Two distinct total-degree-`≤ d`
polynomials over `Fin s` agree at a uniformly random point with probability at most `d/|F|`. -/
theorem lowDegree_agree_prob_le {p q : MvPolynomial (Fin s) F} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) (hpq : p ≠ q) :
    ((Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card : ℝ)
        / (Fintype.card F : ℝ) ^ s
      ≤ (d : ℝ) / (Fintype.card F : ℝ) := by
  have hFpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcountR :
      ((Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card : ℝ)
          * Fintype.card F
        ≤ (d : ℝ) * (Fintype.card F) ^ s := by
    exact_mod_cast lowDegree_agree_card_mul_le hp hq hpq
  rw [div_le_div_iff₀ (by positivity) hFpos]
  exact hcountR

end MvPolynomial
