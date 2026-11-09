/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Extensions.Data.MvPolynomial.Multilinear
import ArkLib.Data.MvPolynomial.LowDegreeAgreement

/-!
# Multilinear Schwartz–Zippel bound (sum-check round soundness)

Specialising the low-degree agreement bounds to **multilinear** polynomials via the
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
  exact lowDegree_zeros_card_mul_le
    (by simpa using totalDegree_le_card_of_mem_restrictDegree_one hp) hp0

/-- **Multilinear identity testing.**  Two distinct multilinear polynomials over `Fin s` agree at
at most `s · |F|^{s-1}` points: `|{x : eval x p = eval x q}| · |F| ≤ s · |F|^s`. -/
theorem multilinear_agree_card_mul_le
    {p q : MvPolynomial (Fin s) F}
    (hp : p ∈ F⦃≤ 1⦄[X (Fin s)]) (hq : q ∈ F⦃≤ 1⦄[X (Fin s)]) (hpq : p ≠ q) :
    (Finset.univ.filter (fun x : Fin s → F => eval x p = eval x q)).card * Fintype.card F
      ≤ s * (Fintype.card F) ^ s := by
  exact lowDegree_agree_card_mul_le
    (by simpa using totalDegree_le_card_of_mem_restrictDegree_one hp)
    (by simpa using totalDegree_le_card_of_mem_restrictDegree_one hq) hpq

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
  exact lowDegree_agree_prob_le
    (by simpa using totalDegree_le_card_of_mem_restrictDegree_one hp)
    (by simpa using totalDegree_le_card_of_mem_restrictDegree_one hq) hpq

end MvPolynomial
