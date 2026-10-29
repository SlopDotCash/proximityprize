/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Lemmas

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Expectations
import Mathlib.Algebra.Order.Chebyshev
/-! # Johnson Bound Lemmas -/


namespace JohnsonBound

open Real Finset Fintype

/-- The `q`-ary Johnson bound function: `J'(q, δ) = ((q-1)/q) · (1 - √(1 - (q/(q-1)) · δ))`. -/
noncomputable def J' (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - √(1 - frac * δ))

section

variable {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {B : Finset (Fin n → F)} {i : Fin n}

/-- **Cauchy–Schwarz / power-mean lower bound on the column second moment.**
For any coordinate `i`, the sum of squares of the column counts `K B i α` is bounded
below by `|B|² / |F|`, equivalently `|B|² ≤ |F| · ∑_α (K B i α)²`. This is the key
*lower* bound that powers the q-ary Plotkin average-distance upper bound; it is the
convex dual of the `le_sum_choose_K` / `almost_johnson` lower bound, obtained from
`Finset.sq_sum_le_card_mul_sum_sq` applied to `K B i · : F → ℕ`. -/
lemma card_sq_le_card_F_mul_sum_K_sq :
    (B.card : ℚ) ^ 2 ≤ (card F : ℚ) * ∑ α : F, (K B i α : ℚ) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset F))
    (f := fun α : F => (K B i α : ℚ))
  rw [show (∑ α : F, (K B i α : ℚ)) = (B.card : ℚ) from by
    rw [← sum_K_eq_card (B := B) (i := i)]; push_cast; rfl] at h
  simpa only [card_univ] using h

/-- **q-ary Plotkin lower bound on `∑_α C₂(K B i α)`.**
The per-coordinate sum of `choose_2` of the column counts is bounded below by
`(|B|²/|F| - |B|)/2`. This is the Plotkin counterpart of `le_sum_choose_K`: where the
latter (via Jensen) lower-bounds `∑_α C₂(K)` by a convex expression used for the
*list-of-many* Johnson bound, this Cauchy–Schwarz form gives the cleaner `|B|²/q`
second-moment lower bound used for the q-ary Plotkin average-distance upper bound. -/
lemma sum_choose_K_i_ge_plotkin (h_card : 2 ≤ card F) :
    ((B.card : ℚ) ^ 2 / (card F : ℚ) - (B.card : ℚ)) / 2 ≤ sum_choose_K_i B i := by
  have hq_pos : (0 : ℚ) < card F := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) h_card
  have h_cs := card_sq_le_card_F_mul_sum_K_sq (B := B) (i := i)
  -- expand `sum_choose_K_i = ∑_α (K² - K)/2 = (∑K² - ∑K)/2`
  have h_expand : sum_choose_K_i B i
      = ((∑ α : F, (K B i α : ℚ) ^ 2) - (B.card : ℚ)) / 2 := by
    simp only [sum_choose_K_i, choose_2]
    rw [show (B.card : ℚ) = ∑ α : F, (K B i α : ℚ) from by
      rw [← sum_K_eq_card (B := B) (i := i)]; push_cast; rfl]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [h_expand]
  -- from `B.card² ≤ q · ∑ K²` we get `B.card²/q ≤ ∑ K²`
  have h_div : (B.card : ℚ) ^ 2 / (card F : ℚ) ≤ ∑ α : F, (K B i α : ℚ) ^ 2 := by
    rw [div_le_iff₀ hq_pos]; linarith [h_cs]
  linarith

/-- **Summed Plotkin lower bound.** Summing `sum_choose_K_i_ge_plotkin` over all `n`
coordinates: `∑_i ∑_α C₂(K B i α) ≥ n · (|B|²/|F| - |B|) / 2`. -/
lemma sum_sum_choose_K_ge_plotkin (h_card : 2 ≤ card F) :
    (n : ℚ) * (((B.card : ℚ) ^ 2 / (card F : ℚ) - (B.card : ℚ)) / 2) ≤
    ∑ i, sum_choose_K_i B i := by
  calc (n : ℚ) * (((B.card : ℚ) ^ 2 / (card F : ℚ) - (B.card : ℚ)) / 2)
      = ∑ _i : Fin n, (((B.card : ℚ) ^ 2 / (card F : ℚ) - (B.card : ℚ)) / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i, sum_choose_K_i B i :=
        Finset.sum_le_sum fun i _ => sum_choose_K_i_ge_plotkin (B := B) (i := i) h_card

/-- **q-ary Plotkin average-distance upper bound (`M-1` form).** For any code `B` over a
finite alphabet `F` of size `q ≥ 2` with `|B| ≥ 2`, the average pairwise Hamming distance
satisfies

  `(|B| - 1) · d(B) ≤ ((q-1)/q) · n · |B|`,

equivalently `d(B) ≤ ((q-1)/q) · n · |B|/(|B|-1)`. This is the classic q-ary Plotkin
average-distance bound. It is the convex *dual* of `almost_johnson`: where the latter
lower-bounds `∑_α C₂(K)` by a Jensen expression, this bound uses the Cauchy–Schwarz
second-moment lower bound `∑_α K(α)² ≥ |B|²/q` (`card_sq_le_card_F_mul_sum_K_sq`) to
*upper*-bound the average distance.

The factor is `(q-1)/q`, i.e. `1 - 1/q` (the maximal per-coordinate disagreement
probability for `q` symbols), **not** `q/(q-1)`. -/
lemma plotkin_avg_distance {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
    {B : Finset (Fin n → F)} (h_B : 2 ≤ B.card) (h_card : 2 ≤ card F) :
    ((B.card : ℚ) - 1) * d B ≤
      (((card F : ℚ) - 1) / (card F : ℚ)) * (n : ℚ) * (B.card : ℚ) := by
  have hq_pos : (0 : ℚ) < card F := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) h_card
  have hM_pos : (0 : ℚ) < B.card := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) h_B
  -- ∑_i ∑_α C₂(K) = C₂(|B|) · (n - d)
  have h_eq := sum_sum_K_i_eq_n_sub_d (B := B) h_B
  -- ∑_i ∑_α C₂(K) ≥ n · (|B|²/q - |B|)/2
  have h_lb := sum_sum_choose_K_ge_plotkin (B := B) (n := n) h_card
  -- combine: C₂(|B|)·(n - d) ≥ n·(|B|²/q - |B|)/2
  rw [h_eq] at h_lb
  -- C₂(|B|) = |B|(|B|-1)/2
  have h_c2 : choose_2 (B.card : ℚ) = (B.card : ℚ) * ((B.card : ℚ) - 1) / 2 := by
    simp [choose_2]
  rw [h_c2] at h_lb
  -- h_lb : n·((|B|²/q - |B|)/2) ≤ |B|·(|B|-1)/2·(n - d)
  -- Clear denominators by multiplying through by `2·q > 0`.
  have hq_ne : (card F : ℚ) ≠ 0 := ne_of_gt hq_pos
  -- Polynomial form of h_lb after `· (2q)`:  n·(|B|² - q·|B|) ≤ q·|B|·(|B|-1)·(n - d)
  have h_poly : (n : ℚ) * ((B.card : ℚ) ^ 2 - (card F : ℚ) * (B.card : ℚ)) ≤
      (card F : ℚ) * ((B.card : ℚ) * ((B.card : ℚ) - 1)) * ((n : ℚ) - d B) := by
    have h2 := mul_le_mul_of_nonneg_left h_lb
      (show (0 : ℚ) ≤ 2 * (card F : ℚ) by positivity)
    calc (n : ℚ) * ((B.card : ℚ) ^ 2 - (card F : ℚ) * (B.card : ℚ))
        = 2 * (card F : ℚ) *
            ((n : ℚ) * (((B.card : ℚ) ^ 2 / (card F : ℚ) - (B.card : ℚ)) / 2)) := by
          field_simp [hq_ne]
      _ ≤ 2 * (card F : ℚ) *
            ((B.card : ℚ) * ((B.card : ℚ) - 1) / 2 * ((n : ℚ) - d B)) := h2
      _ = (card F : ℚ) * ((B.card : ℚ) * ((B.card : ℚ) - 1)) * ((n : ℚ) - d B) := by ring
  -- Goal cleared of `/q`: `q·((|B|-1)·d) ≤ (q-1)·n·|B|`.
  rw [show ((card F : ℚ) - 1) / (card F : ℚ) * (n : ℚ) * (B.card : ℚ)
      = (((card F : ℚ) - 1) * (n : ℚ) * (B.card : ℚ)) / (card F : ℚ) from by ring,
    le_div_iff₀ hq_pos]
  nlinarith [h_poly, hq_pos, hM_pos, mul_pos hM_pos hq_pos]

end

end JohnsonBound
