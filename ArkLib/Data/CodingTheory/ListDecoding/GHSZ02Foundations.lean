/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib

/-!
# GHSZ02 foundations (standalone, land-ready)

Two layers:
  * `GHSZ02Core` — the analytic `1/e` factor `(1 - 1/q)^{q-1} ≥ 1/e`, Mathlib-only.
  * `GHSZ02RS`   — the GHSZ02 Lemma 19 / Corollary 20 averaging core for
    Reed-Solomon codes: there exists a word `w` whose relative-distance
    close-codeword list `Λ(C, δ, w)` is at least the averaged lower bound
    `q^k · C(n, ⌊δn⌋) · (q-1)^⌊δn⌋ / q^n`.

These are the genuine combinatorial/analytic foundations underlying
ABF26 Theorem 3.13 [GHSZ02 Cor 20]. They are additive lemmas: they do *not*
discharge the in-tree `rs_lambda_large_prime_ghsz02` target (see the blocker
note returned alongside this file).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

open scoped BigOperators NNReal
open Real Finset

namespace GHSZ02Core

/-- `(1 + 1/m)^m ≤ e` for all `m`, real form (one-line from `1 + x ≤ exp x`). -/
theorem one_add_inv_pow_le_e (m : ℕ) :
    (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero]
    exact Real.one_le_exp (by norm_num)
  · have hmpos : (0:ℝ) < m := by exact_mod_cast hm
    have hstep : (1 + 1 / (m : ℝ)) ≤ Real.exp (1 / (m : ℝ)) := by
      have := Real.add_one_le_exp (1 / (m : ℝ)); linarith
    have hbase_nonneg : (0:ℝ) ≤ 1 + 1 / (m : ℝ) := by positivity
    calc (1 + 1 / (m : ℝ)) ^ m
        ≤ (Real.exp (1 / (m : ℝ))) ^ m := pow_le_pow_left₀ hbase_nonneg hstep m
      _ = Real.exp ((m : ℝ) * (1 / (m : ℝ))) := by rw [← Real.exp_nat_mul]
      _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hmpos)]

/-- The GHSZ02 `1/e` factor: `(1 - 1/q)^{q-1} ≥ 1/e` for `q ≥ 2`. -/
theorem one_sub_inv_pow_ge_inv_e {q : ℕ} (hq : 2 ≤ q) :
    Real.exp (-1) ≤ (1 - 1 / (q : ℝ)) ^ (q - 1) := by
  have hq1 : 1 ≤ q := by omega
  set m : ℕ := q - 1 with hm
  have hmpos : 1 ≤ m := by omega
  have hmr : (m : ℝ) = (q : ℝ) - 1 := by
    have : (q : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast [Nat.cast_sub hq1]; ring
    linarith
  have hmrpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hqr : (q : ℝ) = (m : ℝ) + 1 := by linarith [hmr]
  have hqpos : (0:ℝ) < (q : ℝ) := by rw [hqr]; positivity
  have hfrac : (1 : ℝ) - 1 / (q : ℝ) = 1 / (1 + 1 / (m : ℝ)) := by
    rw [hqr]; have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmrpos
    rw [eq_div_iff (by positivity)]; field_simp; ring
  rw [hfrac]
  have hbase_pos : (0:ℝ) < 1 + 1 / (m : ℝ) := by positivity
  have hpow_pos : (0:ℝ) < (1 + 1 / (m : ℝ)) ^ m := pow_pos hbase_pos m
  rw [div_pow, one_pow, Real.exp_neg, one_div]
  exact inv_anti₀ hpow_pos (one_add_inv_pow_le_e m)

end GHSZ02Core

namespace GHSZ02RS

open CodingTheory ListDecodable

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Hamming ball volume around `x`: number of words within distance `r`. -/
noncomputable def ballVolF (x : ι → F) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : ι → F => hammingDist x y ≤ r)).card

/-- Hamming distance is translation-invariant on the right. -/
theorem hammingDist_add_right (x y t : ι → F) :
    hammingDist (x + t) (y + t) = hammingDist x y := by
  classical
  unfold hammingDist; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
  constructor
  · intro h hxy; exact h (by rw [hxy])
  · intro h hxy; exact h (by simpa using add_right_cancel hxy)

/-- The Hamming-ball volume is independent of the center. -/
theorem ballVolF_eq (x x' : ι → F) (r : ℕ) : ballVolF x r = ballVolF x' r := by
  classical
  unfold ballVolF
  refine Finset.card_bij' (fun y _ => y + (x' - x)) (fun z _ => z - (x' - x)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have heq : hammingDist x' (y + (x' - x)) = hammingDist x y := by
      have h1 : x' = x + (x' - x) := by abel
      calc hammingDist x' (y + (x' - x))
          = hammingDist (x + (x' - x)) (y + (x' - x)) := by rw [← h1]
        _ = hammingDist x y := hammingDist_add_right x y (x' - x)
    rw [heq]; exact hy
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have heq : hammingDist x (z - (x' - x)) = hammingDist x' z := by
      have key := hammingDist_add_right x (z - (x' - x)) (x' - x)
      have e1 : x + (x' - x) = x' := by abel
      have e2 : (z - (x' - x)) + (x' - x) = z := by abel
      rw [e1, e2] at key; exact key.symm
    rw [heq]; exact hz
  · intro y _; funext i; simp
  · intro z _; funext i; simp

/-- Per-codeword agreement count `|{c ∈ C : d(x,c) ≤ r}|`. -/
noncomputable def listAtF (C : Finset (ι → F)) (x : ι → F) (r : ℕ) : ℕ :=
  (C.filter (fun c => hammingDist x c ≤ r)).card

/-- Double-counting: `∑_x |B(x,r) ∩ C| = |C| · V`. -/
theorem sum_listAtF (C : Finset (ι → F)) (r : ℕ) (x₀ : ι → F) :
    (∑ x : ι → F, listAtF C x r) = C.card * ballVolF x₀ r := by
  classical
  unfold listAtF; simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
  have hinner : ∀ c : ι → F,
      (∑ x : ι → F, if hammingDist x c ≤ r then (1 : ℕ) else 0) = ballVolF c r := by
    intro c; rw [← Finset.card_filter]; unfold ballVolF
    apply Finset.card_bij' (fun x _ => x) (fun y _ => y)
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rwa [hammingDist_comm]
    · intro y hy; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rwa [hammingDist_comm]
    · intro x _; rfl
    · intro y _; rfl
  rw [Finset.sum_congr rfl (fun c _ => hinner c)]
  rw [Finset.sum_congr rfl (fun c _ => ballVolF_eq c x₀ r)]
  rw [Finset.sum_const, smul_eq_mul]

/-- GHSZ02 Lemma 19 averaging existence (integer form). -/
theorem exists_word_listAtF_ge (C : Finset (ι → F)) (r : ℕ) :
    ∃ x₀ : ι → F, C.card * ballVolF x₀ r ≤ (Fintype.card (ι → F)) * listAtF C x₀ r := by
  classical
  haveI : Nonempty (ι → F) := inferInstance
  obtain ⟨x₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (ι → F))
    (fun x => listAtF C x r) Finset.univ_nonempty
  refine ⟨x₀, ?_⟩
  have hsum := sum_listAtF C r x₀
  have hle : (∑ x : ι → F, listAtF C x r)
      ≤ (Finset.univ : Finset (ι → F)).card * listAtF C x₀ r := by
    calc (∑ x : ι → F, listAtF C x r)
        ≤ (Finset.univ : Finset (ι → F)).card • (listAtF C x₀ r) :=
          Finset.sum_le_card_nsmul _ _ _ (fun x _ => hmax x (Finset.mem_univ x))
      _ = (Finset.univ : Finset (ι → F)).card * listAtF C x₀ r := by rw [smul_eq_mul]
  rw [hsum] at hle; rwa [Finset.card_univ] at hle

/-- Relative↔absolute radius bridge (same as Elias proof). -/
theorem closeCodewordsRel_iff
    (C : Submodule F (ι → F)) (w : ι → F) (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (c : ι → F) :
    (c ∈ closeCodewordsRel (↑C : Set (ι → F)) w δ)
      ↔ (c ∈ C ∧ hammingDist w c ≤ ⌊δ * Fintype.card ι⌋₊) := by
  classical
  set n : ℕ := Fintype.card ι with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, SetLike.mem_coe]
  refine and_congr_right (fun _ => ?_)
  simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
  rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ)),
    ← hn_def, Nat.le_floor_iff (mul_nonneg hδ_nonneg (Nat.cast_nonneg n))]
  congr!

/-- **ABF26 Theorem 3.13 / GHSZ02 Corollary 20 — averaging core (full combinatorial strength).**
For `C = ReedSolomon.code domain k`, `q=|F|`, `n=|ι|`, `k≤n`, `0<δ<1`: there is a word `w` with
`q^k · C(n,⌊δn⌋) · (q-1)^⌊δn⌋  ≤  qⁿ · |Λ(C,δ,w)|`. -/
theorem ghsz02_rs_averaging_core
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hk : k ≤ Fintype.card ι) :
    ∃ w : ι → F,
      (Fintype.card F) ^ k
          * (Nat.choose (Fintype.card ι) ⌊δ * Fintype.card ι⌋₊
              * (Fintype.card F - 1) ^ ⌊δ * Fintype.card ι⌋₊)
        ≤ (Fintype.card F) ^ (Fintype.card ι)
            * (closeCodewordsRel ((ReedSolomon.code domain k : Submodule F (ι → F)) :
                  Set (ι → F)) w δ).ncard := by
  classical
  haveI : DecidablePred (fun c : ι → F => c ∈ ReedSolomon.code domain k) := fun c => Classical.dec _
  set C : Submodule F (ι → F) := ReedSolomon.code domain k with hC_def
  haveI : DecidablePred (fun c : ι → F => c ∈ C) := fun c => Classical.dec _
  set q : ℕ := Fintype.card F with hq_def
  set n : ℕ := Fintype.card ι with hn_def
  set r : ℕ := ⌊δ * (n : ℝ)⌋₊ with hr_def
  have hδ_nonneg : (0 : ℝ) ≤ δ := le_of_lt hδ_pos
  set CF : Finset (ι → F) := Finset.univ.filter (fun c : ι → F => c ∈ C) with hCF_def
  have hCF_card : CF.card = q ^ k := by
    haveI : Fintype (↥C) := Fintype.ofFinite _
    rw [hCF_def, ← Fintype.card_subtype (fun c : ι → F => c ∈ C)]
    rw [Module.card_eq_pow_finrank (K := F) (V := ↥C)]
    congr 1
    have hdim : LinearCode.dim C = min k n := by rw [hC_def]; exact ReedSolomon.dim_eq_min_deg_card
    simp only [LinearCode.dim] at hdim
    rw [hdim]; omega
  obtain ⟨w, hw⟩ := exists_word_listAtF_ge CF r
  refine ⟨w, ?_⟩
  have hcard_words : Fintype.card (ι → F) = q ^ n := by rw [Fintype.card_fun, hq_def, hn_def]
  have hballvol_eq : ballVolF w r = hammingBallVolume q δ n := by
    have hb := hammingBallVolume_eq_ncard_hammingBall (F := F) (ι := ι) δ w
    rw [show hammingBallVolume q δ n
          = hammingBallVolume (Fintype.card F) δ (Fintype.card ι) from rfl, hb]
    unfold ballVolF; rw [← Set.ncard_coe_finset]; congr 1; ext y
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq, ListDecodable.hammingBall]
    constructor
    · intro h; rw [hr_def, hn_def] at h; convert h using 2
    · intro h; rw [hr_def, hn_def]; convert h using 2
  have hballvol_ge : (Nat.choose n r * (q - 1) ^ r) ≤ ballVolF w r := by
    rw [hballvol_eq]; exact hammingBallVolume_ge_term_of_le_floor q δ n r le_rfl
  have hlist_eq : (closeCodewordsRel (↑C : Set (ι → F)) w δ).ncard = listAtF CF w r := by
    unfold listAtF; rw [← Set.ncard_coe_finset]; congr 1; ext c
    simp only [hCF_def, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    have h := closeCodewordsRel_iff C w δ hδ_nonneg c
    rw [h]
  calc q ^ k * (Nat.choose n r * (q - 1) ^ r)
      ≤ q ^ k * ballVolF w r := by apply Nat.mul_le_mul_left; exact hballvol_ge
    _ = CF.card * ballVolF w r := by rw [hCF_card]
    _ ≤ (Fintype.card (ι → F)) * listAtF CF w r := hw
    _ = q ^ n * listAtF CF w r := by rw [hcard_words]
    _ = q ^ n * (closeCodewordsRel (↑C : Set (ι → F)) w δ).ncard := by rw [hlist_eq]

end GHSZ02RS
