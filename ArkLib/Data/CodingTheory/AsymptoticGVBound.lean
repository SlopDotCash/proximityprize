/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GilbertVarshamovExistence
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallEntropy
import ArkLib.Data.CodingTheory.EntropyVolumeUpperBall

/-!
# The asymptotic Gilbert–Varshamov bound (rate ≥ 1 − H_q(δ))

Combining the Nat-level GV existence bound `gv_existence` (`q^n ≤ |C|·V(d−1)`) with the entropy
*upper* bound on the ball volume (`hammingBallVolume_le_qEntropy`, bridged to the `univ.filter`
convention) yields the classical **asymptotic Gilbert–Varshamov bound**: there exists a code with
minimum distance `≥ d` (below capacity) of rate `≥ 1 − H_q((d−1)/n)`, i.e.

  `q^{n·(1 − H_q((d−1)/n))} ≤ (n+1)·|C|`.

Helper lemmas `hammingBall_ncard_le_qEntropy` / `filter_ball_card_le_qEntropy` give the entropy
*upper* bound on the radius-`r` ball (the counterpart to `filter_ball_card_ge_qEntropy`).
`sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hammingBall_ncard_le_qEntropy {F : Type} [Fintype F] [DecidableEq F] [Zero F]
    (hq : 2 ≤ Fintype.card F) (r : ℕ) (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hcap : (r : ℝ) / (Fintype.card ι : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    ((ListDecodable.hammingBall (0 : ι → F) r).ncard : ℝ)
      ≤ ((Fintype.card ι : ℝ) + 1)
        * (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
            * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ))) := by
  set n := Fintype.card ι with hn
  have hn0 : 0 < n := lt_trans hr0 hrn
  have hfloor : ⌊(r : ℝ) / (n : ℝ) * (n : ℝ)⌋₊ = r := by
    rw [div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)]; exact Nat.floor_natCast r
  have heq : (ListDecodable.hammingBall (0 : ι → F) r).ncard
      = hammingBallVolume (Fintype.card F) ((r : ℝ) / (n : ℝ)) n := by
    rw [hammingBallVolume_eq_ncard_hammingBall ((r : ℝ) / (n : ℝ)) (0 : ι → F), hfloor]
  rw [heq]
  have hent := hammingBallVolume_le_qEntropy (q := Fintype.card F) hq ((r : ℝ) / (n : ℝ))
    (by rw [hfloor]; exact hrn) (by rw [hfloor]; exact hcap)
  rw [hfloor] at hent
  exact_mod_cast hent

theorem filter_ball_card_le_qEntropy {F : Type} [Fintype F] [DecidableEq F] [Zero F]
    (hq : 2 ≤ Fintype.card F) (r : ℕ) (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hcap : (r : ℝ) / (Fintype.card ι : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    ((Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card : ℝ)
      ≤ ((Fintype.card ι : ℝ) + 1)
        * (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
            * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ))) := by
  rw [CodingTheory.filter_card_eq_hammingBall_ncard]
  exact hammingBall_ncard_le_qEntropy hq r hr0 hrn hcap

/-- **Asymptotic Gilbert–Varshamov bound.** There exists a code with minimum distance `≥ d`
(`2 ≤ d ≤ n`, below capacity) of rate `≥ 1 − H_q(δ)`: `q^{n·(1−H_q((d−1)/n))} ≤ (n+1)·|C|`. -/
theorem gv_existence_rate {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]
    (hq : 2 ≤ Fintype.card F) (d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ Fintype.card ι)
    (hcap : ((d - 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    ∃ C : Finset (ι → F), (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c')
      ∧ (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
          * (1 - qEntropy (Fintype.card F) (((d - 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ))))
        ≤ ((Fintype.card ι : ℝ) + 1) * (C.card : ℝ) := by
  obtain ⟨C, hmin, hcard⟩ := gv_existence (ι := ι) (F := F) d (by omega)
  refine ⟨C, hmin, ?_⟩
  set n := Fintype.card ι with hn
  set q := Fintype.card F with hqc
  set H := qEntropy q (((d - 1 : ℕ) : ℝ) / (n : ℝ)) with hH
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqH_pos : (0 : ℝ) < (q : ℝ) ^ ((n : ℝ) * H) := Real.rpow_pos_of_pos hq0 _
  have hVeq : (univ.filter (fun w : ι → F => hammingDist w 0 ≤ d - 1)).card
      = (univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ d - 1)).card := by
    congr 1; ext w; simp only [Finset.mem_filter, hammingDist_comm]
  have hVle := filter_ball_card_le_qEntropy (ι := ι) (F := F) hq (d - 1) (by omega) (by omega) hcap
  have hcardr : ((q ^ n : ℕ) : ℝ)
      ≤ (C.card : ℝ) * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ d - 1)).card := by
    exact_mod_cast hcard
  have hchain : ((q : ℝ) ^ (n : ℝ))
      ≤ ((n : ℝ) + 1) * (C.card : ℝ) * (q : ℝ) ^ ((n : ℝ) * H) := by
    have h1 : ((q : ℝ) ^ (n : ℝ)) = ((q ^ n : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    rw [h1]
    calc ((q ^ n : ℕ) : ℝ)
        ≤ (C.card : ℝ) * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ d - 1)).card := hcardr
      _ = (C.card : ℝ) * (univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ d - 1)).card := by
          rw [hVeq]
      _ ≤ (C.card : ℝ) * (((n : ℝ) + 1) * (q : ℝ) ^ ((n : ℝ) * H)) :=
          mul_le_mul_of_nonneg_left hVle (Nat.cast_nonneg _)
      _ = ((n : ℝ) + 1) * (C.card : ℝ) * (q : ℝ) ^ ((n : ℝ) * H) := by ring
  have hrpow : (q : ℝ) ^ ((n : ℝ) * (1 - H)) * (q : ℝ) ^ ((n : ℝ) * H) = (q : ℝ) ^ (n : ℝ) := by
    rw [← Real.rpow_add hq0]; congr 1; ring
  have : (q : ℝ) ^ ((n : ℝ) * (1 - H)) * (q : ℝ) ^ ((n : ℝ) * H)
      ≤ (((n : ℝ) + 1) * (C.card : ℝ)) * (q : ℝ) ^ ((n : ℝ) * H) := by
    rw [hrpow]; exact hchain
  exact le_of_mul_le_mul_right this hqH_pos

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.gv_existence_rate
