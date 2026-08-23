/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

/-!
# R342: Mellin level-set (Markov) — PAPR can fail on few frequencies only

Fourth brick of the Gauss-phase PAPR arc (_R339 Mellin identity, _R340
autocorrelation, _R341 Parseval). From the exact frequency Parseval identity we
extract the real form and the Markov/level-set consequence:

* `mellin_parseval_norm` — `∑_{b≠0} ‖S_b‖² = (q−1)·∑_j ‖τ_j‖²` (real form; the
  complex form is re-proved here self-contained so this lane stays fast-path
  iterable without a frontier-to-frontier olean).
* `papr_levelSet` — for every threshold `T > 0`, the number of frequencies with
  `‖S_b‖² ≥ T` is at most `(q−1)·∑_j ‖τ_j‖² / T`. At the PAPR target
  `T = A²·q·t·log t` (with `∑_j ‖τ_j‖² = (t−1)q`) this says the open
  `GaussPhasePAPRBound` can fail on at most `≈ q/(A²·log t)` of the `q−1`
  frequencies — a vanishing fraction. The open core is thus formally confined to
  an `o(1)`-density exceptional frequency set.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.R342MellinLevelSet

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Mellin sum at frequency `b` (the object of `GaussPhasePAPRBound`). -/
noncomputable def mellinSum (d : ℕ) (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (b : F) : ℂ :=
  ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
    ((χ ^ (d * j))⁻¹) b * gaussSum (χ ^ (d * j)) ψ

/-- Frequency orthogonality (self-contained copy of
`R341MellinParseval.freq_orthogonality`, kept local for fast-path iteration). -/
theorem freq_orthogonality {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {j k : ℕ} (hj : j < (Fintype.card F - 1) / d) (hk : k < (Fintype.card F - 1) / d) :
    ∑ b ∈ Finset.univ.erase (0 : F), ((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b
      = if j = k then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
  classical
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    have hone : ∀ b ∈ Finset.univ.erase (0 : F),
        ((χ ^ (d * j))⁻¹) b * (χ ^ (d * j)) b = 1 := by
      intro b hb
      have hbne : b ≠ 0 := Finset.ne_of_mem_erase hb
      have hne : (χ ^ (d * j)) b ≠ 0 := by
        intro h0
        have hn := norm_mulChar_apply_unit (χ ^ (d * j)) hbne
        rw [h0, norm_zero] at hn
        norm_num at hn
      rw [MulChar.inv_apply_eq_inv' (χ ^ (d * j)) b, inv_mul_cancel₀ hne]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  · rw [if_neg hjk]
    set μ : MulChar F ℂ := (χ ^ (d * k)) * (χ ^ (d * j))⁻¹ with hμ
    have hμapply : ∀ b : F, ((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b = μ b := by
      intro b
      rw [hμ, MulChar.mul_apply]
      ring
    have hμne : μ ≠ 1 := by
      rcases Nat.lt_or_ge j k with hlt | hge
      · have hsplit : (χ ^ (d * k)) = (χ ^ (d * (k - j))) * (χ ^ (d * j)) := by
          rw [← pow_add]
          congr 1
          have : d * (k - j) + d * j = d * k := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hlt.le]
          rw [this]
        rw [hμ, hsplit, mul_inv_cancel_right]
        refine chi_pow_ne_one hord (Nat.mul_pos hd0 (by omega)) ?_
        calc d * (k - j) ≤ d * k := Nat.mul_le_mul_left d (Nat.sub_le k j)
          _ < d * t := (Nat.mul_lt_mul_left hd0).mpr hk
          _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
      · have hlt : k < j := by omega
        intro hcontra
        have hsplit : (χ ^ (d * j)) = (χ ^ (d * (j - k))) * (χ ^ (d * k)) := by
          rw [← pow_add]
          congr 1
          have : d * (j - k) + d * k = d * j := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hlt.le]
          rw [this]
        have hinv : μ⁻¹ = (χ ^ (d * (j - k))) := by
          rw [hμ, hsplit]
          group
        have hne : (χ ^ (d * (j - k))) ≠ 1 := by
          refine chi_pow_ne_one hord (Nat.mul_pos hd0 (by omega)) ?_
          calc d * (j - k) ≤ d * j := Nat.mul_le_mul_left d (Nat.sub_le j k)
            _ < d * t := (Nat.mul_lt_mul_left hd0).mpr hj
            _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
        rw [hcontra, inv_one] at hinv
        exact hne hinv.symm
    have hzero : ∑ b : F, μ b = 0 := MulChar.sum_eq_zero_of_ne_one hμne
    have hsplit0 : ∑ b : F, μ b
        = μ 0 + ∑ b ∈ Finset.univ.erase (0 : F), μ b := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
    rw [Finset.sum_congr rfl fun b _ => hμapply b]
    have hμ0 : μ 0 = 0 := MulChar.map_nonunit μ (by simp)
    rw [hsplit0, hμ0, zero_add] at hzero
    exact hzero

/-- **Real Parseval**: `∑_{b≠0} ‖S_b‖² = (q−1)·∑_j ‖τ_j‖²`. -/
theorem mellin_parseval_norm {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖mellinSum d χ ψ b‖ ^ 2
      = ((Fintype.card F - 1 : ℕ) : ℝ)
          * ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
              ‖gaussSum (χ ^ (d * j)) ψ‖ ^ 2 := by
  classical
  set J : Finset ℕ := (Finset.range ((Fintype.card F - 1) / d)).erase 0 with hJ
  -- complex Parseval, proved via expansion + orthogonality
  have hcomplex : ∑ b ∈ Finset.univ.erase (0 : F),
      mellinSum d χ ψ b * (starRingEnd ℂ) (mellinSum d χ ψ b)
      = ((Fintype.card F - 1 : ℕ) : ℂ)
          * ∑ j ∈ J, gaussSum (χ ^ (d * j)) ψ
              * (starRingEnd ℂ) (gaussSum (χ ^ (d * j)) ψ) := by
    have hexpand : ∀ b : F, b ≠ 0 →
        mellinSum d χ ψ b * (starRingEnd ℂ) (mellinSum d χ ψ b)
        = ∑ j ∈ J, ∑ k ∈ J,
            (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
              * (gaussSum (χ ^ (d * j)) ψ
                  * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ)) := by
      intro b hb
      unfold mellinSum
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      have hconj : (starRingEnd ℂ) (((χ ^ (d * k))⁻¹) b) = (χ ^ (d * k)) b := by
        rw [conj_mulChar_apply, inv_inv]
      rw [hconj]
      ring
    rw [Finset.sum_congr rfl fun b hb => hexpand b (Finset.ne_of_mem_erase hb)]
    rw [Finset.sum_comm]
    have hswap2 : ∀ j : ℕ, ∑ b ∈ Finset.univ.erase (0 : F), ∑ k ∈ J,
        (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
          * (gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ))
        = ∑ k ∈ J, ∑ b ∈ Finset.univ.erase (0 : F),
        (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
          * (gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ)) :=
      fun j => Finset.sum_comm
    rw [Finset.sum_congr rfl fun j _ => hswap2 j]
    have hinner : ∀ j ∈ J, ∀ k ∈ J,
        ∑ b ∈ Finset.univ.erase (0 : F),
          (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
            * (gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ))
        = (if j = k then ((Fintype.card F - 1 : ℕ) : ℂ) else 0)
            * (gaussSum (χ ^ (d * j)) ψ
                * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ)) := by
      intro j hj k hk
      rw [← Finset.sum_mul]
      congr 1
      exact freq_orthogonality hd hd0 hord
        (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
        (Finset.mem_range.mp (Finset.mem_of_mem_erase hk))
    rw [Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun k hk => hinner j hj k hk]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_eq_single_of_mem j hj (fun k _ hkj => by
      rw [if_neg (fun h => hkj h.symm), zero_mul])]
    rw [if_pos rfl]
  -- take real parts via z·conj z = ↑(‖z‖²)
  have hlift : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hlhs : ∑ b ∈ Finset.univ.erase (0 : F),
      mellinSum d χ ψ b * (starRingEnd ℂ) (mellinSum d χ ψ b)
      = ((∑ b ∈ Finset.univ.erase (0 : F), ‖mellinSum d χ ψ b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun b _ => hlift (mellinSum d χ ψ b)]
    push_cast
    rfl
  have hrhs : ((Fintype.card F - 1 : ℕ) : ℂ)
      * ∑ j ∈ J, gaussSum (χ ^ (d * j)) ψ
          * (starRingEnd ℂ) (gaussSum (χ ^ (d * j)) ψ)
      = ((((Fintype.card F - 1 : ℕ) : ℝ)
          * ∑ j ∈ J, ‖gaussSum (χ ^ (d * j)) ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun j _ => hlift (gaussSum (χ ^ (d * j)) ψ)]
    push_cast
    rfl
  have := hcomplex
  rw [hlhs, hrhs] at this
  exact_mod_cast this

/-- **The level-set (Markov) bound**: for every threshold `T > 0`, the number of
frequencies `b ≠ 0` with `‖S_b‖² ≥ T` is at most `(q−1)·∑_j ‖τ_j‖² / T`. At the
PAPR target `T = A²·q·t·log t` this confines any failure of the open
`GaussPhasePAPRBound` to an `o(1)`-density set of frequencies. -/
theorem papr_levelSet {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) {T : ℝ} (hT : 0 < T) :
    ((Finset.univ.erase (0 : F)).filter
        (fun b => T ≤ ‖mellinSum d χ ψ b‖ ^ 2)).card
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
              ‖gaussSum (χ ^ (d * j)) ψ‖ ^ 2) / T := by
  classical
  set S : Finset F := (Finset.univ.erase (0 : F)).filter
    (fun b => T ≤ ‖mellinSum d χ ψ b‖ ^ 2) with hS
  have hcount : (S.card : ℝ) * T ≤ ∑ b ∈ Finset.univ.erase (0 : F),
      ‖mellinSum d χ ψ b‖ ^ 2 := by
    calc (S.card : ℝ) * T = ∑ _b ∈ S, T := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ S, ‖mellinSum d χ ψ b‖ ^ 2 :=
          Finset.sum_le_sum fun b hb => (Finset.mem_filter.mp hb).2
      _ ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖mellinSum d χ ψ b‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun b _ _ => by positivity)
  rw [le_div_iff₀ hT]
  calc (S.card : ℝ) * T
      ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖mellinSum d χ ψ b‖ ^ 2 := hcount
    _ = _ := mellin_parseval_norm hd hd0 hord ψ

#print axioms freq_orthogonality
#print axioms mellin_parseval_norm
#print axioms papr_levelSet

end ArkLib.ProximityGap.R342MellinLevelSet
