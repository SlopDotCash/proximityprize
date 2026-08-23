/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

/-!
# R341: Mellin-side Parseval — the PAPR bound holds exactly on average

Third brick of the Gauss-phase PAPR arc (_R339 Mellin identity, _R340 autocorrelation).
For the Mellin sum `S_b = ∑_{j ∈ (range t).erase 0} (χ^{dj})⁻¹(b) · τ(χ^{dj}, ψ)`
(the object whose sup over `b ≠ 0` is the open `GaussPhasePAPRBound`):

  `∑_{b ≠ 0} S_b · conj(S_b) = (q−1) · ∑_{j ∈ (range t).erase 0} τ_j · conj(τ_j)`.

Consequence (with `‖τ_j‖² = q`): the mean of `‖S_b‖²` over the `q−1` frequencies is
EXACTLY `(t−1)·q` — the random-phase mean-square — so the PAPR Prop is true on
average, a `log t` factor below the sup target `A²·q·t·log t`. The formally isolated
open content of face 3 is therefore precisely the sup-vs-mean gap (equivalently the
`r ≈ ln q` DC-subtracted moment tower); depth 2 carries no obstruction.

Proof: expand, swap, and apply character orthogonality — the frequency sums
`∑_{b≠0} (χ^{dj})⁻¹(b)·χ^{dk}(b)` vanish off the diagonal (`χ^{d(k−j)}` nontrivial
for `0 < |k−j| < t`) and equal `q−1` on it.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.R341MellinParseval

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A multiplicative character value at a nonzero point is nonzero. -/
theorem mulChar_apply_ne_zero (χ' : MulChar F ℂ) {b : F} (hb : b ≠ 0) :
    χ' b ≠ 0 := by
  intro h0
  have hn := norm_mulChar_apply_unit χ' hb
  rw [h0, norm_zero] at hn
  norm_num at hn

/-- **Frequency orthogonality**: for `j, k < t` (with `t·d = q−1`),
`∑_{b ≠ 0} (χ^{dj})⁻¹(b) · χ^{dk}(b)` is `q−1` if `j = k` and `0` otherwise. -/
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
      rw [MulChar.inv_apply_eq_inv' (χ ^ (d * j)) b,
        inv_mul_cancel₀ (mulChar_apply_ne_zero (χ ^ (d * j)) hbne)]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  · rw [if_neg hjk]
    -- the product character μ = χ^{dk} · (χ^{dj})⁻¹ is nontrivial
    set μ : MulChar F ℂ := (χ ^ (d * k)) * (χ ^ (d * j))⁻¹ with hμ
    have hμapply : ∀ b : F, ((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b = μ b := by
      intro b
      rw [hμ, MulChar.mul_apply]
      ring
    have hμne : μ ≠ 1 := by
      rcases Nat.lt_or_ge j k with hlt | hge
      · -- k > j: μ = χ^{d(k−j)}
        have hsplit : (χ ^ (d * k)) = (χ ^ (d * (k - j))) * (χ ^ (d * j)) := by
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
      · -- j > k (j ≠ k): μ⁻¹ = χ^{d(j−k)} ≠ 1
        have hlt : k < j := by omega
        intro hcontra
        have hinv : μ⁻¹ = (χ ^ (d * (j - k))) := by
          have hsplit : (χ ^ (d * j)) = (χ ^ (d * (j - k))) * (χ ^ (d * k)) := by
            rw [← pow_add]
            congr 1
            have : d * (j - k) + d * k = d * j := by
              rw [← Nat.mul_add, Nat.sub_add_cancel hlt.le]
            rw [this]
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

/-- **Mellin Parseval**: the exact second moment over frequencies of the Mellin sum
`S_b = ∑_{j ∈ (range t).erase 0} (χ^{dj})⁻¹(b) · τ(χ^{dj}, ψ)`:

  `∑_{b ≠ 0} S_b · conj(S_b) = (q−1) · ∑_{j ∈ (range t).erase 0} τ_j · conj(τ_j)`.

With `‖τ_j‖² = q` this pins the mean of `‖S_b‖²` at exactly `(t−1)·q` — the
random-phase mean square. The open PAPR content is exactly the sup-vs-mean gap. -/
theorem mellin_parseval {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    (ψ : AddChar F ℂ) :
    ∑ b ∈ Finset.univ.erase (0 : F),
        (∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
            ((χ ^ (d * j))⁻¹) b * gaussSum (χ ^ (d * j)) ψ)
          * (starRingEnd ℂ)
            (∑ k ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
              ((χ ^ (d * k))⁻¹) b * gaussSum (χ ^ (d * k)) ψ)
      = ((Fintype.card F - 1 : ℕ) : ℂ)
          * ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
              gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * j)) ψ) := by
  classical
  set t := (Fintype.card F - 1) / d with ht
  set J : Finset ℕ := (Finset.range t).erase 0 with hJ
  -- expand conj and the product of sums
  have hexpand : ∀ b : F, b ≠ 0 →
      (∑ j ∈ J, ((χ ^ (d * j))⁻¹) b * gaussSum (χ ^ (d * j)) ψ)
        * (starRingEnd ℂ) (∑ k ∈ J, ((χ ^ (d * k))⁻¹) b * gaussSum (χ ^ (d * k)) ψ)
      = ∑ j ∈ J, ∑ k ∈ J,
          (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
            * (gaussSum (χ ^ (d * j)) ψ
                * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ)) := by
    intro b hb
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    -- conj((χ^{dk})⁻¹ b) = χ^{dk} b
    have hconj : (starRingEnd ℂ) (((χ ^ (d * k))⁻¹) b) = (χ ^ (d * k)) b := by
      rw [conj_mulChar_apply, inv_inv]
    rw [hconj]
    ring
  rw [Finset.sum_congr rfl fun b hb => hexpand b (Finset.ne_of_mem_erase hb)]
  -- swap the b-sum inside the (j, k)-sums
  rw [Finset.sum_comm]
  have hswap2 : ∀ j : ℕ, ∑ b ∈ Finset.univ.erase (0 : F), ∑ k ∈ J,
      (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
        * (gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ))
      = ∑ k ∈ J, ∑ b ∈ Finset.univ.erase (0 : F),
      (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
        * (gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ)) :=
    fun j => Finset.sum_comm
  rw [Finset.sum_congr rfl fun j _ => hswap2 j]
  -- factor the b-independent Gauss-sum product out of the b-sum, apply orthogonality
  have hinner : ∀ j ∈ J, ∀ k ∈ J,
      ∑ b ∈ Finset.univ.erase (0 : F),
        (((χ ^ (d * j))⁻¹) b * (χ ^ (d * k)) b)
          * (gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ))
      = (if j = k then ((Fintype.card F - 1 : ℕ) : ℂ) else 0)
          * (gaussSum (χ ^ (d * j)) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (d * k)) ψ)) := by
    intro j hj k hk
    rw [← Finset.sum_mul]
    congr 1
    exact freq_orthogonality hd hd0 hord
      (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
      (Finset.mem_range.mp (Finset.mem_of_mem_erase hk))
  rw [Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun k hk => hinner j hj k hk]
  -- collapse the k-sum to the diagonal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_eq_single_of_mem j hj (fun k _ hkj => by
    rw [if_neg (fun h => hkj h.symm), zero_mul])]
  rw [if_pos rfl]

#print axioms mulChar_apply_ne_zero
#print axioms freq_orthogonality
#print axioms mellin_parseval

end ArkLib.ProximityGap.R341MellinParseval
