/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SplittingLadder

/-!
# The smooth-domain instantiation of the splitting ladder: hypothesis-free staircase

`SplittingLadder.lean` proves the ladder events from per-`λ` crossing data. This file
**constructs that data group-theoretically** for the genuine smooth domain
`μ_n = ⟨γ⟩` (`orderOf γ = n = 2m`), discharging every structural hypothesis:

* the enumeration `i ↦ γ^i` is injective (`smoothDom_injective`);
* the coset balance: `γ^m = −1` (`gen_pow_m`), so the sign of `γ^i` is `(−1)^i` and the
  two cosets are exactly the even and odd indices, `m` apiece (`evens_card`);
* the scalar family `λ_j = −γ^{ej}` (`j < n/g`, `g = gcd(e,n)`) is injective
  (`lams_injective`), and its crossing sets `{γ^{j + t·n/g} : t < g}` have the right
  size, the right `e`-th powers, and constant sign (`g ∣ m`).

The payoff is the **hypothesis-free staircase theorem** `smooth_ladder_eps_ge`:

  for `μ_n ⊆ F^×` (`n = 2m`, `char F ≠ 2`), the degree-`< k` smooth-domain code with
  `k ≥ e + 1`, `g = gcd(e, n) ∣ m`, and any agreement `k + g ≤ a ≤ m + g`:

      `ε_mca(C, 1 − a/n) ≥ (n/g) / |F|`.

Every rung of the probes' staircase table is the corresponding instance; the optimal
rung (`g` the largest 2-power `≤ k − 1` at 2-power scales) bottoms out at the
unique-decoding radius. Together with the universal bands `b = 1, 2` and the
half-distance staircase law (sibling lane), the lower profile of `ε_mca` on
`[0, 1/2]` is now machine-checked except for the linear bands `3 ≤ b < (d−1)/2`.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (middle-band cartography, round 3); `SplittingLadder.lean`,
  `CosetSplittingFloor.lean`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.SmoothLadderInstance

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.CensusLowerBound
open ProximityGap.SplittingLadder

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

section Smooth

variable (γ : F) {n m : ℕ}

/-- The smooth domain: the cyclic group `⟨γ⟩` in generator order. -/
def smoothDom (n : ℕ) : Fin n → F := fun i => γ ^ (i : ℕ)

/-- Distinct powers below the order are distinct elements. -/
theorem smoothDom_injective (hord : orderOf γ = n) :
    Function.Injective (smoothDom γ n) := by
  intro i j hij
  unfold smoothDom at hij
  have h := pow_injOn_Iio_orderOf (x := γ)
    (by rw [hord]; exact Set.mem_Iio.mpr i.isLt)
    (by rw [hord]; exact Set.mem_Iio.mpr j.isLt) hij
  exact Fin.ext h

/-- The half-order power of a generator of even order `n = 2m` is `−1`. -/
theorem gen_pow_m (hord : orderOf γ = n) (hm : n = 2 * m) (hm1 : 1 ≤ m) :
    γ ^ m = -1 := by
  have hsq : γ ^ m * γ ^ m = 1 := by
    rw [← pow_add]
    have : m + m = n := by omega
    rw [this, ← hord]
    exact pow_orderOf_eq_one γ
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exfalso
    have hdvd : orderOf γ ∣ m := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have := Nat.le_of_dvd hm1 hdvd
    omega
  · exact h1

/-- The sign of the `i`-th domain point is `(−1)^i`. -/
theorem smoothDom_sign (hord : orderOf γ = n) (hm : n = 2 * m) (hm1 : 1 ≤ m)
    (i : Fin n) : smoothDom γ n i ^ m = (-1 : F) ^ (i : ℕ) := by
  unfold smoothDom
  rw [← pow_mul, mul_comm, pow_mul, gen_pow_m γ hord hm hm1]

/-- The even indices of `Fin (2m)` number exactly `m`. -/
theorem evens_card {n m : ℕ} (hm : n = 2 * m) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 0)).card = m := by
  classical
  have hmap : Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 0)
      = Finset.univ.image (fun j : Fin m => (⟨2 * (j : ℕ), by omega⟩ : Fin n)) := by
    apply Finset.Subset.antisymm
    · intro i hi
      rw [Finset.mem_filter] at hi
      have h2 : (i : ℕ) % 2 = 0 := hi.2
      have hj : (i : ℕ) / 2 < m := by omega
      refine Finset.mem_image.mpr ⟨⟨(i : ℕ) / 2, hj⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only []
      omega
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [Nat.mul_mod_right]⟩
  rw [hmap, Finset.card_image_of_injective _ (fun x y hxy => by
    have := Fin.val_eq_of_eq hxy
    simp only [] at this
    exact Fin.ext (by omega)), Finset.card_univ, Fintype.card_fin]

/-- The odd indices of `Fin (2m)` number exactly `m`. -/
theorem odds_card {n m : ℕ} (hm : n = 2 * m) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 1)).card = m := by
  classical
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => (i : ℕ) % 2 = 0)
  have hcompl : Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) % 2 = 0)
      = Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 1) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h; omega
    · intro h; omega
  rw [hcompl] at hsplit
  have := evens_card (n := n) (m := m) hm
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

end Smooth

/-! ## The hypothesis-free staircase -/

open Classical in
/-- **The smooth-domain splitting-ladder staircase, hypothesis-free.** For the smooth
domain `μ_n = ⟨γ⟩` (`n = 2m`, `char F ≠ 2`), the degree-`< k` evaluation code with
`e + 1 ≤ k`, `g = gcd(e, n) ∣ m`, `1 ≤ e`: at every agreement `k + g ≤ a ≤ m + g`,

    `ε_mca(C, 1 − a/n) ≥ (n/g)/|F|`.

The rungs `g = 1, 2, 4, …` are the probes' staircase; the deepest rung sits at the
unique-decoding radius. -/
theorem smooth_ladder_eps_ge (γ : F) {n m k e g : ℕ}
    (hord : orderOf γ = n) (hm : n = 2 * m) (hm1 : 1 ≤ m)
    (he1 : 1 ≤ e) (hek : e + 1 ≤ k) (hg : g = Nat.gcd e n) (hgm : g ∣ m)
    {a : ℕ} (hka : k + g ≤ a) (ham : a ≤ m + g)
    (hchar : (-1 : F) ≠ 1) :
    ((n / g : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          (evalCode (smoothDom γ n) k : Set (Fin n → F))
          (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0)) := by
  have hn1 : 1 ≤ n := by omega
  have hnone : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hg1 : 1 ≤ g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_right e n
  have hge : g ∣ e := hg ▸ Nat.gcd_dvd_left e n
  have hgm' : g ≤ m := Nat.le_of_dvd hm1 hgm
  obtain ⟨e', he'⟩ := hge
  obtain ⟨n', hn'⟩ := hgn
  obtain ⟨m', hm'⟩ := hgm
  have hng' : n / g = n' := by
    rw [hn']
    exact Nat.mul_div_cancel_left n' (by omega)
  have hn'1 : 1 ≤ n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | h1
    · exfalso
      rw [h0, Nat.mul_zero] at hn'
      omega
    · exact h1
  have hng_pos : 1 ≤ n / g := by rw [hng']; exact hn'1
  -- the order of γ^e is n/g
  have hord_e : orderOf (γ ^ e) = n / g := by
    rw [orderOf_pow' γ (by omega : e ≠ 0), hord, hg, Nat.gcd_comm]
  -- the scalar family λ_j = −γ^{e j} = −(γ^e)^j, j < n/g
  set lams : Fin (n / g) → F := fun j => -((γ ^ e) ^ (j : ℕ)) with hlams_def
  have hlams_inj : Function.Injective lams := by
    intro j j' hjj
    rw [hlams_def] at hjj
    simp only [neg_inj] at hjj
    have h := pow_injOn_Iio_orderOf (x := γ ^ e)
      (by rw [hord_e]; exact Set.mem_Iio.mpr j.isLt)
      (by rw [hord_e]; exact Set.mem_Iio.mpr j'.isLt) hjj
    exact Fin.ext h
  -- the crossing index maps
  have hidx_lt : ∀ (j : Fin (n / g)) (t : Fin g), (j : ℕ) + (t : ℕ) * (n / g) < n := by
    intro j t
    have h1 : (j : ℕ) < n / g := j.isLt
    have h2 : (t : ℕ) + 1 ≤ g := t.isLt
    have h3 : ((t : ℕ) + 1) * (n / g) ≤ g * (n / g) :=
      Nat.mul_le_mul_right _ h2
    have h4 : g * (n / g) = n := Nat.mul_div_cancel' ⟨n', hn'⟩
    calc (j : ℕ) + (t : ℕ) * (n / g) < ((t : ℕ) + 1) * (n / g) := by
          have := h1
          nlinarith
      _ ≤ g * (n / g) := h3
      _ = n := h4
  set idx : Fin (n / g) → Fin g → Fin n := fun j t =>
    ⟨(j : ℕ) + (t : ℕ) * (n / g), hidx_lt j t⟩ with hidx_def
  set Xc : Fin (n / g) → Finset (Fin n) := fun j => Finset.univ.image (idx j)
    with hXc_def
  -- apply the data-parameterized ladder
  refine ladder_eps_ge (smoothDom γ n) (smoothDom_injective γ hord) hm hek hg1 hgm'
    hka ham ?_ ?_ hchar lams hlams_inj
    (fun j => (-1 : F) ^ (j : ℕ)) (fun j => by
      rcases Nat.even_or_odd (j : ℕ) with hev | hod
      · left; exact Even.neg_one_pow hev
      · right; exact Odd.neg_one_pow hod)
    Xc ?_ ?_ ?_
  · -- plus-coset count: the even indices
    have hcong : Finset.univ.filter (fun i : Fin n => smoothDom γ n i ^ m = 1)
        = Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 0) := by
      apply Finset.filter_congr
      intro i _
      rw [smoothDom_sign γ hord hm hm1 i]
      constructor
      · intro h
        by_contra hodd
        have hodd' : Odd (i : ℕ) := Nat.odd_iff.mpr (by omega)
        rw [Odd.neg_one_pow hodd'] at h
        exact hchar h
      · intro h
        exact Even.neg_one_pow (Nat.even_iff.mpr h)
    rw [hcong, evens_card hm]
  · -- minus-coset count: the odd indices
    have hcong : Finset.univ.filter (fun i : Fin n => smoothDom γ n i ^ m = -1)
        = Finset.univ.filter (fun i : Fin n => (i : ℕ) % 2 = 1) := by
      apply Finset.filter_congr
      intro i _
      rw [smoothDom_sign γ hord hm hm1 i]
      constructor
      · intro h
        by_contra heven
        have heven' : Even (i : ℕ) := Nat.even_iff.mpr (by omega)
        rw [Even.neg_one_pow heven'] at h
        exact hchar h.symm
      · intro h
        exact Odd.neg_one_pow (Nat.odd_iff.mpr h)
    rw [hcong, odds_card hm]
  · -- crossing-set cardinality
    intro j
    rw [hXc_def]
    have hidx_inj : Function.Injective (idx j) := by
      intro t t' htt
      have hval : (j : ℕ) + (t : ℕ) * (n / g) = (j : ℕ) + (t' : ℕ) * (n / g) := by
        have := Fin.val_eq_of_eq htt
        rw [hidx_def] at this
        exact this
      have hmul : (t : ℕ) * (n / g) = (t' : ℕ) * (n / g) :=
        Nat.add_left_cancel hval
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) hmul)
    rw [Finset.card_image_of_injective _ hidx_inj, Finset.card_univ, Fintype.card_fin]
  · -- crossing values: x^e = −λ_j
    intro j x hx
    rw [hXc_def] at hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    show smoothDom γ n (idx j t) ^ e = -(lams j)
    rw [hlams_def]
    simp only [neg_neg]
    show (γ ^ ((j : ℕ) + (t : ℕ) * (n / g))) ^ e = (γ ^ e) ^ (j : ℕ)
    rw [← pow_mul, ← pow_mul]
    have hkey2 : n / g * e = e' * n := by
      rw [hng', he', hn']
      ring
    have harith : ((j : ℕ) + (t : ℕ) * (n / g)) * e
        = e * (j : ℕ) + ((t : ℕ) * e') * n := by
      calc ((j : ℕ) + (t : ℕ) * (n / g)) * e
          = e * (j : ℕ) + (t : ℕ) * (n / g * e) := by ring
        _ = e * (j : ℕ) + (t : ℕ) * (e' * n) := by rw [hkey2]
        _ = e * (j : ℕ) + ((t : ℕ) * e') * n := by ring
    rw [harith, pow_add,
      show ((t : ℕ) * e') * n = n * ((t : ℕ) * e') from mul_comm _ _,
      pow_mul γ n ((t : ℕ) * e'),
      show γ ^ n = 1 from by rw [← hord]; exact pow_orderOf_eq_one γ,
      one_pow, mul_one, pow_mul]
  · -- crossing signs: constant (−1)^j on each crossing set
    intro j x hx
    rw [hXc_def] at hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    show smoothDom γ n (idx j t) ^ m = (-1 : F) ^ (j : ℕ)
    rw [smoothDom_sign γ hord hm hm1]
    show (-1 : F) ^ ((j : ℕ) + (t : ℕ) * (n / g)) = (-1 : F) ^ (j : ℕ)
    have hng2 : n / g = 2 * m' := by
      rw [hng']
      have hgg : g * n' = g * (2 * m') := by
        rw [← hn', hm, hm']
        ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) hgg
    have harith : (t : ℕ) * (n / g) = ((t : ℕ) * m') * 2 := by
      rw [hng2]
      ring
    have heven : Even (((t : ℕ) * m') * 2) := ⟨(t : ℕ) * m', by ring⟩
    rw [pow_add, harith, Even.neg_one_pow heven, mul_one]

/-! ## Source audit -/

#print axioms smooth_ladder_eps_ge

end ProximityGap.SmoothLadderInstance
