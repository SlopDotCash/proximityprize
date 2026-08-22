/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B2_char0_logconcave

/-!
# Char-0 W3-anti BASE: discharging the `r = 1` instance of `SharpNewtonBessel` (#444)

Lane B2 (`_wf8B2_char0_logconcave.lean`) reduced the **characteristic-zero** half of the
step-ratio monotonicity inequality [W3-anti] *exactly* — axiom-clean — to a single named input,
the **sharp Newton inequality** on the Bessel power coefficients `c_r = besselCoeff d r`:

  `SharpNewtonBessel d  :  ∀ r ≥ 1,  (r+1)·c_{r-1}·c_{r+1} ≤ r·c_r²`.

B2 proves `c_0 = 1`, `c_1 = d`, the exact reduction `R_antitone_iff_sharpNewton`, and the telescope
consumer `char0_W3anti_of_sharpNewton`, but leaves `SharpNewtonBessel d` itself as a **named (open)
input** — argued classically via the Laguerre–Pólya type-I second-quotient theorem, **not formalised
at any instance**.

This file lands the **FIRST discharge of an instance**: the `r = 1` base case, which is
`2·c_0·c_2 ≤ c_1²`, i.e. `2·besselCoeff d 2 ≤ d²`.

We supply the missing closed form `besselCoeff_two : besselCoeff d 2 = d·(2d − 1)/4` by partitioning
`antidiagonalTuple d 2` (via the filter "has a coordinate `= 2`") into the `d` "double" tuples
(one coord `= 2`, term `1/(2!)² = 1/4`) and the `C(d,2)` "split" tuples (two coords `= 1`, term `1`):
`c_2 = d·(1/4) + C(d,2)·1 = d(2d−1)/4`. The base inequality is then
`2·d(2d−1)/4 ≤ d²` ⟺ `2d² − d ≤ 2d²` (slack `d/2 > 0`).

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `besselCoeff_two` — `besselCoeff d 2 = d·(2d−1)/4`.
* `sharpNewton_base` — `2 · besselCoeff d 2 ≤ (besselCoeff d 1)²` (the `r = 1` `SharpNewtonBessel`
  instance, exact positive slack `d/2`).
* `Rstep_one_le_Rstep_zero` — `Rstep d 1 ≤ Rstep d 0` (first-step descent off the Wick value).

## Honesty / scope

Discharges **one instance** (`r = 1`) of the named open input `SharpNewtonBessel`, char-0 only. Does
NOT close `SharpNewtonBessel d` in general, does NOT touch the char-`p` transfer (lane B3, proven NOT
char-`p`-robust), raises NOTHING on the open CORE ceiling. Turns the B2 telescope's first rung from a
named input into a proven char-0 fact, pinning the exact base slack `d/2`.
-/

open Finset BigOperators

set_option linter.style.longLine false

namespace ProximityGap.PrizeWorkbench

variable {d : ℕ}

/-- The `besselCoeff` summand at tuple `m`. -/
private def bterm (m : Fin d → ℕ) : ℚ := ∏ i, (1 : ℚ) / (Nat.factorial (m i))^2

/-- Each coordinate of a tuple summing to `2` is `≤ 2`. -/
private lemma coord_le_two {m : Fin d → ℕ} (hm : ∑ i, m i = 2) (i : Fin d) : m i ≤ 2 := by
  calc m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = 2 := hm

/-- On a "double" tuple `m` (some coord `= 2`, the others forced `0` since the sum is `2`), the
summand is `1/4`. -/
private lemma bterm_of_double {m : Fin d → ℕ} (hm : ∑ i, m i = 2) {i : Fin d} (hi : m i = 2) :
    bterm m = 1 / 4 := by
  -- every j ≠ i has m j = 0
  have hzero : ∀ j, j ≠ i → m j = 0 := by
    intro j hj
    by_contra hjne
    have h1 : 1 ≤ m j := Nat.one_le_iff_ne_zero.mpr hjne
    have hpair : m i + m j ≤ ∑ k, m k := by
      have hsub : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
      calc m i + m j = ∑ k ∈ ({i, j} : Finset (Fin d)), m k := by
            rw [Finset.sum_pair (Ne.symm hj)]
        _ ≤ ∑ k, m k := Finset.sum_le_sum_of_subset hsub
    rw [hm, hi] at hpair; omega
  unfold bterm
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have herase : ∀ j ∈ Finset.univ.erase i, (1 : ℚ) / (Nat.factorial (m j))^2 = 1 := by
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [hzero j hj.1]; norm_num
  rw [Finset.prod_congr rfl herase, Finset.prod_const_one, one_mul, hi]
  norm_num

/-- On a "split" tuple `m` (two coords `= 1`, rest `0`), the summand is `1`. -/
private lemma bterm_of_split {m : Fin d → ℕ}
    (hall : ∀ k, m k ≤ 1) : bterm m = 1 := by
  unfold bterm
  apply Finset.prod_eq_one
  intro j _
  have : m j = 0 ∨ m j = 1 := by have := hall j; omega
  rcases this with h | h <;> rw [h] <;> norm_num

/-- The membership filter "has a coordinate equal to `2`" classifies the antidiagonal: a tuple
summing to `2` either has some coordinate `= 2` (double) or all coordinates `≤ 1` (split). -/
private lemma split_iff_not_double {m : Fin d → ℕ} (hm : ∑ i, m i = 2) :
    (¬ ∃ i, m i = 2) ↔ ∀ k, m k ≤ 1 := by
  constructor
  · intro h k
    have hk2 := coord_le_two hm k
    rcases Nat.lt_or_ge (m k) 2 with hlt | hge
    · omega
    · exact absurd ⟨k, le_antisymm hk2 hge⟩ h
  · intro h ⟨i, hi⟩
    have := h i; omega

/-- **The double subfamily** of `antidiagonalTuple d 2`: tuples with some coordinate `= 2`.
Its members are exactly `Pi.single i 2`, in bijection with `Fin d`. -/
private lemma sum_double :
    ∑ m ∈ (Finset.Nat.antidiagonalTuple d 2).filter (fun m => ∃ i, m i = 2), bterm m
      = (d : ℚ) * (1 / 4) := by
  classical
  -- the filtered set is the image of `Fin d` under `i ↦ Pi.single i 2`
  have himg : (Finset.Nat.antidiagonalTuple d 2).filter (fun m => ∃ i, m i = 2)
      = Finset.univ.image (fun i : Fin d => (Pi.single i 2 : Fin d → ℕ)) := by
    ext m
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hm, i, hi⟩
      refine ⟨i, ?_⟩
      -- m = Pi.single i 2 : every j ≠ i has m j = 0
      have hzero : ∀ j, j ≠ i → m j = 0 := by
        intro j hj
        by_contra hjne
        have h1 : 1 ≤ m j := Nat.one_le_iff_ne_zero.mpr hjne
        have hpair : m i + m j ≤ ∑ k, m k := by
          have hsub : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
          calc m i + m j = ∑ k ∈ ({i, j} : Finset (Fin d)), m k := by
                rw [Finset.sum_pair (Ne.symm hj)]
            _ ≤ ∑ k, m k := Finset.sum_le_sum_of_subset hsub
        rw [hm, hi] at hpair; omega
      funext j
      by_cases hji : j = i
      · subst hji; rw [hi, Pi.single_eq_same]
      · rw [hzero j hji, Pi.single_eq_of_ne hji]
    · rintro ⟨i, rfl⟩
      refine ⟨?_, i, Pi.single_eq_same i 2⟩
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; rw [Pi.single_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ i) h
  rw [himg]
  rw [Finset.sum_image (by
    intro i _ j _ hij
    by_contra hne
    have h := congrFun hij i
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h
    exact absurd h (by decide))]
  -- each term is 1/4
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      bterm (Pi.single i 2 : Fin d → ℕ) = 1 / 4 := by
    intro i _
    refine bterm_of_double ?_ (Pi.single_eq_same i 2)
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- **The split subfamily** of `antidiagonalTuple d 2`: tuples with all coords `≤ 1` (equivalently
no coord `= 2`). Each summand is `1`, so the sum is the cardinality, which equals `C(d,2)`. The
support map `m ↦ {k | m k = 1}` is a bijection onto the `2`-element subsets of `Fin d`. -/
private lemma sum_split :
    ∑ m ∈ (Finset.Nat.antidiagonalTuple d 2).filter (fun m => ¬ ∃ i, m i = 2), bterm m
      = ((d.choose 2 : ℕ) : ℚ) := by
  classical
  -- every summand is 1
  have hterm : ∀ m ∈ (Finset.Nat.antidiagonalTuple d 2).filter (fun m => ¬ ∃ i, m i = 2),
      bterm m = 1 := by
    intro m hm
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hm
    exact bterm_of_split ((split_iff_not_double hm.1).mp hm.2)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the cardinality equals C(d,2) via the support bijection to 2-element subsets
  congr 1
  -- card (filtered antidiagonal) = card (powersetCard 2 univ) = C(d,2)
  have hcard : ((Finset.Nat.antidiagonalTuple d 2).filter (fun m => ¬ ∃ i, m i = 2)).card
      = ((Finset.univ : Finset (Fin d)).powersetCard 2).card := by
    apply Finset.card_bij (fun m _ => Finset.univ.filter (fun k => m k = 1))
    · -- maps into powersetCard 2 univ
      intro m hm
      rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hm
      have hall := (split_iff_not_double hm.1).mp hm.2
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      -- the support has card 2 since the (0/1)-tuple sums to 2
      have hsum : ∑ k, m k = 2 := hm.1
      have : (Finset.univ.filter (fun k => m k = 1)).card
          = ∑ k, m k := by
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro k _
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hall k) with h0 | h1
        · simp [h0]
        · simp [h1]
      rw [this, hsum]
    · -- injective
      intro m hm n hn hmn
      rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hm hn
      have hallm := (split_iff_not_double hm.1).mp hm.2
      have halln := (split_iff_not_double hn.1).mp hn.2
      funext k
      have hk : (k ∈ Finset.univ.filter (fun k => m k = 1))
          ↔ (k ∈ Finset.univ.filter (fun k => n k = 1)) := by rw [hmn]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hallm k) with h0 | h1
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (halln k) with h0' | h1'
        · rw [h0, h0']
        · exact absurd (hk.mpr h1') (by rw [h0]; decide)
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (halln k) with h0' | h1'
        · exact absurd (hk.mp h1) (by rw [h0']; decide)
        · rw [h1, h1']
    · -- surjective
      intro s hs
      rw [Finset.mem_powersetCard] at hs
      refine ⟨fun k => if k ∈ s then 1 else 0, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
        refine ⟨?_, ?_⟩
        · -- sum = 2 = card s
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
            mul_one, hs.2]
        · -- no coord = 2
          rintro ⟨i, hi⟩
          by_cases hmem : i ∈ s <;> simp [hmem] at hi
      · -- support of the indicator is s
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hmem : k ∈ s <;> simp [hmem]
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **The closed form** `besselCoeff d 2 = d·(2d − 1)/4`.  The antidiagonal `antidiagonalTuple d 2`
splits (by the filter "has a coordinate `= 2`") into the `d` double tuples (term `1/4`) and the
`C(d,2)` split tuples (term `1`), giving `c_2 = d/4 + C(d,2) = (d + 2·C(d,2))/4 = (2d² − d)/4`. -/
theorem besselCoeff_two (d : ℕ) : besselCoeff d 2 = (d : ℚ) * (2 * d - 1) / 4 := by
  classical
  -- besselCoeff d 2 is the sum of `bterm` over the antidiagonal
  have hsum : besselCoeff d 2
      = ∑ m ∈ Finset.Nat.antidiagonalTuple d 2, bterm m := by
    rfl
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not
      (Finset.Nat.antidiagonalTuple d 2) (fun m => ∃ i, m i = 2) bterm,
    sum_double, sum_split]
  -- d/4 + C(d,2) = d(2d-1)/4; use 2·C(d,2) = d(d-1)
  have hchoose : ((d.choose 2 : ℕ) : ℚ) = (d : ℚ) * ((d : ℚ) - 1) / 2 :=
    Nat.cast_choose_two (K := ℚ) d
  rw [hchoose]
  rcases d with _ | d'
  · simp
  · push_cast; ring

/-- **The `r = 1` base case of `SharpNewtonBessel`**: `2·c_0·c_2 ≤ c_1²`, i.e.
`2·besselCoeff d 2 ≤ (besselCoeff d 1)²` (with `c_0 = 1`, `c_1 = d`). Exact positive slack `d/2`:
`(besselCoeff d 1)² − 2·besselCoeff d 2 = d² − (2d²−d)/2 = d/2 > 0` for `d ≥ 1`. -/
theorem sharpNewton_base (d : ℕ) :
    2 * besselCoeff d 2 ≤ (besselCoeff d 1) ^ 2 := by
  rw [besselCoeff_two, besselCoeff_one]
  rcases d with _ | d'
  · simp
  · push_cast
    have hx : (0 : ℚ) ≤ (d' : ℚ) := Nat.cast_nonneg d'
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by norm_num : (0:ℚ) < 4)]
    nlinarith [hx]

/-- **First-step descent (char-0 W3-anti at the base).** The step ratio descends off the Wick
value at the first step: `Rstep d 1 ≤ Rstep d 0`. Obtained by feeding `sharpNewton_base`
(rewritten via `c_0 = 1`, `c_1 = d`) through B2's exact reduction `R_antitone_iff_sharpNewton`
at `r = 0`. -/
theorem Rstep_one_le_Rstep_zero {d : ℕ} (hd : 1 ≤ d) : Rstep d 1 ≤ Rstep d 0 := by
  rw [R_antitone_iff_sharpNewton hd 0]
  -- goal: (0+2)·c_2·c_0 ≤ (0+1)·c_1²  i.e. 2·c_2·1 ≤ c_1²
  have h := sharpNewton_base d
  have h0 : besselCoeff d 0 = 1 := besselCoeff_zero d
  change ((0 + 2 : ℕ) : ℚ) * besselCoeff d (0 + 2) * besselCoeff d 0
      ≤ ((0 + 1 : ℕ) : ℚ) * besselCoeff d (0 + 1) ^ 2
  rw [h0]
  norm_num
  nlinarith [h]

end ProximityGap.PrizeWorkbench

/-! ## Axiom audit -/
#print axioms ProximityGap.PrizeWorkbench.besselCoeff_two
#print axioms ProximityGap.PrizeWorkbench.sharpNewton_base
#print axioms ProximityGap.PrizeWorkbench.Rstep_one_le_Rstep_zero
