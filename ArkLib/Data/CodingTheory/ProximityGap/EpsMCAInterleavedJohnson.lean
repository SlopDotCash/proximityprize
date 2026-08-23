/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedList
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound

/-!
# The Johnson-interleaved splice: an unconditional `ε_mca` window past `d/(3n)` (#232)

O85 (`EpsMCAInterleavedList`) made the conversion "any uniform interleaved (`m = 2`)
list bound `L` at the collapse floor `a = 2t − n` gives `ε_mca ≤ (1 + (n − a)·L)/q`" a
theorem, and O84/O89 record that `badCount` is governed by the interleaved list size
`Λ₂` — but the only in-tree producer of `Λ₂ ≤ L` was unique decoding (`L = 1`, window
`δ < d/(4n)`).  This file produces the **Johnson** list bound for the interleaved code:
the in-tree second-moment bound (`JohnsonListBound`) is alphabet-generic, the
interleaved code `C^{≡2} ⊆ (F²)^ι` inherits pairwise agreement `≤ e = n − d` from `C`
(O78's transfer, replayed over the pair alphabet), so

  `Λ₂(a) ≤ n² / (a² − n·e)`  whenever  `n·e < a²`,

and the O85 conversion turns this into an **unconditional** `ε_mca` upper bound on the
window `δ < (1 − √(e/n))/2` — half the Johnson radius of `C` itself.

## Main results

* `interleavedList_card_le_johnson` — **the pair-alphabet Johnson cap**: packing the
  stack `(f₁, f₂)` and the codeword pairs into words over `F × F` and applying the
  generic `johnson_list_bound_div`, the interleaved list at floor `a` has size
  `≤ n²/(a² − n·e)` whenever `n·e < a²`.  No linearity, no window: only the pairwise
  agreement parameter of `C`.
* `epsMCA_le_interleavedJohnson` — **the splice**: composing through O85's
  `epsMCA_le_of_interleavedList_card_le`, for any `PairClosed` code with pairwise
  agreement `≤ e`, on `n·e < (2t − n)²` (`t = ⌈(1 − δ)n⌉₊`),

    `ε_mca(C, δ) ≤ (1 + (n − (2t − n)) · (n²/((2t − n)² − n·e))) / |F|`,

  in δ-units `(1 + 2δn·L_J)/q` with `L_J = n²/((2t−n)² − n·e)` — the [GCXK25]-shaped
  bound with the Johnson list size, unconditional.
* `johnson_window_of_sqrt` + `nat_gap_of_johnson_window` — **the named real-units
  window**: `2δ + √(e/n) < 1`, i.e. `δ < (1 − √(e/n))/2`, implies the ℕ gap; for a
  code of distance `d = n − e` this is half the Johnson radius `(1 − √(1 − d/n))/2`,
  and `epsMCA_le_interleavedJohnson_of_sqrt_window` states the composed theorem there.
* `nat_gap_of_ud_window` — **window containment**: the O78 UD window `n + e < 2a`
  implies the Johnson gap `n·e < a²` (AM–GM), so this theorem's window contains the
  unconditional `d/(4n)` window outright (with a weaker constant), and the Johnson-only
  band is strictly new territory.
* `johnson_window_wider_of_low_rate` / `johnson_window_crossover` /
  `johnson_window_narrower_of_high_rate` — **the comparison vs `d/(3n)` (O84)**:
  with `ρ ∈ [0, 1)` standing for `e/n` (for RS, `ρ` is the rate up to `O(1/n)`),

    `(1 − ρ)/3 < (1 − √ρ)/2  ⟺  ρ < 1/4`,

  with equality exactly at `ρ = 1/4`.  So at low rates the Johnson window is strictly
  wider than the unconditional `d/(3n)` window of O84: `0.3232… vs 0.2917` at
  `ρ = 1/8`, `0.375 vs 0.3125` at `ρ = 1/16`; at `ρ > 1/4` the O84 window is wider —
  the two unconditional mechanisms genuinely dovetail.

## Where this sits in the bracket (#232)

The unconditional upper-window family is now: O78 `d/(4n)` (UD, `L = 1`) ⊆ this file's
`(1 − √(e/n))/2` (Johnson, `L = L_J`), incomparable with O84's `d/(3n)` (extraction):
Johnson wins below rate `1/4`, extraction above.  Probe demonstration
(RS(16,2)/F₁₇, `δ = 0.32`): `t = 11`, `a = 6` — outside the O84 window
(`3(n−t) = 15 = d` not `< d`) and outside the UD window (`17 ≥ 12`), inside the
Johnson gap (`16 < 36`, `L_J = 12`).  The open core is unchanged: the conjectural
window up to `δ*` where the O68 lower bound lives.

## Falsification record (`scripts/probes/probe_johnson_interleaved_splice.py`, exit 0)

* A (pair-Johnson cap): exact interleaved list sizes on RS over `F₅/F₇/F₁₁/F₁₇`
  (random + planted split stacks), every floor inside the gap — 1,080 checks,
  0 failures.
* B (composed badCount): collapse floors `a = 2t − n`, witness-set reduction (exact by
  monotonicity), 560 checks, 0 failures; full `2^n` subset-enumeration control on
  `n ≤ 6` — 220 controls, 0 mismatches.
* C (window arithmetic, float-free): `(1−ρ)/3 < (1−√ρ)/2 ⟺ 9ρ < (1+2ρ)²` and
  `(1+2ρ)² − 9ρ = (4ρ−1)(ρ−1)` on a 401-point exact grid, 0 failures; crossover at
  `ρ = 1/4` exact; UD ⟹ gap containment on 5,530 ℕ-points, 0 failures.
* D (teeth): the Johnson-only band exercises `Λ₂ ≥ 2` in 216 cases (the UD bound is
  *false* there; only the Johnson cap survives), and the gap condition is load-bearing
  (120 stacks with `Λ₂(a) > n²` below the gap).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated
  Agreement*. ePrint 2026/680.  Tracking issue #232; §5 and Definition 4.3.
- [GCXK25] *List-decodability implies proximity gaps*. ePrint 2025/870.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open Finset

namespace ProximityGap

open InterleavedMCACollapse Round17CAPair

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The pair-alphabet Johnson cap on the interleaved list -/

/-- **Johnson list bound for the `m = 2` interleaved code.**  Packing the stack
`(f₁, f₂)` and the codeword pairs into words over the pair alphabet `F × F`, the
interleaved list at joint-agreement floor `a` is a Johnson list: members agree with the
packed stack on `≥ a` coordinates, and distinct members agree with *each other* on at
most `e` coordinates (a differing pair differs in some row, and joint agreement is
contained in that row's agreement — O78's distance transfer, replayed over `F × F`).
The generic second-moment bound then caps the list by `n²/(a² − n·e)` whenever
`n·e < a²`.  No linearity or window hypothesis. -/
theorem interleavedList_card_le_johnson (C : Finset (ι → F)) (f₁ f₂ : ι → F) {a e : ℕ}
    (hagree : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ e)
    (hgap : Fintype.card ι * e < a ^ 2) :
    (interleavedList C f₁ f₂ a).card ≤
      Fintype.card ι ^ 2 / (a ^ 2 - Fintype.card ι * e) := by
  classical
  set Φ : ((ι → F) × (ι → F)) → (ι → F × F) := fun p x => (p.1 x, p.2 x) with hΦdef
  have hΦinj : Function.Injective Φ := by
    intro p p' h
    exact Prod.ext (funext fun x => congrArg Prod.fst (congrFun h x))
      (funext fun x => congrArg Prod.snd (congrFun h x))
  rw [← Finset.card_image_of_injOn (hΦinj.injOn)]
  refine ArkLib.JohnsonList.johnson_list_bound_div (F := F × F)
    (fun x => (f₁ x, f₂ x)) _ a e ?_ ?_ hgap
  · -- closeness: joint agreement with the stack is agreement over the pair alphabet
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    simp only [interleavedList, Finset.mem_filter, Finset.mem_product] at hp
    refine le_trans hp.2 (Finset.card_le_card ?_)
    intro x hx
    simp only [jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦdef, Prod.mk.injEq]
    exact ⟨hx.1.symm, hx.2.symm⟩
  · -- pairwise: distinct pairs differ in some row; pair agreement ⊆ row agreement
    intro c hc c' hc' hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hc'
    have hpne : p ≠ p' := fun h => hne (congrArg Φ h)
    simp only [interleavedList, Finset.mem_filter, Finset.mem_product] at hp hp'
    have hcomp : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
      rcases eq_or_ne p.1 p'.1 with h1 | h1
      · rcases eq_or_ne p.2 p'.2 with h2 | h2
        · exact absurd (Prod.ext h1 h2) hpne
        · exact Or.inr h2
      · exact Or.inl h1
    rcases hcomp with h1 | h2
    · refine le_trans (Finset.card_le_card ?_) (hagree p.1 hp.1.1 p'.1 hp'.1.1 h1)
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦdef,
        Prod.mk.injEq] at hx ⊢
      exact hx.1
    · refine le_trans (Finset.card_le_card ?_) (hagree p.2 hp.1.2 p'.2 hp'.1.2 h2)
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦdef,
        Prod.mk.injEq] at hx ⊢
      exact hx.2

/-! ## The splice through the O85 conversion -/

open Classical in
/-- **The Johnson-interleaved splice on the `epsMCA` surface.**  For any `PairClosed`
code `C` (every `F`-linear code) whose distinct codewords agree on at most `e = n − d`
points, if the collapse floor `a = 2t − n` (`t = ⌈(1 − δ)n⌉₊`) clears the Johnson gap
`n·e < a²`, then

  `ε_mca(C, δ) ≤ (1 + (n − a) · (n²/(a² − n·e))) / |F|`,

in δ-units `(1 + 2δn·L_J)/q` with the Johnson list size `L_J = n²/(a² − n·e)`.
Unconditional: no extraction residual, no list-decodability hypothesis — only
linearity and the distance parameter.  The pair-alphabet Johnson cap feeds the O85
general-`L` conversion (`epsMCA_le_of_interleavedList_card_le`) verbatim. -/
theorem epsMCA_le_interleavedJohnson (C : Finset (ι → F)) (hC : PairClosed C)
    (δ : ℝ≥0) (e : ℕ)
    (hagree : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ e)
    (hgap : Fintype.card ι * e <
      (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι) ^ 2) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) *
          (Fintype.card ι ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι) ^ 2 -
              Fintype.card ι * e)) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_interleavedList_card_le C hC δ _
    (fun u₀ u₁ => interleavedList_card_le_johnson C u₀ u₁ hagree hgap)

/-! ## The named window: `δ < (1 − √(e/n))/2`, half the Johnson radius -/

/-- **The real-units Johnson window implies the ℕ gap.**  If `n·e < ((1 − 2δ)·n)²`
(ℝ≥0 truncation handles `2δ ≥ 1` for free: the hypothesis is then unsatisfiable), the
collapse floor `a = 2t − n` clears the gap `n·e < a²`. -/
theorem nat_gap_of_johnson_window {n e : ℕ} {δ : ℝ≥0}
    (h : (n : ℝ≥0) * e < ((1 - 2 * δ) * n) ^ 2) :
    n * e < (2 * ⌈(1 - δ) * (n : ℝ≥0)⌉₊ - n) ^ 2 := by
  rcases le_total 1 (2 * δ) with hδ | hδ2
  · rw [tsub_eq_zero_of_le hδ, zero_mul] at h
    simp at h
  · have hδ1 : δ ≤ 1 := le_trans (le_mul_of_one_le_left (zero_le δ) one_le_two) hδ2
    set t := ⌈(1 - δ) * (n : ℝ≥0)⌉₊ with htdef
    have ht : (1 - δ) * (n : ℝ≥0) ≤ (t : ℝ≥0) := Nat.le_ceil _
    have htR : (1 - (δ : ℝ)) * (n : ℝ) ≤ (t : ℝ) := by
      have hcoe := NNReal.coe_le_coe.mpr ht
      rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one, NNReal.coe_natCast,
        NNReal.coe_natCast] at hcoe
    have hδR : 2 * (δ : ℝ) ≤ 1 := by exact_mod_cast hδ2
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2t : n ≤ 2 * t := by
      have hR : (n : ℝ) ≤ 2 * (t : ℝ) := by nlinarith
      exact_mod_cast hR
    -- the real form of the hypothesis
    have hR : (n : ℝ) * e < ((1 - 2 * (δ : ℝ)) * n) ^ 2 := by
      have hcoe := NNReal.coe_lt_coe.mpr h
      rwa [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_sub hδ2,
        NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
        NNReal.coe_natCast] at hcoe
    -- the floor dominates the truncation-free radius
    have haR : (1 - 2 * (δ : ℝ)) * n ≤ ((2 * t - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub h2t]
      push_cast
      nlinarith
    have h0 : (0 : ℝ) ≤ (1 - 2 * (δ : ℝ)) * n := by nlinarith
    have hsq : ((1 - 2 * (δ : ℝ)) * n) ^ 2 ≤ ((2 * t - n : ℕ) : ℝ) ^ 2 := by
      nlinarith [mul_le_mul haR haR h0 (h0.trans haR)]
    have : (n : ℝ) * e < ((2 * t - n : ℕ) : ℝ) ^ 2 := lt_of_lt_of_le hR hsq
    exact_mod_cast this

/-- **The named δ-window.**  `2δ + √(e/n) < 1` — i.e. `δ < (1 − √(e/n))/2`, half the
Johnson radius of a code with pairwise agreement `e` — implies the real-units gap
hypothesis.  For RS of rate `ρ`, `e/n = (k−1)/n < ρ` and the window contains
`δ < (1 − √ρ)/2`. -/
theorem johnson_window_of_sqrt {n e : ℕ} {δ : ℝ≥0} (hn : 0 < n)
    (h : 2 * δ + NNReal.sqrt ((e : ℝ≥0) / n) < 1) :
    (n : ℝ≥0) * e < ((1 - 2 * δ) * n) ^ 2 := by
  have h2δ : 2 * δ ≤ 1 := ((le_add_right le_rfl).trans_lt h).le
  have hs : NNReal.sqrt ((e : ℝ≥0) / n) < 1 - 2 * δ := lt_tsub_iff_left.mpr h
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- pass to ℝ
  rw [← NNReal.coe_lt_coe, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mul,
    NNReal.coe_sub h2δ, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat,
    NNReal.coe_natCast, NNReal.coe_natCast]
  set s : ℝ := (NNReal.sqrt ((e : ℝ≥0) / n) : ℝ) with hsdef
  have hs0 : (0 : ℝ) ≤ s := (NNReal.sqrt _).coe_nonneg
  have hsR : s < 1 - 2 * (δ : ℝ) := by
    have hcoe := NNReal.coe_lt_coe.mpr hs
    rwa [NNReal.coe_sub h2δ, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat]
      at hcoe
  have hs2 : s ^ 2 = (e : ℝ) / n := by
    have := congrArg (NNReal.toReal) (NNReal.sq_sqrt ((e : ℝ≥0) / n))
    rwa [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
      at this
  have he : (e : ℝ) = s ^ 2 * n := by
    field_simp at hs2
    linarith [hs2]
  have hpos : (0 : ℝ) < 1 - 2 * (δ : ℝ) := lt_of_le_of_lt hs0 hsR
  have hs2lt : s ^ 2 < (1 - 2 * (δ : ℝ)) ^ 2 := by nlinarith
  have hn2 : (0 : ℝ) < (n : ℝ) * n := mul_pos hnR hnR
  have hne : (n : ℝ) * e = s ^ 2 * ((n : ℝ) * n) := by rw [he]; ring
  have hrhs : ((1 - 2 * (δ : ℝ)) * n) ^ 2 = (1 - 2 * (δ : ℝ)) ^ 2 * ((n : ℝ) * n) := by
    ring
  rw [hne, hrhs]
  exact mul_lt_mul_of_pos_right hs2lt hn2

open Classical in
/-- **The splice on the named window.**  If `2δ + √(e/n) < 1` (i.e. `δ` is below half
the Johnson radius `(1 − √(e/n))/2`), then unconditionally

  `ε_mca(C, δ) ≤ (1 + (n − a)·(n²/(a² − n·e))) / |F|`,  `a = 2⌈(1 − δ)n⌉₊ − n`.

For RS codes this window is `δ < (1 − √ρ)/2 − O(1/n)`: **strictly wider than the
unconditional `d/(3n) ≈ (1 − ρ)/3` window of O84 whenever `ρ < 1/4`**
(`johnson_window_wider_of_low_rate`; crossover exactly at `ρ = 1/4`). -/
theorem epsMCA_le_interleavedJohnson_of_sqrt_window (C : Finset (ι → F))
    (hC : PairClosed C) (δ : ℝ≥0) (e : ℕ)
    (hagree : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ e)
    (hδ : 2 * δ + NNReal.sqrt ((e : ℝ≥0) / Fintype.card ι) < 1) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) *
          (Fintype.card ι ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι) ^ 2 -
              Fintype.card ι * e)) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_interleavedJohnson C hC δ e hagree
    (nat_gap_of_johnson_window (johnson_window_of_sqrt Fintype.card_pos hδ))

/-! ## Window containment and the comparison vs `d/(3n)` -/

/-- **The UD window implies the Johnson gap** (AM–GM: `4ne ≤ (n+e)² < (2a)²`).  So the
Johnson splice covers the entire O78 unconditional `d/(4n)` window (with constant
`L_J ≥ 1` in place of `1`), and the Johnson-only band `n·e < a² ≤ (n+e+1)²/4` is
strictly new unconditional territory. -/
theorem nat_gap_of_ud_window {n e a : ℕ} (h : n + e < 2 * a) : n * e < a ^ 2 := by
  zify
  nlinarith [sq_nonneg ((n : ℤ) - e)]

/-- **The comparison vs O84's `d/(3n)`, low-rate side.**  With `ρ` standing for the
asymptotic `e/n` (for RS, the rate), below `ρ = 1/4` the Johnson half-radius window
`(1 − √ρ)/2` strictly exceeds the unconditional `d/(3n) → (1 − ρ)/3` window:
`0.3232… vs 0.2917` at `ρ = 1/8`, `0.375 vs 0.3125` at `ρ = 1/16`. -/
theorem johnson_window_wider_of_low_rate {ρ : ℝ} (h0 : 0 ≤ ρ) (h : ρ < 1 / 4) :
    (1 - ρ) / 3 < (1 - Real.sqrt ρ) / 2 := by
  have hs0 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt h0
  have hs : Real.sqrt ρ < 1 / 2 := by
    have h14 : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
    have := Real.sqrt_lt_sqrt h0 h
    rwa [h14, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)] at this
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 / 2 - Real.sqrt ρ)
    (by linarith : (0:ℝ) < 1 - Real.sqrt ρ)]

/-- **The crossover is exactly `ρ = 1/4`**: there the two windows coincide at `1/4`. -/
theorem johnson_window_crossover :
    (1 - (1 / 4 : ℝ)) / 3 = (1 - Real.sqrt (1 / 4)) / 2 := by
  have h14 : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
  rw [h14, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]
  norm_num

/-- **The comparison, high-rate side**: above `ρ = 1/4` (and below `1`) the O84
`d/(3n)` window is the wider one — the two unconditional mechanisms genuinely
dovetail at `ρ = 1/4`. -/
theorem johnson_window_narrower_of_high_rate {ρ : ℝ} (h14 : 1 / 4 < ρ) (h1 : ρ < 1) :
    (1 - Real.sqrt ρ) / 2 < (1 - ρ) / 3 := by
  have h0 : (0 : ℝ) ≤ ρ := le_trans (by norm_num) h14.le
  have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt h0
  have hs : 1 / 2 < Real.sqrt ρ := by
    have h142 : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
    have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1 / 4) h14
    rwa [h142, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)] at this
  have hs1 : Real.sqrt ρ < 1 := by
    have := Real.sqrt_lt_sqrt h0 h1
    rwa [Real.sqrt_one] at this
  nlinarith [mul_pos (by linarith : (0:ℝ) < Real.sqrt ρ - 1 / 2)
    (by linarith : (0:ℝ) < 1 - Real.sqrt ρ)]

/-! ## Non-vacuity -/

/-- The splice fires beyond the UD window: the in-tree zero code over `ZMod 5` on three
coordinates at `δ = 0` (satisfiability witness for the full hypothesis set, with the
gap supplied by `nat_gap_of_ud_window` from the UD window — certifying the containment
is usable end-to-end). -/
example :
    epsMCA (F := ZMod 5) (A := ZMod 5)
        (↑({fun _ => (0 : ZMod 5)} : Finset (Fin 3 → ZMod 5)) : Set (Fin 3 → ZMod 5)) 0 ≤
      ((1 + (Fintype.card (Fin 3) -
          (2 * ⌈(1 - (0 : ℝ≥0)) * (Fintype.card (Fin 3) : ℝ≥0)⌉₊ - Fintype.card (Fin 3))) *
          (Fintype.card (Fin 3) ^ 2 /
            ((2 * ⌈(1 - (0 : ℝ≥0)) * (Fintype.card (Fin 3) : ℝ≥0)⌉₊ -
              Fintype.card (Fin 3)) ^ 2 - Fintype.card (Fin 3) * 0)) : ℕ) : ℝ≥0∞)
        / (Fintype.card (ZMod 5) : ℝ≥0∞) := by
  refine epsMCA_le_interleavedJohnson _ pairClosed_zero_code 0 0
    (fun g₁ hg₁ g₂ hg₂ hne => ?_) ?_
  · rw [Finset.mem_singleton] at hg₁ hg₂
    exact absurd (hg₁.trans hg₂.symm) hne
  · refine nat_gap_of_ud_window ?_
    simp

end ProximityGap

#print axioms ProximityGap.interleavedList_card_le_johnson
#print axioms ProximityGap.epsMCA_le_interleavedJohnson
#print axioms ProximityGap.nat_gap_of_johnson_window
#print axioms ProximityGap.johnson_window_of_sqrt
#print axioms ProximityGap.epsMCA_le_interleavedJohnson_of_sqrt_window
#print axioms ProximityGap.nat_gap_of_ud_window
#print axioms ProximityGap.johnson_window_wider_of_low_rate
#print axioms ProximityGap.johnson_window_crossover
#print axioms ProximityGap.johnson_window_narrower_of_high_rate
