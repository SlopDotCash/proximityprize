/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedUD

/-!
# The general-`L` interleaved conversion on the `epsMCA` surface (#232)

The O78 record claims that "any future interleaved-list bound `L(2δ)` … converts to
`ε_mca ≤ (1 + 2δn·L)/q` with zero plumbing left" — but only the `L = 1`
(unique-decoding) instantiation `epsMCA_le_interleavedUD` is a theorem; the general-`L`
conversion exists only on the exact-count surface
(`mcaBad_card_le_of_interleavedList_card_le`).  This file makes the claimed conversion a
theorem, in two hypothesis shapes, so a future interleaved list bound for explicit
smooth-domain RS plugs in with literally zero plumbing.

## Main results

* `interleavedList_card_anti` — the `m = 2` interleaved list is **antitone in the
  agreement floor**: raising the floor shrinks the list.
* `ceil_doubled_radius_le` — **the floor bridge**: the natural doubled-radius floor
  `⌈(1 − 2δ)·n⌉₊` (the ℕ form of "the list of `C^{≡2}` at radius `2δ`") is at most the
  theorem floor `2·⌈(1 − δ)·n⌉₊ − n` produced by the O74 collapse, for *every* `δ`
  (ℝ≥0 truncation handles `δ ≥ 1/2` for free).  Probe: 9,420 `(n, δ)` points, 0 failures.
* `epsMCA_le_of_interleavedList_card_le` — **the general-`L` conversion**: for a
  `PairClosed` code (every `F`-linear code), a uniform interleaved list bound `L` at the
  collapse floor `2t − n` (`t = ⌈(1 − δ)·n⌉₊`) gives

    `ε_mca(C, δ) ≤ (1 + (n − (2t − n))·L) / |F|`,

  in δ-units `(1 + 2δn·L)/q` — the [GCXK25]-shaped conversion of ABF26 §5 stated on the
  repo's prize surface.  O78's `epsMCA_le_interleavedUD` is the `L = 1` slice.
* `epsMCA_le_of_interleavedList_card_le_doubledRadius` — the same conclusion from a list
  bound at the **natural radius** `⌈(1 − 2δ)·n⌉₊` (via antitonicity + the floor bridge):
  the hypothesis a list-decodability statement `Λ(C^{≡2}, 2δ) ≤ L` actually provides.
* `epsMCA_le_interleaved_trivial` — non-vacuity for **every** linear code, no window
  hypothesis: the trivial list bound `L = |C|²` (`interleavedList_card_le_sq`) already
  yields an unconditional (weak) `ε_mca` bound, so the general theorem is satisfiable
  far beyond the unique-decoding window.

## Falsification record (`scripts/probes/probe_epsmca_interleaved_list.py`, exit 0)

* C1 (floor bridge, exact rationals with ℝ≥0/ℕ truncation semantics): `n ≤ 60`,
  157-point δ-grid through `1.3` — 9,420 points, 0 failures.
* C2 (antitone + composition): exhaustive `F₃` stacks over three codes
  (`n = 4, k = 2` ×2; `n = 3, k = 1`), 8-point δ-grid — 110,808 `(stack, δ)` checks:
  floor bridge, antitonicity, and `#mcaBad(t) ≤ 1 + (n − a)·L(a₀)` at the natural floor
  `a₀ = ⌈(1 − 2δ)n⌉₊` all hold with 0 failures; bound saturated in 8,424 cases.
  Bad counts cross-checked by full `2^n` subset enumeration on 7,200 controls,
  0 mismatches.
* C3 (honesty): the `L(a₀) ≥ 2` regime occurs 82,035 times in the sweep, but at `q = 3`
  the bad count never *strictly* exceeded the `L = 1` form `1 + (n − a)` — consistent
  with O74's record that the factor-free variant survived all probes.  The general-`L`
  theorem is exactly as strong as the count-surface collapse it transports; whether the
  `L`-factor is ever needed remains the open refinement recorded in O74.

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

/-! ## Antitonicity and the trivial bound -/

/-- The interleaved list is antitone in the agreement floor: raising the floor can only
shrink the list. -/
theorem interleavedList_card_anti (C : Finset (ι → F)) (f₁ f₂ : ι → F) {a a' : ℕ}
    (h : a ≤ a') :
    (interleavedList C f₁ f₂ a').card ≤ (interleavedList C f₁ f₂ a).card := by
  refine Finset.card_le_card fun p hp => ?_
  simp only [interleavedList, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, le_trans h hp.2⟩

/-- The trivial interleaved list bound `L = |C|²`: the list is a filter of `C ×ˢ C`. -/
theorem interleavedList_card_le_sq (C : Finset (ι → F)) (f₁ f₂ : ι → F) (a : ℕ) :
    (interleavedList C f₁ f₂ a).card ≤ C.card * C.card :=
  le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_product _ _))

/-! ## The floor bridge -/

/-- **The floor bridge.**  The natural doubled-radius floor `⌈(1 − 2δ)·n⌉₊` is at most
the O74 collapse floor `2·⌈(1 − δ)·n⌉₊ − n`, for every `δ` (when `2δ ≥ 1` the left side
is `0` by ℝ≥0 truncation and the inequality is trivial).  Hence, by antitonicity, a list
bound at the natural radius transports to the collapse floor. -/
theorem ceil_doubled_radius_le (n : ℕ) (δ : ℝ≥0) :
    ⌈(1 - 2 * δ) * (n : ℝ≥0)⌉₊ ≤ 2 * ⌈(1 - δ) * (n : ℝ≥0)⌉₊ - n := by
  rcases le_total 1 (2 * δ) with hδ | hδ2
  · rw [tsub_eq_zero_of_le hδ, zero_mul]
    simp
  · have hδ1 : δ ≤ 1 := le_trans (le_mul_of_one_le_left (zero_le δ) one_le_two) hδ2
    set t := ⌈(1 - δ) * (n : ℝ≥0)⌉₊ with htdef
    have ht : (1 - δ) * (n : ℝ≥0) ≤ (t : ℝ≥0) := Nat.le_ceil _
    have htR : (1 - (δ : ℝ)) * (n : ℝ) ≤ (t : ℝ) := by
      have hcoe := NNReal.coe_le_coe.mpr ht
      rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one, NNReal.coe_natCast,
        NNReal.coe_natCast] at hcoe
    have hδR : 2 * (δ : ℝ) ≤ 1 := by exact_mod_cast hδ2
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : 2 * (δ : ℝ) * (n : ℝ) ≤ (n : ℝ) := by nlinarith
    have h2t : n ≤ 2 * t := by
      have hR : (n : ℝ) ≤ 2 * (t : ℝ) := by nlinarith
      exact_mod_cast hR
    rw [Nat.ceil_le, ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hδ2,
      NNReal.coe_one, NNReal.coe_natCast, NNReal.coe_natCast, Nat.cast_sub h2t]
    push_cast
    nlinarith

/-! ## The general-`L` conversion -/

open Classical in
/-- **The general-`L` interleaved conversion on the `epsMCA` surface.**  For any
`PairClosed` code `C` (every `F`-linear code), a uniform interleaved list bound `L` at
the collapse floor `2t − n` (`t = ⌈(1 − δ)·n⌉₊`) gives

  `ε_mca(C, δ) ≤ (1 + (n − (2t − n))·L) / |F|`,

in δ-units `(1 + 2δn·L)/q`.  This is the O78 record's "zero plumbing" claim made a
theorem: the bridge (`mcaEvent_filter_eq_mcaBadSet`) identifies the `epsMCA` bad-scalar
filter with `mcaBadSet`, the O74 collapse (`mcaBad_card_le_of_interleavedList_card_le`)
bounds its size by `1 + (n − (2t − n))·L`, and `epsMCA_le_of_badCount_le` converts.
O78's unconditional window `epsMCA_le_interleavedUD` is the `L = 1` slice. -/
theorem epsMCA_le_of_interleavedList_card_le (C : Finset (ι → F)) (hC : PairClosed C)
    (δ : ℝ≥0) (L : ℕ)
    (hL : ∀ u₀ u₁ : ι → F,
      (interleavedList C u₀ u₁
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)).card ≤ L) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * L : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_of_badCount_le _ _ _ (fun u => ?_)
  rw [mcaEvent_filter_eq_mcaBadSet C δ (u 0) (u 1)]
  exact mcaBad_card_le_of_interleavedList_card_le C hC (u 0) (u 1) (hL (u 0) (u 1))

open Classical in
/-- **The general-`L` conversion from the natural doubled radius.**  The hypothesis a
list-decodability statement actually provides is a bound on the list of `C^{≡2}` at
radius `2δ`, i.e. at the agreement floor `⌈(1 − 2δ)·n⌉₊`.  Antitonicity plus the floor
bridge transport it to the collapse floor, so

  `Λ(C^{≡2}, 2δ) ≤ L  ⟹  ε_mca(C, δ) ≤ (1 + (n − (2t − n))·L)/|F|`

with zero further plumbing. -/
theorem epsMCA_le_of_interleavedList_card_le_doubledRadius (C : Finset (ι → F))
    (hC : PairClosed C) (δ : ℝ≥0) (L : ℕ)
    (hL : ∀ u₀ u₁ : ι → F,
      (interleavedList C u₀ u₁
        ⌈(1 - 2 * δ) * (Fintype.card ι : ℝ≥0)⌉₊).card ≤ L) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * L : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_of_interleavedList_card_le C hC δ L (fun u₀ u₁ => ?_)
  exact le_trans
    (interleavedList_card_anti C u₀ u₁ (ceil_doubled_radius_le (Fintype.card ι) δ))
    (hL u₀ u₁)

/-! ## Non-vacuity: the trivial bound fires for every linear code at every `δ` -/

open Classical in
/-- **Unconditional non-vacuity.**  Every `PairClosed` code satisfies the general-`L`
conversion with the trivial list bound `L = |C|²`, at every `δ` — no window, distance,
or decodability hypothesis.  (Weak, but it certifies the hypotheses of the general
theorem are satisfiable far beyond the unique-decoding window.) -/
theorem epsMCA_le_interleaved_trivial (C : Finset (ι → F)) (hC : PairClosed C)
    (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι))
          * (C.card * C.card) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_interleavedList_card_le C hC δ (C.card * C.card)
    (fun u₀ u₁ => interleavedList_card_le_sq C u₀ u₁ _)

/-- The doubled-radius form instantiates concretely: the in-tree zero code over
`ZMod 5`, any `δ`, with `L = 1` supplied by the trivial bound (`|C| = 1`). -/
example (δ : ℝ≥0) :
    epsMCA (F := ZMod 5) (A := ZMod 5)
        (↑({fun _ => (0 : ZMod 5)} : Finset (Fin 3 → ZMod 5)) : Set (Fin 3 → ZMod 5)) δ ≤
      ((1 + (Fintype.card (Fin 3) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin 3) : ℝ≥0)⌉₊ - Fintype.card (Fin 3))) * 1 : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod 5) : ℝ≥0∞) := by
  refine epsMCA_le_of_interleavedList_card_le_doubledRadius _ pairClosed_zero_code δ 1
    (fun u₀ u₁ => ?_)
  refine le_trans (interleavedList_card_le_sq _ u₀ u₁ _) ?_
  simp

end ProximityGap

#print axioms ProximityGap.interleavedList_card_anti
#print axioms ProximityGap.interleavedList_card_le_sq
#print axioms ProximityGap.ceil_doubled_radius_le
#print axioms ProximityGap.epsMCA_le_of_interleavedList_card_le
#print axioms ProximityGap.epsMCA_le_of_interleavedList_card_le_doubledRadius
#print axioms ProximityGap.epsMCA_le_interleaved_trivial
