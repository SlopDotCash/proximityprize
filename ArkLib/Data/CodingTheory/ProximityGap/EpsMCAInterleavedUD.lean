/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InterleavedListMCACollapse
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The interleaved collapse on the `epsMCA` surface: a second unconditional upper window (#232)

The O74 brick (`InterleavedListMCACollapse`) bounds the **exact-count** bad set
`mcaBadSet C f₁ f₂ t` by the `m = 2` interleaved list at the doubled radius, but it lives
on its own ℕ-floor surface, while the repo's prize quantity `ε_mca` (`epsMCA`,
ABF26 Definition 4.3) is the supremum of `Pr_γ[mcaEvent]` with a *real* floor
`(S.card : ℝ≥0) ≥ (1 − δ)·n`.  This file splices the two surfaces together and
instantiates the collapse, producing the library's **second unconditional `ε_mca`
upper window** (the first, O77's `TheoremQUpperReduction`, is *conditional* on the
affine-root extraction residual).

## Main results

* `mcaEvent_iff_mem_mcaBadSet` — **the bridge, as a theorem**: for a finite code `C`,
  `mcaEvent ↑C δ u₀ u₁ γ ↔ γ ∈ mcaBadSet C u₀ u₁ ⌈(1 − δ)·n⌉₊`.  The two bad-event
  surfaces coincide exactly at the **ceiling** floor — the quantifier shapes match
  (witness set, line-agreement clause, `¬ pairJointAgreesOn` clause), and the only
  conversion is `Nat.ceil_le` on the size clause plus `smul_eq_mul` on the line
  equation.  The floor convention `⌊(1 − δ)·n⌋₊` is **wrong** (probe: 14,844
  mismatch witnesses); the ceiling is exact (probe: 0 mismatches in 260,570 checks).
* `interleavedList_card_le_one_of_agree_le` — **unique decoding of `C^{≡2}`**: if
  distinct codewords of `C` agree on at most `e = n − d` points and the floor `a`
  satisfies `n + e < 2a`, the interleaved list of any stack at floor `a` has at most
  one element.  (The interleaved code `C^{≡2}` has the same minimum distance `d` as
  `C` in joint-column count: any differing pair differs in some row.)
* `epsMCA_le_interleavedUD` — **the second unconditional upper window**: for any
  `PairClosed` code (every `F`-linear code) with pairwise agreement bound `e`, if
  `n + e < 2·(2t − n)` with `t = ⌈(1 − δ)·n⌉₊`, then

    `ε_mca(C, δ) ≤ (1 + (n − (2t − n))) / |F|`.

  No probabilistic, list-decoding, or extraction hypothesis: only linearity and the
  code's distance parameter.  In δ-units the bound reads `(1 + 2δn)/q` (up to the
  integer ceiling).
* `epsMCA_le_interleavedUD_of_quarter_dist` — the same bound on the **named
  δ-window** `4δn + e < n`, i.e. `δ < d/(4n)` where `d = n − e` is the minimum
  distance: the clean real-units window implies the ℕ window
  (`nat_window_of_quarter_dist`).

## The window, vs O77

O77 (`TheoremQUpperReduction.epsMCA_le_of_affineRoot_extraction`) gives
`ε_mca ≤ W/q ≤ n/q` on the unique-decoding window `δ < d/(2n)` **conditional** on the
min-distance affine-root extraction (the named residual wall).  This file gives
`ε_mca ≤ (1 + 2δn)/q` on the smaller window `δ < d/(4n)` **unconditionally** — the
radius halves again (the price of the O74 radius doubling: the interleaved list must
be unique-decodable at `2δ`), but the extraction residual disappears entirely.  For
RS codes `d/n = 1 − ρ + 1/n`, so the window is `δ < (1 − ρ)/4` up to `O(1/n)` — a
constant fraction of the unique-decoding radius, at cryptographic `q` far below
`ε* = 2⁻¹²⁸·q` in numerator.

## Falsification record (`scripts/probes/probe_epsmca_interleaved_ud.py`, exit 0)

* C0: the probe's witness-set reduction equals full `2^n` subset enumeration —
  240,570 exhaustive `(stack, γ, δ)` checks over `F₃`/`F₅` codes, 0 mismatches.
* C1 (the bridge): real-floor badness == ceil-ℕ-floor badness, 260,570 checks
  (exhaustive `F₃` `n ∈ {3,4}`, three codes; sampled `F₅` RS), **0 mismatches**;
  the floor convention breaks in 14,844 places (the probe has teeth).
* C2: in the window `n + e < 2a`, interleaved list card ≤ 1 and
  `#mcaBad ≤ 1 + (n − a)` — 7,690 checks, 0 violations, bound saturated (max slack 0).
* C2′: just outside the window the list bound `≤ 1` fails (witnesses found).
* C3: `δ < d/(4n)` implies the ℕ window on a fine δ-grid, 0 failures.

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

/-! ## The bridge: `mcaEvent` (real floor) ⟺ `mcaBadSet` (ℕ floor) at the ceiling -/

/-- **The bridge between the two MCA bad-event surfaces.**  For a finite code `C`, the
repo's `mcaEvent` (ABF26 Definition 4.3, real-valued size clause
`(S.card : ℝ≥0) ≥ (1 − δ)·n`) holds at `γ` iff `γ` lies in the O74 exact-count bad set
`mcaBadSet` at the ℕ floor `t = ⌈(1 − δ)·n⌉₊`.  The witness set, line-agreement clause
and `¬ pairJointAgreesOn` clause correspond verbatim; only the floor needs `Nat.ceil_le`
(the floor convention `⌊·⌋₊` is *false* here — see the probe record). -/
theorem mcaEvent_iff_mem_mcaBadSet (C : Finset (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F) :
    mcaEvent (F := F) (↑C : Set (ι → F)) δ u₀ u₁ γ ↔
      γ ∈ mcaBadSet C u₀ u₁ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ := by
  classical
  simp only [mcaBadSet, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨S, hS, ⟨w, hwC, hweq⟩, hno⟩
    refine ⟨S, Nat.ceil_le.mpr hS, ⟨w, Finset.mem_coe.mp hwC, fun x hx => ?_⟩,
      fun hpair => ?_⟩
    · have h := hweq x hx
      rw [smul_eq_mul] at h
      exact h.symm
    · obtain ⟨g₁, hg₁, g₂, hg₂, hag⟩ := hpair
      exact hno ⟨g₁, Finset.mem_coe.mpr hg₁, g₂, Finset.mem_coe.mpr hg₂, hag⟩
  · rintro ⟨S, hSt, ⟨c, hcC, hag⟩, hno⟩
    refine ⟨S, Nat.ceil_le.mp hSt, ⟨c, Finset.mem_coe.mpr hcC, fun i hi => ?_⟩,
      fun hpair => ?_⟩
    · rw [smul_eq_mul]
      exact (hag i hi).symm
    · obtain ⟨v₀, hv₀, v₁, hv₁, hagg⟩ := hpair
      exact hno ⟨v₀, Finset.mem_coe.mp hv₀, v₁, Finset.mem_coe.mp hv₁, hagg⟩

open Classical in
/-- Count form of the bridge: the `epsMCA` bad-scalar filter *is* `mcaBadSet` at the
ceiling floor. -/
theorem mcaEvent_filter_eq_mcaBadSet (C : Finset (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) :
    Finset.filter (fun γ : F => mcaEvent (F := F) (↑C : Set (ι → F)) δ u₀ u₁ γ) Finset.univ
      = mcaBadSet C u₀ u₁ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ := by
  ext γ
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact mcaEvent_iff_mem_mcaBadSet C δ u₀ u₁ γ

/-! ## Unique decoding of the interleaved code in the window -/

/-- **Unique decoding of `C^{≡2}` from the distance of `C`.**  If distinct codewords of
`C` agree on at most `e` points (`e = n − d`) and `n + e < 2a`, then the `m = 2`
interleaved list of any stack at joint-agreement floor `a` has at most one element:
two list members jointly agree with the stack on `≥ a` points each, hence agree with
*each other* (in both rows) on `≥ 2a − n > e` points, forcing both rows equal. -/
theorem interleavedList_card_le_one_of_agree_le (C : Finset (ι → F)) (f₁ f₂ : ι → F)
    {a e : ℕ}
    (hagree : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ e)
    (hwin : Fintype.card ι + e < 2 * a) :
    (interleavedList C f₁ f₂ a).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro p hp p' hp'
  simp only [interleavedList, mem_filter, Finset.mem_product] at hp hp'
  obtain ⟨⟨hp1, hp2⟩, hpa⟩ := hp
  obtain ⟨⟨hp1', hp2'⟩, hpa'⟩ := hp'
  by_contra hne
  have hinter := inter_card_ge hpa hpa'
  have hcomp : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
    rcases eq_or_ne p.1 p'.1 with h1 | h1
    · rcases eq_or_ne p.2 p'.2 with h2 | h2
      · exact absurd (Prod.ext h1 h2) hne
      · exact Or.inr h2
    · exact Or.inl h1
  rcases hcomp with h1 | h2
  · have hsub : jointAgreeSet f₁ f₂ p.1 p.2 ∩ jointAgreeSet f₁ f₂ p'.1 p'.2 ⊆
        Finset.univ.filter (fun x => p.1 x = p'.1 x) := by
      intro x hx
      obtain ⟨hxJ, hxJ'⟩ := Finset.mem_inter.mp hx
      simp only [jointAgreeSet, mem_filter, mem_univ, true_and] at hxJ hxJ'
      simp only [mem_filter, mem_univ, true_and]
      rw [← hxJ.1, ← hxJ'.1]
    have hcard := Finset.card_le_card hsub
    have hbound := hagree p.1 hp1 p'.1 hp1' h1
    omega
  · have hsub : jointAgreeSet f₁ f₂ p.1 p.2 ∩ jointAgreeSet f₁ f₂ p'.1 p'.2 ⊆
        Finset.univ.filter (fun x => p.2 x = p'.2 x) := by
      intro x hx
      obtain ⟨hxJ, hxJ'⟩ := Finset.mem_inter.mp hx
      simp only [jointAgreeSet, mem_filter, mem_univ, true_and] at hxJ hxJ'
      simp only [mem_filter, mem_univ, true_and]
      rw [← hxJ.2, ← hxJ'.2]
    have hcard := Finset.card_le_card hsub
    have hbound := hagree p.2 hp2 p'.2 hp2' h2
    omega

/-- Per-stack bad-count bound in the window: the O74 collapse with `L = 1`. -/
theorem mcaBadSet_card_le_of_agree_le (C : Finset (ι → F)) (hC : PairClosed C)
    (f₁ f₂ : ι → F) {t e : ℕ}
    (hagree : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ e)
    (hwin : Fintype.card ι + e < 2 * (2 * t - Fintype.card ι)) :
    (mcaBadSet C f₁ f₂ t).card
      ≤ 1 + (Fintype.card ι - (2 * t - Fintype.card ι)) := by
  have hL : (interleavedList C f₁ f₂ (2 * t - Fintype.card ι)).card ≤ 1 :=
    interleavedList_card_le_one_of_agree_le C f₁ f₂ hagree hwin
  have h := mcaBad_card_le_of_interleavedList_card_le C hC f₁ f₂ (L := 1) hL
  omega

/-! ## The second unconditional upper window -/

open Classical in
/-- **The second unconditional `ε_mca` upper window (ABF26 §5 collapse, instantiated).**
For any `PairClosed` code `C` (every `F`-linear code) whose distinct codewords agree on
at most `e = n − d` points, if `n + e < 2·(2t − n)` with `t = ⌈(1 − δ)·n⌉₊` — i.e. the
interleaved floor `2t − n` exceeds `n` minus half the (interleaved) minimum distance —
then

  `ε_mca(C, δ) ≤ (1 + (n − (2t − n))) / |F|`,

in δ-units `(1 + 2δn)/q`.  No hypotheses beyond linearity and the distance parameter:
unlike O77's unique-decoding window this carries **no** extraction residual.  Proof:
the bridge identifies the `epsMCA` bad-scalar filter with `mcaBadSet`; unique decoding
of `C^{≡2}` at the doubled radius (`interleavedList_card_le_one_of_agree_le`) feeds the
O74 collapse with `L = 1`; `epsMCA_le_of_badCount_le` converts the count to `ε_mca`. -/
theorem epsMCA_le_interleavedUD (C : Finset (ι → F)) (hC : PairClosed C) (δ : ℝ≥0) (e : ℕ)
    (hagree : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ e)
    (hwin : Fintype.card ι + e <
      2 * (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_of_badCount_le _ _ _ (fun u => ?_)
  rw [mcaEvent_filter_eq_mcaBadSet C δ (u 0) (u 1)]
  exact mcaBadSet_card_le_of_agree_le C hC (u 0) (u 1) hagree hwin

/-! ## The named δ-window: `δ < d/(4n)` -/

/-- **The clean δ-window implies the ℕ window.**  If `4δn + e < n` (with `e = n − d`,
this is `δ < d/(4n)`), then the ceiling floor `t = ⌈(1 − δ)·n⌉₊` satisfies
`n + e < 2·(2t − n)`. -/
theorem nat_window_of_quarter_dist {n e : ℕ} {δ : ℝ≥0}
    (h : 4 * δ * (n : ℝ≥0) + (e : ℝ≥0) < (n : ℝ≥0)) :
    n + e < 2 * (2 * ⌈(1 - δ) * (n : ℝ≥0)⌉₊ - n) := by
  have hn : n ≠ 0 := by
    rintro rfl
    refine absurd h (not_lt.mpr ?_)
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hR : 4 * (δ : ℝ) * n + e < n := by exact_mod_cast h
  have heR : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hδR : (δ : ℝ) < 1 := by nlinarith [hR, hnR, heR]
  have hδ1 : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_one]
    exact hδR.le
  set t := ⌈(1 - δ) * (n : ℝ≥0)⌉₊ with ht
  have hceil : (1 - δ) * (n : ℝ≥0) ≤ (t : ℝ≥0) := Nat.le_ceil _
  have htR : (1 - (δ : ℝ)) * n ≤ (t : ℝ) := by
    have hcoe := NNReal.coe_le_coe.mpr hceil
    rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one, NNReal.coe_natCast,
      NNReal.coe_natCast] at hcoe
  have hkey : 3 * n + e < 4 * t := by
    have hR4 : 3 * (n : ℝ) + e < 4 * t := by nlinarith [htR, hR]
    exact_mod_cast hR4
  omega

open Classical in
/-- **The second window in named δ-units.**  If `4δn + e < n` — for a code of minimum
distance `d = n − e` this is exactly `δ < d/(4n)`, a quarter of the relative distance —
then `ε_mca(C, δ) ≤ (1 + (n − (2t − n)))/|F| = (1 + 2δn + O(1))/q`, with no hypotheses
beyond linearity (`PairClosed`) and the pairwise-agreement parameter `e`. -/
theorem epsMCA_le_interleavedUD_of_quarter_dist (C : Finset (ι → F)) (hC : PairClosed C)
    (δ : ℝ≥0) (e : ℕ)
    (hagree : ∀ g₁ ∈ C, ∀ g₂ ∈ C, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ e)
    (hδ : 4 * δ * (Fintype.card ι : ℝ≥0) + (e : ℝ≥0) < (Fintype.card ι : ℝ≥0)) :
    epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ ≤
      ((1 + (Fintype.card ι -
          (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_interleavedUD C hC δ e hagree (nat_window_of_quarter_dist hδ)

/-! ## Non-vacuity -/

/-- The hypotheses instantiate: the in-tree `pairClosed_zero_code` witness (zero code
over `ZMod 5`, three coordinates) at `δ = 0` satisfies the agreement bound (vacuously,
`e = 0`) and the δ-window `4·0·3 + 0 < 3`, so the main theorem fires. -/
example :
    epsMCA (F := ZMod 5) (A := ZMod 5)
        (↑({fun _ => (0 : ZMod 5)} : Finset (Fin 3 → ZMod 5)) : Set (Fin 3 → ZMod 5)) 0 ≤
      ((1 + (Fintype.card (Fin 3) -
          (2 * ⌈(1 - (0 : ℝ≥0)) * (Fintype.card (Fin 3) : ℝ≥0)⌉₊ - Fintype.card (Fin 3))) : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod 5) : ℝ≥0∞) := by
  refine epsMCA_le_interleavedUD_of_quarter_dist _ pairClosed_zero_code 0 0
    (fun g₁ hg₁ g₂ hg₂ hne => ?_) (by norm_num)
  rw [Finset.mem_singleton] at hg₁ hg₂
  exact absurd (hg₁.trans hg₂.symm) hne

end ProximityGap

#print axioms ProximityGap.mcaEvent_iff_mem_mcaBadSet
#print axioms ProximityGap.mcaEvent_filter_eq_mcaBadSet
#print axioms ProximityGap.interleavedList_card_le_one_of_agree_le
#print axioms ProximityGap.mcaBadSet_card_le_of_agree_le
#print axioms ProximityGap.epsMCA_le_interleavedUD
#print axioms ProximityGap.nat_window_of_quarter_dist
#print axioms ProximityGap.epsMCA_le_interleavedUD_of_quarter_dist
