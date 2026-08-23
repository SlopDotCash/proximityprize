/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetSplittingFloor

/-!
# The splitting ladder: the explicit lower staircase for `ε_mca` on `[UDR, 1/2]`

Generalizes the coset-splitting floor (`CosetSplittingFloor.lean`, the `e = 1` rung) to
the full **monomial splitting ladder**: for the stack `(X^{m+e}, X^m)` over a balanced
even-order domain (`n = 2m`, `dom i ^ m = ±1`), the line word `x^m(x^e + λ)` is piecewise
the *degree-`e` codeword* `±(x^e + λ)` (`e ≤ k − 1`); a witness made of `a − g` points on
the coset opposite the crossing sign plus the `g` crossing points (`x^e = −λ`) fires the
MCA event at every agreement `k + g ≤ a ≤ m + g`.

On the smooth domain `μ_n` the crossings of `λ ∈ −(μ_n)^e` number `g = gcd(e, n)` and lie
in one coset whenever `g ∣ m`, so the ladder gives the **flat, field-independent lower
staircase** (probe-exact at `(16,4)` and `(16,8)`, both `p ∈ {97, 193}`):

  `ε_mca(C, δ) ≥ (n/g)/|F|`  on each band  `δ ≥ 1/2 − g/n`,

interpolating the `n/|F|` floor at `δ ≈ 1/2` (the `g = 1` rung) down to `(2/ρ)/|F|` at
the optimal rung `e = k/2` (2-power scales), which bottoms out at
`δ = 1/2 − k/(2n) = (n−k)/(2n)` — **exactly the unique-decoding radius**. Below the UDR
the probes find the monomial class identically dead, and past the Johnson radius the
counts go field-dependent: the ladder is precisely the structured regime of the window.

This file states the ladder **data-parameterized** (the per-`λ` crossing set is a
hypothesis, kernel-checkable per instance and derivable from subgroup structure): the
event (`ladder_mcaEvent`), and the counted floor (`ladder_eps_ge`) from any injective
family of scalars with crossing data. The group-theoretic instantiation over `μ_n`
(producing the `n/g` scalars with their crossing sets) is the named follow-up.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (middle-band cartography); `probe_middle_band_ladder.py`,
  `probe_takeover_death_radius.py`; `CosetSplittingFloor.lean` (the `e = 1` rung).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.SplittingLadder

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound
open ProximityGap.CosetSplittingFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n m k e g : ℕ} (dom : Fin n → F)

/-- **The ladder event.** Given the balanced-coset structure and, for the scalar `lam`,
a `g`-element crossing set `Xc` (points with `x^e = −lam`, all of one sign `s₀`), the
stack `(x^{m+e}, x^m)` is MCA-bad at `lam` for every agreement `k + g ≤ a ≤ m + g`. -/
theorem ladder_mcaEvent [Nonempty (Fin n)] (hinj : Function.Injective dom)
    (hm : n = 2 * m) (hek : e + 1 ≤ k) (hg1 : 1 ≤ g) (hgm : g ≤ m) {a : ℕ}
    (hka : k + g ≤ a) (ham : a ≤ m + g)
    (hplus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = 1)).card)
    (hminus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = -1)).card)
    (hchar : (-1 : F) ≠ 1)
    (lam s₀ : F) (hs₀ : s₀ = 1 ∨ s₀ = -1)
    (Xc : Finset (Fin n)) (hXcard : Xc.card = g)
    (hXval : ∀ x ∈ Xc, dom x ^ e = -lam)
    (hXsign : ∀ x ∈ Xc, dom x ^ m = s₀) :
    mcaEvent (F := F) (A := F) (evalCode dom k : Set (Fin n → F))
      (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0))
      (fun i => dom i ^ (m + e)) (fun i => dom i ^ m) lam := by
  classical
  -- a − g points on the coset opposite the crossing sign
  set Sopp : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => dom i ^ m = -s₀)
    with hSopp
  have hag : a - g ≤ m := by omega
  have hSoppcard : a - g ≤ Sopp.card := by
    rcases hs₀ with h1 | h1
    · refine le_trans hag ?_
      calc m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = -1)).card := hminus
        _ = Sopp.card := by rw [hSopp, h1]
    · refine le_trans hag ?_
      have hneg : (-s₀ : F) = 1 := by rw [h1, neg_neg]
      calc m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = 1)).card := hplus
        _ = Sopp.card := by rw [hSopp, hneg]
  obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq hSoppcard
  -- signs separate the crossing set from the opposite-coset points
  have hs₀ne : s₀ ≠ -s₀ := by
    intro hcontra
    rcases hs₀ with h1 | h1
    · rw [h1] at hcontra; exact hchar hcontra.symm
    · rw [h1, neg_neg] at hcontra; exact hchar hcontra
  have hdisj : Disjoint T₀ Xc := by
    rw [Finset.disjoint_left]
    intro i hiT₀ hiX
    have h₁ : dom i ^ m = -s₀ := by
      have := hT₀sub hiT₀
      rw [hSopp, Finset.mem_filter] at this
      exact this.2
    have h₂ : dom i ^ m = s₀ := hXsign i hiX
    exact hs₀ne (h₂.symm.trans h₁)
  set T : Finset (Fin n) := T₀ ∪ Xc with hT
  have hTcard : T.card = a := by
    rw [hT, Finset.card_union_of_disjoint hdisj, hT₀card, hXcard]
    omega
  -- the degree-e explanation: (−s₀)·(X^e + λ)
  have hexpl_mem : (fun i => (-s₀) * (dom i ^ e + lam)) ∈
      (evalCode dom k : Set (Fin n → F)) := by
    refine (mem_evalCode _).mpr ⟨C (-s₀) * (X ^ e + C lam), ?_, fun i => ?_⟩
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
      omega
    · simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; omega)]
  refine ⟨T, by rw [hTcard],
    ⟨fun i => (-s₀) * (dom i ^ e + lam), hexpl_mem, fun i hi => ?_⟩, ?_⟩
  · -- agreement on T
    rw [smul_eq_mul]
    rw [hT, Finset.mem_union] at hi
    rcases hi with hi | hi
    · -- opposite-coset point: x^m = −s₀
      have hival : dom i ^ m = -s₀ := by
        have := hT₀sub hi
        rw [hSopp, Finset.mem_filter] at this
        exact this.2
      rw [pow_add, hival]
      ring
    · -- crossing point: x^e = −λ and x^m = s₀ — both sides vanish
      have hie : dom i ^ e = -lam := hXval i hi
      have him : dom i ^ m = s₀ := hXsign i hi
      show (-s₀) * (dom i ^ e + lam) = dom i ^ (m + e) + lam * dom i ^ m
      rw [pow_add, hie, him]
      ring
  · -- no joint explanation: the indicator row is inexplicable on T
    rintro ⟨w₀, _, w₁, hw₁, hag2⟩
    obtain ⟨q', hq', hw₁'⟩ := (mem_evalCode w₁).mp hw₁
    obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by rw [hXcard]; omega : 0 < Xc.card)
    refine lowdeg_const_fail (d := k - 1) (c := -s₀) (y := s₀)
      (P := T₀.image dom) (x₀ := dom x₀) hq' ?_ ?_ ?_ hs₀ne
    · rw [Finset.card_image_of_injective _ hinj, hT₀card]
      omega
    · intro x hx
      obtain ⟨i, hiT₀, rfl⟩ := Finset.mem_image.mp hx
      have hival : dom i ^ m = -s₀ := by
        have := hT₀sub hiT₀
        rw [hSopp, Finset.mem_filter] at this
        exact this.2
      have hiT : i ∈ T := by
        rw [hT]
        exact Finset.mem_union_left _ hiT₀
      have hagi : w₁ i = dom i ^ m := (hag2 i hiT).2
      rw [← hw₁' i, hagi, hival]
    · have hx₀T : x₀ ∈ T := by
        rw [hT]
        exact Finset.mem_union_right _ hx₀
      have hagx : w₁ x₀ = dom x₀ ^ m := (hag2 x₀ hx₀T).2
      rw [← hw₁' x₀, hagx]
      exact hXsign x₀ hx₀

open Classical in
/-- **The counted ladder floor:** any injective family of `c` scalars, each with ladder
crossing data, gives `ε_mca(C, 1 − a/n) ≥ c/|F|`. Over `μ_n` the family is
`−(μ_n)^e` with `c = n/gcd(e,n)`: the staircase heights of the probe table. -/
theorem ladder_eps_ge [Nonempty (Fin n)] (hinj : Function.Injective dom)
    (hm : n = 2 * m) (hek : e + 1 ≤ k) (hg1 : 1 ≤ g) (hgm : g ≤ m) {a : ℕ}
    (hka : k + g ≤ a) (ham : a ≤ m + g)
    (hplus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = 1)).card)
    (hminus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = -1)).card)
    (hchar : (-1 : F) ≠ 1)
    {c : ℕ} (lams : Fin c → F) (hlams : Function.Injective lams)
    (s₀ : Fin c → F) (hs₀ : ∀ jj, s₀ jj = 1 ∨ s₀ jj = -1)
    (Xc : Fin c → Finset (Fin n)) (hXcard : ∀ jj, (Xc jj).card = g)
    (hXval : ∀ jj, ∀ x ∈ Xc jj, dom x ^ e = -(lams jj))
    (hXsign : ∀ jj, ∀ x ∈ Xc jj, dom x ^ m = s₀ jj) :
    (c : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (evalCode dom k : Set (Fin n → F))
          (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0)) := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := F) _ _
    ![fun i => dom i ^ (m + e), fun i => dom i ^ m])
  have h0 : (![fun i => dom i ^ (m + e), fun i => dom i ^ m] :
      WordStack F (Fin 2) (Fin n)) 0 = fun i => dom i ^ (m + e) := rfl
  have h1 : (![fun i => dom i ^ (m + e), fun i => dom i ^ m] :
      WordStack F (Fin 2) (Fin n)) 1 = fun i => dom i ^ m := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  have hsub : Finset.univ.image lams ⊆ Finset.filter
      (fun lam : F => mcaEvent (F := F) (A := F)
        (evalCode dom k : Set (Fin n → F))
        (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0))
        (fun i => dom i ^ (m + e)) (fun i => dom i ^ m) lam)
      Finset.univ := by
    intro lam hlam
    obtain ⟨jj, _, rfl⟩ := Finset.mem_image.mp hlam
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ladder_mcaEvent dom hinj hm hek hg1 hgm hka ham hplus hminus hchar
        (lams jj) (s₀ jj) (hs₀ jj) (Xc jj) (hXcard jj) (hXval jj) (hXsign jj)⟩
  have himgcard : (Finset.univ.image lams).card = c := by
    rw [Finset.card_image_of_injective _ hlams, Finset.card_univ, Fintype.card_fin]
  gcongr
  calc (c : ℕ) = (Finset.univ.image lams).card := himgcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## Source audit -/

#print axioms ladder_mcaEvent
#print axioms ladder_eps_ge

end ProximityGap.SplittingLadder
