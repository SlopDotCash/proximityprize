/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusLowerBound

/-!
# The coset-splitting floor: `ε_mca ≥ n/|F|` on the upper half of the radius range

The general law behind the take-over countermodel (`TakeoverCountermodel.lean`), as a
theorem for **every** scale. Let the evaluation domain `dom : Fin n → F` (`n = 2m`)
satisfy `(dom i)^n = 1` with the two square-root signs balanced (`m` points with
`dom i ^ m = 1` and `m` with `−1` — automatic for the smooth domain `μ_n`), let the code
be the degree-`< k` evaluation code with `k ≥ 2`, and let `char F ≠ 2`.

**The half-order pair `(X^{m+1}, X^m)` makes every `λ ∈ −μ_n` MCA-bad at every agreement
`k + 1 ≤ a ≤ m + 1`** (`halfPair_mcaEvent`): on the domain, `x^m = ±1` splits the points
into two cosets, so the line word `x^{m+1} + λx^m = x^m(x + λ)` is `±(x + λ)` —
piecewise linear; a witness consisting of `a − 1` points on the coset *opposite* the
crossing point `−λ` plus the crossing point itself is explained by the linear codeword
`∓(X + λ)` (the crossing contributes the common value `0`), while the indicator row
`x^m` is inexplicable there (a degree-`< k` polynomial agreeing with a constant on
`a − 1 ≥ k` points is that constant, and fails at the crossing — `lowdeg_const_fail`).

Consequences, both in the `mcaDeltaStar` ledger:

* `halfPair_eps_ge` — **`ε_mca(C, 1 − a/n) ≥ n/|F|`** for every such agreement: an
  unconditional floor with *field-independent numerator `n`* across the entire radius
  band `δ ≥ 1/2 − 1/n`, for every balanced-domain code of rate `< 1/2`. (At `(16,4)`
  this is the probes' flat-16 take-over; here it is closed-form at every scale.)
* `mcaDeltaStar_le_of_undersized_field` — **whenever `ε* < n/|F|`, the threshold is
  capped: `δ* ≤ 1 − (m+1)/n = 1/2 − 1/n`.** For rates `< 1/4` this cap sits *below the
  Johnson radius*: under-sized fields do not merely degrade constants — they pin `δ*`
  under `1/2` outright. This makes the "the prize must fix `|F|` large" folklore
  quantitative with an exact numerator (`n`) and an exact radius (`1/2 − 1/n`), and
  identifies exactly where the large-field hypothesis is consumed.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the take-over arc); `TakeoverCountermodel.lean` (the (16,4)/F₉₇ instance);
  [CS25]/[KK25] (the coset-splitting mechanism at capacity, here localized to `x^m`).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.CosetSplittingFloor

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The degree device -/

/-- A degree-`≤ d` polynomial agreeing with a constant on more than `d` points is that
constant, and then cannot take a different value anywhere. -/
theorem lowdeg_const_fail {q' : Polynomial F} {d : ℕ} (hq' : q'.natDegree ≤ d)
    {c y : F} {P : Finset F} (hPcard : d + 1 ≤ P.card)
    (hvan : ∀ x ∈ P, q'.eval x = c) {x₀ : F} (hx₀ : q'.eval x₀ = y)
    (hne : y ≠ c) : False := by
  classical
  set g : Polynomial F := q' - C c with hg
  have hg0 : g = 0 := by
    by_contra hgne
    have hsub : P ⊆ g.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
      show g.IsRoot x
      rw [Polynomial.IsRoot, hg, Polynomial.eval_sub, Polynomial.eval_C,
        hvan x hx, sub_self]
    have hgdeg : g.natDegree ≤ d := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [Polynomial.natDegree_C]
      exact max_le hq' (Nat.zero_le _)
    have : d + 1 ≤ g.natDegree := by
      calc d + 1 ≤ P.card := hPcard
        _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
        _ ≤ g.natDegree := Polynomial.card_roots' g
    omega
  have hq'c : q' = C c := sub_eq_zero.mp hg0
  rw [hq'c, Polynomial.eval_C] at hx₀
  exact hne hx₀.symm

/-! ## The splitting event -/

section Splitting

variable {n m k : ℕ} (dom : Fin n → F)

/-- The sign of a domain point: its `m`-th power (`±1` under the balance hypotheses). -/
def sgn (i : Fin n) : F := dom i ^ m

/-- **The half-pair coset-splitting event.** Under the balanced-coset hypotheses, every
`λ = −dom j` fires the MCA event for the stack `(x^{m+1}, x^m)` at every agreement
`k + 1 ≤ a ≤ m + 1`. -/
theorem halfPair_mcaEvent [Nonempty (Fin n)] (hinj : Function.Injective dom)
    (hm : n = 2 * m) (hk : 2 ≤ k) {a : ℕ} (hka : k + 1 ≤ a) (ham : a ≤ m + 1)
    (hsign : ∀ i, dom i ^ m = 1 ∨ dom i ^ m = -1)
    (hplus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = 1)).card)
    (hminus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = -1)).card)
    (hchar : (-1 : F) ≠ 1) (j : Fin n) :
    mcaEvent (F := F) (A := F) (evalCode dom k : Set (Fin n → F))
      (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0))
      (fun i => dom i ^ (m + 1)) (fun i => dom i ^ m) (-(dom j)) := by
  classical
  set s : F := dom j ^ m with hs
  have hsval : s = 1 ∨ s = -1 := hsign j
  -- a − 1 points on the coset opposite the crossing sign
  set Sopp : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => dom i ^ m = -s)
    with hSopp
  have ham1 : a - 1 ≤ m := by omega
  have hSoppcard : a - 1 ≤ Sopp.card := by
    rcases hsval with h1 | h1
    · refine le_trans ham1 ?_
      calc m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = -1)).card := hminus
        _ = Sopp.card := by rw [hSopp, h1]
    · refine le_trans ham1 ?_
      have hneg : (-s : F) = 1 := by rw [h1, neg_neg]
      calc m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = 1)).card := hplus
        _ = Sopp.card := by rw [hSopp, hneg]
  obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq hSoppcard
  have hjT₀ : j ∉ T₀ := by
    intro hj
    have hmem := hT₀sub hj
    rw [hSopp, Finset.mem_filter] at hmem
    have hss : s = -s := by
      rw [hs]
      exact hmem.2
    rcases hsval with h1 | h1
    · rw [h1] at hss; exact hchar hss.symm
    · rw [h1, neg_neg] at hss; exact hchar hss
  set T : Finset (Fin n) := insert j T₀ with hT
  have hTcard : T.card = a := by
    rw [hT, Finset.card_insert_of_notMem hjT₀, hT₀card]
    omega
  -- the explicit linear explanation: (−s)·(X + λ), λ = −dom j
  set lam : F := -(dom j) with hlam
  have hexpl_mem : (fun i => (-s) * (dom i + lam)) ∈
      (evalCode dom k : Set (Fin n → F)) := by
    refine (mem_evalCode _).mpr ⟨C (-s) * (X + C lam), ?_, fun i => ?_⟩
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
      omega
    · simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X]
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; omega)]
  refine ⟨T, by rw [hTcard], ⟨fun i => (-s) * (dom i + lam), hexpl_mem, fun i hi => ?_⟩,
    ?_⟩
  · -- agreement of the explanation with the line on T
    rw [smul_eq_mul]
    rw [hT, Finset.mem_insert] at hi
    rcases hi with hij | hi
    · -- the crossing point: both sides are 0
      subst hij
      rw [hlam, pow_succ]
      ring
    · -- an opposite-coset point: x^m = −s
      have hival : dom i ^ m = -s := by
        have := hT₀sub hi
        rw [hSopp, Finset.mem_filter] at this
        exact this.2
      rw [pow_succ, hival]
      ring
  · -- no joint explanation: the indicator row x^m is inexplicable on T
    rintro ⟨w₀, _, w₁, hw₁, hag⟩
    obtain ⟨q', hq', hw₁'⟩ := (mem_evalCode w₁).mp hw₁
    have hq'deg : q'.natDegree ≤ k - 1 := hq'
    -- q' agrees with the constant −s on the a−1 ≥ k points of T₀'s image
    refine lowdeg_const_fail (d := k - 1) (c := -s) (y := s)
      (P := T₀.image dom) (x₀ := dom j) hq'deg ?_ ?_ ?_ ?_
    · rw [Finset.card_image_of_injective _ hinj, hT₀card]
      omega
    · intro x hx
      obtain ⟨i, hiT₀, rfl⟩ := Finset.mem_image.mp hx
      have hival : dom i ^ m = -s := by
        have := hT₀sub hiT₀
        rw [hSopp, Finset.mem_filter] at this
        exact this.2
      have hiT : i ∈ T := by
        rw [hT]
        exact Finset.mem_insert_of_mem hiT₀
      have hagi : w₁ i = dom i ^ m := (hag i hiT).2
      rw [← hw₁' i, hagi, hival]
    · have hjT : j ∈ T := by
        rw [hT]
        exact Finset.mem_insert_self _ _
      have hagj : w₁ j = dom j ^ m := (hag j hjT).2
      rw [← hw₁' j, hagj, ← hs]
    · -- s ≠ −s in characteristic ≠ 2
      intro hcontra
      rcases hsval with h1 | h1
      · rw [h1] at hcontra; exact hchar hcontra.symm
      · rw [h1, neg_neg] at hcontra; exact hchar hcontra

open Classical in
/-- **The coset-splitting floor:** `ε_mca(C, 1 − a/n) ≥ n/|F|` at every agreement
`k + 1 ≤ a ≤ m + 1`, for every balanced even-order smooth domain and every `k ≥ 2`. -/
theorem halfPair_eps_ge [Nonempty (Fin n)] (hinj : Function.Injective dom)
    (hm : n = 2 * m) (hk : 2 ≤ k) {a : ℕ} (hka : k + 1 ≤ a) (ham : a ≤ m + 1)
    (hsign : ∀ i, dom i ^ m = 1 ∨ dom i ^ m = -1)
    (hplus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = 1)).card)
    (hminus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = -1)).card)
    (hchar : (-1 : F) ≠ 1) :
    (n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (evalCode dom k : Set (Fin n → F))
          (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0)) := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := F) _ _
    ![fun i => dom i ^ (m + 1), fun i => dom i ^ m])
  have h0 : (![fun i => dom i ^ (m + 1), fun i => dom i ^ m] :
      WordStack F (Fin 2) (Fin n)) 0 = fun i => dom i ^ (m + 1) := rfl
  have h1 : (![fun i => dom i ^ (m + 1), fun i => dom i ^ m] :
      WordStack F (Fin 2) (Fin n)) 1 = fun i => dom i ^ m := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  have hsub : Finset.univ.image (fun j : Fin n => -(dom j)) ⊆ Finset.filter
      (fun lam : F => mcaEvent (F := F) (A := F)
        (evalCode dom k : Set (Fin n → F))
        (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0))
        (fun i => dom i ^ (m + 1)) (fun i => dom i ^ m) lam)
      Finset.univ := by
    intro lam hlam
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hlam
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      halfPair_mcaEvent dom hinj hm hk hka ham hsign hplus hminus hchar j⟩
  have himgcard : (Finset.univ.image (fun j : Fin n => -(dom j))).card = n := by
    rw [Finset.card_image_of_injective _ (fun x y hxy => hinj (neg_injective hxy)),
      Finset.card_univ, Fintype.card_fin]
  gcongr
  calc (n : ℕ) = (Finset.univ.image (fun j : Fin n => -(dom j))).card := himgcard.symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **The under-sized-field ceiling:** if `ε* < n/|F|`, then
`δ* ≤ 1 − (m+1)/n = 1/2 − 1/n`. For rates `< 1/4` this cap is *below the Johnson
radius*: the large-field hypothesis of the prize is consumed exactly on the band
`δ ≥ 1/2 − 1/n`, with the exact numerator `n`. -/
theorem mcaDeltaStar_le_of_undersized_field [Nonempty (Fin n)]
    (hinj : Function.Injective dom)
    (hm : n = 2 * m) (hk : 2 ≤ k) (hkm : k + 1 ≤ m + 1)
    (hsign : ∀ i, dom i ^ m = 1 ∨ dom i ^ m = -1)
    (hplus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = 1)).card)
    (hminus : m ≤ (Finset.univ.filter (fun i : Fin n => dom i ^ m = -1)).card)
    (hchar : (-1 : F) ≠ 1) {εstar : ℝ≥0∞}
    (hε : εstar < (n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F) (evalCode dom k : Set (Fin n → F)) εstar
      ≤ 1 - ((m + 1 : ℕ) : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0) :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hε
    (halfPair_eps_ge dom hinj hm hk hkm le_rfl hsign hplus hminus hchar))

end Splitting

/-! ## Source audit -/

#print axioms lowdeg_const_fail
#print axioms halfPair_mcaEvent
#print axioms halfPair_eps_ge
#print axioms mcaDeltaStar_le_of_undersized_field

end ProximityGap.CosetSplittingFloor
