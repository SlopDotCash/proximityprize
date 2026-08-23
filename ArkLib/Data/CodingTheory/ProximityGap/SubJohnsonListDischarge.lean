/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListSupply
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound

/-!
# `SubJohnsonListBound` is a THEOREM above the Johnson radius (#389)

The named residual `SubJohnsonListBound dom k m L A` (the open core of #389) is here
**proven unconditionally whenever the band threshold `k+m+1` sits at or above the
Johnson radius** `√(n·(k−1))` — i.e. when `n·(k−1) < (k+m+1)²`.  The proof is the
classical second-moment (Johnson) list bound, already in-tree
(`ArkLib.JohnsonList.johnson_list_bound_div`), fed the Reed–Solomon pairwise
agreement cap `k−1` (`agreement_card_le`):

  `#{codewords agreeing ≥ k+m+1 with w} ≤ n² / ((k+m+1)² − n(k−1))`.

This makes the residual's *name* a theorem: the open part of #389 is **strictly
sub-Johnson** (`(k+m+1)² ≤ n(k−1)`).  Composing with
`explainableCoreSupply_of_listBound`, the deep-band supply is fully proven in the
above-Johnson band, with `B = (n²/((k+m+1)²−n(k−1))) · C(n, k+m+1)`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Reed–Solomon pairwise agreement: two distinct codewords of `rsCode dom k`
(degree `< k`) agree on at most `k − 1` coordinates. -/
theorem rsCode_pairwise_agree_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {c c' : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hne : c ≠ c') :
    (Finset.univ.filter (fun x => c x = c' x)).card ≤ k - 1 := by
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨Q, hQ, rfl⟩ := hc'
  have hPk : P.natDegree < k := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP
  have hQk : Q.natDegree < k := by
    rcases eq_or_ne Q 0 with rfl | hQ0
    · simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQ
  have hPQ : P ≠ Q := by
    intro h; exact hne (by rw [h])
  exact ArkLib.CodingTheory.UniqueDecoding.agreement_card_le (D := dom) hPk hQk hPQ

open Classical in
/-- **The residual is a theorem above the Johnson radius.**  When the band
threshold `k+m+1` lies at/above `√(n(k−1))` (`n·(k−1) < (k+m+1)²`), the sub-Johnson
list bound holds unconditionally with `L = n²/((k+m+1)²−n(k−1))` and the trivial cap
`A = n`.  Hence the open core of #389 is *strictly sub-Johnson*. -/
theorem subJohnsonListBound_aboveJohnson (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    (hJohnson : n * (k - 1) < (k + m + 1) ^ 2) :
    SubJohnsonListBound dom k m
      (n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1))) n := by
  intro w
  refine ⟨?_, ?_⟩
  · -- the second-moment Johnson cap, instantiated
    have hcard : (bigAgreeCodewords dom k m w).card
        ≤ (Fintype.card (Fin n)) ^ 2
            / ((k + m + 1) ^ 2 - Fintype.card (Fin n) * (k - 1)) := by
      refine ArkLib.JohnsonList.johnson_list_bound_div w (bigAgreeCodewords dom k m w)
        (k + m + 1) (k - 1) ?_ ?_ ?_
      · intro c hc
        rw [bigAgreeCodewords, Finset.mem_filter] at hc
        simpa [listAgreeSet] using hc.2.2
      · intro c hc c' hc' hne
        rw [bigAgreeCodewords, Finset.mem_filter] at hc hc'
        exact rsCode_pairwise_agree_le dom hk hc.2.1 hc'.2.1 hne
      · simpa [Fintype.card_fin] using hJohnson
    simpa [Fintype.card_fin] using hcard
  · -- trivial agreement cap A = n
    intro c _
    rw [listAgreeSet]
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp [Finset.card_univ]

open Classical in
/-- **The deep-band supply is fully proven above the Johnson radius.**  Composing the
discharged list bound with `explainableCoreSupply_of_listBound`: when
`n·(k−1) < (k+m+1)²`, the top-level `ExplainableCoreSupply` holds with
`B = (n²/((k+m+1)²−n(k−1))) · C(n, k+m+1)`, no open hypothesis. -/
theorem explainableCoreSupply_aboveJohnson (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    (hJohnson : n * (k - 1) < (k + m + 1) ^ 2) :
    ExplainableCoreSupply dom k m
      ((n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1))) * (n.choose (k + m + 1))) :=
  explainableCoreSupply_of_listBound dom (subJohnsonListBound_aboveJohnson dom hk hJohnson)

open Classical in
/-- **Unconditional subset-counting discharge (valid BELOW Johnson).**  Each
`k`-subset of the domain is owned by at most one codeword (the unique degree-`<k`
interpolant of `w` on those `k` nodes, `explainer_unique`), so summing `C(|agree|, k)`
over the list and counting `k`-subsets gives `|list|·C(k+m+1,k) ≤ C(n,k)` for *every*
band radius.  Hence `SubJohnsonListBound` holds unconditionally with
`L = C(n,k)/C(k+m+1,k)`, `A = n` — no Johnson hypothesis.  This `L` is polynomial for
fixed `k` but *exponential at constant rate* (`k = Θ(n)`), which pinpoints the genuine
open core: not the existence of a list bound (one always exists), but whether it can
be made **subexponential at constant rate**. -/
theorem subJohnsonListBound_unconditional (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k) :
    SubJohnsonListBound dom k m (n.choose k / (k + m + 1).choose k) n := by
  intro w
  refine ⟨?_, ?_⟩
  · set S := bigAgreeCodewords dom k m w with hS
    set P := S.sigma (fun c => (listAgreeSet c w).powersetCard k) with hP
    -- |P| ≤ C(n,k): the second projection `(c,U) ↦ U` is injective (U owns ≤ 1 codeword)
    have hPle : P.card ≤ n.choose k := by
      have hmap : ∀ x ∈ P, x.2 ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
        rintro ⟨c, U⟩ hx
        rw [hP, Finset.mem_sigma] at hx
        rw [Finset.mem_powersetCard] at hx ⊢
        exact ⟨Finset.subset_univ _, hx.2.2⟩
      have hinj : Set.InjOn (fun x : (_ : Fin n → F) × Finset (Fin n) => x.2) P := by
        rintro ⟨c, U⟩ hx ⟨c', U'⟩ hy hUU
        simp only at hUU; subst hUU
        rw [Finset.mem_coe, hP, Finset.mem_sigma] at hx hy
        obtain ⟨hc, hU⟩ := hx
        obtain ⟨hc', hU'⟩ := hy
        rw [Finset.mem_powersetCard] at hU hU'
        rw [hS, bigAgreeCodewords, Finset.mem_filter] at hc hc'
        have hcag : ∀ i ∈ U, c i = w i := fun i hi => by
          have := hU.1 hi; rw [listAgreeSet, Finset.mem_filter] at this; exact this.2
        have hc'ag : ∀ i ∈ U, c' i = w i := fun i hi => by
          have := hU'.1 hi; rw [listAgreeSet, Finset.mem_filter] at this; exact this.2
        have hcc : c = c' :=
          explainer_unique dom hk (le_of_eq hU.2.symm) hc.2.1 hc'.2.1 hcag hc'ag
        subst hcc; rfl
      calc P.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
            Finset.card_le_card_of_injOn _ hmap hinj
        _ = n.choose k := by
            rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    -- |P| = Σ_c C(|agree c|, k) ≥ |S|·C(k+m+1,k)
    have hge : S.card * (k + m + 1).choose k ≤ P.card := by
      rw [hP, Finset.card_sigma]
      calc S.card * (k + m + 1).choose k
          = ∑ _c ∈ S, (k + m + 1).choose k := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ c ∈ S, ((listAgreeSet c w).powersetCard k).card := by
            refine Finset.sum_le_sum (fun c hc => ?_)
            rw [Finset.card_powersetCard]
            refine Nat.choose_le_choose k ?_
            rw [hS, bigAgreeCodewords, Finset.mem_filter] at hc
            exact hc.2.2
    rw [Nat.le_div_iff_mul_le (Nat.choose_pos (by omega))]
    exact le_trans hge hPle
  · intro c _
    rw [listAgreeSet]
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp [Finset.card_univ]

open Classical in
/-- **Unconditional supply, every band.**  Composing the subset-counting discharge
with `explainableCoreSupply_of_listBound`: for *every* band radius the deep-band
supply holds with `B = (C(n,k)/C(k+m+1,k))·C(n,k+m+1)` — exponential at constant rate,
but with no hypothesis at all. -/
theorem explainableCoreSupply_unconditional (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k) :
    ExplainableCoreSupply dom k m
      ((n.choose k / (k + m + 1).choose k) * (n.choose (k + m + 1))) :=
  explainableCoreSupply_of_listBound dom (subJohnsonListBound_unconditional dom hk)

open Classical in
/-- **Above-Johnson composition into the multiplicity reduction (STRUCTURAL, vacuous
as a failure count).**  Composing `deep_band_badSet_card_of_supply` with the
discharged above-Johnson supply gives the no-open-hypothesis inequality
`C(n,k+m+1) ≤ #badSet · q^m · B` with `B = (n²/((k+m+1)²−n(k−1)))·C(n,k+m+1)`.

⚠ **Honesty caveat (do not read this as production failure).**  The chain yields a
*non-vacuous* bad-scalar count only when `B < C(n,k+m+1)/q^m`.  The above-Johnson `B`
here is `≥ C(n,k+m+1)`, so the resulting bound is `#badSet ≥ C(n,k+m+1)/(q^m·B) < 1`,
i.e. `#badSet ≥ 0` — **trivially true, not a failure witness** (verified
integer-exactly at `k=2,m=2,n=16,q=17`: `badSet ≥ 0.0001`).  Production failure needs
a supply `B ≪ C(n,k+m+1)/q^m`, far below the witness mass; the deep-band lower bound
`not_explainableCoreSupply_exponential` shows the supply is *exponentially large* for
`μ_n`, so no such `B` exists at the deep-band radius.  This theorem is therefore a
*type-correct structural composition*, retained for honesty about exactly what the
supply route does and does not deliver — not a non-vacuous deep-band failure. -/
theorem deep_band_badSet_aboveJohnson (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (hJohnson : n * (k - 1) < (k + m + 1) ^ 2) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1)
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (Fintype.card F) ^ m
          * ((n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1))) * (n.choose (k + m + 1))) :=
  deep_band_badSet_card_of_supply dom hk hhi
    (explainableCoreSupply_aboveJohnson dom hk hJohnson)

/-- **Non-vacuity, concrete parameters.**  At `k = 2, m = 2, n = 16` the band
threshold `k+m+1 = 5` sits above the Johnson radius (`16·1 = 16 < 25 = 5²`), so the
deep-band supply is fully proven for *any* domain with the concrete bound
`B = (16²/(5²−16))·C(16,5) = 28·4368 = 122304`. -/
theorem explainableCoreSupply_concrete_k2m2n16 (dom : Fin 16 ↪ F) :
    ExplainableCoreSupply dom 2 2 122304 := by
  have h := explainableCoreSupply_aboveJohnson (k := 2) (m := 2) dom
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_pairwise_agree_le
#print axioms ProximityGap.Ownership.subJohnsonListBound_aboveJohnson
#print axioms ProximityGap.Ownership.explainableCoreSupply_aboveJohnson
#print axioms ProximityGap.Ownership.subJohnsonListBound_unconditional
#print axioms ProximityGap.Ownership.explainableCoreSupply_unconditional
#print axioms ProximityGap.Ownership.deep_band_badSet_aboveJohnson
#print axioms ProximityGap.Ownership.explainableCoreSupply_concrete_k2m2n16
