/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandFailureUnconditional
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound

/-!
# The Johnson split (#389, route 1): the supply, closed above the Johnson
agreement line

The sub-Johnson supply wall asks: bound the number of explainable
`(k+m+1)`-cores of a word.  This file splits the question along the **Johnson
agreement line** `(k+m+1)² = n(k−1)` and closes the upper side:

* `rsCode_pairwise_agreeSet_card_le` — distinct codewords agree pairwise on
  `≤ k − 1` points (root counting).
* `rsCode_agreement_list_card_le` — **the list-size half of the supply**: for
  ANY word `w`, the codewords with agreement `≥ a` number at most
  `n²/(a² − n(k−1))` whenever `n(k−1) < a²` — the in-tree Johnson
  second-moment bound (`ArkLib.JohnsonList.johnson_list_bound_div`)
  instantiated at the RS pairwise-agreement parameter `b = k − 1`.
* `explainable_cores_card_le_list_mul` — the conversion: explainable cores
  inject into (codeword in the agreement-`(k+m+1)` list) × ((k+m+1)-subset of
  its agreement set); under an agreement cap `A` this costs `C(A, k+m+1)` per
  listed codeword.
* `explainableCoreSupply_pinned` — the honesty brick: the UNCAPPED uniform
  supply `ExplainableCoreSupply` is pinned at exactly `C(n,k+m+1)` (the zero
  word attains it), so the right open object is the agreement-CAPPED supply:
* `SubJohnsonSupplyResidual` — the named residual, in its capped per-word
  form: every word whose codeword agreements are all `≤ 2k+m+1` (the cap that
  is AUTOMATIC for every word the deep-band engine generates) has at most `B`
  explainable `(k+m+1)`-cores.  Status:
  - `subJohnsonSupplyResidual_pairCount` — holds with `B = C(n,k)`
    unconditionally (the pair-counting route, as in the unconditional
    deep-band failure);
  - `subJohnsonSupplyResidual_above_johnson` — **above the Johnson line**
    (`n(k−1) < (k+m+1)²`) it holds with
    `B = (n²/((k+m+1)² − n(k−1))) · C(2k+m+1, k+m+1)` — polynomial list
    factor times a binomial in the BAND parameters only (no `C(n,·)`);
  - below the line, a subexponential `B` is the recognized open list-decoding
    wall (`DISPROOF_LOG.md`, 2026-06-12 entry).
* `deep_band_witness_mass_offcode` — the witness-mass law with the generating
  stack certified OFF-code at every shear (`Q₀ + γXᵏ` is never a code
  polynomial), at the cost of a factor `2`.
* `deep_band_badSet_card_of_residual` — **the reduction**: any `B` feeding
  `SubJohnsonSupplyResidual` converts the witness mass into a bad-scalar
  count, `C(n,k+m+1) ≤ 2·#badSet·qᵐ·B`.
* `deep_band_failure_above_johnson` — **the capstone**: above the Johnson
  line, unconditionally,

    `C(n,k+m+1) ≤ 2 · #badSet · qᵐ · (n²/((k+m+1)² − n(k−1))) · C(2k+m+1, k+m+1)`.

* `johnson_gap_of_sqrt_le` / `deep_band_failure_above_johnson_of_sqrt` — the
  split point made literal: the gap holds exactly for the bands
  `m ≥ √(n(k−1)) − k`, i.e. `m* = Nat.sqrt (n(k−1)) − k` is the band where
  the deep-band programme's supply side closes.

Honesty note: versus the unconditional `C(n,k)` fiber, the Johnson fiber
`n²/((k+m+1)²−n(k−1)) · C(2k+m+1, k+m+1)` is an exponential sharpening in the
low-degree regimes `k = n^α`, `α < 1` (e.g. `k = n^{1/3}`: `C(2k+m+1,k)`
versus `C(n,k)` is a factor `exp(Θ(n^{1/3} log n))`) for bands just above the
line `m ≈ √(nk)`; at high rate `k = Θ(n)` the two are comparable and the
production wall (`C(n,k+m+1)/C(n,k)` versus `qᵐ`) is unchanged.  The residual
below the line is precisely the classical sub-Johnson RS list-size question.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] [NeZero n] in
open Classical in
/-- **RS pairwise agreement**: two distinct codewords of `rsCode dom k` agree
on at most `k − 1` points (their difference is a nonzero polynomial of degree
`≤ k − 1`). -/
theorem rsCode_pairwise_agreeSet_card_le (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {c c' : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hne : c ≠ c') :
    (agreeSet c c').card ≤ k - 1 := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  obtain ⟨P', hP'deg, rfl⟩ := hc'
  have hD0 : P - P' ≠ 0 := by
    intro h
    refine hne ?_
    have hPP : P = P' := sub_eq_zero.mp h
    rw [hPP]
  have hDdeg : (P - P').natDegree ≤ k - 1 := by
    have h1 : (P - P').degree < (k : ℕ) :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hPdeg hP'deg)
    have h2 : (P - P').natDegree < k :=
      (Polynomial.natDegree_lt_iff_degree_lt hD0).mpr h1
    omega
  have hsub : (agreeSet (fun i => P.eval (dom i))
        (fun i => P'.eval (dom i))).card
      ≤ (P - P').roots.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun i => dom i) ?_ ?_
    · intro i hi
      have hi' := Finset.mem_coe.mp hi
      rw [agreeSet, Finset.mem_filter] at hi'
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hD0]
      show (P - P').eval (dom i) = 0
      rw [eval_sub, sub_eq_zero]
      exact hi'.2
    · exact fun i _ j _ h => dom.injective h
  calc (agreeSet (fun i => P.eval (dom i))
        (fun i => P'.eval (dom i))).card
      ≤ (P - P').roots.toFinset.card := hsub
    _ ≤ Multiset.card (P - P').roots := Multiset.toFinset_card_le _
    _ ≤ (P - P').natDegree := Polynomial.card_roots' _
    _ ≤ k - 1 := hDdeg

omit [NeZero n] in
open Classical in
/-- **The Johnson list bound for `rsCode`** — the list-size half of the #389
supply statement, closed above the Johnson agreement line: for ANY word `w`,
the codewords with agreement `≥ a` number at most `n²/(a² − n(k−1))` whenever
`n(k−1) < a²`. -/
theorem rsCode_agreement_list_card_le (dom : Fin n ↪ F) {k a : ℕ}
    (hk : 1 ≤ k) (w : Fin n → F)
    (hgap : n * (k - 1) < a ^ 2) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ a ≤ (agreeSet c w).card)).card
      ≤ n ^ 2 / (a ^ 2 - n * (k - 1)) := by
  have h := ArkLib.JohnsonList.johnson_list_bound_div (ι := Fin n) (F := F)
    w ((Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ a ≤ (agreeSet c w).card))
    a (k - 1) ?_ ?_ ?_
  · simpa [Fintype.card_fin] using h
  · intro c hc
    have h2 := (Finset.mem_filter.mp hc).2.2
    rwa [agreeSet] at h2
  · intro c hc c' hc' hne
    have h2 := rsCode_pairwise_agreeSet_card_le dom hk
      (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc').2.1 hne
    rwa [agreeSet] at h2
  · rwa [Fintype.card_fin]

omit [NeZero n] in
open Classical in
/-- **The list-to-cores conversion**: under an agreement cap `A`, the
explainable `(k+m+1)`-cores of `w` inject into pairs (codeword of the
agreement-`(k+m+1)` list, `(k+m+1)`-subset of its agreement set) — at most
`#list · C(A, k+m+1)` cores. -/
theorem explainable_cores_card_le_list_mul (dom : Fin n ↪ F) (k m : ℕ)
    {w : Fin n → F} {A : ℕ}
    (hA : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ A) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k w T)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
            ∧ k + m + 1 ≤ (agreeSet c w).card)).card
        * A.choose (k + m + 1) := by
  set expl := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
    (fun T => ExplainableOn dom k w T) with hexpl
  set L := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ k + m + 1 ≤ (agreeSet c w).card) with hL
  -- the explainer-choice map
  set pick : Finset (Fin n) → (Fin n → F) := fun T =>
    if h : ExplainableOn dom k w T then h.choose else w with hpick
  have hpickspec : ∀ T, ExplainableOn dom k w T →
      pick T ∈ (rsCode dom k : Submodule F (Fin n → F))
        ∧ ∀ i ∈ T, pick T i = w i := by
    intro T hT
    rw [hpick]
    simp only [dif_pos hT]
    exact hT.choose_spec
  -- inject explainable cores into the sigma of agreement subsets
  have hinj : expl.card
      ≤ (L.sigma (fun c => (agreeSet c w).powersetCard (k + m + 1))).card := by
    refine Finset.card_le_card_of_injOn
      (fun T => ⟨pick T, T⟩) ?_ ?_
    · intro T hT
      obtain ⟨hTmem, hTexpl⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hT)
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
      obtain ⟨hpC, hpag⟩ := hpickspec T hTexpl
      have hTag : T ⊆ agreeSet (pick T) w := by
        intro i hi
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hpag i hi⟩
      rw [Finset.mem_coe, Finset.mem_sigma]
      constructor
      · rw [hL, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hpC, ?_⟩
        calc k + m + 1 = T.card := hTcard.symm
          _ ≤ (agreeSet (pick T) w).card := Finset.card_le_card hTag
      · exact Finset.mem_powersetCard.mpr ⟨hTag, hTcard⟩
    · intro T _ T' _ heq2
      exact congrArg Sigma.snd heq2
  -- count the sigma fiberwise against the cap
  calc expl.card
      ≤ (L.sigma (fun c => (agreeSet c w).powersetCard (k + m + 1))).card :=
        hinj
    _ = ∑ c ∈ L, ((agreeSet c w).powersetCard (k + m + 1)).card :=
        Finset.card_sigma _ _
    _ ≤ ∑ c ∈ L, A.choose (k + m + 1) := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [Finset.card_powersetCard]
        refine Nat.choose_le_choose _ ?_
        exact hA c (Finset.mem_filter.mp hc).2.1
    _ = L.card * A.choose (k + m + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

omit [NeZero n] in
open Classical in
/-- **The capped Johnson supply**: above the Johnson agreement line, a word
with codeword-agreement cap `A` has at most
`(n²/((k+m+1)² − n(k−1))) · C(A, k+m+1)` explainable `(k+m+1)`-cores. -/
theorem explainable_cores_card_le_johnson (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {w : Fin n → F} {A : ℕ}
    (hA : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ A)
    (hgap : n * (k - 1) < (k + m + 1) ^ 2) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k w T)).card
      ≤ (n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1))) * A.choose (k + m + 1) :=
  le_trans (explainable_cores_card_le_list_mul dom k m hA)
    (Nat.mul_le_mul_right _ (rsCode_agreement_list_card_le dom hk w hgap))

omit [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- **The uncapped uniform supply is pinned**: any `B` satisfying
`ExplainableCoreSupply` must be at least `C(n,k+m+1)` — the zero word (a
codeword) has EVERY `(k+m+1)`-core explainable.  Together with
`explainableCoreSupply_trivial`, the optimal uniform `B` is exactly
`C(n,k+m+1)`; a useful supply must be agreement-capped
(`SubJohnsonSupplyResidual`). -/
theorem explainableCoreSupply_pinned (dom : Fin n ↪ F) (k m : ℕ) {B : ℕ}
    (hB : ExplainableCoreSupply dom k m B) :
    n.choose (k + m + 1) ≤ B := by
  have h := hB 0
  rw [Finset.filter_true_of_mem
      (fun T _ => ⟨0, Submodule.zero_mem _, fun i _ => rfl⟩),
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h
  exact h

open Classical in
/-- **THE NAMED RESIDUAL (#389)**: the agreement-capped per-word supply.
Every word whose codeword agreements are all `≤ 2k+m+1` — the cap automatic
for the words the deep-band engine generates — has at most `B` explainable
`(k+m+1)`-cores.  Proven with `B = C(n,k)` unconditionally
(`subJohnsonSupplyResidual_pairCount`) and with the polynomial-list Johnson
form above the Johnson line (`subJohnsonSupplyResidual_above_johnson`); a
subexponential `B` below the line is the open sub-Johnson list-size wall. -/
def SubJohnsonSupplyResidual (dom : Fin n ↪ F) (k m B : ℕ) : Prop :=
  ∀ w : Fin n → F,
    (∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ 2 * k + m + 1) →
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
      (fun T => ExplainableOn dom k w T)).card ≤ B

open Classical in
/-- The pair-counting discharge: the residual holds unconditionally with
`B = C(n,k)` (the route of the unconditional deep-band failure). -/
theorem subJohnsonSupplyResidual_pairCount (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) :
    SubJohnsonSupplyResidual dom k m (n.choose k) := by
  intro w hA
  have hsupply := explainable_cores_card_of_agreement_le dom (m := m) hk hA
  have hMk : 2 * k + m + 1 - k = k + m + 1 := by omega
  rw [hMk] at hsupply
  have hsymm : (k + m + 1).choose (m + 1) = (k + m + 1).choose k := by
    have h := Nat.choose_symm (n := k + m + 1) (k := k) (by omega)
    rw [show k + m + 1 - k = m + 1 from by omega] at h
    exact h
  rw [hsymm] at hsupply
  have hchoosepos : 0 < (k + m + 1).choose k := Nat.choose_pos (by omega)
  exact Nat.le_of_mul_le_mul_right hsupply hchoosepos

omit [NeZero n] in
open Classical in
/-- **The above-Johnson discharge**: above the Johnson agreement line
`n(k−1) < (k+m+1)²`, the residual holds with the polynomial-list form
`B = (n²/((k+m+1)² − n(k−1))) · C(2k+m+1, k+m+1)` — no `C(n,·)` factor. -/
theorem subJohnsonSupplyResidual_above_johnson (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) (hgap : n * (k - 1) < (k + m + 1) ^ 2) :
    SubJohnsonSupplyResidual dom k m
      ((n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1)))
        * (2 * k + m + 1).choose (k + m + 1)) :=
  fun _ hA => explainable_cores_card_le_johnson dom hk hA hgap

omit [NeZero n] in
open Classical in
/-- **The off-code witness mass**: at every band, some generating stack `Q₀`
has coherent-core mass `≥ C(n,k+m+1)/(2qᵐ)`, has degree `≤ 2k+m+1`, and is
certified off-code at EVERY shear: `Q₀ + γXᵏ` is never a degree-`<k`
polynomial.  (The factor `2` pays for excising the `q^{k+1}` degenerate
stacks.) -/
theorem deep_band_witness_mass_offcode (dom : Fin n ↪ F) (k m : ℕ) :
    ∃ Q₀ : F[X],
      Q₀.natDegree ≤ 2 * k + m + 1
      ∧ (∀ γ : F, ∀ P : F[X], P.degree < (k : ℕ) → Q₀ + C γ * X ^ k ≠ P)
      ∧ n.choose (k + m + 1)
        ≤ 2 * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T Q₀)).card * (Fintype.card F) ^ m := by
  set q := Fintype.card F with hq
  set M := 2 * k + m + 2 with hM
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set Nm := Pm.card with hNm
  have hNmval : Nm = n.choose (k + m + 1) := by
    rw [hNm, hPm, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos Nm with hNm0 | hNmpos
  · -- empty core geometry: the explicit witness X^(k+1)
    refine ⟨X ^ (k + 1), ?_, ?_, ?_⟩
    · rw [natDegree_X_pow]
      omega
    · intro γ P hPdeg heq2
      have h1 : (X ^ (k + 1) + C γ * X ^ k : F[X]).coeff (k + 1) = 1 := by
        rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_C_mul, coeff_X_pow,
          if_neg (by omega), mul_zero, add_zero]
      have h2 : P.coeff (k + 1) = 0 := by
        refine Polynomial.coeff_eq_zero_of_degree_lt ?_
        exact lt_of_lt_of_le hPdeg (by exact_mod_cast Nat.le_succ k)
      rw [heq2, h2] at h1
      exact zero_ne_one h1
    · rw [← hNmval, hNm0]
      exact Nat.zero_le _
  set Qc : (Fin M → F) → F[X] :=
    fun c => ∑ j : Fin M, C (c j) * X ^ (j : ℕ) with hQc
  -- coefficients of the family polynomial
  have hQccoeff : ∀ (c : Fin M → F) (j : Fin M), (Qc c).coeff (j : ℕ) = c j := by
    intro c j
    rw [hQc, Polynomial.finset_sum_coeff]
    calc ∑ i : Fin M, (C (c i) * X ^ (i : ℕ)).coeff (j : ℕ)
        = ∑ i : Fin M, (if i = j then c i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coeff_C_mul, coeff_X_pow]
          by_cases h : i = j
          · subst h
            simp
          · rw [if_neg (by
              intro hji
              exact h (Fin.ext hji.symm)), if_neg h, mul_zero]
      _ = c j := by
          rw [Finset.sum_ite_eq' Finset.univ j (fun i => c i)]
          simp
  have hQcdeg : ∀ c : Fin M → F, (Qc c).natDegree ≤ M - 1 := by
    intro c
    rw [hQc]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    calc (C (c j) * X ^ (j : ℕ)).natDegree
        ≤ (C (c j)).natDegree + (X ^ (j : ℕ) : F[X]).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ M - 1 := by
          rw [natDegree_C, natDegree_X_pow]
          have := j.2
          omega
  -- the degenerate stacks: all coefficients above k vanish
  set degen : Finset (Fin M → F) := Finset.univ.filter
    (fun c => ∀ j : Fin M, k < (j : ℕ) → c j = 0) with hdegen
  have hdegencard : degen.card ≤ q ^ (k + 1) := by
    have hk1M : k + 1 ≤ M := by rw [hM]; omega
    calc degen.card
        ≤ Fintype.card (Fin (k + 1) → F) := by
          refine Finset.card_le_card_of_injOn
            (fun c => fun i : Fin (k + 1) => c (Fin.castLE hk1M i))
            (fun c _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
          intro a ha b hb hab
          have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
          funext j
          by_cases hj : (j : ℕ) < k + 1
          · have := congrFun hab ⟨(j : ℕ), hj⟩
            simpa [Fin.castLE] using this
          · rw [ha' j (by omega), hb' j (by omega)]
      _ = q ^ (k + 1) := by
          rw [Fintype.card_fun, Fintype.card_fin, hq]
  -- nondegenerate stacks have all their shears off-code
  have hlinecap : ∀ c : Fin M → F, c ∉ degen → ∀ γ : F,
      ∀ P : F[X], P.degree < (k : ℕ) → Qc c + C γ * X ^ k ≠ P := by
    intro c hc γ P hPdeg heq2
    rw [hdegen, Finset.mem_filter] at hc
    push Not at hc
    obtain ⟨j, hjk, hjne⟩ := hc (Finset.mem_univ c)
    have h1 : (Qc c + C γ * X ^ k).coeff (j : ℕ) = c j := by
      rw [coeff_add, hQccoeff, coeff_C_mul, coeff_X_pow,
        if_neg (by omega), mul_zero, add_zero]
    have h2 : P.coeff (j : ℕ) = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt ?_
      exact lt_of_lt_of_le hPdeg (by exact_mod_cast Nat.le_of_lt hjk)
    rw [heq2, h2] at h1
    exact hjne h1.symm
  -- per-core averaging (the multi-kernel bound)
  have hsubQc : ∀ x y : Fin M → F, Qc (x - y) = Qc x - Qc y := by
    intro x y
    rw [hQc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show C (x j - y j) * X ^ (j : ℕ) = _
    rw [C_sub]
    ring
  have hsubI : ∀ (T : Finset (Fin n)) (x y : Fin M → F),
      coreInterp dom T (Qc (x - y))
        = coreInterp dom T (Qc x) - coreInterp dom T (Qc y) := by
    intro T x y
    rw [coreInterp, coreInterp, coreInterp, hsubQc]
    have hvals : (fun i => (Qc x - Qc y).eval (dom i))
        = (fun i => (Qc x).eval (dom i)) - (fun i => (Qc y).eval (dom i)) := by
      funext i
      simp [eval_sub]
    rw [hvals, map_sub]
  have hpercore : ∀ T ∈ Pm,
      q ^ M ≤ (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card * q ^ m := by
    intro T _
    have h := card_multiKernel_ge
      (φ := fun (j : Fin m) (c : Fin M → F) =>
        (coreInterp dom T (Qc c)).coeff (k + 1 + j))
      (fun j x y => by
        show (coreInterp dom T (Qc (x - y))).coeff (k + 1 + (j : ℕ))
            = (coreInterp dom T (Qc x)).coeff (k + 1 + (j : ℕ))
              - (coreInterp dom T (Qc y)).coeff (k + 1 + (j : ℕ))
        rw [hsubI T x y, coeff_sub])
    have hfeq : (Finset.univ.filter
          (fun c : Fin M → F => IsCoherent dom k m T (Qc c)))
        = (Finset.univ.filter (fun c : Fin M → F => ∀ j : Fin m,
            (fun (j : Fin m) (c : Fin M → F) =>
              (coreInterp dom T (Qc c)).coeff (k + 1 + j)) j c = 0)) :=
      Finset.filter_congr fun c _ => Iff.rfl
    rw [hq, hfeq]
    exact h
  have hcohbound : ∀ c : Fin M → F,
      (Pm.filter (fun T => IsCoherent dom k m T (Qc c))).card ≤ Nm := by
    intro c
    rw [hNm]
    exact Finset.card_filter_le _ _
  have hswap : ∑ c : Fin M → F, (Pm.filter
        (fun T => IsCoherent dom k m T (Qc c))).card
      = ∑ T ∈ Pm, (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have htotal : Nm * q ^ M ≤ (∑ c : Fin M → F, (Pm.filter
      (fun T => IsCoherent dom k m T (Qc c))).card) * q ^ m := by
    calc Nm * q ^ M = ∑ T ∈ Pm, q ^ M := by
          rw [Finset.sum_const, smul_eq_mul, hNm]
      _ ≤ ∑ T ∈ Pm, (Finset.univ.filter
            (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card * q ^ m :=
          Finset.sum_le_sum hpercore
      _ = _ := by rw [← Finset.sum_mul, ← hswap]
  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Fintype.one_lt_card
  -- pigeonhole over the nondegenerate stacks
  have hgoodpigeon : ∃ c : Fin M → F, c ∉ degen ∧
      Nm ≤ 2 * (Pm.filter (fun T => IsCoherent dom k m T (Qc c))).card
        * q ^ m := by
    by_contra hall
    push Not at hall
    have hsplit : ∑ c : Fin M → F, (Pm.filter
        (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m)
        < Nm * q ^ M + Nm * q ^ M := by
      have hbound : ∀ c : Fin M → F, (Pm.filter
          (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m)
          ≤ if c ∈ degen then Nm * (2 * q ^ m) else Nm - 1 := by
        intro c
        by_cases hc : c ∈ degen
        · rw [if_pos hc]
          exact Nat.mul_le_mul_right _ (hcohbound c)
        · rw [if_neg hc]
          have h := hall c hc
          have h2 : 2 * (Pm.filter
              (fun T => IsCoherent dom k m T (Qc c))).card * q ^ m
              ≤ Nm - 1 := by omega
          calc (Pm.filter (fun T => IsCoherent dom k m T (Qc c))).card
                * (2 * q ^ m)
              = 2 * (Pm.filter
                (fun T => IsCoherent dom k m T (Qc c))).card * q ^ m := by
                ring
            _ ≤ Nm - 1 := h2
      calc ∑ c : Fin M → F, (Pm.filter
            (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m)
          ≤ ∑ c : Fin M → F, (if c ∈ degen then Nm * (2 * q ^ m)
              else Nm - 1) := Finset.sum_le_sum fun c _ => hbound c
        _ = degen.card * (Nm * (2 * q ^ m))
            + (q ^ M - degen.card) * (Nm - 1) := by
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
              smul_eq_mul, smul_eq_mul]
            have hf1 : (Finset.univ.filter
                (fun c : Fin M → F => c ∈ degen)) = degen := by
              rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
            have hf2 : (Finset.univ.filter
                (fun c : Fin M → F => ¬ c ∈ degen)).card
                = q ^ M - degen.card := by
              have h := Finset.card_filter_add_card_filter_not
                (s := (Finset.univ : Finset (Fin M → F)))
                (fun c => c ∈ degen)
              rw [hf1] at h
              have hcu : (Finset.univ : Finset (Fin M → F)).card = q ^ M := by
                rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hq]
              omega
            rw [hf1, hf2]
        _ < Nm * q ^ M + Nm * q ^ M := by
            have hdc := hdegencard
            have hqM : q ^ (k + 1) * (2 * q ^ m) ≤ q ^ M := by
              have hexp : k + 1 + (m + 1) ≤ M := by rw [hM]; omega
              calc q ^ (k + 1) * (2 * q ^ m)
                  ≤ q ^ (k + 1) * (q * q ^ m) :=
                    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq2)
                _ = q ^ (k + 1 + (m + 1)) := by ring
                _ ≤ q ^ M := Nat.pow_le_pow_right (by omega) hexp
            have h1 : degen.card * (Nm * (2 * q ^ m)) ≤ Nm * q ^ M := by
              calc degen.card * (Nm * (2 * q ^ m))
                  = Nm * (degen.card * (2 * q ^ m)) := by ring
                _ ≤ Nm * (q ^ (k + 1) * (2 * q ^ m)) := by
                    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hdc)
                _ ≤ Nm * q ^ M := Nat.mul_le_mul_left _ hqM
            have h2 : (q ^ M - degen.card) * (Nm - 1) < Nm * q ^ M := by
              have hqMpos : 0 < q ^ M := pow_pos (by omega) M
              calc (q ^ M - degen.card) * (Nm - 1)
                  ≤ q ^ M * (Nm - 1) :=
                    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                _ < q ^ M * Nm := (Nat.mul_lt_mul_left hqMpos).mpr (by omega)
                _ = Nm * q ^ M := by ring
            omega
    have htot2 : Nm * q ^ M + Nm * q ^ M
        ≤ ∑ c : Fin M → F, (Pm.filter
          (fun T => IsCoherent dom k m T (Qc c))).card * (2 * q ^ m) := by
      calc Nm * q ^ M + Nm * q ^ M
          = 2 * (Nm * q ^ M) := by ring
        _ ≤ 2 * ((∑ c : Fin M → F, (Pm.filter
            (fun T => IsCoherent dom k m T (Qc c))).card) * q ^ m) :=
            Nat.mul_le_mul_left _ htotal
        _ = _ := by
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by ring
    exact absurd (lt_of_le_of_lt htot2 hsplit) (lt_irrefl _)
  obtain ⟨c, hcgood, hcmass⟩ := hgoodpigeon
  refine ⟨Qc c, ?_, hlinecap c hcgood, ?_⟩
  · have h := hQcdeg c
    rw [hM] at h
    omega
  · rw [← hNmval]
    exact hcmass

open Classical in
/-- **THE REDUCTION (#389 route 1)**: any `B` discharging the named capped
supply residual converts the off-code witness mass into a bad-scalar count at
every band radius: `C(n,k+m+1) ≤ 2·#badSet·qᵐ·B`. -/
theorem deep_band_badSet_card_of_residual (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {B : ℕ} (hB : SubJohnsonSupplyResidual dom k m B) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1)
        ≤ 2 * (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (Fintype.card F) ^ m * B := by
  obtain ⟨Q₀, hdeg, hoff, hmass⟩ := deep_band_witness_mass_offcode dom k m
  refine ⟨Q₀, ?_⟩
  set q := Fintype.card F with hq
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set coh := Pm.filter (fun T => IsCoherent dom k m T Q₀) with hcoh
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ) with hbad
  set val : Finset (Fin n) → F :=
    fun T => -(coreInterp dom T Q₀).coeff k with hval
  have hmaps : ∀ T ∈ coh, val T ∈ bad := by
    intro T hT
    obtain ⟨hTmem, hTc⟩ := Finset.mem_filter.mp hT
    have hTcard : T.card = k + m + 1 :=
      (Finset.mem_powersetCard.mp hTmem).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mcaEvent_of_coherent dom hk hhi hTcard hTc⟩
  -- the per-scalar fiber is bounded through the capped supply
  have hfiber : ∀ γ, (coh.filter (fun T => val T = γ)).card ≤ B := by
    intro γ
    -- the fiber consists of explainable cores of one off-code line
    have hsub2 : coh.filter (fun T => val T = γ)
        ⊆ Pm.filter (fun T => ExplainableOn dom k
            (fun i => (Q₀ + C γ * X ^ k).eval (dom i)) T) := by
      intro T hT
      obtain ⟨hTcoh, hTval⟩ := Finset.mem_filter.mp hT
      obtain ⟨hTmem, hTc⟩ := Finset.mem_filter.mp hTcoh
      have hTcard : T.card = k + m + 1 :=
        (Finset.mem_powersetCard.mp hTmem).2
      refine Finset.mem_filter.mpr ⟨hTmem, ?_⟩
      have h := coherent_explains_line dom hTcard hTc
      rw [show -(coreInterp dom T Q₀).coeff k = val T from rfl, hTval] at h
      obtain ⟨cw, hcwC, hcwag⟩ := h
      refine ⟨cw, hcwC, fun i hi => ?_⟩
      rw [hcwag i hi]
      simp [eval_add, eval_mul]
    -- the line's agreements are capped at 2k+m+1
    have hagcap : ∀ cw ∈ (rsCode dom k : Submodule F (Fin n → F)),
        (agreeSet cw (fun i => (Q₀ + C γ * X ^ k).eval (dom i))).card
          ≤ 2 * k + m + 1 := by
      refine agreeSet_card_le_of_natDegree_le dom (by omega) ?_ (hoff γ)
      calc (Q₀ + C γ * X ^ k).natDegree
          ≤ max Q₀.natDegree (C γ * X ^ k).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ 2 * k + m + 1 := by
            refine max_le hdeg ?_
            calc (C γ * X ^ k).natDegree
                ≤ (C γ).natDegree + (X ^ k : F[X]).natDegree :=
                  Polynomial.natDegree_mul_le
              _ ≤ 2 * k + m + 1 := by
                  rw [natDegree_C, natDegree_X_pow]
                  omega
    calc (coh.filter (fun T => val T = γ)).card
        ≤ (Pm.filter (fun T => ExplainableOn dom k
            (fun i => (Q₀ + C γ * X ^ k).eval (dom i)) T)).card :=
          Finset.card_le_card hsub2
      _ ≤ B := hB _ hagcap
  -- fiberwise count and assembly
  have hcount : coh.card ≤ bad.card * B := by
    calc coh.card
        = ∑ γ ∈ bad, (coh.filter (fun T => val T = γ)).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ γ ∈ bad, B := Finset.sum_le_sum fun γ _ => hfiber γ
      _ = bad.card * B := by rw [Finset.sum_const, smul_eq_mul]
  calc n.choose (k + m + 1)
      ≤ 2 * coh.card * q ^ m := hmass
    _ ≤ 2 * (bad.card * B) * q ^ m :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcount)
    _ = 2 * bad.card * q ^ m * B := by ring

open Classical in
/-- **THE CAPSTONE (#389 route 1, the Johnson split)**: above the Johnson
agreement line `n(k−1) < (k+m+1)²`, unconditionally at every band radius,
some stack satisfies

  `C(n,k+m+1) ≤ 2 · #badSet · qᵐ · (n²/((k+m+1)² − n(k−1))) · C(2k+m+1, k+m+1)`

— the deep-band bad-scalar count with the polynomial Johnson-list fiber in
place of `C(n,k)`. -/
theorem deep_band_failure_above_johnson (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (hgap : n * (k - 1) < (k + m + 1) ^ 2) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1)
        ≤ 2 * (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (Fintype.card F) ^ m
          * ((n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1)))
              * (2 * k + m + 1).choose (k + m + 1)) :=
  deep_band_badSet_card_of_residual dom hk hhi
    (subJohnsonSupplyResidual_above_johnson dom hk hgap)

omit [NeZero n] in
/-- **The split point**: the Johnson gap holds exactly for the bands
`m ≥ √(n(k−1)) − k`, i.e. from `m* = Nat.sqrt (n(k−1)) − k` upwards. -/
theorem johnson_gap_of_sqrt_le {k m : ℕ}
    (h : Nat.sqrt (n * (k - 1)) ≤ k + m) :
    n * (k - 1) < (k + m + 1) ^ 2 := by
  have h1 : n * (k - 1) < (Nat.sqrt (n * (k - 1)) + 1) ^ 2 :=
    Nat.lt_succ_sqrt' _
  calc n * (k - 1) < (Nat.sqrt (n * (k - 1)) + 1) ^ 2 := h1
    _ ≤ (k + m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2

open Classical in
/-- The capstone in split-point form: the deep-band supply side closes for
every band `m` with `Nat.sqrt (n(k−1)) ≤ k + m` — the band range
`m ≥ m* = √(n(k−1)) − k`. -/
theorem deep_band_failure_above_johnson_of_sqrt (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (hsqrt : Nat.sqrt (n * (k - 1)) ≤ k + m) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1)
        ≤ 2 * (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (Fintype.card F) ^ m
          * ((n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1)))
              * (2 * k + m + 1).choose (k + m + 1)) :=
  deep_band_failure_above_johnson dom hk hhi (johnson_gap_of_sqrt_le hsqrt)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_pairwise_agreeSet_card_le
#print axioms ProximityGap.Ownership.rsCode_agreement_list_card_le
#print axioms ProximityGap.Ownership.explainable_cores_card_le_list_mul
#print axioms ProximityGap.Ownership.explainable_cores_card_le_johnson
#print axioms ProximityGap.Ownership.explainableCoreSupply_pinned
#print axioms ProximityGap.Ownership.subJohnsonSupplyResidual_pairCount
#print axioms ProximityGap.Ownership.subJohnsonSupplyResidual_above_johnson
#print axioms ProximityGap.Ownership.deep_band_witness_mass_offcode
#print axioms ProximityGap.Ownership.deep_band_badSet_card_of_residual
#print axioms ProximityGap.Ownership.deep_band_failure_above_johnson
#print axioms ProximityGap.Ownership.deep_band_failure_above_johnson_of_sqrt
