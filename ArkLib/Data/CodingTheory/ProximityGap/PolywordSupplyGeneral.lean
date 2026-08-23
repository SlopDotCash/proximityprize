/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListBound
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# Any single-polynomial word has polynomial supply — at ANY degree (#389)

`MonomialSupplyChoose` handled degree-exactly-`(k+m+1)` words.  This file removes the degree
restriction: a word `w = eval W` for **any** polynomial `W` with `k ≤ deg W ≤ d` has
explainable-core count

> `polyword_supply_le` — `#cores · C(k+m+1, k) ≤ C(n, k) · C(d, k+m+1)`, **unconditional**.

Two elementary inputs, no GV/Stepanov/Mann:
* **Root bound** (`agreeSet_card_le_of_polyDeg`): every codeword `c = eval P` (deg `< k`)
  agrees with `w` on `≤ d` points — the agreement set injects into the `≤ d` roots of
  `P − W` (degree `≤ d`, nonzero since `deg W ≥ k > deg P`).
* **Deza–Frankl** (`rsCode_subJohnson_list_card_le`): at most `C(n,k)/C(t,k)` codewords reach
  agreement `≥ t`.

Each explainable core lies in the agreement-`t`-subsets of its (unique) explainer, so
`#cores ≤ ∑_{c : a_c ≥ t} C(a_c, t) ≤ (#list)·C(d, t)`.

**Why this matters (#389 deep band):** the deep-band bad-scalar words
`w_γ = eval(Q₀ + γ·X^k)` (`deg ≤ 2k+m+1`) are *single polynomials*, so this bounds the fiber
of every `γ` unconditionally — the `∀w` `ExplainableCoreSupply` hypothesis is replaced, for
the words that actually appear, by an elementary theorem.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- **The root bound**: a codeword agrees with a single-polynomial word `w = eval W` of
degree `≤ d` (and `≥ k`, so `w` is not itself a codeword) on at most `d` points. -/
theorem agreeSet_card_le_of_polyDeg (dom : Fin n ↪ F) {k d : ℕ} (hk : 1 ≤ k) (W : Polynomial F)
    (hkW : k ≤ W.natDegree) (hd : W.natDegree ≤ d)
    {c : Fin n → F} (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (agreeSet c (fun i => W.eval (dom i))).card ≤ d := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  have hPnat : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0; simp only [natDegree_zero]; omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  have hne : P - W ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hPnat; omega
  have hdegle : (P - W).natDegree ≤ d := by
    refine le_trans (Polynomial.natDegree_sub_le P W) ?_
    rw [Nat.max_le]
    exact ⟨by omega, hd⟩
  have hsub : (agreeSet (fun i => P.eval (dom i)) (fun i => W.eval (dom i))).image dom
      ⊆ (P - W).roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [agreeSet, Finset.mem_filter] at hi
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def,
      eval_sub, sub_eq_zero]
    exact hi.2
  calc (agreeSet (fun i => P.eval (dom i)) (fun i => W.eval (dom i))).card
      = ((agreeSet (fun i => P.eval (dom i)) (fun i => W.eval (dom i))).image dom).card :=
        (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ (P - W).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (P - W).roots := Multiset.toFinset_card_le _
    _ ≤ (P - W).natDegree := Polynomial.card_roots' _
    _ ≤ d := hdegle

open Classical in
omit [NeZero n] in
/-- **The general single-polynomial supply bound**: for `w = eval W` with `k ≤ deg W ≤ d`,
`#cores · C(k+m+1, k) ≤ C(n, k) · C(d, k+m+1)`, unconditional, any domain. -/
theorem polyword_supply_le (dom : Fin n ↪ F) {k m d : ℕ} (hk : 1 ≤ k) (W : Polynomial F)
    (hkW : k ≤ W.natDegree) (hd : W.natDegree ≤ d) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k (fun i => W.eval (dom i)) T)).card
      * (k + m + 1).choose k
      ≤ n.choose k * d.choose (k + m + 1) := by
  set w : Fin n → F := fun i => W.eval (dom i) with hw
  set t := k + m + 1 with ht
  set L := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧ t ≤ (agreeSet c w).card) with hL
  set cores := ((Finset.univ : Finset (Fin n)).powersetCard t).filter
    (fun T => ExplainableOn dom k w T) with hcores
  -- each core is a `t`-subset of its explainer's agreement set
  have hsubset : cores ⊆ L.biUnion (fun c => (agreeSet c w).powersetCard t) := by
    intro T hT
    rw [hcores, Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨-, hTcard⟩, c, hc, hagree⟩ := hT
    have hTsub : T ⊆ agreeSet c w := by
      intro i hi; rw [agreeSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hagree i hi⟩
    have hcL : c ∈ L := by
      rw [hL, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hc, hTcard ▸ Finset.card_le_card hTsub⟩
    rw [Finset.mem_biUnion]
    exact ⟨c, hcL, Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩⟩
  -- bound the core count by `∑_{c∈L} C(a_c, t) ≤ #L · C(d, t)`
  have hcoreBound : cores.card ≤ L.card * d.choose t := by
    calc cores.card
        ≤ (L.biUnion (fun c => (agreeSet c w).powersetCard t)).card :=
          Finset.card_le_card hsubset
      _ ≤ ∑ c ∈ L, ((agreeSet c w).powersetCard t).card := Finset.card_biUnion_le
      _ = ∑ c ∈ L, (agreeSet c w).card.choose t := by
          refine Finset.sum_congr rfl (fun c _ => ?_); rw [Finset.card_powersetCard]
      _ ≤ ∑ _c ∈ L, d.choose t := by
          refine Finset.sum_le_sum (fun c hc => ?_)
          have hcmem := (Finset.mem_filter.mp hc).2.1
          exact Nat.choose_le_choose t (agreeSet_card_le_of_polyDeg dom hk W hkW hd hcmem)
      _ = L.card * d.choose t := by rw [Finset.sum_const, smul_eq_mul]
  -- Deza–Frankl: `#L · C(t, k) ≤ C(n, k)`
  have hDF : L.card * t.choose k ≤ n.choose k := rsCode_subJohnson_list_card_le dom hk w
  -- combine
  calc cores.card * t.choose k
      ≤ (L.card * d.choose t) * t.choose k := Nat.mul_le_mul_right _ hcoreBound
    _ = (L.card * t.choose k) * d.choose t := by ring
    _ ≤ n.choose k * d.choose t := Nat.mul_le_mul_right _ hDF

end ProximityGap.Ownership
