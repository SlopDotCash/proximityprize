/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiber
import ArkLib.Data.CodingTheory.ProximityGap.CorePartitionLemma

/-!
# The explicit CODEWORD list-size lower bound for smooth dyadic Reed–Solomon (#389)

`EsymmFiber.lean` proves the *supply* lower bound `rootsOfUnity_dyadic_supply`: the degree-`t`
power word has `≥ C(n/d, t/d)` explainable `(k+m+1)`-cores on the roots-of-unity domain `μ_n`.
This file upgrades that core count to the actual **codeword list** — the count of distinct
Reed–Solomon codewords agreeing with the word on `≥ t` points — which is the headline
sub-Johnson list-size quantity.

* `agree_card_le` — a degree-`<k` RS codeword agrees with a degree-`t=k+m+1` polynomial word on
  `≤ t` points (root-count cap: `P − W` has degree exactly `t`).
* `rootsOfUnity_dyadic_codeword_list_ge` — hence the agreement-`t` codeword list is `≥ C(n/d, t/d)`,
  via the injection `core ↦ its explainer` (injective because each codeword agrees on `≤ t` points,
  so explains `≤ 1` core; a size-`t` core forced into a `≤ t` agreement set equals it).

For `n = 2^μ`, constant rate, constant `m`, this is `2^{Θ(n)}`: explicit smooth (FFT) Reed–Solomon
codes have **exponential** sub-Johnson list size — the multiplicative-subgroup analogue of the
Ben-Sasson–Kopparty–Radhakrishnan subspace-polynomial limit.  Axiom-clean.
-/

open Finset Polynomial

namespace ProximityGap.EsymmFiber

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] [NeZero n] in
/-- A degree-`<k` RS codeword agrees with a degree-`t=k+m+1` polynomial word on `≤ t` points
(root-count cap: `P − W` has degree exactly `t`, so `≤ t` roots, and the domain is injective). -/
theorem agree_card_le (dom : Fin n ↪ F) {k m : ℕ} (W : Polynomial F)
    (hWdeg : W.degree = ((k + m + 1 : ℕ) : WithBot ℕ))
    {c : Fin n → F} (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (Finset.univ.filter (fun i => c i = W.eval (dom i))).card ≤ k + m + 1 := by
  classical
  obtain ⟨P, hPdeg, hcP⟩ := hc
  set t := k + m + 1 with ht
  have hPlt : P.degree < (t : WithBot ℕ) :=
    lt_of_lt_of_le hPdeg (by exact_mod_cast (by omega : k ≤ t))
  have hPWdeg : (P - W).degree = (t : WithBot ℕ) := by
    rw [sub_eq_add_neg, Polynomial.degree_add_eq_right_of_degree_lt
      (by rw [Polynomial.degree_neg, hWdeg]; exact hPlt), Polynomial.degree_neg, hWdeg]
  have hPWne : P - W ≠ 0 := by
    intro h; rw [h, Polynomial.degree_zero] at hPWdeg; exact absurd hPWdeg (by simp)
  have hPWnat : (P - W).natDegree = t := natDegree_eq_of_degree_eq_some hPWdeg
  have hsub : (Finset.univ.filter (fun i => c i = W.eval (dom i))).image dom
      ⊆ (P - W).roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter] at hx
    obtain ⟨i, ⟨-, hi⟩, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPWne, Polynomial.IsRoot.def,
      Polynomial.eval_sub, sub_eq_zero, ← hi]
    exact (congrFun hcP i).symm
  calc (Finset.univ.filter (fun i => c i = W.eval (dom i))).card
      = ((Finset.univ.filter (fun i => c i = W.eval (dom i))).image dom).card :=
        (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ (P - W).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (P - W).roots := Multiset.toFinset_card_le _
    _ ≤ (P - W).natDegree := Polynomial.card_roots' _
    _ = t := hPWnat

open scoped Classical in
/-- **Exact list quotient for degree-`t` polynomial words (the exact sub-Johnson list-size
solution).**  Since no degree-`<k` codeword agrees with `eval W` on more than `t = k+m+1` points,
the agreement-`t` Reed–Solomon list is in **exact bijection** with the forced-polynomial degree
fiber on `t`-subsets — `c ↦ its agreement set`.  Hence the list size is *exactly* the number of
`t`-cores whose forced explainer has degree `< k`. -/
theorem degree_t_list_eq_forcedPoly_degree (dom : Fin n ↪ F) {k m : ℕ} (W : Polynomial F)
    (hWdeg : W.degree = ((k + m + 1 : ℕ) : WithBot ℕ)) :
    ((Finset.univ : Finset (Fin n → F)).filter (fun c =>
        c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ k + m + 1 ≤ (Finset.univ.filter (fun i => c i = W.eval (dom i))).card)).card
      =
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => (forcedPoly dom k m W T).degree < (k : WithBot ℕ))).card := by
  classical
  refine Finset.card_bij
    (fun c _ => Finset.univ.filter (fun i => c i = W.eval (dom i))) ?_ ?_ ?_
  · intro c hc
    obtain ⟨-, hcmem, hge⟩ := Finset.mem_filter.mp hc
    have hle : (Finset.univ.filter (fun i => c i = W.eval (dom i))).card ≤ k + m + 1 :=
      agree_card_le dom W hWdeg hcmem
    have hcard : (Finset.univ.filter (fun i => c i = W.eval (dom i))).card = k + m + 1 :=
      le_antisymm hle hge
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    exact (explainable_iff_forcedPoly_degree dom W hWdeg hcard).mp
      ⟨c, hcmem, fun i hi => (Finset.mem_filter.mp hi).2⟩
  · intro c hc c' hc' heq
    obtain ⟨-, hcmem, hge⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hc'mem, -⟩ := Finset.mem_filter.mp hc'
    refine ProximityGap.PairRank.explainable_core_explainer_unique (k := k) dom
      (le_trans (by omega : k ≤ k + m + 1) hge) hcmem hc'mem
      (fun i hi => (Finset.mem_filter.mp hi).2) ?_
    intro i hi
    have heq2 : Finset.univ.filter (fun i => c i = W.eval (dom i))
        = Finset.univ.filter (fun i => c' i = W.eval (dom i)) := heq
    rw [heq2] at hi
    exact (Finset.mem_filter.mp hi).2
  · intro T hT
    obtain ⟨hTp, hdeg⟩ := Finset.mem_filter.mp hT
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTp
    obtain ⟨c, hcmem, hagree⟩ :=
      (explainable_iff_forcedPoly_degree dom W hWdeg hTcard).mpr hdeg
    have hTsub : T ⊆ Finset.univ.filter (fun i => c i = W.eval (dom i)) :=
      fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree i hi⟩
    have hge : k + m + 1 ≤ (Finset.univ.filter (fun i => c i = W.eval (dom i))).card := by
      calc k + m + 1 = T.card := hTcard.symm
        _ ≤ _ := Finset.card_le_card hTsub
    refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcmem, hge⟩, ?_⟩
    have hle : (Finset.univ.filter (fun i => c i = W.eval (dom i))).card ≤ k + m + 1 :=
      agree_card_le dom W hWdeg hcmem
    exact (Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard]; exact hle)).symm

open scoped Classical in
open Polynomial in
/-- **Explicit exponential CODEWORD list-size lower bound for `μ_n` (#389).**  The agreement-`t`
Reed–Solomon list — the count of distinct codewords of `rsCode (μ_n) k` agreeing with the
degree-`t = k+m+1` power word on `≥ t` points — is `≥ C(n/d, t/d)`.  Upgrades the core-supply
`rootsOfUnity_dyadic_supply` to the actual codeword list via the injection `core ↦ explainer`
(injective by `agree_card_le`: a codeword agrees on `≤ t` points, so explains `≤ 1` core).  For
`n = 2^μ`, constant rate and constant `m`, this is `2^{Θ(n)}` — the sub-Johnson list size is
exponential on explicit smooth (FFT) Reed–Solomon domains. -/
theorem rootsOfUnity_dyadic_codeword_list_ge {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d r : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hnr : n = d * r)
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F) (hlow : lowPart.degree < (k : WithBot ℕ))
    {s : ℕ} (hsd : s * d = k + m + 1) :
    r.choose s ≤
      ((Finset.univ : Finset (Fin n → F)).filter (fun c =>
        c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F))
          ∧ k + m + 1 ≤ (Finset.univ.filter (fun i =>
              c i = (C wt * X ^ (k + m + 1) + lowPart).eval (domRU hζ i))).card)).card := by
  classical
  set t := k + m + 1 with ht
  set W : Polynomial F := C wt * X ^ t + lowPart with hWdef
  have hCXt : (C wt * X ^ t).degree = (t : WithBot ℕ) := degree_C_mul_X_pow t hwt
  have hlowlt : lowPart.degree < (t : WithBot ℕ) :=
    lt_of_lt_of_le hlow (by exact_mod_cast (show k ≤ t by omega))
  have hWdeg : W.degree = (t : WithBot ℕ) := by
    rw [hWdef, degree_add_eq_left_of_degree_lt (by rw [hCXt]; exact hlowlt), hCXt]
  refine le_trans (rootsOfUnity_dyadic_supply hζ hk hd hnr wt hwt lowPart hlow hsd) ?_
  set Score := ((Finset.univ : Finset (Fin n)).powersetCard t).filter
    (fun T => ∃ c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F)),
      ∀ i ∈ T, c i = W.eval (domRU hζ i)) with hScore
  have hkey : ∀ T ∈ Score, ∃ c, c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F))
      ∧ ∀ i ∈ T, c i = W.eval (domRU hζ i) := by
    intro T hT
    obtain ⟨c, hcmem, hcag⟩ := (Finset.mem_filter.mp hT).2
    exact ⟨c, hcmem, hcag⟩
  choose! g hgmem hgag using hkey
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro T hT
    have hTcard : T.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    have hsub : T ⊆ Finset.univ.filter (fun i => g T i = W.eval (domRU hζ i)) :=
      fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgag T hT i hi⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgmem T hT, ?_⟩
    calc t = T.card := hTcard.symm
      _ ≤ _ := Finset.card_le_card hsub
  · intro T hT T' hT' heq
    have hTmem : T ∈ Score := Finset.mem_coe.mp hT
    have hT'mem : T' ∈ Score := Finset.mem_coe.mp hT'
    have hTcard : T.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hTmem).1).2
    have hT'card : T'.card = t := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT'mem).1).2
    have hcap : (Finset.univ.filter (fun i => g T i = W.eval (domRU hζ i))).card ≤ t :=
      agree_card_le (domRU hζ) W hWdeg (hgmem T hTmem)
    have hTsub : T ⊆ Finset.univ.filter (fun i => g T i = W.eval (domRU hζ i)) :=
      fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgag T hTmem i hi⟩
    have hT'sub : T' ⊆ Finset.univ.filter (fun i => g T i = W.eval (domRU hζ i)) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [heq]; exact hgag T' hT'mem i hi
    have hTeq : T = Finset.univ.filter (fun i => g T i = W.eval (domRU hζ i)) :=
      Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard]; exact hcap)
    have hT'eq : T' = Finset.univ.filter (fun i => g T i = W.eval (domRU hζ i)) :=
      Finset.eq_of_subset_of_card_le hT'sub (by rw [hT'card]; exact hcap)
    rw [hTeq, hT'eq]

end ProximityGap.EsymmFiber
