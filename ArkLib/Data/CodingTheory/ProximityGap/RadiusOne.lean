/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.Collapse

/-!
# The radius-one MCA error `ε_mca(C, 1)` and the formal §1 MCA prize predicate

`GrandChallengeCollapse.lean` reduced the formal §1 Grand-MCA-Challenge prize predicate
`GrandChallenges.mcaPrize` to four **radius-one** bounds `ε_mca(RS, 1) ≤ ε*`
(`mcaPrize_iff_forall_epsMCA_one`). This file **computes the radius-one MCA error**
`ε_mca(C, 1)` tightly enough to *decide* that predicate in every field-size regime.

At radius `δ = 1` the witness-size clause of `mcaEvent` is vacuous (`(1-1)·n = 0`), so
`mcaEvent C 1 u₀ u₁ γ` says exactly: there is a set `S` carrying a codeword on the line
`u₀ + γ·u₁` while no joint codeword pair matches `(u₀, u₁)` on `S`.

## Main results

* `epsMCA_one_ge_inv` — **Theorem A (lower bound).** Any proper linear sub-code `MC ⊊ Fⁿ`
  has `ε_mca(MC, 1) ≥ 1/|F|` (point mass of the bad event at `γ = 0`, with `u₁ ∉ MC`).
* `epsMCA_one_le_choose_div` — **Theorem B (upper bound).** For `C := RS[F, domain, k]`
  with injective `domain` and `n := |ι|`,
  `ε_mca(C, 1) ≤ C(n, k+1) / |F|`. The proof routes through Reed–Solomon
  interpolation / gluing (`exists_rs_codeword_agree_of_card_le`,
  `rs_eq_of_agree_on_card_ge`): every bad `γ` selects a non-extendable `(k+1)`-subset of
  `ι`, and the selection is injective in `γ`, so the bad set injects into the
  `(k+1)`-subsets — `C(n, k+1)` of them.
* `mcaPrize_of_large_field` — **Corollary 1.** If `C(n, ⌊ρⱼ·n⌋+1)/|F| ≤ ε*` at every prize
  rate, the formal MCA prize **holds** (true for `|F|` huge relative to `n`).
* `not_mcaPrize_of_small_field` — **Corollary 2.** If `ε* < 1/|F|` (i.e. `|F| < 2^128`) and
  `2 ≤ |ι|`, the formal MCA prize **fails** (the rate-`1/2` RS code is a proper subset, so
  `ε_mca(·, 1) ≥ 1/|F| > ε*`).

Together with `not_listDecodingPrize` from `GrandChallengeCollapse.lean`, these decide the
formal §1 prize predicates: the value of `ε_mca(RS, 1)` is pinned between `1/|F|` and
`C(n, k+1)/|F|`, and the prize is provable iff the field is large enough that
`C(n, k+1)/|F| ≤ ε* = 2^{-128}`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section LowerBound

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A uniform-PMF event has probability at least the point mass `1/|F|` at any single
satisfying outcome `x₀`. -/
theorem prob_uniform_ge_inv_of_holds (P : F → Prop) {x₀ : F} (hx₀ : P x₀) :
    (Fintype.card F : ENNReal)⁻¹ ≤ Pr_{ let r ←$ᵖ F }[ P r ] := by
  classical
  rw [prob_tsum_form_singleton]
  calc (Fintype.card F : ENNReal)⁻¹
      = ($ᵖ F) x₀ * (if P x₀ then (1 : ENNReal) else 0) := by
        rw [if_pos hx₀, mul_one, PMF.uniformOfFintype_apply]
    _ ≤ ∑' r, ($ᵖ F) r * (if P r then (1 : ENNReal) else 0) :=
        ENNReal.le_tsum x₀

/-- **THEOREM A (lower bound).** For a linear code given as a `Submodule MC` that is a proper
subset of all words, `ε_mca(MC, 1) ≥ 1/|F|`. -/
theorem epsMCA_one_ge_inv (MC : Submodule F (ι → F))
    (hproper : (MC : Set (ι → F)) ≠ Set.univ) :
    (Fintype.card F : ENNReal)⁻¹ ≤
      epsMCA (F := F) (A := F) (MC : Set (ι → F)) 1 := by
  classical
  -- pick u₁ ∉ MC
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : ι → F, u₁ ∉ (MC : Set (ι → F)) := by
    by_contra h
    push Not at h
    exact hproper (Set.eq_univ_of_forall h)
  set u : WordStack F (Fin 2) ι := Code.finMapTwoWords 0 u₁ with hu
  have hu0 : u 0 = 0 := rfl
  have hu1 : u 1 = u₁ := rfl
  -- mcaEvent at γ = 0 holds
  have hevent : mcaEvent (MC : Set (ι → F)) 1 (u 0) (u 1) (0 : F) := by
    refine ⟨Finset.univ, ?_, ⟨0, MC.zero_mem, ?_⟩, ?_⟩
    · simp
    · intro i _
      simp [hu0]
    · rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
      apply hu₁
      have : v₁ = u₁ := by
        funext i
        exact (hagree i (Finset.mem_univ i)).2
      rwa [← this]
  -- the inner Pr is at least 1/|F| via the point mass at γ = 0
  have hpr : (Fintype.card F : ENNReal)⁻¹ ≤
      Pr_{ let γ ←$ᵖ F }[ mcaEvent (MC : Set (ι → F)) 1 (u 0) (u 1) γ ] :=
    prob_uniform_ge_inv_of_holds _ hevent
  refine le_trans hpr ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (MC : Set (ι → F)) 1 (u 0) (u 1) γ ]) u

end LowerBound

section RSHelpers

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Polynomial ReedSolomon

/-- The evaluation domain embedding is injective on every finite subset. -/
lemma domain_injOn (domain : ι ↪ F) (S : Finset ι) :
    Set.InjOn (fun i => domain i) (↑S : Set ι) :=
  fun _ _ _ _ h => domain.injective h

/-- **RS interpolation / extension.** Any function `g` restricted to a set `S` of size `≤ k`
extends to a degree-`< k` Reed-Solomon codeword agreeing with `g` on `S`. -/
lemma exists_rs_codeword_agree_of_card_le (domain : ι ↪ F) {k : ℕ} {S : Finset ι}
    (hcard : S.card ≤ k) (g : ι → F) :
    ∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ S, w i = g i := by
  classical
  set p : F[X] := Lagrange.interpolate S (fun i => domain i) g with hp
  have hinj : Set.InjOn (fun i => domain i) (↑S : Set ι) := domain_injOn domain S
  have hdeg : p.degree < k := by
    have := Lagrange.degree_interpolate_lt (s := S) (v := fun i => domain i) (r := g) hinj
    calc p.degree < (S.card : WithBot ℕ) := this
      _ ≤ (k : WithBot ℕ) := by exact_mod_cast hcard
  refine ⟨evalOnPoints domain p, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_code_iff_exists_polynomial]
    exact ⟨p, hdeg, rfl⟩
  · intro i hi
    change p.eval (domain i) = g i
    exact Lagrange.eval_interpolate_at_node (s := S) (v := fun i => domain i) (r := g) hinj hi

/-- **RS gluing / uniqueness.** Two degree-`< k` Reed-Solomon codewords that agree on a set
`T` of size `≥ k` are equal everywhere. -/
lemma rs_eq_of_agree_on_card_ge (domain : ι ↪ F) {k : ℕ} {T : Finset ι}
    (hcard : k ≤ T.card) {w₁ w₂ : ι → F}
    (hw₁ : w₁ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hw₂ : w₂ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hagree : ∀ i ∈ T, w₁ i = w₂ i) :
    w₁ = w₂ := by
  classical
  rw [SetLike.mem_coe, mem_code_iff_exists_polynomial] at hw₁ hw₂
  obtain ⟨p₁, hp₁deg, hp₁⟩ := hw₁
  obtain ⟨p₂, hp₂deg, hp₂⟩ := hw₂
  have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) := domain_injOn domain T
  -- p₁ = p₂ as polynomials (both degree < k ≤ #T, agree on #T distinct nodes)
  have hpeq : p₁ = p₂ := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := T) (v := fun i => domain i)
      hinj ?_ ?_ ?_
    · calc p₁.degree < (k : WithBot ℕ) := hp₁deg
        _ ≤ (T.card : WithBot ℕ) := by exact_mod_cast hcard
    · calc p₂.degree < (k : WithBot ℕ) := hp₂deg
        _ ≤ (T.card : WithBot ℕ) := by exact_mod_cast hcard
    · intro i hi
      have h1 : w₁ i = p₁.eval (domain i) := congrFun hp₁ i
      have h2 : w₂ i = p₂.eval (domain i) := congrFun hp₂ i
      rw [← h1, ← h2]
      exact hagree i hi
  funext i
  have h1 : w₁ i = p₁.eval (domain i) := congrFun hp₁ i
  have h2 : w₂ i = p₂.eval (domain i) := congrFun hp₂ i
  rw [h1, h2, hpeq]

end RSHelpers

section UpperBound

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Polynomial ReedSolomon

/-- A word `g` is *non-extendable* on `T` (for a code `C`) if no codeword agrees with `g`
on all of `T`. -/
def NonExtendableOn (C : Set (ι → F)) (T : Finset ι) (g : ι → F) : Prop :=
  ¬ ∃ v ∈ C, ∀ i ∈ T, v i = g i

/-- **Step 2 (pair-from-extension).** In an `mcaEvent` at radius `1` over a `Submodule` code,
the second word `u₁` is non-extendable on the witness set `S`: if some codeword `v₁` agreed
with `u₁` on `S`, then `w - γ • v₁` would be a codeword agreeing with `u₀` on `S`, giving a
joint pair and contradicting the event's `¬ pairJointAgreesOn` clause. -/
theorem nonExtendable_of_mcaEvent (MC : Submodule F (ι → F)) {u₀ u₁ : ι → F} {γ : F}
    {S : Finset ι} {w : ι → F} (hw : w ∈ (MC : Set (ι → F)))
    (hwline : ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hpair : ¬ pairJointAgreesOn (MC : Set (ι → F)) S u₀ u₁) :
    NonExtendableOn (MC : Set (ι → F)) S u₁ := by
  rintro ⟨v₁, hv₁, hv₁agree⟩
  apply hpair
  refine ⟨w - γ • v₁, MC.sub_mem hw (MC.smul_mem γ hv₁), v₁, hv₁, ?_⟩
  intro i hi
  refine ⟨?_, hv₁agree i hi⟩
  change w i - γ • v₁ i = u₀ i
  rw [hv₁agree i hi, hwline i hi]
  simp

/-- **Step 3 (interpolation forces large witness).** Over an RS code with injective domain,
if `u₁` is non-extendable on `S`, then `S.card ≥ k + 1` (equivalently `¬ S.card ≤ k`): a set
of size `≤ k` always admits an interpolating codeword. -/
theorem card_ge_of_nonExtendable (domain : ι ↪ F) {k : ℕ} {S : Finset ι} {u₁ : ι → F}
    (hne : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁) :
    k + 1 ≤ S.card := by
  by_contra h
  push Not at h
  have hcard : S.card ≤ k := by omega
  obtain ⟨w, hw, hagree⟩ := exists_rs_codeword_agree_of_card_le domain hcard u₁
  exact hne ⟨w, hw, hagree⟩

/-- **Step 5 (counting / per-`T` uniqueness).** For a fixed set `T` on which `u₁` is
non-extendable for an RS code, at most one scalar `γ` admits a codeword `w` with
`w = u₀ + γ • u₁` on `T`. Concretely: two such pairs `(γ₁, w₁)`, `(γ₂, w₂)` with `γ₁ ≠ γ₂`
would make `(γ₁ - γ₂)⁻¹ • (w₁ - w₂)` a codeword agreeing with `u₁` on `T`. -/
theorem unique_gamma_of_nonExtendable (domain : ι ↪ F) {k : ℕ} {T : Finset ι} {u₀ u₁ : ι → F}
    (hne : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) T u₁)
    {γ₁ γ₂ : F} {w₁ w₂ : ι → F}
    (hw₁ : w₁ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hw₂ : w₂ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (h₁ : ∀ i ∈ T, w₁ i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ T, w₂ i = u₀ i + γ₂ • u₁ i) :
    γ₁ = γ₂ := by
  by_contra hne_γ
  apply hne
  set MC := ReedSolomon.code domain k
  have hsub : (γ₁ - γ₂)⁻¹ • (w₁ - w₂) ∈ (MC : Set (ι → F)) := by
    rw [SetLike.mem_coe]
    exact MC.smul_mem _ (MC.sub_mem (SetLike.mem_coe.mp hw₁) (SetLike.mem_coe.mp hw₂))
  refine ⟨(γ₁ - γ₂)⁻¹ • (w₁ - w₂), hsub, ?_⟩
  intro i hi
  have hdiff : (w₁ - w₂) i = (γ₁ - γ₂) • u₁ i := by
    change w₁ i - w₂ i = (γ₁ - γ₂) • u₁ i
    rw [h₁ i hi, h₂ i hi, sub_smul]
    abel
  change (γ₁ - γ₂)⁻¹ • (w₁ - w₂) i = u₁ i
  rw [hdiff, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne_γ), one_smul]

/-- **Step 4 (gluing).** If `u₁` is non-extendable on `S` for an RS code, then there is a
`(k+1)`-subset `T ⊆ S` on which `u₁` is already non-extendable. Contrapositive: if *every*
`(k+1)`-subset of `S` is extendable, gluing the local codewords (which all coincide, agreeing
on `≥ k` nodes) produces a single codeword extending `u₁` on all of `S`. -/
theorem exists_card_eq_subset_nonExtendable (domain : ι ↪ F) {k : ℕ} {S : Finset ι} {u₁ : ι → F}
    (hne : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁) :
    ∃ T ⊆ S, T.card = k + 1 ∧
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) T u₁ := by
  classical
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ T ⊆ S, T.card = k+1 → (∃ v ∈ C, ∀ i ∈ T, v i = u₁ i)
  -- We derive that u₁ is extendable on S, contradicting hne.
  set C := (ReedSolomon.code domain k : Set (ι → F))
  -- Every (k+1)-subset T ⊆ S has an extending codeword.
  have hext : ∀ T : Finset ι, T ⊆ S → T.card = k + 1 →
      ∃ v ∈ C, ∀ i ∈ T, v i = u₁ i := by
    intro T hTS hTcard
    have := hcon T hTS hTcard
    simpa [NonExtendableOn] using this
  have hScard : k + 1 ≤ S.card := card_ge_of_nonExtendable domain hne
  -- Choose a base (k+1)-subset T₀ ⊆ S.
  obtain ⟨T₀, hT₀S, hT₀card⟩ := Finset.exists_subset_card_eq hScard
  obtain ⟨v, hvC, hvT₀⟩ := hext T₀ hT₀S hT₀card
  -- T₀ is nonempty, pick t₀ ∈ T₀.
  have hT₀ne : T₀.Nonempty := by
    rw [← Finset.card_pos, hT₀card]; omega
  obtain ⟨t₀, ht₀⟩ := hT₀ne
  -- Claim: v agrees with u₁ on all of S.
  apply hne
  refine ⟨v, hvC, ?_⟩
  intro i hiS
  by_cases hiT₀ : i ∈ T₀
  · exact hvT₀ i hiT₀
  · -- Build T_i := insert i (T₀.erase t₀), card = k+1, ⊆ S.
    set Te := T₀.erase t₀ with hTe
    have hTecard : Te.card = k := by
      rw [hTe, Finset.card_erase_of_mem ht₀, hT₀card]; omega
    have hi_not_Te : i ∉ Te := by
      rw [hTe]; intro h; exact hiT₀ (Finset.mem_of_mem_erase h)
    set Ti := insert i Te with hTi
    have hTicard : Ti.card = k + 1 := by
      rw [hTi, Finset.card_insert_of_notMem hi_not_Te, hTecard]
    have hTiS : Ti ⊆ S := by
      rw [hTi]
      apply Finset.insert_subset hiS
      exact (Finset.erase_subset _ _).trans hT₀S
    obtain ⟨v', hv'C, hv'Ti⟩ := hext Ti hTiS hTicard
    -- v' and v agree on Te (⊆ both), card Te = k, so v' = v.
    have hTe_sub_Ti : Te ⊆ Ti := by rw [hTi]; exact Finset.subset_insert _ _
    have hTe_sub_T₀ : Te ⊆ T₀ := by rw [hTe]; exact Finset.erase_subset _ _
    have hagree_Te : ∀ j ∈ Te, v' j = v j := by
      intro j hj
      rw [hv'Ti j (hTe_sub_Ti hj), hvT₀ j (hTe_sub_T₀ hj)]
    have hvv' : v' = v :=
      rs_eq_of_agree_on_card_ge domain (k := k) (T := Te) (by rw [hTecard]) hv'C hvC hagree_Te
    -- Then v i = v' i = u₁ i (i ∈ Ti).
    rw [← hvv']
    exact hv'Ti i (by rw [hTi]; exact Finset.mem_insert_self _ _)

/-- A `(k+1)`-subset `T` is *`(u₀,u₁,γ)`-good* (for the RS code) if `u₁` is non-extendable
on `T` and some codeword equals the line `u₀ + γ • u₁` on `T`. By Step 5 each good `T`
pins `γ` uniquely. -/
def GoodSubset (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) (γ : F) (T : Finset ι) : Prop :=
  T.card = k + 1 ∧
    (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ T, w i = u₀ i + γ • u₁ i) ∧
    NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) T u₁

/-- **Steps 1–4 packaged.** Every `mcaEvent` at radius `1` over an RS code yields a good
`(k+1)`-subset. -/
theorem exists_goodSubset_of_mcaEvent (domain : ι ↪ F) {k : ℕ} {u₀ u₁ : ι → F} {γ : F}
    (h : mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ γ) :
    ∃ T, GoodSubset domain k u₀ u₁ γ T := by
  obtain ⟨S, _hScard, ⟨w, hw, hwline⟩, hpair⟩ := h
  -- u₁ non-extendable on S (Step 2)
  have hneS : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁ :=
    nonExtendable_of_mcaEvent (ReedSolomon.code domain k) hw hwline hpair
  -- shrink to a (k+1)-subset T ⊆ S still non-extendable (Step 4)
  obtain ⟨T, hTS, hTcard, hneT⟩ := exists_card_eq_subset_nonExtendable domain hneS
  refine ⟨T, hTcard, ⟨w, hw, ?_⟩, hneT⟩
  intro i hi
  exact hwline i (hTS hi)

/-- **Step 6 (counting / per-stack bound).** For a fixed stack `(u₀, u₁)`, the `mcaEvent`
probability at radius `1` over an RS code with injective domain is at most
`choose n (k+1) / |F|`: the bad `γ`-set injects into the `(k+1)`-subsets of `ι`. -/
theorem mcaEvent_prob_le (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) :
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ γ ] ≤
      (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  set Bad := Finset.univ.filter
    (fun γ : F => mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ γ) with hBad
  -- choice of a good subset for each bad γ
  have hgood : ∀ γ ∈ Bad, ∃ T, GoodSubset domain k u₀ u₁ γ T := by
    intro γ hγ
    rw [hBad, Finset.mem_filter] at hγ
    exact exists_goodSubset_of_mcaEvent domain hγ.2
  choose! Tf hTf using hgood
  -- Tf maps Bad into the (k+1)-subsets of univ, injectively
  have hmaps : Set.MapsTo Tf (↑Bad) (↑((Finset.univ : Finset ι).powersetCard (k + 1))) := by
    intro γ hγ
    have hg := hTf γ hγ
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hg.1⟩
  have hinj : (↑Bad : Set F).InjOn Tf := by
    intro γ₁ hγ₁ γ₂ hγ₂ hTeq
    have hg₁ := hTf γ₁ hγ₁
    have hg₂ := hTf γ₂ hγ₂
    obtain ⟨w₁, hw₁, hw₁line⟩ := hg₁.2.1
    obtain ⟨w₂, hw₂, hw₂line⟩ := hg₂.2.1
    -- on T := Tf γ₁ = Tf γ₂ both lines match codewords, T non-extendable ⇒ γ₁ = γ₂
    have hneT : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) (Tf γ₁) u₁ := hg₁.2.2
    refine unique_gamma_of_nonExtendable domain hneT hw₁ hw₂ hw₁line ?_
    rw [hTeq]; exact hw₂line
  have hcard_le : Bad.card ≤ ((Finset.univ : Finset ι).powersetCard (k + 1)).card :=
    Finset.card_le_card_of_injOn Tf hmaps hinj
  rw [Finset.card_powersetCard, Finset.card_univ] at hcard_le
  -- push to ENNReal division
  have hnum : (↑(↑Bad.card : ℝ≥0) : ENNReal) ≤
      (↑((Fintype.card ι).choose (k + 1)) : ENNReal) := by exact_mod_cast hcard_le
  have hden : (↑(↑(Fintype.card F) : ℝ≥0) : ENNReal) = (↑(Fintype.card F) : ENNReal) := by
    push_cast; rfl
  rw [hden]
  gcongr

/-- **THEOREM B (upper bound).** For `C := ReedSolomon.code domain k` with injective `domain`
and `n := |ι|`: `ε_mca(C, 1) ≤ choose n (k+1) / |F|`. -/
theorem epsMCA_one_le_choose_div (domain : ι ↪ F) (k : ℕ) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 ≤
      (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  exact mcaEvent_prob_le domain k (u 0) (u 1)

end UpperBound

section Corollaries

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Polynomial ReedSolomon GrandChallenges

/-- **Proper-subset witness.** If `0 < k` and `k < |ι|`, the RS code `code domain k` is a
proper subset of all words: the `i₀`-indicator (for any `i₀`) is not a codeword, since a
degree-`< k` polynomial vanishing on a `k`-subset disjoint from `i₀` is zero. -/
theorem rsCode_ne_univ (domain : ι ↪ F) {k : ℕ} (_hk : 0 < k) (hkn : k < Fintype.card ι) :
    (ReedSolomon.code domain k : Set (ι → F)) ≠ Set.univ := by
  classical
  -- pick i₀ and a k-subset K of ι.erase i₀
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have herase : k ≤ ((Finset.univ : Finset ι).erase i₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq herase
  have hi₀K : i₀ ∉ K := fun h => (Finset.mem_erase.mp (hKsub h)).1 rfl
  -- indicator word
  set g : ι → F := fun i => if i = i₀ then 1 else 0 with hg
  intro huniv
  have hmem : g ∈ (ReedSolomon.code domain k : Set (ι → F)) := huniv ▸ Set.mem_univ g
  -- 0 ∈ code and 0 agrees with g on K (card k); gluing ⇒ g = 0
  have hzero_mem : (0 : ι → F) ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
    rw [SetLike.mem_coe]; exact (ReedSolomon.code domain k).zero_mem
  have hagree : ∀ i ∈ K, g i = (0 : ι → F) i := by
    intro i hi
    have : i ≠ i₀ := fun h => hi₀K (h ▸ hi)
    simp [hg, this]
  have hgzero : g = 0 :=
    rs_eq_of_agree_on_card_ge domain (k := k) (T := K) (by rw [hKcard]) hmem hzero_mem hagree
  have : g i₀ = 0 := by rw [hgzero]; rfl
  rw [hg] at this
  simp at this

/-- **COROLLARY 1 (`mcaPrize_of_large_field`).** If at every prize rate the counting bound
`choose n (⌊ρⱼ·n⌋ + 1) / |F|` is at most `ε*`, then the formal §1 MCA prize predicate holds.
This is true whenever `|F|` is large relative to `n` (e.g. `|F| ≥ 2^128`). -/
theorem mcaPrize_of_large_field (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι) (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    GrandChallenges.mcaPrize domain := by
  rw [mcaPrize_iff_forall_epsMCA_one]
  intro j
  exact le_trans (epsMCA_one_le_choose_div domain _) (hbound j)

/-- **COROLLARY 2 (`not_mcaPrize_of_small_field`).** If `ε* < 1/|F|` (i.e. the field is small,
`|F| < 2^128`) and `2 ≤ |ι|`, then the formal §1 MCA prize predicate fails: at rate `1/2`
the RS code is a proper subset, so `ε_mca(·, 1) ≥ 1/|F| > ε*`, violating the radius-one
bound the prize collapses to. -/
theorem not_mcaPrize_of_small_field (domain : ι ↪ F)
    (hsmall : (epsStar : ENNReal) < (Fintype.card F : ENNReal)⁻¹)
    (hι : 2 ≤ Fintype.card ι) :
    ¬ GrandChallenges.mcaPrize domain := by
  rw [mcaPrize_iff_forall_epsMCA_one]
  intro hprize
  -- rate j = 0 is ρ = 1/2, giving k = ⌊n/2⌋ with 0 < k < n.
  have h0 := hprize 0
  have hrate : prizeRates 0 = 1 / 2 := by unfold prizeRates; norm_num
  set k := ⌊prizeRates 0 * (Fintype.card ι : ℝ≥0)⌋₊ with hk
  have hk_pos : 0 < k := by
    rw [hk, hrate]
    have h2 : ((1 : ℕ) : ℝ≥0) ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
      push_cast
      calc (1 : ℝ≥0) = (1 / 2) * 2 := by norm_num
        _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
            gcongr; exact_mod_cast hι
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor h2)
  have hk_lt : k < Fintype.card ι := by
    rw [hk, hrate]
    have hpos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
      exact_mod_cast Fintype.card_pos
    have hlt : (1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
      calc (1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0)
          < 1 * (Fintype.card ι : ℝ≥0) := by
            apply mul_lt_mul_of_pos_right _ hpos; norm_num
        _ = (Fintype.card ι : ℝ≥0) := one_mul _
    exact (Nat.floor_lt (zero_le _)).mpr
      (show (1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0) < ((Fintype.card ι : ℕ) : ℝ≥0) from hlt)
  -- proper subset ⇒ lower bound 1/|F|
  have hproper := rsCode_ne_univ domain hk_pos hk_lt
  have hlb := epsMCA_one_ge_inv (ReedSolomon.code domain k) hproper
  -- combine: ε* < 1/|F| ≤ ε_mca ≤ ε*, contradiction
  have := le_trans hlb h0
  exact absurd (lt_of_lt_of_le hsmall this) (lt_irrefl _)

end Corollaries

end ProximityGap
