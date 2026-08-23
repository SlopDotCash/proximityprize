/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DerandomizationFrontier

/-!
# The MULTI-POINT puncture pigeonhole — the iterated derandomization transfer (#444 / #232)

`DerandomizationFrontier.lean` (Round 14, Angle E) localized the derandomization core to the
gap between "some size-`n` evaluation set works" and "the explicit smooth-subgroup domain works",
and proved the **single-coordinate** puncture pigeonhole

> `listDecodableAbs_punctureCode_pigeonhole` :
> `ListDecodableAbs C (t+1) L → ListDecodableAbs (punctureCode x C) t (|F|·L)`,

flagging (via `naive_margin_fails_concrete` / `pigeonhole_tight_concrete`) that the `|F|` factor
per deleted coordinate is unavoidable.  But the derandomization-relevant statement compares the
explicit subgroup domain to an ambient set differing by a WHOLE BLOCK of `k = |S|` coordinates,
and the single-point lemma was never iterated to that block form.

This file supplies the missing brick: the **`S`-block puncture pigeonhole**, deleting an
arbitrary `Finset S` of coordinates at once via restriction to the complement subtype
`{i // i ∉ S}`.  The headline is

> **`listDecodableAbs_punctureSetCode_pigeonhole`** :
> `ListDecodableAbs C (t + S.card) L → ListDecodableAbs (punctureSetCode S C) t (|F|^S.card · L)`,

the exact `k`-fold iterate of the single-point bound (threshold drops by `S.card`, list grows by
`|F|^{S.card}`), proved by a single block pigeonhole over the deleted-coordinate assignments
`S → F` (`Fintype.card (S → F) = |F|^S.card`).  Companions:

* `agreement_punctureSetWord_le` — restriction never increases agreement;
* `agreement_le_punctureSetWord_add_card` — deleting `S` loses at most `S.card` agreement;
* `listDecodableAbs_punctureSetCode` — SAME-threshold survival (the `S`-block of part (i));
* `listDecodableAbs_of_punctureSetCode` — the transfer-BACK direction (the derandomization-relevant
  one): an injective `S`-block puncture of a good complement-domain code certifies the FULL code at
  threshold `t + S.card` with the SAME list `L` (NO `|F|` blow-up — the deleted block is paid only in
  the threshold).  The `S`-block iterate of `listDecodableAbs_of_punctureCode`;
* `punctureSetCode_empty_pigeonhole` — `S = ∅` sanity recovers the identity (`|F|^0 = 1`).

## Honest scope (what this is and is NOT)
This is a strict **EXTEND** of the proved single-point pigeonhole: a structural transfer law on
the derandomization face, proved by elementary fiberwise counting.  It does **NOT** prove
`DerandomizationCore` (whether existence of a good size-`n` set forces the smooth-subgroup domain
to be good) — that remains the stated-but-unasserted open research content of
`DerandomizationFrontier`.  The `|F|^{S.card}` factor is genuinely needed (the single-point
tightness witness `pigeonhole_tight_concrete` iterates), so the transfer DEGRADES the list size
geometrically in the block size — precisely why naive derandomization-by-puncturing does not by
itself close the prize.  NON-MOMENT (coding-theoretic / pigeonhole), field-universal.  Makes NO
capacity / beyond-Johnson / growth-law claim; the cliff-at-`n/2` is untouched.  CORE
`M(μ_n) ≤ C √(n log(p/n))` UNCHANGED.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- Tracking issues #232 (ABF26), #444 (proximity prize).
-/

namespace R14Derand

open Finset

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [DecidableEq F]

/-! ## Multi-point puncture: restriction to the complement of a `Finset S`. -/

/-- The `S`-block puncture of a word: its restriction to the coordinates OUTSIDE `S`. -/
def punctureSetWord (S : Finset ι) (c : ι → F) : {i : ι // i ∉ S} → F :=
  fun i => c i.1

/-- The `S`-block punctured code: the image of the code under deleting the coordinates in `S`. -/
def punctureSetCode (S : Finset ι) (C : Finset (ι → F)) : Finset ({i : ι // i ∉ S} → F) :=
  C.image (punctureSetWord S)

/-- Extension of an `S`-punctured word back to the full domain, using `g : ι → F` on `S`. -/
def extendSetWord (S : Finset ι) (g : ι → F) (w' : {i : ι // i ∉ S} → F) : ι → F :=
  fun i => if h : i ∈ S then g i else w' ⟨i, h⟩

@[simp] lemma punctureSetWord_extendSetWord (S : Finset ι) (g : ι → F)
    (w' : {i : ι // i ∉ S} → F) :
    punctureSetWord S (extendSetWord S g w') = w' := by
  funext i
  simp [punctureSetWord, extendSetWord, i.2]

/-- `S = ∅` recovers the full word (no coordinate deleted). -/
lemma punctureSetWord_empty (c : ι → F) :
    punctureSetWord (∅ : Finset ι) c = fun i => c i.1 := rfl

/-! ## The two agreement transfer bounds for an `S`-block. -/

/-- **Restriction never increases agreement.**  Agreeing off `S` is a subset of agreeing. -/
lemma agreement_punctureSetWord_le (S : Finset ι) (w c : ι → F) :
    agreement (punctureSetWord S w) (punctureSetWord S c) ≤ agreement w c := by
  unfold agreement
  refine Finset.card_le_card_of_injOn (fun i => i.1) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      punctureSetWord] at hi ⊢
    exact hi
  · intro a _ b _ h
    exact Subtype.ext h

/-- **Deleting the block `S` loses at most `S.card` units of agreement.**  Every full-agreement
coordinate either lies in `S` (at most `S.card` of them) or is a punctured-agreement coordinate. -/
lemma agreement_le_punctureSetWord_add_card (S : Finset ι) (w c : ι → F) :
    agreement w c ≤ agreement (punctureSetWord S w) (punctureSetWord S c) + S.card := by
  unfold agreement
  -- the full agreement set ⊆ S ∪ (image of the punctured agreement set)
  have hsub : (Finset.univ.filter fun i => w i = c i) ⊆
      S ∪ ((Finset.univ.filter fun i : {i : ι // i ∉ S} =>
        punctureSetWord S w i = punctureSetWord S c i).image (fun i => i.1)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hS : i ∈ S
    · exact Finset.mem_union_left _ hS
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨i, hS⟩, ?_, rfl⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, punctureSetWord]
      exact hi
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  rw [Nat.add_comm]
  refine Nat.add_le_add_right ?_ _
  exact (Finset.card_image_le (s := (Finset.univ.filter fun i : {i : ι // i ∉ S} =>
    punctureSetWord S w i = punctureSetWord S c i)) (f := fun i => i.1))

/-- **If the words also agree everywhere on `S`, the full agreement is at least the punctured
agreement plus `S.card`.**  (The sharp lower transfer; used only for the same-threshold survival.) -/
lemma agreement_punctureSetWord_add_card_le (S : Finset ι) (w c : ι → F)
    (hS : ∀ i ∈ S, w i = c i) :
    agreement (punctureSetWord S w) (punctureSetWord S c) + S.card ≤ agreement w c := by
  unfold agreement
  -- S and the (injective) image of the punctured agreement set are disjoint subsets of the
  -- full agreement set, so their card sum bounds it.
  set img := (Finset.univ.filter fun i : {i : ι // i ∉ S} =>
      punctureSetWord S w i = punctureSetWord S c i).image (fun i => i.1) with himg
  have hdisj : Disjoint S img := by
    rw [Finset.disjoint_left]
    intro a haS ha
    rw [himg, Finset.mem_image] at ha
    rcases ha with ⟨j, -, rfl⟩
    exact j.2 haS
  have hcard_img : img.card = (Finset.univ.filter fun i : {i : ι // i ∉ S} =>
      punctureSetWord S w i = punctureSetWord S c i).card :=
    Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)
  have hsub : S ∪ img ⊆ Finset.univ.filter fun i => w i = c i := by
    intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS i h
    · rw [himg, Finset.mem_image] at h
      rcases h with ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, punctureSetWord] at hj ⊢
      exact hj
  have h1 := Finset.card_le_card hsub
  rwa [Finset.card_union_of_disjoint hdisj, hcard_img, Nat.add_comm] at h1

/-! ## (i) Same-threshold survival for an `S`-block (the multi-point version of part (i)). -/

/-- **Same-threshold survival under an `S`-block puncture.**  Keeping the SAME absolute
threshold `t` on the smaller (complement) domain preserves list decodability. -/
theorem listDecodableAbs_punctureSetCode [Nonempty F] (S : Finset ι) {C : Finset (ι → F)}
    {t L : ℕ} (h : ListDecodableAbs C t L) :
    ListDecodableAbs (punctureSetCode S C) t L := by
  intro w'
  obtain ⟨a⟩ := ‹Nonempty F›
  have hw : punctureSetWord S (extendSetWord S (fun _ => a) w') = w' :=
    punctureSetWord_extendSetWord S _ w'
  have hsub : (punctureSetCode S C).filter (fun c' => t ≤ agreement w' c') ⊆
      (C.filter fun c => t ≤ agreement (extendSetWord S (fun _ => a) w') c).image
        (punctureSetWord S) := by
    intro c' hc'
    rcases Finset.mem_filter.1 hc' with ⟨hmem, ht⟩
    simp only [punctureSetCode] at hmem
    rcases Finset.mem_image.1 hmem with ⟨c, hcC, rfl⟩
    refine Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hcC, ?_⟩, rfl⟩
    have h1 : agreement (punctureSetWord S (extendSetWord S (fun _ => a) w'))
        (punctureSetWord S c) ≤ agreement (extendSetWord S (fun _ => a) w') c :=
      agreement_punctureSetWord_le S _ c
    rw [hw] at h1
    exact ht.trans h1
  exact ((Finset.card_le_card hsub).trans Finset.card_image_le).trans (h _)

/-! ## (ii) The headline: the `S`-block puncture pigeonhole (the iterated transfer). -/

/-- **The `S`-block puncture pigeonhole — the iterated derandomization transfer.**
If `C` is list-decodable at absolute threshold `t + S.card` with list `L`, then deleting the
whole block `S` of coordinates yields list decodability at threshold `t` with list
`|F|^{S.card} · L`.  This is the exact `k`-fold iterate of `listDecodableAbs_punctureCode_pigeonhole`
(`k = S.card`): each deleted coordinate drops the threshold by one and multiplies the list by `|F|`,
realized here as a SINGLE block pigeonhole over the deleted-coordinate assignments `S → F`
(`Fintype.card (S → F) = |F|^{S.card}`). -/
theorem listDecodableAbs_punctureSetCode_pigeonhole [Fintype F] (S : Finset ι)
    {C : Finset (ι → F)} {t L : ℕ} (h : ListDecodableAbs C (t + S.card) L) :
    ListDecodableAbs (punctureSetCode S C) t (Fintype.card F ^ S.card * L) := by
  intro w'
  -- Step 1: punctured matches pull back to full matches of the punctured threshold.
  have h1 : ((punctureSetCode S C).filter fun c' => t ≤ agreement w' c').card ≤
      (C.filter fun c => t ≤ agreement w' (punctureSetWord S c)).card := by
    have hsub : (punctureSetCode S C).filter (fun c' => t ≤ agreement w' c') ⊆
        (C.filter fun c => t ≤ agreement w' (punctureSetWord S c)).image
          (punctureSetWord S) := by
      intro c' hc'
      rcases Finset.mem_filter.1 hc' with ⟨hmem, ht⟩
      simp only [punctureSetCode] at hmem
      rcases Finset.mem_image.1 hmem with ⟨c, hcC, rfl⟩
      exact Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hcC, ht⟩, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  -- Step 2: fiber the full matches over the deleted-block assignment `i ↦ c i` on `S`.
  -- the fiber map: a codeword ↦ its restriction to `S` (a function `S → F`).
  set Cfilt := C.filter fun c => t ≤ agreement w' (punctureSetWord S c) with hCfilt
  have h2 : Cfilt.card =
      ∑ g ∈ (Finset.univ : Finset (S → F)),
        (Cfilt.filter fun c => (fun i : S => c i.1) = g).card :=
    Finset.card_eq_sum_card_fiberwise (fun c _ => Finset.mem_univ (fun i : S => c i.1))
  -- Step 3: each fiber has ≤ L elements — fixing the block assignment lifts the threshold by S.card.
  have h3 : ∀ g : S → F,
      (Cfilt.filter fun c => (fun i : S => c i.1) = g).card ≤ L := by
    intro g
    -- the witness word: extend w' by g on S.
    have hsub : (Cfilt.filter fun c => (fun i : S => c i.1) = g) ⊆
        C.filter fun c => t + S.card ≤
          agreement (extendSetWord S (fun i => if h : i ∈ S then g ⟨i, h⟩ else w' ⟨i, h⟩) w') c := by
      intro c hc
      rcases Finset.mem_filter.1 hc with ⟨hc1, hcg⟩
      rcases Finset.mem_filter.1 hc1 with ⟨hcC, ht⟩
      refine Finset.mem_filter.2 ⟨hcC, ?_⟩
      -- the extended witness agrees with c on all of S (its S-values are g, which equal c's on S),
      -- and its puncture is w', so the sharp lower transfer applies.
      set wext := extendSetWord S (fun i => if h : i ∈ S then g ⟨i, h⟩ else w' ⟨i, h⟩) w' with hwext
      have hpunct : punctureSetWord S wext = w' := punctureSetWord_extendSetWord S _ w'
      have hSagree : ∀ i ∈ S, wext i = c i := by
        intro i hiS
        have : wext i = g ⟨i, hiS⟩ := by simp [hwext, extendSetWord, hiS]
        rw [this]
        have := congrFun hcg ⟨i, hiS⟩
        simpa using this.symm
      have hstep := agreement_punctureSetWord_add_card_le S wext c hSagree
      rw [hpunct] at hstep
      omega
    exact (Finset.card_le_card hsub).trans (h _)
  -- assemble: |Cfilt| ≤ |F|^|S| · L, then h1.
  calc ((punctureSetCode S C).filter fun c' => t ≤ agreement w' c').card
      ≤ Cfilt.card := h1
    _ = ∑ g ∈ (Finset.univ : Finset (S → F)),
          (Cfilt.filter fun c => (fun i : S => c i.1) = g).card := h2
    _ ≤ ∑ _g ∈ (Finset.univ : Finset (S → F)), L := Finset.sum_le_sum fun g _ => h3 g
    _ = Fintype.card (S → F) * L := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = Fintype.card F ^ S.card * L := by
          rw [Fintype.card_fun, Fintype.card_coe]

/-! ## (iii) The transfer-BACK direction: a good complement-domain certifies the full domain. -/

/-- **The `S`-block transfer-back — the derandomization-relevant direction.**  If the `S`-block
puncture is injective on `C` (true for an RS code whenever the surviving domain still has at least
`k` points, so distinct codewords stay distinct after deletion) and the punctured code on the
complement domain `{i // i ∉ S}` is list-decodable at threshold `t` with list `L`, then the FULL
code is list-decodable at threshold `t + S.card` with the SAME list `L` (NO `|F|` blow-up).  This is
the `S`-block iterate of `listDecodableAbs_of_punctureCode`: a good (smaller, possibly explicit)
complement domain pulls back to the original domain, paying the deleted block ONLY in the agreement
threshold, not the list size. -/
theorem listDecodableAbs_of_punctureSetCode (S : Finset ι) {C : Finset (ι → F)} {t L : ℕ}
    (hinj : ∀ a ∈ C, ∀ b ∈ C, punctureSetWord S a = punctureSetWord S b → a = b)
    (h : ListDecodableAbs (punctureSetCode S C) t L) :
    ListDecodableAbs C (t + S.card) L := by
  intro w
  have hb : (C.filter fun c => t + S.card ≤ agreement w c).card ≤
      ((punctureSetCode S C).filter fun c' =>
        t ≤ agreement (punctureSetWord S w) c').card := by
    refine Finset.card_le_card_of_injOn (punctureSetWord S) ?_ ?_
    · intro c hc
      rw [Finset.mem_coe] at hc
      rcases Finset.mem_filter.1 hc with ⟨hcC, ht⟩
      rw [Finset.mem_coe]
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hcC, ?_⟩
      -- agreement w c ≤ punctured agreement + S.card, so t + S.card ≤ agreement w c forces
      -- t ≤ punctured agreement.
      have hstep := agreement_le_punctureSetWord_add_card S w c
      omega
    · intro a ha b hb' hab
      exact hinj a (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1
        b (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).1 hab
  exact hb.trans (h _)

/-! ## Sanity: the empty block recovers the identity (no deletion). -/

/-- `S = ∅` ⇒ the pigeonhole degenerates to `|F|^0 · L = L` at the SAME threshold `t`. -/
theorem punctureSetCode_empty_pigeonhole [Fintype F] {C : Finset (ι → F)} {t L : ℕ}
    (h : ListDecodableAbs C t L) :
    ListDecodableAbs (punctureSetCode (∅ : Finset ι) C) t L := by
  have := listDecodableAbs_punctureSetCode_pigeonhole (∅ : Finset ι)
    (by simpa using h)
  simpa using this

end General

end R14Derand
