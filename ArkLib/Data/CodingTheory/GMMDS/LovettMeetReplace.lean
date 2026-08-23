/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24
import ArkLib.Data.CodingTheory.GMMDS.LovettPrimitiveDischarge

/-!
# Lovett's GM-MDS proof: the meet-replacement system for Lemma 2.4 (#389)

This file builds the *meet-replacement* system `V'` used in the proof of Lovett's Lemma 2.4
(arXiv:1803.02523, p.8).  Given a `V*(k)` system `V` and a **tight** index set `I` with
`1 < |I| < m`, Lemma 2.4 replaces the entire `I`-block of vectors by the single coordinate-wise
meet `v_I = ⋀_{i∈I} vᵢ`, keeping every vector outside `I`.  The resulting system

> `replaceMeet V I = ⟨v_I⟩ ⊕ ⟨vᵢ : i ∉ I⟩`  over the index type  `Fin 1 ⊕ {i // i ∉ I}`,

has the following key properties (all proven here):

* `replaceMeet_card` — its number of vectors is `m − |I| + 1`, strictly less than `m` (since
  `|I| > 1`), so the **`m`-induction hypothesis** of the master frame applies to it.
* `lovettD_replaceMeet` — when `I` is *tight*, the induction measure `d = Σ (k − |vᵢ|)` is
  **unchanged**: removing the `|I|` blocks `Σ_{i∈I}(k − |vᵢ|)` and adding back the single block
  `k − |v_I|` is a wash by tightness (`k − |v_I| = Σ_{i∈I}(k − |vᵢ|)`).
* `replaceMeet_isVStar` — `V'` is again a `V*(k)` system.  Clauses (i)/(iii) are immediate from
  the meet being `≤` each member; clause (ii) is the genuine combinatorial content of Lemma 2.4:
  an index set `I'` of `V'` that uses the meet block is re-expressed as the index set
  `(I' \ {meet}) ∪ I` of `V`, whose meet and sum coincide (the sum step uses tightness).

The remaining content of Lemma 2.4 — that `P(k, V')` independent transfers to `P(k, V)`
independent via the equal-span / equal-cardinality counting lemma over `F(a)` — is the algebraic
finish, isolated downstream.  This file is the *combinatorial* layer: construction, cardinality,
measure invariance, and `V*(k)` preservation.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-! ## Meet monotonicity -/

/-- The meet over `I` is coordinate-wise `≤` every member of `I`. -/
theorem vMeet_le_mem {V : Fin m → (Fin n → ℕ)} {I : Finset (Fin m)} (hI : I.Nonempty)
    {i : Fin m} (hi : i ∈ I) (l : Fin n) : vMeet V I hI l ≤ V i l :=
  Finset.inf'_le (fun i => V i l) hi

/-- The meet weight is `≤` the weight of every member of `I`. -/
theorem vAbs_vMeet_le_mem {V : Fin m → (Fin n → ℕ)} {I : Finset (Fin m)} (hI : I.Nonempty)
    {i : Fin m} (hi : i ∈ I) : vAbs (vMeet V I hI) ≤ vAbs (V i) :=
  Finset.sum_le_sum (fun l _ => vMeet_le_mem hI hi l)

/-! ## The meet-replacement system -/

/-- The index type of the meet-replacement system: one new "meet" index plus the indices
**outside** `I`. -/
abbrev ReplaceIdx (I : Finset (Fin m)) : Type := Fin 1 ⊕ {i : Fin m // i ∉ I}

/-- The meet-replacement system `V'`: the meet `v_I` on the new index, and `vᵢ` on each `i ∉ I`. -/
noncomputable def replaceMeet (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    ReplaceIdx I → (Fin n → ℕ) :=
  Sum.elim (fun _ => vMeet V I hI) (fun i => V i.1)

/-- The new system has `m − |I| + 1` vectors. -/
theorem replaceMeet_card (I : Finset (Fin m)) :
    Fintype.card (ReplaceIdx I) = (m - I.card) + 1 := by
  classical
  rw [Fintype.card_sum, Fintype.card_fin]
  have : Fintype.card {i : Fin m // i ∉ I} = m - I.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    congr 1
    simp [Fintype.card_coe]
  rw [this]; omega

/-- The canonical reindexing equivalence `ReplaceIdx I ≃ Fin (m − |I| + 1)`. -/
noncomputable def replaceEquiv (I : Finset (Fin m)) : ReplaceIdx I ≃ Fin ((m - I.card) + 1) :=
  (Fintype.equivFinOfCardEq (replaceMeet_card I))

/-- The meet-replacement system as a genuine `Fin (m − |I| + 1)`-indexed system (so that the
master frame's `m`-induction hypothesis, which quantifies over `Fin m'`-indexed systems, applies). -/
noncomputable def replaceMeetFin (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    Fin ((m - I.card) + 1) → (Fin n → ℕ) :=
  replaceMeet V I hI ∘ (replaceEquiv I).symm

/-- `replaceMeetFin` is a reindexing of `replaceMeet` along the bijection `(replaceEquiv I).symm`. -/
theorem replaceMeetFin_comp (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    replaceMeetFin V I hI = replaceMeet V I hI ∘ (replaceEquiv I).symm := rfl

/-! ## The induction measure is invariant under tight meet-replacement -/

/-- A sum over the not-in-`I` subtype equals the Finset sum over the complement of `I`. -/
theorem sum_notMem_eq_sum_compl {M : Type*} [AddCommMonoid M] (I : Finset (Fin m))
    (g : Fin m → M) :
    (∑ i : {i : Fin m // i ∉ I}, g i.1) = ∑ i ∈ Iᶜ, g i := by
  classical
  rw [← Finset.sum_subtype Iᶜ (fun x => by simp) g]

/-- **The measure is unchanged under tight meet-replacement.**  When `I` is tight (and `|v_I| ≤ k`,
which holds in a `V*(k)` system), the induction measure `d = Σ (k − |vᵢ|)` of the replacement
system equals that of the original. -/
theorem lovettD_replaceMeet {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (htight : tightConstraint V k I hI) :
    lovettD (replaceMeetFin V I hI) k = lovettD V k := by
  classical
  unfold lovettD replaceMeetFin
  -- reindex the Fin-sum back to the ReplaceIdx sum via the equivalence
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp (replaceEquiv I).symm (fun p => k - vAbs (replaceMeet V I hI p))]
  unfold replaceMeet
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const]
  -- left block: one term `k - |v_I|`
  rw [Finset.card_univ, Fintype.card_fin, one_smul]
  -- right block: sum over the not-in-I subtype = sum over Iᶜ
  rw [sum_notMem_eq_sum_compl I (fun i => k - vAbs (V i))]
  -- original: split Fin m into I and Iᶜ
  rw [← Finset.sum_add_sum_compl I (fun i => k - vAbs (V i))]
  -- tightness: k - |v_I| = Σ_{i∈I}(k-|vᵢ|)
  unfold tightConstraint at htight
  omega

/-! ## `V*(k)` preservation under tight meet-replacement (clause (ii)) -/

/-- The `Fin m`-block attached to a replacement index: the whole of `I` for the meet index, a
singleton for each surviving index. -/
def replaceBlock (I : Finset (Fin m)) : ReplaceIdx I → Finset (Fin m) :=
  Sum.elim (fun _ => I) (fun i => {i.1})

/-- The expansion of an index set `J` of `V'` to a `Fin m`-index set of `V`: replace the meet
index by all of `I`, keep the surviving indices. -/
noncomputable def expandIdx (I : Finset (Fin m)) (J : Finset (ReplaceIdx I)) : Finset (Fin m) :=
  J.biUnion (replaceBlock I)

/-- Each replacement block is nonempty (for the meet index this uses `I.Nonempty`). -/
theorem replaceBlock_nonempty {I : Finset (Fin m)} (hI : I.Nonempty) (p : ReplaceIdx I) :
    (replaceBlock I p).Nonempty := by
  cases p with
  | inl _ => exact hI
  | inr i => exact Finset.singleton_nonempty i.1

/-- The replacement blocks are pairwise disjoint. -/
theorem replaceBlock_pairwiseDisjoint (I : Finset (Fin m)) :
    (Set.univ : Set (ReplaceIdx I)).PairwiseDisjoint (replaceBlock I) := by
  classical
  rintro p - q - hpq
  -- show blocks are disjoint
  cases p with
  | inl a => cases q with
    | inl b => exact absurd (by rw [Subsingleton.elim a b]) hpq
    | inr j =>
      -- I vs {j.1}, j.1 ∉ I
      show Disjoint I ({j.1} : Finset (Fin m))
      refine Finset.disjoint_right.mpr ?_
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact j.2
  | inr i => cases q with
    | inl b =>
      show Disjoint ({i.1} : Finset (Fin m)) I
      refine Finset.disjoint_left.mpr ?_
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact i.2
    | inr j =>
      -- {i.1} vs {j.1}, i ≠ j
      have hij : i.1 ≠ j.1 := by
        intro h; exact hpq (by cases i; cases j; simp_all)
      show Disjoint ({i.1} : Finset (Fin m)) {j.1}
      exact Finset.disjoint_singleton.mpr hij

/-- The expansion of a `Fin`-index set `J` of `V' = replaceMeetFin` to a `Fin m`-index set of `V`:
push `J` through the reindexing bijection, then replace the meet index by all of `I`. -/
noncomputable def expandFin (I : Finset (Fin m)) (J : Finset (Fin ((m - I.card) + 1))) :
    Finset (Fin m) :=
  expandIdx I (J.image (replaceEquiv I).symm)

/-- `expandFin` of a nonempty set is nonempty. -/
theorem expandFin_nonempty {I : Finset (Fin m)} (hI : I.Nonempty)
    {J : Finset (Fin ((m - I.card) + 1))} (hJ : J.Nonempty) : (expandFin I J).Nonempty := by
  unfold expandFin expandIdx
  exact (hJ.image _).biUnion (fun p _ => replaceBlock_nonempty hI p)

/-- **The replacement meet equals the original meet over the expanded index set** (`Fin` form). -/
theorem vMeet_replaceMeetFin {V : Fin m → (Fin n → ℕ)} {I : Finset (Fin m)} (hI : I.Nonempty)
    {J : Finset (Fin ((m - I.card) + 1))} (hJ : J.Nonempty) :
    vMeet (replaceMeetFin V I hI) J hJ
      = vMeet V (expandFin I J) (expandFin_nonempty hI hJ) := by
  classical
  funext l
  unfold vMeet expandFin expandIdx replaceMeetFin
  simp only [Function.comp_apply]
  -- reindex inf' over J along the injection symm into ReplaceIdx
  have hrw : (J.inf' hJ fun x => replaceMeet V I hI ((replaceEquiv I).symm x) l)
      = (J.image (replaceEquiv I).symm).inf' (hJ.image _)
          (fun p => replaceMeet V I hI p l) :=
    (Finset.inf'_image (f := (replaceEquiv I).symm) (s := J)
      (hs := hJ.image _) (g := fun p => replaceMeet V I hI p l)).symm
  rw [hrw]
  rw [Finset.inf'_biUnion (fun i => V i l) (hJ.image _)
      (fun p => replaceBlock_nonempty hI p)]
  refine Finset.inf'_congr (hJ.image _) rfl (fun p _ => ?_)
  cases p with
  | inl a =>
    show vMeet V I hI l = (replaceBlock I (Sum.inl a)).inf' _ (fun i => V i l)
    simp only [replaceBlock, Sum.elim_inl]
    rfl
  | inr i =>
    show V i.1 l = (replaceBlock I (Sum.inr i)).inf' _ (fun i => V i l)
    simp only [replaceBlock, Sum.elim_inr, Finset.inf'_singleton]

/-- **The replacement block-size sum equals the original over the expanded index set** (`Fin` form;
uses tightness: the meet block `k − |v_I|` accounts for the full `Σ_{i∈I}(k − |vᵢ|)`). -/
theorem sum_replaceMeetFin {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)} (hI : I.Nonempty)
    (htight : tightConstraint V k I hI) (J : Finset (Fin ((m - I.card) + 1))) :
    (∑ q ∈ J, (k - vAbs (replaceMeetFin V I hI q)))
      = ∑ i ∈ expandFin I J, (k - vAbs (V i)) := by
  classical
  unfold expandFin expandIdx replaceMeetFin
  simp only [Function.comp_apply]
  -- reindex sum over J along the injection symm
  rw [← Finset.sum_image (g := (replaceEquiv I).symm)
      (f := fun p => k - vAbs (replaceMeet V I hI p))
      (fun a _ b _ h => (replaceEquiv I).symm.injective h : Set.InjOn _ _)]
  rw [Finset.sum_biUnion
      ((replaceBlock_pairwiseDisjoint I).subset (Set.subset_univ _))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  cases p with
  | inl a =>
    show (k - vAbs (vMeet V I hI)) = ∑ i ∈ replaceBlock I (Sum.inl a), (k - vAbs (V i))
    simp only [replaceBlock, Sum.elim_inl]
    unfold tightConstraint at htight
    omega
  | inr i =>
    show (k - vAbs (V i.1)) = ∑ i' ∈ replaceBlock I (Sum.inr i), (k - vAbs (V i'))
    simp only [replaceBlock, Sum.elim_inr, Finset.sum_singleton]

/-- **`V*(k)` is preserved under tight meet-replacement** (`Fin`-indexed form).  The combinatorial
heart of Lovett's Lemma 2.4: clauses (i)/(iii) from the meet being `≤` each member, clause (ii)
for any index set `J` of `V'` is the MDS inequality of `V` at the *expanded* index set
`expandFin I J` (meet block ↦ all of `I`), using tightness for the size bookkeeping. -/
theorem replaceMeetFin_isVStar {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (_hk : 1 ≤ k) (hV : IsVStar V k) (htight : tightConstraint V k I hI) :
    IsVStar (replaceMeetFin V I hI) k := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- (i) weight ≤ k-1
    intro q
    show vAbs (replaceMeet V I hI ((replaceEquiv I).symm q)) ≤ k - 1
    rcases (replaceEquiv I).symm q with a | i
    · show vAbs (vMeet V I hI) ≤ k - 1
      obtain ⟨i₀, hi₀⟩ := id hI
      exact le_trans (vAbs_vMeet_le_mem hI hi₀) (hV.weight_le i₀)
    · exact hV.weight_le i.1
  · -- (ii) MDS via expansion
    intro J hJ
    rw [sum_replaceMeetFin hI htight J, vMeet_replaceMeetFin hI hJ]
    exact hV.mds (expandFin I J) _
  · -- (iii) shape: meet ≤ each member, members ≤ 1 on interior coords
    intro q l hl
    show replaceMeet V I hI ((replaceEquiv I).symm q) l ≤ 1
    rcases (replaceEquiv I).symm q with a | i
    · show vMeet V I hI l ≤ 1
      obtain ⟨i₀, hi₀⟩ := id hI
      exact le_trans (vMeet_le_mem hI hi₀ l) (hV.shape i₀ l hl)
    · exact hV.shape i.1 l hl

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.vAbs_vMeet_le_mem
#print axioms ArkLib.GMMDS.replaceMeet_card
#print axioms ArkLib.GMMDS.lovettD_replaceMeet
#print axioms ArkLib.GMMDS.vMeet_replaceMeetFin
#print axioms ArkLib.GMMDS.sum_replaceMeetFin
#print axioms ArkLib.GMMDS.replaceMeetFin_isVStar
