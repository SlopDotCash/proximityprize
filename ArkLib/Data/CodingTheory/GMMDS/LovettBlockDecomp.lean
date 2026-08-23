/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettBlockDim
import ArkLib.Data.CodingTheory.GMMDS.LovettMeetReplace
import ArkLib.Data.CodingTheory.GMMDS.LovettCounting
import ArkLib.Data.CodingTheory.GMMDS.LovettBaseCase
import ArkLib.Data.CodingTheory.GMMDS.LovettFractionField
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma2456

/-!
# Lovett's GM-MDS proof: the range decomposition closing Lemma 2.4 (#389)

This file performs the *range-decomposition plumbing* that discharges the corrected residual
`Lemma24SpanTransferWithIBlock` (see [[LovettLemma24Finish]]), thereby fully closing the algebraic
finish of Lovett's Lemma 2.4 (arXiv:1803.02523, p.8–9), and then derives the classification
`tightConstraint ∧ IsVStar ⟹ |I| ∈ {1, m}`.

The meet-replacement system `V' = replaceMeetFin V I hI` (built in [[LovettMeetReplace]]) replaces
the entire `I`-block of `V` by the single coordinate-wise meet `v_I = ⋀_{i∈I} vᵢ`, keeping every
vector outside `I`.  Everything happens over the **fraction field** `K = F(a) = Frac(F[a])`, reached
from the ring `R = F[a] = MvPolynomial (Fin n) F` via [[LovettFractionField]] (the field is needed
for the basis-counting step — a spanning set of size `=` dimension is independent).

The families `P(k,V) = pFamUnion V k` and `P(k,V') = pFamUnion V' k` decompose as

> `P(k,V)  = (shared blocks, i ∉ I)  ⊔  (I-block, i ∈ I)`
> `P(k,V') = (shared blocks, i ∉ I)  ⊔  (meet block, v_I)`,

with the shared blocks *pointwise identical*.  The two key span facts (over `K`):

* `iBlock_span_eq_meetBlock_K` — the `I`-block and the meet block span the **same** `K`-subspace.
  Forward (`I`-block ⊆ meet block) maps from the unconditional ring fact
  (`pFamUnion_I_mem_span_meetBlock`); the reverse is the dimension count
  (`span_eq_of_le_of_card_of_indep` over `K`) which needs the `I`-block independent — the genuine
  extra input of Lemma 2.4, threaded as a hypothesis (supplied at the call site by the
  `d`-induction hypothesis on the `I`-subsystem).
* `pFamUnion_span_eq_replaceMeetFin_K` — hence `span P(k,V) = span P(k,V')` over `K`.

With equal cardinality (`lovettD_replaceMeet`, tightness) and `P(k,V')` independent (the `m`-IH),
`linearIndependent_of_span_eq_card` transfers independence to `P(k,V)`.  This proves
`Lemma24SpanTransferWithIBlock`, and the classification follows.

Issue #389.
-/

open Polynomial Finset Submodule

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-! ## The base-change map `Φ : R[X] → K[X]` -/

/-- The coefficient base-change `R[X] →ₗ[R] K[X]` with `R = F[a]`, `K = F(a) = Frac(R)`. -/
noncomputable abbrev phiX (F : Type*) [Field F] (n : ℕ) :
    (MvPolynomial (Fin n) F)[X] →ₗ[MvPolynomial (Fin n) F]
      (FractionRing (MvPolynomial (Fin n) F))[X] :=
  (Polynomial.mapAlgHom (Algebra.ofId (MvPolynomial (Fin n) F)
    (FractionRing (MvPolynomial (Fin n) F)))).toLinearMap

/-- `Φ` applied to a member of an `R`-span lands in the `K`-span of the `Φ`-image. -/
theorem phiX_mem_span_image {x : (MvPolynomial (Fin n) F)[X]}
    {S : Set (MvPolynomial (Fin n) F)[X]}
    (hx : x ∈ Submodule.span (MvPolynomial (Fin n) F) S) :
    phiX F n x ∈ Submodule.span (FractionRing (MvPolynomial (Fin n) F)) (phiX F n '' S) := by
  have h1 : phiX F n x ∈
      Submodule.span (MvPolynomial (Fin n) F) (phiX F n '' S) :=
    Submodule.image_span_subset_span (phiX F n) S ⟨x, hx, rfl⟩
  exact Submodule.span_subset_span (MvPolynomial (Fin n) F)
    (FractionRing (MvPolynomial (Fin n) F)) _ h1

/-- The `Φ`-image of a range is the range of the composed family. -/
theorem phiX_image_range {ι : Type*} (g : ι → (MvPolynomial (Fin n) F)[X]) :
    phiX F n '' Set.range g = Set.range (fun i => phiX F n (g i)) := by
  rw [← Set.range_comp]; rfl

/-! ## The `I`-block family and its cardinality -/

/-- The `I`-block family of `P(k,V)`: the subfamily over the indices `i ∈ I`,
`{ pFam vᵢ e : i ∈ I, e < k − |vᵢ| }`. -/
noncomputable def iBlock (V : Fin m → (Fin n → ℕ)) (k : ℕ) (I : Finset (Fin m)) :
    (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1))) → (MvPolynomial (Fin n) F)[X] :=
  fun p => pFam (F := F) (V p.1.1) (p.2 : ℕ)

/-- The cardinality of the `I`-block index type is `Σ_{i∈I}(k − |vᵢ|)`. -/
theorem card_iBlock_index (V : Fin m → (Fin n → ℕ)) (k : ℕ) (I : Finset (Fin m)) :
    Fintype.card (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1))) = ∑ i ∈ I, (k - vAbs (V i)) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_coe_sort I (fun i => k - vAbs (V i))]

/-- Under tightness (and `|v_I| ≤ k`), the `I`-block index cardinality equals the meet-block size
`k − |v_I|`. -/
theorem card_iBlock_eq_meet {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (htight : tightConstraint V k I hI) :
    Fintype.card (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1)))
      = k - vAbs (vMeet V I hI) := by
  rw [card_iBlock_index]
  unfold tightConstraint at htight
  omega

/-! ## The `I`-block and the meet block span the same `K`-subspace -/

/-- **The `I`-block and the meet block span the same `K`-subspace.**  Forward inclusion maps from
the unconditional ring fact; the reverse is the dimension count over `K`, requiring the `I`-block to
be independent over `R` (`hIblock`) — Lovett's genuine extra input. -/
theorem iBlock_span_eq_meetBlock_K {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (hV : IsVStar V k) (htight : tightConstraint V k I hI)
    (hIblock : LinearIndependent (MvPolynomial (Fin n) F) (iBlock (F := F) V k I)) :
    Submodule.span (FractionRing (MvPolynomial (Fin n) F))
        (Set.range (fun p => phiX F n (iBlock (F := F) V k I p)))
      = Submodule.span (FractionRing (MvPolynomial (Fin n) F))
          (Set.range (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s))) := by
  classical
  set K := FractionRing (MvPolynomial (Fin n) F)
  -- the meet block is independent over R, hence over K
  have hMeetR : LinearIndependent (MvPolynomial (Fin n) F)
      (meetBlock (F := F) (vMeet V I hI) k) := by
    unfold meetBlock
    exact pFam_single_linearIndependent (vMeet V I hI) (k - vAbs (vMeet V I hI))
  have hMeetK : LinearIndependent K
      (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s)) :=
    (linearIndependent_fractionField_iff _).mp hMeetR
  have hIblockK : LinearIndependent K
      (fun p => phiX F n (iBlock (F := F) V k I p)) :=
    (linearIndependent_fractionField_iff _).mp hIblock
  -- weight bound on the meet ≤ k
  have hwk : ∀ i ∈ I, vAbs (V i) ≤ k := fun i _ => le_trans (hV.weight_le i) (Nat.sub_le k 1)
  -- forward inclusion over K: span (Φ I-block) ≤ span (Φ meet block)
  have hle : Submodule.span K (Set.range (fun p => phiX F n (iBlock (F := F) V k I p)))
      ≤ Submodule.span K
          (Set.range (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s))) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    -- iBlock p ∈ span_R (range meetBlock)  (the ring forward inclusion)
    have hR : iBlock (F := F) V k I p ∈
        Submodule.span (MvPolynomial (Fin n) F)
          (Set.range (meetBlock (F := F) (vMeet V I hI) k)) :=
      pFamUnion_I_mem_span_meetBlock hI p.1.2 (hwk p.1.1 p.1.2) (p.2 : ℕ) p.2.2
    have := phiX_mem_span_image (F := F) (n := n) hR
    rwa [phiX_image_range] at this
  -- equal cardinality
  have hcard : Fintype.card (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1)))
      = Fintype.card (Fin (k - vAbs (vMeet V I hI))) := by
    rw [card_iBlock_eq_meet hI htight, Fintype.card_fin]
  exact ArkLib.GMMDS.span_eq_of_le_of_card_of_indep hle hcard hIblockK hMeetK

/-! ## The Sum-indexed form of `P(k, V')` and the full span equality -/

/-- The `ReplaceIdx`-indexed (un-reindexed) family `P(k, V')`: `pFam (replaceMeet p) e`. -/
noncomputable def gSum (V : Fin m → (Fin n → ℕ)) (k : ℕ) (I : Finset (Fin m)) (hI : I.Nonempty) :
    (Σ p : ReplaceIdx I, Fin (k - vAbs (replaceMeet V I hI p))) → (MvPolynomial (Fin n) F)[X] :=
  fun p => pFam (F := F) (replaceMeet V I hI p.1) (p.2 : ℕ)

/-- The `Φ`-range of `P(k, V')` equals the `Φ`-range of its `Sum`-indexed form `gSum`
(reindexing the base by `replaceEquiv I`). -/
theorem phiX_range_pFamUnion_replaceMeetFin {V : Fin m → (Fin n → ℕ)} {k : ℕ}
    {I : Finset (Fin m)} (hI : I.Nonempty) :
    Set.range (fun p => phiX F n (pFamUnion (F := F) (replaceMeetFin V I hI) k p))
      = Set.range (fun p => phiX F n (gSum (F := F) V k I hI p)) := by
  classical
  -- the base reindex equiv on the sigma
  let e : (Σ q : Fin ((m - I.card) + 1), Fin (k - vAbs (replaceMeetFin V I hI q)))
      ≃ (Σ p : ReplaceIdx I, Fin (k - vAbs (replaceMeet V I hI p))) :=
    Equiv.sigmaCongrLeft (β := fun p => Fin (k - vAbs (replaceMeet V I hI p))) (replaceEquiv I).symm
  have hcomp : (fun p => phiX F n (pFamUnion (F := F) (replaceMeetFin V I hI) k p))
      = (fun p => phiX F n (gSum (F := F) V k I hI p)) ∘ e := by
    funext q
    rfl
  rw [hcomp, EquivLike.range_comp]

/-- **The full span equality** (over `K = F(a)`): `P(k,V)` and `P(k,V')` span the same `K`-subspace.
Decompose both into shared blocks (`i ∉ I`, pointwise identical) plus the `I`-block resp. the meet
block, which span the same subspace (`iBlock_span_eq_meetBlock_K`). -/
theorem pFamUnion_span_eq_replaceMeetFin_K {V : Fin m → (Fin n → ℕ)} {k : ℕ}
    {I : Finset (Fin m)} (hI : I.Nonempty) (hV : IsVStar V k) (htight : tightConstraint V k I hI)
    (hIblock : LinearIndependent (MvPolynomial (Fin n) F) (iBlock (F := F) V k I)) :
    Submodule.span (FractionRing (MvPolynomial (Fin n) F))
        (Set.range (fun p => phiX F n (pFamUnion (F := F) V k p)))
      = Submodule.span (FractionRing (MvPolynomial (Fin n) F))
          (Set.range (fun p => phiX F n (pFamUnion (F := F) (replaceMeetFin V I hI) k p))) := by
  classical
  set K := FractionRing (MvPolynomial (Fin n) F)
  set g := fun p => phiX F n (pFamUnion (F := F) V k p) with hg
  set g' := fun p => phiX F n (pFamUnion (F := F) (replaceMeetFin V I hI) k p) with hg'
  -- the I-block / meet-block K-span equality
  have hblock := iBlock_span_eq_meetBlock_K (F := F) hI hV htight hIblock
  -- g'-range = gSum-range
  have hg'range : Set.range g' = Set.range (fun p => phiX F n (gSum (F := F) V k I hI p)) :=
    phiX_range_pFamUnion_replaceMeetFin hI
  -- meet-block elements are V'-generators (via gSum, inl block)
  have hmeet_sub_g' : Set.range (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s))
      ⊆ Set.range g' := by
    rw [hg'range]
    rintro _ ⟨s, rfl⟩
    -- meetBlock s = pFam vMeet s = gSum ⟨inl 0, s⟩
    refine ⟨⟨Sum.inl 0, s⟩, ?_⟩
    simp only [gSum, meetBlock, replaceMeet, Sum.elim_inl]
  -- I-block elements are V-generators (i ∈ I)
  have hiblock_sub_g : Set.range (fun p => phiX F n (iBlock (F := F) V k I p)) ⊆ Set.range g := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨p.1.1, p.2⟩, rfl⟩
  refine le_antisymm ?_ ?_
  · -- span g ≤ span g'
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, e⟩, rfl⟩
    by_cases hi : i ∈ I
    · -- I-block element: in span (Φ meet block) ⊆ span g'
      have hmem : phiX F n (pFamUnion (F := F) V k ⟨i, e⟩)
          ∈ Submodule.span K (Set.range
              (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s))) := by
        rw [← hblock]
        exact Submodule.subset_span ⟨⟨⟨i, hi⟩, e⟩, rfl⟩
      exact Submodule.span_mono hmeet_sub_g' hmem
    · -- shared element (i ∉ I): a V'-generator
      apply Submodule.subset_span
      rw [hg'range]
      refine ⟨⟨Sum.inr ⟨i, hi⟩, e⟩, ?_⟩
      simp only [gSum, replaceMeet, Sum.elim_inr]
      rfl
  · -- span g' ≤ span g
    rw [hg'range, Submodule.span_le]
    rintro _ ⟨⟨p, e⟩, rfl⟩
    cases p with
    | inl a =>
      -- meet-block element: in span (Φ I-block) ⊆ span g
      have hmem : phiX F n (gSum (F := F) V k I hI ⟨Sum.inl a, e⟩)
          ∈ Submodule.span K (Set.range
              (fun s => phiX F n (meetBlock (F := F) (vMeet V I hI) k s))) := by
        apply Submodule.subset_span
        refine ⟨e, ?_⟩
        simp only [gSum, meetBlock, replaceMeet, Sum.elim_inl]
      rw [← hblock] at hmem
      exact Submodule.span_mono hiblock_sub_g hmem
    | inr i =>
      -- surviving element (i ∉ I): a V-generator
      apply Submodule.subset_span
      refine ⟨⟨i.1, e⟩, ?_⟩
      simp only [gSum, replaceMeet, Sum.elim_inr]
      rfl

/-- **Lemma 2.4 span-transfer residual, discharged.**  The corrected residual
`Lemma24SpanTransferWithIBlock` (see [[LovettLemma24Finish]]) is provable: given the `I`-block
independent (the `d`-IH input) and `P(k, V')` independent (the `m`-IH), `P(k, V)` is independent. -/
theorem lemma24SpanTransferWithIBlock_holds :
    Lemma24SpanTransferWithIBlock F := by
  intro n m V k I hI hk hV htight hlo hhi hIblock hV'
  -- transfer to the field
  rw [LovettHolds, linearIndependent_fractionField_iff]
  -- P(k,V') independent over K
  rw [LovettHolds, linearIndependent_fractionField_iff] at hV'
  -- equal cardinality of the index types
  have hcard : Fintype.card (Σ i : Fin m, Fin (k - vAbs (V i)))
      = Fintype.card (Σ q : Fin ((m - I.card) + 1),
          Fin (k - vAbs (replaceMeetFin V I hI q))) := by
    rw [card_pFamUnion_index, card_pFamUnion_index]
    have := lovettD_replaceMeet hI htight
    unfold lovettD at this
    rw [this]
  -- span equality over K
  have hspan := pFamUnion_span_eq_replaceMeetFin_K (F := F) hI hV htight hIblock
  exact linearIndependent_of_span_eq_card hspan hcard hV'

/-! ## The `I`-block independence from the `d`-induction hypothesis -/

/-- The `I`-block of `V` equals (the reindexing of) `pFamUnion (V ∘ σ) k` for the enumeration
`σ : Fin (card {i // i ∈ I}) → Fin m` of `I`. -/
theorem iBlock_eq_pFamUnion_comp {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)} :
    LinearIndependent (MvPolynomial (Fin n) F) (iBlock (F := F) V k I) ↔
      LinearIndependent (MvPolynomial (Fin n) F)
        (pFamUnion (F := F)
          (fun q : Fin (Fintype.card {i // i ∈ I}) =>
            V ((Fintype.equivFin {i // i ∈ I}).symm q).1) k) := by
  classical
  set e := (Fintype.equivFin {i // i ∈ I}).symm with he
  -- the sigma base-reindex equiv
  let σ : (Σ q : Fin (Fintype.card {i // i ∈ I}), Fin (k - vAbs (V (e q).1)))
      ≃ (Σ i : {i // i ∈ I}, Fin (k - vAbs (V i.1))) :=
    Equiv.sigmaCongrLeft (β := fun i : {i // i ∈ I} => Fin (k - vAbs (V i.1))) e
  have hcomp : pFamUnion (F := F) (fun q => V (e q).1) k
      = iBlock (F := F) V k I ∘ σ := by
    funext q; rfl
  rw [hcomp, linearIndependent_equiv σ]

/-- **The `I`-block is independent, from the `d`-induction hypothesis.**  For a tight `I` with
`1 < |I| < m`, the `I`-subsystem `V ∘ σ` is `V*(k)` (`isVStar_comp`) with measure
`Σ_{i∈I}(k − |vᵢ|) < lovettD V k` (since `|I| < m` leaves ≥ 1 surviving positive block), so the
`d`-IH applies and gives the `I`-block independent. -/
theorem iBlock_indep_of_dIH {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (hk : 1 ≤ k) (hV : IsVStar V k) (hhi : I.card < m)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) :
    LinearIndependent (MvPolynomial (Fin n) F) (iBlock (F := F) V k I) := by
  classical
  set e := (Fintype.equivFin {i // i ∈ I}).symm with he
  set W := fun q : Fin (Fintype.card {i // i ∈ I}) => V (e q).1 with hW
  -- W = V ∘ σ with σ injective
  have hσinj : Function.Injective (fun q => (e q).1) :=
    fun a b h => e.injective (Subtype.ext h)
  have hWstar : IsVStar W k := isVStar_comp hV hσinj
  -- measure of W = Σ_{i∈I}(k - |vᵢ|)
  have hWmeasure : lovettD W k = ∑ i ∈ I, (k - vAbs (V i)) := by
    unfold lovettD
    rw [Equiv.sum_comp e (fun i : {i // i ∈ I} => k - vAbs (V i.1))]
    rw [← Finset.sum_coe_sort I (fun i => k - vAbs (V i))]
  -- the measure is strictly smaller than lovettD V k (Iᶜ nonempty, terms ≥ 1)
  have hlt : lovettD W k < lovettD V k := by
    rw [hWmeasure]
    unfold lovettD
    rw [← Finset.sum_add_sum_compl I (fun i => k - vAbs (V i))]
    have hcompl : (Iᶜ : Finset (Fin m)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; omega
    obtain ⟨i₀, hi₀⟩ := hcompl
    have hpos : 1 ≤ k - vAbs (V i₀) := by
      have := hV.weight_le i₀; omega
    have hsum : 1 ≤ ∑ i ∈ Iᶜ, (k - vAbs (V i)) :=
      le_trans hpos (Finset.single_le_sum (f := fun i => k - vAbs (V i))
        (fun i _ => Nat.zero_le _) hi₀)
    omega
  -- apply the d-IH to W, then reindex back to the I-block
  have hWindep : LovettHolds F W k := IHd W hlt hWstar
  rw [iBlock_eq_pFamUnion_comp]
  exact hWindep

/-! ## Lemma 2.4: the tight case is independent, and the classification -/

/-- **Lovett's Lemma 2.4 — the tight case `1 < |I| < m` is independent (self-contained).**  Given
the master frame's `d`-IH (`IHd`) and `m`-IH (`IHm`), a `V*(k)` system with a tight set `I`,
`1 < |I| < m`, satisfies `LovettHolds`: the `I`-block is independent by `IHd` (the `I`-subsystem has
smaller measure), the meet-replacement is independent by `IHm` (equal measure, fewer vectors), and
the span-transfer (`lemma24SpanTransferWithIBlock_holds`) closes it. -/
theorem lovettHolds_of_tight {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (hk : 1 ≤ k) (hV : IsVStar V k) (htight : tightConstraint V k I hI)
    (hlo : 1 < I.card) (hhi : I.card < m)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k)
    (IHm : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) :
    LovettHolds F V k := by
  have hIblock := iBlock_indep_of_dIH (F := F) hI hk hV hhi IHd
  have hV' := lovettHolds_replaceMeetFin hI hk hV htight hlo IHm
  exact lemma24SpanTransferWithIBlock_holds V k I hI hk hV htight hlo hhi hIblock hV'

/-- **Lovett's Lemma 2.4 (classification).**  In a minimal counterexample to Theorem 1.7 (`V*(k)`
with `¬ LovettHolds`), every tight constraint `I` has `|I| = 1` or `|I| = m`: a tight set with
`1 < |I| < m` would force `LovettHolds` (`lovettHolds_of_tight`), contradicting the counterexample.

This is the exact form `arXiv:1803.02523` Lemma 2.4 states; it is consumed by the merge-branch
clause-(ii) verification (`mergeSys_mds` at all index sets). -/
theorem tight_card_eq_one_or_m {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (hk : 1 ≤ k) (hV : IsVStar V k) (htight : tightConstraint V k I hI)
    (hcex : ¬ LovettHolds F V k)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k)
    (IHm : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) :
    I.card = 1 ∨ I.card = m := by
  -- I is nonempty so |I| ≥ 1; and |I| ≤ m always.
  have hlo : 1 ≤ I.card := Finset.Nonempty.card_pos hI
  have hhi : I.card ≤ m := by
    have := Finset.card_le_univ I; simpa [Fintype.card_fin] using this
  -- rule out the strict interior 1 < |I| < m
  rcases Nat.lt_or_ge 1 I.card with h1 | h1
  · rcases Nat.lt_or_ge I.card m with h2 | h2
    · exact absurd (lovettHolds_of_tight hI hk hV htight h1 h2 IHd IHm) hcex
    · exact Or.inr (le_antisymm hhi h2)
  · exact Or.inl (le_antisymm h1 hlo)

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.phiX_mem_span_image
#print axioms ArkLib.GMMDS.card_iBlock_index
#print axioms ArkLib.GMMDS.card_iBlock_eq_meet
#print axioms ArkLib.GMMDS.iBlock_span_eq_meetBlock_K
#print axioms ArkLib.GMMDS.phiX_range_pFamUnion_replaceMeetFin
#print axioms ArkLib.GMMDS.pFamUnion_span_eq_replaceMeetFin_K
#print axioms ArkLib.GMMDS.lemma24SpanTransferWithIBlock_holds
#print axioms ArkLib.GMMDS.iBlock_eq_pFamUnion_comp
#print axioms ArkLib.GMMDS.iBlock_indep_of_dIH
#print axioms ArkLib.GMMDS.lovettHolds_of_tight
#print axioms ArkLib.GMMDS.tight_card_eq_one_or_m
