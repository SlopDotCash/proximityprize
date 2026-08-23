/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.GK16Claim16Witness
import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import Mathlib.FieldTheory.Finiteness

/-!
# GK16 Claim 16: structural encoder-isomorphism + adapted-basis transport (proven)

This file discharges the last structural residual of GK16 Claim 16 — the
*encoder-isomorphism + adapted-basis* transport that `GK16Claim16StructuralData`
(in `SubspaceDesign.lean`) packages — under the genuine, documented side conditions.

The core pieces are:

* `exists_adapted_finrankBasis` — a generic linear-algebra brick: any subspace `W` of a
  finite-dimensional space `V` admits a `Fin (finrank V)`-indexed basis of `V` together
  with a `finrank W`-element index set whose basis vectors lie in `W` (extend a basis of
  `W` to a basis of `V`).
* `exists_recombination_of_bases` — two `Fin n`-bases of a submodule `A'` of `F[X]` are
  related by an *invertible* `F`-linear recombination of polynomials (`bQ l = ∑ c l m • bP m`,
  `det c ≠ 0`).
* `preimageSubspace` and friends — the encoder-isomorphism transport: for `A ≤ frsCode` and
  the encoder injective, the polynomial pre-image subspace `A' := comap encoder A ⊓ degreeLT F k`
  satisfies `A'.map encoder = A` and `finrank A' = finrank A`, so a basis of `A'` is an
  independent realizing family `P : Fin (dim A) → F[X]` of degrees `< k`.
* `gk16Claim16StructuralData_at` — assembles the realizing family with, per coordinate, the
  adapted recombination and its `dim A_i`-element orbit-vanishing index set (under
  `dim A ≤ s`), i.e. the full existential body of `GK16Claim16StructuralData` for a single `A`.

The two side conditions are exactly the ones documented on `frs_is_subspaceDesign_gk16`:
encoder injectivity (`h_encoder_inj`, the `dim_frsCode` hypothesis) and the design-range
bound `dim A ≤ s` (so the `dim A` dilation exponents are genuine fold indices `< s`).
The `ω`-degree-separation admissibility (`hω_sep`) is threaded through as the third
conjunct of the structural data; the multiplicity-counting engine itself
(`claim16_rootMultiplicity_ge`) and Lemma 12 are already proven.

Everything here is `sorry`/axiom-clean.
-/

open Submodule Module Polynomial Matrix

namespace ArkLib.FRS.GK16

/-! ## Generic linear-algebra bricks -/

section LinearAlgebra

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **Extend a subspace basis to an adapted basis of the whole space.** For a subspace
`W ≤ V` of a finite-dimensional space, there is a `Fin (finrank V)`-indexed basis `b` of `V`
and a `finrank W`-element index set `T` with every `b l` (`l ∈ T`) lying in `W`. This is the
"extend a basis of `W` to a basis of `V`" fact, packaged with the `Fin`-reindexing and the
distinguished index set that the GK16 adapted-basis transport consumes. -/
theorem exists_adapted_finrankBasis (W : Submodule F V) :
    ∃ (b : Basis (Fin (finrank F V)) F V) (T : Finset (Fin (finrank F V))),
      T.card = finrank F W ∧ (∀ l ∈ T, b l ∈ W) := by
  classical
  set d := finrank F W with hd
  let bW : Basis (Fin d) F W := finBasis F W
  set wv : Fin d → V := fun i => (bW i : V) with hwv
  have hwv_inj : Function.Injective wv := fun a c h => bW.injective (Subtype.ext h)
  have hwv_indep : LinearIndependent F wv := bW.linearIndependent.map' W.subtype (by simp)
  set s : Set V := Set.range wv with hs_def
  have hsW : s ⊆ (W : Set V) := by
    rintro x ⟨i, rfl⟩; exact (bW i).2
  have hs : LinearIndepOn F id s := (linearIndepOn_id_range_iff hwv_inj).mpr hwv_indep
  have hs_card : s.toFinset.card = d := by
    rw [Set.toFinset_range, Finset.card_image_of_injective _ hwv_inj, Finset.card_univ,
      Fintype.card_fin]
  let E := hs.extend (Set.subset_univ s)
  let B : Basis (↥E) F V := Basis.extend hs
  have hBself : ∀ x : ↥E, B x = (x : V) := Basis.extend_apply_self hs
  have hfin : Fintype.card (↥E) = finrank F V := by rw [← Module.finrank_eq_card_basis B]
  let e : (↥E) ≃ Fin (finrank F V) := Fintype.equivFinOfCardEq hfin
  let b : Basis (Fin (finrank F V)) F V := B.reindex e
  have hsE : s ⊆ E := hs.subset_extend _
  have hb_apply : ∀ l, b l = ((e.symm l : ↥E) : V) := by
    intro l; rw [Basis.reindex_apply, hBself]
  have hs_range : s ⊆ Set.range b := by
    intro x hx
    refine ⟨e ⟨x, hsE hx⟩, ?_⟩
    rw [hb_apply]; simp
  refine ⟨b, Finset.univ.filter (fun l => b l ∈ s), ?_, ?_⟩
  · refine Eq.trans ?_ hs_card
    apply Finset.card_bij (fun l _ => b l)
    · intro l hl; rw [Finset.mem_filter] at hl; simpa using hl.2
    · intro l1 h1 l2 h2 heq; exact b.injective heq
    · intro x hx
      rw [Set.mem_toFinset] at hx
      obtain ⟨l, rfl⟩ := hs_range hx
      exact ⟨l, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩, rfl⟩
  · intro l hl
    rw [Finset.mem_filter] at hl
    exact hsW hl.2

end LinearAlgebra

/-! ## Recombination of two bases of a polynomial submodule -/

section Recombination

variable {F : Type*} [Field F]

/-- **Two bases of a polynomial submodule are an invertible recombination.** Given two
`Fin n`-indexed bases `bP`, `bQ` of a submodule `A' ≤ F[X]`, the change of coordinates
expressing `bQ` in `bP` is an *invertible* `F`-linear recombination of the underlying
polynomials: `bQ l = ∑ m, c l m • bP m` with `det c ≠ 0`. -/
theorem exists_recombination_of_bases {n : ℕ} (A' : Submodule F (Polynomial F))
    (bP bQ : Basis (Fin n) F A') :
    ∃ c : Fin n → Fin n → F, (Matrix.of c).det ≠ 0 ∧
      (∀ l, ((bQ l : Polynomial F)) = ∑ m, c l m • ((bP m : Polynomial F))) := by
  classical
  refine ⟨fun l m => bP.repr (bQ l) m, ?_, ?_⟩
  · have heq : (Matrix.of (fun l m => bP.repr (bQ l) m))
        = (bP.toMatrix (fun l => (bQ l : A')))ᵀ := by
      ext l m
      simp [Basis.toMatrix_apply]
    rw [heq, Matrix.det_transpose]
    apply Matrix.det_ne_zero_of_left_inverse (B := bQ.toMatrix ⇑bP)
    rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
  · intro l
    have hsum : (∑ m, (bP.repr (bQ l) m) • (bP m)) = bQ l := bP.sum_repr (bQ l)
    have h2 := congrArg (Submodule.subtype A') hsum
    rw [map_sum] at h2
    simp only [map_smul, Submodule.subtype_apply] at h2
    exact h2.symm

end Recombination

/-! ## The polynomial pre-image subspace (encoder-isomorphism side) -/

open ReedSolomon.Folded

section FRS

variable {F : Type} [Field F] [DecidableEq F] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The polynomial pre-image subspace of a code subspace `A ≤ frsCode` inside `degreeLT F k`:
`A' := comap encoder A ⊓ degreeLT F k`. Under encoder injectivity, `A' ≃ A` (so
`finrank A' = finrank A`) and `A'.map encoder = A`. -/
noncomputable def preimageSubspace (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (A : Submodule F (ι → Fin s → F)) : Submodule F (Polynomial F) :=
  A.comap (frsEvalOnPoints (ι := ι) (F := F) domain s ω) ⊓ Polynomial.degreeLT F k

/-- `(preimageSubspace A).map encoder = A` for `A ≤ frsCode` (every codeword is the
encoding of a degree-`< k` polynomial in the pre-image). -/
theorem preimageSubspace_map (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (A : Submodule F (ι → Fin s → F)) (hA_le : A ≤ frsCode (ι := ι) (F := F) domain k s ω) :
    (preimageSubspace domain k s ω A).map (frsEvalOnPoints (ι := ι) (F := F) domain s ω) = A := by
  apply le_antisymm
  · calc (preimageSubspace domain k s ω A).map (frsEvalOnPoints (ι := ι) (F := F) domain s ω)
          ≤ (A.comap (frsEvalOnPoints (ι := ι) (F := F) domain s ω)).map (frsEvalOnPoints (ι := ι) (F := F) domain s ω) :=
            Submodule.map_mono inf_le_left
      _ ≤ A := by rw [Submodule.map_comap_eq]; exact inf_le_right
  · intro x hx
    have hx' : x ∈ frsCode (ι := ι) (F := F) domain k s ω := hA_le hx
    rw [frsCode, Submodule.mem_map] at hx'
    obtain ⟨p, hp, rfl⟩ := hx'
    exact ⟨p, ⟨hx, hp⟩, rfl⟩

/-- Finite-dimensionality of the pre-image subspace (it is isomorphic to the finite-
dimensional code subspace `A` via the injective encoder). -/
theorem preimageSubspace_finiteDimensional (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hinj : Function.Injective (frsEvalOnPoints (ι := ι) (F := F) domain s ω))
    (A : Submodule F (ι → Fin s → F)) (hA_le : A ≤ frsCode (ι := ι) (F := F) domain k s ω) :
    FiniteDimensional F (preimageSubspace domain k s ω A) := by
  have e : (preimageSubspace domain k s ω A) ≃ₗ[F]
      ((preimageSubspace domain k s ω A).map (frsEvalOnPoints (ι := ι) (F := F) domain s ω)) :=
    Submodule.equivMapOfInjective _ hinj _
  rw [preimageSubspace_map domain k s ω A hA_le] at e
  exact Module.Finite.equiv e.symm

/-- `finrank (preimageSubspace A) = finrank A` under encoder injectivity. -/
theorem preimageSubspace_finrank (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hinj : Function.Injective (frsEvalOnPoints (ι := ι) (F := F) domain s ω))
    (A : Submodule F (ι → Fin s → F)) (hA_le : A ≤ frsCode (ι := ι) (F := F) domain k s ω) :
    finrank F (preimageSubspace domain k s ω A) = finrank F A := by
  have h := (Submodule.equivMapOfInjective (frsEvalOnPoints (ι := ι) (F := F) domain s ω) hinj
      (preimageSubspace domain k s ω A)).finrank_eq
  rw [preimageSubspace_map domain k s ω A hA_le] at h
  exact h

omit [DecidableEq ι] [DecidableEq F] in
theorem preimageSubspace_le_degreeLT (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (A : Submodule F (ι → Fin s → F)) :
    preimageSubspace domain k s ω A ≤ Polynomial.degreeLT F k := inf_le_right

omit [DecidableEq ι] [DecidableEq F] in
theorem preimageSubspace_mono (domain : ι ↪ F) (k s : ℕ) (ω : F)
    {A B : Submodule F (ι → Fin s → F)} (h : A ≤ B) :
    preimageSubspace domain k s ω A ≤ preimageSubspace domain k s ω B :=
  inf_le_inf_right _ (Submodule.comap_mono h)

omit [DecidableEq ι] [DecidableEq F] in
/-- A polynomial in the pre-image of the per-coordinate vanishing subspace `A ⊓ ker(eval_i)`
vanishes on the whole `s`-fold orbit `{domain i · ω^j : j < s}` of `domain i`. -/
theorem preimage_vanishes_on_orbit (domain : ι ↪ F) (k s : ℕ) (ω : F) (i : ι)
    (A : Submodule F (ι → Fin s → F)) (p : Polynomial F)
    (hp : p ∈ preimageSubspace domain k s ω (A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))) :
    ∀ j : Fin s, p.eval (domain i * ω ^ (j : ℕ)) = 0 := by
  intro j
  have hcomap : frsEvalOnPoints (ι := ι) (F := F) domain s ω p ∈ (A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) := hp.1
  have hker : frsEvalOnPoints (ι := ι) (F := F) domain s ω p ∈ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) := hcomap.2
  rw [LinearMap.mem_ker] at hker
  have hzero : (frsEvalOnPoints (ι := ι) (F := F) domain s ω p) i = 0 := hker
  have h2 : (frsEvalOnPoints (ι := ι) (F := F) domain s ω p) i j = 0 := by rw [hzero]; rfl
  simpa [frsEvalOnPoints] using h2

omit [DecidableEq ι] in
/-- Degree bound: a polynomial in `degreeLT F k` (with `k ≥ 1`) has `natDegree ≤ k - 1`. -/
theorem natDegree_le_of_mem_degreeLT {k : ℕ} (hk : 1 ≤ k) {p : Polynomial F}
    (hp : p ∈ Polynomial.degreeLT F k) : p.natDegree ≤ k - 1 := by
  rw [Polynomial.mem_degreeLT] at hp
  by_cases hp0 : p = 0
  · simp [hp0]
  · have hlt : (p.natDegree : WithBot ℕ) < (k : WithBot ℕ) := by
      rwa [← Polynomial.degree_eq_natDegree hp0]
    have h2 : p.natDegree < k := by exact_mod_cast hlt
    omega

/-! ## The structural data, assembled per subspace -/

/-- **GK16 Claim 16 structural data for a single subspace `A` (the genuinely-unwritten gap,
now written).** Under the two documented side conditions — encoder injectivity (`hinj`, the
`dim_frsCode` hypothesis) and the design-range bound `dim A ≤ s` (`hAs`) — together with the
`ω`-degree-separation admissibility (`hω_sep`, the hypothesis of
`foldedWronskian_ne_zero_of_linearIndependent`), this constructs the full existential package
of `GK16Claim16StructuralData` for the subspace `A`:

* the realizing family `P` is a basis of the polynomial pre-image subspace
  `A' := preimageSubspace ⋯ A ≤ degreeLT F k` (encoder isomorphism `A' ≃ A`), hence
  `F`-linearly independent with degrees `< k`;
* per coordinate `i`, the adapted recombination `Q^{(i)}` is a basis of `A'` extending a
  basis of the pre-image `A'_i := preimageSubspace ⋯ (A ⊓ ker(eval_i))` (so its first
  `dim A_i` members lie in `A'_i`); `c^{(i)}` is the invertible change of basis `P → Q^{(i)}`
  (`exists_recombination_of_bases`); `T_i` is the `dim A_i`-element index set of the adapted
  members. Each such member, lying in `A'_i`, vanishes on the whole `s`-fold orbit of
  `domain i` (`preimage_vanishes_on_orbit`); since `dim A ≤ s` the `dim A` dilation exponents
  `b : Fin (dim A)` are genuine fold indices `< s`, giving orbit-vanishing on the full
  `Fin (dim A)` dilation range as required.

This is `sorry`/axiom-clean. Composed with the proven multiplicity engine
`claim16_rootMultiplicity_ge` and Lemma 12, it discharges the per-coordinate budget for `A`
(see `SubspaceDesign.lean`). -/
theorem gk16Claim16StructuralData_at
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hinj : Function.Injective (frsEvalOnPoints domain s ω))
    (hk : 1 ≤ k)
    (A : Submodule F (ι → Fin s → F)) (hA_le : A ≤ frsCode domain k s ω)
    (hAs : finrank F A ≤ s)
    (hω_sep : ∀ Q : Fin (finrank F A) → Polynomial F, (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree)) :
    ∃ P : Fin (finrank F A) → Polynomial F,
      (∀ j, (P j).natDegree ≤ k - 1) ∧
      LinearIndependent F P ∧
      (∀ Q : Fin (finrank F A) → Polynomial F, (∀ j, Q j ≠ 0) →
          Function.Injective (fun j => (Q j).natDegree) →
          Function.Injective (fun j => ω ^ (Q j).natDegree)) ∧
      (∀ i : ι, ∃ (Q : Fin (finrank F A) → Polynomial F)
          (c : Fin (finrank F A) → Fin (finrank F A) → F)
          (T : Finset (Fin (finrank F A))),
        (Matrix.of c).det ≠ 0 ∧
        (∀ l, Q l = ∑ m, c l m • P m) ∧
        T.card = finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) ∧
        (∀ l ∈ T, ∀ b : Fin (finrank F A),
            (Q l).eval (domain i * ω ^ (b : ℕ)) = 0)) := by
  classical
  set n := finrank F A with hn
  set A' := preimageSubspace domain k s ω A with hA'def
  haveI : FiniteDimensional F A' := preimageSubspace_finiteDimensional domain k s ω hinj A hA_le
  have hA'rank : finrank F A' = n := preimageSubspace_finrank domain k s ω hinj A hA_le
  let bP : Basis (Fin n) F A' := finBasisOfFinrankEq F A' hA'rank
  set P : Fin n → Polynomial F := fun m => (bP m : Polynomial F) with hP
  have hA'D : A' ≤ Polynomial.degreeLT F k := preimageSubspace_le_degreeLT domain k s ω A
  have hP_deg : ∀ j, (P j).natDegree ≤ k - 1 := by
    intro j; exact natDegree_le_of_mem_degreeLT hk (hA'D (bP j).2)
  have hP_indep : LinearIndependent F P :=
    bP.linearIndependent.map' A'.subtype (by simp)
  refine ⟨P, hP_deg, hP_indep, hω_sep, ?_⟩
  intro i
  -- A_i and its polynomial pre-image A'_i ≤ A'.
  set Ai := A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hAi
  set A'i := preimageSubspace domain k s ω Ai with hA'i
  have hAi_le_A : Ai ≤ A := inf_le_left
  have hA'i_le_A' : A'i ≤ A' := preimageSubspace_mono domain k s ω hAi_le_A
  have hAi_le_frs : Ai ≤ frsCode domain k s ω := hAi_le_A.trans hA_le
  -- A'_i viewed as a subspace `W` of `A'`.
  set W : Submodule F A' := A'i.comap A'.subtype with hW
  have hW_finrank : finrank F W = finrank F Ai := by
    rw [hW, (Submodule.comapSubtypeEquivOfLe hA'i_le_A').finrank_eq,
      preimageSubspace_finrank domain k s ω hinj Ai hAi_le_frs]
  -- Adapted basis of `A'` (reindexed to `Fin n`) with its vanishing index set.
  obtain ⟨b0, T0, hcard0, hmem0⟩ := exists_adapted_finrankBasis W
  let eqv : Fin (finrank F A') ≃ Fin n := finCongr hA'rank
  let bQ : Basis (Fin n) F A' := b0.reindex eqv
  set T : Finset (Fin n) := T0.image eqv with hT
  have hT_card : T.card = finrank F Ai := by
    rw [hT, Finset.card_image_of_injective _ eqv.injective, hcard0, hW_finrank]
  -- The invertible recombination relating `bP` and `bQ`.
  obtain ⟨c, hc_det, hc_rec⟩ := exists_recombination_of_bases A' bP bQ
  set Q : Fin n → Polynomial F := fun l => (bQ l : Polynomial F) with hQ
  refine ⟨Q, c, T, hc_det, hc_rec, hT_card, ?_⟩
  -- Orbit-vanishing on the `n`-fold dilation range (`n ≤ s` ⟹ genuine fold indices).
  intro l hl b
  rw [hT, Finset.mem_image] at hl
  obtain ⟨l0, hl0, rfl⟩ := hl
  have hmemA'i : (bQ (eqv l0) : Polynomial F) ∈ A'i := by
    have hbq : bQ (eqv l0) = b0 l0 := by rw [Basis.reindex_apply, Equiv.symm_apply_apply]
    rw [hbq]; exact hmem0 l0 hl0
  have hfold : (b : ℕ) < s := lt_of_lt_of_le b.2 hAs
  have hvanish_s := preimage_vanishes_on_orbit domain k s ω i A
      (Q (eqv l0)) (by rw [hQ]; exact hmemA'i) ⟨(b : ℕ), hfold⟩
  simpa using hvanish_s

end FRS

end ArkLib.FRS.GK16
