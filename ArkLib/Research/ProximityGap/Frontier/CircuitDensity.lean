/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors

/-! # Multiplicity of local interpolation failures in an MCA witness

A noninterpolable received word on a set of size t fails interpolation on at
least (t-1).choose k subsets of size k+1. Each such subset inside a witness
for an affine line determines the bad scalar uniquely.
-/

set_option autoImplicit false
namespace ProximityGap.CircuitDensity
open Finset
open scoped NNReal
variable {I A : Type} [DecidableEq I]

private def Fits (C : Set (I → A)) (u : I → A) (S : Finset I) : Prop :=
  ∃ c ∈ C, ∀ i ∈ S, c i = u i

omit [DecidableEq I] in
private theorem fits_mono {C : Set (I → A)} {u : I → A} {S T : Finset I}
    (h : Fits C u T) (hST : S ⊆ T) : Fits C u S := by
  obtain ⟨c,hc,h⟩ := h
  exact ⟨c,hc,fun i hi => h i (hST hi)⟩

open Classical in
/-- If agreement on k points determines a codeword, every inconsistent set of size t
contains at least (t-1).choose k inconsistent subsets of size k+1. -/
theorem detecting_density (C : Set (I → A)) (u : I → A) (S : Finset I) (k : ℕ)
    (huniq : ∀ c ∈ C, ∀ d ∈ C, ∀ T : Finset I, k ≤ T.card →
      (∀ i ∈ T, c i = d i) → c = d)
    (hs : S.Nonempty) (hn : ¬ ∃ c ∈ C, ∀ i ∈ S, c i = u i) :
    (S.card-1).choose k ≤ ((S.powersetCard (k+1)).filter
      (fun U => ¬ ∃ c ∈ C, ∀ i ∈ U, c i = u i)).card := by
  classical
  obtain ⟨x,hx⟩ := hs
  let family := (S.erase x).powersetCard k
  have extend (T : Finset I) (hT : T ∈ family) :
      ∃ y ∈ S, y ∉ T ∧ ¬ Fits C u (insert y T) ∧ (y = x ∨ Fits C u (insert x T)) := by
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hT
    have hxt : x ∉ T := fun h => (notMem_erase x S) (hsub h)
    by_cases hfit : Fits C u (insert x T)
    · obtain ⟨c,hc,hmatch⟩ := hfit
      obtain ⟨y,hy,hm⟩ : ∃ y ∈ S, c y ≠ u y := by
        by_contra! h
        exact hn ⟨c,hc,h⟩
      have hyt : y ∉ T := fun h => hm (hmatch y (mem_insert_of_mem h))
      refine ⟨y,hy,hyt,?_,Or.inr ⟨c,hc,hmatch⟩⟩
      rintro ⟨d,hd,hdmatch⟩
      have he := huniq c hc d hd T hcard.ge (fun i hi =>
        (hmatch i (mem_insert_of_mem hi)).trans (hdmatch i (mem_insert_of_mem hi)).symm)
      exact hm (he ▸ hdmatch y (mem_insert_self ..))
    · exact ⟨x,hx,hxt,hfit,Or.inl rfl⟩
  let : Nonempty I := ⟨x⟩
  choose! y hys hyt hbad hside using extend
  let out (T : Finset I) := insert (y T) T
  have hi : Set.InjOn out (↑family : Set (Finset I)) := by
    intro T hT V hV he
    have hTS := (mem_powersetCard.mp hT).1
    have hVS := (mem_powersetCard.mp hV).1
    have hxt : x ∉ T := fun h => (notMem_erase x S) (hTS h)
    have hxv : x ∉ V := fun h => (notMem_erase x S) (hVS h)
    change insert (y T) T = insert (y V) V at he
    have hyeq (h : y T = y V) : T = V := by
      simpa [h, hyt V hV, show y V ∉ T by simpa only [← h] using hyt T hT] using
        congrArg (fun U : Finset I => U.erase (y V)) he
    by_contra hne
    have hd : y T ≠ y V := fun h => hne (hyeq h)
    have ha : y T ∈ V := (mem_insert.mp (he ▸ mem_insert_self (y T) T)).resolve_left hd
    have hb : y V ∈ T := (mem_insert.mp (he.symm ▸ mem_insert_self (y V) V)).resolve_left hd.symm
    obtain ⟨c,hc,hcfit⟩ := (hside T hT).resolve_left (fun h => hxv (h ▸ ha))
    obtain ⟨d,hd',hdfit⟩ := (hside V hV).resolve_left (fun h => hxt (h ▸ hb))
    let core := insert x (T.erase (y V))
    have hcard : k ≤ core.card := by
      rw [show core.card = (T.erase (y V)).card+1 by
        exact card_insert_of_notMem (fun h => hxt (mem_of_mem_erase h))]
      rw [card_erase_of_mem hb, (mem_powersetCard.mp hT).2]
      have hpos : 0 < k := (mem_powersetCard.mp hT).2 ▸ card_pos.mpr ⟨_,hb⟩
      omega
    have heq : c = d := huniq c hc d hd' core hcard (by
      intro i hi
      rcases mem_insert.mp hi with rfl | h
      · exact (hcfit _ (mem_insert_self ..)).trans (hdfit _ (mem_insert_self ..)).symm
      · obtain ⟨hin,hit⟩ := mem_erase.mp h
        have hiv : i ∈ V := (mem_insert.mp (he ▸ (show i ∈ insert (y T) T from mem_insert_of_mem hit))).resolve_left hin
        exact (hcfit i (mem_insert_of_mem hit)).trans (hdfit i (mem_insert_of_mem hiv)).symm)
    apply hbad T hT
    refine ⟨c,hc,fun i hi => ?_⟩
    rcases mem_insert.mp hi with rfl | h
    · exact heq ▸ hdfit _ (mem_insert_of_mem ha)
    · exact hcfit _ (mem_insert_of_mem h)
  have sub : family.image out ⊆ (S.powersetCard (k+1)).filter (fun U => ¬ Fits C u U) := by
    intro W hW
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hW
    obtain ⟨hTS,hcard⟩ := mem_powersetCard.mp hT
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨insert_subset (hys T hT) (hTS.trans (erase_subset ..)), ?_⟩,
      hbad T hT⟩
    simp [out, hyt T hT, hcard]
  have hle := card_le_card sub
  rw [card_image_of_injOn hi, show family.card = (S.card-1).choose k by
    simp only [family, card_powersetCard, card_erase_of_mem hx]] at hle
  exact hle


variable {F : Type} [Field F]

omit [DecidableEq I] in
private theorem direction_fits_of_two (C : Submodule F (I → F)) (u₀ u₁ : I → F)
    (U : Finset I) {γ β : F} (hne : γ ≠ β)
    (hγ : Fits (C : Set (I → F)) (fun i => u₀ i + γ * u₁ i) U)
    (hβ : Fits (C : Set (I → F)) (fun i => u₀ i + β * u₁ i) U) :
    Fits (C : Set (I → F)) u₁ U := by
  obtain ⟨v,hv,hvfit⟩ := hγ
  obtain ⟨w,hw,hwfit⟩ := hβ
  refine ⟨(γ-β)⁻¹ • (v-w), C.smul_mem _ (C.sub_mem hv hw), ?_⟩
  intro i hi
  change (γ-β)⁻¹ * (v i - w i) = u₁ i
  rw [hvfit i hi, hwfit i hi]
  rw [show u₀ i + γ*u₁ i - (u₀ i + β*u₁ i) = (γ-β)*u₁ i by ring]
  exact inv_mul_cancel_left₀ (sub_ne_zero.mpr hne) _

open Classical in
/-- Every bad scalar owns (t−1).choose k distinct circuits. The argument works on
arbitrary injective evaluation domains and does not need a global farness premise. -/
private theorem mca_count_mul_le_of_nonfitting [Fintype I] [Fintype F] [DecidableEq F]
    (dom : I ↪ F) (k t : ℕ) (δ : ℝ≥0) (u₀ u₁ : I → F) (ht : 0 < t)
    (hδ : ∀ S : Finset I, (1-δ) * (Fintype.card I : ℝ≥0) ≤ S.card → ¬ Fits (ReedSolomon.code dom k : Set (I → F)) u₁ S → t ≤ S.card) :
    (univ.filter (mcaEvent (F := F) (ReedSolomon.code dom k : Set (I → F)) δ u₀ u₁)).card *
      (t-1).choose k ≤ (Fintype.card I).choose (k+1) := by
  classical
  let C := ReedSolomon.code dom k
  let B := univ.filter (mcaEvent (F := F) (C : Set (I → F)) δ u₀ u₁)
  have witness (γ : F) (hγ : γ ∈ B) : ∃ S : Finset I, t ≤ S.card ∧
      Fits (C : Set (I → F)) (fun i => u₀ i + γ*u₁ i) S ∧ ¬ Fits (C : Set (I → F)) u₁ S := by
    obtain ⟨S,hs,⟨w,hw,hfit⟩,hnj⟩ := (mem_filter.mp hγ).2
    have hfail : ¬ Fits (C : Set (I → F)) u₁ S := by
      rintro ⟨c,hc,hcfit⟩
      apply hnj
      refine ⟨w-γ • c,C.sub_mem hw (C.smul_mem γ hc),c,hc,fun i hi => ⟨?_,hcfit i hi⟩⟩
      change w i - γ*c i = u₀ i
      rw [hfit i hi, hcfit i hi]
      simp
    exact ⟨S, hδ S hs hfail, ⟨w,hw,hfit⟩, hfail⟩
  choose! S hsize hmix hnon using witness
  let slots (γ : F) := ((S γ).powersetCard (k+1)).filter (fun U => ¬ Fits (C : Set (I → F)) u₁ U)
  have hcount (γ : F) (hγ : γ ∈ B) : (t-1).choose k ≤ (slots γ).card := by
    have hsc : (S γ).Nonempty := card_pos.mp (ht.trans_le (hsize γ hγ))
    exact (Nat.choose_le_choose k (Nat.sub_le_sub_right (hsize γ hγ) 1)).trans
      (detecting_density (C : Set (I → F)) u₁ (S γ) k
        (fun _ hc _ hd _ hcard hag => ReedSolomon.eq_of_agree_of_card_le hc hd hcard hag)
        hsc (hnon γ hγ))
  have hd : (↑B : Set F).PairwiseDisjoint slots := by
    intro γ hγ β hβ hne
    apply disjoint_left.mpr
    intro U hU hV
    obtain ⟨hsub,hfail⟩ := mem_filter.mp hU
    have hsub' := (mem_filter.mp hV).1
    exact hfail (direction_fits_of_two C u₀ u₁ U hne
      (fits_mono (hmix γ hγ) (mem_powersetCard.mp hsub).1)
      (fits_mono (hmix β hβ) (mem_powersetCard.mp hsub').1))
  have hsub : B.biUnion slots ⊆ (univ : Finset I).powersetCard (k+1) := by
    intro U hU
    obtain ⟨γ,_,hs⟩ := mem_biUnion.mp hU
    exact mem_powersetCard.mpr ⟨subset_univ _, (mem_powersetCard.mp (mem_filter.mp hs).1).2⟩
  calc
    B.card * (t-1).choose k = ∑ _γ ∈ B, (t-1).choose k := by simp
    _ ≤ ∑ γ ∈ B, (slots γ).card := sum_le_sum hcount
    _ = (B.biUnion slots).card := (card_biUnion hd).symm
    _ ≤ (Fintype.card I).choose (k+1) := by simpa using card_le_card hsub

open Classical in
/-- Every bad scalar owns (t−1).choose k distinct circuits. The argument works on
arbitrary injective evaluation domains and does not need a global farness premise. -/
theorem mca_count_mul_le [Fintype I] [Fintype F] [DecidableEq F]
    (dom : I ↪ F) (k t : ℕ) (δ : ℝ≥0) (u₀ u₁ : I → F) (ht : 0 < t)
    (hδ : ∀ S : Finset I, (1-δ) * (Fintype.card I : ℝ≥0) ≤ S.card → t ≤ S.card) :
    (univ.filter (mcaEvent (F := F) (ReedSolomon.code dom k : Set (I → F)) δ u₀ u₁)).card *
      (t-1).choose k ≤ (Fintype.card I).choose (k+1) :=
  mca_count_mul_le_of_nonfitting dom k t δ u₀ u₁ ht (fun S hs _ => hδ S hs)

open Classical in
/-- At every radius the scalar count is at most the total number of circuits. -/
theorem mca_count_le_choose [Fintype I] [Fintype F] [DecidableEq F]
    (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) (u₀ u₁ : I → F) :
    (univ.filter (mcaEvent (F := F) (ReedSolomon.code dom k : Set (I → F)) δ u₀ u₁)).card
      ≤ (Fintype.card I).choose (k+1) := by
  classical
  have hδ (S : Finset I) (hn : ¬ Fits (ReedSolomon.code dom k : Set (I → F)) u₁ S) :
      k+1 ≤ S.card := by
    by_contra! hl
    let f := Lagrange.interpolate S dom u₁
    have hd : f.degree < (k : WithBot ℕ) :=
      (Lagrange.degree_interpolate_lt u₁ dom.injective.injOn).trans_le
        (by exact_mod_cast (show S.card ≤ k by omega))
    apply hn
    refine ⟨_, ReedSolomon.mem_code_iff_exists_polynomial.mpr ⟨f,hd,rfl⟩, ?_⟩
    intro i hi
    exact Lagrange.eval_interpolate_at_node u₁ dom.injective.injOn hi
  simpa using mca_count_mul_le_of_nonfitting dom k (k+1) δ u₀ u₁ (by omega) (fun S _ => hδ S)

/-- The affine-line MCA error is bounded by the quotient of circuit counts
divided by the field size. The natural division takes the floor. -/
theorem mcaError_le [Fintype I] [Nonempty I] [Fintype F] [DecidableEq F] [SampleableType F]
    (dom : I ↪ F) (k t : ℕ) (δ : ℝ≥0) (hkt : k < t)
    (hδ : ∀ S : Finset I, (1-δ) * (Fintype.card I : ℝ≥0) ≤ S.card → t ≤ S.card) :
    CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code dom k)
      (δ : ℝ) ≤ ENNReal.ofReal
        ((((Fintype.card I).choose (k+1) / (t-1).choose k : ℕ) : ℝ) / Fintype.card F) := by
  classical
  apply iSup_le
  intro u
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hu : ![u 0, u 1] = u := by
    funext j
    fin_cases j <;> rfl
  have hev (γ : F) := mcaEvent_iff_isMCA (ReedSolomon.code dom k) δ (u 0) (u 1) γ
  simp only [hu] at hev
  simp_rw [← hev]
  exact_mod_cast (Nat.le_div_iff_mul_le (Nat.choose_pos (by omega : k ≤ t-1))).mpr
    (mca_count_mul_le dom k t δ (u 0) (u 1) (by omega) hδ)

#print axioms mca_count_le_choose
#print axioms mcaError_le

#print axioms detecting_density
#print axioms mca_count_mul_le

end ProximityGap.CircuitDensity
