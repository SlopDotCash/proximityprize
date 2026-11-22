/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DenseOddRedundancy
import ArkLib.Research.ProximityGap.Frontier.ProjectiveDomainMass

/-! # The odd predecessor for arbitrary multiplicative cosets -/

namespace ProximityGap.CosetOddRedundancy
open Finset ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A domain closed under a reflection of its multiplicative coordinates
acquires additive pairs on removing the fixed site and inverting. -/
theorem reciprocal_lower {n k h : ℕ} [NeZero n] (D : Fin n ↪ F) (j : Fin n)
    (nz : ∀ i, D i ≠ 0) (closed : ∀ i, ∃ l, D l=(D j)^2/D i)
    (length : n=k+2*h-1) (hk : 4≤k) (large : 3≤h) (odd : h%2=1) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  classical
  let a := D j
  have ha : a≠0 := nz j
  let T := (univ : Finset (Fin n)).erase j
  let N := n-1
  have card : T.card=N := by simp [T,N,card_erase_of_mem]
  let eqv := (T.equivFinOfCardEq card).symm
  let old := eqv.toEmbedding.trans (Function.Embedding.subtype (·∈T))
  let x := old.trans D
  have image (i : Fin N) : old i≠j := (mem_erase.mp (eqv i).property).1
  have full (v : Fin n) (hv : v≠j) : ∃ i : Fin N, old i=v := by
    let t : T := ⟨v,mem_erase.mpr ⟨hv,mem_univ _⟩⟩
    exact ⟨eqv.symm t,congrArg Subtype.val (eqv.apply_symm_apply t)⟩
  let z : Fin N ↪ F := ⟨fun i => x i-a,fun i l he => x.injective (sub_left_inj.mp he)⟩
  let y : Fin N ↪ F := ⟨fun i => (z i)⁻¹,fun _ _ he => z.injective (inv_injective he)⟩
  have neq (i : Fin N) : x i≠a := D.injective.ne (image i)
  have nzZ (i : Fin N) : z i≠0 := sub_ne_zero.mpr (neq i)
  let B := univ.filter (fun i : Fin N => x i≠ -a)
  have few : (univ.filter (fun i : Fin N => x i= -a)).card≤1 := by
    apply card_le_one.mpr
    intro i hi l hl
    exact x.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hl).2.symm)
  have manyB : N≤B.card+1 := by
    have count := card_filter_add_card_filter_not (s:=(univ : Finset (Fin N))) (fun i => x i= -a)
    simp only [card_univ,Fintype.card_fin] at count
    change _ + B.card = N at count
    omega
  have count : B.card≤(DenseOddRedundancy.pairs y (-a⁻¹)).card := by
    apply card_le_card_of_surjOn Prod.fst
    intro i hi
    have hi' : x i≠ -a := (mem_filter.mp hi).2
    obtain ⟨v,hv⟩ := closed (old i)
    change D v=a^2/x i at hv
    have hx : x i≠0 := nz _
    have vj : v ≠ j := by
      rintro rfl
      change a=a^2/x i at hv
      have h' := (eq_div_iff hx).mp hv
      exact neq i (mul_left_cancel₀ ha (by simpa [pow_two] using h'))
    obtain ⟨l,hl⟩ := full v vj
    have eq : x l=a^2/x i := by change D (old l)=_;rw [hl,hv]
    have il : i≠l := by
      rintro rfl
      have h' := (eq_div_iff hx).mp eq
      have prod : (x i-a)*(x i+a)=0 := by linear_combination h'
      exact hi' (eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp prod).resolve_left (nzZ i)))
    refine ⟨(i,l),mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _,mem_univ _,il⟩,?_⟩,rfl⟩
    change (x i-a)⁻¹+(x l-a)⁻¹= -a⁻¹
    have rel := (eq_div_iff hx).mp eq
    field_simp [ha,sub_ne_zero.mpr (neq i),sub_ne_zero.mpr (neq l)]
    linear_combination rel
  let : NeZero N := ⟨by dsimp [N];omega⟩
  let : NeZero (k-1) := ⟨by omega⟩
  have low := DenseOddRedundancy.paired_lower (k:=k-1) y (-a⁻¹)
    (by dsimp [N];omega) large odd (by dsimp [N] at manyB;omega)
  rw [ProjectiveDomainMass.inversion z y nzZ (fun _ => rfl),
    ProjectiveDomainMass.translated_code x z (-a) (fun i => sub_eq_add_neg ..)] at low
  have ext := LocatorShortening.eps_le_extension (k:=k-1) old D (by omega) (h-1)
  rw [show k-1+(n-N)=k by dsimp [N];omega] at ext
  exact low.trans ext

/-- The reciprocal involution closes inside every multiplicative coset.
No constraint on the order of its defining subgroup is needed. -/
theorem coset_lower {n k h : ℕ} [NeZero n] (D : Fin n ↪ F) (a : Fˣ) (H : Subgroup Fˣ)
    (coset : Set.range D=(fun u : Fˣ => (a:F)*(u:F)) '' (H : Set Fˣ))
    (length : n=k+2*h-1) (hk : 4≤k) (large : 3≤h) (odd : h%2=1) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  have point (u : Fˣ) (hu : u∈H) : ∃ i, D i=(a:F)*(u:F) := by
    change (a:F)*(u:F)∈Set.range D
    rw [coset]
    exact ⟨u,hu,rfl⟩
  obtain ⟨j,hj⟩ := point 1 H.one_mem
  simp only [Units.val_one,mul_one] at hj
  have source (i : Fin n) : ∃ u : Fˣ, u∈H ∧ (a:F)*(u:F)=D i := by
    have hi : D i∈Set.range D := ⟨i,rfl⟩
    rwa [coset] at hi
  apply reciprocal_lower D j _ _ length hk large odd
  · intro i
    obtain ⟨u,_,hu⟩ := source i
    rw [←hu];exact mul_ne_zero a.ne_zero u.ne_zero
  · intro i
    obtain ⟨u,hu,hi⟩ := source i
    obtain ⟨l,hl⟩ := point u⁻¹ (H.inv_mem hu)
    refine ⟨l,?_⟩
    rw [hl,hj,←hi,Units.val_inv_eq_inv_val]
    field_simp

/-- When the coset has even order, an element of order two pairs every site
with its additive negative. This includes the remaining dimension k=3. -/
theorem even_coset_lower {n k h : ℕ} [NeZero n] (D : Fin n ↪ F) (a : Fˣ) (H : Subgroup Fˣ)
    (coset : Set.range D=(fun u : Fˣ => (a:F)*(u:F)) '' (H : Set Fˣ))
    (length : n=k+2*h-1) (hk : 3≤k) (even : n%2=0) (large : 3≤h) (odd : h%2=1) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  classical
  let val : H ↪ F := ⟨fun u => (a:F)*((u:Fˣ):F),fun _ _ he =>
    Subtype.ext (Units.ext (mul_left_cancel₀ a.ne_zero he))⟩
  have sites : Set.range D=Set.range val := by
    rw [coset]
    ext z
    exact ⟨fun ⟨u,hu,he⟩ => ⟨⟨u,hu⟩,he⟩,fun ⟨u,he⟩ => ⟨u.val,u.property,he⟩⟩
  have cards : Fintype.card H=n := by
    have eq : univ.image D=univ.image val := by
      ext z
      simpa only [mem_image,mem_univ,true_and,Set.mem_range] using (Set.ext_iff.mp sites z)
    simpa only [card_image_of_injective _ D.injective,card_image_of_injective _ val.injective,
      card_univ,Fintype.card_fin] using (congrArg Finset.card eq).symm
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card (G:=H) 2 (cards ▸ Nat.dvd_of_mod_eq_zero even)
  let v : F := ((g:Fˣ):F)
  have order : v^2=1 := by
    have eq := pow_orderOf_eq_one g
    rw [hg] at eq
    exact congrArg (fun u : H => ((u:Fˣ):F)) eq
  have ne : v≠1 := by
    intro bad
    have e : g=1 := Subtype.ext (Units.ext bad)
    simp [e] at hg
  have neg : v= -1 := (sq_eq_one_iff.mp order).resolve_left ne
  have paired : (univ : Finset (Fin n)).card ≤ (DenseOddRedundancy.pairs D 0).card := by
    apply card_le_card_of_surjOn Prod.fst
    intro i _
    have hi : D i∈Set.range D := ⟨i,rfl⟩
    rw [sites] at hi
    obtain ⟨u,hu⟩ := hi
    have hj : val (g*u)∈Set.range D := sites ▸ (show val (g*u)∈Set.range val from ⟨_,rfl⟩)
    obtain ⟨j,hj⟩ := hj
    have eq : D j=v*D i := by
      rw [hj,←hu]
      change (a:F)*(v*((u:Fˣ):F)) = v*((a:F)*((u:Fˣ):F))
      ring
    have nz : D i≠0 := hu ▸ mul_ne_zero a.ne_zero (u:Fˣ).ne_zero
    have ij : i≠j := by
      rintro rfl
      exact ne (mul_right_cancel₀ nz (eq.symm.trans (one_mul _).symm))
    exact ⟨(i,j),mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _,mem_univ _,ij⟩,by simp [eq,neg]⟩,rfl⟩
  simp only [card_univ,Fintype.card_fin] at paired
  exact DenseOddRedundancy.paired_lower D 0 length large odd (by omega)

/-- Every multiplicative coset of every order attains the odd extra label
at every dimension at least three in the stated band. -/
theorem all_cosets {n k h : ℕ} [NeZero n] (D : Fin n ↪ F) (a : Fˣ) (H : Subgroup Fˣ)
    (coset : Set.range D=(fun u : Fˣ => (a:F)*(u:F)) '' (H : Set Fˣ))
    (length : n=k+2*h-1) (hk : 3≤k) (large : 3≤h) (odd : h%2=1) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  by_cases four : 4≤k
  · exact coset_lower D a H coset length four large odd
  exact even_coset_lower D a H coset length hk (by omega) large odd

end ProximityGap.CosetOddRedundancy
#print axioms ProximityGap.CosetOddRedundancy.coset_lower
#print axioms ProximityGap.CosetOddRedundancy.all_cosets
