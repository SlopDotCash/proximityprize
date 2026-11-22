/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PartitionOriginCertificate
import ArkLib.Research.ProximityGap.Frontier.SecondOrderBlockCounts

/-! # A two-derivative partition-support matrix counted by integral weight slices -/
namespace ProximityGap.SecondOrderOriginBlocks
open ReedSolomon ReedSolomon.HiddenDerivative PolynomialDifferential MvPolynomial Finset
open PartitionOriginCertificate SecondOrderBlockCounts
noncomputable section

private theorem encoded_cover {I J K F : Type*} [Fintype J] [Field F]
    (M : Matrix I J F) (G : Finset K) (R : K → Set I) (C : K → Set J)
    (RR CC : K → Type*) [∀ k, Fintype (RR k)] [∀ k, Fintype (CC k)]
    (ri : ∀ k, R k ↪ RR k) (ci : ∀ k, C k ↪ CC k)
    (cover : ∀ i j, M i j ≠ 0 → ∃ k ∈ G, i ∈ R k ∧ j ∈ C k) :
    M.rank ≤ ∑ k ∈ G, min (Fintype.card (RR k)) (Fintype.card (CC k)) := by
  classical
  letI (k : K) : Fintype (R k) := Fintype.ofInjective (ri k) (ri k).injective
  letI (k : K) : Fintype (C k) := Fintype.ofInjective (ci k) (ci k).injective
  let rows (k : K) := (Set.toFinite (R k)).toFinset
  let cols (k : K) := (Set.toFinite (C k)).toFinset
  apply (HigherJetBigrading.rank_le_sum_min M G rows cols ?_).trans
  · apply sum_le_sum
    intro k _
    apply min_le_min
    · simpa [rows,Set.Finite.card_toFinset] using Fintype.card_le_of_injective _ (ri k).injective
    · simpa [cols,Set.Finite.card_toFinset] using Fintype.card_le_of_injective _ (ci k).injective
  · intro i j h
    simpa [rows,cols] using cover i j h

private abbrev JT := JetVariable 2 →₀ ℕ
private abbrev LT := LocalVariable 2 →₀ ℕ

private def col1 (j : JT) : ℕ := j (some 1)
private def col2 (j : JT) : ℕ := j (some 2)
private def col0 (j : JT) : ℕ := j (some 0)
private def deriv (j : JT) := col1 j + 2*col2 j
private def total (j : JT) := col0 j + col1 j + col2 j
private def err (i : LT) := i (localE 2)
private def first (i : LT) := i (localY 0)
private def second (i : LT) := i (localY 1)
private def jet (i : LT) := err i + first i + second i
private def response (i : LT) := second i + 2*err i

private theorem total_eq (j : JT) : totalJetDegree j = total j := by
  rw [totalJetDegree_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
  simp [total,col0,col1,col2, Nat.add_assoc]

private theorem deriv_eq (j : JT) : fullDerivativeJetWeight j = deriv j := by
  simp [fullDerivativeJetWeight, jetDerivativeWeight, Finsupp.weight_eq_sum, Fintype.sum_option,
    Fin.sum_univ_succ, deriv,col1,col2,Nat.mul_comm]

private theorem source_ext {i j : JT} (hx : i none = j none) (h0 : col0 i = col0 j)
    (h1 : col1 i = col1 j) (h2 : col2 i = col2 j) : i=j := by
  ext v
  rcases v with _|v
  · exact hx
  · fin_cases v <;> assumption

private theorem target_ext {i j : LT} (hx : i (localT 2) = j (localT 2))
    (h0 : err i = err j) (h1 : first i = first j) (h2 : second i = second j) : i=j := by
  ext v
  rcases v with _|_|v
  · exact hx
  · exact h0
  · fin_cases v <;> assumption

private theorem active {F : Type} [Field F] {D W m : ℕ} {L : ℝ} (hD : 0 < D)
    (i : LowContactIndex 2 m) (j : ↥(partitionSupportExponents D 2 W L hD))
    (nz : pointMatrix m hD (0 : F) 0 i j ≠ 0) :
    jet i.val = total j.val ∧
      localContactOrder 2 i.val + deriv j.val = j.val none + total j.val + response i.val := by
  let c := SourceColumn.ofExponent j.val
  have hn : (localConstraintAt m (0:F) 0 (sourceMonomial c.x c.y₀ c.higher)).coeff i.val ≠ 0 := by
    rw [← SourceColumn.polynomial_eq_sourceMonomial, localConstraintAt, LinearMap.comp_apply,
      coeff_projectLowContact, ite_eq_left i.property]
    exact nz
  obtain ⟨h₁,h₂⟩ := HigherJetBigrading.nonzero_labels (by decide : 0<2) _ _ _ _ hn
  simp only [Finsupp.weight_eq_sum,Fintype.sum_option,Fin.sum_univ_two] at h₁ h₂
  simp [c,SourceColumn.ofExponent, localJetDegreeWeight,HigherJetBigrading.targetWeight,
    jet,total,col0,col1,col2,err,first,second,localT,localE,localAux,localY,
    Nat.add_assoc] at h₁ h₂ ⊢
  rw [localContactOrder_eq]
  simp only [deriv,response,col1,col2,second,err,localT,localE,localAux,localY]
  constructor <;> omega

private def rowSet (m W t z : ℕ) : Set (LowContactIndex 2 m) :=
  {i | jet i.val = t ∧ localContactOrder 2 i.val + W = z+t+response i.val}

private def columnSet {D W : ℕ} {L : ℝ} (hD : 0<D) (t z : ℕ) :
    Set ↥(partitionSupportExponents D 2 W L hD) :=
  {j | total j.val = t ∧ j.val none + W = z+deriv j.val}

private def rowEncoding (m W t z : ℕ) :
    rowSet m W t z ↪ Slice t (W-(z+t)) (W+m-(z+t)) where
  toFun i :=
    ⟨(second i.val.val,err i.val.val), by
      have ht := i.property.1
      have hz := i.property.2
      have hl := i.val.property
      dsimp [jet,response] at ht hz
      dsimp; omega⟩
  inj' := by
    intro i j he
    have h1 := congrArg (fun q => q.val.1) he
    have h2 := congrArg (fun q => q.val.2) he
    dsimp at h1 h2
    apply Subtype.ext
    apply Subtype.ext
    have it := i.property.1
    have jt := j.property.1
    have iz := i.property.2
    have jz := j.property.2
    dsimp [jet,response] at it jt iz jz
    rw [localContactOrder_eq] at iz jz
    change _ + 2*err _ + _ = _ at iz jz
    exact target_ext (by omega) h2 (by omega) h1

private def columnEncoding {D W : ℕ} {L : ℝ} (hD : 0<D) (t z : ℕ) :
    columnSet (W := W) (L := L) hD t z ↪ Slice t (W-z) (W+1) where
  toFun j :=
    ⟨(col1 j.val.val,col2 j.val.val), by
      have ht := j.property.1
      have hz := j.property.2
      have hl := (mem_partitionSupportExponents.mp j.val.property).1
      rw [deriv_eq] at hl
      dsimp [total,deriv] at ht hz hl
      dsimp; omega⟩
  inj' := by
    intro i j he
    have h1 := congrArg (fun q => q.val.1) he
    have h2 := congrArg (fun q => q.val.2) he
    dsimp at h1 h2
    apply Subtype.ext
    apply Subtype.ext
    have it := i.property.1
    have jt := j.property.1
    have iz := i.property.2
    have jz := j.property.2
    dsimp [total,deriv] at it jt iz jz
    exact source_ext (by omega) (by omega) h1 h2

/-- An explicit sum of minimum row and column counts for the local matrix. -/
def blockBudget (m W v : ℕ) : ℕ :=
  ∑ t ∈ range (v+1), ∑ z ∈ range (W+m),
    min (countBelow t (W+m-(z+t)) - countBelow t (W-(z+t)))
      (countBelow t (W+1) - countBelow t (W-z))

/-- Every field and every partition support of jet degree at most `v`
satisfies the explicit order-two rank bound. -/
theorem origin_rank {F : Type} [Field F] {D W m v : ℕ} {L : ℝ} (hD : 0 < D)
    (hv : ∀ u, PartitionSupportEligible D 2 W L u → totalJetDegree u ≤ v) :
    (pointMatrix (d := 2) (W := W) (L := L) m hD (0:F) 0).rank ≤ blockBudget m W v := by
  let G := range (v+1) ×ˢ range (W+m)
  apply (encoded_cover _ G (fun k => rowSet m W k.1 k.2) (fun k => columnSet hD k.1 k.2)
    _ _ (fun k => rowEncoding m W k.1 k.2) (fun k => columnEncoding hD k.1 k.2) ?_).trans
  · simp [G,blockBudget,Finset.sum_product,card_slice]
  · intro i j nz
    obtain ⟨ht,hz⟩ := active hD i j nz
    let t := total j.val
    let z := j.val none + W - deriv j.val
    have hel := mem_partitionSupportExponents.mp j.property
    have hj := hel.1
    rw [deriv_eq] at hj
    have ht' := hv j.val hel
    rw [total_eq] at ht'
    have hm := i.property
    refine ⟨(t,z), ?_, ?_, ?_⟩
    · simp only [G,mem_product,mem_range,t,z]; omega
    · change jet i.val = t ∧ _
      exact ⟨ht,by dsimp [z,t]; omega⟩
    · exact ⟨rfl,by dsimp [z]; omega⟩

private def makeExponent (x v u b : ℕ) : JT :=
  Finsupp.equivFunOnFinite.symm fun
  | none => x
  | some i => ![v,u,b] i

/-- Source columns counted by total degree and derivative partition. -/
def sourceBudget (D L W v : ℕ) : ℕ :=
  ∑ t ∈ range (v+1), countBelow t (W+1) * (L-D*t)

private abbrev SourceSlots (D L W v : ℕ) :=
  Σ t : Fin (v+1), Slice t.val 0 (W+1) × Fin (L-D*t.val)

private theorem sourceSlots_card (D L W v : ℕ) :
    Fintype.card (SourceSlots D L W v) = sourceBudget D L W v := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fin,card_slice]
  unfold sourceBudget
  have emptyBelow (t : ℕ) : countBelow t 0 = 0 := by simp [countBelow,triangle,unrestricted]
  simp only [emptyBelow,Nat.sub_zero]
  exact Fin.sum_univ_eq_sum_range (fun t => countBelow t (W+1) * (L-D*t)) (v+1)

private def makeColumn {D L W v : ℕ} (hD : 0 < D) (s : SourceSlots D L W v) :
    ↥(partitionSupportExponents D 2 W (L:ℝ) hD) :=
  let t := s.1.val
  let q := s.2.1.val
  let x := s.2.2.val
  ⟨makeExponent x (t-q.1-q.2) q.1 q.2, by
    rw [mem_partitionSupportExponents]
    have hq := s.2.1.property
    have hx := s.2.2.isLt
    refine ⟨?_,?_⟩
    · rw [deriv_eq]
      change s.2.1.val.1 + 2*s.2.1.val.2 ≤ W
      omega
    · rw [total_eq]
      change ((x+D*(t-q.1-q.2+q.1+q.2) : ℕ) : ℝ) < L
      have hqt : q.1+q.2≤t := hq.1
      rw [show t-q.1-q.2+q.1+q.2=t by omega]
      exact_mod_cast (show x+D*t<L by dsimp [t,x]; omega)⟩

private theorem makeColumn_injective {D L W v : ℕ} (hD : 0<D) :
    Function.Injective (makeColumn (L := L) (W := W) (v := v) hD) := by
  rintro ⟨⟨t,ht⟩,⟨⟨u,b⟩,hq⟩,⟨x,hx⟩⟩ ⟨⟨t',ht'⟩,⟨⟨u',b'⟩,hq'⟩,⟨x',hx'⟩⟩ he
  have ex := congrArg (fun c => c.val none) he
  have e0 := congrArg (fun c => col0 c.val) he
  have e1 := congrArg (fun c => col1 c.val) he
  have e2 := congrArg (fun c => col2 c.val) he
  change x=x' at ex
  change t-u-b=t'-u'-b' at e0
  change u=u' at e1
  change b=b' at e2
  change u+b ≤ t ∧ _ at hq
  change u'+b' ≤ t' ∧ _ at hq'
  have et : t=t' := by omega
  subst t' u' b' x'
  rfl

/-- The enumerated columns inject into the canonical source support. -/
theorem source_card_lower {D L W v : ℕ} (hD : 0 < D) :
    sourceBudget D L W v ≤ (partitionSupportExponents D 2 W (L:ℝ) hD).card := by
  rw [←sourceSlots_card,←Fintype.card_coe]
  exact Fintype.card_le_of_injective _ (makeColumn_injective hD)

/-- The coarse cutoff supplies a uniform jet degree bound by one division. -/
theorem jet_cap {D L W v : ℕ} (h : L ≤ D*(v+1)) (u : JT)
    (hu : PartitionSupportEligible D 2 W (L:ℝ) u) : totalJetDegree u ≤ v := by
  have hcut : u none+D*totalJetDegree u < L := by exact_mod_cast hu.2
  by_contra ng
  have hh := Nat.mul_le_mul_left D (show v+1 ≤ totalJetDegree u by omega)
  omega

end
end ProximityGap.SecondOrderOriginBlocks

#print axioms ProximityGap.SecondOrderOriginBlocks.origin_rank

#print axioms ProximityGap.SecondOrderOriginBlocks.source_card_lower
