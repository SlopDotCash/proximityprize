/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceAverageAnchor

set_option autoImplicit false
set_option maxRecDepth 4096

namespace ProximityGap.IncidenceFullScaleCores

open Finset Polynomial ProximityGap.Ownership
open ProximityGap Code
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26

private abbrev sponsorP := ArkLib.ProximityGap.PrizeShapePrimeP30.P

private instance : Fact sponsorP.Prime := ⟨prime_P⟩
private instance : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 536870912
abbrev commonSize : ℕ := 536870910
abbrev groupSize : ℕ := 178956971
abbrev Coord := Fin n

/-- Coordinate embedding of the common root set. -/
def commonEmb : Fin commonSize ↪ Coord where
  toFun a := ⟨a.val, by
    have ha := a.isLt
    simp only [n,commonSize,groupSize] at *
    omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Coord => x.val) h

/-- Three disjoint coordinate groups, leaving one unused coordinate. -/
def groupEmb (j : Fin 3) : Fin groupSize ↪ Coord where
  toFun a := ⟨commonSize + j.val * groupSize + a.val, by
    have ha := a.isLt
    have hj := j.isLt
    simp only [n,commonSize,groupSize] at *
    omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp at hh
    omega

def common : Finset Coord := Finset.univ.map commonEmb
def group (j : Fin 3) : Finset Coord := Finset.univ.map (groupEmb j)
def core (j : Fin 3) : Finset Coord := common ∪ group j

theorem mem_common (i : Coord) : i ∈ common ↔ i.val < commonSize := by
  constructor
  · intro hi
    obtain ⟨a,_,ha⟩ := Finset.mem_map.mp hi
    have he := congrArg Fin.val ha
    have hb := a.isLt
    dsimp [commonEmb] at he
    omega
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i.val,hi⟩,Finset.mem_univ _,Fin.ext rfl⟩

theorem mem_group (j : Fin 3) (i : Coord) : i ∈ group j ↔
    commonSize + j.val * groupSize ≤ i.val ∧
      i.val < commonSize + (j.val + 1) * groupSize := by
  constructor
  · intro hi
    obtain ⟨a,_,ha⟩ := Finset.mem_map.mp hi
    have he := congrArg Fin.val ha
    have hb := a.isLt
    dsimp [groupEmb] at he
    simp only [n,commonSize,groupSize] at *
    omega
  · rintro ⟨hlo,hhi⟩
    refine Finset.mem_map.mpr ⟨⟨i.val - (commonSize + j.val * groupSize),by
      simp only [commonSize,groupSize] at *
      omega⟩,
      Finset.mem_univ _,?_⟩
    apply Fin.ext
    dsimp [groupEmb]
    omega

theorem core_card (j : Fin 3) : (core j).card = 715827881 := by
  have hd : Disjoint common (group j) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hc := (mem_common i).mp hi
    have hg := (mem_group j i).mp hj
    omega
  rw [core,Finset.card_union_of_disjoint hd]
  simp only [common,group,Finset.card_map,Finset.card_univ,Fintype.card_fin]
  norm_num

/-- Heights of the three groups and the one unused coordinate. -/
def height (i : Coord) : ℕ :=
  if i.val < commonSize then 3 else
    if i.val < commonSize + 3 * groupSize then (i.val - commonSize) / groupSize else 3

theorem height_le (i : Coord) : height i ≤ 3 := by
  unfold height
  simp only [commonSize,groupSize] at *
  split_ifs
  all_goals omega

theorem height_eq_iff (j : Fin 3) (i : Coord) : height i = j.val ↔ i ∈ group j := by
  rw [mem_group]
  have hj := j.isLt
  unfold height
  simp only [commonSize,groupSize] at *
  split_ifs
  all_goals omega

/-- Locator of the common coordinates, without enumerating the production domain. -/
noncomputable def locator : Polynomial (ZMod sponsorP) :=
  ∏ a : Fin commonSize, (Polynomial.X - Polynomial.C (g ^ a.val))

noncomputable def z (i : Coord) : ZMod sponsorP := locator.eval (g ^ i.val)

theorem locator_natDegree_le : locator.natDegree ≤ commonSize := by
  unfold locator
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _a : Fin commonSize, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro a _
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = commonSize := by simp

theorem z_eq_zero_iff (i : Coord) : z i = 0 ↔ i ∈ common := by
  rw [z,locator,Polynomial.eval_prod,Finset.prod_eq_zero_iff]
  simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_eq_zero]
  constructor
  · rintro ⟨a,_,ha⟩
    have he : i = commonEmb a :=
      (smoothDom g n orderOf_g).injective ha
    rw [he,mem_common]
    exact a.isLt
  · intro hi
    have hc := (mem_common i).mp hi
    exact ⟨⟨i.val,hc⟩,Finset.mem_univ _,rfl⟩

noncomputable def prodCode : Submodule (ZMod sponsorP) (Coord → ZMod sponsorP) :=
  ProximityGap.SpikeFloor.rsCode (smoothDom g n orderOf_g) k

noncomputable def xz (i : Coord) : ZMod sponsorP := z i * g ^ i.val
noncomputable def u1 (i : Coord) : ZMod sponsorP := (height i : ZMod sponsorP) * z i
noncomputable def u0 (i : Coord) : ZMod sponsorP := (height i : ZMod sponsorP) ^ 2 * xz i
noncomputable def v1 (j : Fin 3) : Coord → ZMod sponsorP := (j.val : ZMod sponsorP) • z
noncomputable def v0 (j : Fin 3) : Coord → ZMod sponsorP := (j.val : ZMod sponsorP) ^ 2 • xz

theorem z_mem : z ∈ prodCode := by
  change ∃ q : Polynomial (ZMod sponsorP), q.degree < k ∧ z = fun i => q.eval (g ^ i.val)
  refine ⟨locator,?_,rfl⟩
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree
    (by exact_mod_cast (locator_natDegree_le.trans_lt (by norm_num : commonSize < k)))

theorem xz_mem : xz ∈ prodCode := by
  change ∃ q : Polynomial (ZMod sponsorP), q.degree < k ∧ xz = fun i => q.eval (g ^ i.val)
  refine ⟨locator * Polynomial.X,?_,?_⟩
  · apply lt_of_le_of_lt (Polynomial.degree_mul_le _ _)
    have hz : locator.degree ≤ (commonSize : ℕ) :=
      Polynomial.degree_le_natDegree.trans (by exact_mod_cast locator_natDegree_le)
    have hx : (Polynomial.X : Polynomial (ZMod sponsorP)).degree ≤ (1 : ℕ) :=
      Polynomial.degree_X_le
    exact (add_le_add hz hx).trans_lt (by norm_num)
  · funext i
    simp only [Polynomial.eval_mul,Polynomial.eval_X]
    rfl

theorem v1_mem (j : Fin 3) : v1 j ∈ prodCode := prodCode.smul_mem _ z_mem
theorem v0_mem (j : Fin 3) : v0 j ∈ prodCode := prodCode.smul_mem _ xz_mem

theorem agree_v1 (j : Fin 3) : ∀ i ∈ core j, v1 j i = u1 i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hc | hg
  · have hz := (z_eq_zero_iff i).mpr hc
    simp [v1,u1,hz]
  · have hh := (height_eq_iff j i).mpr hg
    simp [v1,u1,hh]

theorem agree_v0 (j : Fin 3) : ∀ i ∈ core j, v0 j i = u0 i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hc | hg
  · have hz := (z_eq_zero_iff i).mpr hc
    simp [v0,u0,xz,hz]
  · have hh := (height_eq_iff j i).mpr hg
    simp [v0,u0,hh]

open ProximityGap Code
open scoped NNReal ENNReal
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

/- The four channel lemmas below retain the SYZ2/SYZ3 authorship and proofs.
They are restated to keep this construction's imported proof cone small. -/
section Channel

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The pencil scalar attached to an off-`S` point `x` of a degenerate subset
(SYZ2 `pencilScalar`). -/
noncomputable def pencilScalar (u₀ u₁ v₀ v₁ : ι → F) (x : ι) : F :=
  -((u₀ x - v₀ x) / (u₁ x - v₁ x))

/-- SYZ2 channel theorem (a): the codeword pencil agrees with the line on `S ∪ {x}`. -/
theorem pencil_line_agrees {S : Finset ι} {u₀ u₁ v₀ v₁ : ι → F}
    (h₀ : ∀ i ∈ S, v₀ i = u₀ i) (h₁ : ∀ i ∈ S, v₁ i = u₁ i)
    {x : ι} (hd₁ : u₁ x ≠ v₁ x) :
    ∀ i ∈ insert x S,
      (v₀ + pencilScalar u₀ u₁ v₀ v₁ x • v₁) i
        = u₀ i + pencilScalar u₀ u₁ v₀ v₁ x • u₁ i := by
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hiS
  · have hne : u₁ i - v₁ i ≠ 0 := sub_ne_zero.mpr hd₁
    have key : pencilScalar u₀ u₁ v₀ v₁ i * (u₁ i - v₁ i) = -(u₀ i - v₀ i) := by
      rw [pencilScalar, neg_mul, div_mul_cancel₀ _ hne]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -key
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h₀ i hiS, h₁ i hiS]

/-- SYZ2 channel theorem (b): the pair-joint clause fails on the enlarged witness set. -/
theorem not_pairJointAgreesOn_insert (C : Submodule F (ι → F))
    {S : Finset ι} {u₀ u₁ v₁ : ι → F}
    (huniq₁ : ∀ w ∈ (C : Set (ι → F)), (∀ i ∈ S, w i = u₁ i) → w = v₁)
    {x : ι} (hd₁ : u₁ x ≠ v₁ x) :
    ¬ pairJointAgreesOn (C : Set (ι → F)) (insert x S) u₀ u₁ := by
  rintro ⟨w₀, hw₀, w₁, hw₁, h⟩
  have hw₁v : w₁ = v₁ :=
    huniq₁ w₁ hw₁ fun i hi => (h i (Finset.mem_insert_of_mem hi)).2
  have hx : w₁ x = u₁ x := (h x (Finset.mem_insert_self x S)).2
  rw [hw₁v] at hx
  exact hd₁ hx.symm

/-- SYZ2 per-point channel: every eligible off-`S` point produces a literal
`mcaEvent`-bad scalar. -/
theorem mcaEvent_pencil (C : Submodule F (ι → F)) {δ : ℝ≥0}
    {S : Finset ι} {u₀ u₁ v₀ v₁ : ι → F}
    (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C)
    (h₀ : ∀ i ∈ S, v₀ i = u₀ i) (h₁ : ∀ i ∈ S, v₁ i = u₁ i)
    (huniq₁ : ∀ w ∈ (C : Set (ι → F)), (∀ i ∈ S, w i = u₁ i) → w = v₁)
    {x : ι} (hd₁ : u₁ x ≠ v₁ x)
    (hcard : (((insert x S).card : ℝ≥0)) ≥ (1 - δ) * Fintype.card ι) :
    mcaEvent (C : Set (ι → F)) δ u₀ u₁ (pencilScalar u₀ u₁ v₀ v₁ x) :=
  ⟨insert x S, hcard,
    ⟨v₀ + pencilScalar u₀ u₁ v₀ v₁ x • v₁,
      C.add_mem hv₀ (C.smul_mem _ hv₁),
      pencil_line_agrees h₀ h₁ hd₁⟩,
    not_pairJointAgreesOn_insert C huniq₁ hd₁⟩

/-- SYZ2 Reed–Solomon interpolation uniqueness on any subset of at least `k` points. -/
theorem rsCode_eq_of_agree_on_card_le {n : ℕ} [NeZero n]
    (dom : Fin n ↪ F) {k : ℕ} {S : Finset (Fin n)} (hk : k ≤ S.card)
    {w w' : Fin n → F} (hw : w ∈ ProximityGap.SpikeFloor.rsCode dom k) (hw' : w' ∈ ProximityGap.SpikeFloor.rsCode dom k)
    (hagree : ∀ i ∈ S, w i = w' i) : w = w' := by
  obtain ⟨p, hP, rfl⟩ := hw
  obtain ⟨Q, hQ, rfl⟩ := hw'
  have hPQ : p - Q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := p - Q) (s := S.image dom) ?_ ?_
    · rw [Finset.card_image_of_injective _ dom.injective]
      calc (p - Q).degree ≤ max p.degree Q.degree := Polynomial.degree_sub_le p Q
        _ < (k : WithBot ℕ) := max_lt hP hQ
        _ ≤ (S.card : WithBot ℕ) := by exact_mod_cast hk
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.eval_sub, sub_eq_zero]
      exact hagree i hi
  have hPQ' : p = Q := sub_eq_zero.mp hPQ
  rw [hPQ']

end Channel

theorem row1_ne (j : Fin 3) (i : Coord) (hi : i ∉ core j) : u1 i ≠ v1 j i := by
  have hc : i ∉ common := fun h => hi (Finset.mem_union_left _ h)
  have hg : i ∉ group j := fun h => hi (Finset.mem_union_right _ h)
  have hz : z i ≠ 0 := fun h => hc ((z_eq_zero_iff i).mp h)
  have hnat : height i ≠ j.val := fun h => hg ((height_eq_iff j i).mp h)
  have hcast : (height i : ZMod sponsorP) ≠ (j.val : ZMod sponsorP) := by
    intro h
    have hp : 5 < sponsorP := by norm_num [sponsorP,ArkLib.ProximityGap.PrizeShapePrimeP30.P]
    have hvh := ZMod.val_natCast_of_lt ((height_le i).trans_lt (by omega : 3 < sponsorP))
    have hvj := ZMod.val_natCast_of_lt (j.isLt.trans (by omega : 3 < sponsorP))
    have he := congrArg ZMod.val h
    rw [hvh,hvj] at he
    exact hnat he
  intro h
  exact hcast (mul_right_cancel₀ hz h)

theorem uniq_v1 (j : Fin 3) : ∀ w ∈ (prodCode : Set (Coord → ZMod sponsorP)),
    (∀ i ∈ core j, w i = u1 i) → w = v1 j := by
  intro w hw ha
  exact rsCode_eq_of_agree_on_card_le (smoothDom g n orderOf_g)
    (by
      rw [core_card]
      norm_num : k ≤ (core j).card) hw (v1_mem j)
    (fun i hi => (ha i hi).trans (agree_v1 j i hi).symm)

theorem support_card (j : Fin 3) (i : Coord) (hi : i ∉ core j) :
    (insert i (core j)).card = 715827882 := by
  rw [Finset.card_insert_of_notMem hi,core_card]

theorem support_threshold (j : Fin 3) (i : Coord) (hi : i ∉ core j) :
    (1 - (178956971 : ℝ≥0) / 536870912) * Fintype.card Coord ≤
      ((insert i (core j)).card : ℝ≥0) := by
  rw [support_card j i hi]
  have hle : (178956971 : ℝ≥0) / 536870912 ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    norm_num
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_mul, NNReal.coe_sub hle]
  norm_num [Coord, n]

noncomputable def scalar (j : Fin 3) (i : Coord) : ZMod sponsorP :=
  -((height i + j.val : ℕ) : ZMod sponsorP) * g ^ i.val

theorem scalar_eq_pencil (j : Fin 3) (i : Coord) (hi : i ∉ core j) :
    scalar j i = pencilScalar u0 u1 (v0 j) (v1 j) i := by
  have hd := sub_ne_zero.mpr (row1_ne j i hi)
  unfold pencilScalar
  apply neg_injective
  rw [neg_neg]
  apply (eq_div_iff hd).2
  simp only [scalar,u0,u1,v0,v1,xz,Pi.smul_apply,smul_eq_mul,Nat.cast_add]
  ring

theorem scalar_bad (j : Fin 3) (i : Coord) (hi : i ∉ core j) :
    mcaEvent (prodCode : Set (Coord → ZMod sponsorP))
      ((178956971 : ℝ≥0) / 536870912) u0 u1 (scalar j i) := by
  rw [scalar_eq_pencil j i hi]
  exact mcaEvent_pencil prodCode (v0_mem j) (v1_mem j) (agree_v0 j) (agree_v1 j)
    (uniq_v1 j) (row1_ne j i hi) (support_threshold j i hi)

/- Square-and-multiply proof adapted from the existing SYZ3 module. -/
private def powAux {M : Type*} [Monoid M] (a : M) (m : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 => if m = 0 then 1 else if m % 2 = 0 then
      powAux (a*a) (m/2) fuel else a * powAux (a*a) (m/2) fuel

private theorem powAux_eq {M : Type*} [Monoid M] (a : M) (m fuel : ℕ)
    (hm : m < fuel) : powAux a m fuel = a ^ m := by
  induction fuel generalizing a m with
  | zero => omega
  | succ fuel ih =>
      rw [powAux]
      split_ifs with h0 heven
      · subst m
        simp
      · have hp : 0 < m := Nat.pos_of_ne_zero h0
        have hh : m / 2 < fuel := (Nat.div_lt_self hp (by norm_num)).trans_le (by omega)
        rw [ih (a*a) (m/2) hh,← pow_two,← pow_mul]
        have hd : 2 ∣ m := (Nat.dvd_iff_mod_eq_zero).2 heven
        have he := Nat.mul_div_cancel' hd
        congr 1
      · have hp : 0 < m := Nat.pos_of_ne_zero h0
        have hh : m / 2 < fuel := (Nat.div_lt_self hp (by norm_num)).trans_le (by omega)
        rw [ih (a*a) (m/2) hh,← pow_two,← pow_mul,← pow_succ']
        have hmod : m % 2 = 1 := by omega
        have he := Nat.mod_add_div m 2
        congr 1
        omega

private def fastPow (a : ZMod sponsorP) : ZMod sponsorP := powAux a n (n+1)

private theorem fastPow_eq (a : ZMod sponsorP) : fastPow a = a ^ n :=
  powAux_eq a n (n+1) (by omega)

set_option maxRecDepth 100000 in
private theorem coefficient_certificate : ∀ a b : Fin 5,
    fastPow ((a.val+1 : ℕ) : ZMod sponsorP) = fastPow ((b.val+1 : ℕ) : ZMod sponsorP) → a = b := by
  decide

theorem coefficient_powers_injective {a b : ℕ}
    (ha : 1 ≤ a ∧ a ≤ 5) (hb : 1 ≤ b ∧ b ≤ 5)
    (h : (a : ZMod sponsorP) ^ n = (b : ZMod sponsorP) ^ n) : a = b := by
  let aa : Fin 5 := ⟨a-1,by omega⟩
  let bb : Fin 5 := ⟨b-1,by omega⟩
  have haa : aa.val + 1 = a := by
    dsimp [aa]
    omega
  have hbb : bb.val + 1 = b := by
    dsimp [bb]
    omega
  have he : fastPow ((aa.val+1 : ℕ) : ZMod sponsorP) = fastPow ((bb.val+1 : ℕ) : ZMod sponsorP) := by
    rw [fastPow_eq,fastPow_eq,haa,hbb]
    exact h
  have hab := congrArg Fin.val (coefficient_certificate aa bb he)
  dsimp [aa,bb] at hab
  omega

theorem coefficient_bounds (j : Fin 3) (i : Coord) (hi : i ∉ core j) :
    1 ≤ height i + j.val ∧ height i + j.val ≤ 5 := by
  have hh := height_le i
  have hj := j.isLt
  have hn : height i ≠ j.val := fun h => hi
    (Finset.mem_union_right _ ((height_eq_iff j i).mp h))
  omega

theorem scalar_injective {j j' : Fin 3} {i i' : Coord}
    (hi : i ∉ core j) (hi' : i' ∉ core j')
    (he : scalar j i = scalar j' i') : j = j' ∧ i = i' := by
  have hh : ((height i + j.val : ℕ) : ZMod sponsorP) * g ^ i.val =
      ((height i' + j'.val : ℕ) : ZMod sponsorP) * g ^ i'.val := by
    simpa only [scalar,neg_mul,neg_inj] using he
  have hg : ∀ m : ℕ, (g ^ m) ^ n = 1 := by
    intro m
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    have hfull : g ^ n = 1 := by
      simpa only [orderOf_g] using pow_orderOf_eq_one g
    rw [hfull,one_pow]
  have hp := congrArg (fun a : ZMod sponsorP => a ^ n) hh
  simp only [mul_pow,hg,mul_one] at hp
  have hab := coefficient_powers_injective (coefficient_bounds j i hi)
    (coefficient_bounds j' i' hi') hp
  have hn : ((height i + j.val : ℕ) : ZMod sponsorP) ≠ 0 := by
    have hb := coefficient_bounds j i hi
    have hl : 5 < sponsorP := by norm_num [sponsorP,ArkLib.ProximityGap.PrizeShapePrimeP30.P]
    have hv := ZMod.val_natCast_of_lt (by omega : height i + j.val < sponsorP)
    intro h
    have hz := congrArg ZMod.val h
    rw [hv,ZMod.val_zero] at hz
    omega
  rw [← hab] at hh
  have hii : i = i' := (smoothDom g n orderOf_g).injective (mul_left_cancel₀ hn hh)
  subst i'
  have hjj : j = j' := Fin.ext (by omega)
  exact ⟨hjj,rfl⟩

/-- The designated decoded head has no agreement coordinates beyond its witness. -/
theorem exact_agreement_support (j : Fin 3) (i : Coord) (hi : i ∉ core j) (y : Coord) :
    (v0 j + scalar j i • v1 j) y = u0 y + scalar j i * u1 y ↔
      y ∈ insert i (core j) := by
  constructor
  · intro he
    by_cases hy : y ∈ core j
    · exact Finset.mem_insert_of_mem hy
    · have hd := sub_ne_zero.mpr (row1_ne j y hy)
      have hmul : scalar j i * (u1 y - v1 j y) = -(u0 y - v0 j y) := by
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at he
        linear_combination -he
      have hscalar : scalar j i = pencilScalar u0 u1 (v0 j) (v1 j) y := by
        unfold pencilScalar
        apply neg_injective
        rw [neg_neg]
        apply (eq_div_iff hd).2
        linear_combination -hmul
      rw [← scalar_eq_pencil j y hy] at hscalar
      have hiy := (scalar_injective hi hy hscalar).2
      exact Finset.mem_insert.mpr (Or.inl hiy.symm)
  · intro hy
    have hag := pencil_line_agrees (agree_v0 j) (agree_v1 j) (row1_ne j i hi) y hy
    rw [← scalar_eq_pencil j i hi] at hag
    exact hag

noncomputable def image (j : Fin 3) : Finset (ZMod sponsorP) := (core j)ᶜ.image (scalar j)

theorem image_card (j : Fin 3) : (image j).card = 357913943 := by
  classical
  have hinj : Set.InjOn (scalar j) (↑((core j)ᶜ) : Set Coord) := by
    intro a ha b hb he
    exact (scalar_injective (Finset.mem_compl.mp ha) (Finset.mem_compl.mp hb) he).2
  rw [image,Finset.card_image_iff.mpr hinj,Finset.card_compl,core_card]
  norm_num [Coord, n]

theorem images_disjoint {j j' : Fin 3} (hj : j ≠ j') : Disjoint (image j) (image j') := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ha
  obtain ⟨i',hi',he'⟩ := Finset.mem_image.mp hb
  exact hj (scalar_injective (Finset.mem_compl.mp hi) (Finset.mem_compl.mp hi')
    (he.trans he'.symm)).1

noncomputable def allScalars : Finset (ZMod sponsorP) := image 0 ∪ image 1 ∪ image 2

theorem allScalars_card : allScalars.card = 1073741829 := by
  classical
  have h01 : Disjoint (image 0) (image 1) := images_disjoint (by decide)
  have h012 : Disjoint (image 0 ∪ image 1) (image 2) :=
    Finset.disjoint_union_left.mpr ⟨images_disjoint (by decide),images_disjoint (by decide)⟩
  rw [allScalars,Finset.card_union_of_disjoint h012,Finset.card_union_of_disjoint h01,
    image_card,image_card,image_card]

theorem allScalars_bad : ∀ a ∈ allScalars,
    mcaEvent (prodCode : Set (Coord → ZMod sponsorP))
      ((178956971 : ℝ≥0) / 536870912) u0 u1 a := by
  classical
  have hrow : ∀ j : Fin 3, ∀ a ∈ image j,
      mcaEvent (prodCode : Set (Coord → ZMod sponsorP))
        ((178956971 : ℝ≥0) / 536870912) u0 u1 a := by
    intro j a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact scalar_bad j i (Finset.mem_compl.mp hi)
  intro a ha
  rcases Finset.mem_union.mp ha with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact hrow 0 a h
    · exact hrow 1 a h
  · exact hrow 2 a h

theorem firstPrime_fullScale_upper :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
      (F := ZMod sponsorP) (A := ZMod sponsorP)
      (evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ℝ≥0∞)
      ≤ ((178956971 : ℝ≥0) / 536870912) := by
  have hbridge : evalCode g (2 ^ 30) (2 ^ 29 - 1)
      = ((prodCode : Submodule (ZMod sponsorP) (Fin (2 ^ 30) → ZMod sponsorP)) :
          Set (Fin (2 ^ 30) → ZMod sponsorP)) := by
    simpa only [prodCode, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 29)] using
      (evalCode_eq_rsCode orderOf_g (2 ^ 29 - 1))
  rw [hbridge]
  let u : WordStack (ZMod sponsorP) (Fin 2) (Fin (2 ^ 30)) :=
    fun r => if r = 0 then u0 else u1
  let G : Finset (ZMod sponsorP) := allScalars
  have hu0 : u 0 = u0 := by simp [u]
  have hu1 : u 1 = u1 := by simp [u]
  have hcount : 2 ^ 30 + 1 ≤ G.card := by
    rw [allScalars_card]
    norm_num
  have hG : ∀ γ ∈ G,
      mcaEvent (prodCode : Set (Coord → ZMod sponsorP))
        ((178956971 : ℝ≥0) / 536870912) (u 0) (u 1) γ := by
    rw [hu0,hu1]
    exact allScalars_bad
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod sponsorP) (A := ZMod sponsorP)
    (prodCode : Set (Fin (2 ^ 30) → ZMod sponsorP))
    (((178956971 : ℝ≥0) / 536870912)) u G hG
  rw [ZMod.card] at hengine
  have hPnat : (sponsorP : ℕ) < G.card * 2 ^ 128 := by
    have hbase : (sponsorP : ℕ) < (2 ^ 30 + 1) * 2 ^ 128 := by
      show (365375409332725729550921208179070755120141565953 : ℕ) <
        (2 ^ 30 + 1) * 2 ^ 128
      norm_num
    exact lt_of_lt_of_le hbase (Nat.mul_le_mul_right _ hcount)
  have hP0 : ((sponsorP : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact prime_P.pos.ne'
  have hPtop : ((sponsorP : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top sponsorP
  have h2t0 : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    norm_num
  have h2ttop : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hkey : ((sponsorP : ℕ) : ℝ≥0∞) <
      ((G.card : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul]
    exact_mod_cast hPnat
  have hmass : (ProximityGap.epsStar : ℝ≥0∞) <
      ((G.card : ℕ) : ℝ≥0∞) / ((sponsorP : ℕ) : ℝ≥0∞) := by
    rw [epsStar_coe_eq_natCast_inv,
      ENNReal.lt_div_iff_mul_lt (Or.inl hP0) (Or.inl hPtop),
      ← ENNReal.div_eq_inv_mul,
      ENNReal.div_lt_iff (Or.inl h2t0) (Or.inl h2ttop)]
    exact hkey
  have hlt : (ProximityGap.epsStar : ℝ≥0∞) <
      epsMCA (F := ZMod sponsorP) (A := ZMod sponsorP)
        (prodCode : Set (Fin (2 ^ 30) → ZMod sponsorP))
        (((178956971 : ℝ≥0) / 536870912)) :=
    lt_of_lt_of_le hmass hengine
  have hbad := ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad
    (F := ZMod sponsorP) (A := ZMod sponsorP)
    (prodCode : Set (Fin (2 ^ 30) → ZMod sponsorP))
    (ProximityGap.epsStar : ℝ≥0∞) hlt
  exact hbad


end ProximityGap.IncidenceFullScaleCores

#print axioms ProximityGap.IncidenceFullScaleCores.core_card
#print axioms ProximityGap.IncidenceFullScaleCores.z_eq_zero_iff
#print axioms ProximityGap.IncidenceFullScaleCores.z_mem
#print axioms ProximityGap.IncidenceFullScaleCores.xz_mem
#print axioms ProximityGap.IncidenceFullScaleCores.agree_v1
#print axioms ProximityGap.IncidenceFullScaleCores.agree_v0
#print axioms ProximityGap.IncidenceFullScaleCores.scalar_bad
#print axioms ProximityGap.IncidenceFullScaleCores.coefficient_powers_injective
#print axioms ProximityGap.IncidenceFullScaleCores.scalar_injective
#print axioms ProximityGap.IncidenceFullScaleCores.exact_agreement_support
#print axioms ProximityGap.IncidenceFullScaleCores.allScalars_card
#print axioms ProximityGap.IncidenceFullScaleCores.allScalars_bad

#print axioms ProximityGap.IncidenceFullScaleCores.firstPrime_fullScale_upper
