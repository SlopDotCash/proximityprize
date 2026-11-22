/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseMobius

/-! # Actual union of the sixteen transverse label images -/
namespace ArkLib.ProximityGap.Frontier.EighthTransverseCollisions
open Finset SecondPrimeSmoothSeed EighthTransverseMobius PrizeShapePrimeP30Second
open _root_.ProximityGap.MobiusSeamCoordinateSupply (Mobius)
local instance : Fact P.Prime := ⟨prime_P⟩

/-- Put the ordinary map first, then the two fixed poles, then the thirteen
variable poles in the order of `variableFiber`. -/
def mapIndex (i : Fin 16) : Fin 16 := ⟨(i.val+15)%16,by omega⟩

/-- The concrete fractional linear map in the incidence count's ordering. -/
def chart (i : Fin 16) : Mobius F :=
  let m := labelMap (mapIndex i)
  ⟨m.a,m.b,m.c,m.d⟩

theorem chart_det (i : Fin 16) : (chart i).det≠0 :=
  (by decide : ∀ j : Fin 16, (chart j).det≠0) i

variable {I : Type*}

/-- Coordinates of one specified site family after removing its possible pole. -/
def nonpoles (coord : I ↪ F) (i : Fin 16) (s : Finset I) : Finset I :=
  s.filter fun x => (chart i).den (coord x) ≠ 0

/-- Distinct labels supplied by one site family. -/
def labels (coord : I ↪ F) (i : Fin 16) (s : Finset I) : Finset F :=
  (nonpoles coord i s).image fun x => (chart i).value (coord x)

theorem labels_card (coord : I ↪ F) (i : Fin 16) (s : Finset I) :
    (labels coord i s).card=(nonpoles coord i s).card := by
  apply card_image_of_injOn
  intro a ha b hb eq
  exact coord.injective ((chart i).injective_on_finite (chart_det _) (mem_filter.mp ha).2
    (mem_filter.mp hb).2 eq)

theorem pole_loss (coord : I ↪ F) (i : Fin 16) (s : Finset I) :
    s.card ≤ (labels coord i s).card + (if i=0 then 0 else 1) := by
  rw [labels_card]
  have part := card_filter_add_card_filter_not (s:=s) (p:=fun x => (chart i).den (coord x) ≠ 0)
  change (nonpoles coord i s).card+_=_ at part
  by_cases hz : i=0
  · subst i
    have reg : nonpoles coord 0 s=s := by
      ext x
      have hh : (chart 0).den (coord x)=1 := by
        change (0:F)*coord x+1=1
        simp
      simp [nonpoles,hh]
    simp [reg]
  · have coeff := (by decide : ∀ j : Fin 16, j≠0 → (chart j).c≠0) i hz
    have bound : (s.filter fun x => ¬ (chart i).den (coord x) ≠ 0).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      have h₁ := not_ne_iff.mp (mem_filter.mp ha).2
      have h₂ := not_ne_iff.mp (mem_filter.mp hb).2
      apply coord.injective
      have eq : (chart i).c * (coord a - coord b)=0 := by
        unfold Mobius.den at h₁ h₂
        linear_combination h₁ - h₂
      exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left coeff)
    simp [hz]
    omega

/-- Coordinates in one coset all have the same power at this exponent. -/
def exponent (i : Fin 16) : ℕ := if i.val < 3 then 2^30 else 2^25

private theorem rescaled_graph {T : Type*} [Fintype T] [Nonempty T]
    (j i : Fin 16) (ltji : j < i) (x y : T → F) (inj : Function.Injective x)
    (xn : ∀ t, x t≠0) (yn : ∀ t, y t≠0)
    (xp : ∀ t v, (x t)^exponent j=(x v)^exponent j)
    (yp : ∀ t v, (y t)^exponent i=(y v)^exponent i)
    (hx : ∀ t, (chart j).den (x t)≠0) (hy : ∀ t, (chart i).den (y t)≠0)
    (eq : ∀ t, (chart j).value (x t)=(chart i).value (y t)) :
    Fintype.card T ≤ if i.val < 3 then 3960117 else if j.val < 3 then 1243048 else 392196 := by
  classical
  let t := Classical.choice ‹Nonempty T›
  let f := chart j
  let g := chart i
  let r := relative (labelMap (mapIndex j)) (labelMap (mapIndex i))
  have hij : mapIndex j ≠ mapIndex i := by
    intro h
    have := congrArg Fin.val h
    change (j.val+15)%16=(i.val+15)%16 at this
    omega
  obtain ⟨ha,hb,hc,_,hd⟩ := relative_regular _ _ hij
  let a := r.a*x t
  let b := r.b
  let c := y t*r.c*x t
  let d := y t*r.d
  have ar : a≠0 := mul_ne_zero ha (xn t)
  have cr : c≠0 := mul_ne_zero (mul_ne_zero (yn t) hc) (xn t)
  have dr : a*d-b*c≠0 := by
    have h : a*d-b*c=x t*y t*(r.a*r.d-r.b*r.c) := by dsimp [a,b,c,d];ring
    rw [h]
    exact mul_ne_zero (mul_ne_zero (xn t) (yn t)) hd
  let X₁ (v : T) := x v/x t
  let Y₁ (v : T) := y v/y t
  have xi : Function.Injective X₁ := fun _ _ h => inj ((div_left_inj' (xn t)).mp h)
  have xone (v : T) : (X₁ v)^exponent j=1 := by
    dsimp only [X₁]
    rw [div_pow,xp v t,div_self (pow_ne_zero _ (xn t))]
  have yone (v : T) : (Y₁ v)^exponent i=1 := by
    dsimp only [Y₁]
    rw [div_pow,yp v t,div_self (pow_ne_zero _ (yn t))]
  have graph (v : T) : a*X₁ v+b=Y₁ v*(c*X₁ v+d) := by
    have cross := (div_eq_div_iff (hx v) (hy v)).mp (eq v)
    change (f.a*x v+f.b)*(g.c*y v+g.d)=(g.a*y v+g.b)*(f.c*x v+f.d) at cross
    have h : r.a*x v+r.b=y v*(r.c*x v+r.d) := by
      dsimp [r,relative] at ⊢
      dsimp [f,g,chart] at cross
      linear_combination cross
    dsimp [a,b,c,d,X₁,Y₁]
    field_simp [xn t,yn t]
    linear_combination h
  by_cases hi : i.val < 3
  · have hj : j.val < 3 := by omega
    simp [hi]
    apply _root_.ProximityGap.MobiusSubgroupBound.production_graph prime_P (by decide) X₁ Y₁ xi
      (fun v => by simpa [exponent,hj] using xone v)
      (fun v => by simpa [exponent,hi] using yone v) dr (Or.inl hb) (Or.inl ar) graph
  · simp [hi]
    by_cases hj : j.val < 3
    · simpa [hj] using small_graph true X₁ Y₁ xi (fun v => by simpa [exponent,hj] using xone v)
        (fun v => by simpa [exponent,hi] using yone v) ar hb cr dr graph
    · simpa [hj] using small_graph false X₁ Y₁ xi (fun v => by simpa [exponent,hj] using xone v)
        (fun v => by simpa [exponent,hi] using yone v) ar hb cr dr graph

/-- Select one original input in each family for every common output label.
Rescaling those coordinates inside their respective cosets gives the three
unconditional intersection bounds. -/
theorem overlap (coord : I ↪ F) (j i : Fin 16) (ltji : j < i) (s t : Finset I)
    (sn : ∀ x∈s, coord x≠0) (tn : ∀ x∈t, coord x≠0)
    (sp : ∀ x∈s, ∀ y∈s, (coord x)^exponent j=(coord y)^exponent j)
    (tp : ∀ x∈t, ∀ y∈t, (coord x)^exponent i=(coord y)^exponent i) :
    ((labels coord j s) ∩ (labels coord i t)).card ≤
      if i.val < 3 then 3960117 else if j.val < 3 then 1243048 else 392196 := by
  classical
  let U := labels coord j s ∩ labels coord i t
  change U.card ≤ _
  rcases U.eq_empty_or_nonempty with he|hU
  · simp [he]
  let T := ↥U
  have : Nonempty T := hU.to_subtype
  have left (q : T) := mem_image.mp (mem_inter.mp q.property).1
  have right (q : T) := mem_image.mp (mem_inter.mp q.property).2
  choose x hx ex using left
  choose y hy ey using right
  have h := rescaled_graph j i ltji (fun q => coord (x q)) (fun q => coord (y q))
    (fun q r eq => Subtype.ext ((ex q).symm.trans ((congrArg (chart j).value eq).trans (ex r))))
    (fun q => sn _ (mem_filter.mp (hx q)).1) (fun q => tn _ (mem_filter.mp (hy q)).1)
    (fun a b => sp _ (mem_filter.mp (hx a)).1 _ (mem_filter.mp (hx b)).1)
    (fun a b => tp _ (mem_filter.mp (hy a)).1 _ (mem_filter.mp (hy b)).1)
    (fun q => (mem_filter.mp (hx q)).2) (fun q => (mem_filter.mp (hy q)).2)
    (fun q => (ex q).trans (ey q).symm)
  simpa only [T,Fintype.card_coe] using h

/-- The total incidence bound alone implies the required union mass for any
sixteen input families respecting the full-domain and small-coset powers. -/
theorem union_mass (coord : I ↪ F) (S : Fin 16 → Finset I)
    (size : 2239758337 ≤ ∑ i, (S i).card)
    (hn : ∀ i, ∀ x∈S i, coord x≠0)
    (hp : ∀ i, ∀ x∈S i, ∀ y∈S i, (coord x)^exponent i=(coord y)^exponent i) :
    2148807811 ≤ (univ.biUnion fun i => labels coord i (S i)).card := by
  classical
  let images (i : ℕ) := labels coord (Fin.ofNat 16 i) (S (Fin.ofNat 16 i))
  have cast (i : Fin 16) : Fin.ofNat 16 i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have sumEq : (∑ i ∈ range 16, (images i).card) = ∑ i : Fin 16, (labels coord i (S i)).card := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl (fun i _ => by dsimp only [images];rw [cast i])
  have losses := sum_le_sum (s:=(univ : Finset (Fin 16))) (fun i _ => pole_loss coord i (S i))
  rw [sum_add_distrib] at losses
  have loss : (∑ i : Fin 16, (if i=0 then 0 else 1 : ℕ)) = 15 := by decide
  rw [loss] at losses
  have mass := image_mass images (by rw [sumEq];omega) (fun i hi j hj => by
    let i' : Fin 16 := ⟨i,hi⟩
    let j' : Fin 16 := ⟨j,by omega⟩
    have h := overlap coord j' i' (show j' < i' from hj) (S j') (S i') (hn _) (hn _) (hp _) (hp _)
    change ((labels coord (Fin.ofNat 16 j'.val) (S (Fin.ofNat 16 j'.val))) ∩
      (labels coord (Fin.ofNat 16 i'.val) (S (Fin.ofNat 16 i'.val)))).card ≤ _
    rw [cast j',cast i']
    exact h)
  apply mass.trans (card_le_card ?_)
  intro z hz
  obtain ⟨i,_,hit⟩ := mem_biUnion.mp hz
  exact mem_biUnion.mpr ⟨Fin.ofNat 16 i, mem_univ _,hit⟩

/-- Entry point for the actual smooth domain. The last thirteen input subsets
need only advertise their quotient index modulo 32. -/
theorem smooth_union_mass (S : Fin 16 → Finset (Fin N))
    (size : 2239758337 ≤ ∑ i, (S i).card)
    (cosets : ∀ (i : Fin 16) (hi : 3 ≤ i.val), ∀ x ∈ S i,
      x.val%32=(variableFiber ⟨i.val-3,by omega⟩).val) :
    2148807811 ≤ (univ.biUnion fun i => labels dom i (S i)).card := by
  let gen := PrizeShapePrimeP30Second.g
  have gn : gen≠0 := _root_.ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g
  have gp : gen^(2^30 : ℕ)=1 := by simpa only [gen,orderOf_g] using pow_orderOf_eq_one PrizeShapePrimeP30Second.g
  apply union_mass dom S size
  · intro i x hx
    exact pow_ne_zero _ gn
  · intro i x hx y hy
    change (gen^x.val)^exponent i=(gen^y.val)^exponent i
    by_cases hi : i.val < 3
    · have eq (v : ℕ) : (gen^v)^(2^30 : ℕ)=1 := by
        rw [← pow_mul,Nat.mul_comm,pow_mul,gp,one_pow]
      rw [show exponent i=2^30 by simp [exponent,hi],eq x.val,eq y.val]
    · let b := gen^(2^25 : ℕ)
      have bp : b^32=1 := by
        change (gen^(2^25 : ℕ))^32=1
        rw [← pow_mul]
        exact gp
      have eq (v : ℕ) : (gen^v)^(2^25 : ℕ)=b^(v%32) := by
        rw [← pow_mul,Nat.mul_comm,pow_mul]
        change b^v = b^(v%32)
        calc
          _ = b^(v%32+32*(v/32)) := congrArg (b^·) (Nat.mod_add_div _ _).symm
          _ = _ := by rw [pow_add,pow_mul,bp,one_pow,mul_one]
      rw [show exponent i=2^25 by simp [exponent,hi],eq x.val,eq y.val]
      rw [cosets i (by omega) x hx,cosets i (by omega) y hy]

#print axioms overlap
#print axioms smooth_union_mass
end ArkLib.ProximityGap.Frontier.EighthTransverseCollisions
