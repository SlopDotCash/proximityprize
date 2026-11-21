/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusSubgroupBound
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed

/-! # Collision bounds for the transverse fourth head at eighth rate -/

namespace ArkLib.ProximityGap.Frontier.EighthTransverseMobius

open Finset SecondPrimeSmoothSeed PrizeShapePrimeP30Second
set_option maxRecDepth 10000
local instance : Fact P.Prime := ⟨prime_P⟩

/-- The thirteen ordinary quotient fibers that carry the variable direction. -/
def variableFiber : Fin 13 → Fin 32 := ![5,7,8,9,11,12,13,15,17,19,21,22,23]

/-- Upper bound for a full/subgroup or subgroup/subgroup collision graph. -/
theorem small_graph (full : Bool) {I : Type*} [Fintype I] (x y : I → F) (hi : Function.Injective x)
    (hx : ∀ i, (x i)^(if full then 2^30 else 2^25 : ℕ)=1)
    (hy : ∀ i, (y i)^(2^25 : ℕ)=1)
    {a b c e : F} (ha : a≠0) (hb : b≠0) (hc : c≠0) (hdet : a*e-b*c≠0)
    (hxy : ∀ i, a*x i+b=y i*(c*x i+e)) :
    Fintype.card I ≤ if full then 1243048 else 392196 := by
  cases full
  · have hh := _root_.ProximityGap.MobiusSubgroupBound.rectangular_graph
      (N:=2^25) (M:=2^25) (A:=131072) (B:=509) (C:=256) (D:=65279) prime_P
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) x y hi hx hy ha hb hc hdet hxy
    change Fintype.card I ≤ 392196
    omega
  · have hh := _root_.ProximityGap.MobiusSubgroupBound.rectangular_graph
      (N:=2^30) (M:=2^25) (A:=419430) (B:=5101) (C:=80) (D:=205908) prime_P
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) x y hi hx hy ha hb hc hdet hxy
    change Fintype.card I ≤ 1243048
    omega

/-- A finite-field projective matrix with the usual linear-fractional action. -/
structure Map where
  a : F
  b : F
  c : F
  d : F
  deriving DecidableEq

/-- Matrix of the second map inverse composed with the first, up to scalar. -/
def relative (f h : Map) : Map :=
  ⟨h.d*f.a-h.b*f.c,h.d*f.b-h.b*f.d,h.a*f.c-h.c*f.a,h.a*f.d-h.c*f.b⟩

def u : F := PrizeShapePrimeP30Second.g
def v : F := PrizeShapePrimeP30Second.g^(3 : ℕ)

/-- Coefficients of the line taking the two specified quotient values at u and v. -/
def intercept : F := 634331933699032925492590358005807727185199707295
def slope : F := 710284477582651152851487348699283527841344368941

/-- The fifteen finite poles, in the order of the two fixed and thirteen fiber maps. -/
def pole : Fin 15 → F := ![
  19564519496894670112370553195635338850177913162,
  52376359615579196269896564483276800731309245779,
  458524446188838711581087080261595616681306512389,
  452316735042211499771716570390461314081707376836,
  368922502247240332561774861027602065216573717440,
  171686055631833987706657350889221017833253120969,
  352194560330733956327308983337602027580404210825,
  78578928441940726680680596976655118247149872492,
  242939495191174525108162919193890914821173695991,
  156777336440006306489570702477829210127759263557,
  561187786008269774582089057441373072662425283096,
  723127978401692859711201246399983951683179730605,
  533547656346095535392659905159782426657488081870,
  143425621725385387041240408958504637237414511754,
  88828625691297937470091761036164736347492649309]

/-- Fractional label maps indexed by their poles and the projective point at infinity. -/
def labelMap (i : Fin 16) : Map :=
  if h : i.val=15 then ⟨-1,0,0,1⟩ else
    let j : Fin 15 := ⟨i.val,by omega⟩
    ⟨pole j-u-v,u*v,1,-pole j⟩

private def pval (j : Fin 32) : F := values (z^j.val) 1
private def qval (j : Fin 32) : F := values (z^j.val) 2

/-- The extra two interpolation constraints are satisfied on unpaired quotient fibers. -/
theorem marked :
    (intercept+slope*u)*pval 1=qval 1 ∧
    (intercept+slope*v)*pval 3=qval 3 ∧ slope≠0 ∧ u≠v ∧ u≠-v := by decide

/-- These poles implement exactly the two fixed and thirteen variable quotient values. -/
theorem poles :
    intercept+slope*pole 0=0 ∧ intercept+slope*pole 1=1 ∧
    ∀ i : Fin 13, pval (variableFiber i)≠0 ∧
      (intercept+slope*pole ⟨i.val+2,by omega⟩)*pval (variableFiber i)=qval (variableFiber i) := by
  decide

/-- Matrix entries and determinant for any two distinct label maps are nonzero. -/
theorem relative_regular : ∀ i j, i ≠ j →
    let r := relative (labelMap i) (labelMap j)
    r.a≠0 ∧ r.b≠0 ∧ r.c≠0 ∧ r.d≠0 ∧ r.a*r.d-r.b*r.c≠0 := by
  decide

/-- The fourth-coordinate row formula is a linear fractional label wherever its
second-row difference is nonzero. -/
theorem cross_label (x h : F) (hx : x≠h) :
    -x+(x-u)*(x-v)/(x-h) = ((h-u-v)*x+u*v)/(x-h) := by
  field_simp [sub_ne_zero.mpr hx]
  ring

private theorem union_cover {α : Type*} [DecidableEq α] (images : ℕ → Finset α) (n : ℕ) :
    ∑ i ∈ range n, (images i).card ≤ ((range n).biUnion images).card +
      ∑ i ∈ range n, ∑ j ∈ range i, (images j ∩ images i).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    have overlap : (((range n).biUnion images) ∩ images n).card ≤
        ∑ j ∈ range n, (images j ∩ images n).card := by
      rw [biUnion_inter]
      exact card_biUnion_le
    have total := card_union_add_card_inter ((range n).biUnion images) (images n)
    rw [sum_range_succ, sum_range_succ (f:=fun i => ∑ j ∈ range i, (images j ∩ images i).card),
      range_add_one, biUnion_insert, union_comm (images n)]
    omega

/-- The first three image sets are supported on the full domain, and the remaining
thirteen each lie over one small coset. Their pairwise intersection bounds give a
single union of more than the production budget from the regular incidences. -/
theorem image_mass {α : Type*} [DecidableEq α] (images : ℕ → Finset α)
    (incidences : 2239758337 ≤ 15 + ∑ i ∈ range 16, (images i).card)
    (overlap : ∀ i < 16, ∀ j < i, (images j ∩ images i).card ≤
        if i<3 then 3960117 else if j<3 then 1243048 else 392196) :
    2148807811 ≤ ((range 16).biUnion images).card := by
  have loss : (∑ i ∈ range 16, ∑ j ∈ range i, (images j ∩ images i).card) ≤ 90950511 := by
    calc
      _ ≤ ∑ i ∈ range 16, ∑ j ∈ range i,
          (if i<3 then 3960117 else if j<3 then 1243048 else 392196 : ℕ) :=
        sum_le_sum (fun i hi => sum_le_sum (fun j hj => overlap i (mem_range.mp hi) j (mem_range.mp hj)))
      _ = 90950511 := by decide
  have h := union_cover images 16
  omega

/-- Even after every possible pole and every pairwise intersection is removed,
the single-stack incidence schedule exceeds the production budget. -/
theorem budget : 2147483648 < 2148807811 ∧
    (2239758337 : ℕ) - 15 - (3*3960117+39*1243048+78*392196)=2148807811 ∧
    (2^30 : ℕ)-394264575-1=679477248 := by decide

#print axioms small_graph
#print axioms relative_regular
#print axioms poles
#print axioms image_mass
end ArkLib.ProximityGap.Frontier.EighthTransverseMobius
