/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.KKH26RegimeSplit

/-!
# The maximally enlarged smooth rate-quarter construction over P1

We enumerate the order-`2^30` subgroup as sixteen residue fibres.  The first
index is `(Fin 3 × Fin r) ⊕ Fin 1`: the three `Fin r` branches are transferred
from the old hole fibre into the three private cores, and the final singleton
is the genuinely affine hole.  This realizes the maximal split
`3r+1=m`, so only one hole coordinate remains.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 1200000
set_option maxRecDepth 250000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterScaleConstruction

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open HalfPredecessorRateQuarterMu16Locator
open HalfPredecessorCoreFreshDecode

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

/-- Three private branches of size `r`, followed by the singleton affine hole. -/
abbrev FibreIndex := (Fin 3 × Fin r) ⊕ Fin 1

/-- A quotient-fibre index and a sixteenth-root residue. -/
abbrev Coord := FibreIndex × Fin 16

/-- Natural index of a quotient-fibre label. -/
def fibreNat : FibreIndex → ℕ
  | Sum.inl iq => r * (iq.1 : ℕ) + (iq.2 : ℕ)
  | Sum.inr _ => 3 * r

theorem fibreNat_lt_m (j : FibreIndex) : fibreNat j < m := by
  have hmr := three_mul_r_add_one
  rcases j with ⟨i, q⟩ | h
  · have hq := q.isLt
    fin_cases i <;> simp only [fibreNat] <;> omega
  · simp only [fibreNat]
    omega

theorem fibreNat_injective : Function.Injective fibreNat := by
  intro x y h
  rcases x with ⟨ix, qx⟩ | hx
  · rcases y with ⟨iy, qy⟩ | hy
    · have hqx := qx.isLt
      have hqy := qy.isLt
      have hrp := r_pos
      fin_cases ix <;> fin_cases iy <;> simp only [fibreNat] at h
      · congr 2; apply Fin.ext; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · congr 2; apply Fin.ext; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · congr 2; apply Fin.ext; omega
    · have hqx := qx.isLt
      have hrp := r_pos
      fin_cases ix <;> simp only [fibreNat] at h
      all_goals exfalso; omega
  · rcases y with ⟨iy, qy⟩ | hy
    · have hqy := qy.isLt
      have hrp := r_pos
      fin_cases iy <;> simp only [fibreNat] at h
      all_goals exfalso; omega
    · exact congrArg Sum.inr (Subsingleton.elim hx hy)

/-- The ordinary power index `a+16j`, now with the split fibre label. -/
def coordIndex : Coord ↪ Fin N where
  toFun e := ⟨(e.2 : ℕ) + 16 * fibreNat e.1, by
    have hj := fibreNat_lt_m e.1
    have ha := e.2.isLt
    norm_num [N, m] at hj ⊢
    omega⟩
  inj' := by
    intro e e' h
    have hv : (e.2 : ℕ) + 16 * fibreNat e.1 =
        (e'.2 : ℕ) + 16 * fibreNat e'.1 := congrArg Fin.val h
    have ha := e.2.isLt
    have ha' := e'.2.isLt
    have hf : fibreNat e.1 = fibreNat e'.1 := by omega
    have hr : e.2 = e'.2 := Fin.ext (by omega)
    exact Prod.ext (fibreNat_injective hf) hr

theorem g_ne_zero : g ≠ (0 : F) := by decide

/-- The actual P1 smooth subgroup, re-enumerated by split fibres. -/
def domain : Coord ↪ F :=
  coordIndex.trans
    (_root_.ProximityGap.KKH26RegimeSplit.powDomain g orderOf_g g_ne_zero)

@[simp] theorem domain_apply (e : Coord) :
    domain e = g ^ ((e.2 : ℕ) + 16 * fibreNat e.1) := rfl

theorem g_pow_N : g ^ N = (1 : F) := by
  have h := pow_orderOf_eq_one g
  rw [orderOf_g] at h
  exact h

/-- Raising a domain point to `m` forgets the fibre label and leaves its
sixteenth-root residue. -/
theorem domain_pow_m (e : Coord) : domain e ^ m = z ^ (e.2 : ℕ) := by
  rw [domain_apply, ← pow_mul]
  calc
    g ^ (((e.2 : ℕ) + 16 * fibreNat e.1) * m) =
        g ^ (m * (e.2 : ℕ) + N * fibreNat e.1) := by
          congr 1
          norm_num [N, m]
          ring
    _ = g ^ (m * (e.2 : ℕ)) * (g ^ N) ^ fibreNat e.1 := by
          rw [pow_add, pow_mul g N (fibreNat e.1)]
    _ = g ^ (m * (e.2 : ℕ)) := by rw [g_pow_N]; simp
    _ = (g ^ m) ^ (e.2 : ℕ) := by rw [pow_mul]
    _ = z ^ (e.2 : ℕ) := by rw [g_pow_m]

theorem domain_ne_zero (e : Coord) : domain e ≠ 0 :=
  by rw [domain_apply]; exact pow_ne_zero _ g_ne_zero

theorem card_fibreIndex : Fintype.card FibreIndex = m := by
  norm_num [m, r]

theorem card_coord : Fintype.card Coord = N := by
  norm_num [N, m, r]

/-! ## The three polynomial directions -/

/-- A computable value-level version of the `A` locator. -/
def locatorAValue (x : F) : F :=
  (x - 1) * (x - z) * (x - z ^ 8)

/-- A computable value-level version of the `C` locator. -/
def locatorCValue (x : F) : F :=
  (x - z ^ 3) * (x - z ^ 5) * (x - z ^ 7)

/-- Direction values on the sixteen quotient residues. -/
def baseValue : Fin 3 → Fin 16 → F
  | 0, a => 0
  | 1, a => (1 - lambdaValue) * locatorAValue (z ^ (a : ℕ))
  | 2, a => locatorCValue (z ^ (a : ℕ))

/-- Cubic quotient polynomials for the three affine lines. -/
noncomputable def baseDirection : Fin 3 → F[X]
  | 0 => 0
  | 1 => C (1 - lambdaValue) * locatorA z
  | 2 => locatorC z

/-- Lift the quotient cubics along `X ↦ X^m`. -/
noncomputable def direction (i : Fin 3) : F[X] :=
  Polynomial.comp (baseDirection i) ((Polynomial.X : F[X]) ^ m)

/-- The line intercept is `X` times its direction. -/
noncomputable def intercept (i : Fin 3) : F[X] :=
  (Polynomial.X : F[X]) * direction i

theorem direction_eval (i : Fin 3) (e : Coord) :
    (direction i).eval (domain e) = baseValue i e.2 := by
  fin_cases i
  · simp [direction, baseDirection, baseValue]
  · simp only [direction, baseDirection, eval_comp, eval_pow, eval_X,
      domain_pow_m, eval_mul, eval_C]
    simp [baseValue, locatorAValue, locatorA]
  · simp only [direction, baseDirection, eval_comp, eval_pow, eval_X,
      domain_pow_m]
    simp [baseValue, locatorCValue, locatorC]

theorem baseValue_hole (i : Fin 3) : baseValue i 15 = holeValue i := by
  fin_cases i <;>
    simp [baseValue, locatorAValue, locatorCValue, holeValue, lambdaValue, z] <;>
    decide

theorem direction_eval_hole_fibre (i : Fin 3) (j : FibreIndex) :
    (direction i).eval (domain (j, 15)) = holeValue i := by
  rw [direction_eval, baseValue_hole]

theorem locatorProduct_natDegree_le_three (a b c : F) :
    ((Polynomial.X - C a) * (Polynomial.X - C b) *
      (Polynomial.X - C c) : F[X]).natDegree ≤ 3 := by
  have hfactor (d : F) : ((Polynomial.X : F[X]) - C d).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (Polynomial.natDegree_C d).le.trans (by omega)
  calc
    ((Polynomial.X - C a) * (Polynomial.X - C b) *
      (Polynomial.X - C c) : F[X]).natDegree ≤
        ((Polynomial.X - C a) * (Polynomial.X - C b) : F[X]).natDegree +
          ((Polynomial.X : F[X]) - C c).natDegree :=
      natDegree_mul_le
    _ ≤ (((Polynomial.X : F[X]) - C a).natDegree +
        ((Polynomial.X : F[X]) - C b).natDegree) +
        ((Polynomial.X : F[X]) - C c).natDegree :=
      Nat.add_le_add_right natDegree_mul_le _
    _ ≤ 3 := by
      have ha := hfactor a
      have hb := hfactor b
      have hc := hfactor c
      omega

theorem baseDirection_natDegree_le_three (i : Fin 3) :
    (baseDirection i).natDegree ≤ 3 := by
  fin_cases i
  · simp [baseDirection]
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      (by simpa only [locatorA] using locatorProduct_natDegree_le_three 1 z (z ^ 8))
  · simpa only [baseDirection, locatorC] using
      locatorProduct_natDegree_le_three (z ^ 3) (z ^ 5) (z ^ 7)

theorem direction_natDegree_le (i : Fin 3) :
    (direction i).natDegree ≤ 3 * m := by
  calc
    (direction i).natDegree ≤
        (baseDirection i).natDegree *
          ((Polynomial.X : F[X]) ^ m).natDegree :=
      natDegree_comp_le
    _ ≤ 3 * m := by
      rw [natDegree_X_pow]
      exact Nat.mul_le_mul_right m (baseDirection_natDegree_le_three i)

theorem direction_natDegree_lt_k (i : Fin 3) :
    (direction i).natDegree < k :=
  (direction_natDegree_le i).trans_lt (by norm_num [m, k])

theorem intercept_natDegree_lt_k (i : Fin 3) :
    (intercept i).natDegree < k := by
  have hmul : (intercept i).natDegree ≤ 1 + (direction i).natDegree := by
    simpa only [intercept, natDegree_X] using
      (natDegree_mul_le : ((Polynomial.X : F[X]) * direction i).natDegree ≤
        (Polynomial.X : F[X]).natDegree + (direction i).natDegree)
  have hdir := direction_natDegree_le i
  norm_num [m, k] at hdir ⊢
  omega

theorem degree_lt_of_natDegree_lt_k {p : F[X]}
    (hp : p.natDegree < k) : p.degree < (k : ℕ) := by
  by_cases hzero : p = 0
  · rw [hzero]
    exact WithBot.bot_lt_coe k
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hp

theorem direction_degree_lt_k (i : Fin 3) :
    (direction i).degree < (k : ℕ) :=
  degree_lt_of_natDegree_lt_k (direction_natDegree_lt_k i)

theorem intercept_degree_lt_k (i : Fin 3) :
    (intercept i).degree < (k : ℕ) :=
  degree_lt_of_natDegree_lt_k (intercept_natDegree_lt_k i)

theorem affine_natDegree_lt_k (i : Fin 3) (γ : F) :
    (intercept i + C γ * direction i).natDegree < k := by
  refine (natDegree_add_le _ _).trans_lt (max_lt (intercept_natDegree_lt_k i) ?_)
  exact (Polynomial.natDegree_C_mul_le _ _).trans_lt (direction_natDegree_lt_k i)

theorem affine_degree_lt_k (i : Fin 3) (γ : F) :
    (intercept i + C γ * direction i).degree < (k : ℕ) :=
  degree_lt_of_natDegree_lt_k (affine_natDegree_lt_k i γ)

/-! ## Residue cores and the enlarged private branches -/

/-- The original eight-fibre cores. -/
def baseCore : Fin 3 → Finset (Fin 16) := ![
  {0, 1, 3, 4, 5, 6, 7, 8},
  {0, 1, 2, 8, 9, 10, 11, 12},
  {2, 3, 5, 7, 9, 10, 13, 14}]

theorem baseCore_card (i : Fin 3) : (baseCore i).card = 8 := by
  fin_cases i <;> decide

theorem fifteen_not_mem_baseCore (i : Fin 3) : (15 : Fin 16) ∉ baseCore i := by
  fin_cases i <;> decide

/-- The line used to store the received pair on each old non-hole residue. -/
def ordinaryLine : Fin 16 → Fin 3 := ![
  0, 0, 1, 0, 0, 0, 0, 0,
  0, 1, 1, 1, 1, 2, 2, 0]

/-- The chosen received line has the same direction value as every line whose
base core contains that residue. -/
theorem locatorCValue_eq_scaledA_of_locatorB_root (x : F)
    (hx : (locatorB z).eval x = 0) :
    locatorCValue x = (1 - lambdaValue) * locatorAValue x := by
  have hpoly := locatorC_eq_affine z z_pow_eight (by decide : (2 : F) ≠ 0)
  have heval := congrArg (fun p : F[X] => p.eval x) hpoly
  simp only [eval_add, eval_mul, eval_C, hx, mul_zero, add_zero] at heval
  rw [lambdaValue_eq_locatorLambda]
  simpa only [locatorA, locatorC, locatorAValue, locatorCValue, eval_mul,
    eval_sub, eval_X, eval_C] using heval

theorem ordinaryLine_compatible (i : Fin 3) (a : Fin 16)
    (ha : a ∈ baseCore i) : baseValue (ordinaryLine a) a = baseValue i a := by
  fin_cases i
  · fin_cases a <;> simp [baseCore] at ha ⊢
    all_goals simp [ordinaryLine, baseValue]
  · fin_cases a <;> simp [baseCore] at ha ⊢
    all_goals simp [ordinaryLine, baseValue, locatorAValue]
  · fin_cases a <;> simp [baseCore] at ha ⊢
    · exact (locatorCValue_eq_scaledA_of_locatorB_root (z ^ 2)
        (locatorB_eval_z2 z)).symm
    · simp [ordinaryLine, baseValue, locatorCValue]
    · simp [ordinaryLine, baseValue, locatorCValue]
    · simp [ordinaryLine, baseValue, locatorCValue]
    · exact (locatorCValue_eq_scaledA_of_locatorB_root (z ^ 9)
        (locatorB_eval_z9 z)).symm
    · exact (locatorCValue_eq_scaledA_of_locatorB_root (z ^ 10)
        (locatorB_eval_z10 z)).symm
    · simp [ordinaryLine, baseValue]
    · simp [ordinaryLine, baseValue]

/-- Embedding of the private `Fin r` branch for line `i`. -/
def transferEmbedding (i : Fin 3) : Fin r ↪ FibreIndex where
  toFun q := Sum.inl (i, q)
  inj' := by intro q q' h; simpa using h

def transferIndices (i : Fin 3) : Finset FibreIndex :=
  Finset.univ.map (transferEmbedding i)

def ordinaryCore (i : Fin 3) : Finset Coord :=
  (Finset.univ : Finset FibreIndex).product (baseCore i)

def transferCore (i : Fin 3) : Finset Coord :=
  (transferIndices i).product {(15 : Fin 16)}

theorem mem_ordinaryCore_iff (i : Fin 3) (e : Coord) :
    e ∈ ordinaryCore i ↔ e.2 ∈ baseCore i := by
  change e ∈ ((Finset.univ : Finset FibreIndex) ×ˢ baseCore i) ↔ _
  simp only [Finset.mem_product, Finset.mem_univ, true_and]

theorem mem_transferIndices_iff (i : Fin 3) (j : FibreIndex) :
    j ∈ transferIndices i ↔ ∃ q : Fin r, j = Sum.inl (i, q) := by
  simp only [transferIndices, Finset.mem_map, Finset.mem_univ, true_and,
    transferEmbedding]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩

theorem mem_transferCore_iff (i : Fin 3) (e : Coord) :
    e ∈ transferCore i ↔
      (∃ q : Fin r, e.1 = Sum.inl (i, q)) ∧ e.2 = (15 : Fin 16) := by
  change e ∈ (transferIndices i ×ˢ {(15 : Fin 16)}) ↔ _
  rw [Finset.mem_product, mem_transferIndices_iff, Finset.mem_singleton]

/-- Membership predicate for an old eight-fibre core enlarged by its private
branch.  Keeping this predicate explicit makes later witness extraction
independent of the enormous concrete `Fin r` enumerator. -/
def corePred (i : Fin 3) (e : Coord) : Prop :=
  e.2 ∈ baseCore i ∨
    ((∃ q : Fin r, e.1 = Sum.inl (i, q)) ∧ e.2 = (15 : Fin 16))

/-- Each old `8m` core enlarged by one private branch of size `r`. -/
noncomputable def core (i : Fin 3) : Finset Coord := Finset.univ.filter (corePred i)

theorem core_eq_ordinary_union_transfer (i : Fin 3) :
    core i = ordinaryCore i ∪ transferCore i := by
  ext e
  simp only [core, corePred, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, mem_ordinaryCore_iff, mem_transferCore_iff]

theorem ordinaryCore_card (i : Fin 3) : (ordinaryCore i).card = 8 * m := by
  change ((Finset.univ : Finset FibreIndex) ×ˢ baseCore i).card = 8 * m
  rw [Finset.card_product, Finset.card_univ, baseCore_card, card_fibreIndex]
  omega

theorem transferIndices_card (i : Fin 3) : (transferIndices i).card = r := by
  simp [transferIndices]

theorem transferCore_card (i : Fin 3) : (transferCore i).card = r := by
  change (transferIndices i ×ˢ {(15 : Fin 16)}).card = r
  rw [Finset.card_product, transferIndices_card, Finset.card_singleton, Nat.mul_one]

theorem ordinaryCore_disjoint_transferCore (i : Fin 3) :
    Disjoint (ordinaryCore i) (transferCore i) := by
  change Disjoint
    ((Finset.univ : Finset FibreIndex) ×ˢ baseCore i)
    (transferIndices i ×ˢ {(15 : Fin 16)})
  rw [Finset.disjoint_product]
  exact Or.inr (Finset.disjoint_singleton_right.mpr (fifteen_not_mem_baseCore i))

theorem core_card (i : Fin 3) : (core i).card = 8 * m + r := by
  rw [core_eq_ordinary_union_transfer,
    Finset.card_union_of_disjoint (ordinaryCore_disjoint_transferCore i),
    ordinaryCore_card, transferCore_card]

/-- The singleton coordinate left after transferring all three `Fin r`
branches into private cores. -/
def hole : Coord := (Sum.inr 0, 15)

theorem hole_not_mem_core (i : Fin 3) : hole ∉ core i := by
  rw [core_eq_ordinary_union_transfer, Finset.mem_union]
  push Not
  constructor
  · rw [mem_ordinaryCore_iff]
    exact fifteen_not_mem_baseCore i
  · rw [mem_transferCore_iff]
    intro h
    obtain ⟨⟨q, hq⟩, -⟩ := h
    cases hq

/-- Which polynomial line supplies the received pair.  Only `hole` has none. -/
def lineAt (e : Coord) : Option (Fin 3) :=
  if e.2 = (15 : Fin 16) then
    match e.1 with
    | Sum.inl iq => some iq.1
    | Sum.inr _ => none
  else
    some (ordinaryLine e.2)

theorem lineAt_hole : lineAt hole = none := by simp [lineAt, hole]

/-- Direction row of the received stack; the affine hole value is `2`. -/
noncomputable def u1 (e : Coord) : F :=
  match lineAt e with
  | some i => (direction i).eval (domain e)
  | none => 2

/-- Intercept row of the received stack; line points use `(x t,t)`, while
the affine hole row is `(x,2)`. -/
noncomputable def u0 (e : Coord) : F :=
  match lineAt e with
  | some i => domain e * (direction i).eval (domain e)
  | none => domain e

noncomputable def u : WordStack F (Fin 2) Coord :=
  fun row => Fin.cases u0 (fun _ => u1) row

@[simp] theorem u_zero : u 0 = u0 := rfl
@[simp] theorem u_one : u 1 = u1 := rfl

theorem lineAt_transfer (i : Fin 3) (q : Fin r) :
    lineAt (Sum.inl (i, q), (15 : Fin 16)) = some i := by simp [lineAt]

set_option maxHeartbeats 50000 in
theorem core_pair_agreement (i : Fin 3) (e : Coord) (he : e ∈ core i) :
    (intercept i).eval (domain e) = u0 e ∧
      (direction i).eval (domain e) = u1 e := by
  simp only [core, corePred, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rcases he with hbase | heTransfer
  ·
    have hne15 : e.2 ≠ (15 : Fin 16) := by
      intro h
      rw [h] at hbase
      exact fifteen_not_mem_baseCore i hbase
    have hcompat := ordinaryLine_compatible i e.2 hbase
    have hline : lineAt e = some (ordinaryLine e.2) := by simp [lineAt, hne15]
    have hu0 : u0 e = domain e * (direction (ordinaryLine e.2)).eval (domain e) := by
      simp only [u0, hline]
    have hu1 : u1 e = (direction (ordinaryLine e.2)).eval (domain e) := by
      simp only [u1, hline]
    constructor
    · rw [intercept, eval_mul, eval_X, hu0, direction_eval, direction_eval, hcompat]
    · rw [hu1, direction_eval, direction_eval, hcompat]
  · obtain ⟨⟨q, heq1⟩, heq2⟩ := heTransfer
    have heq : e = (Sum.inl (i, q), (15 : Fin 16)) := Prod.ext heq1 heq2
    subst e
    constructor
    · simp only [intercept, eval_mul, eval_X, u0, lineAt_transfer]
    · simp only [u1, lineAt_transfer]

theorem u0_hole : u0 hole = domain hole := by
  change (match lineAt hole with
      | some i => domain hole * (direction i).eval (domain hole)
      | none => domain hole) = domain hole
  rw [lineAt_hole]

theorem u1_hole : u1 hole = 2 := by
  change (match lineAt hole with
      | some i => (direction i).eval (domain hole)
      | none => 2) = 2
  rw [lineAt_hole]

theorem hole_rows : u0 hole = domain hole ∧ u1 hole = 2 := ⟨u0_hole, u1_hole⟩

/-
/-! ## The `N-1` safe scalars -/

/-- A line outside the core of each old non-hole residue. -/
def ordinarySafeSource : Fin 16 → Fin 3 := ![
  2, 2, 0, 1, 1, 1, 1, 1,
  2, 0, 0, 0, 0, 0, 0, 0]

/-- On a transferred hole coordinate, use a different line. -/
def transferSafeSource (i : Fin 3) : Fin 3 := if i = 0 then 1 else 0

theorem transferSafeSource_ne (i : Fin 3) : transferSafeSource i ≠ i := by
  fin_cases i <;> decide

/-- The certifying line for the scalar `-x` attached to a non-hole coordinate. -/
def safeSource (e : Coord) : Fin 3 :=
  if e.2 = (15 : Fin 16) then
    match e.1 with
    | Sum.inl iq => transferSafeSource iq.1
    | Sum.inr _ => 0
  else
    ordinarySafeSource e.2

theorem ordinarySafeSource_not_mem (a : Fin 16) (ha : a ≠ 15) :
    a ∉ baseCore (ordinarySafeSource a) := by
  fin_cases a <;> simp at ha <;> decide

set_option maxHeartbeats 1200000 in
theorem ordinarySafeSource_mismatch (a : Fin 16) (ha : a ≠ 15) :
    baseValue (ordinarySafeSource a) a ≠ baseValue (ordinaryLine a) a := by
  fin_cases a <;> simp at ha
  all_goals
    simp [ordinarySafeSource, ordinaryLine, baseValue, locatorAValue,
      locatorCValue, lambdaValue, z]
  all_goals decide

theorem coord_eq_hole_of_fibre_inr_residue_fifteen
    (e : Coord) (j : Fin 1) (hj : e.1 = Sum.inr j)
    (h15 : e.2 = (15 : Fin 16)) : e = hole := by
  apply Prod.ext
  · rw [hj]
    exact congrArg Sum.inr (Subsingleton.elim j 0)
  · exact h15

theorem safeSource_not_mem_core (e : Coord) (he : e ≠ hole) :
    e ∉ core (safeSource e) := by
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
  by_cases h15 : e.2 = (15 : Fin 16)
  · rcases hfirst : e.1 with iq | j
    · rcases iq with ⟨i, q⟩
      intro hcore
      rcases hcore with hbase | ⟨⟨q', heq⟩, -⟩
      · rw [h15] at hbase
        exact fifteen_not_mem_baseCore (safeSource e) hbase
      · have hi : i = transferSafeSource i := by
          have := congrArg (fun x : FibreIndex =>
            match x with
            | Sum.inl iq => iq.1
            | Sum.inr _ => 0) heq
          simpa [safeSource, h15, hfirst] using this
        exact transferSafeSource_ne i hi.symm
    · exact (he (coord_eq_hole_of_fibre_inr_residue_fifteen e j hfirst h15)).elim
  · intro hcore
    rcases hcore with hbase | ⟨-, hres⟩
    · have hs : safeSource e = ordinarySafeSource e.2 := by simp [safeSource, h15]
      rw [hs] at hbase
      exact ordinarySafeSource_not_mem e.2 h15 hbase
    · exact h15 hres

theorem received_rows_on_line_of_ne_hole (e : Coord) (he : e ≠ hole) :
    u0 e = domain e * u1 e := by
  by_cases h15 : e.2 = (15 : Fin 16)
  · rcases hfirst : e.1 with ⟨i, q⟩ | j
    · have hline : lineAt e = some i := by
        rw [show e = (Sum.inl (i, q), (15 : Fin 16)) from Prod.ext hfirst h15]
        exact lineAt_transfer i q
      simp only [u0, u1, hline]
    · exact (he (coord_eq_hole_of_fibre_inr_residue_fifteen e j hfirst h15)).elim
  · have hline : lineAt e = some (ordinaryLine e.2) := by simp [lineAt, h15]
    simp only [u0, u1, hline]

theorem safe_direction_mismatch (e : Coord) (he : e ≠ hole) :
    (direction (safeSource e)).eval (domain e) ≠ u1 e := by
  by_cases h15 : e.2 = (15 : Fin 16)
  · rcases hfirst : e.1 with ⟨i, q⟩ | j
    · have heq : e = (Sum.inl (i, q), (15 : Fin 16)) := Prod.ext hfirst h15
      subst e
      simp only [safeSource, lineAt_transfer, u1, direction_eval_hole_fibre]
      exact fun h => transferSafeSource_ne i (holeValue_pairwise_ne h)
    · exact (he (coord_eq_hole_of_fibre_inr_residue_fifteen e j hfirst h15)).elim
  · have hline : lineAt e = some (ordinaryLine e.2) := by simp [lineAt, h15]
    simp only [safeSource, h15, u1, hline, direction_eval]
    exact ordinarySafeSource_mismatch e.2 h15

theorem safe_fresh_agreement (e : Coord) (he : e ≠ hole) :
    (intercept (safeSource e) + C (-domain e) * direction (safeSource e)).eval
        (domain e) = u0 e + (-domain e) * u1 e := by
  rw [eval_add, eval_mul, eval_C, intercept, eval_mul, eval_X,
    received_rows_on_line_of_ne_hole e he]
  ring

theorem safe_fresh_pair_mismatch (e : Coord) (he : e ≠ hole) :
    ((intercept (safeSource e)).eval (domain e),
      (direction (safeSource e)).eval (domain e)) ≠ (u0 e, u1 e) := by
  intro hpair
  exact safe_direction_mismatch e he (congrArg Prod.snd hpair)

theorem core_card_ge_k (i : Fin 3) : k ≤ (core i).card := by
  rw [core_card]
  norm_num [k, m, r]

theorem core_fresh_size_condition (i : Fin 3) :
    (((core i).card + 1 : ℕ) : ℝ≥0) ≥
      (1 - delta) * (Fintype.card Coord : ℝ≥0) := by
  rw [core_card, card_coord, agreement_mass_eq_threshold]

/-- All coordinates except the singleton affine hole. -/
noncomputable def safeCoords : Finset Coord := Finset.univ.erase hole

abbrev SafeCoord := {e : Coord // e ≠ hole}

theorem safeCoords_card : safeCoords.card = N - 1 := by
  rw [safeCoords, Finset.card_erase_of_mem (Finset.mem_univ hole),
    Finset.card_univ, card_coord]

theorem safeCoord_ne_hole (e : SafeCoord) : (e : Coord) ≠ hole := by
  exact e.property

theorem safe_fresh_agreement_stack (e : SafeCoord) :
    (intercept (safeSource (e : Coord)) + C (-domain (e : Coord)) *
      direction (safeSource (e : Coord))).eval (domain (e : Coord)) =
      u 0 (e : Coord) + (-domain (e : Coord)) * u 1 (e : Coord) := by
  rw [u_zero, u_one]
  exact safe_fresh_agreement (e : Coord) e.property

theorem safe_fresh_pair_mismatch_stack (e : SafeCoord) :
    ((intercept (safeSource (e : Coord))).eval (domain (e : Coord)),
      (direction (safeSource (e : Coord))).eval (domain (e : Coord))) ≠
      (u 0 (e : Coord), u 1 (e : Coord)) := by
  rw [u_zero, u_one]
  exact safe_fresh_pair_mismatch (e : Coord) e.property

/-- Every non-hole coordinate supplies the safe scalar `γ=-x`. -/
theorem safe_mcaEvent (e : SafeCoord) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
      delta (u 0) (u 1) (-domain (e : Coord)) := by
  let i := safeSource (e : Coord)
  apply mcaEvent_of_affine_core_fresh domain k delta u (-domain (e : Coord))
    (core i) (e : Coord) (intercept i) (direction i)
  · exact safeSource_not_mem_core (e : Coord) (safeCoord_ne_hole e)
  · exact intercept_degree_lt_k i
  · exact direction_degree_lt_k i
  · exact affine_degree_lt_k i (-domain (e : Coord))
  · exact core_card_ge_k i
  · exact core_fresh_size_condition i
  · intro x hx
    exact core_pair_agreement_stack i x hx
  · exact safe_fresh_agreement_stack e
  · exact safe_fresh_pair_mismatch_stack e

/-! ## The three unsafe singleton-hole scalars -/

theorem hole_not_mem_core (i : Fin 3) : hole ∉ core i := by
  simp [core, corePred, hole, fifteen_not_mem_baseCore]

theorem unsafeConstant_cross (i : Fin 3) :
    unsafeConstant i * (2 - holeValue i) = holeValue i - 1 := by
  fin_cases i <;> decide

theorem direction_eval_hole (i : Fin 3) :
    (direction i).eval (domain hole) = holeValue i := by
  change (direction i).eval (domain (Sum.inr 0, 15)) = holeValue i
  exact direction_eval_hole_fibre i (Sum.inr 0)

theorem unsafe_fresh_agreement (i : Fin 3) :
    (intercept i + C (unsafeConstant i * domain hole) * direction i).eval
        (domain hole) =
      u0 hole + (unsafeConstant i * domain hole) * u1 hole := by
  rw [eval_add, eval_mul, eval_C, intercept, eval_mul, eval_X,
    direction_eval_hole, u0_hole, u1_hole]
  have hc := unsafeConstant_cross i
  linear_combination -(domain hole) * hc

theorem unsafe_fresh_pair_mismatch (i : Fin 3) :
    ((intercept i).eval (domain hole), (direction i).eval (domain hole)) ≠
      (u0 hole, u1 hole) := by
  intro hpair
  have hsecond := congrArg Prod.snd hpair
  rw [direction_eval_hole, u1_hole] at hsecond
  exact holeValue_ne_two i hsecond

theorem unsafe_fresh_agreement_stack (i : Fin 3) :
    (intercept i + C (unsafeConstant i * domain hole) * direction i).eval
        (domain hole) =
      u 0 hole + (unsafeConstant i * domain hole) * u 1 hole := by
  rw [u_zero, u_one]
  exact unsafe_fresh_agreement i

theorem unsafe_fresh_pair_mismatch_stack (i : Fin 3) :
    ((intercept i).eval (domain hole), (direction i).eval (domain hole)) ≠
      (u 0 hole, u 1 hole) := by
  rw [u_zero, u_one]
  exact unsafe_fresh_pair_mismatch i

/-- Each polynomial line supplies one additional scalar at the singleton hole. -/
theorem unsafe_mcaEvent (i : Fin 3) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
      delta (u 0) (u 1) (unsafeConstant i * domain hole) := by
  apply mcaEvent_of_affine_core_fresh domain k delta u
    (unsafeConstant i * domain hole) (core i) hole (intercept i) (direction i)
  · exact hole_not_mem_core i
  · exact intercept_degree_lt_k i
  · exact direction_degree_lt_k i
  · exact affine_degree_lt_k i (unsafeConstant i * domain hole)
  · exact core_card_ge_k i
  · exact core_fresh_size_condition i
  · intro x hx
    exact core_pair_agreement_stack i x hx
  · exact unsafe_fresh_agreement_stack i
  · exact unsafe_fresh_pair_mismatch_stack i
-/

end ArkLib.ProximityGap.Frontier.P1RateQuarterScaleConstruction

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleConstruction
#print axioms domain_pow_m
#print axioms direction_eval
#print axioms core_card
#print axioms core_pair_agreement
