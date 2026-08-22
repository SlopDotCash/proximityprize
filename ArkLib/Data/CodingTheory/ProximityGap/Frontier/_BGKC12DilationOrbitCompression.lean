/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLateNewtonTwoColourPhysicalBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKC12TranslateIntersectionReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R348PeriodSquareRecursion

/-!
# Multiplicative-orbit compression of the late Newton `C12` alignment

Scratch lane for issue #466.  This file studies the exact multiplicative symmetry of the two
physical rows in the translate/intersection factorization of `C12`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKC12DilationOrbitCompression

open ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance
open ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge
open ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction
open ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion

section ExactSymmetry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Every member of a finite multiplicative subgroup of a field is nonzero. -/
theorem mem_ne_zero (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) : a ≠ 0 := by
  obtain ⟨ai, _hai, haai⟩ := hG.exists_inv a ha
  intro haz
  rw [haz, zero_mul] at haai
  exact zero_ne_one haai

/-- A chosen inverse supplied by the finite-subgroup package. -/
noncomputable def subgroupInverse (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) : F :=
  Classical.choose (hG.exists_inv a ha)

theorem subgroupInverse_mem (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) : subgroupInverse G hG ha ∈ G :=
  (Classical.choose_spec (hG.exists_inv a ha)).1

theorem mul_subgroupInverse (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) : a * subgroupInverse G hG ha = 1 :=
  (Classical.choose_spec (hG.exists_inv a ha)).2

/-- Multiplication by a subgroup member is a permutation of the labelled copy of `G`. -/
noncomputable def pointDilationEquiv (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) : {x : F // x ∈ G} ≃ {x : F // x ∈ G} :=
    { toFun := fun x => ⟨a * x.1, hG.mul_mem a ha x.1 x.2⟩
      invFun := fun x => ⟨subgroupInverse G hG ha * x.1,
        hG.mul_mem _ (subgroupInverse_mem G hG ha) x.1 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        change subgroupInverse G hG ha * (a * x.1) = x.1
        rw [← mul_assoc, mul_comm (subgroupInverse G hG ha) a,
          mul_subgroupInverse G hG ha, one_mul]
      right_inv := fun x => by
        apply Subtype.ext
        change a * (subgroupInverse G hG ha * x.1) = x.1
        rw [← mul_assoc, mul_subgroupInverse G hG ha, one_mul] }

@[simp] theorem pointDilationEquiv_apply_val (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (x : {x : F // x ∈ G}) :
    (pointDilationEquiv G hG ha x).1 = a * x.1 := by
  rfl

/-- Dilation of a fixed-cardinality labelled subset. -/
noncomputable def subsetDilationEquiv (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (m : Nat) : SubsetAt G m ≃ SubsetAt G m :=
  ((pointDilationEquiv G hG ha).finsetCongr).subtypeEquiv fun S => by
    simp only [Finset.mem_powersetCard, Equiv.finsetCongr_apply, Finset.subset_univ,
      true_and, Finset.card_map]

/-- Dilation scales the sum of a labelled subset by the same scalar. -/
theorem subsetDilationEquiv_sum (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (m : Nat) (S : SubsetAt G m) :
    (∑ x ∈ (subsetDilationEquiv G hG ha m S).1, x.1) =
      a * ∑ x ∈ S.1, x.1 := by
  classical
  change (∑ x ∈ S.1.map (pointDilationEquiv G hG ha).toEmbedding, x.1) = _
  calc
    (∑ x ∈ S.1.map (pointDilationEquiv G hG ha).toEmbedding, x.1) =
        ∑ x ∈ S.1, (pointDilationEquiv G hG ha x).1 := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ x ∈ S.1, a * x.1 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact pointDilationEquiv_apply_val G hG ha x
    _ = a * ∑ x ∈ S.1, x.1 := by rw [Finset.mul_sum]

/-- Marked-pair source for the physical row `W_G`. -/
abbrev MarkedPair (G : Finset F) := {x : F // x ∈ G} × {y : F // y ∈ G}

/-- Adjacent subset source for the physical row `R_r`. -/
abbrev AdjacentSubsetPair (G : Finset F) (r : Nat) := SubsetAt G r × SubsetAt G (r - 1)

/-- Marked difference phase `2*y-x`. -/
def markedDifferencePhase (G : Finset F) (z : MarkedPair G) : F :=
  2 * z.2.1 - z.1.1

/-- Adjacent subset-sum difference phase. -/
noncomputable def subsetDifferencePhase (G : Finset F) (r : Nat)
    (z : AdjacentSubsetPair G r) : F :=
  (∑ x ∈ z.1.1, x.1) - ∑ y ∈ z.2.1, y.1

/-- Multiplication by a subgroup member on marked pairs. -/
noncomputable def markedPairDilationEquiv (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) : MarkedPair G ≃ MarkedPair G :=
  Equiv.prodCongr (pointDilationEquiv G hG ha) (pointDilationEquiv G hG ha)

/-- Multiplication by a subgroup member on adjacent subset pairs. -/
noncomputable def adjacentSubsetPairDilationEquiv (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (r : Nat) :
    AdjacentSubsetPair G r ≃ AdjacentSubsetPair G r :=
  Equiv.prodCongr (subsetDilationEquiv G hG ha r)
    (subsetDilationEquiv G hG ha (r - 1))

theorem markedDifferencePhase_dilation (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (z : MarkedPair G) :
    markedDifferencePhase G (markedPairDilationEquiv G hG ha z) =
      a * markedDifferencePhase G z := by
  change
    2 * (pointDilationEquiv G hG ha z.2).1 -
        (pointDilationEquiv G hG ha z.1).1 =
      a * (2 * z.2.1 - z.1.1)
  rw [pointDilationEquiv_apply_val, pointDilationEquiv_apply_val]
  ring

theorem subsetDifferencePhase_dilation (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (r : Nat) (z : AdjacentSubsetPair G r) :
    subsetDifferencePhase G r (adjacentSubsetPairDilationEquiv G hG ha r z) =
      a * subsetDifferencePhase G r z := by
  change
    (∑ x ∈ (subsetDilationEquiv G hG ha r z.1).1, x.1) -
        (∑ y ∈ (subsetDilationEquiv G hG ha (r - 1) z.2).1, y.1) =
      a * ((∑ x ∈ z.1.1, x.1) - ∑ y ∈ z.2.1, y.1)
  rw [subsetDilationEquiv_sum G hG ha r z.1,
    subsetDilationEquiv_sum G hG ha (r - 1) z.2]
  ring

/-- Number of points in a phase fibre. -/
noncomputable def fiberCount {X : Type*} [Fintype X]
    (phi : X -> F) (t : F) : Nat :=
  (Finset.univ.filter fun x => phi x = t).card

/-- Equivariant phase maps have orbit-invariant fibre cardinalities. -/
theorem fiberCount_smul {X : Type*} [Fintype X]
    (phi : X -> F) (e : X ≃ X) {a : F} (ha0 : a ≠ 0)
    (hphase : forall x, phi (e x) = a * phi x) (t : F) :
    fiberCount phi (a * t) = fiberCount phi t := by
  classical
  let E : {x : X // phi x = t} ≃ {x : X // phi x = a * t} :=
    e.subtypeEquiv fun x => by
      rw [hphase]
      exact (mul_right_inj' ha0).symm
  simpa [fiberCount, Fintype.card_subtype] using (Fintype.card_congr E).symm

/-- The marked-difference row `W_G`. -/
noncomputable def markedDifferenceMultiplicity (G : Finset F) (t : F) : Nat :=
  fiberCount (markedDifferencePhase G) t

/-- The adjacent subset-difference row `R_r`. -/
noncomputable def subsetDifferenceMultiplicity (G : Finset F) (r : Nat) (t : F) : Nat :=
  fiberCount (subsetDifferencePhase G r) t

/-- Exact `G`-orbit invariance of the marked/intersection row. -/
theorem markedDifferenceMultiplicity_smul (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (t : F) :
    markedDifferenceMultiplicity G (a * t) = markedDifferenceMultiplicity G t := by
  unfold markedDifferenceMultiplicity
  exact fiberCount_smul _ (markedPairDilationEquiv G hG ha)
    (mem_ne_zero G hG ha) (markedDifferencePhase_dilation G hG ha) t

/-- Exact `G`-orbit invariance of the adjacent subset-correlation row. -/
theorem subsetDifferenceMultiplicity_smul (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (r : Nat) (t : F) :
    subsetDifferenceMultiplicity G r (a * t) = subsetDifferenceMultiplicity G r t := by
  unfold subsetDifferenceMultiplicity
  exact fiberCount_smul _ (adjacentSubsetPairDilationEquiv G hG ha r)
    (mem_ne_zero G hG ha) (subsetDifferencePhase_dilation G hG ha r) t

end ExactSymmetry

section LiteralRows

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Literal shifted-intersection row `#{y in G : 2*y-t in G}`. -/
def doubledTranslateIntersection (G : Finset F) (t : F) : Nat :=
  (G.filter fun y => 2 * y - t ∈ G).card

/-- The marked phase fibre is exactly the literal shifted-intersection row. -/
theorem markedDifferenceMultiplicity_eq_doubledTranslateIntersection
    (G : Finset F) (t : F) :
    markedDifferenceMultiplicity G t = doubledTranslateIntersection G t := by
  classical
  unfold markedDifferenceMultiplicity fiberCount doubledTranslateIntersection
  refine Finset.card_bij (fun z _hz => z.2.1) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine Finset.mem_filter.mpr ⟨z.2.2, ?_⟩
    have hx : 2 * z.2.1 - t = z.1.1 := by
      unfold markedDifferencePhase at hz
      linear_combination hz
    exact hx.symm ▸ z.1.2
  · intro z hz z' hz' heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    unfold markedDifferencePhase at hz hz'
    have hx : (z.1.1 : F) = 2 * z.2.1 - t := by linear_combination -hz
    have hx' : (z'.1.1 : F) = 2 * z'.2.1 - t := by linear_combination -hz'
    apply Prod.ext
    · apply Subtype.ext
      exact hx.trans ((congrArg (fun y : F => 2 * y - t) heq).trans hx'.symm)
    · exact Subtype.ext heq
  · intro y hy
    simp only [Finset.mem_filter] at hy
    let x : {x : F // x ∈ G} := ⟨2 * y - t, hy.2⟩
    let y' : {y : F // y ∈ G} := ⟨y, hy.1⟩
    refine ⟨(x, y'), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold markedDifferencePhase
    dsimp [x, y']
    ring

/-- **Exact zero-orbit dichotomy.**  For a multiplicative subgroup, the marked row at zero is
all of `G` when `2` belongs to `G`, and empty otherwise. -/
theorem doubledTranslateIntersection_zero (G : Finset F) (hG : IsMulSubgroup G) :
    doubledTranslateIntersection G 0 = if (2 : F) ∈ G then G.card else 0 := by
  classical
  by_cases htwo : (2 : F) ∈ G
  · rw [if_pos htwo]
    unfold doubledTranslateIntersection
    have hfilter : G.filter (fun y => 2 * y - 0 ∈ G) = G := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      simpa using hG.mul_mem (2 : F) htwo y hy
    rw [hfilter]
  · rw [if_neg htwo]
    unfold doubledTranslateIntersection
    have hfilter : G.filter (fun y => 2 * y - 0 ∈ G) = ∅ := by
      ext y
      constructor
      · intro hyFilter
        simp only [Finset.mem_filter] at hyFilter
        exfalso
        obtain ⟨yi, hyi, hyyi⟩ := hG.exists_inv y hyFilter.1
        apply htwo
        have hmem : yi * (2 * y) ∈ G :=
          hG.mul_mem yi hyi (2 * y) (by simpa using hyFilter.2)
        have heq : yi * (2 * y) = 2 := by
          calc
            yi * (2 * y) = 2 * (y * yi) := by ring
            _ = 2 := by rw [hyyi, mul_one]
        exact heq ▸ hmem
      · intro hyEmpty
        simpa using hyEmpty
    rw [hfilter, Finset.card_empty]

theorem markedDifferenceMultiplicity_zero (G : Finset F) (hG : IsMulSubgroup G) :
    markedDifferenceMultiplicity G 0 = if (2 : F) ∈ G then G.card else 0 := by
  rw [markedDifferenceMultiplicity_eq_doubledTranslateIntersection,
    doubledTranslateIntersection_zero G hG]

end LiteralRows

section ActualC12

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Reassociate the two Newton joins into marked variables and adjacent subset variables. -/
def reassociateNewtonPairs (G : Finset F) (r : Nat) :
    (NewtonJoin G r × NewtonJoin G (r - 1)) ≃
      (MarkedPair G × AdjacentSubsetPair G r) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- The Newton collision equation is equality of the two separated difference phases. -/
theorem newton_collision_iff_difference_collision (G : Finset F) (r : Nat)
    (p : NewtonJoin G r × NewtonJoin G (r - 1)) :
    newtonJoinPhase G 1 r p.1 = newtonJoinPhase G 2 (r - 1) p.2 ↔
      markedDifferencePhase G (reassociateNewtonPairs G r p).1 =
        subsetDifferencePhase G r (reassociateNewtonPairs G r p).2 := by
  simp only [reassociateNewtonPairs, newtonJoinPhase, markedDifferencePhase,
    subsetDifferencePhase, Nat.cast_one, one_mul, Nat.cast_ofNat]
  constructor <;> intro h <;> linear_combination -h

/-- Actual `C12` is the cross collision of the two separated physical rows. -/
theorem newtonJoinCollisionCount_one_two_eq_differenceCrossCollision
    (G : Finset F) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      phaseCrossCollisionCount (markedDifferencePhase G) (subsetDifferencePhase G r) := by
  classical
  unfold newtonJoinCollisionCount phaseCrossCollisionCount
  calc
    (∑ x : NewtonJoin G r, ∑ y : NewtonJoin G (r - 1),
        if newtonJoinPhase G 1 r x = newtonJoinPhase G 2 (r - 1) y then 1 else 0) =
        ∑ p : NewtonJoin G r × NewtonJoin G (r - 1),
          if newtonJoinPhase G 1 r p.1 = newtonJoinPhase G 2 (r - 1) p.2 then 1 else 0 := by
      exact (Fintype.sum_prod_type
        (fun p : NewtonJoin G r × NewtonJoin G (r - 1) =>
          if newtonJoinPhase G 1 r p.1 = newtonJoinPhase G 2 (r - 1) p.2
          then 1 else 0)).symm
    _ = ∑ p : MarkedPair G × AdjacentSubsetPair G r,
          if markedDifferencePhase G p.1 = subsetDifferencePhase G r p.2 then 1 else 0 := by
      apply Fintype.sum_equiv (reassociateNewtonPairs G r)
      intro p
      simp only [newton_collision_iff_difference_collision]
    _ = ∑ x : MarkedPair G, ∑ y : AdjacentSubsetPair G r,
          if markedDifferencePhase G x = subsetDifferencePhase G r y then 1 else 0 := by
      rw [Fintype.sum_prod_type]

/-- The actual favourable cross-collision count is the inner product `sum_t W(t)R(t)`. -/
theorem newtonJoinCollisionCount_one_two_eq_orbitCorrelation
    (G : Finset F) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      ∑ t : F, markedDifferenceMultiplicity G t * subsetDifferenceMultiplicity G r t := by
  rw [newtonJoinCollisionCount_one_two_eq_differenceCrossCollision,
    BGKLateNewtonTwoColourPhysicalBridge.phaseCrossCollisionCount_eq_fiberInner]
  rfl

/-- One summand of the `W/R` alignment. -/
noncomputable def c12OrbitSummand (G : Finset F) (r : Nat) (t : F) : Nat :=
  markedDifferenceMultiplicity G t * subsetDifferenceMultiplicity G r t

theorem c12OrbitSummand_smul (G : Finset F) (hG : IsMulSubgroup G)
    {a : F} (ha : a ∈ G) (r : Nat) (t : F) :
    c12OrbitSummand G r (a * t) = c12OrbitSummand G r t := by
  unfold c12OrbitSummand
  rw [markedDifferenceMultiplicity_smul G hG ha,
    subsetDifferenceMultiplicity_smul G hG ha]

end ActualC12

section OrbitCompression

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A supplied exact coordinate system for the nonzero multiplicative `G`-orbits.  The finite set
`T` contains one representative for each orbit, and `coordinates` records unique factorization
`t=a*c` with `a in G`, `c in T`. -/
structure DilationTransversal (G : Finset F) (T : Finset F) where
  coordinates : ({a : F // a ∈ G} × {c : F // c ∈ T}) ≃ {t : F // t ≠ 0}
  coordinates_apply : forall z, (coordinates z).1 = z.1.1 * z.2.1

/-- A dilation-invariant function sums over the nonzero field as `|G|` times its sum over an
exact transversal. -/
theorem sum_nonzero_orbitInvariant_eq_card_mul_representatives
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T)
    (f : F -> Nat) (hf : ∀ a ∈ G, ∀ t, f (a * t) = f t) :
    (∑ t : {t : F // t ≠ 0}, f t.1) = G.card * ∑ c ∈ T, f c := by
  classical
  have hcoord :
      (∑ z : {a : F // a ∈ G} × {c : F // c ∈ T}, f (tr.coordinates z).1) =
        ∑ t : {t : F // t ≠ 0}, f t.1 := by
    exact Fintype.sum_equiv tr.coordinates _ _ (fun _ => rfl)
  calc
    (∑ t : {t : F // t ≠ 0}, f t.1) =
        ∑ z : {a : F // a ∈ G} × {c : F // c ∈ T}, f (tr.coordinates z).1 :=
      hcoord.symm
    _ = ∑ z : {a : F // a ∈ G} × {c : F // c ∈ T}, f z.2.1 := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [tr.coordinates_apply, hf z.1.1 z.1.2]
    _ = ∑ a : {a : F // a ∈ G}, ∑ c : {c : F // c ∈ T}, f c.1 := by
      rw [Fintype.sum_prod_type]
    _ = G.card * ∑ c : {c : F // c ∈ T}, f c.1 := by simp
    _ = G.card * ∑ c ∈ T, f c := by
      rw [Finset.sum_subtype T (fun _ => Iff.rfl)]

/-- The whole-field sum is its exceptional zero contribution plus `|G|` times one term per
nonzero orbit. -/
theorem sum_orbitInvariant_eq_zero_add_card_mul_representatives
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T)
    (f : F -> Nat) (hf : ∀ a ∈ G, ∀ t, f (a * t) = f t) :
    (∑ t : F, f t) = f 0 + G.card * ∑ c ∈ T, f c := by
  classical
  have hnonzero :=
    sum_nonzero_orbitInvariant_eq_card_mul_representatives G T hG tr f hf
  calc
    (∑ t : F, f t) = (∑ t ∈ Finset.univ.erase (0 : F), f t) + f 0 := by
      exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : F))).symm
    _ = (∑ t : {t : F // t ≠ 0}, f t.1) + f 0 := by
      exact congrArg (fun n : Nat => n + f 0)
        (Finset.sum_subtype (Finset.univ.erase (0 : F))
          (fun t => by simp [Finset.mem_erase]) f)
    _ = f 0 + G.card * ∑ c ∈ T, f c := by rw [hnonzero]; omega

/-- **Actual `C12` orbit compression.**  The full correlation is the zero phase plus exactly
`|G|` times one `W(c)R(c)` product per nonzero multiplicative orbit. -/
theorem newtonJoinCollisionCount_one_two_eq_zero_add_card_mul_representatives
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      c12OrbitSummand G r 0 + G.card * ∑ c ∈ T, c12OrbitSummand G r c := by
  rw [newtonJoinCollisionCount_one_two_eq_orbitCorrelation]
  exact sum_orbitInvariant_eq_zero_add_card_mul_representatives G T hG tr
    (c12OrbitSummand G r) (fun a ha t => c12OrbitSummand_smul G hG ha r t)

/-- **Factored `C12` formula including the zero orbit.**  Since `W(0)` is either `0` or `|G|`,
the *entire* favourable collision count is divisible by the subgroup order. -/
theorem newtonJoinCollisionCount_one_two_eq_card_mul_orbitBracket
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      G.card * ((if (2 : F) ∈ G then subsetDifferenceMultiplicity G r 0 else 0) +
        ∑ c ∈ T, c12OrbitSummand G r c) := by
  rw [newtonJoinCollisionCount_one_two_eq_zero_add_card_mul_representatives G T hG tr]
  unfold c12OrbitSummand
  rw [markedDifferenceMultiplicity_zero G hG]
  by_cases htwo : (2 : F) ∈ G <;> simp [htwo]
  ring

/-- Raw arithmetic corollary: actual `C12` is a multiple of `|G|`. -/
theorem newtonJoinCollisionCount_one_two_divisible_by_card
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T) (r : Nat) :
    exists K : Nat, newtonJoinCollisionCount G 1 r 2 (r - 1) = G.card * K := by
  refine ⟨(if (2 : F) ∈ G then subsetDifferenceMultiplicity G r 0 else 0) +
    ∑ c ∈ T, c12OrbitSummand G r c, ?_⟩
  exact newtonJoinCollisionCount_one_two_eq_card_mul_orbitBracket G T hG tr r

/-- The local copy of the denominator-cleared centered `C12` alignment. -/
noncomputable def c12CenteredAlignment (G : Finset F) (r : Nat) : Int :=
  (Fintype.card F : Int) * (newtonJoinCollisionCount G 1 r 2 (r - 1) : Int) -
    (G.card : Int) ^ 2 *
      ((G.card.choose r : Int) * G.card.choose (r - 1))

/-- The orbit lane's local numerator is exactly the centered-alignment declaration in the
translate/intersection reduction.  The two definitions use respectively actual `C12` and its
`W/R` factorization; the existing centered decomposition identifies them without loss. -/
theorem c12CenteredAlignment_eq_translateIntersectionAlignment
    (G : Finset F) (r : Nat) :
    c12CenteredAlignment G r =
      ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction.c12CenteredAlignment
        G r := by
  have h :=
    card_mul_newtonJoinCollisionCount_one_two_eq_massProduct_add_centeredAlignment G r
  unfold c12CenteredAlignment
  linear_combination h

/-- The exact orbit-representative bracket governing the centered alignment. -/
noncomputable def c12CenteredOrbitBracket (G T : Finset F) (r : Nat) : Int :=
  (Fintype.card F : Int) *
      (((if (2 : F) ∈ G then subsetDifferenceMultiplicity G r 0 else 0) +
        ∑ c ∈ T, c12OrbitSummand G r c : Nat) : Int) -
    (G.card : Int) *
      ((G.card.choose r : Int) * G.card.choose (r - 1))

/-- **Centered orbit compression.**  The full alignment numerator is exactly `|G|` times a
quotient-sized signed bracket.  This is an integrality/compression statement, not a sign bound. -/
theorem c12CenteredAlignment_eq_card_mul_orbitBracket
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T) (r : Nat) :
    c12CenteredAlignment G r = (G.card : Int) * c12CenteredOrbitBracket G T r := by
  rw [c12CenteredAlignment, c12CenteredOrbitBracket,
    newtonJoinCollisionCount_one_two_eq_card_mul_orbitBracket G T hG tr]
  push_cast
  ring

/-- Centered arithmetic corollary: `A_r` is divisible by `|G|`. -/
theorem c12CenteredAlignment_divisible_by_card
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T) (r : Nat) :
    exists K : Int, c12CenteredAlignment G r = (G.card : Int) * K := by
  exact ⟨c12CenteredOrbitBracket G T r,
    c12CenteredAlignment_eq_card_mul_orbitBracket G T hG tr r⟩

/-- A scaled lower gate on the full centered alignment is exactly the corresponding gate on the
orbit-representative bracket.  No positivity of that bracket is assumed or concluded. -/
theorem scaled_centeredAlignment_lower_iff_orbitBracket_lower
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T)
    (r : Nat) (scale threshold : Int) :
    scale * c12CenteredAlignment G r >= threshold ↔
      scale * (G.card : Int) * c12CenteredOrbitBracket G T r >= threshold := by
  rw [c12CenteredAlignment_eq_card_mul_orbitBracket G T hG tr]
  ring_nf

/-- If `2` is outside the subgroup then the zero phase vanishes entirely; only nonzero orbit
representatives remain. -/
theorem newtonJoinCollisionCount_one_two_eq_card_mul_nonzero_representatives
    (G T : Finset F) (hG : IsMulSubgroup G) (tr : DilationTransversal G T)
    (htwo : (2 : F) ∉ G) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      G.card * ∑ c ∈ T, c12OrbitSummand G r c := by
  rw [newtonJoinCollisionCount_one_two_eq_card_mul_orbitBracket G T hG tr]
  simp [htwo]

end OrbitCompression

/-! ## Axiom audit -/

#print axioms markedDifferenceMultiplicity_smul
#print axioms subsetDifferenceMultiplicity_smul
#print axioms doubledTranslateIntersection_zero
#print axioms newtonJoinCollisionCount_one_two_eq_orbitCorrelation
#print axioms newtonJoinCollisionCount_one_two_eq_card_mul_orbitBracket
#print axioms c12CenteredAlignment_eq_translateIntersectionAlignment
#print axioms c12CenteredAlignment_eq_card_mul_orbitBracket
#print axioms scaled_centeredAlignment_lower_iff_orbitBracket_lower


end ArkLib.ProximityGap.Frontier.BGKC12DilationOrbitCompression
