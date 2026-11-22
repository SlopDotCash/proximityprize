/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Bigraded local constraints for arbitrary positive derivative order

At a translated origin, the Taylor substitution preserves both total jet
degree and the complementary derivative weight. These two nonnegative
integers index independent row and column blocks at every derivative order.
-/
namespace ProximityGap.HigherJetBigrading
open ReedSolomon.HiddenDerivative PolynomialDifferential MvPolynomial Finset

/-- Give `X` weight one and `Y_j` weight `d−j`. -/
def sourceWeight (d : ℕ) : JetVariable d → ℕ
  | none => 1
  | some j => d-j.val

/-- In unscaled Taylor coordinates, displacement has weight one, error has
weight `d−1`, and the visible derivative of order `j+1` has weight `d−j−1`. -/
def targetWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some none => d-1
  | some (some j) => d-(j.val+1)

private theorem correction {R : Type*} [CommRing R] (d : ℕ) :
    (localCorrection (R:=R) d).IsWeightedHomogeneous (targetWeight d) d := by
  rw [← mem_weightedHomogeneousSubmodule]
  apply Submodule.sum_mem
  intro j _
  rw [mem_weightedHomogeneousSubmodule]
  have hc := isWeightedHomogeneous_C (targetWeight d) ((-1:R)^j.val)
  have ht := (isWeightedHomogeneous_X R (targetWeight d) (localT d)).pow (j.val+1)
  have hy := isWeightedHomogeneous_X R (targetWeight d) (localY j)
  have hed : j.val+1+(d-(j.val+1))=d := by omega
  simpa [targetWeight,localT,localY,hed] using (hc.mul ht).mul hy

private theorem image {R : Type*} [CommRing R] {d : ℕ} (hd : 0<d) (v : JetVariable d) :
    (unscaledLocalImage d (0:R) 0 v).IsWeightedHomogeneous (targetWeight d) (sourceWeight d v) := by
  have hj := isWeightedHomogeneous_X R (targetWeight d)
  rcases v with _|j
  · simpa [unscaledLocalImage,sourceWeight,targetWeight,localT] using hj (localT d)
  · refine Fin.cases ?_ (fun a => ?_) j
    · have eq : 1+(d-1)=d := by omega
      have te := (hj (localT d)).mul (hj (localE d))
      simp only [localT,localE,localAux,targetWeight,eq] at te
      simpa [unscaledLocalImage,sourceWeight,localT,localE,localAux] using (correction (R:=R) d).add te
    · simpa [unscaledLocalImage,sourceWeight,targetWeight,localY] using hj (localY a)

/-- The complementary derivative grading is preserved by the actual local
constraint operator at the origin over every commutative coefficient ring. -/
theorem origin_homogeneous {R : Type*} [CommRing R] {d m s : ℕ} (hd : 0<d)
    {Q : DifferentialPolynomial R d} (hq : Q.IsWeightedHomogeneous (sourceWeight d) s) :
    (localConstraintAt m 0 0 Q).IsWeightedHomogeneous (targetWeight d) s :=
  (hq.bind₁ (image hd)).weightedTruncation _ m

/-- Every nonzero matrix coefficient of an origin source monomial must match
both integer labels. This also holds after base change to a rational-function
field for the symbolic received line. -/
theorem nonzero_labels {R : Type*} [CommRing R] {d m : ℕ} (hd : 0<d)
    (x a : ℕ) (higher : Fin d→ℕ) (e : LocalVariable d→₀ℕ)
    (hn : (localConstraintAt m (0:R) 0 (sourceMonomial x a higher)).coeff e ≠ 0) :
    e.weight (localJetDegreeWeight d)=a+∑ j,higher j ∧
    e.weight (targetWeight d)=x+d*a+∑ j,higher j*(d-(j.val+1)) := by
  constructor
  · exact not_not.mp (fun h => hn (coeff_localConstraintAt_zero_sourceMonomial_eq_zero x a higher e h))
  · have hh := origin_homogeneous (m:=m) hd (sourceMonomial_isWeightedHomogeneous (R:=R)
      (sourceWeight d) x a higher)
    have w := hh hn
    simpa [sourceWeight,Nat.mul_comm] using w

private theorem pick {K F : Type*} [DecidableEq K] [Field F] (S : Finset K) (f : K→F) (x : K) :
    (∑ z : S, if z.val=x then f z.val else 0) = if x∈S then f x else 0 := by
  by_cases h : x∈S
  · rw [ite_eq_left h,Fintype.sum_eq_single (⟨x,h⟩ : S)]
    · simp
    · intro y hy
      rw [ite_eq_right (fun he => hy (Subtype.ext he))]
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro y _
    have hy : y.val ≠ x := fun he => h (he ▸ y.property)
    simp [hy]

/-- Covering the nonzero entries of a matrix by `s` rows and `t` columns
bounds the rank by `s+t`. Selecting the smaller side in each nonzero
bigraded block then gives the sum of the blockwise minima. -/
theorem rank_le_vertex_cover {I J F : Type*} [Fintype J] [Field F]
    (M : Matrix I J F) (rows : Finset I) (cols : Finset J)
    (cover : ∀ i j, i∉rows → j∉cols → M i j=0) : M.rank ≤ rows.card+cols.card := by
  classical
  let B : Matrix I (rows⊕cols) F := Matrix.of fun i z => Sum.elim
    (fun r : rows => if r.val=i then 1 else 0)
    (fun c : cols => if i∈rows then 0 else M i c.val) z
  let C : Matrix (rows⊕cols) J F := Matrix.of fun z j => Sum.elim
    (fun r : rows => M r.val j)
    (fun c : cols => if c.val=j then 1 else 0) z
  have eq : B*C=M := by
    ext i j
    simp only [Matrix.mul_apply,Fintype.sum_sum_type,B,C,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr]
    by_cases ir : i∈rows
    · simp only [ite_eq_left ir,zero_mul,sum_const_zero,add_zero,ite_mul,one_mul,zero_mul]
      exact (pick rows (fun z => M z j) i).trans (ite_eq_left ir)
    · simp only [ite_eq_right ir,ite_mul,one_mul,zero_mul,mul_ite,mul_one,mul_zero]
      rw [pick rows (fun z => M z j) i,pick cols (fun z => M i z) j,ite_eq_right ir,zero_add]
      by_cases jc : j∈cols
      · exact ite_eq_left jc
      · rw [ite_eq_right jc,cover i j ir jc]
  calc M.rank = (B*C).rank := by rw [eq]
       _ ≤ C.rank := Matrix.rank_mul_le_right B C
       _ ≤ Fintype.card (rows⊕cols) := C.rank_le_card_height
       _ = _ := by simp

/-- If all nonzero entries occur in the indicated family of rectangular
blocks, the sum of their smaller side counts bounds matrix rank. The blocks
may overlap and rows outside their union may form an infinite index set. -/
theorem rank_le_sum_min {I J K F : Type*} [Fintype J] [Field F]
    (M : Matrix I J F) (G : Finset K) (rows : K→Finset I) (cols : K→Finset J)
    (blocks : ∀ i j, M i j≠0 → ∃ g∈G, i∈rows g ∧ j∈cols g) :
    M.rank ≤ ∑ g∈G, min (rows g).card (cols g).card := by
  classical
  let rr g := if (rows g).card≤(cols g).card then rows g else ∅
  let cc g := if (rows g).card≤(cols g).card then ∅ else cols g
  have cover : ∀ i j, i∉G.biUnion rr → j∉G.biUnion cc → M i j=0 := by
    intro i j ni nj
    by_contra h
    obtain ⟨g,hg,hi,hj⟩ := blocks i j h
    by_cases less : (rows g).card≤(cols g).card
    · exact ni (mem_biUnion.mpr ⟨g,hg,by simpa [rr,less] using hi⟩)
    · exact nj (mem_biUnion.mpr ⟨g,hg,by simpa [cc,less] using hj⟩)
  refine (rank_le_vertex_cover M _ _ cover).trans ((Nat.add_le_add card_biUnion_le card_biUnion_le).trans ?_)
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro g _
  by_cases h : (rows g).card≤(cols g).card
  · simp [rr,cc,h]
  · simp [rr,cc,h,min_eq_right (not_le.mp h).le]

end ProximityGap.HigherJetBigrading

#print axioms ProximityGap.HigherJetBigrading.nonzero_labels
#print axioms ProximityGap.HigherJetBigrading.rank_le_vertex_cover
#print axioms ProximityGap.HigherJetBigrading.rank_le_sum_min
