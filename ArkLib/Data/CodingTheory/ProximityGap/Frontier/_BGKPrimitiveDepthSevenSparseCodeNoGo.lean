/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R394L1KernelCertificate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R390RelationResultantCertificate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R379SparseOrbitSupportBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Primitive depth seven as a restricted-alphabet single-check code

For an order-`2m` production root `g`, fold the two halves of the exponent cycle using
`g^m = -1`.  A pair of seven-tuples then has the integer difference vector

`d = tupleVec(a) - tupleVec(b) in Z^m`.

The pair is a finite-field collision with nonzero characteristic-zero label exactly when

`d ≠ 0`, `sum_j d_j g^j = 0`.

Moreover `||d||_1 <= 14`, hence `|supp(d)| <= 14`; its relation polynomial has degree `< m`,
the same support, and evaluates to zero at `g`.  This is the exact sparse-kernel/codeword
form of the globally-disjoint depth-seven residual.  Distinctness and disjointness of the
original petals only restrict the source of such vectors; the kernel statement itself is exact.

There is also an important no-go.  If the integer alphabet is forgotten and coefficients are
allowed to range over the full field, `v |-> sum_j v_j g^j` is just one parity check.  For every
nonzero `g` its kernel has minimum Hamming weight exactly two.  More strongly, the kernels for
any two nonzero roots are related by a support-preserving diagonal rescaling.  Thus BCH distance,
Singleton/Hamming parameters, ordinary uncertainty, and any other invariant of the ambient
linear code cannot distinguish either production prime.  The arithmetic content is precisely
the weight distribution in the tiny coordinate-dependent alphabet coming from integer vectors
with `l1 <= 14`.

The last section instantiates the folding identity at both certified production primes.  It does
not claim the required `6.115%` saving on the primitive Wick coefficient: it isolates the exact
restricted-list-recovery statement that would have to provide it.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.BGKPrimitiveDepthSevenSparseCodeNoGo

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound
open ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate
open ArkLib.ProximityGap.Frontier.R394L1KernelCertificate

/-! ## The ambient one-check code -/

section AmbientCode

variable {F : Type*} [Field F] [DecidableEq F]

/-- Evaluation of a field-valued coefficient word at one root. -/
def fieldEval (g : F) (m : Nat) (v : Fin m -> F) : F :=
  ∑ j : Fin m, v j * g ^ (j : Nat)

/-- Hamming support of a coefficient word. -/
def fieldSupport {m : Nat} (v : Fin m -> F) : Finset (Fin m) :=
  Finset.univ.filter fun j => v j ≠ 0

/-- Coordinatewise rescaling transporting evaluation at `g` to evaluation at `h`. -/
def diagonalTransport (g h : F) {m : Nat} (v : Fin m -> F) : Fin m -> F :=
  fun j => (g / h) ^ (j : Nat) * v j

/-- Diagonal transport intertwines the two evaluation checks. -/
theorem fieldEval_diagonalTransport (g h : F) (hh : h ≠ 0)
    {m : Nat} (v : Fin m -> F) :
    fieldEval h m (diagonalTransport g h v) = fieldEval g m v := by
  unfold fieldEval diagonalTransport
  apply Finset.sum_congr rfl
  intro j _
  calc
    (g / h) ^ (j : Nat) * v j * h ^ (j : Nat) =
        g ^ (j : Nat) * v j * (h⁻¹ ^ (j : Nat) * h ^ (j : Nat)) := by
          rw [div_pow, div_eq_mul_inv]
          ring
    _ = g ^ (j : Nat) * v j := by
      rw [← mul_pow, inv_mul_cancel₀ hh, one_pow, mul_one]
    _ = v j * g ^ (j : Nat) := by ring

/-- For nonzero roots, diagonal transport preserves Hamming support exactly. -/
theorem fieldSupport_diagonalTransport (g h : F) (hg : g ≠ 0) (hh : h ≠ 0)
    {m : Nat} (v : Fin m -> F) :
    fieldSupport (diagonalTransport g h v) = fieldSupport v := by
  ext j
  simp [fieldSupport, diagonalTransport, hg, hh]

/-- Consequently all nonzero evaluation roots define support-isometric kernels. -/
theorem diagonalTransport_mem_kernel_iff (g h : F) (_hg : g ≠ 0) (hh : h ≠ 0)
    {m : Nat} (v : Fin m -> F) :
    fieldEval h m (diagonalTransport g h v) = 0 <-> fieldEval g m v = 0 := by
  rw [fieldEval_diagonalTransport g h hh]

/-- A canonical weight-two word in the kernel of a one-point evaluation check. -/
def weightTwoKernelWord (g : F) {m : Nat} (_hm : 2 <= m) : Fin m -> F :=
  fun j => if (j : Nat) = 0 then g else if (j : Nat) = 1 then -1 else 0

theorem weightTwoKernelWord_eval (g : F) {m : Nat} (hm : 2 <= m) :
    fieldEval g m (weightTwoKernelWord g hm) = 0 := by
  unfold fieldEval weightTwoKernelWord
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let f : Fin m -> F := fun x =>
    (if (x : Nat) = 0 then g else if (x : Nat) = 1 then -1 else 0) *
      g ^ (x : Nat)
  have hsum : ∑ x ∈ ({i0, i1} : Finset (Fin m)), f x = ∑ x, f x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hx0 : (x : Nat) ≠ 0 := by
      intro h
      apply hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Fin.ext h)
    have hx1 : (x : Nat) ≠ 1 := by
      intro h
      apply hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Fin.ext h)
    simp [f, hx0, hx1]
  change ∑ x, f x = 0
  rw [← hsum]
  simp [f, i0, i1]

theorem weightTwoKernelWord_support (g : F) (hg : g ≠ 0)
    {m : Nat} (hm : 2 <= m) :
    fieldSupport (weightTwoKernelWord g hm) =
      {⟨0, by omega⟩, ⟨1, by omega⟩} := by
  ext j
  simp only [fieldSupport, weightTwoKernelWord, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  by_cases hj0 : (j : Nat) = 0
  · have hj : j = (⟨0, by omega⟩ : Fin m) := Fin.ext hj0
    simp [hj, hg]
  by_cases hj1 : (j : Nat) = 1
  · have hj : j = (⟨1, by omega⟩ : Fin m) := Fin.ext hj1
    simp [hj]
  · have hjne0 : j ≠ (⟨0, by omega⟩ : Fin m) := fun h => hj0 (congrArg Fin.val h)
    have hjne1 : j ≠ (⟨1, by omega⟩ : Fin m) := fun h => hj1 (congrArg Fin.val h)
    simp [hj0, hj1, hjne0, hjne1]

theorem weightTwoKernelWord_support_card (g : F) (hg : g ≠ 0)
    {m : Nat} (hm : 2 <= m) :
    (fieldSupport (weightTwoKernelWord g hm)).card = 2 := by
  rw [weightTwoKernelWord_support g hg hm]
  simp

/-- A nonzero word supported on at most one coordinate cannot satisfy the evaluation check. -/
theorem two_le_support_card_of_nonzero_kernel (g : F) (hg : g ≠ 0)
    {m : Nat} {v : Fin m -> F} (hv : v ≠ 0) (hker : fieldEval g m v = 0) :
    2 <= (fieldSupport v).card := by
  by_contra hlt
  have hcard : (fieldSupport v).card <= 1 := by omega
  rw [Finset.card_le_one] at hcard
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  have hjS : j ∈ fieldSupport v := by simp [fieldSupport, hj]
  have hsingle : fieldSupport v = {j} := by
    ext k
    constructor
    · intro hk
      exact Finset.mem_singleton.mpr (hcard k hk j hjS)
    · intro hk
      have hkj : k = j := Finset.mem_singleton.mp hk
      simpa [hkj] using hjS
  have hsum : fieldEval g m v = v j * g ^ (j : Nat) := by
    unfold fieldEval
    have heq : ∑ k ∈ fieldSupport v, v k * g ^ (k : Nat) =
        ∑ k, v k * g ^ (k : Nat) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      have hk0 : v k = 0 := by
        by_contra hkne
        exact hk (by simp [fieldSupport, hkne])
      simp [hk0]
    rw [← heq, hsingle]
    simp
  rw [hsum, mul_eq_zero] at hker
  exact hker.elim hj (pow_ne_zero _ hg)

/-- The ambient evaluation kernel has minimum Hamming weight exactly two. -/
theorem ambient_kernel_distance_exactly_two (g : F) (hg : g ≠ 0)
    {m : Nat} (hm : 2 <= m) :
    (∀ v : Fin m -> F, v ≠ 0 -> fieldEval g m v = 0 ->
      2 <= (fieldSupport v).card) ∧
    ∃ v : Fin m -> F, v ≠ 0 ∧ fieldEval g m v = 0 ∧
      (fieldSupport v).card = 2 := by
  constructor
  · intro v hv hker
    exact two_le_support_card_of_nonzero_kernel g hg hv hker
  · refine ⟨weightTwoKernelWord g hm, ?_, weightTwoKernelWord_eval g hm,
      weightTwoKernelWord_support_card g hg hm⟩
    intro hzero
    have := congrFun hzero (⟨0, by omega⟩ : Fin m)
    simp [weightTwoKernelWord, hg] at this

end AmbientCode

/-! ## The exact restricted integer kernel at depth seven -/

section IntegerKernel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Difference of the two folded seven-tuple shadows. -/
def depthSevenRelation (m : Nat)
    (a b : Fin 7 -> Fin (2 * m)) : Fin m -> Int :=
  fun j => tupleVec (2 * m) m 7 a j - tupleVec (2 * m) m 7 b j

/-- The exact primitive residual predicate before imposing setwise distinctness. -/
def NontrivialDepthSevenCollision (g : F) (m : Nat)
    (a b : Fin 7 -> Fin (2 * m)) : Prop :=
  gsumR g (2 * m) 7 a = gsumR g (2 * m) 7 b ∧
    depthSevenRelation m a b ≠ 0

/-- The source-side condition for globally disjoint seven-petals: each tuple has no repeated
exponent, and the two exponent sets are disjoint. -/
def GloballyDisjointSevenPetals {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) : Prop :=
  Function.Injective a ∧ Function.Injective b ∧
    Disjoint (Finset.univ.image a) (Finset.univ.image b)

/-- The literal primitive depth-seven witness: globally disjoint petals, a field collision, and a
nonzero characteristic-zero folded label. -/
def PrimitiveDepthSevenCollision (g : F) (m : Nat)
    (a b : Fin 7 -> Fin (2 * m)) : Prop :=
  GloballyDisjointSevenPetals a b ∧ NontrivialDepthSevenCollision g m a b

/-- Evaluation of the difference vector is the difference of the two tuple sums. -/
theorem evalVec_depthSevenRelation (g : F) (m : Nat) (hm : 0 < m)
    (hg : g ^ m = -1) (a b : Fin 7 -> Fin (2 * m)) :
    evalVec g m (depthSevenRelation m a b) =
      gsumR g (2 * m) 7 a - gsumR g (2 * m) 7 b := by
  calc
    evalVec g m (depthSevenRelation m a b) =
        evalVec g m (tupleVec (2 * m) m 7 a) -
          evalVec g m (tupleVec (2 * m) m 7 b) := by
      unfold evalVec depthSevenRelation
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simpa [sub_eq_add_neg] using sub_zsmul (g ^ (j : Nat))
        (tupleVec (2 * m) m 7 a j) (tupleVec (2 * m) m 7 b j)
    _ = gsumR g (2 * m) 7 a - gsumR g (2 * m) 7 b := by
      rw [← gsumR_eq_evalVec_tupleVec g (2 * m) m 7 hm rfl hg a,
        ← gsumR_eq_evalVec_tupleVec g (2 * m) m 7 hm rfl hg b]

/-- **Exact sparse-kernel equivalence.** -/
theorem nontrivialDepthSevenCollision_iff (g : F) (m : Nat) (hm : 0 < m)
    (hg : g ^ m = -1) (a b : Fin 7 -> Fin (2 * m)) :
    NontrivialDepthSevenCollision g m a b <->
      depthSevenRelation m a b ≠ 0 ∧
        evalVec g m (depthSevenRelation m a b) = 0 := by
  rw [NontrivialDepthSevenCollision, evalVec_depthSevenRelation g m hm hg]
  constructor
  · rintro ⟨hsum, hne⟩
    exact ⟨hne, sub_eq_zero.mpr hsum⟩
  · rintro ⟨hne, hzero⟩
    exact ⟨sub_eq_zero.mp hzero, hne⟩

/-- The exact sparse-kernel equivalence with the primitive source restrictions retained. -/
theorem primitiveDepthSevenCollision_iff (g : F) (m : Nat) (hm : 0 < m)
    (hg : g ^ m = -1) (a b : Fin 7 -> Fin (2 * m)) :
    PrimitiveDepthSevenCollision g m a b <->
      GloballyDisjointSevenPetals a b ∧
        depthSevenRelation m a b ≠ 0 ∧
          evalVec g m (depthSevenRelation m a b) = 0 := by
  rw [PrimitiveDepthSevenCollision, nontrivialDepthSevenCollision_iff g m hm hg]

/-- Every depth-seven difference vector has endpoint `l1` mass at most fourteen. -/
theorem depthSevenRelation_l1_le_fourteen (m : Nat)
    (a b : Fin 7 -> Fin (2 * m)) :
    endpointL1 (depthSevenRelation m a b) <= 14 := by
  unfold endpointL1 depthSevenRelation
  have ha :
      (∑ j : Fin m, (tupleVec (2 * m) m 7 a j).natAbs) <= 7 := by
    obtain ⟨s, hs⟩ := exists_length_eq_two_mul_add_endpointL1_of_tuple m 7 a
    unfold endpointL1 at hs
    omega
  have hb :
      (∑ j : Fin m, (tupleVec (2 * m) m 7 b j).natAbs) <= 7 := by
    obtain ⟨s, hs⟩ := exists_length_eq_two_mul_add_endpointL1_of_tuple m 7 b
    unfold endpointL1 at hs
    omega
  calc
    ∑ j : Fin m, (tupleVec (2 * m) m 7 a j - tupleVec (2 * m) m 7 b j).natAbs
        <= ∑ j : Fin m, ((tupleVec (2 * m) m 7 a j).natAbs +
          (tupleVec (2 * m) m 7 b j).natAbs) := by
            apply Finset.sum_le_sum
            intro j _
            exact Int.natAbs_sub_le _ _
    _ = (∑ j : Fin m, (tupleVec (2 * m) m 7 a j).natAbs) +
          ∑ j : Fin m, (tupleVec (2 * m) m 7 b j).natAbs := by
            rw [Finset.sum_add_distrib]
    _ <= 7 + 7 := by
      exact Nat.add_le_add ha hb
    _ = 14 := by norm_num

/-- Hence every depth-seven relation is supported on at most fourteen folded coordinates. -/
theorem depthSevenRelation_support_card_le_fourteen (m : Nat)
    (a b : Fin 7 -> Fin (2 * m)) :
    (vectorSupport (depthSevenRelation m a b)).card <= 14 :=
  (card_vectorSupport_le_endpointL1 _).trans (depthSevenRelation_l1_le_fourteen m a b)

/-- The relation polynomial has exactly the vector support, transported into natural degrees. -/
theorem relPoly_support_eq_vectorSupport_map (m : Nat) (d : Fin m -> Int) :
    (relPoly m d).support = (vectorSupport d).map Fin.valEmbedding := by
  ext i
  constructor
  · intro hi
    have hcoeff : (relPoly m d).coeff i ≠ 0 := by
      simpa [Polynomial.mem_support_iff] using hi
    have hiM : i < m := by
      by_contra hnot
      have hdeg := relPoly_degree_lt m d
      have hz : (relPoly m d).coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt (by
          exact lt_of_lt_of_le hdeg (by exact_mod_cast Nat.le_of_not_gt hnot))
      exact hcoeff hz
    let j : Fin m := ⟨i, hiM⟩
    have hdj : d j ≠ 0 := by
      intro hz
      apply hcoeff
      rw [show i = (j : Nat) from rfl, relPoly_coeff]
      exact hz
    exact Finset.mem_map.mpr ⟨j, by simp [vectorSupport, hdj], rfl⟩
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hdj : d j ≠ 0 := by simpa [vectorSupport] using hj
    rw [Polynomial.mem_support_iff]
    change (relPoly m d).coeff (j : Nat) ≠ 0
    rw [relPoly_coeff]
    exact hdj

theorem relPoly_support_card_eq_vectorSupport_card (m : Nat) (d : Fin m -> Int) :
    (relPoly m d).support.card = (vectorSupport d).card := by
  rw [relPoly_support_eq_vectorSupport_map]
  exact Finset.card_map _

/-- Polynomial form of the primitive depth-seven socket. -/
theorem nontrivialDepthSevenCollision_gives_sparse_polynomial
    (g : F) (m : Nat) (hm : 0 < m) (hg : g ^ m = -1)
    (a b : Fin 7 -> Fin (2 * m))
    (h : NontrivialDepthSevenCollision g m a b) :
    let d := depthSevenRelation m a b
    relPoly m d ≠ 0 ∧
      (relPoly m d).natDegree < m ∧
      (relPoly m d).support.card <= 14 ∧
      (∀ i, |(relPoly m d).coeff i| <= 14) ∧
      Polynomial.aeval g (relPoly m d) = 0 := by
  dsimp only
  have hk := (nontrivialDepthSevenCollision_iff g m hm hg a b).mp h
  refine ⟨relPoly_ne_zero m _ hk.1, relPoly_natDegree_lt m _ hk.1, ?_, ?_, ?_⟩
  · rw [relPoly_support_card_eq_vectorSupport_card]
    exact depthSevenRelation_support_card_le_fourteen m a b
  · intro i
    by_cases hi : i < m
    · let j : Fin m := ⟨i, hi⟩
      rw [show i = (j : Nat) from rfl, relPoly_coeff]
      have hsingle : (depthSevenRelation m a b j).natAbs <=
          endpointL1 (depthSevenRelation m a b) :=
        Finset.single_le_sum (s := (Finset.univ : Finset (Fin m)))
          (f := fun k => (depthSevenRelation m a b k).natAbs)
          (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
      have hnat := hsingle.trans (depthSevenRelation_l1_le_fourteen m a b)
      have hcast : ((depthSevenRelation m a b j).natAbs : Int) <= (14 : Int) := by
        exact_mod_cast hnat
      simpa only [Int.natCast_natAbs] using hcast
    · have hz : (relPoly m (depthSevenRelation m a b)).coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact lt_of_lt_of_le (relPoly_degree_lt m _) (by exact_mod_cast Nat.le_of_not_gt hi)
      rw [hz]
      norm_num
  · rw [aeval_relPoly]
    exact hk.2

/-- Primitive globally-disjoint witnesses satisfy the same sparse-polynomial kernel socket. -/
theorem primitiveDepthSevenCollision_gives_sparse_polynomial
    (g : F) (m : Nat) (hm : 0 < m) (hg : g ^ m = -1)
    (a b : Fin 7 -> Fin (2 * m))
    (h : PrimitiveDepthSevenCollision g m a b) :
    let d := depthSevenRelation m a b
    relPoly m d ≠ 0 ∧
      (relPoly m d).natDegree < m ∧
      (relPoly m d).support.card <= 14 ∧
      (∀ i, |(relPoly m d).coeff i| <= 14) ∧
      Polynomial.aeval g (relPoly m d) = 0 :=
  nontrivialDepthSevenCollision_gives_sparse_polynomial g m hm hg a b h.2

end IntegerKernel

/-! ## Kelley sparse-root bound: production-scale quantitative no-go

Kelley's theorem for a `t`-nomial over `F_q` bounds its nonzero roots by

`2 * (q - 1)^(1 - 1/(t-1)) * C^(1/(t-1))`,

where `C` is the largest multiplicative coset on which it vanishes identically
([Kelley, 2016](https://arxiv.org/abs/1602.00208)).  Even granting the optimistically smallest
possible value `C=1`, the `t=14` cap has thirteenth power `2^13 * (q-1)^12`.  The following exact
integer comparisons put its scale between `2^146` and `2^148` at the first production prime, and
between `2^147` and `2^149` at the second.  Both are more than 116 bits above the order-`2^30`
subgroup.  Thus this best generic fewnomial-root theorem cannot even prove that a depth-seven
relation has fewer roots than the whole production subgroup, let alone the required collision
saving.
-/

/-- Thirteenth power of the optimistic (`C=1`) Kelley `t=14` root cap. -/
def kelleyFourteenPowerScale (q : Nat) : Nat := 2 ^ 13 * (q - 1) ^ 12

theorem firstProduction_kelley_scale_window :
    (2 ^ 146) ^ 13 <
        kelleyFourteenPowerScale ArkLib.ProximityGap.PrizeShapePrimeP30.P ∧
      kelleyFourteenPowerScale ArkLib.ProximityGap.PrizeShapePrimeP30.P <
        (2 ^ 148) ^ 13 := by
  norm_num [kelleyFourteenPowerScale, ArkLib.ProximityGap.PrizeShapePrimeP30.P]

theorem secondProduction_kelley_scale_window :
    (2 ^ 147) ^ 13 <
        kelleyFourteenPowerScale ArkLib.ProximityGap.PrizeShapePrimeP30Second.P ∧
      kelleyFourteenPowerScale ArkLib.ProximityGap.PrizeShapePrimeP30Second.P <
        (2 ^ 149) ^ 13 := by
  norm_num [kelleyFourteenPowerScale, ArkLib.ProximityGap.PrizeShapePrimeP30Second.P]

/-- The optimistic Kelley cap is already vastly above the complete `2^30` root subgroup at both
production primes. -/
theorem production_kelley_scale_exceeds_subgroup :
    ((2 ^ 30) ^ 13 <
        kelleyFourteenPowerScale ArkLib.ProximityGap.PrizeShapePrimeP30.P) ∧
      ((2 ^ 30) ^ 13 <
        kelleyFourteenPowerScale ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) := by
  constructor
  · exact (by norm_num : (2 ^ 30) ^ 13 < (2 ^ 146) ^ 13) |>.trans
      firstProduction_kelley_scale_window.1
  · exact (by norm_num : (2 ^ 30) ^ 13 < (2 ^ 147) ^ 13) |>.trans
      secondProduction_kelley_scale_window.1

/-! ## Concrete production instantiations and the no-go verdict -/

section Production

/-- An order-`2m` element has the required half-order value `-1`. -/
theorem pow_half_eq_neg_one_of_orderOf_eq_two_mul
    {F : Type*} [Field F] {g : F} {m : Nat} (hm : 0 < m)
    (hord : orderOf g = 2 * m) : g ^ m = -1 := by
  have hprim : IsPrimitiveRoot g (2 * m) :=
    IsPrimitiveRoot.iff_orderOf.mpr hord
  have hsq : g ^ m * g ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by omega]
    exact hprim.pow_eq_one
  rcases mul_self_eq_one_iff.mp hsq with hone | hneg
  · exact absurd hone (hprim.pow_ne_one_of_pos_of_lt hm.ne' (by omega))
  · exact hneg

local instance firstPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance secondPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

theorem firstProductionRoot_half_pow :
    ArkLib.ProximityGap.PrizeShapePrimeP30.g ^ (2 ^ 29) = -1 := by
  apply pow_half_eq_neg_one_of_orderOf_eq_two_mul (by positivity)
  rw [ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g]
  norm_num

theorem secondProductionRoot_half_pow :
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.g ^ (2 ^ 29) = -1 := by
  apply pow_half_eq_neg_one_of_orderOf_eq_two_mul (by positivity)
  rw [ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g]
  norm_num

/-- The first production ambient code has exact distance two. -/
theorem firstProduction_ambient_kernel_distance_two :
    (∀ v : Fin (2 ^ 29) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P,
      v ≠ 0 ->
      fieldEval ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 29) v = 0 ->
      2 <= (fieldSupport v).card) ∧
    ∃ v : Fin (2 ^ 29) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P,
      v ≠ 0 ∧
      fieldEval ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 29) v = 0 ∧
      (fieldSupport v).card = 2 := by
  apply ambient_kernel_distance_exactly_two
  · intro hz
    have h := firstProductionRoot_half_pow
    rw [hz, zero_pow (by positivity : (2 ^ 29 : Nat) ≠ 0)] at h
    norm_num at h
  · norm_num

/-- The second production ambient code has exact distance two as well. -/
theorem secondProduction_ambient_kernel_distance_two :
    (∀ v : Fin (2 ^ 29) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P,
      v ≠ 0 ->
      fieldEval ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2 ^ 29) v = 0 ->
      2 <= (fieldSupport v).card) ∧
    ∃ v : Fin (2 ^ 29) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P,
      v ≠ 0 ∧
      fieldEval ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2 ^ 29) v = 0 ∧
      (fieldSupport v).card = 2 := by
  apply ambient_kernel_distance_exactly_two
  · intro hz
    have h := secondProductionRoot_half_pow
    rw [hz, zero_pow (by positivity : (2 ^ 29 : Nat) ≠ 0)] at h
    norm_num at h
  · norm_num

/-- At either production root, every nontrivial depth-seven collision lands in the exact
degree-`<2^29`, support-`<=14`, height-`<=14` restricted polynomial kernel. -/
theorem production_sparse_kernel_socket :
    (∀ (a b : Fin 7 -> Fin (2 ^ 30)),
      NontrivialDepthSevenCollision ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 29) a b ->
      let d := depthSevenRelation (2 ^ 29) a b
      relPoly (2 ^ 29) d ≠ 0 ∧
        (relPoly (2 ^ 29) d).natDegree < 2 ^ 29 ∧
        (relPoly (2 ^ 29) d).support.card <= 14 ∧
        (∀ i, |(relPoly (2 ^ 29) d).coeff i| <= 14) ∧
        Polynomial.aeval ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (relPoly (2 ^ 29) d) = 0) ∧
    (∀ (a b : Fin 7 -> Fin (2 ^ 30)),
      NontrivialDepthSevenCollision ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2 ^ 29) a b ->
      let d := depthSevenRelation (2 ^ 29) a b
      relPoly (2 ^ 29) d ≠ 0 ∧
        (relPoly (2 ^ 29) d).natDegree < 2 ^ 29 ∧
        (relPoly (2 ^ 29) d).support.card <= 14 ∧
        (∀ i, |(relPoly (2 ^ 29) d).coeff i| <= 14) ∧
        Polynomial.aeval ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (relPoly (2 ^ 29) d) = 0) := by
  constructor
  · intro a b h
    exact nontrivialDepthSevenCollision_gives_sparse_polynomial _ _ (by positivity)
      firstProductionRoot_half_pow a b h
  · intro a b h
    exact nontrivialDepthSevenCollision_gives_sparse_polynomial _ _ (by positivity)
      secondProductionRoot_half_pow a b h

end Production

#print axioms fieldEval_diagonalTransport
#print axioms fieldSupport_diagonalTransport
#print axioms ambient_kernel_distance_exactly_two
#print axioms nontrivialDepthSevenCollision_iff
#print axioms primitiveDepthSevenCollision_iff
#print axioms depthSevenRelation_l1_le_fourteen
#print axioms nontrivialDepthSevenCollision_gives_sparse_polynomial
#print axioms primitiveDepthSevenCollision_gives_sparse_polynomial
#print axioms firstProduction_kelley_scale_window
#print axioms secondProduction_kelley_scale_window
#print axioms production_kelley_scale_exceeds_subgroup
#print axioms firstProductionRoot_half_pow
#print axioms secondProductionRoot_half_pow
#print axioms firstProduction_ambient_kernel_distance_two
#print axioms secondProduction_ambient_kernel_distance_two
#print axioms production_sparse_kernel_socket

end ArkLib.ProximityGap.Frontier.BGKPrimitiveDepthSevenSparseCodeNoGo
