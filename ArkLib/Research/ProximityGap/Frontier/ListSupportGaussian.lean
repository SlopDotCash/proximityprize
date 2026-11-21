/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FiniteGaussianNullity
import ArkLib.Research.ProximityGap.Frontier.ListSupportForcedPair

/-! # Executable block Vandermonde nullities for interleaved list decoding

The coordinate list is an input presentation of the domain. It may contain duplicates.
The algorithm needs only field arithmetic, decidable equality and the supplied points.
-/

namespace ProximityGap.ListSupportRank

open Code Finset
open FiniteGaussianNullity

variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I] {L : ℕ}

private def indices (L : ℕ) (points : List I) : List (Fin L × Fin L × I) :=
  (List.finRange L).flatMap fun a =>
    (List.finRange L).flatMap fun b => points.map fun i => (a, b, i)

omit [DecidableEq I] in
private theorem mem_indices (points : List I) (h : ∀ i, i ∈ points) (e : Fin L × Fin L × I) :
    e ∈ indices L points := by
  obtain ⟨a,b,i⟩ := e
  simp [indices, h]

/-- A coefficient row for an active overlap or a prescribed collision. -/
def gaussianRow (α : I ↪ K) (k : ℕ) (S : Fin L → Finset I) (T : Finset (Fin L × Fin L))
    (e : Fin L × Fin L × I) : Fin (L * k) → K :=
  if (e.2.2 ∈ S e.1 ∧ e.2.2 ∈ S e.2.1) ∨ (e.1, e.2.1) ∈ T then
    cache fun v =>
      let j := finProdFinEquiv.symm v
      (if j.1 = e.1 then α e.2.2 ^ (j.2 : ℕ) else 0) -
        (if j.1 = e.2.1 then α e.2.2 ^ (j.2 : ℕ) else 0)
  else fun _ => 0

/-- The Gaussian computation of a kernel dimension on a presented evaluation domain. -/
def gaussianNullity (points : List I) (α : I ↪ K) (k : ℕ) (S : Fin L → Finset I)
    (T : Finset (Fin L × Fin L)) : ℕ :=
  nullity (L * k) ((indices L points).map (gaussianRow α k S T))

private def reshape (k L : ℕ) : (Fin (L * k) → K) ≃ (Fin L → Fin k → K) where
  toFun x a j := x (finProdFinEquiv (a,j))
  invFun y v := y (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2
  left_inv x := funext fun v => congrArg x (finProdFinEquiv.apply_symm_apply v)
  right_inv y := funext fun a => funext fun j => by simp

omit [DecidableEq K] in
private theorem row_dot (α : I ↪ K) (k : ℕ) (S : Fin L → Finset I) (T : Finset (Fin L × Fin L))
    (e : Fin L × Fin L × I) (x : Fin (L * k) → K) :
    dot (gaussianRow α k S T e) x = (vandermonde α k S T (reshape k L x)) e := by
  classical
  obtain ⟨a,b,i⟩ := e
  by_cases active : (i ∈ S a ∧ i ∈ S b) ∨ (a,b) ∈ T
  · simp only [dot, gaussianRow, active, ite_eq_left, vandermonde, LinearMap.pi_apply,
      LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]
    rw [← Equiv.sum_comp (finProdFinEquiv (m := L) (n := k)), Fintype.sum_prod_type]
    have hcache (r : Fin (L * k) → K) : cache r = r := by funext j; simp [cache]
    simp only [hcache, Equiv.symm_apply_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
      zero_mul]
    congr 1 <;> rw [Finset.sum_comm] <;> simp [reshape]
  · simp [dot, gaussianRow, vandermonde, active]

/-- Executing pivot elimination gives exactly the kernel dimension in the rank theorems. -/
theorem gaussianNullity_eq [Finite K] (points : List I) (h : ∀ i, i ∈ points) (α : I ↪ K)
    (k : ℕ) (S : Fin L → Finset I) (T : Finset (Fin L × Fin L)) :
    gaussianNullity points α k S T = Module.finrank K (vandermonde α k S T).ker := by
  classical
  let _ := Fintype.ofFinite K
  let rows := (indices L points).map (gaussianRow α k S T)
  let φ := vandermonde α k S T
  have mem (x : Fin (L * k) → K) :
      (∀ r ∈ rows, dot r x = 0) ↔ reshape k L x ∈ φ.ker := by
    rw [LinearMap.mem_ker, funext_iff]
    constructor
    · intro hall e
      rw [← row_dot]
      exact hall _ (List.mem_map.mpr ⟨e, mem_indices points h e, rfl⟩)
    · intro hall r hr
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
      rw [row_dot]
      exact hall e
  let equiv : Solutions rows ≃ φ.ker := {
    toFun := fun x => ⟨reshape k L x.val, (mem _).mp x.property⟩
    invFun := fun y => ⟨(reshape k L).symm y.val, (mem _).mpr (by simp)⟩
    left_inv x := Subtype.ext ((reshape k L).symm_apply_apply x.val)
    right_inv y := Subtype.ext ((reshape k L).apply_symm_apply y.val) }
  have hcard := Nat.card_congr equiv
  rw [card_solutions, Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card] at hcard
  exact Nat.pow_right_injective Fintype.one_lt_card hcard

/-- The support patterns, enumerated directly from the coordinates in the presentation. -/
def patterns (points : List I) (L t : ℕ) : Finset (Fin L → Finset I) :=
  Fintype.piFinset fun _ => points.toFinset.powersetCard t

omit [Field K] [DecidableEq K] in
private theorem mem_patterns (points : List I) (h : ∀ i, i ∈ points) (t : ℕ)
    (S : Fin L → Finset I) : S ∈ patterns points L t ↔ ∀ a, (S a).card = t := by
  simp only [patterns, Fintype.mem_piFinset, mem_powersetCard]
  exact forall_congr' fun a => ⟨And.right, fun ht => ⟨fun i _ => List.mem_toFinset.mpr (h i), ht⟩⟩

/-- Executable exact rank-sum test at any field size and any width. The size is given as
an integer, so execution has no need to enumerate field elements. -/
def gaussianSafe (points : List I) (α : I ↪ K) (k q m B t : ℕ) : Bool :=
  decide (∀ S ∈ patterns points (B + 1) t,
    (∑ T ∈ (pairs (B + 1)).powerset, (-1 : ℤ) ^ T.card *
      (q : ℤ) ^ (gaussianNullity points α k S T * m)) ≤ 0)

/-- Evaluate the unaugmented system once for this pattern and test the single-pair systems. -/
def hasForcedPair (points : List I) (α : I ↪ K) (k : ℕ) (S : Fin L → Finset I) : Bool :=
  let base := gaussianNullity points α k S ∅
  decide (∃ e ∈ pairs L, base ≤ gaussianNullity points α k S {e})

/-- Executable single-pair test under the pair-count hypothesis. -/
def gaussianPairSafe (points : List I) (α : I ↪ K) (k B t : ℕ) : Bool :=
  decide (∀ S ∈ patterns points (B + 1) t, hasForcedPair points α k S = true)

/-- Correctness of the executable signed test against the canonical worst-center list size. -/
theorem gaussianSafe_iff [Fintype I] [Fintype K] (points : List I) (h : ∀ i, i ∈ points)
    (α : I ↪ K) (k m B t : ℕ) (hn : 0 < Fintype.card I) (hk : k ≤ Fintype.card I) :
    gaussianSafe points α k (Fintype.card K) m B t = true ↔
      Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code α k : Set (I → K)))
        (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) := by
  rw [rs_vandermonde_safe_iff α k m B t hn hk]
  simp only [gaussianSafe, decide_eq_true_eq, mem_patterns points h, gaussianNullity_eq points h]

/-- Correctness of the executable pair test, using polynomially many nullities per pattern. -/
theorem gaussianPairSafe_iff [Fintype I] [Fintype K] (points : List I) (h : ∀ i, i ∈ points)
    (α : I ↪ K) (k m B t : ℕ) (hn : 0 < Fintype.card I) (hk : k ≤ Fintype.card I)
    (hm : 0 < m) (hq : (B + 1).choose 2 ≤ Fintype.card K) :
    gaussianPairSafe points α k B t = true ↔
      Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code α k : Set (I → K)))
        (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) := by
  rw [rs_forced_pair_safe_iff α k m B t hn hk hm hq]
  simp only [gaussianPairSafe, hasForcedPair, decide_eq_true_eq, mem_patterns points h,
    gaussianNullity_eq points h]

end ProximityGap.ListSupportRank

#print axioms ProximityGap.ListSupportRank.gaussianNullity_eq
#print axioms ProximityGap.ListSupportRank.gaussianSafe_iff
#print axioms ProximityGap.ListSupportRank.gaussianPairSafe_iff
