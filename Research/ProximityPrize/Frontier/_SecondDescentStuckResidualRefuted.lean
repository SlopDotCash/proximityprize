/-
Copyright (c) 2026 Mikhail (mashingaan). All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Mikhail (mashingaan)
-/
import Research.ProximityPrize.Frontier._SecondDescentParity
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Basic

/-!
# The second-descent root-count residual is false as stated

`SecondDescentStuckResidual F 2` quantifies over every polynomial `A` of degree less
than four and every `O` of degree less than two. It asserts that any set of roots of
`A^2 - X * O^2` at which `O` is nonzero has cardinality at most three.

More generally, interpolation refutes the residual at every `k ≥ 2` whenever the
field has `k + 2` distinct square nodes. In characteristic zero the nodes
`1^2, ..., (k + 2)^2` discharge this condition for every such `k`.
Over each prime field `ZMod p`, the same positive nodes are distinct whenever
`2 * (k + 2) < p`, giving an explicit finite-characteristic range.

Over a characteristic-zero field, the integer polynomial
`A = X^3 - 35 X^2 + 574 X + 720`, with `O = 1260`, has the four distinct roots
`1, 4, 9, 16` in that equation. A second witness over `ZMod 17` has four roots in
the order-eight subgroup, none paired with its antipode. Its `A` has a two-monomial
head and constant tail, while `O` is linear. Thus adding only subgroup membership,
antipodal isolation and that sparse head shape does not repair the universal claim.

These are refutations of the recorded residual, not production counterexamples.
The decoded-family, head/tail and production-parameter restrictions of a future
replacement are not discharged here. The production Delta Star problem remains open.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ProximityGap.Frontier.SecondDescentStuckResidualRefuted

open SecondDescentParity

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Interpolation refutes the count whenever `k + 2` distinct square nodes are available. -/
theorem not_secondDescentStuckResidual_of_square_nodes
    {F : Type*} [Field F] {k : ℕ} (hk : 2 ≤ k) (s : Finset F) (r : F → F)
    (hcard : s.card = k + 2) (hroots : ∀ x ∈ s, r x ^ 2 = x) :
    ¬ SecondDescentStuckResidual F k := by
  classical
  let A : F[X] := Lagrange.interpolate s id r
  have hinj : Set.InjOn (id : F → F) (s : Set F) := fun _ _ _ _ h => h
  have hA : A.natDegree ≤ s.card - 1 :=
    natDegree_le_iff_degree_le.mpr (Lagrange.degree_interpolate_le r hinj)
  have hdeg : A.natDegree < 2 * k := by
    rw [hcard] at hA
    omega
  have hO : (1 : F[X]).natDegree < k := by
    simp only [natDegree_one]
    omega
  intro h
  have hcount := h A 1 hdeg hO s (fun x hx => by
    have hval : A.eval x = r x := Lagrange.eval_interpolate_at_node r hinj hx
    exact ⟨by simp [IsRoot, hval, hroots x hx], by simp⟩)
  rw [hcard] at hcount
  omega

/-- In characteristic zero the universal residual fails at every `k ≥ 2`. -/
theorem not_secondDescentStuckResidual_charZero_all
    {F : Type*} [Field F] [CharZero F] {k : ℕ} (hk : 2 ≤ k) :
    ¬ SecondDescentStuckResidual F k := by
  classical
  let v : ℕ → F := fun i => ((i + 1 : ℕ) : F) ^ 2
  have hv : Function.Injective v := by
    intro i j h
    change (((i + 1 : ℕ) : F) ^ 2) = (((j + 1 : ℕ) : F) ^ 2) at h
    have hsq : (i + 1) ^ 2 = (j + 1) ^ 2 := by exact_mod_cast h
    have heq : i + 1 = j + 1 := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hsq
    omega
  let s : Finset F := (Finset.range (k + 2)).image v
  have hcard : s.card = k + 2 := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hv, Finset.card_range]
  have hsquare : ∀ x ∈ s, ∃ y : F, y ^ 2 = x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact ⟨((i + 1 : ℕ) : F), rfl⟩
  let r : F → F := fun x => if hx : x ∈ s then Classical.choose (hsquare x hx) else 0
  have hroots : ∀ x ∈ s, r x ^ 2 = x := by
    intro x hx
    simp only [r, dif_pos hx]
    exact Classical.choose_spec (hsquare x hx)
  exact not_secondDescentStuckResidual_of_square_nodes hk s r hcard hroots

/-- The unrestricted residual also fails over every sufficiently large prime field. -/
theorem not_secondDescentStuckResidual_prime_range
    {p k : ℕ} [Fact (Nat.Prime p)] (hk : 2 ≤ k) (hp : 2 * (k + 2) < p) :
    ¬ SecondDescentStuckResidual (ZMod p) k := by
  classical
  let v : ℕ → ZMod p := fun i => ((i + 1 : ℕ) : ZMod p) ^ 2
  have hv : Set.InjOn v (Finset.range (k + 2) : Set ℕ) := by
    intro i hi j hj h
    have hi' : i < k + 2 := Finset.mem_range.mp hi
    have hj' : j < k + 2 := Finset.mem_range.mp hj
    change (((i + 1 : ℕ) : ZMod p) ^ 2) = (((j + 1 : ℕ) : ZMod p) ^ 2) at h
    have hmul :
        (((i + 1 : ℕ) : ZMod p) - ((j + 1 : ℕ) : ZMod p)) *
          (((i + 1 : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p)) = 0 := by
      calc
        _ = (((i + 1 : ℕ) : ZMod p) ^ 2) - (((j + 1 : ℕ) : ZMod p) ^ 2) := by ring
        _ = 0 := sub_eq_zero.mpr h
    rcases mul_eq_zero.mp hmul with hdiff | hsum
    · have hval := congrArg ZMod.val (sub_eq_zero.mp hdiff)
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
      omega
    · have hsumcast : ((i + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
        simpa only [Nat.cast_add] using hsum
      have hdiv := (ZMod.natCast_eq_zero_iff (i + 1 + (j + 1)) p).mp hsumcast
      have hzero := Nat.eq_zero_of_dvd_of_lt hdiv (by omega : i + 1 + (j + 1) < p)
      omega
  let s : Finset (ZMod p) := (Finset.range (k + 2)).image v
  have hcard : s.card = k + 2 := by
    dsimp [s]
    rw [Finset.card_image_of_injOn hv, Finset.card_range]
  have hsquare : ∀ x ∈ s, ∃ y : ZMod p, y ^ 2 = x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact ⟨((i + 1 : ℕ) : ZMod p), rfl⟩
  let r : ZMod p → ZMod p := fun x =>
    if hx : x ∈ s then Classical.choose (hsquare x hx) else 0
  have hroots : ∀ x ∈ s, r x ^ 2 = x := by
    intro x hx
    simp only [r, dif_pos hx]
    exact Classical.choose_spec (hsquare x hx)
  exact not_secondDescentStuckResidual_of_square_nodes hk s r hcard hroots

/-- An integer interpolation witness for the overbroad second-descent residual. -/
def rationalWitness {F : Type*} [Field F] : F[X] :=
  X ^ 3 - C 35 * X ^ 2 + C 574 * X + C 720

/-- The witness meets the exact degree hypothesis at `k = 2`. -/
theorem rationalWitness_degree_le {F : Type*} [Field F] :
    (rationalWitness (F := F)).natDegree ≤ 3 := by
  unfold rationalWitness
  compute_degree

/-- A field-uniform factorization explains all four interpolation roots. -/
theorem rationalWitness_factorization {F : Type*} [Field F] :
    rationalWitness ^ 2 - X * (C 1260 : F[X]) ^ 2 =
      (X - C 1) * (X - C 4) * (X - C 9) * (X - C 16) *
        (X ^ 2 - C 40 * X + C 900) := by
  unfold rationalWitness
  simp only [C_ofNat, map_one]
  ring

/-- The four interpolation nodes are roots of the same squared equation. -/
theorem rationalWitness_roots {F : Type*} [Field F] [DecidableEq F] (x : F)
    (hx : x ∈ ({1, 4, 9, 16} : Finset F)) :
    (rationalWitness ^ 2 - X * (C 1260 : F[X]) ^ 2).IsRoot x := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals norm_num [IsRoot, rationalWitness]

/-- Any field with four distinct interpolation nodes and nonzero `1260` refutes the residual. -/
theorem not_secondDescentStuckResidual_of_four_nodes
    {F : Type*} [Field F] [DecidableEq F] (hscale : (1260 : F) ≠ 0)
    (hnodes : ({1, 4, 9, 16} : Finset F).card = 4) :
    ¬ SecondDescentStuckResidual F 2 := by
  classical
  intro h
  have hdeg : (rationalWitness (F := F)).natDegree < 2 * 2 :=
    lt_of_le_of_lt rationalWitness_degree_le (by norm_num)
  have hcard := h rationalWitness (C 1260) hdeg (by simp)
    {1, 4, 9, 16} (fun x hx =>
      ⟨rationalWitness_roots x hx, by simpa using hscale⟩)
  rw [hnodes] at hcard
  omega

/-- In every characteristic-zero field, the recorded residual fails at `k = 2`. -/
theorem not_secondDescentStuckResidual_charZero
    {F : Type*} [Field F] [CharZero F] :
    ¬ SecondDescentStuckResidual F 2 := by
  classical
  exact not_secondDescentStuckResidual_of_four_nodes (by norm_num) (by norm_num)

/-- A two-monomial head with constant tail, over every field. -/
def sparseHeadWitness {F : Type*} [Field F] : F[X] :=
  C 5 * X ^ 3 - C 257 * X ^ 2 + C 1632

/-- The corresponding linear odd part. -/
def sparseOddWitness {F : Type*} [Field F] : F[X] := C 2200 - C 820 * X

/-- Exact factorization for the sparse-head witness. -/
theorem sparseHeadWitness_factorization {F : Type*} [Field F] :
    sparseHeadWitness ^ 2 - X * (sparseOddWitness (F := F)) ^ 2 =
      (X - C 1) * (X - C 4) * (X - C 9) * (X - C 16) *
        (C 25 * X ^ 2 - C 1820 * X + C 4624) := by
  unfold sparseHeadWitness sparseOddWitness
  simp only [C_ofNat, map_one]
  ring

/-- The sparse-head roots also satisfy the nonzero odd-part requirement. -/
theorem sparseHeadWitness_roots {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (x : F) (hx : x ∈ ({1, 4, 9, 16} : Finset F)) :
    (sparseHeadWitness ^ 2 - X * (sparseOddWitness (F := F)) ^ 2).IsRoot x ∧
      sparseOddWitness.eval x ≠ 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals norm_num [IsRoot, sparseHeadWitness, sparseOddWitness]

/-- A sparse head and constant tail do not repair the characteristic-zero residual. -/
theorem not_secondDescentStuckResidual_charZero_sparseHead
    {F : Type*} [Field F] [CharZero F] :
    ¬ SecondDescentStuckResidual F 2 := by
  classical
  intro h
  have hA : (sparseHeadWitness (F := F)).natDegree < 2 * 2 := by
    unfold sparseHeadWitness
    compute_degree!
  have hO : (sparseOddWitness (F := F)).natDegree < 2 := by
    unfold sparseOddWitness
    compute_degree!
  have hcard := h sparseHeadWitness sparseOddWitness hA hO {1, 4, 9, 16}
    (fun x hx => sparseHeadWitness_roots x hx)
  have hnodes : ({1, 4, 9, 16} : Finset F).card = 4 := by norm_num
  rw [hnodes] at hcard
  omega

/-- A finite-field witness with antipodally isolated subgroup roots. -/
def finiteWitness : (ZMod 17)[X] := C 4 + C 11 * X ^ 2 + C 7 * X ^ 3

/-- A linear odd-part witness, nonzero on the four listed roots. -/
def finiteOddWitness : (ZMod 17)[X] := X + C 4

/-- Four nonzero elements of the order-eight subgroup in `F_17`. -/
def finiteRoots : Finset (ZMod 17) := {1, 2, 4, 8}

/-- The finite witness meets the exact degree hypothesis at `k = 2`. -/
theorem finiteWitness_degree_le : finiteWitness.natDegree ≤ 3 := by
  unfold finiteWitness
  compute_degree

/-- The odd-part witness meets the degree bound at `k = 2`. -/
theorem finiteOddWitness_degree_le : finiteOddWitness.natDegree ≤ 1 := by
  unfold finiteOddWitness
  compute_degree

/-- Every listed point is a root, lies in `mu_8`, and has a non-root antipode. -/
theorem finiteRoots_spec (x : ZMod 17) (hx : x ∈ finiteRoots) :
    (finiteWitness ^ 2 - X * finiteOddWitness ^ 2).IsRoot x ∧
      finiteOddWitness.eval x ≠ 0 ∧ x ^ 8 = 1 ∧
        ¬ (finiteWitness ^ 2 - X * finiteOddWitness ^ 2).IsRoot (-x) := by
  simp only [finiteRoots, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals norm_num [IsRoot, finiteWitness, finiteOddWitness]
  all_goals decide

/-- The finite witness has four distinct listed roots. -/
theorem finiteRoots_card : finiteRoots.card = 4 := by
  norm_num [finiteRoots]
  decide

/-- The recorded residual fails even over the finite field `F_17`. -/
theorem not_secondDescentStuckResidual_zmod17 :
    ¬ SecondDescentStuckResidual (ZMod 17) 2 := by
  intro h
  have hdeg : finiteWitness.natDegree < 2 * 2 :=
    lt_of_le_of_lt finiteWitness_degree_le (by norm_num)
  have hOdeg : finiteOddWitness.natDegree < 2 :=
    lt_of_le_of_lt finiteOddWitness_degree_le (by norm_num)
  have hcard := h finiteWitness finiteOddWitness hdeg hOdeg finiteRoots (fun x hx =>
    ⟨(finiteRoots_spec x hx).1, (finiteRoots_spec x hx).2.1⟩)
  rw [finiteRoots_card] at hcard
  omega

end ProximityGap.Frontier.SecondDescentStuckResidualRefuted

open ProximityGap.Frontier.SecondDescentStuckResidualRefuted

#print axioms rationalWitness_factorization
#print axioms not_secondDescentStuckResidual_of_square_nodes
#print axioms not_secondDescentStuckResidual_charZero_all
#print axioms not_secondDescentStuckResidual_prime_range
#print axioms not_secondDescentStuckResidual_of_four_nodes
#print axioms not_secondDescentStuckResidual_charZero
#print axioms sparseHeadWitness_factorization
#print axioms not_secondDescentStuckResidual_charZero_sparseHead
#print axioms finiteRoots_spec
#print axioms not_secondDescentStuckResidual_zmod17
