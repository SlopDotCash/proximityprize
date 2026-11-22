/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SaturatedListCliques
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import ArkLib.Data.Polynomial.FiniteDomainQuotient

/-! # Two-coefficient tests for saturated Reed–Solomon differences

The constant-to-leading coefficient ratio of a fully split difference is the signed
product of its roots. On a multiplicative coset all such ratios have the same `n`th
power. This test uses two coefficients per message, without reading its agreements.
-/

namespace ProximityGap.SplitCoefficientSecants
open Finset Polynomial SaturatedListCliques
set_option autoImplicit false
variable {I F : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]

omit [Fintype I] [DecidableEq I] [DecidableEq F] in
/-- A difference attaining its root bound has a nonzero top coefficient, and its two
end coefficients satisfy the coset power equation. -/
theorem full_difference (D : I ↪ F) (S : Finset I) (P : F[X]) {d n : ℕ} {c : F}
    (hD : ∀ j, (-D j) ^ n = c) (hP : P ≠ 0) (hd : P.natDegree ≤ d)
    (hS : d ≤ S.card) (hr : ∀ j ∈ S, P.eval (D j) = 0) :
    P.coeff d ≠ 0 ∧ (P.coeff 0) ^ n = (P.coeff d) ^ n * c ^ d := by
  classical
  have dv := Polynomial.prod_X_sub_C_dvd S D D.injective.injOn P hr
  change Lagrange.nodal S D ∣ P at dv
  obtain ⟨Q, hf⟩ := dv
  have hQ : Q ≠ 0 := by intro h; simp [hf, h] at hP
  have deg := natDegree_mul (Lagrange.nodal_ne_zero (s := S) (v := D)) hQ
  rw [← hf, Lagrange.natDegree_nodal] at deg
  have zero : Q.natDegree = 0 := by omega
  have hs : S.card = d := by omega
  have hc := eq_C_of_natDegree_eq_zero zero
  rw [hc] at hf
  have top : P.coeff d = Q.coeff 0 := by
    have hmono : (Lagrange.nodal S D).Monic := Lagrange.nodal_monic
    rw [hf, coeff_mul_C, ← hs, ← Lagrange.natDegree_nodal (s := S) (v := D),
      hmono.coeff_natDegree, one_mul]
  refine ⟨by rw [top]; intro h; apply hQ; rw [hc, h, map_zero], ?_⟩
  have prod : ((Lagrange.nodal S D).eval 0) ^ n = c ^ d := by
    rw [Lagrange.eval_nodal]
    simp only [zero_sub, ← Finset.prod_pow, hD, prod_const, hs]
  rw [top, coeff_zero_eq_eval_zero P, hf, eval_mul, eval_C, mul_pow, prod, mul_comm]

/-- The permitted ordered partners of one message, from a supplied table of pairs
`(constant coefficient, coefficient in degree d)`. -/
def partners {M : ℕ} (ends : Fin M → F × F) (n : ℕ) (cosetPower : F) (i : Fin M) :
    Finset (Fin M) := univ.filter fun j => (ends i).2 ≠ (ends j).2 ∧
      ((ends i).1 - (ends j).1) ^ n = ((ends i).2 - (ends j).2) ^ n * cosetPower

omit [DecidableEq I] in
/-- Every proposed collection of messages around one center must pass this integer
incidence inequality. A failed test rejects every center for the collection. -/
theorem necessary {M d n t : ℕ} {c : F} (D : I ↪ F) (hD : ∀ j, (-D j) ^ n = c)
    (P : Fin M → F[X]) (inj : Function.Injective P) (hd : ∀ i, (P i).natDegree ≤ d)
    (S : Fin M → Finset I) (hsize : ∀ i, t ≤ (S i).card) (y : I → F)
    (hag : ∀ i j, j ∈ S i → (P i).eval (D j) = y j) (hpos : 0 < d) (a : ℕ) :
    2 * a * (M * t) ≤ M * ((M - 1) * (d - 1)) +
      ∑ i, (partners (fun j => ((P j).coeff 0, (P j).coeff d)) n (c ^ d) i).card +
      a * (a + 1) * Fintype.card I := by
  classical
  have root (i j : Fin M) (x : I) (h : x ∈ S i ∩ S j) : (P i - P j).eval (D x) = 0 := by
    rw [eval_sub, hag i x (mem_inter.mp h).1, hag j x (mem_inter.mp h).2, sub_self]
  have degree (i j : Fin M) : (P i - P j).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le (hd i) (hd j))
  have pair (i j : Fin M) (h : i ≠ j) : (S i ∩ S j).card ≤ d := by
    have dvd := Polynomial.prod_X_sub_C_dvd (S i ∩ S j) D D.injective.injOn (P i - P j) (root i j)
    change Lagrange.nodal (S i ∩ S j) D ∣ _ at dvd
    have bound := (natDegree_le_of_dvd dvd (sub_ne_zero.mpr (inj.ne h))).trans (degree i j)
    simpa only [Lagrange.natDegree_nodal] using bound
  have count (i : Fin M) : (fullGraph S d).degree i ≤
      (partners (fun j => ((P j).coeff 0, (P j).coeff d)) n (c ^ d) i).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply card_le_card
    intro j hj
    obtain ⟨hne, hs⟩ := (SimpleGraph.mem_neighborFinset _ _ _).mp hj
    obtain ⟨hn, he⟩ := full_difference D _ _ hD
      (sub_ne_zero.mpr (inj.ne hne)) (degree i j) hs (root i j)
    exact mem_filter.mpr ⟨mem_univ _, by
      simpa only [coeff_sub, sub_ne_zero] using And.intro hn he⟩
  have edges := forced_edges S hpos hsize pair a
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges] at edges
  exact edges.trans (by gcongr; exact count _)

/-- Rotation realizes every product of `d` distinct sites whenever `d` is coprime
to the order of the evaluation subgroup. Thus the two-coefficient filter alone
cannot forbid any further nonzero slopes in that subgroup. -/
theorem all_products {G : Type*} [CommGroup G] [Fintype G] {d : ℕ}
    (hd : d ≤ Fintype.card G) (cop : (Nat.card G).Coprime d) (v : G) :
    ∃ S : Finset G, S.card = d ∧ ∏ x ∈ S, x = v := by
  classical
  have hcard : d ≤ (univ : Finset G).card := by simpa using hd
  obtain ⟨T, _, hT⟩ := exists_subset_card_eq hcard
  obtain ⟨u, hu⟩ := cop.pow_left_bijective.surjective (v / ∏ x ∈ T, x)
  refine ⟨T.map (Equiv.mulLeft u).toEmbedding, (card_map _).trans hT, ?_⟩
  rw [prod_map]
  change (∏ x ∈ T, u * x) = v
  change u ^ d = v / ∏ x ∈ T, x at hu
  rw [prod_mul_distrib, prod_const, hT, hu, div_mul_cancel]

omit [Fintype I] [DecidableEq I] [DecidableEq F] in
/-- Polynomials in the same affine slice cannot differ by a polynomial with
`d` distinct physical roots when their slice has an excluded slope. -/
theorem fewer_roots {d n : ℕ} {c u b : F} (D : I ↪ F) (hD : ∀ j, (-D j) ^ n = c)
    (hu : u ^ n ≠ c ^ d) {P Q : F[X]} (hne : P ≠ Q)
    (hdP : P.natDegree ≤ d) (hdQ : Q.natDegree ≤ d)
    (hp : P.coeff 0 = u * P.coeff d + b) (hq : Q.coeff 0 = u * Q.coeff d + b)
    (S : Finset I) (hag : ∀ j ∈ S, P.eval (D j) = Q.eval (D j)) : S.card ≤ d - 1 := by
  by_contra! bigger
  have deg := (natDegree_sub_le P Q).trans (max_le hdP hdQ)
  obtain ⟨htop, hpow⟩ := full_difference D S (P - Q) hD (sub_ne_zero.mpr hne) deg
    (by omega) (fun x hx => by rw [eval_sub, hag x hx, sub_self])
  simp only [coeff_sub] at htop hpow
  rw [hp, hq, add_sub_add_right_eq_sub, ← mul_sub, mul_pow, mul_comm] at hpow
  exact hu (mul_left_cancel₀ (pow_ne_zero n htop) hpow)

/-- Evaluation words from polynomials satisfying one affine relation between
their constant coefficient and coefficient in degree `d`. -/
def slice (D : I ↪ F) (d : ℕ) (u b : F) : Set (I → F) :=
  { w | ∃ P : F[X], P.natDegree ≤ d ∧ P.coeff 0 = u * P.coeff d + b ∧
    ∀ x, P.eval (D x) = w x }

open Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
  (card_le_universe_of_equal_card_pair_inter_le)

omit [DecidableEq I] [DecidableEq F] in
/-- At any received word, for any interleaving width, the excluded-slope subcode
has list size at most the block length throughout the improved Johnson region. -/
theorem forbidden_slice [Nonempty I] {d n t : ℕ} {c u b : F} (D : I ↪ F)
    (hD : ∀ j, (-D j) ^ n = c) (hu : u ^ n ≠ c ^ d) (arity : ℕ) (δ : ℝ)
    (hδ : δ * (Fintype.card I : ℝ) < (Fintype.card I : ℝ) - t + 1)
    (ht : 0 < t) (hgap : Fintype.card I * (d - 1) < t ^ 2) :
    Lambda (interleavedCodeSet (κ := Fin arity) (slice D d u b)) δ ≤
      (Fintype.card I : ℕ∞) := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro y W hW
  let e := (Fintype.equivFin ↥W).symm
  let word (i : Fin (Fintype.card ↥W)) := (e i).val
  let support (i : Fin (Fintype.card ↥W)) := univ.filter fun x => word i x = y x
  have hclose (i) := mem_closeCodewordsRel_iff.mp (hW (word i) (e i).property)
  have hsize (i) : t ≤ (support i).card := by
    have hd := (hclose i).2
    have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    rw [relHammingDist_coe, hammingDist_comm, div_le_iff₀ hn] at hd
    have htotal : (agree (word i) y : ℝ) + (hammingDist (word i) y : ℝ) = Fintype.card I := by
      exact_mod_cast agree_add_hammingDist
    exact Nat.le_of_lt_succ (by
      exact_mod_cast (show (t : ℝ) < (agree (word i) y : ℝ) + 1 by linarith))
  choose S hsub hcard using fun i => exists_subset_card_eq (hsize i)
  have pair : Pairwise fun i j => (S i ∩ S j).card ≤ d - 1 := by
    intro i j hij
    have wne : word i ≠ word j := fun he => hij (e.injective (Subtype.ext he))
    obtain ⟨x, z, hdiff⟩ : ∃ x z, word i x z ≠ word j x z := by
      by_contra! he
      exact wne (funext fun x => funext (he x))
    obtain ⟨P, hdP, hp, heP⟩ := (hclose i).1 z
    obtain ⟨Q, hdQ, hq, heQ⟩ := (hclose j).1 z
    have ne : P ≠ Q := fun h => hdiff ((heP x).symm.trans (h ▸ heQ x))
    apply fewer_roots D hD hu ne hdP hdQ hp hq
    intro x hx
    have hi := (mem_filter.mp (hsub i (mem_inter.mp hx).1)).2
    have hj := (mem_filter.mp (hsub j (mem_inter.mp hx).2)).2
    exact (heP x).trans ((congrFun (hi.trans hj.symm) z).trans (heQ x).symm)
  simpa using card_le_universe_of_equal_card_pair_inter_le
    S (Fintype.card I) t (d - 1) rfl ht hcard pair (by omega)

omit [DecidableEq I] in
/-- An overflow of the unrestricted scalar list yields distinct messages whose
coefficient pairs pass the test for every multiplier `a`. -/
theorem of_list {B d n t : ℕ} {c : F} (D : I ↪ F) (hD : ∀ j, (-D j) ^ n = c)
    (hd : 0 < d) (ht : t ≤ Fintype.card I) (hn : 0 < Fintype.card I)
    (hlist : (B : ℕ∞) < Lambda (ReedSolomon.code D (d + 1) : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I)) :
    ∃ P : Fin (B + 1) → F[X], Function.Injective P ∧ (∀ i, (P i).natDegree ≤ d) ∧
      ∀ a : ℕ, 2 * a * ((B + 1) * t) ≤ (B + 1) * (B * (d - 1)) +
        ∑ i, (partners (fun j => ((P j).coeff 0, (P j).coeff d)) n (c ^ d) i).card +
        a * (a + 1) * Fintype.card I := by
  classical
  obtain ⟨y, P, S, hinj, hdeg, hsize, hag, -⟩ :=
    from_list_at_overlap D (s := 0) (r := 0) (by omega) ht hn
      (fun _ _ _ => SimpleGraph.not_cliqueFree_zero) hlist
  have deg (i) : (P i).natDegree ≤ d := Nat.le_of_lt_succ (hdeg i)
  refine ⟨P, hinj, deg, fun a => ?_⟩
  simpa using necessary D hD P hinj deg S (fun i => (hsize i).ge) y hag hd a

/-- Each first open agreement count lies in the rank-safe region of every forbidden
slope slice. The two eighth-rate entries correspond to the two different budgets. -/
theorem named_slice_arithmetic :
    1073741824 * (536870911 - 1) < (759250124 : ℕ) ^ 2 ∧
    1073741824 * (268435455 - 1) < (536870910 : ℕ) ^ 2 ∧
    1073741824 * (134217727 - 1) < (379625061 : ℕ) ^ 2 ∧
    1073741824 * (134217727 - 1) < (379625060 : ℕ) ^ 2 ∧
    1073741824 * (67108863 - 1) < (268435453 : ℕ) ^ 2 := by decide

#print axioms all_products
#print axioms forbidden_slice
#print axioms full_difference
#print axioms of_list
#print axioms necessary
end ProximityGap.SplitCoefficientSecants
