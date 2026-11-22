/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import CompPoly.Univariate.EuclideanAlgorithm
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Research.ProximityGap.Frontier.QuarterSplitPencilProduct
import ArkLib.Research.ProximityGap.Frontier.SaturatedListCliques

/-! # Exact agreement counts for proposed pairs on dyadic evaluation cosets

Repeated squaring modulo a proposed difference computes its common roots with
the domain polynomial. The input includes the coset power and order exponent.
The computation does not construct the full domain polynomial or enumerate sites.
-/

set_option autoImplicit false
namespace ProximityGap.DyadicDifferenceRoots
open Finset Polynomial CompPoly
open ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct (sites dvd_nodal_iff_sites)

variable {F : Type} [Field F] [DecidableEq F]

/-- Remainder of `X^(2^h)` after `h` modular squarings. -/
def residue (q : CPolynomial F) : ℕ → CPolynomial F
  | 0 => CPolynomial.X.modByMonic q
  | h + 1 =>
    let r := residue q h
    (r * r).modByMonic q

/-- A computable factor whose roots are the common roots of the input and
the dyadic coset binomial. -/
def factor (p : CPolynomial F) (h : ℕ) (c : F) : CPolynomial F :=
  let q := CPolynomial.monicNormalize p
  CPolynomial.gcdMonic q (residue q h - CPolynomial.C c)

/-- Exact number of physical roots. The zero polynomial agrees on the whole domain. -/
def rootCount (p : CPolynomial F) (h : ℕ) (c : F) : ℕ :=
  if p == 0 then 2 ^ h else (factor p h c).natDegree

theorem residue_spec (q : CPolynomial F) (hq : q.monic) (h : ℕ) :
    (residue q h).toPoly = ((Polynomial.X : F[X]) ^ (2 ^ h)) %ₘ q.toPoly := by
  induction h with
  | zero =>
    simp only [residue, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hq,
      CPolynomial.X_toPoly, pow_zero, pow_one]
  | succ h ih =>
    rw [residue, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hq, CPolynomial.toPoly_mul,
      ih, ← mul_modByMonic, ← pow_two, ← pow_mul, pow_succ]

/-- The factor detects all common polynomial divisors, including multiplicities. -/
theorem dvd_factor_iff {p : CPolynomial F} (hp : p ≠ 0) (h : ℕ) (c : F) (A : F[X]) :
    A ∣ (factor p h c).toPoly ↔ A ∣ p.toPoly ∧ A ∣ (Polynomial.X : F[X]) ^ (2 ^ h) - C c := by
  let q := CPolynomial.monicNormalize p
  have qnorm : q.toPoly = normalize p.toPoly := CPolynomial.monicNormalize_toPoly_eq_normalize _
  have hq : q.monic := (CPolynomial.monic_toPoly_iff q).mpr
    (qnorm ▸ monic_normalize ((CPolynomial.toPoly_eq_zero_iff p).not.mpr hp))
  let U := (residue q h - CPolynomial.C c).toPoly
  let N : F[X] := (Polynomial.X : F[X]) ^ (2 ^ h) - C c
  have diff : q.toPoly ∣ U - N := by
    dsimp only [U,N]
    rw [CPolynomial.toPoly_sub, CPolynomial.C_toPoly, residue_spec q hq]
    convert dvd_modByMonic_sub ((Polynomial.X : F[X]) ^ (2 ^ h)) q.toPoly using 1
    ring
  change A ∣ (CPolynomial.gcdMonic q _).toPoly ↔ _ ∧ A ∣ N
  rw [CPolynomial.gcdMonic_toPoly_eq_normalize_gcd, dvd_normalize_iff]
  change A ∣ EuclideanDomain.gcd q.toPoly U ↔ _ ∧ _
  constructor
  · intro ha
    have h1 := ha.trans (EuclideanDomain.gcd_dvd_left q.toPoly U)
    have h2 := ha.trans (EuclideanDomain.gcd_dvd_right q.toPoly U)
    refine ⟨dvd_normalize_iff.mp (qnorm ▸ h1), ?_⟩
    convert dvd_sub h2 (h1.trans diff) using 1
    ring
  · rintro ⟨h1, h2⟩
    have hqA : A ∣ q.toPoly := qnorm ▸ dvd_normalize_iff.mpr h1
    apply EuclideanDomain.dvd_gcd hqA
    convert dvd_add (hqA.trans diff) h2 using 1
    ring

variable {I : Type} [Fintype I]

/-- On the complete dyadic coset, `rootCount` is the number of distinct
evaluation sites where the polynomial vanishes. -/
theorem rootCount_eq (D : I ↪ F) {h : ℕ} {c : F} (hn : Fintype.card I = 2 ^ h)
    (hD : ∀ i, D i ^ (2 ^ h) = c) (p : CPolynomial F) :
    rootCount p h c = (sites D p.toPoly).card := by
  classical
  by_cases hp : p = 0
  · simp [hp, rootCount, sites, CPolynomial.toPoly_zero, hn]
  have hpos : 0 < 2 ^ h := pow_pos (by decide) _
  have nodal : Lagrange.nodal univ D = (Polynomial.X : F[X]) ^ (2 ^ h) - C c := by
    symm
    apply eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic (monic_X_pow_sub_C c hpos.ne')
    · exact prod_X_sub_C_dvd _ _ D.injective.injOn _ (fun i _ => by simp [hD i])
    · rw [natDegree_X_pow_sub_C, Lagrange.natDegree_nodal, card_univ, hn]
  let G := (factor p h c).toPoly
  have hdg := (dvd_factor_iff hp h c G).mp dvd_rfl
  have hG : G ≠ 0 := by
    intro he
    have : p.toPoly = 0 := zero_dvd_iff.mp (he ▸ hdg.1)
    exact hp ((CPolynomial.toPoly_eq_zero_iff p).mp this)
  have same : sites D G = sites D p.toPoly := by
    ext i
    simp only [sites, mem_filter, mem_univ, true_and]
    change IsRoot G (D i) ↔ IsRoot p.toPoly (D i)
    simp only [← dvd_iff_isRoot, G, dvd_factor_iff hp]
    exact and_iff_left (dvd_iff_isRoot.mpr (by simp [IsRoot.def, hD i]))
  rw [rootCount, ite_eq_right (by simpa using hp), CPolynomial.natDegree_toPoly,
    ← same, (dvd_nodal_iff_sites D hG).mp (nodal ▸ hdg.2)]

/-- Necessary integer test for any proposed message table to agree with one center.
Each contribution is its exact number of physical coincidences. -/
theorem family_test (D : I ↪ F) {h M t : ℕ} {c : F}
    (hn : Fintype.card I = 2 ^ h) (hD : ∀ i, D i ^ (2 ^ h) = c)
    (P : Fin M → CPolynomial F) (S : Fin M → Finset I) (hsize : ∀ i, t ≤ (S i).card)
    (y : I → F) (hag : ∀ i x, x ∈ S i → (P i).toPoly.eval (D x) = y x) (a : ℕ) :
    2 * a * (M * t) ≤ (∑ i, ∑ j ∈ univ.erase i, rootCount (P i - P j) h c) +
      a * (a + 1) * 2 ^ h := by
  classical
  have sd (i j : Fin M) : (S i ∩ S j).card ≤ rootCount (P i - P j) h c := by
    rw [rootCount_eq D hn hD]
    apply card_le_card
    intro x hx
    simp only [sites, mem_filter, mem_univ, true_and]
    rw [CPolynomial.toPoly_sub, eval_sub, hag i x (mem_inter.mp hx).1,
      hag j x (mem_inter.mp hx).2, sub_self]
  have bound := SaturatedListCliques.pair_incidence S hsize a
  rw [hn] at bound
  exact bound.trans (by gcongr; exact sd _ _)

/-- Every scalar over-budget list yields an explicit table of distinct polynomial
messages passing the exact dyadic collision test. -/
theorem of_list (D : I ↪ F) {h k B t : ℕ} {c : F}
    (hn : Fintype.card I = 2 ^ h) (hD : ∀ i, D i ^ (2 ^ h) = c)
    (hk : 0 < k) (ht : t ≤ Fintype.card I)
    (hlist : (B : ℕ∞) < Code.Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I)) :
    ∃ P : Fin (B + 1) → CPolynomial F, Function.Injective P ∧ (∀ i, (P i).natDegree < k) ∧
      ∀ a : ℕ, 2 * a * ((B + 1) * t) ≤ (∑ i, ∑ j ∈ univ.erase i, rootCount (P i - P j) h c) +
        a * (a + 1) * 2 ^ h := by
  classical
  obtain ⟨y, Q, S, hinj, hdeg, hsize, hag, -⟩ :=
    SaturatedListCliques.from_list_at_overlap D (s := 0) (r := 0) hk ht
      (hn ▸ pow_pos (by decide) _) (fun _ _ _ => SimpleGraph.not_cliqueFree_zero) hlist
  let P (i) := CPolynomial.ringEquiv.symm (Q i)
  have hP i : (P i).toPoly = Q i := CPolynomial.ringEquiv.apply_symm_apply _
  refine ⟨P, CPolynomial.ringEquiv.symm.injective.comp hinj, fun i => ?_, fun a => ?_⟩
  · simpa only [CPolynomial.natDegree_toPoly, hP] using hdeg i
  · exact family_test D hn hD P S (fun i => (hsize i).ge) y
      (fun i x hx => (congrArg (eval (D x)) (hP i)).trans (hag i x hx)) a

/-- The quadratics `X²-1` and `X²+X-1` have identical end coefficients. -/
private def quadratic (a : F) : CPolynomial F :=
  CPolynomial.X * CPolynomial.X + CPolynomial.C a * CPolynomial.X - 1

open ArkLib.ProximityGap

section
local instance : Fact (Nat.Prime PrizeShapePrimeP30.P) := ⟨PrizeShapePrimeP30.prime_P⟩
local instance : Fact (Nat.Prime PrizeShapePrimeP30Second.P) := ⟨PrizeShapePrimeP30Second.prime_P⟩

set_option maxRecDepth 6000 in
/-- On each named subgroup, two differences pass the same end-coefficient test
and have respectively two and zero physical roots. -/
theorem named_quadratic_roots :
    rootCount (quadratic (0 : ZMod PrizeShapePrimeP30.P)) 30 1 = 2 ∧
    rootCount (quadratic (1 : ZMod PrizeShapePrimeP30.P)) 30 1 = 0 ∧
    rootCount (quadratic (0 : ZMod PrizeShapePrimeP30Second.P)) 30 1 = 2 ∧
    rootCount (quadratic (1 : ZMod PrizeShapePrimeP30Second.P)) 30 1 = 0 := by
  decide +kernel

end

#print axioms named_quadratic_roots
#print axioms of_list
#print axioms rootCount_eq
end ProximityGap.DyadicDifferenceRoots
