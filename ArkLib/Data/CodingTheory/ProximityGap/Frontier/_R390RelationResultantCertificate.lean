/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R389CensusIdentityExactFiber
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS2PatternAnnihilatorResultant

/-!
# LANE B2 (#466 round 390): EVERY SECTOR RELATION OWNS A RESULTANT ANNIHILATOR — the
  census identity welded to the FS arithmetic ledger

r389 identified the wall scalar as `S = Σ_{z vanishing} M(z)`.  This brick proves that
each vanishing relation `z` carries an INTEGER CERTIFICATE: a nonzero integer
`patternResultant m (relPoly z)` divisible by the characteristic.  Hence the set of primes
at which a given relation can vanish is finite (divisors of a fixed nonzero integer), and
the r389 sum ranges over relations whose FS2 annihilators the prime divides.

* **`relPoly`** :  the relation as an integer polynomial `Σ_j z_j X^j` (degree `< m`);
* **`relPoly_coeff` / `relPoly_ne_zero` / `relPoly_degree_lt`** :  basic structure;
* **`aeval_relPoly`** :  `aeval g (relPoly z) = evalVec g m z` — the shadow evaluation IS
  polynomial evaluation;
* **`relation_resultant_certificate`** :  for `m = 2^k`, char `p`, `g^m = −1`, and a
  vanishing nonzero relation `z`:  `patternResultant m (relPoly z) ≠ 0` and
  `(p : ℤ) ∣ patternResultant m (relPoly z)`  (FS2's nonvanishing + divisibility);
* **`sectorRelations_annihilator`** :  every member of `sectorRelations g n m r s` owns
  such a certificate.

Combined chain: wall scalar `S` (r331) = `Σ_{z vanishing} M(z)` (r389), and each `z` in the
sum forces `p ∣ N(z)` with `N(z) ≠ 0` a fixed integer of the relation (this brick) — so `S`
at a given prime is controlled by which of the finitely many relation-annihilators the
prime divides: the exact object of the FS1 (prime × pattern) double-count and the r305
census.  Issue #466, round 390, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound
open ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber
open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The relation vector as an integer polynomial `Σ_j z_j X^j`. -/
noncomputable def relPoly (m : ℕ) (z : Fin m → ℤ) : ℤ[X] :=
  ∑ j : Fin m, Polynomial.monomial (j : ℕ) (z j)

theorem relPoly_coeff (m : ℕ) (z : Fin m → ℤ) (j : Fin m) :
    (relPoly m z).coeff (j : ℕ) = z j := by
  unfold relPoly
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro i _ hij
    rw [Polynomial.coeff_monomial, if_neg]
    intro h
    exact hij (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem relPoly_ne_zero (m : ℕ) (z : Fin m → ℤ) (hz0 : z ≠ 0) :
    relPoly m z ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
  intro h
  apply hj
  have := relPoly_coeff m z j
  rw [h, Polynomial.coeff_zero] at this
  exact this.symm

theorem relPoly_degree_lt (m : ℕ) (z : Fin m → ℤ) :
    (relPoly m z).degree < (m : ℕ) := by
  unfold relPoly
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe m)]
  intro j _
  refine lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) ?_
  exact_mod_cast j.isLt

theorem relPoly_natDegree_lt (m : ℕ) (z : Fin m → ℤ) (hz0 : z ≠ 0) :
    (relPoly m z).natDegree < m := by
  rw [Polynomial.natDegree_lt_iff_degree_lt (relPoly_ne_zero m z hz0)]
  exact relPoly_degree_lt m z

/-- **The shadow evaluation is polynomial evaluation**: `aeval g (relPoly z) = evalVec z`. -/
theorem aeval_relPoly (g : F) (m : ℕ) (z : Fin m → ℤ) :
    Polynomial.aeval g (relPoly m z) = evalVec g m z := by
  unfold relPoly evalVec
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.aeval_monomial, zsmul_eq_mul]
  congr 1

/-- **The resultant certificate**: a vanishing nonzero relation at an order-`2m` element
(`g^m = −1`, `m = 2^k`) forces the characteristic to divide the relation's nonzero
FS2 annihilator. -/
theorem relation_resultant_certificate (k : ℕ) (m : ℕ) (hm : m = 2 ^ k)
    (p : ℕ) [CharP F p]
    (g : F) (hg : g ^ m = -1)
    (z : Fin m → ℤ) (hz : evalVec g m z = 0) (hz0 : z ≠ 0) :
    patternResultant m (relPoly m z) ≠ 0
      ∧ (p : ℤ) ∣ patternResultant m (relPoly m z) := by
  have hm0 : 0 < m := by
    rw [hm]
    positivity
  constructor
  · subst hm
    exact patternResultant_ne_zero (relPoly_ne_zero _ z hz0)
      (relPoly_natDegree_lt _ z hz0)
  · refine charP_dvd_patternResultant_of_common_root hm0 F p g hg ?_
    rw [aeval_relPoly]
    exact hz

/-- **Every sector relation owns an annihilator**: for each `z` in any r387/r389 sector,
there is a nonzero integer divisible by the characteristic — the finite obstruction set of
the census, per relation, machine-checked. -/
theorem sectorRelations_annihilator (k : ℕ) (n m r s : ℕ) (hm : m = 2 ^ k)
    (p : ℕ) [CharP F p]
    (g : F) (hg : g ^ m = -1)
    (z : Fin m → ℤ) (hz : z ∈ sectorRelations g n m r s) :
    ∃ N : ℤ, N ≠ 0 ∧ (p : ℤ) ∣ N := by
  have hvan := sectorRelations_vanishing g n m r s z hz
  exact ⟨patternResultant m (relPoly m z),
    (relation_resultant_certificate k m hm p g hg z hvan.1 hvan.2).1,
    (relation_resultant_certificate k m hm p g hg z hvan.1 hvan.2).2⟩

end ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate.aeval_relPoly
#print axioms
  ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate.relation_resultant_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate.sectorRelations_annihilator
