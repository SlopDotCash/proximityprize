/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R390RelationResultantCertificate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS3AnnihilatorHeightBound

/-!
# LANE B2 (#466 round 391): THE HEIGHT LEDGER FOR SECTOR RELATIONS — bounded-height
  annihilators, completing the census→arithmetic weld

r390 gave every vanishing relation a nonzero annihilator divisible by `p`.  This brick adds
the HEIGHT: relation vectors have `ℓ∞ ≤ 2r` (differences of `r`-tuple shadows), so the FS3
factorial bound applies with `B = 2r`:

* **`abs_vecOf_le_one` / `abs_le_of_mem_keysR`** :  realized keys have entries `|v_j| ≤ r`;
* **`abs_sub_le_two_mul`** :  relation entries are bounded by `2r`;
* **`relPoly_coeff_abs_le`** :  hence `relPoly z` has all coefficients `≤ 2r` in absolute
  value;
* **`relation_certificate_with_height`** :  for `m = 2^k`, char `p`, `g^m = −1`, `1 ≤ r`,
  every vanishing nonzero relation `z` owns `N(z) = patternResultant m (relPoly z)` with

  ```text
  N(z) ≠ 0,   p ∣ N(z),   |N(z)| ≤ (2m)! · (2r)^{2m}
  ```

* **`sectorRelations_certificate_with_height`** :  ditto for every member of every sector.

This completes the generic arithmetic ledger: at depth `r` and dimension `m`, EVERY
contributing relation of the r389 census identity is certified by a nonzero integer of
height `≤ (2m)!·(2r)^{2m}`, divisible by the prime.  A prime therefore admits at most
`log_p((2m)!·(2r)^{2m})` "bad divisibilities" per relation-annihilator value — the FS1
double-count's quantitative input, now available at every depth for the exact census
objects.  Issue #466, round 391, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R391RelationHeightLedger

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R388SectorRelationCountBound
open ArkLib.ProximityGap.Frontier.R389CensusIdentityExactFiber
open ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate
open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant
open ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem abs_vecOf_le_one (n m : ℕ) (a : Fin n) (j : Fin m) :
    |vecOf n m a j| ≤ 1 := by
  unfold vecOf
  split_ifs <;> norm_num

/-- Realized keys have entries bounded by `r` in absolute value. -/
theorem abs_le_of_mem_keysR (n m r : ℕ) (v : Fin m → ℤ)
    (hv : v ∈ keysR n m r) (j : Fin m) : |v j| ≤ (r : ℤ) := by
  classical
  unfold keysR at hv
  rw [Finset.mem_image] at hv
  obtain ⟨t, _, rfl⟩ := hv
  unfold tupleVec
  calc |∑ i : Fin r, vecOf n m (t i) j|
      ≤ ∑ i : Fin r, |vecOf n m (t i) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin r, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => abs_vecOf_le_one n m (t i) j)
    _ = (r : ℤ) := by simp

/-- Relation entries (differences of realized keys) are bounded by `2r`. -/
theorem abs_sub_le_two_mul (n m r : ℕ) (v w : Fin m → ℤ)
    (hv : v ∈ keysR n m r) (hw : w ∈ keysR n m r) (j : Fin m) :
    |v j - w j| ≤ (2 * r : ℤ) := by
  calc |v j - w j| ≤ |v j| + |w j| := abs_sub _ _
    _ ≤ (r : ℤ) + (r : ℤ) :=
        add_le_add (abs_le_of_mem_keysR n m r v hv j) (abs_le_of_mem_keysR n m r w hw j)
    _ = (2 * r : ℤ) := by ring

/-- All coefficients of the relation polynomial are bounded by the relation's `ℓ∞`. -/
theorem relPoly_coeff_abs_le (m : ℕ) (z : Fin m → ℤ) {B : ℤ}
    (hB : 0 ≤ B) (hz : ∀ j : Fin m, |z j| ≤ B) (i : ℕ) :
    |(relPoly m z).coeff i| ≤ B := by
  by_cases hi : i < m
  · have := relPoly_coeff m z ⟨i, hi⟩
    rw [show ((⟨i, hi⟩ : Fin m) : ℕ) = i from rfl] at this
    rw [this]
    exact hz ⟨i, hi⟩
  · rw [Polynomial.coeff_eq_zero_of_degree_lt]
    · simpa using hB
    · exact lt_of_lt_of_le (relPoly_degree_lt m z)
        (by exact_mod_cast Nat.le_of_not_lt hi)

/-- **The height-equipped certificate**: every vanishing nonzero relation owns a nonzero
annihilator divisible by `p` of height at most `(2m)! · (2r)^{2m}`. -/
theorem relation_certificate_with_height (k : ℕ) (m r : ℕ) (hm : m = 2 ^ k)
    (hr : 1 ≤ r) (p : ℕ) [CharP F p]
    (g : F) (hg : g ^ m = -1)
    (z : Fin m → ℤ) (hz : evalVec g m z = 0) (hz0 : z ≠ 0)
    (hheight : ∀ j : Fin m, |z j| ≤ (2 * r : ℤ)) :
    patternResultant m (relPoly m z) ≠ 0
      ∧ (p : ℤ) ∣ patternResultant m (relPoly m z)
      ∧ |patternResultant m (relPoly m z)|
          ≤ (Nat.factorial (2 * m) : ℤ) * (2 * r : ℤ) ^ (2 * m) := by
  have hm0 : 0 < m := by rw [hm]; positivity
  have hcert := relation_resultant_certificate k m hm p g hg z hz hz0
  refine ⟨hcert.1, hcert.2, ?_⟩
  have hB : (1 : ℤ) ≤ (2 * r : ℤ) := by
    have : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    linarith
  have habs := patternResultant_abs_le hm0 (relPoly m z) hB
    (relPoly_coeff_abs_le m z (by linarith) hheight)
  refine le_trans habs ?_
  have hdeg : (relPoly m z).natDegree < m := relPoly_natDegree_lt m z hz0
  have hexp : m + (relPoly m z).natDegree ≤ 2 * m := by omega
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · exact_mod_cast Nat.factorial_le hexp
  · exact pow_le_pow_right₀ hB hexp

/-- **Every sector relation carries the height-equipped certificate.** -/
theorem sectorRelations_certificate_with_height (k : ℕ) (n m r s : ℕ)
    (hm : m = 2 ^ k) (hr : 1 ≤ r) (p : ℕ) [CharP F p]
    (g : F) (hg : g ^ m = -1)
    (z : Fin m → ℤ) (hz : z ∈ sectorRelations g n m r s) :
    ∃ N : ℤ, N ≠ 0 ∧ (p : ℤ) ∣ N
      ∧ |N| ≤ (Nat.factorial (2 * m) : ℤ) * (2 * r : ℤ) ^ (2 * m) := by
  classical
  have hvan := sectorRelations_vanishing g n m r s z hz
  -- extract the entry bound from a witnessing pair
  have hheight : ∀ j : Fin m, |z j| ≤ (2 * r : ℤ) := by
    unfold sectorRelations at hz
    rw [Finset.mem_filter, Finset.mem_image] at hz
    obtain ⟨⟨q, hq, rfl⟩, _⟩ := hz
    unfold shadowCollisionPairs at hq
    rw [Finset.mem_filter, Finset.mem_offDiag] at hq
    intro j
    exact abs_sub_le_two_mul n m r q.1 q.2 hq.1.1 hq.1.2.1 j
  obtain ⟨h1, h2, h3⟩ := relation_certificate_with_height k m r hm hr p g hg
    z hvan.1 hvan.2 hheight
  exact ⟨patternResultant m (relPoly m z), h1, h2, h3⟩

end ArkLib.ProximityGap.Frontier.R391RelationHeightLedger

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R391RelationHeightLedger.abs_le_of_mem_keysR
#print axioms
  ArkLib.ProximityGap.Frontier.R391RelationHeightLedger.relation_certificate_with_height
#print axioms
  ArkLib.ProximityGap.Frontier.R391RelationHeightLedger.sectorRelations_certificate_with_height
