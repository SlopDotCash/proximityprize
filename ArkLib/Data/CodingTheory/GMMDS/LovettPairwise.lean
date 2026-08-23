/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettUnion
import ArkLib.Data.CodingTheory.GMMDS.LovettBaseCase
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination

/-!
# Lovett's GM-MDS proof: the two-vector (pairwise) case (#389)

The pairwise (`m = 2`) instance of Lovett's Theorem 1.7 (arXiv:1803.02523): for two
multiplicity vectors `v₀, v₁` satisfying the `V*(k)` MDS condition, the union family
`P(k,v₀) ∪ P(k,v₁) = { pVanish vᵢ · xᵉ : e < k − |vᵢ| }` is linearly independent over
`F[a] = MvPolynomial (Fin n) F`.

Mechanism (the "shared meet + coprime cofactor" argument):
* peel the coordinate-wise meet `w = v₀ ∧ v₁` out of both vanishing polynomials,
  `pVanish vᵢ = g · cᵢ` with `g = pVanish w`;
* the cofactors `c₀, c₁` are *coprime* (disjoint `(x − aⱼ)`-support, since `wⱼ = min`);
* a degree count plus `IsRelPrime` cancellation forces the `v₀`-side relation to vanish,
  then the `v₁`-side, then monomial independence finishes.

Issue #389.
-/

open Polynomial Finset

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- The coordinate-wise meet (pointwise `min`) of two multiplicity vectors. -/
def pairMeet (v0 v1 : Fin n → ℕ) : Fin n → ℕ := fun j => min (v0 j) (v1 j)

/-- The cofactor `cᵢ = ∏ⱼ (x − aⱼ)^{vᵢ(j) − wⱼ}` after peeling out the meet. -/
noncomputable def pairCofactor (v w : Fin n → ℕ) : (MvPolynomial (Fin n) F)[X] :=
  ∏ j, (xSubA j) ^ (v j - w j)

theorem pairCofactor_monic (v w : Fin n → ℕ) : (pairCofactor (F := F) v w).Monic :=
  monic_prod_of_monic _ _ (fun j _ => (xSubA_monic j).pow _)

theorem pairCofactor_ne_zero (v w : Fin n → ℕ) : pairCofactor (F := F) v w ≠ 0 :=
  (pairCofactor_monic v w).ne_zero

/-- **(H3)** Degree of a cofactor: `cᵢ.natDegree = ∑ⱼ (vᵢ(j) − wⱼ)`. -/
theorem pairCofactor_natDegree (v w : Fin n → ℕ) :
    (pairCofactor (F := F) v w).natDegree = ∑ j, (v j - w j) := by
  classical
  rw [pairCofactor, natDegree_prod_of_monic _ _ (fun j _ => (xSubA_monic j).pow _)]
  exact Finset.sum_congr rfl (fun j _ => by rw [natDegree_pow, xSubA_natDegree, mul_one])

/-- **(H1)** Peeling the meet: `pVanish v = pVanish w · cofactor v w` whenever `w ≤ v`
coordinate-wise. -/
theorem pVanish_eq_meet_mul_cofactor {v w : Fin n → ℕ} (hwv : ∀ j, w j ≤ v j) :
    pVanish (F := F) v = pVanish w * pairCofactor (F := F) v w := by
  classical
  rw [pVanish, pVanish, pairCofactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← pow_add]
  congr 1
  have := hwv j
  omega

theorem pairMeet_le_left (v0 v1 : Fin n → ℕ) (j : Fin n) : pairMeet v0 v1 j ≤ v0 j :=
  min_le_left _ _

theorem pairMeet_le_right (v0 v1 : Fin n → ℕ) (j : Fin n) : pairMeet v0 v1 j ≤ v1 j :=
  min_le_right _ _

/-- A single linear factor `x − aᵢ` is irreducible (degree-one monic / prime). -/
theorem xSubA_irreducible (i : Fin n) : Irreducible (xSubA (F := F) i) :=
  irreducible_X_sub_C _

/-- Distinct linear factors `x − aᵢ`, `x − aⱼ` (`i ≠ j`) are relatively prime. -/
theorem isRelPrime_xSubA {i j : Fin n} (hij : i ≠ j) :
    IsRelPrime (xSubA (F := F) i) (xSubA (F := F) j) := by
  rw [(xSubA_irreducible i).isRelPrime_iff_not_dvd]
  intro hdvd
  -- `x − aᵢ ∣ x − aⱼ`, both monic deg 1 ⟹ associated ⟹ equal ⟹ aᵢ = aⱼ ⟹ i = j.
  obtain ⟨g, hg⟩ := hdvd
  have hgmonic : g.Monic := by
    have := (xSubA_monic (F := F) j)
    rw [hg] at this
    exact (xSubA_monic (F := F) i).of_mul_monic_left this
  have hdeg : (xSubA (F := F) j).natDegree
      = (xSubA (F := F) i).natDegree + g.natDegree := by
    rw [hg, natDegree_mul (xSubA_monic i).ne_zero hgmonic.ne_zero]
  rw [xSubA_natDegree, xSubA_natDegree] at hdeg
  have hg0 : g.natDegree = 0 := by omega
  have hg1 : g = 1 := eq_one_of_monic_natDegree_zero hgmonic hg0
  rw [hg1, mul_one] at hg
  -- xSubA i = xSubA j ⟹ C (X i) = C (X j) ⟹ X i = X j ⟹ i = j
  have : (Polynomial.C (MvPolynomial.X i) : (MvPolynomial (Fin n) F)[X])
      = Polynomial.C (MvPolynomial.X j) := by
    have h2 := hg
    simp only [xSubA] at h2
    calc (Polynomial.C (MvPolynomial.X i) : (MvPolynomial (Fin n) F)[X])
        = Polynomial.X - (Polynomial.X - Polynomial.C (MvPolynomial.X i)) := by ring
      _ = Polynomial.X - (Polynomial.X - Polynomial.C (MvPolynomial.X j)) := by rw [h2]
      _ = Polynomial.C (MvPolynomial.X j) := by ring
  have hXX : (MvPolynomial.X i : MvPolynomial (Fin n) F) = MvPolynomial.X j :=
    Polynomial.C_injective this
  exact hij (MvPolynomial.X_injective hXX)

/-- **(H4)** The cofactors of two vectors over their meet are relatively prime: for each
coordinate `j`, `wⱼ = min` forces at least one of the two exponents to vanish, so no
`(x − aⱼ)` appears in both cofactors. -/
theorem isRelPrime_pairCofactor (v0 v1 : Fin n → ℕ) :
    IsRelPrime (pairCofactor (F := F) v1 (pairMeet v0 v1))
      (pairCofactor (F := F) v0 (pairMeet v0 v1)) := by
  classical
  set w := pairMeet v0 v1 with hw
  rw [pairCofactor, pairCofactor]
  refine IsRelPrime.prod_left (fun i _ => ?_)
  -- Factor at coordinate i on the v1-side.
  by_cases hi0 : v1 i - w i = 0
  · -- exponent 0 ⟹ factor is 1 ⟹ trivially relatively prime
    rw [hi0, pow_zero]; exact isRelPrime_one_left
  · -- exponent positive ⟹ w i = v0 i (since w i = min v0 v1 and v1 i > w i),
    -- hence v0 i - w i = 0: the i-th factor on the v0-side disappears.
    have hwi : w i = v0 i := by
      simp only [hw, pairMeet] at *; omega
    refine IsRelPrime.pow_left ?_
    refine IsRelPrime.prod_right (fun j _ => ?_)
    by_cases hij : i = j
    · subst hij
      have : v0 i - w i = 0 := by rw [hwi]; omega
      rw [this, pow_zero]; exact isRelPrime_one_right
    · exact IsRelPrime.pow_right (isRelPrime_xSubA hij)

/-- **The pairwise core.**  Given a `v₀`/`v₁` vanishing relation whose `v₀`-side coefficient `A`
has degree below `∑ⱼ(v₁(j)−wⱼ) = deg c₁`, the `v₀`-side coefficient vanishes.  Mechanism: peel the
meet (`pVanish vᵢ = g·cᵢ`), cancel the common `g ≠ 0`, then `c₁ ∣ c₀·A` with `IsRelPrime c₁ c₀`
gives `c₁ ∣ A`, impossible below `deg c₁` unless `A = 0`. -/
theorem pairwise_core {v0 v1 : Fin n → ℕ} {A B : (MvPolynomial (Fin n) F)[X]}
    (hrel : pVanish (F := F) v0 * A + pVanish (F := F) v1 * B = 0)
    (hdeg : A.natDegree < ∑ j, (v1 j - pairMeet v0 v1 j)) :
    A = 0 := by
  classical
  set w := pairMeet v0 v1 with hw
  set c0 := pairCofactor (F := F) v0 w with hc0
  set c1 := pairCofactor (F := F) v1 w with hc1
  have hv0 : pVanish (F := F) v0 = pVanish (F := F) w * c0 :=
    pVanish_eq_meet_mul_cofactor (pairMeet_le_left v0 v1)
  have hv1 : pVanish (F := F) v1 = pVanish (F := F) w * c1 :=
    pVanish_eq_meet_mul_cofactor (pairMeet_le_right v0 v1)
  rw [hv0, hv1] at hrel
  have hgne : pVanish (F := F) w ≠ 0 := (pVanish_monic w).ne_zero
  have hfac : pVanish (F := F) w * (c0 * A + c1 * B) = 0 := by linear_combination hrel
  have hsum : c0 * A + c1 * B = 0 :=
    (mul_eq_zero.mp hfac).resolve_left hgne
  have hca : c1 ∣ c0 * A := ⟨-B, by linear_combination hsum⟩
  have hrp : IsRelPrime c1 c0 := isRelPrime_pairCofactor v0 v1
  have hc1A : c1 ∣ A := hrp.dvd_of_dvd_mul_left hca
  by_contra hA0
  have hle := natDegree_le_of_dvd hc1A hA0
  rw [hc1, pairCofactor_natDegree] at hle
  omega

/-- For a two-vector system the coordinate-wise meet over `univ = {0,1}` is the pointwise `min`. -/
theorem vMeet_pair (V : Fin 2 → (Fin n → ℕ))
    (hI : (Finset.univ : Finset (Fin 2)).Nonempty) (j : Fin n) :
    vMeet V Finset.univ hI j = min (V 0 j) (V 1 j) := by
  show (Finset.univ : Finset (Fin 2)).inf' hI (fun i => V i j) = min (V 0 j) (V 1 j)
  refine le_antisymm (le_min ?_ ?_) (Finset.le_inf' _ _ (fun i _ => ?_))
  · exact Finset.inf'_le _ (Finset.mem_univ 0)
  · exact Finset.inf'_le _ (Finset.mem_univ 1)
  · fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- **The MDS degree bridge.**  For a `V*(k)` two-vector system, the MDS condition (ii) at
`I = {0,1}` yields `k − |V₀| ≤ ∑ⱼ(V₁(j) − minⱼ)`, the degree budget `pairwise_core` consumes. -/
theorem pairwise_mds_deg (V : Fin 2 → (Fin n → ℕ)) (k : ℕ) (hV : IsVStar V k) :
    k - vAbs (V 0) ≤ ∑ j, (V 1 j - pairMeet (V 0) (V 1) j) := by
  classical
  have hI : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hmds := hV.mds Finset.univ hI
  rw [Fin.sum_univ_two] at hmds
  have hmeet : vAbs (vMeet V Finset.univ hI) = ∑ j, min (V 0 j) (V 1 j) := by
    simp only [vAbs]; exact Finset.sum_congr rfl (fun j _ => vMeet_pair V hI j)
  rw [hmeet] at hmds
  have hadd : (∑ j, (V 1 j - pairMeet (V 0) (V 1) j)) + (∑ j, min (V 0 j) (V 1 j)) = vAbs (V 1) := by
    rw [← Finset.sum_add_distrib]
    simp only [vAbs]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (V 1 j - min (V 0 j) (V 1 j)) + min (V 0 j) (V 1 j) = V 1 j
    exact Nat.sub_add_cancel (min_le_right _ _)
  have hw1 : vAbs (V 1) ≤ k - 1 := hV.weight_le 1
  omega

/-- **The two-vector (pairwise) case of Lovett's GM-MDS Theorem 1.7.**  For ANY two-vector
`V*(k)` system (primitivity not required — only the MDS condition at `I = {0,1}`), the union
family `P(k,V) = { pVanish (V i) · xᵉ : i < 2, e < k − |V i| }` is linearly independent over
`F[a] = MvPolynomial (Fin n) F`.  This is the pairwise base of the GM-MDS induction, beyond the
`m ≤ 1` bases; it discharges the `m = 2` instance unconditionally. -/
theorem lovett_pairwise_linearIndependent (V : Fin 2 → (Fin n → ℕ)) (k : ℕ) (hV : IsVStar V k) :
    LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set A : (MvPolynomial (Fin n) F)[X] :=
    ∑ e : Fin (k - vAbs (V 0)), g ⟨0, e⟩ • (Polynomial.X) ^ (e : ℕ) with hA
  set B : (MvPolynomial (Fin n) F)[X] :=
    ∑ e : Fin (k - vAbs (V 1)), g ⟨1, e⟩ • (Polynomial.X) ^ (e : ℕ) with hB
  -- cheap unfold of a single union member (isolated so the defeq does not blow up in context)
  have hpfu : ∀ (i : Fin 2) (e : Fin (k - vAbs (V i))),
      pFamUnion (F := F) V k ⟨i, e⟩ = pVanish (F := F) (V i) * Polynomial.X ^ (e : ℕ) :=
    fun _ _ => rfl
  -- the split relation: pVanish(V0)·A + pVanish(V1)·B = the original vanishing combination
  have hrel : pVanish (F := F) (V 0) * A + pVanish (F := F) (V 1) * B = 0 := by
    have expand : pVanish (F := F) (V 0) * A + pVanish (F := F) (V 1) * B
        = ∑ p : (Σ i : Fin 2, Fin (k - vAbs (V i))), g p • pFamUnion (F := F) V k p := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Fin.sum_univ_two, hA, hB,
        Finset.mul_sum, Finset.mul_sum]
      congr 1 <;>
        refine Finset.sum_congr rfl (fun e _ => ?_) <;>
        rw [hpfu, mul_smul_comm]
    rw [expand]; exact hg
  -- degree bound: deg A < k − |V0|
  have hAbnd : A.natDegree ≤ k - vAbs (V 0) - 1 := by
    rw [hA]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun e _ => ?_)
    calc (g ⟨0, e⟩ • (Polynomial.X : (MvPolynomial (Fin n) F)[X]) ^ (e : ℕ)).natDegree
        ≤ ((Polynomial.X : (MvPolynomial (Fin n) F)[X]) ^ (e : ℕ)).natDegree :=
          Polynomial.natDegree_smul_le _ _
      _ = (e : ℕ) := by rw [natDegree_pow, natDegree_X, mul_one]
      _ ≤ k - vAbs (V 0) - 1 := by have := e.isLt; omega
  -- pairwise core ⟹ A = 0 (the empty-fiber case `k = |V0|` is handled directly), then B = 0
  have hA0 : A = 0 := by
    rcases Nat.eq_zero_or_pos (k - vAbs (V 0)) with h0 | h0
    · rw [hA]
      refine Finset.sum_eq_zero (fun e _ => ?_)
      exfalso; have := e.isLt; omega
    · have hAdeg : A.natDegree < k - vAbs (V 0) := by omega
      exact pairwise_core hrel (lt_of_lt_of_le hAdeg (pairwise_mds_deg V k hV))
  have hB0 : B = 0 := by
    rw [hA0, mul_zero, zero_add] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left (pVanish_monic (V 1)).ne_zero
  -- monomial independence extracts the coefficients on each side
  have hgA : ∀ e, g (⟨0, e⟩ : Σ i : Fin 2, Fin (k - vAbs (V i))) = 0 := by
    have hxi := xpow_linearIndependent (MvPolynomial (Fin n) F) (k - vAbs (V 0))
    rw [Fintype.linearIndependent_iff] at hxi
    exact hxi (fun e => g ⟨0, e⟩) (by rw [← hA]; exact hA0)
  have hgB : ∀ e, g (⟨1, e⟩ : Σ i : Fin 2, Fin (k - vAbs (V i))) = 0 := by
    have hxi := xpow_linearIndependent (MvPolynomial (Fin n) F) (k - vAbs (V 1))
    rw [Fintype.linearIndependent_iff] at hxi
    exact hxi (fun e => g ⟨1, e⟩) (by rw [← hB]; exact hB0)
  intro p
  obtain ⟨i, e⟩ := p
  fin_cases i
  · exact hgA e
  · exact hgB e

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.pairwise_core
#print axioms ArkLib.GMMDS.pairwise_mds_deg
#print axioms ArkLib.GMMDS.lovett_pairwise_linearIndependent
