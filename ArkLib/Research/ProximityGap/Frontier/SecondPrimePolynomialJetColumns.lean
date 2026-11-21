/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeJetMultiplication
import Mathlib.RingTheory.Polynomial.DegreeLT

/-! # Polynomial multipliers in the joint jet at a received site -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimePolynomialJetColumns

open Finset Polynomial SecondPrimeJetMultiplication
variable {K : Type} [Field K]

/-- Coefficient of the column obtained by a monomial shift in the truncated jet. -/
noncomputable def entry {R : Type} [CommRing R] (p : R[X][X]) (x y : ℕ × ℕ) : R :=
  if x.1 ≤ y.1 ∧ x.2 ≤ y.2 then (p.coeff (y.1-x.1)).coeff (y.2-x.2) else 0

private theorem shift_coeff {R : Type} [CommRing R] (p : R[X][X]) (x y : ℕ × ℕ) :
    ((p * monomial x.1 (monomial x.2 (1 : R))).coeff y.1).coeff y.2 = entry p x y := by
  classical
  simp only [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C, map_one,
    one_mul, entry]
  split_ifs <;> simp_all [coeff_mul_X_pow']

/-- Apply the genuine jet multiplier by its untranslated shifts of coefficients. -/
theorem multiplyJet_apply (f : K[X][X]) (n μ : ℕ) (v : Jet n → K) (y : Jet μ) :
    multiplyJet f n μ v y = ∑ x : Jet n, v x * entry f x.val y.val := by
  classical
  change ((f * ∑ x : Jet n, v x • monomial x.val.1 (monomial x.val.2 1)).coeff _).coeff _ = _
  simp only [Finset.mul_sum, mul_smul_comm, finsetSum_coeff, coeff_smul, shift_coeff, smul_eq_mul]

/-- Scalar localization, retaining both axes of the joint jet. -/
noncomputable def generic (p : K[X][X][X]) : (RatFunc K)[X][X] :=
  p.map (mapRingHom (algebraMap K[X] (RatFunc K)))

private theorem entry_generic (p : K[X][X][X]) (x y : ℕ × ℕ) :
    entry (generic p) x y = algebraMap K[X] (RatFunc K) (entry p x y) := by
  simp only [generic, entry, coeff_map, coe_mapRingHom]
  split_ifs <;> simp

private theorem entry_degree (p : K[X][X][X]) (m : ℕ)
    (hp : ∀ i j, ((p.coeff i).coeff j).natDegree ≤ m) (x y : ℕ × ℕ) :
    (entry p x y).natDegree ≤ m := by
  unfold entry
  split_ifs
  · exact hp _ _
  · simp

private theorem term_degree (p q : K[X]) {m e : ℕ} (hp : p.natDegree ≤ m)
    (hq : q ∈ degreeLT K e) : q * p ∈ degreeLT K (e+m) := by
  by_cases h : q = 0
  · simp [h]
  rw [mem_degreeLT] at hq ⊢
  apply (degree_le_natDegree.trans_lt ?_)
  have hq' : q.natDegree < e := by simpa [degree_eq_natDegree h] using hq
  exact_mod_cast (natDegree_mul_le.trans_lt (by omega : q.natDegree+p.natDegree < e+m))

/-- Translate independent jet columns by bounded scalar polynomials, keeping all entries
polynomial prior to scalar specialization. The output has scalar degree strictly below e+m. -/
noncomputable def boundedColumns (p : K[X][X][X]) (n μ m e : ℕ)
    (hp : ∀ i j, ((p.coeff i).coeff j).natDegree ≤ m) :
    (Jet n → degreeLT K e) →ₗ[K] (Jet μ → degreeLT K (e+m)) where
  toFun v y := ⟨∑ x : Jet n, (v x).val * entry p x.val y.val,
    (degreeLT K (e+m)).sum_mem fun x _ =>
      term_degree _ _ (entry_degree p m hp _ _) (v x).property⟩
  map_add' v w := by ext y j; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by ext y j; simp [Finset.smul_sum]

/-- Polynomial scalar multipliers of bounded degree remain independent over the ground
field, thanks to generic independence of the actual monomial shifts. -/
theorem boundedColumns_injective (p : K[X][X][X]) (μ m e : ℕ)
    (hp : ∀ i j, ((p.coeff i).coeff j).natDegree ≤ m) (hgen : generic p ≠ 0) :
    Function.Injective (boundedColumns p (μ-jetOrder (generic p)) μ m e hp) := by
  classical
  let n := μ - jetOrder (generic p)
  let χ := algebraMap K[X] (RatFunc K)
  intro v w h
  have hgen' : multiplyJet (generic p) n μ (fun x => χ (v x).val) =
      multiplyJet (generic p) n μ (fun x => χ (w x).val) := by
    ext y
    have hy := congrArg (fun b : Jet μ → degreeLT K (e+m) => χ (b y).val) h
    change χ (∑ x : Jet n, (v x).val * entry p _ _) = χ (∑ x : Jet n, (w x).val * entry p _ _) at hy
    simpa only [multiplyJet_apply, entry_generic, map_sum, map_mul, χ] using hy
  have hh := multiplyJet_injective (generic p) hgen μ hgen'
  funext x
  exact Subtype.ext (RatFunc.algebraMap_injective K (congrFun hh x))

private theorem bounded_finrank (n e : ℕ) :
    Module.finrank K (Jet n → degreeLT K e) = (n * (n+1)/2) * e := by
  have he : Module.finrank K (degreeLT K e) = e := by
    simpa using (degreeLTEquiv K e).finrank_eq
  rw [Module.finrank_pi_fintype]
  simp [he, Jet, GSMultInterp.card_multIdx]

/-- Exact net number of scalar linear conditions charged at a single site. -/
theorem bounded_codimension (p : K[X][X][X]) (μ m e : ℕ)
    (hp : ∀ i j, ((p.coeff i).coeff j).natDegree ≤ m) (hgen : generic p ≠ 0) :
    let n := μ - jetOrder (generic p)
    Module.finrank K ((Jet μ → degreeLT K (e+m)) ⧸
      LinearMap.range (boundedColumns p n μ m e hp)) =
        (μ * (μ+1) / 2) * (e+m) - (n * (n+1)/2)*e := by
  dsimp only
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (boundedColumns p (μ-jetOrder (generic p)) μ m e hp))
  rw [LinearMap.finrank_range_of_inj (boundedColumns_injective p μ m e hp hgen),
    bounded_finrank, bounded_finrank] at h
  exact Nat.eq_sub_of_add_eq h

#print axioms bounded_codimension
end ArkLib.ProximityGap.Frontier.SecondPrimePolynomialJetColumns
