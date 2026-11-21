/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Length
import Mathlib.Data.ENat.Monoid
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Colength on branches of a curve

For a curve algebra embedded with finite codimension in finitely many power
series branches, the polar colength equals the sum of its branch orders.
The coordinate ring and its normalization may both be infinite dimensional.
-/

set_option autoImplicit false
noncomputable section

open Module LinearMap Finset
open scoped BigOperators PowerSeries

namespace ArkLib.ProximityGap.Frontier.FiniteNormalizationColength

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module K A] [Module K B] [Module K C]

/-- Cokernel length is additive under composition by an injection. -/
theorem length_coker_comp (f : A →ₗ[K] B) (g : B →ₗ[K] C) (hg : Function.Injective g) :
    Module.length K (C ⧸ (g.comp f).range) =
      Module.length K (B ⧸ f.range) + Module.length K (C ⧸ g.range) := by
  let q := (g.comp f).range
  have hpre : q.comap g = f.range := by
    ext x
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, hg hw⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
  let i := f.range.mapQ q g hpre.ge
  have hq : q ≤ g.range := LinearMap.range_comp_le_range _ _
  let π := Submodule.factor hq
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot]
    simp only [i, Submodule.ker_mapQ, hpre, Submodule.mkQ_map_self]
  have he : Function.Exact i π := by
    apply LinearMap.exact_iff.mpr
    simp [i, π, Submodule.factor, Submodule.ker_mapQ, Submodule.range_mapQ]
  exact Module.length_eq_add_of_exact i π hi (Submodule.factor_surjective hq) he

/-- A finite-dimensional normalization defect cancels from the two
factorizations of multiplication by a common parameter. -/
theorem length_eq_of_finite_defect (inc : A →ₗ[K] B) (u : A →ₗ[K] A) (v : B →ₗ[K] B)
    (hi : Function.Injective inc) (hv : Function.Injective v)
    (hc : inc.comp u = v.comp inc) (hdef : Module.length K (B ⧸ inc.range) ≠ ⊤) :
    Module.length K (A ⧸ u.range) = Module.length K (B ⧸ v.range) := by
  apply ENat.add_left_injective_of_ne_top hdef
  dsimp only
  rw [← length_coker_comp u inc hi, hc, length_coker_comp inc v hv, add_comm]

variable {ι : Type*}

/-- Multiplication by a tuple of formal series, one per branch. -/
def branchMul (r : ι → K⟦X⟧) : (ι → K⟦X⟧) →ₗ[K] (ι → K⟦X⟧) :=
  LinearMap.mulLeft K r

/-- The polar jet takes the coefficients up to its branch order at every point. -/
def branchJets (n : ι → ℕ) :
    (ι → K⟦X⟧) →ₗ[K] ((i : ι) → Fin (n i) → K) :=
  LinearMap.pi fun i => LinearMap.pi fun j =>
    (PowerSeries.coeff j.val).comp (LinearMap.proj i)

theorem branchJets_surjective (n : ι → ℕ) : Function.Surjective (branchJets (K := K) n) := by
  intro g
  refine ⟨fun i => PowerSeries.mk (fun k => if h : k < n i then g i ⟨k,h⟩ else 0), ?_⟩
  funext i j
  simp [branchJets, PowerSeries.coeff_mk, j.isLt]

/-- The kernel of the simultaneous polar jets consists of actual multiples
of the polar in the product of the normalized branch rings. -/
theorem branchJets_ker (r : ι → K⟦X⟧) (hr : ∀ i, r i ≠ 0) :
    (branchJets fun i => (r i).order.toNat).ker = (branchMul r).range := by
  ext x
  have hdiv (i : ι) : r i ∣ x i ↔ (PowerSeries.X : K⟦X⟧) ^ (r i).order.toNat ∣ x i := by
    obtain ⟨u, hu⟩ := PowerSeries.isUnit_divided_by_X_pow_order (hr i)
    have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := r i)
    rw [← hu] at h
    conv_lhs => lhs; rw [← h]
    exact Units.mul_right_dvd
  constructor
  · intro hx
    have hj : ∀ i, r i ∣ x i := by
      intro i
      apply (hdiv i).mpr
      rw [PowerSeries.X_pow_dvd_iff]
      intro j hj
      exact congrFun (congrFun (LinearMap.mem_ker.mp hx) i) ⟨j,hj⟩
    choose w hw using hj
    exact ⟨w, funext fun i => (hw i).symm⟩
  · rintro ⟨w, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i j
    exact PowerSeries.X_pow_dvd_iff.mp ((hdiv i).mp ⟨w i, rfl⟩) j j.isLt

variable [Fintype ι]

/-- Length on the product of complete normalized branches is exactly the
sum of the ordinary vanishing orders of the polar. -/
theorem branch_polar_colength (r : ι → K⟦X⟧) (hr : ∀ i, r i ≠ 0) :
    Module.length K ((ι → K⟦X⟧) ⧸ (branchMul r).range) = ↑(∑ i, (r i).order.toNat) := by
  rw [← branchJets_ker r hr]
  let e := (branchJets (K := K) fun i => (r i).order.toNat).quotKerEquivOfSurjective
    (branchJets_surjective _)
  rw [e.length_eq, Module.length_eq_finrank]
  simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]

/-- If a normalization is given as a finite-codimension inclusion into
power-series branches, the actual curve polar colength is the branch order sum. -/
theorem local_polar_colength (inc : A →ₗ[K] (ι → K⟦X⟧)) (u : A →ₗ[K] A)
    (r : ι → K⟦X⟧) (hi : Function.Injective inc) (hr : ∀ i, r i ≠ 0)
    (hc : inc.comp u = (branchMul r).comp inc)
    (hdef : Module.length K ((ι → K⟦X⟧) ⧸ inc.range) ≠ ⊤) :
    Module.length K (A ⧸ u.range) = ↑(∑ i, (r i).order.toNat) := by
  apply (length_eq_of_finite_defect inc u (branchMul r) hi ?_ hc hdef).trans
    (branch_polar_colength r hr)
  intro x y hxy
  exact funext fun i => mul_left_cancel₀ (hr i) (congrFun hxy i)

/-- An Artinian factor of the completed local curve cut out by the polar
has dimension at most the sum of its vanishing orders on the branches. -/
theorem finite_factor_rank_le {L : Type*} [AddCommGroup L] [Module K L] [Module.Finite K L]
    (inc : A →ₗ[K] (ι → K⟦X⟧)) (u : A →ₗ[K] A) (r : ι → K⟦X⟧)
    (hi : Function.Injective inc) (hr : ∀ i, r i ≠ 0)
    (hc : inc.comp u = (branchMul r).comp inc)
    (hdef : Module.length K ((ι → K⟦X⟧) ⧸ inc.range) ≠ ⊤)
    (π : A →ₗ[K] L) (hπ : Function.Surjective π) (hz : π.comp u = 0) :
    finrank K L ≤ ∑ i, (r i).order.toNat := by
  have hk : u.range ≤ π.ker := by
    rintro _ ⟨x,rfl⟩
    exact LinearMap.congr_fun hz x
  let φ := u.range.liftQ π hk
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x,rfl⟩ := hπ y
    exact ⟨u.range.mkQ x, rfl⟩
  have h := Module.length_le_of_surjective φ hφ
  rw [Module.length_eq_finrank, local_polar_colength inc u r hi hr hc hdef] at h
  exact_mod_cast h

#print axioms finite_factor_rank_le
#print axioms length_eq_of_finite_defect
#print axioms branch_polar_colength
#print axioms local_polar_colength

end ArkLib.ProximityGap.Frontier.FiniteNormalizationColength
