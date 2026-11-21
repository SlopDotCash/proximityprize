/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.FiniteNormalizationColength
import ArkLib.Research.ProximityGap.Frontier.JacobianPowerFiniteAlgebra
import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Pulling the first-polar algebra back to the completed curve

Every primary factor of a finite quotient of the affine curve is a quotient
of its completion at the corresponding point. The comparison uses the actual
adic evaluation map and preserves the polar equation.
-/

set_option autoImplicit false
noncomputable section

open Module AdicCompletion
open scoped PowerSeries BigOperators

namespace ArkLib.ProximityGap.Frontier.CompletedFirstPolar

open FiniteNormalizationColength JacobianPowerFiniteAlgebra

variable {K T R : Type*} [Field K] [CommRing T] [CommRing R] [Algebra K T] [Algebra K R]

/-- The canonical map from the completed curve to a factor of a finite quotient. -/
def factorMap (ψ : T →ₐ[K] R) (m : Ideal R) (N : ℕ) :
    AdicCompletion (m.comap ψ) T →ₐ[K] (R ⧸ m^N) :=
  (Ideal.quotientMapₐ (m^N) ψ (Ideal.le_comap_pow ψ.toRingHom N)).comp
    ((AdicCompletion.evalₐ (m.comap ψ) N).restrictScalars K)

set_option backward.isDefEq.respectTransparency false in
/-- On the original curve, the map agrees with the literal quotient map. -/
@[simp] theorem factorMap_of (ψ : T →ₐ[K] R) (m : Ideal R) (N : ℕ) (x : T) :
    factorMap ψ m N (AdicCompletion.of (m.comap ψ) T x) = Ideal.Quotient.mk (m^N) (ψ x) := by
  exact congrArg (Ideal.quotientMapₐ (m^N) ψ (Ideal.le_comap_pow ψ.toRingHom N))
    (AdicCompletion.evalₐ_of (m.comap ψ) N x)

theorem factorMap_surjective (ψ : T →ₐ[K] R) (hψ : Function.Surjective ψ) (m : Ideal R) (N : ℕ) :
    Function.Surjective (factorMap ψ m N) := by
  intro x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨w,rfl⟩ := hψ y
  exact ⟨AdicCompletion.of (m.comap ψ) T w, factorMap_of ..⟩

/-- For the actual completion and actual primary quotient, all that is needed
to bound the quotient by branch orders is the finite-defect normalization. -/
theorem factor_rank_le {ι : Type*} [Fintype ι] [Module.Finite K R]
    (ψ : T →ₐ[K] R) (hψ : Function.Surjective ψ) (m : Ideal R) (N : ℕ) (p : T) (hp : ψ p = 0)
    (inc : AdicCompletion (m.comap ψ) T →ₐ[K] (ι → K⟦X⟧))
    (hi : Function.Injective inc)
    (hr : ∀ i, inc (AdicCompletion.of (m.comap ψ) T p) i ≠ 0)
    (hdef : Module.length K ((ι → K⟦X⟧) ⧸ inc.toLinearMap.range) ≠ ⊤) :
    finrank K (R ⧸ m^N) ≤ ∑ i, (inc (AdicCompletion.of (m.comap ψ) T p) i).order.toNat := by
  let q := AdicCompletion.of (m.comap ψ) T p
  apply finite_factor_rank_le inc.toLinearMap (LinearMap.mulLeft K q) (inc q) hi hr ?_ hdef
    (factorMap ψ m N).toLinearMap (factorMap_surjective ψ hψ m N) ?_
  · apply LinearMap.ext
    intro x
    exact map_mul inc q x
  · ext x
    change factorMap ψ m N (q*x) = 0
    rw [map_mul, show factorMap ψ m N q = 0 by simp [q, hp], zero_mul]

variable {S : Type*} [CommRing S] [Algebra K S]

/-- The quotient map from the original chart algebra to the first polar. -/
def polarMap (c u v : S) (a : ℕ) : S →ₐ[K] FirstPolar c u v a :=
  (Ideal.Quotient.mkₐ K _).comp (Ideal.Quotient.mkₐ K _)

theorem polarMap_surjective (c u v : S) (a : ℕ) : Function.Surjective (polarMap (K := K) c u v a) :=
  Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective

@[simp] theorem polarMap_polar (c u v : S) (a : ℕ) :
    polarMap (K := K) c u v a (u+c*v) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- Both Jacobian partials vanish at every residue-field point of the
first-polar algebra. -/
theorem polarMap_support {L : Type*} [Field L] (c u v : S) (a : ℕ)
    (η : FirstPolar c u v a →+* L) :
    η (polarMap (K := K) c u v a u) = 0 ∧ η (polarMap (K := K) c u v a v) = 0 := by
  have hgen (i : Fin (a+1)) : u^i.val * v^(a-i.val) ∈ mixedIdeal u v a :=
    Ideal.subset_span ⟨i,rfl⟩
  have hu : u^a ∈ mixedIdeal u v a := by simpa using hgen ⟨a, Nat.lt_succ_self a⟩
  have hv : v^a ∈ mixedIdeal u v a := by simpa using hgen ⟨0, Nat.zero_lt_succ a⟩
  have vanish (w : S) (hw : w^a ∈ mixedIdeal u v a) :
      η (polarMap (K := K) c u v a w) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := a)
    rw [← map_pow, ← map_pow]
    change η (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (w^a))) = 0
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hw]
  exact ⟨vanish u hu, vanish v hv⟩

/-- The global Artinian dimension is controlled by completed local branch
orders. All maps to the individual primary factors are canonical. -/
theorem global_rank_le [Module.Finite K R] [IsArtinianRing R]
    (ψ : T →ₐ[K] R) (hψ : Function.Surjective ψ) (p : T) (hp : ψ p = 0)
    (ι : MaximalSpectrum R → Type*) [∀ m, Fintype (ι m)]
    (inc : ∀ m : MaximalSpectrum R, AdicCompletion (m.asIdeal.comap ψ) T →ₐ[K] (ι m → K⟦X⟧))
    (hi : ∀ m, Function.Injective (inc m))
    (hr : ∀ m i, inc m (AdicCompletion.of (m.asIdeal.comap ψ) T p) i ≠ 0)
    (hdef : ∀ m, Module.length K ((ι m → K⟦X⟧) ⧸ (inc m).toLinearMap.range) ≠ ⊤) :
    letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
    finrank K R ≤ ∑ m, ∑ i, (inc m (AdicCompletion.of (m.asIdeal.comap ψ) T p) i).order.toNat := by
  classical
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  obtain ⟨N,hN⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  rw [finrank_eq_sum_local (K := K) N hN]
  exact Finset.sum_le_sum fun m _ =>
    factor_rank_le ψ hψ m.asIdeal N p hp (inc m) (hi m) (hr m) (hdef m)

/-- For the actual Jacobian-power algebra and any affine curve presentation,
the same branches used by the Hessian bound control the raw codimension. -/
theorem jacobian_rank_le [Module.Finite K S]
    (c u v : S) (a : ℕ) [IsArtinianRing (FirstPolar c u v a)]
    (θ : T →ₐ[K] S) (hθ : Function.Surjective θ) (p : T) (hθp : θ p = u+c*v)
    (ι : MaximalSpectrum (FirstPolar c u v a) → Type*) [∀ m, Fintype (ι m)]
    (inc : ∀ m : MaximalSpectrum (FirstPolar c u v a), AdicCompletion
      (m.asIdeal.comap ((polarMap (K := K) c u v a).comp θ)) T →ₐ[K] (ι m → K⟦X⟧))
    (hi : ∀ m, Function.Injective (inc m))
    (hr : ∀ m i, inc m (AdicCompletion.of _ T p) i ≠ 0)
    (hdef : ∀ m, Module.length K ((ι m → K⟦X⟧) ⧸ (inc m).toLinearMap.range) ≠ ⊤) :
    letI : Fintype (MaximalSpectrum (FirstPolar c u v a)) := Fintype.ofFinite _
    finrank K (PowerQuotient u v a) ≤ a * ∑ m, ∑ i, (inc m (AdicCompletion.of _ T p) i).order.toNat := by
  classical
  let _ : Fintype (MaximalSpectrum (FirstPolar c u v a)) := Fintype.ofFinite _
  apply (power_quotient_finrank (K := K) c u v a).trans
  apply Nat.mul_le_mul_left
  apply global_rank_le ((polarMap (K := K) c u v a).comp θ)
    ((polarMap_surjective c u v a).comp hθ) p _ ι inc hi hr hdef
  simp [hθp]

#print axioms jacobian_rank_le
#print axioms global_rank_le
#print axioms factor_rank_le
#print axioms polarMap_support

end ArkLib.ProximityGap.Frontier.CompletedFirstPolar
