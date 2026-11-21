/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.IntrinsicQuarticSectionCap
import ArkLib.Research.ProximityGap.Frontier.ReverseHessianAffineSection
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-! # A primitive trivariate component in either iterated function-field presentation

Localizing the innermost variable preserves primality of an equation of positive
value degree. A generic divisibility already holds in the raw polynomial ring,
since every cleared denominator has value degree zero.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped nonZeroDivisors
namespace ArkLib.ProximityGap.Frontier.TerminalQuarticLocalization
open JetMultiplierGraph

variable {k : Type} [Field k]
abbrev localPlane (f : k[X][X][X]) : (RatFunc k)[X][X] :=
  mapPlane (algebraMap k[X] (RatFunc k)) f

private theorem baseInjective :
    Function.Injective (mapRingHom (algebraMap k[X] (RatFunc k))) :=
  Polynomial.map_injective _ (RatFunc.algebraMap_injective k)

theorem local_degree (f : k[X][X][X]) : (localPlane f).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective baseInjective f

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

private abbrev den (k : Type) [Field k] : Submonoid k[X][X][X] :=
  ((k[X])⁰.map (Polynomial.C : k[X] →+* k[X][X])).map (Polynomial.C : k[X][X] →+* k[X][X][X])

set_option backward.isDefEq.respectTransparency false in
theorem local_irreducible (f : k[X][X][X]) (hf : Irreducible f) (hy : 0 < f.natDegree) :
    Irreducible (localPlane f) := by
  have hpos : 0 < (localPlane f).natDegree := (local_degree f).symm ▸ hy
  have hnon : localPlane f ≠ 0 := by intro hz; simp [hz] at hpos
  have hunit := not_isUnit_of_natDegree_pos (localPlane f) hpos
  let L := IsLocalization.toLocalizationMap (R := k[X][X][X]) (den k) ((RatFunc k)[X][X])
  have hf' : Prime f := hf.prime
  exact (L.map_prime (m := f) hf' hnon hunit).irreducible

/-- Fractional irreducibility and the primitiveness required by canonical site order. -/
theorem local_generic (f : k[X][X][X]) (hf : Irreducible f) (hy : 0 < f.natDegree) :
    (localPlane f).IsPrimitive ∧ Irreducible (MovingCubicVanishingBranch.genericEquation (localPlane f)) := by
  have hi := local_irreducible f hf hy
  have hp := hi.isPrimitive (by rw [local_degree]; omega)
  exact ⟨hp,(hp.irreducible_iff_irreducible_map_fraction_map (K := RatFunc (RatFunc k))).mp hi⟩

/-- Divisibility over both fraction-field variables descends to the original
positive-value-degree prime component. -/
theorem raw_dvd_iff (f g : k[X][X][X]) (hf : Irreducible f) (hy : 0 < f.natDegree) :
    f ∣ g ↔ MovingCubicVanishingBranch.genericEquation (localPlane f) ∣
      MovingCubicVanishingBranch.genericEquation (localPlane g) := by
  have hp := (local_generic f hf hy).1
  rw [← hp.dvd_iff_fraction_map_dvd_fraction_map (RatFunc (RatFunc k))]
  change f ∣ g ↔ (IsLocalization.toLocalizationMap (den k) (RatFunc k)[X][X]) f ∣
    (IsLocalization.toLocalizationMap (den k) (RatFunc k)[X][X]) g
  rw [Submonoid.LocalizationMap.map_dvd_map]
  constructor
  · intro hd
    exact ⟨1,one_mem _,by simpa using hd⟩
  · rintro ⟨s,hs,hd⟩
    have hf' : Prime f := hf.prime
    refine (hf'.dvd_or_dvd hd).resolve_left ?_
    rintro hx
    obtain ⟨a,ha,rfl⟩ := hs
    obtain ⟨b,hb,rfl⟩ := ha
    have hn : (C (C b) : k[X][X][X]) ≠ 0 :=
      C_ne_zero.mpr (C_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hb))
    have hle := Polynomial.natDegree_le_of_dvd hx hn
    rw [natDegree_C] at hle
    omega

end ArkLib.ProximityGap.Frontier.TerminalQuarticLocalization
