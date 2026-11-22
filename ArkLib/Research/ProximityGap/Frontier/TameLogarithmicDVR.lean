/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Integer

/-! # Descent of logarithmic derivations along a tame DVR extension -/

namespace ArkLib.ProximityGap.TameLogarithmicDVR

open Polynomial

section Local

variable {B : Type*} [CommRing B]

/-- Differentiating a base uniformizer of the form `u^(e + 1) * v` shows that
a logarithmic derivation is tangent to `u` when the ramification index is a unit. -/
theorem uniformizer_log [IsDomain B] (D : Derivation ℤ B B) (u : B) (hu : u ≠ 0)
    (v : Bˣ) (e : ℕ) (he : IsUnit ((e + 1 : ℕ) : B))
    (h : u ^ (e + 1) ∣ D (u ^ (e + 1) * v)) : u ∣ D u := by
  obtain ⟨w, hw⟩ := h
  rw [D.leibniz, D.leibniz_pow] at hw
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_one_sub_one] at hw
  have hp : u ^ e * (((e + 1 : ℕ) : B) * (v:B) * D u) =
      u ^ e * (u * (w - D v)) := by
    rw [pow_succ] at hw
    linear_combination hw
  have h' := mul_left_cancel₀ (pow_ne_zero _ hu) hp
  obtain ⟨z,hz⟩ := he.mul v.isUnit
  refine ⟨(↑z⁻¹:B) * (w-D v), ?_⟩
  rw [←hz] at h'
  calc
    D u = (↑z⁻¹:B) * ((z:B) * D u) := by simp
    _ = _ := by rw [h']; ring

variable {S L : Type*} [CommRing S] [Field L]

/-- Differentiation modulo a prime whose residue kills the differentiated
coefficients obeys the ordinary polynomial chain rule. -/
theorem residue_chain (D : Derivation ℤ B B) (ρ : B →+* L) (i : S →+* B)
    (hi : ∀ c, ρ (D (i c)) = 0) (b : B) (f : S[X]) :
    ρ (D (f.eval₂ i b)) = f.derivative.eval₂ (ρ.comp i) (ρ b) * ρ (D b) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [derivative_add, hp, hq, add_mul]
  | monomial n c =>
    simp only [eval₂_monomial, D.leibniz, D.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      map_add, map_mul, map_natCast, map_pow, hi, mul_zero, add_zero, derivative_monomial,
      RingHom.comp_apply]
    ring

/-- A polynomial over the base lifting the residue minimal polynomial
has simple residue root whenever the residue-field extension is separable. -/
theorem residue_simple_lift {k : Type*} [Field k] [Algebra k L] [Algebra.IsSeparable k L]
    (σ : S →+* k) (hs : Function.Surjective σ) (φ : S →+* L)
    (hφ : φ = (algebraMap k L).comp σ) (x : L) :
    ∃ f : S[X], f.eval₂ φ x = 0 ∧ f.derivative.eval₂ φ x ≠ 0 := by
  obtain ⟨f,hf⟩ := Polynomial.map_surjective σ hs (minpoly k x)
  refine ⟨f, ?_, ?_⟩
  · rw [hφ, ←eval₂_map, hf]
    exact minpoly.aeval k x
  · rw [hφ, ←eval₂_map, ←derivative_map, hf]
    exact (Algebra.IsSeparable.isSeparable k x).aeval_derivative_ne_zero (minpoly.aeval k x)

/-- A derivation tangent to the uniformizer and zero on the base modulo it
vanishes on all residues if each residue has a separable relation over the base. -/
theorem residue_vanishes (D : Derivation ℤ B B) (u : B) (hu : u ∣ D u)
    (ρ : B →+* L) (hker : ∀ b, ρ b = 0 ↔ u ∣ b) (i : S →+* B)
    (hi : ∀ c, ρ (D (i c)) = 0)
    (hs : ∀ b : B, ∃ f : S[X], f.eval₂ (ρ.comp i) (ρ b) = 0 ∧
      f.derivative.eval₂ (ρ.comp i) (ρ b) ≠ 0) (b : B) : u ∣ D b := by
  obtain ⟨f,hf,hf'⟩ := hs b
  have hz : ρ (f.eval₂ i b) = 0 := by rwa [hom_eval₂]
  obtain ⟨c,hc⟩ := (hker _).mp hz
  have ht : ρ (D (f.eval₂ i b)) = 0 := by
    have h₀ : ρ u = 0 := (hker _).mpr (dvd_refl u)
    rw [hc,D.leibniz]
    simp [smul_eq_mul,h₀,(hker _).mpr hu]
  rw [residue_chain D ρ i hi b f] at ht
  exact (hker _).mp ((mul_eq_zero.mp ht).resolve_left hf')

end Local

section FractionField

variable {K : Type*} [Field K] {B : Subring K}

/-- A power of the uniformizer clears the derivation on the whole local ring. -/
def Clears (D : Derivation ℤ K K) (u : B) (m : ℕ) : Prop :=
  ∀ b : B, (u : K) ^ m * D (b : K) ∈ B

/-- The actual scaled fraction-field derivation restricted to its ring of integral values. -/
def scaled (D : Derivation ℤ K K) (u : B) (m : ℕ) (h : Clears D u m) : Derivation ℤ B B :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun b => ⟨(u : K) ^ m * D (b : K), h b⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [mul_add]) })
    (fun a b => Subtype.ext (by
      change (u : K)^m * D ((a:K)*(b:K)) =
        (a:K)*((u:K)^m*D (b:K)) + (b:K)*((u:K)^m*D (a:K))
      rw [D.leibniz]; simp only [smul_eq_mul]; ring))

private theorem scaled_log (D : Derivation ℤ K K) (u : B) (hu : u ≠ 0) (e : ℕ)
    (v : Bˣ) (he : IsUnit ((e + 1 : ℕ) : B)) (m : ℕ) (hc : Clears D u m)
    (hlog : ∃ c : B, D ((u ^ (e + 1) * v : B) : K) =
      ((u ^ (e + 1) * v : B) : K) * (c : K)) :
    u ∣ scaled D u m hc u := by
  apply uniformizer_log _ u hu v e he
  obtain ⟨c,hc'⟩ := hlog
  refine ⟨u^m*v*c, Subtype.ext ?_⟩
  change (u:K)^m*D ((u ^ (e + 1) * v : B) : K) = _
  rw [hc']
  simp only [Subring.coe_mul,Subring.coe_pow]
  ring

/-- Each positive pole-clearing exponent drops by one. -/
theorem descend {L : Type*} [Field L] (D : Derivation ℤ K K) (R : Subring B)
    (u : B) (hu : u ≠ 0) (e : ℕ) (v : Bˣ) (he : IsUnit ((e + 1 : ℕ) : B))
    (ρ : B →+* L) (hker : ∀ b, ρ b = 0 ↔ u ∣ b)
    (hbase : ∀ c : R, D ((c:B):K) ∈ B)
    (hlog : ∃ c : B, D ((u ^ (e + 1) * v : B) : K) =
      ((u ^ (e + 1) * v : B) : K) * (c : K))
    (hs : ∀ b : B, ∃ f : R[X], f.eval₂ (ρ.comp R.subtype) (ρ b) = 0 ∧
      f.derivative.eval₂ (ρ.comp R.subtype) (ρ b) ≠ 0)
    (m : ℕ) (hc : Clears D u (m+1)) : Clears D u m := by
  let δ := scaled D u (m+1) hc
  have htan : u ∣ δ u := scaled_log D u hu e v he (m+1) hc hlog
  have hr (c : R) : ρ (δ (R.subtype c)) = 0 := by
    apply (hker _).mpr
    refine ⟨u^m * (⟨D ((c:B):K),hbase c⟩ : B), Subtype.ext ?_⟩
    change (u:K)^(m+1)*D ((c:B):K) = (u:K)*((u:K)^m*D ((c:B):K))
    rw [pow_succ']; ring
  intro b
  obtain ⟨c,hc'⟩ := residue_vanishes δ u htan ρ hker R.subtype hr hs b
  have hmul := congrArg (fun t : B => (t:K)) hc'
  change (u:K)^(m+1)*D (b:K) = (u:K)*(c:K) at hmul
  rw [pow_succ',mul_assoc] at hmul
  rw [mul_left_cancel₀ (show (u:K)≠0 from fun h => hu (Subtype.ext h)) hmul]
  exact c.property

/-- Once one power clears the field derivation, tame ramification and a
separable residue extension make the unscaled derivation regular and logarithmic. -/
theorem logarithmic_of_clears [IsDiscreteValuationRing B] (D : Derivation ℤ K K)
    (R : Subring B) [IsLocalRing R] [IsLocalHom (algebraMap R B)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B)]
    (u : B) (hu : Irreducible u) (e : ℕ) (v : Bˣ) (he : IsUnit ((e + 1 : ℕ) : B))
    (hbase : ∀ c : R, D ((c:B):K) ∈ B)
    (hlog : ∃ c : B, D ((u ^ (e + 1) * v : B) : K) =
      ((u ^ (e + 1) * v : B) : K) * (c : K))
    (hclear : ∃ m, Clears D u m) :
    (∀ b : B, D (b:K) ∈ B) ∧ ∃ c : B, D (u:K) = (u:K)*(c:K) := by
  let ρ := IsLocalRing.residue B
  have hker (b : B) : ρ b=0 ↔ u ∣ b := by
    rw [IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer u).mp hu]
    exact Ideal.mem_span_singleton
  have hs (b : B) := residue_simple_lift (IsLocalRing.residue R)
    IsLocalRing.residue_surjective (ρ.comp R.subtype)
    (show ρ.comp R.subtype = (algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField B)).comp (IsLocalRing.residue R) by rfl) (ρ b)
  obtain ⟨m,hm⟩ := hclear
  have ht : Clears D u 0 := by
    induction m with
    | zero => exact hm
    | succ m ih => exact ih (descend D R u hu.ne_zero e v he ρ hker hbase hlog hs m hm)
  refine ⟨fun b => by simpa using ht b, ?_⟩
  obtain ⟨c,hc⟩ := scaled_log D u hu.ne_zero e v he 0 ht hlog
  refine ⟨c, ?_⟩
  have hh := congrArg (fun t : B => (t:K)) hc
  change (u:K)^0*D (u:K)=(u:K)*(c:K) at hh
  simpa using hh

/-- Over the fraction field of a DVR, one uniformizer power clears the
derivatives on every element of a finite algebra over the base. -/
theorem clear_finite_algebra [IsFractionRing B K] [IsDiscreteValuationRing B]
    (D : Derivation ℤ K K) (R : Subring B) (A : Subalgebra R B) [Module.Finite R A]
    (u : B) (hu : Irreducible u) (hbase : ∀ r : R, D ((r:B):K) ∈ B) :
    ∃ m : ℕ, ∀ a : A, (u:K)^m * D ((a:B):K) ∈ B := by
  classical
  obtain ⟨t,g,hg⟩ := Module.Finite.exists_fin (R:=R) (M:=A)
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors B) (fun j : Fin t => D ((g j:B):K))
  obtain ⟨m,v,hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (mem_nonZeroDivisors_iff_ne_zero.mp d.property) hu
  refine ⟨m,?_⟩
  have hgen (j : Fin t) : (u:K)^m*D ((g j:B):K) ∈ B := by
    obtain ⟨c,hc⟩ := hd j
    change (c:K) = ((d:B):K)*D ((g j:B):K) at hc
    rw [hv] at hc
    have he : (u:K)^m*D ((g j:B):K) = ((↑v⁻¹:B):K)*(c:K) := by
      rw [hc]
      simp only [Subring.coe_mul,Subring.coe_pow]
      have hinv : ((↑v⁻¹:B):K)*((v:B):K)=1 := by exact_mod_cast v.inv_mul
      linear_combination -(u:K)^m*D ((g j:B):K)*(hinv)
    rw [he]
    exact B.mul_mem (↑v⁻¹:B).property c.property
  intro a
  have hmem : a ∈ Submodule.span R (Set.range g) := hg.symm ▸ Submodule.mem_top
  refine Submodule.span_induction (s:=Set.range g) (R:=R) (p:=fun z _ => (u:K)^m*D ((z:B):K)∈B)
    (fun _ ⟨j,hj⟩ => hj ▸ hgen j) ?_ ?_ ?_ hmem
  · simp
  · intro x y _ _ hx hy
    change (u:K)^m*D (((x:B):K)+((y:B):K))∈B
    rw [map_add,mul_add]
    exact B.add_mem hx hy
  · intro r x _ hx
    change (u:K)^m*D (((r:B):K)*((x:B):K))∈B
    rw [D.leibniz]
    simp only [smul_eq_mul]
    rw [show (u:K)^m*(((r:B):K)*D ((x:B):K)+((x:B):K)*D ((r:B):K)) =
      ((r:B):K)*((u:K)^m*D ((x:B):K))+((x:B):K)*((u:K)^m*D ((r:B):K)) by ring]
    exact B.add_mem (B.mul_mem r.val.property hx)
      (B.mul_mem x.val.property (B.mul_mem (B.pow_mem u.property _) (hbase r)))

/-- Localizing a finite algebra at elements that become units in the local
DVR preserves a single common pole bound for the fraction-field derivation. -/
theorem clear_finite_localization [IsFractionRing B K] [IsDiscreteValuationRing B]
    (D : Derivation ℤ K K) (R : Subring B) (A : Subalgebra R B) [Module.Finite R A]
    (S : Submonoid A) [IsLocalization S B] (u : B) (hu : Irreducible u)
    (hbase : ∀ r : R, D ((r:B):K) ∈ B) : ∃ m, Clears D u m := by
  obtain ⟨m,hm⟩ := clear_finite_algebra D R A u hu hbase
  refine ⟨m,?_⟩
  intro b
  obtain ⟨⟨a,s⟩,hs⟩ := IsLocalization.surj S b
  obtain ⟨v,hv⟩ := IsLocalization.map_units B s
  change b*(s.val:B)=(a:B) at hs
  change (v:B)=(s.val:B) at hv
  have hh := congrArg (fun x : B => D (x:K)) hs
  change D ((b:K)*((s.val:B):K))=D ((a:B):K) at hh
  rw [D.leibniz] at hh
  simp only [smul_eq_mul] at hh
  let z : K := (u:K)^m*D ((a:B):K)-(b:K)*((u:K)^m*D ((s.val:B):K))
  have hz : z∈B := B.sub_mem (hm a) (B.mul_mem b.property (hm s.val))
  have he : ((v:B):K)*((u:K)^m*D (b:K))=z := by
    dsimp [z]; rw [hv]
    linear_combination (u:K)^m * hh
  have hval : (u:K)^m*D (b:K) = ((↑v⁻¹:B):K)*z := by
    rw [←he]
    have hunit : ((↑v⁻¹:B):K)*((v:B):K)=1 := by exact_mod_cast v.inv_mul
    rw [←mul_assoc,hunit,one_mul]
  rw [hval]
  exact B.mul_mem (↑v⁻¹:B).property hz

/-- A derivation on the fraction field extends regularly over a DVR that
is a localization of a finite algebra. It preserves the normalized uniformizer
ideal whenever the base uniformizer is logarithmic and ramification is tame. -/
theorem tame_logarithmic_lift [IsFractionRing B K] [IsDiscreteValuationRing B]
    (D : Derivation ℤ K K) (R : Subring B) [IsLocalRing R] [IsLocalHom (algebraMap R B)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B)]
    (A : Subalgebra R B) [Module.Finite R A] (S : Submonoid A) [IsLocalization S B]
    (u : B) (hu : Irreducible u) (e : ℕ) (v : Bˣ) (he : IsUnit ((e + 1 : ℕ) : B))
    (π : R) (hπ : (π : B) = u ^ (e + 1) * v) (hbase : ∀ r : R, D ((r:B):K) ∈ B)
    (hlog : ∃ c : R, D ((π:B):K)=((π:B):K)*((c:B):K)) :
    (∀ b : B, D (b:K) ∈ B) ∧ ∃ c : B, D (u:K) = (u:K)*(c:K) := by
  obtain ⟨c,hc⟩ := hlog
  apply logarithmic_of_clears D R u hu e v he hbase _ (clear_finite_localization D R A S u hu hbase)
  exact ⟨(c:B), hπ ▸ hc⟩

end FractionField

end ArkLib.ProximityGap.TameLogarithmicDVR

#print axioms ArkLib.ProximityGap.TameLogarithmicDVR.uniformizer_log
#print axioms ArkLib.ProximityGap.TameLogarithmicDVR.residue_vanishes
#print axioms ArkLib.ProximityGap.TameLogarithmicDVR.logarithmic_of_clears
#print axioms ArkLib.ProximityGap.TameLogarithmicDVR.tame_logarithmic_lift
