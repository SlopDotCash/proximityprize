/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

/-!
# Coset FFT domains

This file defines coset FFT domains: evaluation domains of the form `x · G` for an FFT
subgroup domain `G`.  The data is packaged as a structure `CosetFftDomain` (an injective
group embedding `Multiplicative ι →* Fˣ` together with a coset generator) and an
abstract interface `CosetFftDomainClass` characterizing such maps via `map_zero_unit`,
`map_add`, and `map_neg`.  It provides the `FunLike` instance, the evaluation identity
`eval_coset_fft_domain_eq_eval_generator_mul_domain`, conversions between the structure and
the class (`mkSubgroupUnit`, `toCosetFftDomain`), injectivity lemmas, the `SmoothCosetFftDomain`
abbreviation, and the underlying `Finset` of evaluation points (`toFinset`, `card_toFinset`).
-/

namespace Domain

open Function

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- A coset FFT domain is a domain of the form `x · G` for
  an FFT domain `G`. -/
structure CosetFftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] where
  subgroupDomain : Multiplicative ι →* Fˣ
  subgroupDomain_inj : Injective subgroupDomain
  cosetGenerator : Fˣ

class CosetFftDomainClass.{u, v}
  (D : Type u) (ι : outParam (Type v)) [AddCommGroup ι]
  (F : outParam (Type v)) [Field F] [FunLike D ι F] where
  map_zero_unit (ω : D) : IsUnit (ω 0)
  map_add (ω : D) (i j : ι) : ω (i + j) = (ω 0)⁻¹ * ω i * ω j
  map_neg (ω : D) (i : ι) : ω (-i) = (ω 0) ^ 2 * (ω i)⁻¹
  injective (ω : D) : Injective ω

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma ne_zero (ω : D) (i : ι) : ω i ≠ 0 := fun h ↦ by
  have h0 : IsUnit (ω 0) := map_zero_unit ω
  have h_add := map_add ω i (-i)
  rw [add_neg_cancel, h] at h_add
  simp only [mul_zero, zero_mul] at h_add
  exact h0.ne_zero h_add

end CosetFftDomainClass

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
private lemma eq_iff_gen_and_domains_eq {φ₁ φ₂ : CosetFftDomain ι F} :
  φ₁ = φ₂ ↔ φ₁.cosetGenerator = φ₂.cosetGenerator ∧
    φ₁.subgroupDomain = φ₂.subgroupDomain := by
  rcases φ₁ with ⟨f₁, h₁⟩
  aesop

end CosetFftDomain

instance : FunLike (CosetFftDomain ι F) ι F where
  coe cosetDomain i :=
    cosetDomain.cosetGenerator * cosetDomain.subgroupDomain i
  coe_injective' φ₁ φ₂ h := by
    simp only at h
    have h₀ := congrFun h 0
    have h := congrFun h
    have key₀ : (φ₁.subgroupDomain (0 : ι) : F) = 1 := by
      simp [show (0 : ι) = (1 : Multiplicative ι) from rfl]
    have key₁ : (φ₂.subgroupDomain (0 : ι) : F) = 1 := by
      simp [show (0 : ι) = (1 : Multiplicative ι) from rfl]
    rw [key₀, mul_one, key₁, mul_one] at h₀
    have h_coset : φ₁.cosetGenerator = φ₂.cosetGenerator := Units.ext h₀
    have h_eq : ∀ a : ι, (φ₁.subgroupDomain a : F) = (φ₂.subgroupDomain a : F) := fun a ↦ by
      have ha := h a
      simp only [h_coset, mul_eq_mul_left_iff, Units.ne_zero, or_false] at ha
      exact ha
    exact CosetFftDomain.eq_iff_gen_and_domains_eq.mpr
      ⟨h_coset, MonoidHom.ext fun x => Units.ext (h_eq x)⟩

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma eval_coset_fft_domain_eq_eval_generator_mul_domain
    {cosetDomain : CosetFftDomain ι F} {i : ι} :
  cosetDomain i = cosetDomain.cosetGenerator * cosetDomain.subgroupDomain i := rfl

end CosetFftDomain

instance : CosetFftDomainClass (CosetFftDomain ι F) ι F where
  map_zero_unit ω := by
    aesop (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])
  map_add ω i j := by
    have :
      (i + j) = ((Multiplicative.ofAdd i) * (Multiplicative.ofAdd j) : Multiplicative ι) := by rfl
    have : ω.subgroupDomain (0 : ι) = 1 := by
      simp [show (0 : ι) = (1 : Multiplicative ι) from rfl]
    aesop
      (add simp
        [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
          Multiplicative.ofAdd])
      (add safe (by field_simp))
  map_neg ω i := by
    have h₁ : (-i : ι) = (Multiplicative.ofAdd i)⁻¹ := by rfl
    have h₂ : (0 : ι) = (Multiplicative.ofAdd 0 : Multiplicative ι) := by rfl
    aesop
      (add simp [sq, CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])
      (add safe (by field_simp))
  injective ω x y h := ω.subgroupDomain_inj <| by
    aesop
      (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

namespace CosetFftDomainClass

def mkSubgroupUnit {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) (i : ι) : Fˣ where
  val := (ω 0)⁻¹ * ω i
  inv := ω 0 * (ω i)⁻¹
  val_inv := by
    have h0 := CosetFftDomainClass.ne_zero ω (0 : ι)
    have hi := CosetFftDomainClass.ne_zero ω i
    field_simp
  inv_val := by
    have h0 := CosetFftDomainClass.ne_zero ω (0 : ι)
    have hi := CosetFftDomainClass.ne_zero ω i
    field_simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
private lemma mkSubgroupUnit_mul {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) (a b : ι) :
    mkSubgroupUnit ω (a + b) = mkSubgroupUnit ω a * mkSubgroupUnit ω b := by
  unfold mkSubgroupUnit
  have := (‹CosetFftDomainClass D ι F›.map_add ω a b)
  aesop (add safe (by grind))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
private lemma mkSubgroupUnit_injective {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) : Injective (mkSubgroupUnit ω) := by
  intro a b hab
  apply (‹CosetFftDomainClass D ι F›.injective ω)
  have h_eq : (ω 0)⁻¹ * ω a = (ω 0)⁻¹ * ω b := by
    convert congr_arg Units.val hab using 1
  exact mul_left_cancel₀
    (inv_ne_zero (show ω 0 ≠ 0 from by have :=
      (‹CosetFftDomainClass D ι F›.ne_zero ω 0); aesop)) h_eq

def toCosetFftDomain {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) :
  CosetFftDomain ι F where
  subgroupDomain := {
    toFun := fun i ↦ mkSubgroupUnit ω (Multiplicative.toAdd i)
    map_one' := by
      ext
      simp [mkSubgroupUnit, CosetFftDomainClass.ne_zero ω (0 : ι)]
    map_mul' := mkSubgroupUnit_mul ω
  }
  subgroupDomain_inj := fun x y h ↦ by
    have hinj := mkSubgroupUnit_injective ω
    have h' : mkSubgroupUnit ω (Multiplicative.toAdd x) =
              mkSubgroupUnit ω (Multiplicative.toAdd y) := h
    exact Multiplicative.toAdd.injective (hinj h')
  cosetGenerator := ⟨ω 0, (ω 0)⁻¹,
    mul_inv_cancel₀ (CosetFftDomainClass.ne_zero ω (0 : ι)),
    inv_mul_cancel₀ (CosetFftDomainClass.ne_zero ω (0 : ι))⟩

omit [DecidableEq ι] [DecidableEq F] [Fintype ι] in
lemma toCosetFftDomain_of_CosetFftDomain {ω : CosetFftDomain ι F} :
    toCosetFftDomain ω = ω := by
  simp only [toCosetFftDomain, CosetFftDomain.eq_iff_gen_and_domains_eq]
  constructor
  · have h : (0 : ι) = (Multiplicative.ofAdd 0 : Multiplicative ι) := by rfl
    aesop (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])
  · have h : (0 : ι) = (Multiplicative.ofAdd 0 : Multiplicative ι) := by rfl
    ext i
    aesop
      (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain, mkSubgroupUnit])

omit [DecidableEq ι] [DecidableEq F] [Fintype ι] in
lemma toCosetFftDomain_apply_self {ω : CosetFftDomain ι F} {i : ι} :
    toCosetFftDomain ω i = ω i := by
  rw [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain]
  aesop
    (add simp [toCosetFftDomain, mkSubgroupUnit])

end CosetFftDomainClass

instance {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F] :
  CoeOut D (ι ↪ F) where
  coe ω := ⟨ω, fun _ _ h ↦ CosetFftDomainClass.injective ω h⟩

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

set_option linter.unusedSectionVars false in
omit [DecidableEq ι] [DecidableEq F] [Fintype ι] in
@[ext]
theorem ext {ω₁ ω₂ : D} (h : ∀ i, ω₁ i = ω₂ i) : ω₁ = ω₂ := DFunLike.ext _ _ h

end CosetFftDomainClass

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma map_0_eq_coset_generator {ω : CosetFftDomain ι F} :
    ω 0 = ω.cosetGenerator := by
  simp [eval_coset_fft_domain_eq_eval_generator_mul_domain,
        show (0 : ι) = (1 : Multiplicative ι) by rfl]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma injective {ω : CosetFftDomain ι F} :
    Injective ω := CosetFftDomainClass.injective _

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma injOn {ω : CosetFftDomain ι F} {s : Set ι} :
    Set.InjOn ω s := fun _ _ _ _ h ↦ injective h

end CosetFftDomain

abbrev SmoothCosetFftDomain (n : ℕ) (F : Type) [Field F] : Type :=
  CosetFftDomain (Fin (2 ^ n)) F

namespace CosetFftDomainClass
def toFinset {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) : Finset F := Finset.image ω Finset.univ

omit [DecidableEq ι] in
@[simp]
lemma card_toFinset {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    {ω : D} :
  Finset.card (CosetFftDomainClass.toFinset ω) = Fintype.card ι := by
  aesop
    (add simp [CosetFftDomainClass.toFinset, Finset.card_image_of_injective,
                CosetFftDomainClass.injective])

end CosetFftDomainClass

namespace CosetFftDomain

abbrev toFinset (ω : CosetFftDomain ι F) : Finset F :=
  CosetFftDomainClass.toFinset ω

end CosetFftDomain

end Domain
