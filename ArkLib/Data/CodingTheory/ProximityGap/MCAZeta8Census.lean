/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeta8Bridge

/-!
# The `n = 8` census computation (#357 round 12): integer arithmetic for `ℤ[ζ₈]`

Concrete integer model of `ℤ[ζ₈]` (coordinates in the power basis `1, ζ, ζ², ζ³`, with
multiplication reduced by `ζ⁴ = −1`), the evaluation homomorphism into any field with a
primitive 8th root, and the **collinearity determinant as an integer vector**
(`detVec`): by the coordinate bridge, a `μ₈` pair-triangle is collinear in some/every
char-0 field iff `detVec = 0` — a decidable integer statement. The census classification
itself (`detVec = 0 ↔ horizontal ∨ vertical ∨ slanted`) is the round-12(c) decide.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeta8Census

open ProximityGap.MCAZeta8Bridge

/-- Integer coordinates in the power basis of `ℤ[ζ₈]`. -/
structure Z8 where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
deriving DecidableEq, Repr

namespace Z8

def add (x y : Z8) : Z8 := ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩

def sub (x y : Z8) : Z8 := ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2, x.c3 - y.c3⟩

/-- Multiplication with the reduction `ζ⁴ = −1`. -/
def mul (x y : Z8) : Z8 :=
  ⟨x.c0 * y.c0 - x.c1 * y.c3 - x.c2 * y.c2 - x.c3 * y.c1,
   x.c0 * y.c1 + x.c1 * y.c0 - x.c2 * y.c3 - x.c3 * y.c2,
   x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 - x.c3 * y.c3,
   x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0⟩

def zero : Z8 := ⟨0, 0, 0, 0⟩

/-- The basis power `ζ^t` as a coordinate vector (period 8, sign at the half). -/
def zpow (t : ℕ) : Z8 :=
  match t % 8 with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩
  | 4 => ⟨-1, 0, 0, 0⟩
  | 5 => ⟨0, -1, 0, 0⟩
  | 6 => ⟨0, 0, -1, 0⟩
  | _ => ⟨0, 0, 0, -1⟩

end Z8

section Phi

variable {L : Type*} [Field L]

/-- Evaluation of a coordinate vector at `ζ`. -/
def phi (ζ : L) (x : Z8) : L :=
  (x.c0 : L) + (x.c1 : L) * ζ + (x.c2 : L) * ζ ^ 2 + (x.c3 : L) * ζ ^ 3

theorem phi_add (ζ : L) (x y : Z8) :
    phi ζ (Z8.add x y) = phi ζ x + phi ζ y := by
  simp only [phi, Z8.add]
  push_cast
  ring

theorem phi_sub (ζ : L) (x y : Z8) :
    phi ζ (Z8.sub x y) = phi ζ x - phi ζ y := by
  simp only [phi, Z8.sub]
  push_cast
  ring

theorem phi_mul {ζ : L} (hζ4 : ζ ^ 4 = -1) (x y : Z8) :
    phi ζ (Z8.mul x y) = phi ζ x * phi ζ y := by
  have h5 : ζ ^ 5 = -ζ := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, hζ4]
    ring
  have h6 : ζ ^ 6 = -(ζ ^ 2) := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, hζ4]
    ring
  simp only [phi, Z8.mul]
  push_cast
  linear_combination (-((x.c1 : L) * y.c3 + (x.c2 : L) * y.c2 + (x.c3 : L) * y.c1)) * hζ4
    + (-((x.c2 : L) * y.c3 + (x.c3 : L) * y.c2)) * h5 + (-((x.c3 : L) * y.c3)) * h6

/-- `φ(ζ^t-vector) = ζ^t` for a primitive 8th root. -/
theorem phi_zpow {ζ : L} (hζ : IsPrimitiveRoot ζ 8) (t : ℕ) :
    phi ζ (Z8.zpow t) = ζ ^ t := by
  have hζ8 : ζ ^ 8 = 1 := hζ.pow_eq_one
  have hred : ζ ^ t = ζ ^ (t % 8) := by
    conv_lhs => rw [← Nat.div_add_mod t 8]
    rw [pow_add, pow_mul, hζ8, one_pow, one_mul]
  have hζ4 : ζ ^ 4 = -1 := by
    have hsq : (ζ ^ 4) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
      exact hζ8
    have hne : ζ ^ 4 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hfac : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h) hne
    · linear_combination h
  have h5 : ζ ^ 5 = -ζ := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, hζ4]
    ring
  have h6 : ζ ^ 6 = -(ζ ^ 2) := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, hζ4]
    ring
  have h7 : ζ ^ 7 = -(ζ ^ 3) := by
    rw [show (7 : ℕ) = 4 + 3 from rfl, pow_add, hζ4]
    ring
  rw [hred, Z8.zpow]
  have hm : t % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases h : t % 8 <;> simp [phi, hζ4, h5, h6, h7]

end Phi

/-! ## The determinant vector -/

/-- The pair invariants as coordinate vectors. -/
def eVec (i j : ℕ) : Z8 := Z8.add (Z8.zpow i) (Z8.zpow j)

def mVec (i j : ℕ) : Z8 := Z8.zpow (i + j)

/-- The collinearity determinant of the pair-triangle `(P, Q, R)` as an integer
coordinate vector. -/
def detVec (p p' q q' r r' : ℕ) : Z8 :=
  Z8.sub
    (Z8.mul (Z8.sub (eVec q q') (eVec p p')) (Z8.sub (mVec r r') (mVec p p')))
    (Z8.mul (Z8.sub (mVec q q') (mVec p p')) (Z8.sub (eVec r r') (eVec p p')))

section BridgeGeneral

variable {L : Type*} [Field L]

/-- **The determinant bridge.** The field-level collinearity determinant of a `μ₈`
pair-triangle equals the evaluation of its integer vector. -/
theorem det_eq_phi {ζ : L} (hζ : IsPrimitiveRoot ζ 8) (p p' q q' r r' : ℕ) :
    ((ζ ^ q + ζ ^ q') - (ζ ^ p + ζ ^ p')) * (ζ ^ (r + r') - ζ ^ (p + p'))
      - (ζ ^ (q + q') - ζ ^ (p + p')) * ((ζ ^ r + ζ ^ r') - (ζ ^ p + ζ ^ p'))
    = phi ζ (detVec p p' q q' r r') := by
  have hζ4 : ζ ^ 4 = -1 := by
    have h := phi_zpow hζ 4
    simpa [Z8.zpow, phi] using h.symm
  rw [detVec, phi_sub, phi_mul hζ4, phi_mul hζ4, phi_sub, phi_sub, phi_sub, phi_sub]
  unfold eVec mVec
  rw [phi_add, phi_add, phi_add]
  rw [phi_zpow hζ, phi_zpow hζ, phi_zpow hζ, phi_zpow hζ, phi_zpow hζ, phi_zpow hζ,
    phi_zpow hζ, phi_zpow hζ, phi_zpow hζ]

end BridgeGeneral

section Bridge

variable {L : Type*} [Field L] [CharZero L]

/-- **Census decidability.** A `μ₈` pair-triangle is collinear in a char-0 field iff its
integer determinant vector vanishes — the census is a finite integer computation. -/
theorem collinear_iff_detVec_eq_zero {ζ : L} (hζ : IsPrimitiveRoot ζ 8)
    (p p' q q' r r' : ℕ) :
    (((ζ ^ q + ζ ^ q') - (ζ ^ p + ζ ^ p')) * (ζ ^ (r + r') - ζ ^ (p + p'))
      - (ζ ^ (q + q') - ζ ^ (p + p')) * ((ζ ^ r + ζ ^ r') - (ζ ^ p + ζ ^ p')) = 0)
    ↔ detVec p p' q q' r r' = Z8.zero := by
  rw [det_eq_phi hζ]
  constructor
  · intro h
    have hlin := zeta8_linear_independence hζ (c₀ := (detVec p p' q q' r r').c0)
      (c₁ := (detVec p p' q q' r r').c1) (c₂ := (detVec p p' q q' r r').c2)
      (c₃ := (detVec p p' q q' r r').c3) (by
        rw [← h]
        rfl)
    obtain ⟨h0, h1, h2, h3⟩ := hlin
    show detVec p p' q q' r r' = ⟨0, 0, 0, 0⟩
    cases hdv : detVec p p' q q' r r'
    rw [hdv] at h0 h1 h2 h3
    simp_all [Z8.zero]
  · intro h
    rw [h]
    simp [phi, Z8.zero]

end Bridge

/-! ## Source audit -/

#print axioms phi_mul
#print axioms phi_zpow
#print axioms det_eq_phi
#print axioms collinear_iff_detVec_eq_zero

end ProximityGap.MCAZeta8Census
