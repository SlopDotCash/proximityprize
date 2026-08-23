/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R390CharZeroNonzeroRepFourBound

/-!
# R391: toric normalization of a nonzero four-sum fiber

Dividing a four-tuple by its last coordinate removes the dilation degree of freedom.  On a
nonzero fiber this normalization is injective.  For `n`-th roots it lands on the three-dimensional
torsion surface

`(1 + y₀ + y₁ + y₂)^n = c^n`.

This is the geometric form needed to separate the positive-dimensional antipodal components from
the generic zero-dimensional remainder in finite characteristic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Finset

namespace ArkLib.ProximityGap.Frontier.R391FourFiberToricNormalization

variable {F : Type*} [Field F] [DecidableEq F]

/-- Divide the first three coordinates by the fourth. -/
def normalizeFour (a : Fin 4 → F) : Fin 3 → F := fun i =>
  a i.castSucc / a (Fin.last 3)

/-- The affine base appearing after normalization. -/
def affineBase (y : Fin 3 → F) : F := 1 + ∑ i, y i

/-- The normalized torsion surface attached to the target `c`. -/
def OnToricSurface (n : ℕ) (c : F) (y : Fin 3 → F) : Prop :=
  (∀ i, (y i) ^ n = 1) ∧ (affineBase y) ^ n = c ^ n

/-- Reconstruct a four-tuple from normalized coordinates. -/
def reconstructFour (c : F) (y : Fin 3 → F) : Fin 4 → F :=
  Fin.lastCases (c / affineBase y) (fun i => (c / affineBase y) * y i)

/-- Splitting a four-term sum into its first three terms and its last term. -/
theorem sum_four_eq_firstThree_add_last (a : Fin 4 → F) :
    ∑ i, a i = (∑ i : Fin 3, a i.castSucc) + a (Fin.last 3) := by
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  rfl

/-- A nonzero four-sum fiber contains no zero coordinate when all coordinates are roots of unity. -/
theorem coord_ne_zero_of_pow_eq_one
    {n : ℕ} (hn : 0 < n) {a : Fin 4 → F} (ha : ∀ i, (a i) ^ n = 1) (i : Fin 4) : a i ≠ 0 := by
  intro hi
  have hai := ha i
  rw [hi] at hai
  simpa [zero_pow (Nat.ne_of_gt hn)] using hai

/-- The original sum factors as the last coordinate times the normalized affine base. -/
theorem sum_eq_last_mul_affineBase
    {n : ℕ} (hn : 0 < n) (a : Fin 4 → F) (ha : ∀ i, (a i) ^ n = 1) :
    ∑ i, a i = a (Fin.last 3) * affineBase (normalizeFour a) := by
  have hlast := coord_ne_zero_of_pow_eq_one hn ha (Fin.last 3)
  rw [sum_four_eq_firstThree_add_last]
  simp only [affineBase, normalizeFour]
  rw [mul_add, mul_one]
  rw [Finset.mul_sum]
  have hterm : ∀ i : Fin 3,
      a (Fin.last 3) * (a i.castSucc / a (Fin.last 3)) = a i.castSucc := by
    intro i
    field_simp
  simp_rw [hterm]
  ring

/-- **Normalization is injective on a fixed nonzero root fiber.** -/
theorem normalizeFour_injective_on_fiber
    {n : ℕ} (hn : 0 < n) {c : F} (hc : c ≠ 0) {a b : Fin 4 → F}
    (haRoot : ∀ i, (a i) ^ n = 1) (hbRoot : ∀ i, (b i) ^ n = 1)
    (haSum : ∑ i, a i = c) (hbSum : ∑ i, b i = c)
    (hnorm : normalizeFour a = normalizeFour b) : a = b := by
  have haFact := sum_eq_last_mul_affineBase hn a haRoot
  have hbFact := sum_eq_last_mul_affineBase hn b hbRoot
  rw [haSum, hnorm] at haFact
  rw [hbSum] at hbFact
  have hbase : affineBase (normalizeFour b) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hbFact
    exact hc hbFact
  have hlast : a (Fin.last 3) = b (Fin.last 3) := by
    apply mul_right_cancel₀ hbase
    exact haFact.symm.trans hbFact
  funext i
  refine Fin.lastCases hlast (fun j => ?_) i
  have h := congrFun hnorm j
  rw [normalizeFour, normalizeFour, hlast] at h
  have hb0 := coord_ne_zero_of_pow_eq_one hn hbRoot (Fin.last 3)
  calc
    a j.castSucc = (a j.castSucc / b (Fin.last 3)) * b (Fin.last 3) := by field_simp
    _ = (b j.castSucc / b (Fin.last 3)) * b (Fin.last 3) := by rw [h]
    _ = b j.castSucc := by field_simp

/-- Normalized root coordinates remain `n`-th roots. -/
theorem normalizeFour_pow_eq_one
    {n : ℕ} (hn : 0 < n) {a : Fin 4 → F} (ha : ∀ i, (a i) ^ n = 1) (j : Fin 3) :
    (normalizeFour a j) ^ n = 1 := by
  rw [normalizeFour, div_pow, ha, ha]
  simp

/-- **Forward toric-surface equation.** Every nonzero four-fiber point normalizes to
`(1 + y₀ + y₁ + y₂)^n = c^n`. -/
theorem normalizeFour_affineBase_pow
    {n : ℕ} (hn : 0 < n) {c : F} {a : Fin 4 → F}
    (haRoot : ∀ i, (a i) ^ n = 1) (haSum : ∑ i, a i = c) :
    (affineBase (normalizeFour a)) ^ n = c ^ n := by
  have hlast := coord_ne_zero_of_pow_eq_one hn haRoot (Fin.last 3)
  have hfact := sum_eq_last_mul_affineBase hn a haRoot
  rw [haSum] at hfact
  rw [hfact, mul_pow, haRoot]
  simp

/-- A toric-surface point has nonzero affine base when `c` is nonzero. -/
theorem affineBase_ne_zero_of_onToricSurface
    {n : ℕ} (hn : 0 < n) {c : F} (hc : c ≠ 0) {y : Fin 3 → F} (hy : OnToricSurface n c y) :
    affineBase y ≠ 0 := by
  intro hzero
  unfold OnToricSurface at hy
  rw [hzero] at hy
  have : c ^ n = 0 := by simpa [zero_pow (Nat.ne_of_gt hn)] using hy.2.symm
  exact hc (eq_zero_of_pow_eq_zero this)

/-- The reconstructed scale is itself an `n`-th root. -/
theorem reconstructScale_pow_eq_one
    {n : ℕ} (hn : 0 < n) {c : F} (hc : c ≠ 0) {y : Fin 3 → F} (hy : OnToricSurface n c y) :
    (c / affineBase y) ^ n = 1 := by
  rw [div_pow, hy.2]
  exact div_self (pow_ne_zero n hc)

/-- Reconstruction lands in the `n`-th roots coordinatewise. -/
theorem reconstructFour_pow_eq_one
    {n : ℕ} (hn : 0 < n) {c : F} (hc : c ≠ 0) {y : Fin 3 → F} (hy : OnToricSurface n c y) :
    ∀ i, (reconstructFour c y i) ^ n = 1 := by
  refine Fin.lastCases ?_ (fun i => ?_)
  · exact reconstructScale_pow_eq_one hn hc hy
  · simp only [reconstructFour, Fin.lastCases_castSucc]
    rw [mul_pow, reconstructScale_pow_eq_one hn hc hy, hy.1]
    simp

/-- Reconstruction has the prescribed four-sum. -/
theorem reconstructFour_sum
    {n : ℕ} (hn : 0 < n) {c : F} (hc : c ≠ 0) {y : Fin 3 → F} (hy : OnToricSurface n c y) :
    ∑ i, reconstructFour c y i = c := by
  rw [sum_four_eq_firstThree_add_last]
  simp only [reconstructFour, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [← Finset.mul_sum]
  unfold affineBase
  have hbase := affineBase_ne_zero_of_onToricSurface hn hc hy
  field_simp
  have hb : 1 + ∑ i, y i ≠ 0 := by simpa [affineBase] using hbase
  rw [add_comm (∑ i, y i) 1, div_self hb]

/-- Normalizing the reconstruction returns the original surface point. -/
theorem normalizeFour_reconstructFour
    {n : ℕ} (hn : 0 < n) {c : F} (hc : c ≠ 0) {y : Fin 3 → F} (hy : OnToricSurface n c y) :
    normalizeFour (reconstructFour c y) = y := by
  funext i
  simp only [normalizeFour, reconstructFour, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hbase := affineBase_ne_zero_of_onToricSurface hn hc hy
  have hscale : c / affineBase y ≠ 0 := div_ne_zero hc hbase
  field_simp

/-- **Exact normalized correspondence.** Root tuples in a fixed nonzero four-fiber and points of
the normalized toric surface are inverse under `normalizeFour` and `reconstructFour`. -/
theorem normalizeFour_onToricSurface
    {n : ℕ} (hn : 0 < n) {c : F} {a : Fin 4 → F}
    (haRoot : ∀ i, (a i) ^ n = 1) (haSum : ∑ i, a i = c) :
    OnToricSurface n c (normalizeFour a) := by
  exact ⟨normalizeFour_pow_eq_one hn haRoot,
    normalizeFour_affineBase_pow hn haRoot haSum⟩

end ArkLib.ProximityGap.Frontier.R391FourFiberToricNormalization

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R391FourFiberToricNormalization.normalizeFour_injective_on_fiber
#print axioms
  ArkLib.ProximityGap.Frontier.R391FourFiberToricNormalization.normalizeFour_affineBase_pow
#print axioms
  ArkLib.ProximityGap.Frontier.R391FourFiberToricNormalization.reconstructFour_sum
#print axioms
  ArkLib.ProximityGap.Frontier.R391FourFiberToricNormalization.normalizeFour_reconstructFour
