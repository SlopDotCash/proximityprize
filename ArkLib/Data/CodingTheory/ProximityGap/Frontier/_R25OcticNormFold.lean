/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24DBlockIndependence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25FractionRatio
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25QuarticAdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing

/-!
# LANE OCTICFOLD (#466): the first `d = 8` norm-fold brick

The proved `d = 4` norm-fold lane folds a four-block relation down to the two-block
Stepanov non-vanishing core.  The next doubling begins similarly.  For an octic element

`P + θQ`, where `P = A₀ + A₂t + A₄t² + A₆t³`, `Q = A₁ + A₃t + A₅t² + A₇t³`,
`t = θ²`, and `t⁴ = g(Y)/g(X)`, the relative norm is `P² - tQ²`.

Multiplying by `g(X)` and reducing powers of `t` modulo `t⁴ = g(Y)/g(X)` gives four
quartic norm blocks.  This file pins those blocks and proves their degree budget, which
is the input shape needed to feed the already-proven `dBlockIndependence_four`.

Current endpoint: the octic descent seam is now discharged from the weighted quartic norm
descent plus the two fraction-field ratio nonsquare facts, giving the public theorem
`dBlockIndependence_eight`.  The next norm-fold target is therefore `d = 16`, not `d = 8`.
-/

namespace ArkLib.ProximityGap.Frontier.R25OcticNormFold

open Polynomial
open ArkLib.ProximityGap.StepanovNonVanishing
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence
open ArkLib.ProximityGap.Frontier.R25FractionRatio
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot

variable {F : Type*} [Field F]

/-- Blocks of a sum with a common bound. -/
theorem blocks_add_le {A B : Polynomial (Polynomial F)} {a : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ a) (hB : ∀ j, (B.coeff j).natDegree ≤ a) :
    ∀ j, ((A + B).coeff j).natDegree ≤ a := by
  intro j
  rw [coeff_add]
  exact (natDegree_add_le _ _).trans (max_le (hA j) (hB j))

/-- Blocks of `2*A*B + 2*C*D`. -/
theorem blocks_two_mul_add_two_mul_le
    {A B C Dp : Polynomial (Polynomial F)} {D : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ D)
    (hB : ∀ j, (B.coeff j).natDegree ≤ D)
    (hC : ∀ j, (C.coeff j).natDegree ≤ D)
    (hD : ∀ j, (Dp.coeff j).natDegree ≤ D) :
    ∀ j, ((2 * A * B + 2 * C * Dp).coeff j).natDegree ≤ 2 * D :=
  blocks_add_le
    (by
      intro j
      have h := blocks_two_mul_mul_le hA hB j
      omega)
    (by
      intro j
      have h := blocks_two_mul_mul_le hC hD j
      omega)

/-- The first coefficient block of `g(X) * (P² - tQ²)` after reducing `t⁴ = g(Y)/g(X)`. -/
noncomputable def octicNormBlock0 (g : F[X]) (A : Fin 8 → Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  C g * (A 0) ^ 2
    + (g.map C) *
      (2 * (A 2) * (A 6) + (A 4) ^ 2
        - (2 * (A 1) * (A 7) + 2 * (A 3) * (A 5)))

/-- The second coefficient block of `g(X) * (P² - tQ²)` after reducing `t⁴ = g(Y)/g(X)`. -/
noncomputable def octicNormBlock1 (g : F[X]) (A : Fin 8 → Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  C g * (2 * (A 0) * (A 2) - (A 1) ^ 2)
    + (g.map C) *
      (2 * (A 4) * (A 6)
        - (2 * (A 3) * (A 7) + (A 5) ^ 2))

/-- The third coefficient block of `g(X) * (P² - tQ²)` after reducing `t⁴ = g(Y)/g(X)`. -/
noncomputable def octicNormBlock2 (g : F[X]) (A : Fin 8 → Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  C g * (2 * (A 0) * (A 4) + (A 2) ^ 2 - 2 * (A 1) * (A 3))
    + (g.map C) * ((A 6) ^ 2 - 2 * (A 5) * (A 7))

/-- The fourth coefficient block of `g(X) * (P² - tQ²)` after reducing `t⁴ = g(Y)/g(X)`. -/
noncomputable def octicNormBlock3 (g : F[X]) (A : Fin 8 → Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  C g *
    (2 * (A 0) * (A 6) + 2 * (A 2) * (A 4)
      - (2 * (A 1) * (A 5) + (A 3) ^ 2))
    - (g.map C) * (A 7) ^ 2

/-- The four octic norm blocks as a `Fin 4` family. -/
noncomputable def octicNormBlock (g : F[X]) (A : Fin 8 → Polynomial (Polynomial F)) :
    Fin 4 → Polynomial (Polynomial F)
  | ⟨0, _⟩ => octicNormBlock0 g A
  | ⟨1, _⟩ => octicNormBlock1 g A
  | ⟨2, _⟩ => octicNormBlock2 g A
  | ⟨3, _⟩ => octicNormBlock3 g A

/-- Every octic norm block has block degree at most `deg g + 2D` if every original
coefficient block has degree at most `D`. -/
theorem octicNormBlock_blocks_le (g : F[X]) (A : Fin 8 → Polynomial (Polynomial F))
    {D : ℕ} (hblk : ∀ i : Fin 8, ∀ k, ((A i).coeff k).natDegree ≤ D) :
    ∀ i : Fin 4, ∀ k, (((octicNormBlock g A i).coeff k).natDegree ≤ g.natDegree + 2 * D) := by
  classical
  have hsq : ∀ i : Fin 8, ∀ k, (((A i) ^ 2).coeff k).natDegree ≤ 2 * D := fun i =>
    blocks_pow_le (hblk i) 2
  have htwo : ∀ i j : Fin 8, ∀ k, ((2 * (A i) * (A j)).coeff k).natDegree ≤ 2 * D := by
    intro i j k
    have h := blocks_two_mul_mul_le (hblk i) (hblk j) k
    omega
  have h0inner :
      ∀ k, (((2 * (A 2) * (A 6) + (A 4) ^ 2
        - (2 * (A 1) * (A 7) + 2 * (A 3) * (A 5))).coeff k).natDegree ≤ 2 * D) :=
    blocks_sub_le
      (blocks_add_le (htwo 2 6) (hsq 4))
      (blocks_two_mul_add_two_mul_le (hblk 1) (hblk 7) (hblk 3) (hblk 5))
  have h1left : ∀ k, (((2 * (A 0) * (A 2) - (A 1) ^ 2).coeff k).natDegree ≤ 2 * D) :=
    blocks_sub_le (htwo 0 2) (hsq 1)
  have h1inner :
      ∀ k, (((2 * (A 4) * (A 6)
        - (2 * (A 3) * (A 7) + (A 5) ^ 2)).coeff k).natDegree ≤ 2 * D) :=
    blocks_sub_le (htwo 4 6) (blocks_add_le (htwo 3 7) (hsq 5))
  have h2left :
      ∀ k, (((2 * (A 0) * (A 4) + (A 2) ^ 2
        - 2 * (A 1) * (A 3)).coeff k).natDegree ≤ 2 * D) :=
    blocks_sub_le (blocks_add_le (htwo 0 4) (hsq 2)) (htwo 1 3)
  have h2inner : ∀ k, ((((A 6) ^ 2 - 2 * (A 5) * (A 7)).coeff k).natDegree ≤ 2 * D) :=
    blocks_sub_le (hsq 6) (htwo 5 7)
  have h3left :
      ∀ k, (((2 * (A 0) * (A 6) + 2 * (A 2) * (A 4)
        - (2 * (A 1) * (A 5) + (A 3) ^ 2)).coeff k).natDegree ≤ 2 * D) :=
    blocks_sub_le
      (blocks_two_mul_add_two_mul_le (hblk 0) (hblk 6) (hblk 2) (hblk 4))
      (blocks_add_le (htwo 1 5) (hsq 3))
  intro i k
  fin_cases i
  · change ((octicNormBlock0 g A).coeff k).natDegree ≤ g.natDegree + 2 * D
    rw [octicNormBlock0, coeff_add]
    have ht1 := blocks_C_mul_le g (hsq 0) k
    have ht2 := blocks_mapC_mul_le g h0inner k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  · change ((octicNormBlock1 g A).coeff k).natDegree ≤ g.natDegree + 2 * D
    rw [octicNormBlock1, coeff_add]
    have ht1 := blocks_C_mul_le g h1left k
    have ht2 := blocks_mapC_mul_le g h1inner k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  · change ((octicNormBlock2 g A).coeff k).natDegree ≤ g.natDegree + 2 * D
    rw [octicNormBlock2, coeff_add]
    have ht1 := blocks_C_mul_le g h2left k
    have ht2 := blocks_mapC_mul_le g h2inner k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  · change ((octicNormBlock3 g A).coeff k).natDegree ≤ g.natDegree + 2 * D
    rw [octicNormBlock3, coeff_sub]
    have ht1 := blocks_C_mul_le g h3left k
    have ht2 := blocks_mapC_mul_le g (hsq 7) k
    exact (natDegree_sub_le _ _).trans (max_le ht1 (by omega))

/-- The octic norm fold converts an 8-block relation with step `e = (q-1)/8` into a
4-block relation among the octic norm blocks with step `2e = (q-1)/4`.

This is the relation-algebra half of the `d = 8` norm-fold: the remaining missing piece is
the descent lemma that zero norm blocks force the original eight blocks to vanish. -/
theorem octicNormBlock_fold_relation [Fintype F]
    (g : F[X]) (A : Fin 8 → Polynomial (Polynomial F))
    {q e : ℕ} (hqcard : q = Fintype.card F) (hqe : q = 8 * e + 1)
    (hsum8 :
      subq q (A 0) + g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
        + g ^ (3 * e) * subq q (A 3) + g ^ (4 * e) * subq q (A 4)
        + g ^ (5 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 6)
        + g ^ (7 * e) * subq q (A 7) = 0) :
    subq q (octicNormBlock0 g A)
      + g ^ (2 * e) * subq q (octicNormBlock1 g A)
      + g ^ (4 * e) * subq q (octicNormBlock2 g A)
      + g ^ (6 * e) * subq q (octicNormBlock3 g A) = 0 := by
  subst q
  let q := Fintype.card F
  have hgq : subq q (g.map (C : F →+* F[X])) = g ^ q := (pow_card_eq_subq_map_C g).symm
  have hSB0 : subq q (octicNormBlock0 g A)
      = g * (subq q (A 0)) ^ 2
        + g ^ q *
          (2 * (subq q (A 2)) * (subq q (A 6)) + (subq q (A 4)) ^ 2
            - (2 * (subq q (A 1)) * (subq q (A 7))
              + 2 * (subq q (A 3)) * (subq q (A 5)))) := by
    rw [octicNormBlock0]
    change subqHom q _ = _
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, subqHom_apply, subq_C, hgq]
  have hSB1 : subq q (octicNormBlock1 g A)
      = g * (2 * (subq q (A 0)) * (subq q (A 2)) - (subq q (A 1)) ^ 2)
        + g ^ q *
          (2 * (subq q (A 4)) * (subq q (A 6))
            - (2 * (subq q (A 3)) * (subq q (A 7)) + (subq q (A 5)) ^ 2)) := by
    rw [octicNormBlock1]
    change subqHom q _ = _
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, subqHom_apply, subq_C, hgq]
  have hSB2 : subq q (octicNormBlock2 g A)
      = g * (2 * (subq q (A 0)) * (subq q (A 4)) + (subq q (A 2)) ^ 2
          - 2 * (subq q (A 1)) * (subq q (A 3)))
        + g ^ q * ((subq q (A 6)) ^ 2 - 2 * (subq q (A 5)) * (subq q (A 7))) := by
    rw [octicNormBlock2]
    change subqHom q _ = _
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, subqHom_apply, subq_C, hgq]
  have hSB3 : subq q (octicNormBlock3 g A)
      = g *
          (2 * (subq q (A 0)) * (subq q (A 6))
            + 2 * (subq q (A 2)) * (subq q (A 4))
            - (2 * (subq q (A 1)) * (subq q (A 5)) + (subq q (A 3)) ^ 2))
        - g ^ q * (subq q (A 7)) ^ 2 := by
    rw [octicNormBlock3]
    change subqHom q _ = _
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, subqHom_apply, subq_C, hgq]
  have hkey :
      (subq q (A 0) + g ^ (2 * e) * subq q (A 2) + g ^ (4 * e) * subq q (A 4)
          + g ^ (6 * e) * subq q (A 6)) ^ 2
        - g ^ (2 * e)
          * (subq q (A 1) + g ^ (2 * e) * subq q (A 3) + g ^ (4 * e) * subq q (A 5)
            + g ^ (6 * e) * subq q (A 7)) ^ 2 = 0 := by
    linear_combination
      (subq q (A 0) - g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
        - g ^ (3 * e) * subq q (A 3) + g ^ (4 * e) * subq q (A 4)
        - g ^ (5 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 6)
        - g ^ (7 * e) * subq q (A 7)) * hsum8
  have hgq8 : g ^ q = g ^ (8 * e + 1) := by
    simpa [q] using congrArg (fun n : ℕ => g ^ n) hqe
  rw [hSB0, hSB1, hSB2, hSB3, hgq8]
  linear_combination g * hkey

/-- The remaining octic descent brick: vanishing of the four norm blocks forces all
eight original blocks to vanish.  This is deliberately named as a single residual Prop so
the `d = 8` reduction below is auditable. -/
def OcticNormForcesTrivial (g : F[X]) : Prop :=
  ∀ A : Fin 8 → Polynomial (Polynomial F),
    octicNormBlock0 g A = 0 →
    octicNormBlock1 g A = 0 →
    octicNormBlock2 g A = 0 →
    octicNormBlock3 g A = 0 →
    ∀ i, A i = 0

/-- The fraction-field weighted quartic descent statement needed to discharge the octic norm
blocks.  This is the exact shape produced by `quartic_weighted_norm_descent_coeffs` together
with the ratio nonsquare lemmas in `r25_fraction_ratio_probe`: take
`G = g(X)`, `H = g(Y)`, and `K = Frac(F[X][Y])`. -/
def FractionFieldWeightedOcticDescent (g : F[X]) : Prop :=
  let R := Polynomial (Polynomial F)
  let K := FractionRing R
  let G : K := algebraMap R K (C g)
  let H : K := algebraMap R K (g.map (C : F →+* F[X]))
  G ≠ 0 →
    ∀ p0 p1 p2 p3 q0 q1 q2 q3 : K,
      G * p0 ^ 2 + H * (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2)) = 0 →
      G * (2 * p0 * p1 - q0 ^ 2)
        + H * (2 * p2 * p3 - (2 * q1 * q3 + q2 ^ 2)) = 0 →
      G * (2 * p0 * p2 + p1 ^ 2 - 2 * q0 * q1)
        + H * (p3 ^ 2 - 2 * q2 * q3) = 0 →
      G * (2 * p0 * p3 + 2 * p1 * p2 - (2 * q0 * q2 + q1 ^ 2))
        - H * q3 ^ 2 = 0 →
      p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 ∧
        q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0

/-- The reusable theorem shape supplied by the quartic AdjoinRoot probe. -/
def WeightedQuarticDescentStatement (K : Type*) [Field K] : Prop :=
  ∀ (G H : K), G ≠ 0 →
    ¬ IsSquare (H / G) → ¬ IsSquare (-(H / G)) →
    ∀ p0 p1 p2 p3 q0 q1 q2 q3 : K,
      G * p0 ^ 2 + H * (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2)) = 0 →
      G * (2 * p0 * p1 - q0 ^ 2)
        + H * (2 * p2 * p3 - (2 * q1 * q3 + q2 ^ 2)) = 0 →
      G * (2 * p0 * p2 + p1 ^ 2 - 2 * q0 * q1)
        + H * (p3 ^ 2 - 2 * q2 * q3) = 0 →
      G * (2 * p0 * p3 + 2 * p1 * p2 - (2 * q0 * q2 + q1 ^ 2))
        - H * q3 ^ 2 = 0 →
      p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 ∧
        q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0

/-- Substitution seam: the quartic weighted descent theorem plus the two ratio nonsquare
facts give the exact fraction-field descent interface needed by the octic norm fold. -/
theorem fractionFieldWeightedOcticDescent_of_weightedQuartic_and_ratioNonsquares
    (g : F[X])
    (hquartic :
      WeightedQuarticDescentStatement (FractionRing (Polynomial (Polynomial F))))
    (hratio :
      ¬ IsSquare
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g)))
    (hnegratio :
      ¬ IsSquare
        (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g)))) :
    FractionFieldWeightedOcticDescent g := by
  dsimp [FractionFieldWeightedOcticDescent]
  intro hG p0 p1 p2 p3 q0 q1 q2 q3 h0 h1 h2 h3
  exact hquartic _ _ hG hratio hnegratio
    p0 p1 p2 p3 q0 q1 q2 q3 h0 h1 h2 h3

theorem weightedQuarticDescentStatement_fractionRing
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))] :
    WeightedQuarticDescentStatement (FractionRing (Polynomial (Polynomial F))) := by
  intro G H hG hratio hnegratio p0 p1 p2 p3 q0 q1 q2 q3 h0 h1 h2 h3
  exact quartic_weighted_norm_descent_coeffs G H hG hratio hnegratio
    p0 p1 p2 p3 q0 q1 q2 q3 h0 h1 h2 h3

theorem fractionFieldWeightedOcticDescent_of_squarefree_natDegree_pos
    [PerfectField F]
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    {g : F[X]} (hg0 : g ≠ 0) (hgsqf : Squarefree g) (hgdeg : 0 < g.natDegree) :
    FractionFieldWeightedOcticDescent g := by
  classical
  exact fractionFieldWeightedOcticDescent_of_weightedQuartic_and_ratioNonsquares g
    weightedQuarticDescentStatement_fractionRing
    (ratio_not_square_of_squarefree_natDegree_pos hg0 hgsqf hgdeg)
    (neg_ratio_not_square_of_squarefree_natDegree_pos hg0 hgsqf hgdeg)

set_option maxHeartbeats 800000 in
-- This proof pushes the eight octic blocks through the fraction-field norm identity; the final
-- `simpa` steps are large enough that the default heartbeat budget is unreliable.
/-- Algebraic integration step for the octic descent: once the weighted quartic descent is
available over `Frac(F[X][Y])`, vanishing of the four octic norm blocks forces all eight
original blocks to vanish in `F[X][Y]`. -/
theorem octicNormForcesTrivial_of_fractionFieldWeightedOcticDescent
    (g : F[X]) (hg : g ≠ 0) (hdesc : FractionFieldWeightedOcticDescent g) :
    OcticNormForcesTrivial g := by
  classical
  intro A h0 h1 h2 h3 i
  let R := Polynomial (Polynomial F)
  let K := FractionRing R
  let ψ : R →+* K := algebraMap R K
  have hψinj : Function.Injective ψ := IsFractionRing.injective R K
  let G : K := ψ (C g)
  let H : K := ψ (g.map (C : F →+* F[X]))
  have hG0 : G ≠ 0 := by
    intro hG
    have hCg : (C g : R) = 0 := hψinj (hG.trans (map_zero ψ).symm)
    exact hg (C_eq_zero.mp hCg)
  have h0K :
      G * (ψ (A 0)) ^ 2
        + H * (2 * ψ (A 2) * ψ (A 6) + (ψ (A 4)) ^ 2
          - (2 * ψ (A 1) * ψ (A 7) + 2 * ψ (A 3) * ψ (A 5))) = 0 := by
    simpa [octicNormBlock0, G, H, ψ, R, K, map_add, map_mul, map_sub, map_pow, map_ofNat,
      mul_assoc] using congrArg ψ h0
  have h1K :
      G * (2 * ψ (A 0) * ψ (A 2) - (ψ (A 1)) ^ 2)
        + H * (2 * ψ (A 4) * ψ (A 6)
          - (2 * ψ (A 3) * ψ (A 7) + (ψ (A 5)) ^ 2)) = 0 := by
    simpa [octicNormBlock1, G, H, ψ, R, K, map_add, map_mul, map_sub, map_pow, map_ofNat,
      mul_assoc] using congrArg ψ h1
  have h2K :
      G * (2 * ψ (A 0) * ψ (A 4) + (ψ (A 2)) ^ 2 - 2 * ψ (A 1) * ψ (A 3))
        + H * ((ψ (A 6)) ^ 2 - 2 * ψ (A 5) * ψ (A 7)) = 0 := by
    simpa [octicNormBlock2, G, H, ψ, R, K, map_add, map_mul, map_sub, map_pow, map_ofNat,
      mul_assoc] using congrArg ψ h2
  have h3K :
      G * (2 * ψ (A 0) * ψ (A 6) + 2 * ψ (A 2) * ψ (A 4)
          - (2 * ψ (A 1) * ψ (A 5) + (ψ (A 3)) ^ 2))
        - H * (ψ (A 7)) ^ 2 = 0 := by
    simpa [octicNormBlock3, G, H, ψ, R, K, map_add, map_mul, map_sub, map_pow, map_ofNat,
      mul_assoc] using congrArg ψ h3
  have hz := hdesc hG0 (ψ (A 0)) (ψ (A 2)) (ψ (A 4)) (ψ (A 6))
    (ψ (A 1)) (ψ (A 3)) (ψ (A 5)) (ψ (A 7)) h0K h1K h2K h3K
  rcases hz with ⟨hA0, hA2, hA4, hA6, hA1, hA3, hA5, hA7⟩
  fin_cases i
  · exact hψinj (by simpa using hA0)
  · exact hψinj (by simpa using hA1)
  · exact hψinj (by simpa using hA2)
  · exact hψinj (by simpa using hA3)
  · exact hψinj (by simpa using hA4)
  · exact hψinj (by simpa using hA5)
  · exact hψinj (by simpa using hA6)
  · exact hψinj (by simpa using hA7)

/-- Fully composed octic descent seam, pending only the imported concrete proofs of the
weighted quartic theorem and the ratio nonsquare hypotheses. -/
theorem octicNormForcesTrivial_of_weightedQuartic_and_ratioNonsquares
    (g : F[X]) (hg : g ≠ 0)
    (hquartic :
      WeightedQuarticDescentStatement (FractionRing (Polynomial (Polynomial F))))
    (hratio :
      ¬ IsSquare
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g)))
    (hnegratio :
      ¬ IsSquare
        (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g)))) :
    OcticNormForcesTrivial g :=
  octicNormForcesTrivial_of_fractionFieldWeightedOcticDescent g hg
    (fractionFieldWeightedOcticDescent_of_weightedQuartic_and_ratioNonsquares
      g hquartic hratio hnegratio)

theorem octicNormForcesTrivial_of_squarefree_natDegree_pos
    [PerfectField F]
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    {g : F[X]} (hg0 : g ≠ 0) (hgsqf : Squarefree g) (hgdeg : 0 < g.natDegree) :
    OcticNormForcesTrivial g :=
  octicNormForcesTrivial_of_fractionFieldWeightedOcticDescent g hg0
    (fractionFieldWeightedOcticDescent_of_squarefree_natDegree_pos hg0 hgsqf hgdeg)

/-- If an 8-block relation has the explicit octic spacing `e = (q-1)/8`, then the proved
`d = 4` theorem kills the four octic norm blocks.  The only mathematical residual for a
full `d = 8` theorem is therefore the descent Prop `OcticNormForcesTrivial`. -/
theorem octicNormBlocks_zero_of_fold [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    {D e : ℕ} (hqe : Fintype.card F = 8 * e + 1)
    (hD : 8 * D + 7 * g.natDegree < Fintype.card F)
    (A : Fin 8 → Polynomial (Polynomial F))
    (hblk : ∀ i : Fin 8, ∀ k, ((A i).coeff k).natDegree ≤ D)
    (hsum8 :
      subq (Fintype.card F) (A 0) + g ^ e * subq (Fintype.card F) (A 1)
        + g ^ (2 * e) * subq (Fintype.card F) (A 2)
        + g ^ (3 * e) * subq (Fintype.card F) (A 3)
        + g ^ (4 * e) * subq (Fintype.card F) (A 4)
        + g ^ (5 * e) * subq (Fintype.card F) (A 5)
        + g ^ (6 * e) * subq (Fintype.card F) (A 6)
        + g ^ (7 * e) * subq (Fintype.card F) (A 7) = 0) :
    ∀ i : Fin 4, octicNormBlock g A i = 0 := by
  classical
  set q := Fintype.card F with hqdef
  have hq1 : 1 ≤ q := Fintype.card_pos
  have h4 : 4 ∣ Fintype.card F - 1 := by
    use 2 * e
    omega
  have h4step : (q - 1) / 4 = 2 * e := by
    omega
  have hbudget : 4 * (g.natDegree + 2 * D) + 3 * g.natDegree < Fintype.card F := by
    omega
  have hrel_explicit :
      subq (Fintype.card F) (octicNormBlock0 g A)
        + g ^ (2 * e) * subq (Fintype.card F) (octicNormBlock1 g A)
        + g ^ (4 * e) * subq (Fintype.card F) (octicNormBlock2 g A)
        + g ^ (6 * e) * subq (Fintype.card F) (octicNormBlock3 g A) = 0 :=
    octicNormBlock_fold_relation g A rfl hqe hsum8
  have hBrel :
      (∑ j : Fin 4,
          g ^ ((j : ℕ) * ((Fintype.card F - 1) / 4)) *
            subq (Fintype.card F) (octicNormBlock g A j)) = 0 := by
    rw [Fin.sum_univ_four]
    rw [show ((Fintype.card F - 1) / 4) = 2 * e by omega]
    simpa [octicNormBlock, pow_mul, mul_assoc, mul_comm, mul_left_comm] using hrel_explicit
  exact dBlockIndependence_four g hg hdeg hq_odd h4 hbudget
    (octicNormBlock g A) (octicNormBlock_blocks_le g A hblk) hBrel

/-- Conditional `d = 8` block independence from the explicit octic norm descent lemma.
This theorem is intentionally honest: it proves all relation algebra and degree accounting,
and isolates the remaining descent step as `OcticNormForcesTrivial`. -/
theorem dBlockIndependence_eight_of_octicNormForcesTrivial [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 8 * D + 7 * g.natDegree < Fintype.card F)
    (hdesc : OcticNormForcesTrivial g) :
    DBlockIndependence F 8 (Fintype.card F) D g := by
  classical
  intro A hblk hsum i
  set q := Fintype.card F with hqdef
  obtain ⟨e, he⟩ := h8
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hqe : Fintype.card F = 8 * e + 1 := by omega
  have h8step : (q - 1) / 8 = e := by omega
  have hsum8 :
      subq (Fintype.card F) (A 0) + g ^ e * subq (Fintype.card F) (A 1)
        + g ^ (2 * e) * subq (Fintype.card F) (A 2)
        + g ^ (3 * e) * subq (Fintype.card F) (A 3)
        + g ^ (4 * e) * subq (Fintype.card F) (A 4)
        + g ^ (5 * e) * subq (Fintype.card F) (A 5)
        + g ^ (6 * e) * subq (Fintype.card F) (A 6)
        + g ^ (7 * e) * subq (Fintype.card F) (A 7) = 0 := by
    have h := hsum
    rw [Fin.sum_univ_eight] at h
    rw [h8step] at h
    simpa [hqdef, pow_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have hBzero :=
    octicNormBlocks_zero_of_fold g hg hdeg hq_odd hqe hD A hblk hsum8
  have h0 : octicNormBlock0 g A = 0 := by simpa [octicNormBlock] using hBzero 0
  have h1 : octicNormBlock1 g A = 0 := by simpa [octicNormBlock] using hBzero 1
  have h2 : octicNormBlock2 g A = 0 := by simpa [octicNormBlock] using hBzero 2
  have h3 : octicNormBlock3 g A = 0 := by simpa [octicNormBlock] using hBzero 3
  exact hdesc A h0 h1 h2 h3 i

/-- Fully composed `d = 8` block independence over finite fields, with the octic descent
discharged from squarefreeness and positive degree of `g`.

This is the current R25 endpoint: the relation folding, the quartic weighted norm descent, and
the two fraction-field ratio nonsquare facts are all composed into the public
`DBlockIndependence` statement. -/
theorem dBlockIndependence_eight [Fintype F]
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 8 * D + 7 * g.natDegree < Fintype.card F) :
    DBlockIndependence F 8 (Fintype.card F) D g := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hdeg
  exact dBlockIndependence_eight_of_octicNormForcesTrivial g hg hdeg hq_odd h8 hD
    (octicNormForcesTrivial_of_squarefree_natDegree_pos hg0 hg hdeg)

end ArkLib.ProximityGap.Frontier.R25OcticNormFold

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms octicNormBlock_blocks_le
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms octicNormBlock_fold_relation
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms fractionFieldWeightedOcticDescent_of_weightedQuartic_and_ratioNonsquares
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms octicNormForcesTrivial_of_fractionFieldWeightedOcticDescent
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms octicNormForcesTrivial_of_weightedQuartic_and_ratioNonsquares
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms octicNormBlocks_zero_of_fold
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms dBlockIndependence_eight_of_octicNormForcesTrivial
open ArkLib.ProximityGap.Frontier.R25OcticNormFold in
#print axioms dBlockIndependence_eight
