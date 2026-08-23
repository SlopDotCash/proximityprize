/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepStratumRankUnconditional
import ArkLib.Data.CodingTheory.ProximityGap.DeepStratumMovingDirection

/-!
# Discharging `SurvivingTPrimeCoord` unconditionally (#389, route 2)

This file assembles the moving direction (`DeepStratumMovingDirection`) with the
`T`-band surjectivity (`tband_surjective`) to prove `SurvivingTPrimeCoord`
**unconditionally** on the deep stratum.  Consequently `deep_pair_rank_ge_m_succ`
holds with no extra hypothesis: the deep-stratum pair-coherence rank is `≥ m+1`
for *every* deep pair.

The argument is pure linearity over the generator coefficient space.  Write `c₀`
for the coefficients of `Z_T = ∏_{i∈T}(X − dom i)`.  Then `genPoly c₀ = Z_T`
(degree `k+m+1 < M`), so its `T`-band is zero (`interp_T_vanishPoly_eq_zero`)
while its `T'`-coordinate `d` is the nonzero leading coefficient of the
`T'`-interpolant (`exists_surviving_band_coord`).  For any target `t`, use
`tband_surjective` to fix the `T`-band, then add the right scalar multiple of `c₀`
to hit the `T'`-coordinate — the `T`-band is unchanged (`c₀` has zero `T`-band).

Honest scope: route-2 *rank* residual on the deep stratum; the route-2 *list*
input (the sub-Johnson list-size wall) is the recognized open core, untouched.
-/

open Finset Polynomial

namespace ProximityGap.DeepStratumSurviving

open ProximityGap ProximityGap.PairRank ProximityGap.Ownership
open ProximityGap.DeepStratumUncond ProximityGap.DeepStratumMoving

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Linearity of `c ↦ coreInterp dom T (genPoly c)` -/

theorem genPoly_add {M : ℕ} (x y : Fin M → F) :
    genPoly (x + y) = genPoly x + genPoly y := by
  rw [genPoly, genPoly, genPoly, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show C (x j + y j) * X ^ (j : ℕ) = C (x j) * X ^ (j : ℕ) + C (y j) * X ^ (j : ℕ)
  rw [C_add]; ring

theorem genPoly_smul {M : ℕ} (s : F) (x : Fin M → F) :
    genPoly (s • x) = C s * genPoly x := by
  rw [genPoly, genPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show C ((s • x) j) * X ^ (j : ℕ) = C s * (C (x j) * X ^ (j : ℕ))
  rw [Pi.smul_apply, smul_eq_mul, C_mul]; ring

theorem coreInterp_genPoly_add (dom : Fin n ↪ F) (T : Finset (Fin n))
    {M : ℕ} (x y : Fin M → F) :
    coreInterp dom T (genPoly (x + y))
      = coreInterp dom T (genPoly x) + coreInterp dom T (genPoly y) := by
  rw [coreInterp, coreInterp, coreInterp, genPoly_add]
  have hvals : (fun i => (genPoly x + genPoly y).eval (dom i))
      = (fun i => (genPoly x).eval (dom i)) + (fun i => (genPoly y).eval (dom i)) := by
    funext i; simp [eval_add]
  rw [hvals, map_add]

theorem coreInterp_genPoly_smul (dom : Fin n ↪ F) (T : Finset (Fin n))
    {M : ℕ} (s : F) (x : Fin M → F) :
    coreInterp dom T (genPoly (s • x)) = s • coreInterp dom T (genPoly x) := by
  rw [coreInterp, coreInterp, genPoly_smul]
  have hvals : (fun i => (C s * genPoly x).eval (dom i))
      = s • (fun i => (genPoly x).eval (dom i)) := by
    funext i; simp [eval_mul, eval_C, smul_eq_mul]
  rw [hvals, map_smul]

/-! ## The moving direction as a generator -/

/-- The coefficient vector of `Z_T` (the moving generator). -/
noncomputable def movingGen (dom : Fin n ↪ F) (T : Finset (Fin n)) (M : ℕ) :
    Fin M → F := fun j => (vanishPoly dom T).coeff (j : ℕ)

theorem vanishPoly_ne_zero (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    vanishPoly dom T ≠ 0 := by
  rw [vanishPoly, Finset.prod_ne_zero_iff]
  exact fun i _ => Polynomial.X_sub_C_ne_zero (dom i)

/-- `genPoly (movingGen) = Z_T` when `M > k+m+1` (degree fits). -/
theorem genPoly_movingGen (dom : Fin n ↪ F) {k m : ℕ} (T : Finset (Fin n))
    (hT : T.card = k + m + 1) {M : ℕ} (hM : k + m + 1 < M) :
    genPoly (movingGen dom T M) = vanishPoly dom T := by
  refine genPoly_coeff_eq ?_
  have h1 : (vanishPoly dom T).natDegree = k + m + 1 := by
    rw [vanishPoly_natDegree, hT]
  rw [Polynomial.degree_eq_natDegree (vanishPoly_ne_zero dom T), h1]
  exact_mod_cast hM

/-- The `T`-band of the moving generator is zero. -/
theorem coreInterp_T_movingGen_eq_zero (dom : Fin n ↪ F) {k m : ℕ} (T : Finset (Fin n))
    (hT : T.card = k + m + 1) {M : ℕ} (hM : k + m + 1 < M) :
    coreInterp dom T (genPoly (movingGen dom T M)) = 0 := by
  rw [genPoly_movingGen dom T hT hM]
  exact interp_T_vanishPoly_eq_zero dom T

/-- The `T'`-interpolant of the moving generator is the moving interpolant. -/
theorem coreInterp_Tp_movingGen (dom : Fin n ↪ F) {k m : ℕ} (T T' : Finset (Fin n))
    (hT : T.card = k + m + 1) {M : ℕ} (hM : k + m + 1 < M) :
    coreInterp dom T' (genPoly (movingGen dom T M)) = movingInterp dom T T' := by
  rw [genPoly_movingGen dom T hT hM]
  rfl

open Classical in
/-- **`SurvivingTPrimeCoord` holds UNCONDITIONALLY on the deep stratum.**  For deep
pairs (`|T| = |T'| = k+m+1`, `k+1 ≤ |T∩T'| ≤ k+m`) and `M > k+m+1`, there is a
`T'`-band coordinate `d` jointly surjective with the whole `T`-band: combine
`tband_surjective` (fix the `T`-band) with the moving direction `Z_T` (whose
`T`-band is zero and whose coordinate `d` is nonzero), scaled to hit the target. -/
theorem surviving_tprime_coord (dom : Fin n ↪ F) {k m : ℕ} (T T' : Finset (Fin n))
    (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hlo : k + 1 ≤ (T ∩ T').card) (hhi : (T ∩ T').card ≤ k + m)
    {M : ℕ} (hM : k + m + 1 < M) :
    SurvivingTPrimeCoord dom k m T T' M := by
  -- a node `p ∈ T' \ T`
  have hne : (T' \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have heq : T ∩ T' = T' := Finset.inter_eq_right.mpr hsub
    rw [heq, hT'] at hhi; omega
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_sdiff] at hp
  obtain ⟨hpT', hpT⟩ := hp
  -- the surviving coordinate
  obtain ⟨d, hd⟩ := exists_surviving_band_coord dom T T' hT' hlo hpT' hpT
  set c₀ : Fin M → F := movingGen dom T M with hc₀
  set w : F := (movingInterp dom T T').coeff (k + 1 + (d : ℕ)) with hw
  have hwne : w ≠ 0 := hd
  refine ⟨d, fun t => ?_⟩
  -- the `T`-band generator
  obtain ⟨c₁, hc₁⟩ := tband_surjective dom hT (le_of_lt hM) (fun j => t (Sum.inl j))
  set v : F := (coreInterp dom T' (genPoly c₁)).coeff (k + 1 + (d : ℕ)) with hv
  set s : F := (t (Sum.inr ()) - v) / w with hs
  refine ⟨c₁ + s • c₀, ?_, ?_⟩
  · -- the `T`-band is unchanged (`c₀` has zero `T`-band)
    intro j
    rw [coreInterp_genPoly_add, coreInterp_genPoly_smul,
      coreInterp_T_movingGen_eq_zero dom T hT hM]
    simp only [smul_zero, add_zero, Polynomial.coeff_add]
    rw [hc₁ j]
  · -- the `T'`-coordinate hits the target
    rw [coreInterp_genPoly_add, coreInterp_genPoly_smul,
      coreInterp_Tp_movingGen dom T T' hT hM]
    rw [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul, ← hv, ← hw, hs]
    field_simp
    ring

open Classical in
/-- **The deep-stratum rank `≥ m+1` is UNCONDITIONAL.**  Discharging
`SurvivingTPrimeCoord` via `surviving_tprime_coord`, the deep pair-coherence kernel
obeys `#kernel · q^(m+1) ≤ q^M` for every deep pair — no hypothesis. -/
theorem deep_pair_rank_ge_m_succ_uncond (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hlo : k + 1 ≤ (T ∩ T').card) (hhi : (T ∩ T').card ≤ k + m)
    {M : ℕ} (hM : k + m + 1 < M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (m + 1) ≤ (Fintype.card F) ^ M :=
  deep_pair_rank_ge_m_succ dom hT hT' hlo
    (surviving_tprime_coord dom T T' hT hT' hlo hhi hM)

end ProximityGap.DeepStratumSurviving

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DeepStratumSurviving.surviving_tprime_coord
#print axioms ProximityGap.DeepStratumSurviving.deep_pair_rank_ge_m_succ_uncond
