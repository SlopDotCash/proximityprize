/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS2PatternAnnihilatorResultant
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# LANE FS16 (#466, Fable session 2026-07-09): THE SHARP ARCHIMEDEAN RESULTANT ENVELOPE —
  `|Res(x^m+1, g)| ≤ (Σ|coeffs g|)^m`, discharging the `WraparoundExactCount` envelope shape

The #464 lane `WraparoundExactCount` recorded the per-config resultant envelope
`(2r)^{n/2}` only as an ABSTRACT SHAPE ("we record only the shape of this envelope as a
number").  This brick proves it: over `ℂ` the roots of `x^m + 1` have unit modulus, so by
`resultant_eq_prod_eval` (monic, splits, `lc = 1`)

  `|patternResultant m g| = ∏_{ω^m = −1} |g(ω)| ≤ (Σᵢ |gᵢ|)^m`  (`coeffMass g`),

i.e. for depth-`r` patterns (`coeffMass ≤ 2r`) the envelope `(2r)^{n/2}` is a THEOREM
(`patternResultant_natAbs_le_pow`).  This sharpens FS3's factorial/Hadamard height
`(m+d)!·B^{m+d} ≈ 2^{Θ(n log n)}` to `2^{Θ(n log r)}` — a `log n / log r` factor in every
FS-ledger budget — and pins where the good-prime route is Paley-independent exactly as the
envelope's docstring predicted (fixed `r`: finite; `r ≈ ln q`: `2^{Θ(n log log q)}`).

Issue #466, lane FS16.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.FS16SharpResultantEnvelope

open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant

/-- The ℓ¹ coefficient mass of an integer polynomial. -/
noncomputable def coeffMass (g : ℤ[X]) : ℕ := ∑ i ∈ g.support, (g.coeff i).natAbs

/-- Evaluation at a unit-modulus point is bounded by the coefficient mass. -/
theorem norm_eval_le_coeffMass (g : ℤ[X]) {ω : ℂ} (hω : ‖ω‖ = 1) :
    ‖aeval ω g‖ ≤ (coeffMass g : ℝ) := by
  rw [aeval_def, eval₂_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (g.natDegree + 1), (algebraMap ℤ ℂ) (g.coeff i) * ω ^ i‖
      ≤ ∑ i ∈ Finset.range (g.natDegree + 1), ‖(algebraMap ℤ ℂ) (g.coeff i) * ω ^ i‖ :=
        norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (g.natDegree + 1), ((g.coeff i).natAbs : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_mul, norm_pow, hω, one_pow, mul_one]
        simp only [algebraMap_int_eq, eq_intCast, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
    _ = (coeffMass g : ℝ) := by
        rw [coeffMass, Nat.cast_sum]
        symm
        refine Finset.sum_subset (Polynomial.supp_subset_range_natDegree_succ (p := g))
          (fun x _ hx => ?_)
        rw [Polynomial.notMem_support_iff.mp hx]
        simp

/-- Roots of the mapped pattern modulus `x^m + 1` have unit modulus. -/
theorem norm_root_fpoly_eq_one {m : ℕ} (hm : 0 < m) {ω : ℂ}
    (hω : ω ∈ ((fpoly m).map (Int.castRingHom ℂ)).roots) : ‖ω‖ = 1 := by
  have hroot := Polynomial.isRoot_of_mem_roots hω
  have heval : ω ^ m + 1 = 0 := by
    have : ((fpoly m).map (Int.castRingHom ℂ)).eval ω = ω ^ m + 1 := by
      simp [fpoly]
    rwa [Polynomial.IsRoot, this] at hroot
  have hpow : ω ^ m = -1 := by linear_combination heval
  have hnorm : ‖ω‖ ^ m = 1 := by
    rw [← norm_pow, hpow]
    simp
  have h0 : (0 : ℝ) ≤ ‖ω‖ := norm_nonneg _
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := pow_lt_one₀ h0 h hm.ne'
    linarith
  · have := one_lt_pow₀ h hm.ne'
    linarith

/-- **THE SHARP ARCHIMEDEAN ENVELOPE.**  For `m = 2^k` and `g ≠ 0` of degree `< m`,
`|patternResultant m g| ≤ (coeffMass g)^m`. -/
theorem patternResultant_natAbs_le_pow {k : ℕ} {g : ℤ[X]}
    (hdeg : g.natDegree < 2 ^ k) :
    (patternResultant (2 ^ k) g).natAbs ≤ coeffMass g ^ (2 ^ k) := by
  set m : ℕ := 2 ^ k with hmdef
  have hm : 0 < m := by positivity
  -- push to ℂ
  set fC : ℂ[X] := (fpoly m).map (Int.castRingHom ℂ) with hfC
  set gC : ℂ[X] := g.map (Int.castRingHom ℂ) with hgC
  have hmonic : fC.Monic := (fpoly_monic hm).map _
  have hfdeg : fC.natDegree = m := by
    rw [hfC, (fpoly_monic hm).natDegree_map, fpoly_natDegree hm]
  have hgdeg : gC.natDegree ≤ g.natDegree := Polynomial.natDegree_map_le
  -- the ℂ resultant is the image of the ℤ resultant
  have hcast : resultant fC gC m g.natDegree
      = ((patternResultant m g : ℤ) : ℂ) := by
    unfold patternResultant
    rw [hfC, hgC, resultant_map_map]
    simp
  -- product formula
  have hsplits : fC.Splits := IsAlgClosed.splits fC
  have hprod := resultant_eq_prod_eval fC gC g.natDegree
    (le_trans hgdeg le_rfl) hsplits
  rw [hfdeg] at hprod
  rw [hprod, hmonic.leadingCoeff, one_pow, one_mul] at hcast
  -- pointwise: each root evaluation is bounded by the mass
  have hpoint : ∀ ω ∈ fC.roots, ‖gC.eval ω‖ ≤ (coeffMass g : ℝ) := by
    intro ω hω
    have h1 : ‖ω‖ = 1 := norm_root_fpoly_eq_one hm hω
    have hev : gC.eval ω = aeval ω g := by
      rw [hgC, ← algebraMap_int_eq, eval_map, ← aeval_def]
    rw [hev]
    exact norm_eval_le_coeffMass g h1
  -- product bound by induction over the root multiset
  have key : ∀ (s : Multiset ℂ), (∀ ω ∈ s, ‖gC.eval ω‖ ≤ (coeffMass g : ℝ)) →
      ‖(s.map gC.eval).prod‖ ≤ (coeffMass g : ℝ) ^ (Multiset.card s) := by
    intro s
    induction s using Multiset.induction with
    | empty => intro _; simp
    | cons a t ih =>
      intro hbound
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
      calc ‖gC.eval a * (Multiset.map gC.eval t).prod‖
          = ‖gC.eval a‖ * ‖(Multiset.map gC.eval t).prod‖ := norm_mul _ _
        _ ≤ (coeffMass g : ℝ) * (coeffMass g : ℝ) ^ (Multiset.card t) :=
            mul_le_mul (hbound a (Multiset.mem_cons_self a t))
              (ih (fun ω hω => hbound ω (Multiset.mem_cons_of_mem hω)))
              (norm_nonneg _) (Nat.cast_nonneg _)
  have hnorm : ‖((patternResultant m g : ℤ) : ℂ)‖ ≤ (coeffMass g : ℝ) ^ m := by
    rw [← hcast]
    have hcard : Multiset.card fC.roots = m := by
      rw [← hfdeg]
      exact hsplits.natDegree_eq_card_roots.symm
    calc ‖(fC.roots.map gC.eval).prod‖
        ≤ (coeffMass g : ℝ) ^ (Multiset.card fC.roots) := key _ hpoint
      _ = (coeffMass g : ℝ) ^ m := by rw [hcard]
  -- back to ℕ
  have : ((patternResultant m g).natAbs : ℝ) ≤ ((coeffMass g ^ m : ℕ) : ℝ) := by
    push_cast
    calc ((patternResultant m g).natAbs : ℝ)
        = ‖((patternResultant m g : ℤ) : ℂ)‖ := by
          simp only [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
      _ ≤ (coeffMass g : ℝ) ^ m := hnorm
  exact_mod_cast this

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms norm_eval_le_coeffMass
#print axioms norm_root_fpoly_eq_one
#print axioms patternResultant_natAbs_le_pow

end ArkLib.ProximityGap.Frontier.FS16SharpResultantEnvelope
