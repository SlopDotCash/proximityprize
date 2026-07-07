/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R20QuadFaceBridge

/-!
# LANE CASTBRIDGE (#466 round 20, part 2): `MobiusCrossRatioIdentity` is a THEOREM —
# the quadratic face of `QuarticWeilInput` now rests on `LegendreCubicHasse` ALONE

`_R20QuadFaceBridge.lean` closed the ℤ → ℂ cast bridge and reduced the full quadratic
face to TWO named inputs: `LegendreCubicHasse` (genus-1 Hasse, the wall) and
`MobiusCrossRatioIdentity` (the exact Möbius/cross-ratio law, left "elementary,
unformalized").  This file DISCHARGES the second input.

## The proof shape (probe `probe_r20_mobius_lite.py` + `probe_r20_normalform.py`:
## EXACT, 0 failures over ~4500 random distinct tuples, p ∈ {13,…,211})

No general fractional-linear bookkeeping is needed.  The single substitution
`t = d + 1/s` (the Möbius map `∞ ↦ d`) does everything, because `χ` is quadratic and
the substitution scales the quartic argument by the perfect square `(t−d)⁴`:

* `mobius_reduction_raw`:
  `∑_t χ((t−a)(t−b)(t−c)(t−d)) = χ((d−a)(d−b)(d−c)) · ∑_w χ(w(w−u₀)(w−v₀)) − 1`,
  `u₀ = (a−b)/((d−a)(d−b))`, `v₀ = (a−c)/((d−a)(d−c))` — split off `t = d` (term `0`),
  reindex `s = (t−d)⁻¹` (a bijection `univ.erase d ≃ univ.erase 0`), kill the Jacobian
  square, complete the sum at `s = 0` (value `χ(1) = 1`, the `−1`), factor the leading
  coefficient, shift.
* `cubic_scale`: `∑_w χ(w(w−u)(w−v)) = χ(u)·∑_x χ(x(x−1)(x−v/u))` for `u ≠ 0`
  (scaling reindex `w = u·x`; `χ(u³) = χ(u)`).
* `mobius_normal_form`: composing the two,
  `∑_t χ(…) = χ((a−b)(d−c)) · ∑_x χ(x(x−1)(x−λ')) − 1`, `λ' = (a−c)(d−b)/((a−b)(d−c))`.
* `mobiusCrossRatioIdentity_holds`: the r20 residual VERBATIM — apply the normal form at
  the relabeled tuple `(a, d, c, b)` (the quartic is symmetric in its roots; the
  relabeling turns `λ'` into the residual's cross-ratio `(a−c)(b−d)/((a−d)(b−c))` and
  the twist into `χ((a−d)(b−c))`), for every odd-characteristic finite field.

## Consequences (axiom-clean, single-residual form)

* `quarticWeilInput_of_legendreCubicHasse`:
  `ringChar F ≠ 2 → LegendreCubicHasse F → QuarticWeilInput (quadCharC F) G` for EVERY
  `G` — the full quadratic face (all `n⁴` tuples), ONE residual.
* `fourthMoment_quadChar_of_legendreCubicHasse`: with `|G|⁴ ≤ p`, the r=2 rung's
  fourth-moment bound `∑_s ‖T_{χ₂}(s)‖⁴ ≤ 6|G|²p` at the quadratic character, from
  `LegendreCubicHasse` alone.

## HONEST residual accounting (no closure claimed)

* `LegendreCubicHasse` (elliptic Hasse `|a_p| ≤ 2√p` for `y² = s(s−u)(s−v)`) is NOT
  proven here or anywhere in Mathlib — it remains THE named open input, now carrying the
  entire quadratic face by itself.
* The r=2 rung (`FourthMomentTwistBound G X 6`) quantifies over ALL `χ ∈ X`
  (`chiFamily`: the `m−1` nontrivial characters of order dividing `m = 2^μ`).  This
  chain closes exactly ONE face — the unique order-2 member.  For order `d > 2` the
  quartic becomes `(s−x₁)(s−x₂)(s−y₁)^{d−1}(s−y₂)^{d−1}` (genus grows with `d`), the
  degeneracy predicate differs, and the Möbius-lite step only kills `d`-th-power
  factors; those faces remain open at `QuarticWeilInput χ`.

Issue #466, round 20, CASTBRIDGE lane (part 2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R20MobiusDischarge

open ArkLib.ProximityGap.Frontier.R19HasseAudit
open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R20QuadFaceBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step 1: the raw `∞ ↦ d` reduction -/

/-- **The Möbius-lite reduction** (exact, no error term): for pairwise-distinct
`a, b, c, d`,
`∑_t χ((t−a)(t−b)((t−c)(t−d))) = χ((d−a)(d−b)(d−c)) · ∑_w χ(w((w−u₀)(w−v₀))) − 1`
with `u₀ = (a−b)/((d−a)(d−b))`, `v₀ = (a−c)/((d−a)(d−c))`. -/
theorem mobius_reduction_raw (_hF : ringChar F ≠ 2) {a b c d : F}
    (_hab : a ≠ b) (_hac : a ≠ c) (had : a ≠ d) (_hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    ∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d)))
      = quadraticChar F ((d - a) * (d - b) * (d - c))
          * (∑ w : F, quadraticChar F
              (w * ((w - (a - b) / ((d - a) * (d - b)))
                * (w - (a - c) / ((d - a) * (d - c))))))
        - 1 := by
  classical
  have hda : d - a ≠ 0 := sub_ne_zero.mpr (fun h => had h.symm)
  have hdb : d - b ≠ 0 := sub_ne_zero.mpr (fun h => hbd h.symm)
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (fun h => hcd h.symm)
  -- Step A: drop t = d (its term is χ 0 = 0)
  have hstepA : ∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d)))
      = ∑ t ∈ Finset.univ.erase d,
          quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d))) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ d)]
    simp
  -- Step B: reindex s = (t − d)⁻¹; the Jacobian is the square (t−d)⁴, invisible to χ
  have hstepB : ∑ t ∈ Finset.univ.erase d,
        quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d)))
      = ∑ s ∈ Finset.univ.erase (0 : F),
          quadraticChar F
            ((1 + (d - a) * s) * (1 + (d - b) * s) * (1 + (d - c) * s)) := by
    refine Finset.sum_nbij' (fun t => (t - d)⁻¹) (fun s => d + s⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact Finset.mem_erase.mpr
        ⟨inv_ne_zero (sub_ne_zero.mpr (Finset.mem_erase.mp ht).1), Finset.mem_univ _⟩
    · intro s hs
      have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      have hinv : s⁻¹ = 0 := by linear_combination h
      exact hs0 (inv_eq_zero.mp hinv)
    · intro t ht
      have htd : t - d ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp ht).1
      change d + ((t - d)⁻¹)⁻¹ = t
      rw [inv_inv]; ring
    · intro s hs
      change (d + s⁻¹ - d)⁻¹ = s
      rw [show d + s⁻¹ - d = s⁻¹ by ring, inv_inv]
    · intro t ht
      have htd : t - d ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp ht).1
      have harg : (t - a) * (t - b) * ((t - c) * (t - d))
          = ((t - d) ^ 2) ^ 2
            * ((1 + (d - a) * (t - d)⁻¹) * (1 + (d - b) * (t - d)⁻¹)
              * (1 + (d - c) * (t - d)⁻¹)) := by
        field_simp
        ring
      rw [harg, map_mul, quadraticChar_sq_one' (pow_ne_zero 2 htd), one_mul]
  -- Step C: complete the sum at s = 0 (value χ(1) = 1)
  have hstepC : ∑ s ∈ Finset.univ.erase (0 : F),
        quadraticChar F ((1 + (d - a) * s) * (1 + (d - b) * s) * (1 + (d - c) * s))
      = (∑ s : F, quadraticChar F
          ((1 + (d - a) * s) * (1 + (d - b) * s) * (1 + (d - c) * s))) - 1 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun s : F => quadraticChar F
        ((1 + (d - a) * s) * (1 + (d - b) * s) * (1 + (d - c) * s)))
      (Finset.mem_univ (0 : F))
    simp only [mul_zero, add_zero, mul_one, map_one] at h
    linarith
  -- Step D: factor the leading coefficient A = (d−a)(d−b)(d−c)
  have hstepD : ∀ s : F,
      quadraticChar F ((1 + (d - a) * s) * (1 + (d - b) * s) * (1 + (d - c) * s))
        = quadraticChar F ((d - a) * (d - b) * (d - c))
            * quadraticChar F
              ((s - -(d - a)⁻¹) * ((s - -(d - b)⁻¹) * (s - -(d - c)⁻¹))) := by
    intro s
    have hfac : (1 + (d - a) * s) * (1 + (d - b) * s) * (1 + (d - c) * s)
        = ((d - a) * (d - b) * (d - c))
            * ((s - -(d - a)⁻¹) * ((s - -(d - b)⁻¹) * (s - -(d - c)⁻¹))) := by
      field_simp
      ring
    rw [hfac, map_mul]
  -- Step E: shift by α = −(d−a)⁻¹
  have hstepE : ∑ s : F,
        quadraticChar F ((s - -(d - a)⁻¹) * ((s - -(d - b)⁻¹) * (s - -(d - c)⁻¹)))
      = ∑ w : F, quadraticChar F
          (w * ((w - (-(d - b)⁻¹ - -(d - a)⁻¹)) * (w - (-(d - c)⁻¹ - -(d - a)⁻¹)))) := by
    refine (Fintype.sum_equiv (Equiv.subRight (-(d - a)⁻¹)) _ _ fun s => ?_).symm.symm
    · simp only [Equiv.subRight_apply]
      congr 1
      ring
  -- root-constant conversions to division form
  have hu : -(d - b)⁻¹ - -(d - a)⁻¹ = (a - b) / ((d - a) * (d - b)) := by
    field_simp
    ring
  have hv : -(d - c)⁻¹ - -(d - a)⁻¹ = (a - c) / ((d - a) * (d - c)) := by
    field_simp
    ring
  rw [hstepA, hstepB, hstepC, Finset.sum_congr rfl fun s _ => hstepD s,
    ← Finset.mul_sum, hstepE, hu, hv]

/-! ## Step 2: scaling to the Legendre normal form -/

/-- **Scaling reindex** `w = u·x`, `u ≠ 0`:
`∑_w χ(w(w−u)(w−v)) = χ(u) · ∑_x χ(x(x−1)(x−v/u))` — the cubic sum with a root at `u`
is the Legendre-normal-form sum at `λ = v/u`, twisted by `χ(u)` (since `χ(u³) = χ(u)`). -/
theorem cubic_scale (_hF : ringChar F ≠ 2) {u : F} (hu : u ≠ 0) (v : F) :
    ∑ w : F, quadraticChar F (w * ((w - u) * (w - v)))
      = quadraticChar F u
          * ∑ x : F, quadraticChar F (x * ((x - 1) * (x - v / u))) := by
  classical
  have hre : ∑ w : F, quadraticChar F (w * ((w - u) * (w - v)))
      = ∑ x : F, quadraticChar F ((u * x) * ((u * x - u) * (u * x - v))) :=
    (Fintype.sum_equiv (Equiv.mulLeft₀ u hu)
      (fun x => quadraticChar F ((u * x) * ((u * x - u) * (u * x - v))))
      (fun w => quadraticChar F (w * ((w - u) * (w - v))))
      (fun x => rfl)).symm
  have hpt : ∀ x : F, quadraticChar F ((u * x) * ((u * x - u) * (u * x - v)))
      = quadraticChar F u * quadraticChar F (x * ((x - 1) * (x - v / u))) := by
    intro x
    have harg : (u * x) * ((u * x - u) * (u * x - v))
        = u ^ 2 * (u * (x * ((x - 1) * (x - v / u)))) := by
      field_simp
      try ring
    rw [harg, map_mul, quadraticChar_sq_one' hu, one_mul, map_mul]
  rw [hre, Finset.sum_congr rfl fun x _ => hpt x, ← Finset.mul_sum]

/-! ## Step 3: the normal form and the residual discharge -/

/-- **Normal form**: for pairwise-distinct `a,b,c,d`,
`∑_t χ((t−a)(t−b)(t−c)(t−d)) = χ((a−b)(d−c)) · ∑_x χ(x(x−1)(x−λ')) − 1`,
`λ' = (a−c)(d−b)/((a−b)(d−c))`. -/
theorem mobius_normal_form (hF : ringChar F ≠ 2) {a b c d : F}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    ∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d)))
      = quadraticChar F ((a - b) * (d - c))
          * (∑ x : F, quadraticChar F
              (x * ((x - 1) * (x - (a - c) * (d - b) / ((a - b) * (d - c))))))
        - 1 := by
  have hda : d - a ≠ 0 := sub_ne_zero.mpr (fun h => had h.symm)
  have hdb : d - b ≠ 0 := sub_ne_zero.mpr (fun h => hbd h.symm)
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (fun h => hcd h.symm)
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
  have hu0 : (a - b) / ((d - a) * (d - b)) ≠ 0 :=
    div_ne_zero hab' (mul_ne_zero hda hdb)
  have hraw := mobius_reduction_raw hF hab hac had hbc hbd hcd
  rw [hraw, cubic_scale hF hu0 ((a - c) / ((d - a) * (d - c))), ← mul_assoc,
    ← map_mul]
  have hAu : (d - a) * (d - b) * (d - c) * ((a - b) / ((d - a) * (d - b)))
      = (a - b) * (d - c) := by
    field_simp
    try ring
  have hvu : (a - c) / ((d - a) * (d - c)) / ((a - b) / ((d - a) * (d - b)))
      = (a - c) * (d - b) / ((a - b) * (d - c)) := by
    field_simp
    try ring
  rw [hAu, hvu]

/-- **THE DISCHARGE**: `MobiusCrossRatioIdentity` (the round-20 named residual) is a
THEOREM for every finite field of odd characteristic — apply the normal form at the
relabeled root tuple `(a, d, c, b)`. -/
theorem mobiusCrossRatioIdentity_holds (hF : ringChar F ≠ 2) :
    MobiusCrossRatioIdentity F := by
  intro a b c d hab hac had hbc hbd hcd
  have h := mobius_normal_form hF (a := a) (b := d) (c := c) (d := b)
    had hac hab (Ne.symm hcd) (Ne.symm hbd) (Ne.symm hbc)
  calc ∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d)))
      = ∑ t : F, quadraticChar F ((t - a) * (t - d) * ((t - c) * (t - b))) :=
        Finset.sum_congr rfl fun t _ => congrArg (quadraticChar F) (by ring)
    _ = quadraticChar F ((a - d) * (b - c))
          * (∑ s : F, quadraticChar F
              (s * ((s - 1) * (s - (a - c) * (b - d) / ((a - d) * (b - c))))))
        - 1 := h

/-! ## The single-residual quadratic face -/

/-- **THE LANE RESULT (single residual)**: `LegendreCubicHasse F` ALONE closes the
entire quadratic face of `QuarticWeilInput` — all `n⁴` tuples, every shift set `G`. -/
theorem quarticWeilInput_of_legendreCubicHasse (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) (G : Finset F) :
    QuarticWeilInput (quadCharC F) G :=
  quarticWeilInput_of_cubicHasse_mobius hF hH (mobiusCrossRatioIdentity_holds hF) G

/-- Consumer corollary: `LegendreCubicHasse` + the regime `|G|⁴ ≤ p` give the r=2
rung's fourth-moment bound at the quadratic character. -/
theorem fourthMoment_quadChar_of_legendreCubicHasse (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) (G : Finset F)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum
        (quadCharC F) G s‖ ^ 4
      ≤ 6 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) :=
  fourthMoment_le_of_quarticWeilInput (quadCharC F) G
    (quarticWeilInput_of_legendreCubicHasse hF hH G) hp

end ArkLib.ProximityGap.Frontier.R20MobiusDischarge

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R20MobiusDischarge.mobius_reduction_raw
#print axioms ArkLib.ProximityGap.Frontier.R20MobiusDischarge.cubic_scale
#print axioms ArkLib.ProximityGap.Frontier.R20MobiusDischarge.mobius_normal_form
#print axioms
  ArkLib.ProximityGap.Frontier.R20MobiusDischarge.mobiusCrossRatioIdentity_holds
#print axioms
  ArkLib.ProximityGap.Frontier.R20MobiusDischarge.quarticWeilInput_of_legendreCubicHasse
#print axioms
  ArkLib.ProximityGap.Frontier.R20MobiusDischarge.fourthMoment_quadChar_of_legendreCubicHasse
