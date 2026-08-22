/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18FourthMomentTwist
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19HasseAudit

/-!
# LANE CASTBRIDGE (#466 round 20): the quadratic face of `QuarticWeilInput`,
# closed modulo `LegendreCubicHasse` + ONE exact Möbius identity

Round 19 left two gaps between `_R19HasseAudit` (integer-valued `quadraticChar F : MulChar F ℤ`)
and `QuarticWeilInput` (`_R18FourthMomentTwist`, a ℂ-valued `MulChar` norm bound):

**Gap 1 — the ℤ → ℂ cast bridge: CLOSED here (fully proven).**
`quadCharC F := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)` is the quadratic character
into ℂ; it is conj-invariant (integer values), so `quadTerm (quadCharC F) z` is EXACTLY the
cast of the integer quartic character sum `intQuartic z`, and
`‖quadTerm (quadCharC F) z‖ = |intQuartic z|` (`norm_quadTerm_quadCharC`).  Every integer
bound from `_R19HasseAudit` transfers verbatim to the ℂ-norm interface.

**Gap 2 — general (non-±-paired) tuples.**  HONEST ARITHMETIC first: ±-paired tuples
`((x,−x),(y,−y))` number `≤ |G|²` out of `|G|⁴` — a `1/n²` fraction.  The r19 paired
reduction alone CANNOT cover the mass; the bulk needs the general quartic.  Resolution here,
in three layers:
1. **Repeated-root nondegenerate tuples (patterns (2,1,1) and (3,1)): PROVEN
   unconditionally**, `|intQuartic| ≤ 2` (`intQuartic_sq_factor_bound` — the even factor
   `(s−w)²` has `χ = 1` off `s = w`, leaving the r19 complete quadratic evaluation `−1`).
2. **All-distinct tuples: the Möbius/cross-ratio law**, stated as the NAMED residual
   `MobiusCrossRatioIdentity`:
   `∑_t χ((t−a)(t−b)(t−c)(t−d)) = χ((a−d)(b−c)) · ∑_s χ(s(s−1)(s−λ)) − 1`,
   `λ = (a−c)(b−d)/((a−d)(b−c))` the cross-ratio.  Probe
   (`probe_r20_mobius*.py`, round-20 scratchpad): EXACT at `p ∈ {101, 211, 401, 613}`
   (both residue classes mod 4), 300 random distinct tuples each, **1200/1200**, twist
   factor pinned to `χ((a−d)(b−c))` (the two alternative twists fail ≈50%).  The identity
   is elementary (fractional-linear reindexing `t = m(s)` with `m : 0↦a, 1↦b, ∞↦d`;
   `χ(denominator⁴) = 1`; one pole term = the `−1`) — formalizable, unformalized;
   left as the named residual rather than a rushed proof.
3. **λ lands in the r19 residual**: `λ ≠ 0` (from `a≠c, b≠d`) and `λ ≠ 1` (from
   `(a−c)(b−d) − (a−d)(b−c) = (a−b)(c−d) ≠ 0` — proven in-file), so
   `∑_s χ(s(s−1)(s−λ))` is `LegendreCubicHasse` at `u = 1, v = λ`.  No NEW Hasse-type
   input beyond r19's single residual.

**Main theorem** (`quarticWeilInput_of_cubicHasse_mobius`):
`LegendreCubicHasse F → MobiusCrossRatioIdentity F → QuarticWeilInput (quadCharC F) G`
for EVERY `G` — the full quadratic face, all tuples, with budget room:
distinct tuples get `2√p + 1 ≤ 3√p`, repeated-root tuples get `2 ≤ 3√p`.
Also kept: the paired-only face `paired_quadTerm_bound_of_cubicHasse` needing ONLY
`LegendreCubicHasse` (no Möbius) — the r19 deliverable, now at the ℂ interface.

**Residual ledger after this file** (quadratic face of the corrected-B r=2 rung):
`QuarticWeilInput (quadCharC F) G` ⟸ `LegendreCubicHasse F` (genus-1 Hasse, the true
wall, absent from Mathlib) + `MobiusCrossRatioIdentity F` (elementary exact identity,
probe-verified, formalization debt only).  No closure claimed.

Issue #466, round 20, CASTBRIDGE lane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R20QuadFaceBridge

open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R19HasseAudit
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Gap 1: the cast bridge (fully proven) -/

/-- The ℂ-valued quadratic character: ring-hom composition of the integer-valued
`quadraticChar F` with `Int.castRingHom ℂ`. -/
noncomputable def quadCharC (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem quadCharC_apply (a : F) : quadCharC F a = ((quadraticChar F a : ℤ) : ℂ) := rfl

/-- The composed character is conjugation-invariant (its values are integer casts). -/
theorem conj_quadCharC (a : F) : conj' (quadCharC F a) = quadCharC F a := by
  rw [quadCharC_apply]
  exact map_intCast (starRingEnd ℂ) _

/-- The integer quartic character sum of a quadruple. -/
def intQuartic (z : (F × F) × (F × F)) : ℤ :=
  ∑ s : F, quadraticChar F ((s - z.1.1) * (s - z.1.2) * ((s - z.2.1) * (s - z.2.2)))

/-- **CAST BRIDGE, exact form**: the ℂ-valued `quadTerm` of the composed quadratic
character IS the cast of the integer quartic sum. -/
theorem quadTerm_quadCharC_eq (z : (F × F) × (F × F)) :
    quadTerm (quadCharC F) z = ((intQuartic z : ℤ) : ℂ) := by
  unfold quadTerm intQuartic
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [conj_quadCharC, conj_quadCharC, quadCharC_apply, quadCharC_apply,
    quadCharC_apply, quadCharC_apply]
  simp only [map_mul]
  push_cast
  ring

/-- **CAST BRIDGE, norm form**: the ℂ-norm equals the integer absolute value. -/
theorem norm_quadTerm_quadCharC (z : (F × F) × (F × F)) :
    ‖quadTerm (quadCharC F) z‖ = |((intQuartic z : ℤ) : ℝ)| := by
  rw [quadTerm_quadCharC_eq,
    show ((intQuartic z : ℤ) : ℂ) = (((intQuartic z : ℤ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

/-! ## Arithmetic helpers -/

/-- From the integer-clean Hasse shape `L² ≤ 4p` to the real bound `|L| ≤ 2√p`. -/
theorem int_abs_le_two_sqrt {L : ℤ} {p : ℕ} (h : L ^ 2 ≤ 4 * p) :
    |((L : ℤ) : ℝ)| ≤ 2 * Real.sqrt p := by
  have h' : ((L : ℝ)) ^ 2 ≤ 4 * (p : ℝ) := by exact_mod_cast h
  have h1 : Real.sqrt (((L : ℝ)) ^ 2) ≤ Real.sqrt (4 * p) := Real.sqrt_le_sqrt h'
  rw [Real.sqrt_sq_eq_abs] at h1
  rwa [show (4 : ℝ) * p = 2 ^ 2 * p by norm_num,
    Real.sqrt_mul (by positivity) (p : ℝ), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h1

/-- `1 ≤ √(card F)` for any finite field. -/
theorem one_le_sqrt_card : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
  have h1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
    have := Fintype.one_lt_card (α := F)
    exact_mod_cast this.le
  have := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_one] at this

/-! ## Layer 1: repeated-root nondegenerate tuples — PROVEN, `|S| ≤ 2` -/

/-- **Repeated-root bound (unconditional)**: for `r₁ ≠ r₂`,
`|∑_s χ((s−w)²(s−r₁)(s−r₂))| ≤ 2`.  The even factor contributes `χ = 1` off `s = w`,
leaving the r19 complete quadratic evaluation `−1`, minus one boundary term. -/
theorem intQuartic_sq_factor_bound (hF : ringChar F ≠ 2) {w r₁ r₂ : F} (h : r₁ ≠ r₂) :
    |∑ s : F, quadraticChar F ((s - w) ^ 2 * ((s - r₁) * (s - r₂)))| ≤ 2 := by
  classical
  have hpt : ∀ s : F, quadraticChar F ((s - w) ^ 2 * ((s - r₁) * (s - r₂)))
      = if s = w then 0 else quadraticChar F ((s - r₁) * (s - r₂)) := by
    intro s
    by_cases hs : s = w
    · subst hs; simp
    · rw [if_neg hs, map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr hs), one_mul]
  have hsum : ∑ s : F, quadraticChar F ((s - w) ^ 2 * ((s - r₁) * (s - r₂)))
      = ∑ s ∈ univ.erase w, quadraticChar F ((s - r₁) * (s - r₂)) := by
    rw [Finset.sum_congr rfl fun s _ => hpt s,
      ← Finset.sum_erase_add univ _ (mem_univ w), if_pos rfl, add_zero]
    exact Finset.sum_congr rfl fun s hs => if_neg (Finset.mem_erase.mp hs).1
  have hfull := sum_quadraticChar_quadratic hF h (u := r₁) (v := r₂)
  have hdecomp := Finset.sum_erase_add univ
    (fun s => quadraticChar F ((s - r₁) * (s - r₂))) (mem_univ w)
  rw [hfull] at hdecomp  -- ∑_{erase w} + f w = −1  ... careful: hfull is the full sum
  -- hdecomp : ∑_{erase w} f + f w = ∑_univ f = −1
  have hval : ∑ s ∈ univ.erase w, quadraticChar F ((s - r₁) * (s - r₂))
      = -1 - quadraticChar F ((w - r₁) * (w - r₂)) := by linarith
  rw [hsum, hval]
  rcases (quadraticChar_isQuadratic F) ((w - r₁) * (w - r₂)) with hq | hq | hq <;>
    simp [hq]

/-! ## Layer 2: the Möbius/cross-ratio residual (probe-verified 1200/1200) -/

/-- **THE NAMED RESIDUAL (elementary, unformalized)**: the exact Möbius/cross-ratio law
for the all-distinct quartic character sum:
`∑_t χ((t−a)(t−b)(t−c)(t−d)) = χ((a−d)(b−c)) · ∑_s χ(s(s−1)(s−λ)) − 1` with
`λ = (a−c)(b−d)/((a−d)(b−c))`.  Probe-verified EXACTLY at 1200 random distinct tuples
across `p ∈ {101, 211, 401, 613}`; the twist `χ((a−d)(b−c))` is pinned (alternatives fail).
Elementary proof: reindex `t = m(s)` by the fractional-linear map `0↦a, 1↦b, ∞↦d`;
`χ(q(s)⁴) = 1` kills the denominator; the single pole accounts for the `−1`. -/
def MobiusCrossRatioIdentity (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ a b c d : F, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d)))
      = quadraticChar F ((a - d) * (b - c))
          * (∑ s : F, quadraticChar F
              (s * ((s - 1) * (s - (a - c) * (b - d) / ((a - d) * (b - c))))))
        - 1

/-- The cross-ratio of four distinct points is `≠ 0` and `≠ 1` — so the Legendre-family
sum in `MobiusCrossRatioIdentity` is an instance of `LegendreCubicHasse` at `u = 1, v = λ`. -/
theorem crossRatio_ne_zero_ne_one {a b c d : F}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (a - c) * (b - d) / ((a - d) * (b - c)) ≠ 0
      ∧ (a - c) * (b - d) / ((a - d) * (b - c)) ≠ 1 := by
  have hnum : (a - c) * (b - d) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hac) (sub_ne_zero.mpr hbd)
  have hden : (a - d) * (b - c) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr had) (sub_ne_zero.mpr hbc)
  constructor
  · exact div_ne_zero hnum hden
  · intro h1
    have heq : (a - c) * (b - d) = (a - d) * (b - c) := by
      exact (div_eq_one_iff_eq hden).mp h1
    have hdiff : (a - b) * (c - d) = 0 := by
      calc (a - b) * (c - d)
          = (a - c) * (b - d) - (a - d) * (b - c) := by ring
        _ = 0 := by rw [heq]; ring
    rcases mul_eq_zero.mp hdiff with h | h
    · exact hab (sub_eq_zero.mp h)
    · exact hcd (sub_eq_zero.mp h)

/-- **All-distinct bound, modulo the two residuals**: `|intQuartic| ≤ 2√p + 1` in ℝ. -/
theorem intQuartic_distinct_bound (hH : LegendreCubicHasse F)
    (hM : MobiusCrossRatioIdentity F) {a b c d : F}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    |((∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d))) : ℤ) : ℝ)|
      ≤ 2 * Real.sqrt (Fintype.card F) + 1 := by
  obtain ⟨hlam0, hlam1⟩ := crossRatio_ne_zero_ne_one hab hac had hbc hbd hcd
  set lam : F := (a - c) * (b - d) / ((a - d) * (b - c)) with hlam
  set L : ℤ := ∑ s : F, quadraticChar F (s * ((s - 1) * (s - lam))) with hL
  have hLb : L ^ 2 ≤ 4 * Fintype.card F := hH 1 lam one_ne_zero hlam0 (fun h => hlam1 h.symm)
  have hLr : |((L : ℤ) : ℝ)| ≤ 2 * Real.sqrt (Fintype.card F) := int_abs_le_two_sqrt hLb
  have hid := hM a b c d hab hac had hbc hbd hcd
  set eps : ℤ := quadraticChar F ((a - d) * (b - c)) with heps
  have hepsr : |((eps : ℤ) : ℝ)| ≤ 1 := by
    rcases (quadraticChar_isQuadratic F) ((a - d) * (b - c)) with hq | hq | hq <;>
      simp [heps, hq]
  have hcast : ((∑ t : F, quadraticChar F ((t - a) * (t - b) * ((t - c) * (t - d))) : ℤ) : ℝ)
      = ((eps : ℤ) : ℝ) * ((L : ℤ) : ℝ) - 1 := by
    rw [hid, ← hlam, ← hL]
    push_cast
    ring
  rw [hcast]
  calc |((eps : ℤ) : ℝ) * ((L : ℤ) : ℝ) - 1|
      ≤ |((eps : ℤ) : ℝ) * ((L : ℤ) : ℝ)| + |(1 : ℝ)| := abs_sub _ _
    _ = |((eps : ℤ) : ℝ)| * |((L : ℤ) : ℝ)| + 1 := by rw [abs_mul, abs_one]
    _ ≤ 1 * (2 * Real.sqrt (Fintype.card F)) + 1 := by
        have hLnn : 0 ≤ |((L : ℤ) : ℝ)| := abs_nonneg _
        nlinarith [hepsr, hLr, hLnn]
    _ = 2 * Real.sqrt (Fintype.card F) + 1 := by ring

/-! ## The paired face (r19 deliverable at the ℂ interface): needs ONLY LegendreCubicHasse -/

/-- **Paired-face bound**: for the ±-paired tuple `((x,−x),(y,−y))` with `x, y ≠ 0`,
`x² ≠ y²`, `LegendreCubicHasse` alone gives `‖quadTerm (quadCharC F) z‖ ≤ 3√p`.
(HONEST MASS NOTE: such tuples are `≤ |G|²` of the `|G|⁴` total — a `1/n²` fraction;
the bulk requires the Möbius layer below.) -/
theorem paired_quadTerm_bound_of_cubicHasse (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ^ 2 ≠ y ^ 2) :
    ‖quadTerm (quadCharC F) ((x, -x), (y, -y))‖ ≤ 3 * Real.sqrt (Fintype.card F) := by
  rw [norm_quadTerm_quadCharC]
  have hval : intQuartic ((x, -x), (y, -y))
      = ∑ t : F, quadraticChar F ((t ^ 2 - x ^ 2) * (t ^ 2 - y ^ 2)) := by
    unfold intQuartic
    exact Finset.sum_congr rfl fun s _ => congrArg (quadraticChar F) (by ring)
  have hQ := quartic_even_bound_of_cubicHasse hF hH (pow_ne_zero 2 hx) (pow_ne_zero 2 hy) hxy
  rw [hval]
  set Q : ℤ := ∑ t : F, quadraticChar F ((t ^ 2 - x ^ 2) * (t ^ 2 - y ^ 2)) with hQdef
  have h' : ((Q : ℝ)) ^ 2 ≤ 9 * (Fintype.card F : ℝ) := by exact_mod_cast hQ
  have h1 : Real.sqrt (((Q : ℝ)) ^ 2) ≤ Real.sqrt (9 * Fintype.card F) := Real.sqrt_le_sqrt h'
  rw [Real.sqrt_sq_eq_abs] at h1
  rwa [show (9 : ℝ) * Fintype.card F = 3 ^ 2 * Fintype.card F by norm_num,
    Real.sqrt_mul (by positivity) _, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)] at h1

/-! ## MAIN THEOREM: the full quadratic face -/

/-- **THE ROUND-20 REDUCTION (all tuples, every `G`)**:
`LegendreCubicHasse F` (genus-1 Hasse, the wall) plus `MobiusCrossRatioIdentity F`
(elementary exact identity, probe-verified) imply the FULL `QuarticWeilInput` for the
quadratic character — degenerate tuples excluded by hypothesis, repeated-root tuples
proven unconditionally (`≤ 2`), distinct tuples via Möbius + Hasse (`≤ 2√p + 1 ≤ 3√p`). -/
theorem quarticWeilInput_of_cubicHasse_mobius (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) (hM : MobiusCrossRatioIdentity F) (G : Finset F) :
    QuarticWeilInput (quadCharC F) G := by
  rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ _hz hdeg
  simp only [IsDegenerate, not_or] at hdeg
  obtain ⟨hd1, hd2, hd3⟩ := hdeg
  rw [norm_quadTerm_quadCharC]
  have hboundify : ∀ m : ℤ, |m| ≤ 2 →
      |((m : ℤ) : ℝ)| ≤ 3 * Real.sqrt (Fintype.card F) := by
    intro m hm
    have h2 : |((m : ℤ) : ℝ)| ≤ 2 := by exact_mod_cast hm
    have hs := one_le_sqrt_card (F := F)
    linarith
  have hrep : ∀ w r₁ r₂ : F, r₁ ≠ r₂ →
      (∀ s : F, (s - x₁) * (s - x₂) * ((s - y₁) * (s - y₂))
        = (s - w) ^ 2 * ((s - r₁) * (s - r₂))) →
      |((intQuartic ((x₁, x₂), (y₁, y₂)) : ℤ) : ℝ)| ≤ 3 * Real.sqrt (Fintype.card F) := by
    intro w r₁ r₂ hr heq
    refine hboundify _ ?_
    have hv : intQuartic ((x₁, x₂), (y₁, y₂))
        = ∑ s : F, quadraticChar F ((s - w) ^ 2 * ((s - r₁) * (s - r₂))) := by
      unfold intQuartic
      exact Finset.sum_congr rfl fun s _ => congrArg (quadraticChar F) (heq s)
    rw [hv]
    exact intQuartic_sq_factor_bound hF hr
  by_cases h12 : x₁ = x₂
  · -- pattern (2,·): w = x₁, remaining (y₁, y₂); y₁ ≠ y₂ from ¬clause 3
    have hy : y₁ ≠ y₂ := fun h => hd3 ⟨h12, h⟩
    exact hrep x₁ y₁ y₂ hy fun s => by rw [← h12]; ring
  by_cases h11 : x₁ = y₁
  · have hne : x₂ ≠ y₂ := fun h => hd1 ⟨h11, h⟩
    exact hrep x₁ x₂ y₂ hne fun s => by rw [h11]; ring
  by_cases h1y2 : x₁ = y₂
  · have hne : x₂ ≠ y₁ := fun h => hd2 ⟨h1y2, h⟩
    exact hrep x₁ x₂ y₁ hne fun s => by rw [h1y2]; ring
  by_cases h21 : x₂ = y₁
  · have hne : x₁ ≠ y₂ := fun h => hd2 ⟨h, h21⟩
    exact hrep x₂ x₁ y₂ hne fun s => by rw [h21]; ring
  by_cases h22 : x₂ = y₂
  · have hne : x₁ ≠ y₁ := fun h => hd1 ⟨h, h22⟩
    exact hrep x₂ x₁ y₁ hne fun s => by rw [h22]; ring
  by_cases hyy : y₁ = y₂
  · exact hrep y₁ x₁ x₂ h12 fun s => by rw [hyy]; ring
  -- all distinct: Möbius + LegendreCubicHasse
  have hb := intQuartic_distinct_bound hH hM h12 h11 h1y2 h21 h22 hyy
  have hs := one_le_sqrt_card (F := F)
  calc |((intQuartic ((x₁, x₂), (y₁, y₂)) : ℤ) : ℝ)|
      ≤ 2 * Real.sqrt (Fintype.card F) + 1 := hb
    _ ≤ 3 * Real.sqrt (Fintype.card F) := by linarith

/-- Composition with the round-18 reduction: both residuals + `p ≥ n⁴` give the
r=2 rung's FourthMomentTwistBound input at the quadratic character. -/
theorem fourthMoment_bound_of_residuals (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) (hM : MobiusCrossRatioIdentity F) (G : Finset F)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ 6 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) :=
  fourthMoment_le_of_quarticWeilInput (quadCharC F) G
    (quarticWeilInput_of_cubicHasse_mobius hF hH hM G) hp

end ArkLib.ProximityGap.Frontier.R20QuadFaceBridge

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.quadCharC_apply
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.conj_quadCharC
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.quadTerm_quadCharC_eq
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.norm_quadTerm_quadCharC
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.int_abs_le_two_sqrt
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.intQuartic_sq_factor_bound
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.crossRatio_ne_zero_ne_one
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.intQuartic_distinct_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.paired_quadTerm_bound_of_cubicHasse
#print axioms
  ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.quarticWeilInput_of_cubicHasse_mobius
#print axioms ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.fourthMoment_bound_of_residuals
