/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidenceDeviationCharSum

/-!
# The incidence deviation has √q-cancellation IN MEAN-SQUARE OVER THE OFFSET — #444

This file sharpens the latest prize-floor capstone (`Frontier/_PrizeFloorOfBGK.lean`,
`prizeFloor_window_of_BGK_and_incidence`).  That capstone's TWO-input correction observes that the
*pointwise* far-line incidence deviation only has the **naive `(#dev)·B` triangle bound**
(`IncidenceDeviationCharSum.incidence_dev_le`), which is VACUOUS at the prize budget for any nonzero
`B`; the operative open input it isolates is the **per-frequency `√q·B` square-root cancellation**
(BCHKS Conj 1.12 over the annihilator hyperplane).

We prove here, UNCONDITIONALLY and axiom-clean, the precise sense in which that `√q·B`
square-root cancellation is **already true**: it holds in the **mean-square average over the line
offset `s₀`**.  Concretely, for the deviation field

  `D(s₀) := I(s₀, s₁) − |G| = ∑_{b ∈ deviationSupport s₁} conj(η_b)·ψ(b·s₀)`
  (`= IncidenceDeviationCharSum.incidence_sub_mean`),

the additive-character orthogonality `∑_{s₀} ψ((b−b')·s₀) = q·[b = b']` (`AddChar.sum_mulShift`)
collapses ALL cross terms, giving the **exact Parseval identity over the offset**:

  > `∑_{s₀ ∈ F} ‖D(s₀)‖² = q · ∑_{b ∈ deviationSupport s₁} ‖η_b‖²`.   (`dev_l2_offset_eq`)

Consequently, under the uniform per-frequency bound `‖η_b‖ ≤ B` (`b ≠ 0`):

  > `∑_{s₀} ‖D(s₀)‖²  ≤  q · (#dev) · B²`,                              (`dev_l2_offset_le`)

so the **mean-square (root-mean-square) deviation over the offset** satisfies

  > `(1/q) ∑_{s₀} ‖D(s₀)‖²  ≤  (#dev) · B²  ≤  q · B²`,                 (`dev_meansq_offset_le`)

i.e. the **rms-over-offset deviation is `≤ √(#dev) · B ≤ √q · B`** — exactly the
square-root-cancellation scale the prize budget needs, achieved here on AVERAGE over `s₀`.

## WHAT THIS IS AND IS NOT (honesty header)

This is the **√q·B cancellation in the `L²(s₀)` / mean-square norm**.  It is NOT the prize.  The
prize needs the bound on the **worst-case (`L∞(s₀)`) single offset** — `max_{s₀}‖D(s₀)‖ ≲ √q·B` —
and the gap between the proven mean-square `√q·B` and the open worst-case `√q·B` is *exactly* the
L²→L∞ (average→sup over offset) upgrade, which is BCHKS Conj 1.12 / the 25-yr Paley wall.  What is
new and certified here: the cancellation is **free in mean-square**, and the entire remaining
difficulty is localised to the sup-over-offset, NOT to the per-frequency bound `B`.  This is the
quantitative form of the `_PrizeFloorOfBGK` correction: the naive triangle `(#dev)·B` is loose by a
full `√(#dev)` factor that is recovered for FREE by orthogonality the moment you average over `s₀`.

Probe: `scripts/probes/probe_incidence_dev_l2_offset.py` (TRUE thin μ_n, n=2^a, prize-regime
p ≡ 1 mod n incl. Fermat F4=257; Parseval identity exact + rms ≤ √(#dev)·B strictly below the
triangle `(#dev)·B` in every instance).

Axiom-clean (`propext, Classical.choice, Quot.sound`); pure additive-character orthogonality, no
field-size or regime hypotheses.  Issue #444.
-/

set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.IncidenceDevL2Offset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open ArkLib.ProximityGap.IncidenceDeviationCharSum

/-- **The pointwise deviation field, as a character sum over the deviation support.**
A convenient abbreviation: `D ψ G s₀ s₁ = ∑_{b ∈ deviationSupport s₁} conj(η_b)·ψ(b·s₀)`. By
`IncidenceDeviationCharSum.incidence_sub_mean` this equals `I(s₀,s₁) − |G|` (the spectral error of
the far-line incidence at offset `s₀`). -/
noncomputable def devField (ψ : AddChar F ℂ) (G : Finset F) (s₀ s₁ : F) : ℂ :=
  ∑ b ∈ deviationSupport s₁, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

theorem devField_eq_incidence_sub_mean {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) :
    devField ψ G s₀ s₁ = (lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ) := by
  rw [devField, ← incidence_sub_mean hψ G s₀ s₁]

/-- **Orthogonality of the offset-characters (specialised `AddChar.sum_mulShift`).**
For primitive `ψ` and any two frequencies `b b'`, summing `ψ(b·s₀)·conj(ψ(b'·s₀))` over the
offset `s₀` collapses to `q·[b = b']`:

  `∑_{s₀} ψ(b·s₀)·conj(ψ(b'·s₀)) = if b = b' then q else 0`.

This is the engine of the mean-square cancellation: distinct frequencies are orthogonal over the
offset, so all cross terms in `‖D(s₀)‖²` vanish on summation. -/
theorem sum_offset_char_orthogonal {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (b b' : F) :
    (∑ s₀ : F, ψ (b * s₀) * (starRingEnd ℂ) (ψ (b' * s₀)))
      = if b = b' then (Fintype.card F : ℂ) else 0 := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  -- conj(ψ(b'·s₀)) = ψ(-(b'·s₀)), and ψ(b·s₀)·ψ(-(b'·s₀)) = ψ((b−b')·s₀).
  have hterm : ∀ s₀ : F, ψ (b * s₀) * (starRingEnd ℂ) (ψ (b' * s₀))
      = ψ (s₀ * (b - b')) := by
    intro s₀
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have hstep : (∑ s₀ : F, ψ (b * s₀) * (starRingEnd ℂ) (ψ (b' * s₀)))
      = ∑ s₀ : F, ψ (s₀ * (b - b')) := Finset.sum_congr rfl (fun s₀ _ => hterm s₀)
  rw [hstep, AddChar.sum_mulShift (b - b') hψ]
  simp only [sub_eq_zero]
  split_ifs <;> simp_all

/-- **THE MEAN-SQUARE-OVER-OFFSET PARSEVAL IDENTITY (headline).**
Summing the squared modulus of the incidence deviation over ALL line offsets `s₀` equals `q` times
the period energy carried by the deviation support:

  `∑_{s₀ ∈ F} ‖D(s₀)‖² = q · ∑_{b ∈ deviationSupport s₁} ‖η_b‖²`.

Mechanism: expand `‖D(s₀)‖² = ∑_{b,b'} conj(η_b)·η_{b'}·ψ(b·s₀)·conj(ψ(b'·s₀))`, swap the `s₀` sum
inside, and apply `sum_offset_char_orthogonal` — every `b ≠ b'` cross term dies, leaving the
diagonal `∑_b ‖η_b‖²·q`.  This is the exact L²(offset) cancellation: the naive `(#dev)·B` triangle
is loose by `√(#dev)` once you average over `s₀`. -/
theorem dev_l2_offset_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₁ : F) :
    (∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2)
      = (Fintype.card F : ℝ) * ∑ b ∈ deviationSupport s₁, ‖eta ψ G b‖ ^ 2 := by
  classical
  -- Work in ℂ: ‖z‖² = (conj z · z).re, then push the cast to ℝ at the end.
  have hcast : ∀ s₀ : F, (‖devField ψ G s₀ s₁‖ ^ 2 : ℝ)
      = (((starRingEnd ℂ) (devField ψ G s₀ s₁) * devField ψ G s₀ s₁).re) := by
    intro s₀
    have h1 : ((starRingEnd ℂ) (devField ψ G s₀ s₁) * devField ψ G s₀ s₁).re
        = Complex.normSq (devField ψ G s₀ s₁) := by
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]; ring
    have h2 : Complex.normSq (devField ψ G s₀ s₁) = ‖devField ψ G s₀ s₁‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    rw [h1, h2]
  -- Expand each ‖D(s₀)‖² as a double sum over (b', b) in the deviation support (outer b' from
  -- conj D, inner b from D), matching `Finset.sum_mul_sum`.
  have hexpand : ∀ s₀ : F,
      (starRingEnd ℂ) (devField ψ G s₀ s₁) * devField ψ G s₀ s₁
        = ∑ b' ∈ deviationSupport s₁, ∑ b ∈ deviationSupport s₁,
            ((eta ψ G b' * (starRingEnd ℂ) (eta ψ G b))
              * (ψ (b * s₀) * (starRingEnd ℂ) (ψ (b' * s₀)))) := by
    intro s₀
    -- conj(D) = ∑_{b'} η_{b'}·conj(ψ(b' s₀));  D = ∑_b conj(η_b)·ψ(b s₀)
    have hconjD : (starRingEnd ℂ) (devField ψ G s₀ s₁)
        = ∑ b' ∈ deviationSupport s₁, eta ψ G b' * (starRingEnd ℂ) (ψ (b' * s₀)) := by
      rw [devField, map_sum]
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      rw [map_mul, Complex.conj_conj]
    rw [hconjD]
    conv_lhs => rw [devField]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  -- Sum over s₀ in ℂ, swap to put the s₀-sum innermost, apply orthogonality.
  have hsumC :
      (∑ s₀ : F, (starRingEnd ℂ) (devField ψ G s₀ s₁) * devField ψ G s₀ s₁)
        = (Fintype.card F : ℂ) * ∑ b ∈ deviationSupport s₁, ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b) := by
    rw [Finset.sum_congr rfl (fun s₀ _ => hexpand s₀)]
    -- swap ∑_{s₀} ∑_{b'} ∑_{b} → ∑_{b'} ∑_{b} ∑_{s₀}
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b' hb'mem => ?_)
    rw [Finset.sum_comm]
    -- inner over b: ∑_b coeff(b',b) ∑_{s₀} ψ(b s₀)conj ψ(b' s₀) = coeff(b',b')·q (only b=b' survives)
    have hb : ∀ b ∈ deviationSupport s₁,
        (∑ s₀ : F, (eta ψ G b' * (starRingEnd ℂ) (eta ψ G b))
            * (ψ (b * s₀) * (starRingEnd ℂ) (ψ (b' * s₀))))
          = if b = b' then (Fintype.card F : ℂ) * ((starRingEnd ℂ) (eta ψ G b') * eta ψ G b')
              else 0 := by
      intro b _
      rw [← Finset.mul_sum, sum_offset_char_orthogonal hψ b b']
      by_cases h : b = b'
      · subst h; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hb, Finset.sum_ite_eq' (deviationSupport s₁) b']
    rw [if_pos hb'mem]
  -- Cast the ℂ identity to ℝ via the real parts.
  rw [Finset.sum_congr rfl (fun s₀ _ => hcast s₀)]
  have hre := congrArg Complex.re hsumC
  rw [Complex.re_sum] at hre
  rw [hre]
  -- RHS real part: (q : ℂ)·∑ (conj η_b · η_b)  →  q·∑ ‖η_b‖²
  rw [Complex.mul_re]
  have him : (∑ b ∈ deviationSupport s₁, (starRingEnd ℂ) (eta ψ G b) * eta ψ G b).im = 0 := by
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  have hre' : (∑ b ∈ deviationSupport s₁, (starRingEnd ℂ) (eta ψ G b) * eta ψ G b).re
      = ∑ b ∈ deviationSupport s₁, ‖eta ψ G b‖ ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have h1 : ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b).re = Complex.normSq (eta ψ G b) := by
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]; ring
    rw [h1, Complex.normSq_eq_norm_sq]
  simp only [Complex.natCast_re, Complex.natCast_im, him, hre']
  ring

/-- **The mean-square deviation is `≤ q·(#dev)·B²` under a uniform period bound.**
Combining the Parseval identity `dev_l2_offset_eq` with `‖η_b‖ ≤ B` (`b ≠ 0`): each of the
`#dev` diagonal terms is `≤ B²`, so

  `∑_{s₀} ‖D(s₀)‖²  ≤  q · (#dev) · B²`.

(`B ≥ 0` is automatic from `‖η_b‖ ≤ B` whenever the support is nonempty; we carry it as a
hypothesis to keep the statement total, including the vacuous empty-support case.) -/
theorem dev_l2_offset_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₁ : F)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    (∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2)
      ≤ (Fintype.card F : ℝ) * ((deviationSupport s₁).card : ℝ) * B ^ 2 := by
  classical
  rw [dev_l2_offset_eq hψ G s₁]
  have hdiag : (∑ b ∈ deviationSupport s₁, ‖eta ψ G b‖ ^ 2)
      ≤ ∑ _b ∈ deviationSupport s₁, B ^ 2 := by
    refine Finset.sum_le_sum (fun b hb => ?_)
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    have hle := hB b hb0
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    nlinarith [hle, hnn, hB0]
  rw [Finset.sum_const, nsmul_eq_mul] at hdiag
  have hcardnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc (Fintype.card F : ℝ) * ∑ b ∈ deviationSupport s₁, ‖eta ψ G b‖ ^ 2
      ≤ (Fintype.card F : ℝ) * (((deviationSupport s₁).card : ℝ) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hdiag hcardnn
    _ = (Fintype.card F : ℝ) * ((deviationSupport s₁).card : ℝ) * B ^ 2 := by ring

/-- **The mean-square (per-offset average) deviation is `≤ (#dev)·B² ≤ q·B²`.**
Dividing `dev_l2_offset_le` by `q = |F| > 0`: the *average over offsets* of `‖D(s₀)‖²` is at most
`(#dev)·B²`, hence at most `q·B²`.  Equivalently the **root-mean-square deviation over the offset is
`≤ √(#dev)·B ≤ √q·B`** — the square-root-cancelled scale, achieved on average over `s₀`.  Contrast
the pointwise `IncidenceDeviationCharSum.incidence_dev_le` bound `(#dev)·B`: averaging over the
offset recovers a full factor `√(#dev)` for free (orthogonality), and the remaining gap to the prize
is purely the open sup-over-offset (`L²→L∞`) upgrade = BCHKS Conj 1.12. -/
theorem dev_meansq_offset_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₁ : F)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    (1 / (Fintype.card F : ℝ)) * (∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2)
      ≤ ((deviationSupport s₁).card : ℝ) * B ^ 2 := by
  classical
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F)
    exact_mod_cast this
  have hle := dev_l2_offset_le hψ G s₁ hB0 hB
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hq]
  calc (∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2)
      ≤ (Fintype.card F : ℝ) * ((deviationSupport s₁).card : ℝ) * B ^ 2 := hle
    _ = ((deviationSupport s₁).card : ℝ) * B ^ 2 * (Fintype.card F : ℝ) := by ring

/-- **The mean-square deviation is `≤ q·B²` (the explicit `√q·B` rms statement).**
Bounding `#dev ≤ q` (`IncidenceDeviationCharSum.deviationSupport_card_le`) in the mean-square bound:

  `(1/q) ∑_{s₀} ‖I(s₀,s₁) − |G||²  ≤  q · B²`,

i.e. the **rms-over-offset incidence deviation is `≤ √q · B`** — the prize-scale square-root
cancellation, UNCONDITIONALLY, on average over the line offset.  (Stated on the incidence deviation
directly via `devField_eq_incidence_sub_mean`.) -/
theorem incidence_dev_meansq_offset_le_sqrtq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₁ : F) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    (1 / (Fintype.card F : ℝ))
        * (∑ s₀ : F, ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖ ^ 2)
      ≤ (Fintype.card F : ℝ) * B ^ 2 := by
  classical
  -- rewrite the incidence deviation back to devField
  have hrw : (∑ s₀ : F, ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖ ^ 2)
      = ∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun s₀ _ => ?_)
    rw [devField_eq_incidence_sub_mean hψ G s₀ s₁]
  rw [hrw]
  have hmsq := dev_meansq_offset_le hψ G s₁ hB0 hB
  have hcard : ((deviationSupport s₁).card : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast deviationSupport_card_le s₁
  have hBsq : (0 : ℝ) ≤ B ^ 2 := by positivity
  calc (1 / (Fintype.card F : ℝ)) * (∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2)
      ≤ ((deviationSupport s₁).card : ℝ) * B ^ 2 := hmsq
    _ ≤ (Fintype.card F : ℝ) * B ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcard hBsq

end ArkLib.ProximityGap.IncidenceDevL2Offset

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.IncidenceDevL2Offset.dev_l2_offset_eq
#print axioms ArkLib.ProximityGap.IncidenceDevL2Offset.dev_l2_offset_le
#print axioms ArkLib.ProximityGap.IncidenceDevL2Offset.dev_meansq_offset_le
#print axioms ArkLib.ProximityGap.IncidenceDevL2Offset.incidence_dev_meansq_offset_le_sqrtq
