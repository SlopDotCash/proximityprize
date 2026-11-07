/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.AHIV22

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen, Elias Judin,
  Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ProximityGap.AHIV22Support
import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding

/-!
## Main Definitions
- Statements of proximity results for Reed Solomon codes (`Lemma 4.3`, `Lemma 4.4` and `Lemma 4.5`
   from `[AHIV22]`

## References

* [Ames, S., Hazay, C., Ishai, Y., and Venkitasubramaniam, M., *Ligero: Lightweight sublinear
    arguments without a trusted setup*][AHIV22]
      * NB we use version 20221118:030830
-/

noncomputable section

open Code ProbabilityTheory

-- `Pr_{...}[...]` notation is universe-restricted (requires `F : Type`).
variable {F : Type} [Field F] [Finite F] [DecidableEq F]
         {κ : Type*} [Fintype κ]
         {ι : Type} [Fintype ι]

local instance localInstance_AHIV22_1 : Fintype F := Fintype.ofFinite F

-- This mathematical interface assumes only a finite field. Keep the fallback module-local.
local instance (priority := 10) ahivFiniteSampler : SampleableType F :=
  SampleableType.ofFintype F

namespace ProximityToRS
open ReedSolomon NNReal

-- We first prove the distance-bound form `e_le_dist_over_3_strong` and then derive the
-- mutual-exclusion corollary `e_le_dist_over_3` from it.
/-- If every point on a nondegenerate affine line is close and the field is larger than the
Reed-Solomon minimum distance, then the line cannot have only few close points. -/
private lemma all_close_not_few_close_pts
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (hv : v ≠ 0)
    (hFd : ‖(RScodeSet α deg)‖₀ < Fintype.card F)
    (h_all :
      ∀ x ∈ Affine.affineLineAtOrigin (F := F) u v, Δ₀(x, ReedSolomon.code α deg) ≤ e) :
    ¬numberOfClosePts u v deg α e ≤ ‖(RScodeSet α deg)‖₀ := by
  intro h_few
  have hnum_ge : Fintype.card F ≤ numberOfClosePts (F := F) (ι := ι) u v deg α e := by
    have hex : ∃ j, v j ≠ 0 := by
      by_contra h
      apply hv
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    rcases hex with ⟨j, hj⟩
    let g : F → closePtsOnAffineLine (F := F) (u := u) (v := v)
        (deg := deg) (α := α) (e := e) :=
      fun r ↦
        ⟨u + r • v, by
            refine ⟨?_, ?_⟩
            · refine
                (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u) (direction := v) _).2 ?_
              exact ⟨r, rfl⟩
            · apply h_all
              refine
                (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u) (direction := v) _).2 ?_
              exact ⟨r, rfl⟩⟩
    have hg_inj : Function.Injective g := by
      intro r₁ r₂ hr
      have hval : u + r₁ • v = u + r₂ • v := congrArg Subtype.val hr
      have hmul : r₁ * v j = r₂ * v j := by
        have := congrArg (fun f : ι → F ↦ f j) hval
        simpa [Pi.add_apply, Pi.smul_apply] using add_left_cancel this
      exact mul_right_cancel₀ hj hmul
    have hnat :
        Nat.card F ≤ Nat.card
          (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) :=
      Nat.card_le_card_of_injective g hg_inj
    have hnum :
        numberOfClosePts (F := F) (ι := ι) u v deg α e =
          Nat.card
            (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) :=
      by simpa using number_of_close_pts_eq_nat_card (F := F) (ι := ι) u v deg α e
    have hcardF : Fintype.card F = Nat.card F := by
      exact (Fintype.card_eq_nat_card (α := F))
    calc
      Fintype.card F = Nat.card F := hcardF
      _ ≤ Nat.card
            (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) :=
        hnat
      _ = numberOfClosePts (F := F) (ι := ι) u v deg α e := hnum.symm
  have hcardF_le : Fintype.card F ≤ ‖(RScodeSet α deg)‖₀ := le_trans hnum_ge h_few
  exact (not_lt_of_ge hcardF_le) hFd

/-- Named residual for the AHIV17/AHIV22 source-to-interface gap.

The current in-tree AHIV22 proof is the row-span probability theorem `prob_of_bad_pts`; ABF26
T4.8 needs this affine-line correlated-agreement predicate for Reed-Solomon codes before the
generic `epsCA` bridge applies.  This `Prop` names that remaining specialization target
without claiming it is already proved by the row-span theorem. -/
def ahiv17_affineLine_correlatedAgreement_residual
    [Nonempty ι]
    (deg : ℕ) (α : ι ↪ F) (δ ε : ℝ≥0) : Prop :=
  ProximityGap.δ_ε_correlatedAgreementAffineLines
    (F := F) (A := F) (C := RScodeSet α deg) δ ε

/-- **ABF26 Theorem 4.8 / AHIV17 unique-decoding bound — `epsCA` interface wrapper.**

The current AHIV22 development proves the unique-decoding row-span probability theorem
`prob_of_bad_pts` above.  The ABF26 Section 4 survey consumes the affine-line
correlated-agreement statement through the numeric `epsCA` API.  This wrapper records the
checked final interface step: once the AHIV17/AHIV22 affine-line correlated-agreement predicate
is available for the Reed-Solomon code, the corresponding `epsCA` inequality follows by the
generic bridge in `Errors.lean`.

The remaining theorem-port work, if any, is therefore the source-level specialization from the
row-span AHIV22 lemma to `δ_ε_correlatedAgreementAffineLines`; this declaration does not
pretend that step is already hidden in `prob_of_bad_pts`. -/
theorem ahiv17_epsCA_bound
    [Nonempty ι]
    {deg : ℕ} {α : ι ↪ F} {δ ε : ℝ≥0}
    (hAHIV : ProximityGap.δ_ε_correlatedAgreementAffineLines
      (F := F) (A := F) (C := RScodeSet α deg) δ ε) :
    ProximityGap.epsCA (F := F) (A := F) (RScodeSet α deg) δ δ ≤ (ε : ENNReal) := by
    classical
    exact (ProximityGap.δ_ε_correlatedAgreementAffineLines_iff_epsCA_le
      (F := F) (A := F) (C := RScodeSet α deg) δ ε).mp hAHIV

/-- ABF26 T4.8 `epsCA` wrapper from the named AHIV17/AHIV22 affine-line residual. -/
theorem ahiv17_epsCA_bound_of_affineLine_residual
    [Nonempty ι]
    {deg : ℕ} {α : ι ↪ F} {δ ε : ℝ≥0}
    (hAHIV : ahiv17_affineLine_correlatedAgreement_residual deg α δ ε) :
    ProximityGap.epsCA (F := F) (A := F) (RScodeSet α deg) δ δ ≤ (ε : ENNReal) :=
  ahiv17_epsCA_bound (deg := deg) (α := α) (δ := δ) (ε := ε) hAHIV

/-! ### AHIV17/AHIV22 tighter `d/q` residual (issue #88)

The row-span theorem `prob_of_bad_pts` proves a `‖RS‖₀ / |F|` probability bound for AHIV22's
row-span sample space.  The remaining #88 source-to-interface work is to identify that row-span
event with the affine-line correlated-agreement predicate consumed by ABF26.  We name exactly
that target at the tighter `d/q` error level and provide the final checked `epsCA` wrapper below.
-/

/-- **#88 residual.** The AHIV22 row-span probability theorem, specialized all the way to the
ABF26 affine-line correlated-agreement predicate at the tighter AHIV error level
`‖RScodeSet α deg‖₀ / |F|`.

This is intentionally still a residual: it is the missing row-span-to-affine-line event
identification, not a consequence of the already-proven unique-decoding wrapper. -/
def ahiv17_rowSpan_to_affineLine_dOverQ_residual
    [Nonempty ι]
    (deg : ℕ) (α : ι ↪ F) (δ : ℝ≥0)
    (_hδ : (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℚ≥0) < ‖RScodeSet α deg‖₀ / 3) : Prop :=
    ahiv17_affineLine_correlatedAgreement_residual deg α δ
      ((‖RScodeSet α deg‖₀ : ℝ≥0) / (Fintype.card F : ℝ≥0))

/-- **ABF26 T4.8 at the tighter AHIV `d/q` error level, conditional on the #88 bridge.**
Once the row-span-to-affine-line specialization is supplied, the generic `epsCA` bridge gives

`epsCA (RScodeSet α deg) δ δ ≤ ‖RScodeSet α deg‖₀ / |F|`.

The only hypothesis here is the numeric bound on δ; the wrapper itself is fully checked. -/
theorem ahiv17_epsCA_bound_of_rowSpan_to_affineLine_dOverQ_residual
    [Nonempty ι]
    {deg : ℕ} {α : ι ↪ F} {δ : ℝ≥0}
    (hδ : (⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℚ≥0) < ‖RScodeSet α deg‖₀ / 3)
    (hAHIV : ahiv17_rowSpan_to_affineLine_dOverQ_residual deg α δ hδ) :
    ProximityGap.epsCA (F := F) (A := F) (RScodeSet α deg) δ δ ≤
      (((‖RScodeSet α deg‖₀ : ℝ≥0) / (Fintype.card F : ℝ≥0)) : ENNReal) := by
    have hF_ne : (Fintype.card F : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
    simpa [ENNReal.coe_div hF_ne] using
      (ahiv17_epsCA_bound_of_affineLine_residual (deg := deg) (α := α) (δ := δ)
        (ε := ((‖RScodeSet α deg‖₀ : ℝ≥0) / (Fintype.card F : ℝ≥0)))
        hAHIV)

/-! ### Unique-decoding-regime instantiation (fully proven, no residual)

The named affine-line residual **holds** in the unique-decoding regime: `RScodeSet α deg`
is a definitional abbrev for `ReedSolomon.code α deg` (`ReedSolomon.lean`), so the BCIKS20
affine-lines base case `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` discharges
`ahiv17_affineLine_correlatedAgreement_residual` at `ε = errorBound δ deg α` whenever
`δ ≤ relUDR(RS)`.  Chaining through the `epsCA` bridge yields the fully-proven (non-residual)
ABF26 T4.8 bound for the unique-decoding regime.

Caveat (kept as the named residual above): this lands the BCIKS20 UDR error bound
`errorBound δ deg α = n/q`; the tighter AHIV17 bound `d/q = ‖RS‖₀/q` from `prob_of_bad_pts`
still requires the row-span → affine-line specialization tracked by
`ahiv17_affineLine_correlatedAgreement_residual`. -/

/-- The named affine-line residual, **discharged** in the unique-decoding regime by
`ProximityGap.RS_correlatedAgreement_affineLines_uniqueDecodingRegime` (definitional match
via the `RScodeSet` abbrev). -/
theorem ahiv17_affineLine_residual_uniqueDecodingRegime
    [Nonempty ι]
    {deg : ℕ} {α : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code α deg)) :
    ahiv17_affineLine_correlatedAgreement_residual deg α δ
      (ProximityGap.errorBound δ deg α) :=
  ProximityGap.RS_correlatedAgreement_affineLines_uniqueDecodingRegime
    (deg := deg) (domain := α) (δ := δ) hδ

/-- **ABF26 Theorem 4.8 / AHIV17 — unique-decoding regime, fully proven.**

For `δ ≤ relUDR(RS[F, α, deg])`, the `epsCA` bound
`epsCA (RScodeSet α deg) δ δ ≤ errorBound δ deg α` holds with **no residual hypothesis**:
the affine-line correlated agreement is supplied by the proven BCIKS20 unique-decoding base
case and routed through the generic `epsCA` bridge. -/
theorem ahiv17_epsCA_bound_uniqueDecodingRegime
    [Nonempty ι]
    {deg : ℕ} {α : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code α deg)) :
    ProximityGap.epsCA (F := F) (A := F) (RScodeSet α deg) δ δ
      ≤ (ProximityGap.errorBound δ deg α : ENNReal) :=
  ahiv17_epsCA_bound_of_affineLine_residual
    (ahiv17_affineLine_residual_uniqueDecodingRegime hδ)

/-- **#80 (unique-decoding regime, proven).** Explicit-argument form of
`ahiv17_affineLine_residual_uniqueDecodingRegime`: in the unique-decoding regime
`δ ≤ relUDR(RS)`, the AHIV17/T4.8 affine-line correlated-agreement residual holds at
`ε = errorBound δ deg α`, discharged by the BCIKS20 affine-lines base case.

This lands the BCIKS20 unique-decoding bound `errorBound δ deg α`; the tighter AHIV17 `‖RS‖₀/q`
bound remains the separate row-span-to-affine-line specialization work. -/
theorem ahiv17_affineLine_correlatedAgreement_residual_uniqueDecodingRegime
    [Nonempty ι] (deg : ℕ) (α : ι ↪ F) {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code α deg)) :
    ahiv17_affineLine_correlatedAgreement_residual deg α δ (ProximityGap.errorBound δ deg α) :=
  ahiv17_affineLine_residual_uniqueDecodingRegime hδ

#print axioms ProximityToRS.prob_of_bad_pts
#print axioms ProximityToRS.ahiv17_affineLine_correlatedAgreement_residual
#print axioms ProximityToRS.ahiv17_epsCA_bound
#print axioms ProximityToRS.ahiv17_epsCA_bound_of_affineLine_residual
#print axioms ProximityToRS.ahiv17_rowSpan_to_affineLine_dOverQ_residual
#print axioms ProximityToRS.ahiv17_epsCA_bound_of_rowSpan_to_affineLine_dOverQ_residual
#print axioms ProximityToRS.ahiv17_affineLine_residual_uniqueDecodingRegime
#print axioms ProximityToRS.ahiv17_affineLine_correlatedAgreement_residual_uniqueDecodingRegime
#print axioms ProximityToRS.ahiv17_epsCA_bound_uniqueDecodingRegime
end ProximityToRS
end
