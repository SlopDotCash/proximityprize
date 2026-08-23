/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# The far-coset explosion law (#357, items 18/19 — the binding side of B6 = 7)

The general law behind the first exact explosion-band value
(`probe_band3_exact_value.py`: `ε_mca(RS[F₁₇,⟨2⟩,4], 1/4) = 7/17`):

**`mcaEvent_iff_line_explainable`** — when no codeword agrees with `u₁` on any
witness-sized set (the *far-coset* condition: `u₁`'s coset minimum weight exceeds
the witness slack `n − ⌈(1−δ)n⌉`), the no-joint clause of `mcaEvent` is automatic,
and badness degenerates to **pure line-explainability**: `γ` is bad iff the line
`u₀ + γ·u₁` agrees with some codeword on a witness-sized set.

This is the binding side of the explosion-band dichotomy: for far cosets the bad
count equals the line–`W` syndrome incidence (the geometry that attains `7` at the
band-3 instance, beating the joint-corrected near-coset count `6` and the pencil
supply `4`).  The near-coset side (unique representatives below half distance, the
per-γ support criterion) is the probe-verified complement.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The far-coset condition**: no codeword agrees with `u₁` on any witness-sized
set.  For a code of distance `d` this holds whenever the coset minimum weight of
`u₁` exceeds the witness slack `n − ⌈(1−δ)n⌉`. -/
def FarFromCode (C : Set (ι → A)) (δ : ℝ≥0) (u₁ : ι → A) : Prop :=
  ∀ c ∈ C, ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
    ∃ i ∈ S, c i ≠ u₁ i

/-- **The far-coset explosion law**: for far `u₁`, the `mcaEvent` degenerates to pure
line-explainability — the no-joint clause is automatic, every explainable scalar is
bad.  The bad count becomes the line–syndrome incidence, the binding object of the
explosion regime. -/
theorem mcaEvent_iff_line_explainable (C : Set (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (hfar : FarFromCode C δ u₁) (γ : F) :
    mcaEvent (F := F) C δ u₀ u₁ γ ↔
      ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i := by
  constructor
  · rintro ⟨S, hsz, hline, -⟩
    exact ⟨S, hsz, hline⟩
  · rintro ⟨S, hsz, hline⟩
    refine ⟨S, hsz, hline, ?_⟩
    rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    obtain ⟨i, hi, hne⟩ := hfar v₁ hv₁ S hsz
    exact hne (hag i hi).2

open Classical in
/-- The numeric face: for far `u₁`, the bad-scalar set IS the explainable-scalar
set — exact equality of the two filters. -/
theorem badScalars_eq_explainable (C : Set (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (hfar : FarFromCode C δ u₁) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ u₀ u₁ γ))
      = (Finset.univ.filter (fun γ : F =>
          ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)) := by
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mcaEvent_iff_line_explainable C δ hfar γ

open Classical in
/-- **THE INCIDENCE LOWER BOUND — the top-down attack surface.**  For any far
direction `u₁` and any offset `u₀`, the MCA error at radius `δ` is at least the
line-explainability count over `q`:

  `ε_mca(C, δ) ≥ #{γ : u₀ + γ·u₁ agrees with C on a witness-sized set} / q`.

For linear `C` this count is the incidence of the affine line
`syn(u₀) + γ·syn(u₁)` with the weight-`⌊δn⌋` syndrome ball — so pinning `δ*` from
above is EXACTLY the construction of high-incidence lines with far directions, and
pinning from below is exactly bounding the maximum such incidence.  (Far directions
exist at every radius below capacity: any `u₁` beyond covering-slack distance.) -/
theorem epsMCA_ge_far_incidence (C : Set (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (hfar : FarFromCode C δ u₁) :
    ((Finset.univ.filter (fun γ : F =>
        ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := A) C δ := by
  rw [← badScalars_eq_explainable C δ hfar]
  exact ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set C δ ![u₀, u₁]
    _ (fun γ hγ => by
      have := (Finset.mem_filter.mp hγ).2
      simpa using this)

end ProximityGap.FarCosetExplosion

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FarCosetExplosion.mcaEvent_iff_line_explainable
#print axioms ProximityGap.FarCosetExplosion.badScalars_eq_explainable
#print axioms ProximityGap.FarCosetExplosion.epsMCA_ge_far_incidence
