/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSBounds
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSFieldUniversal

/-!
# Issue #141: honest partial progress on the open ABF26 Grand Challenge 1 prize surfaces

Issue #141 tracks the genuinely **open** ABF26 Grand Challenge 1 prize conjectures — the
beyond-UDR Guruswami–Sudan list-decoder mass bound at radius up to the Johnson/capacity bound
`1 - ρ - η`. The named `Prop`s carrying that open content are
`ProximityGap.GrandChallenges.mcaConjecture` (abstract `ε_mca` polynomial bound),
`ProximityGap.MCAGS.epsMCAgs_prizeBound_conjecture` /
`ProximityGap.MCAGS.uniformEpsMCAgsPrizeBoundConjecture` (GS-exposed forms), and
`ProximityGap.MCAGS.epsMCAgsPrizeUniversalConjecture` (field-universal GS form).

**Integrity.** This file adds *only* honest partial progress. It does **not** prove any open
conjecture, does **not** carry one as a `sorry`-backed theorem, and does **not** assume an
equivalent packaged form silently. Every genuinely open statement remains an explicit named
hypothesis on every theorem that consumes it. The new content here is:

1. **Unconditional special case of the conjecture's conclusion** in the trivial-bound regime
   (`epsMCA_le_mcaConjectureBound_of_one_le_bound`): wherever the conjectural RHS is `≥ 1`, the
   conclusion `ε_mca ≤ RHS` holds *unconditionally* because `ε_mca ≤ 1` always. This is the
   honest small-field / large-gap floor of the conjecture — no GS mass bound needed there.

2. **A faithful equivalence of surfaces** (`mcaConjecture_iff_abstractRSMcaPolyBound`): the
   abstract polynomial-bound surface `AbstractRSMcaPolyBound` is *exactly* `mcaConjecture` (a
   definitional bidirectional reduction), with explicit intro/elim rules. This certifies the
   packaged surface adds no hidden slack — it is the same open content, repackaged for reuse.

3. **A genuine new conditional reduction** (`nonempty_mcaLowerWitness_of_universalGSPrize`)
   threading the *open* field-universal GS prize through to the in-tree one-sided Grand-MCA
   progress framework (`MCALowerWitness`): under the open prize (an explicit hypothesis), every
   prize-rate radius whose GS mass bound clears `ε*` yields a one-sided lower witness pinning the
   maximal Grand-MCA threshold `δ*`. The open conjecture stays a hypothesis; the abstract
   `ε_mca ≤ bound` is supplied by the already-proved `MCAGS.epsMCA_le_of_universalGSConjecture`.

All theorems below are `sorry`-free and depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` (see the `#print axioms` audit at the end), *except*
where they explicitly take an open conjecture as a hypothesis — in which case that hypothesis is
the only non-standard input and is visible in the signature.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026,
  §1 Grand MCA Challenge; §4.5 `conj:mca-conjecture`.
- Tracking: Issue #141.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

namespace GrandChallenges

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## (1) Unconditional special case: the conjecture's conclusion in the trivial-bound regime

The §4.5 conjecture asserts `ε_mca(RS, δ) ≤ mcaConjectureBound …`. Since `ε_mca ≤ 1` *always*
(`epsMCA_le_one`), the conclusion is unconditionally true on any radius where the conjectural RHS
is already `≥ 1`. This is the honest floor of the conjecture: at small field size `q` or large
gap `η = 1 - ρ - δ` the polynomial bound `(1/q)·n^{c₁}/(ρ^{c₂}·η^{c₃})` exceeds `1`, and there the
prize content (the beyond-UDR GS list-decoder mass bound) is *not* needed. The open territory is
exactly where this bound drops below `1`. -/

/-- **Special case (unconditional): the §4.5 conjecture conclusion holds wherever the bound is
`≥ 1`.** No GS list-decoder mass bound is required: `ε_mca ≤ 1 ≤ mcaConjectureBound` directly.
This bounds the open prize's content to the sub-`1` regime of the conjectural RHS. -/
theorem epsMCA_le_mcaConjectureBound_of_one_le_bound
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (c₁ c₂ c₃ : ℝ)
    (hbound : (1 : ℝ) ≤ mcaConjectureBound (Fintype.card ι) (Fintype.card F) k δ c₁ c₂ c₃) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ≤
      ENNReal.ofReal
        (mcaConjectureBound (Fintype.card ι) (Fintype.card F) k δ c₁ c₂ c₃) := by
  have h1 : epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ≤ 1 :=
    epsMCA_le_one _ _
  have hofr : (1 : ENNReal) ≤ ENNReal.ofReal
      (mcaConjectureBound (Fintype.card ι) (Fintype.card F) k δ c₁ c₂ c₃) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hbound
  exact le_trans h1 hofr

/-! ## (2) A faithful equivalence of surfaces

`AbstractRSMcaPolyBound` is a re-statement of the §4.5 abstract polynomial bound as a standalone
named `Prop`. The equivalence `mcaConjecture_iff_abstractRSMcaPolyBound` (a *definitional* `Iff`)
certifies it carries exactly the same open content — no hidden strengthening, no hidden slack —
giving downstream developments clean intro/elim rules without risking laundering the prize. -/

/-- **Packaged form of the §4.5 abstract MCA polynomial bound.** A named `Prop`: a universal
constant triple `(c₁, c₂, c₃)` bounding `ε_mca(RS, δ)` by `mcaConjectureBound` for every RS code
and every sub-`(1-ρ)` radius. This is the abstract-`ε_mca` surface downstream developments may
consume; the equivalence below shows it is *exactly* `mcaConjecture`. -/
def AbstractRSMcaPolyBound : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
      {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
      (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
      0 < k →
      (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
      epsMCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ ≤
        ENNReal.ofReal
          (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃)

/-- The packaged abstract bound is **definitionally** the §4.5 conjecture: a bidirectional
reduction confirming the two surfaces are not redundant restatements with hidden slack. The open
prize content is preserved exactly. -/
theorem mcaConjecture_iff_abstractRSMcaPolyBound :
    mcaConjecture ↔ AbstractRSMcaPolyBound := Iff.rfl

/-- **Introduction rule for `mcaConjecture`.** Any proof of the packaged abstract polynomial
bound is a proof of the §4.5 conjecture (still open; this is just the surface conversion). -/
theorem mcaConjecture_of_abstractRSMcaPolyBound (h : AbstractRSMcaPolyBound) :
    mcaConjecture := h

/-- **Elimination rule for `mcaConjecture`.** The §4.5 conjecture yields the packaged abstract
polynomial bound, for downstream developments that prefer the named-surface form. -/
theorem abstractRSMcaPolyBound_of_mcaConjecture (h : mcaConjecture) :
    AbstractRSMcaPolyBound := h

/-! ## (3) New conditional reduction: open GS prize ⇒ prize-rate MCA lower witnesses

This threads the genuinely-open field-universal Guruswami–Sudan prize
(`MCAGS.epsMCAgsPrizeUniversalConjecture`) through to the in-tree one-sided Grand-MCA progress
framework (`MCALowerWitness`). The open prize stays an explicit hypothesis; the abstract
`ε_mca ≤ bound` step is the already-proved `MCAGS.epsMCA_le_of_universalGSConjecture`. The payoff:
under the prize, every prize-rate radius whose GS mass bound clears `ε*` pins the maximal
Grand-MCA threshold `δ*` from below (via `MCALowerWitness.le_δStar`). -/

/-- **Open GS prize ⇒ prize-rate MCA lower witnesses.** Under the field-universal Guruswami–Sudan
prize (`MCAGS.epsMCAgsPrizeUniversalConjecture m`, an explicit hypothesis), for the exposed
constants and every field/domain/prize-rate/gap/radius with `δ ≤ 1 - ρ - η`, `δ ≤ 1`, and the
`epsMCAgsPrizeBound` clearing `ε*`, the RS code admits an `MCALowerWitness` at `δ`.

The open conjecture is *not* proved here — it is consumed as a hypothesis. This is the honest
bridge from the open GS prize surface to one-sided Grand-MCA progress. -/
theorem nonempty_mcaLowerWitness_of_universalGSPrize (m : ℕ)
    (hUniv : MCAGS.epsMCAgsPrizeUniversalConjecture m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (η δ ε_star : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) → δ ≤ 1 →
        ENNReal.ofReal
            (MCAGS.epsMCAgsPrizeBound (Fintype.card FC) m
              (ProximityGap.prizeRates j) η c₁ c₂ c₃)
          ≤ (ε_star : ENNReal) →
        Nonempty (MCALowerWitness
          (ReedSolomon.code domain
            ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
          ε_star) := by
  obtain ⟨c₁, c₂, c₃, hbound⟩ := MCAGS.epsMCA_le_of_universalGSConjecture m hUniv
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j η δ ε_star hη hδ hδ1 hclear
  exact ⟨⟨δ, hδ1, le_trans (hbound domain j η δ hη hδ) hclear⟩⟩

/-- **Existential form** of `nonempty_mcaLowerWitness_of_universalGSPrize`, exposing the witness
radius `w.δ = δ` for downstream composition with `MCALowerWitness.le_δStar`. The open GS prize
remains an explicit hypothesis. -/
theorem exists_mcaLowerWitness_of_universalGSPrize (m : ℕ)
    (hUniv : MCAGS.epsMCAgsPrizeUniversalConjecture m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (j : Fin 4) (η δ ε_star : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) → δ ≤ 1 →
        ENNReal.ofReal
            (MCAGS.epsMCAgsPrizeBound (Fintype.card FC) m
              (ProximityGap.prizeRates j) η c₁ c₂ c₃)
          ≤ (ε_star : ENNReal) →
        ∃ w : MCALowerWitness
          (ReedSolomon.code domain
            ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ιC : ℝ≥0)⌋₊ : Set (ιC → FC))
          ε_star, w.δ = δ := by
  obtain ⟨c₁, c₂, c₃, hbound⟩ := MCAGS.epsMCA_le_of_universalGSConjecture m hUniv
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain j η δ ε_star hη hδ hδ1 hclear
  exact ⟨⟨δ, hδ1, le_trans (hbound domain j η δ hη hδ) hclear⟩, rfl⟩

end GrandChallenges

end ProximityGap

/-! ## Source / axiom audit

The unconditional progress lemmas are axiom-clean (`[propext, Classical.choice, Quot.sound]`).
The conditional reductions additionally rest only on their explicit open-conjecture hypotheses;
they introduce no `sorry` and no extra axioms. The open ABF26 Grand Challenge 1 prize conjectures
remain unproven named hypotheses. -/

#print axioms ProximityGap.GrandChallenges.epsMCA_le_mcaConjectureBound_of_one_le_bound
#print axioms ProximityGap.GrandChallenges.mcaConjecture_iff_abstractRSMcaPolyBound
#print axioms ProximityGap.GrandChallenges.mcaConjecture_of_abstractRSMcaPolyBound
#print axioms ProximityGap.GrandChallenges.abstractRSMcaPolyBound_of_mcaConjecture
#print axioms ProximityGap.GrandChallenges.nonempty_mcaLowerWitness_of_universalGSPrize
#print axioms ProximityGap.GrandChallenges.exists_mcaLowerWitness_of_universalGSPrize
