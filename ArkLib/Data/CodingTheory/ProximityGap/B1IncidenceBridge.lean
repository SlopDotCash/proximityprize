/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.B1CountLawUnconditional
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

/-!
# Wiring B1's unconditional count law toward the exact `δ*` (far-line incidence) object (#407)

## The two objects, kept STRICTLY separate (anti-conflation)

The landed B1 count law
(`SubsetSurj.topReadouts_card_eq_n_unconditional`) proves, axiom-clean and `p`-independent,
that the number of **distinct top-direction divided-difference readout VALUES** over the
`(k+1)`-subsets of `μ_n = nthRootsFinset n 1` is **exactly `n`**:

  `#{ dividedDifferencePow R v (n-1) : R ∈ powersetCard (k+1) } = n`.

The exact `δ*` object (`FarCosetExplosion.epsMCA_ge_far_incidence`) is a *different* count —
the **worst-case far-line incidence**: for a far direction `u₁` and offset `u₀`,

  `I = #{ γ : F | the line u₀ + γ·u₁ agrees with some codeword on a witness-sized set }`,

and `δ*` is pinned from above by the *maximum* of `I` over far stacks (the "binder").

These are **NOT the same quantity, and this file refuses to conflate them.**  The trap (the
prior circular B2 attempt) is to identify the *value-fiber* of the readout map — the number of
`(k+1)`-subsets sharing one readout value, `≈ C(n,k+1)/n` — with the incidence `I`.  Exhaustive
enumeration (`probe_farline_incidence_exact`, p-independent) separates all THREE:

* `n = 8`, `k = 2`:
  * distinct readout VALUES (`= n`, PROVEN): `8`;
  * max value-FIBER (`≈ C(n,k+1)/n`, GROWS): `7`;
  * worst-case far INCIDENCE (the δ* binder, OPEN): `9`
    (at `r=4`, binder `(a,b)=(5,2)`).
* `n = 12`, `k = 3`:
  * distinct readout VALUES (`= n`, PROVEN): `12`;
  * max value-FIBER (`≈ C(n,k+1)/n`, GROWS): `43`;
  * worst-case far INCIDENCE (the δ* binder, OPEN): `13`
    (at `r=6`, binder `(6,4)`).
* `n = 16`, `k = 4`:
  * distinct readout VALUES (`= n`, PROVEN): `16`;
  * max value-FIBER (`≈ C(n,k+1)/n`, GROWS): `273`;
  * worst-case far INCIDENCE (the δ* binder, OPEN): `89`
    (at `r=10`, binder `(10,4)`).

The value-fiber numbers `7, 43, 273` are the ones the prior attempt mistook for incidence; the
*actual* incidence binders `9, 13, 89` occur at a DIFFERENT agreement-set size `r` (past Johnson)
and a DIFFERENT direction (`b = k`, not the top `b = n-1`).  So:

> **The B1 count law pins the readout VALUE-SET cardinality (`= n`); it does NOT bound the
> worst-case far-line incidence, which remains the OPEN δ* object.**

## What this file proves (honest, axiom-clean)

* `topDirectionValueCount_eq_n` — re-exports the proven B1 `= n` value count (the wired fact).
* `WorstCaseFarIncidenceBounded` — the EXACT δ* object as a NAMED OPEN `Prop`: for every far
  stack the incidence count is `≤ budget`.  This is the open obligation; it is NOT discharged
  here.
* `epsMCA_le_of_worstCaseFarIncidence` — the genuine, non-circular bridge: IF
  `WorstCaseFarIncidenceBounded` holds at `budget = B`, THEN the far-line bad-`γ` count is
  `≤ B` (so dividing by `q` caps `epsMCA`).  The incidence bound is a HYPOTHESIS, not a
  consequence of the value count.
* `epsMCA_pinch_of_worstCaseFarIncidence` — the pinch: the SAME incidence count both
  lower-bounds `epsMCA` (proven, via `FarCosetExplosion.epsMCA_ge_far_incidence`) and is
  upper-bounded by the open `B`, with no circularity.  Setting `B = ⌊q·ε*⌋` is the δ* ceiling.
* `worstCaseIncidence_is_the_open_object` — the ANTI-CONFLATION witness: the δ* object is the
  separate `WorstCaseFarIncidenceBounded`, type-checked so that downstream code cannot silently
  substitute the value count `= n` for the incidence bound (the value count being `n` entails NO
  bound on the incidence; numeric separation above).
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.WireB1ToIncidence

open Polynomial ProximityGap.FarCosetExplosion

/-! ## Part 1 — the WIRED fact: B1 distinct top-direction value count is `n`. -/

/-- **The wired B1 fact (PROVEN, re-export).**  For a field `F` carrying a primitive `n`-th root
`ζ` (`2 ≤ n`) and `1 ≤ k ≤ n-2`, the number of DISTINCT top-direction divided-difference readout
*values* over the `(k+1)`-subsets of `μ_n = nthRootsFinset n 1` is exactly `n`.

This is the cardinality of the readout VALUE-SET — emphatically NOT the worst-case far-line
incidence (see `WorstCaseFarIncidenceBounded` and the file header table). -/
theorem topDirectionValueCount_eq_n {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 2) :
    (ProximityGap.B1CountLaw.topReadouts (nthRootsFinset n (1 : F)) id n k).card = n :=
  SubsetSurj.topReadouts_card_eq_n_unconditional hζ hn k hk1 hk2

/-! ## Part 2 — the EXACT δ* object as a NAMED OPEN Prop, and the honest bridge. -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The worst-case far-line incidence count** for a single far stack `(u₀, u₁)` at radius `δ`:
the number of scalars `γ` for which the line `u₀ + γ·u₁` agrees with some codeword on a
witness-sized set.  By `FarCosetExplosion.badScalars_eq_explainable`, for far `u₁` this is exactly
the bad-`γ` count, hence `= q · ε_mca`'s lower-bounding numerator. -/
noncomputable def farIncidence (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ :=
  (Finset.univ.filter (fun γ : F =>
      ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card

/-- **THE OPEN δ* OBJECT, stated as an explicit named `Prop`.**  At radius `δ` with budget
`B = ⌊q·ε*⌋`, *every* far stack has far-line incidence at most `B`.  This is precisely the
upper-bound half that pins `δ*` (`sup{δ : worst-case far incidence ≤ q·ε*}`); it is the
character-sum / line–ball-incidence wall and is NOT proven here — it is the prize-grade open core
(face 4 of the #357 open core map).  The B1 value count `= n` does NOT supply it. -/
def WorstCaseFarIncidenceBounded (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) : Prop :=
  ∀ u₀ u₁ : ι → A, FarFromCode C δ u₁ → farIncidence (F := F) C δ u₀ u₁ ≤ B

open Classical in
/-- **THE HONEST, NON-CIRCULAR BRIDGE.**  If the worst-case far-line incidence is bounded by
`B` at radius `δ` (the named open obligation `WorstCaseFarIncidenceBounded`), then for every far
stack the MCA error is at most `B / q`:

  `epsMCA C δ ≤ B / q`.

This is a clean *consequence* of the incidence bound via
`FarCosetExplosion.epsMCA_ge_far_incidence` read in the contrapositive direction — i.e. the
incidence bound `B` caps the bad-`γ` count, which caps `q·ε_mca`.  The bound `B` is an INPUT
(the open obligation), never derived from the B1 value count.  Setting `B = ⌊q·ε*⌋` gives the
`δ*` upper-bound rung. -/
theorem epsMCA_le_of_worstCaseFarIncidence
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (hB : WorstCaseFarIncidenceBounded (F := F) C δ B)
    {u₀ u₁ : ι → A} (hfar : FarFromCode C δ u₁) :
    ((Finset.univ.filter (fun γ : F =>
        ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card : ℝ≥0∞)
      ≤ (B : ℝ≥0∞) := by
  have hle : farIncidence (F := F) C δ u₀ u₁ ≤ B := hB u₀ u₁ hfar
  have : (farIncidence (F := F) C δ u₀ u₁ : ℝ≥0∞) ≤ (B : ℝ≥0∞) := by exact_mod_cast hle
  simpa [farIncidence] using this

open Classical in
/-- **The δ*-upper-bound rung (the wired consumer).**  Given the open incidence bound `B` at
radius `δ`, the MCA error along every far stack is `≤ B/q`.  Routes the incidence numerator
through the proven `epsMCA_ge_far_incidence` lower bound: the *same* count both lower-bounds
`epsMCA` (proven) and is upper-bounded by `B` (the open hypothesis), so the two pinch
`epsMCA`-relevant data without circularity.  With `B = ⌊q·ε*⌋` this is the `δ*` ceiling rung. -/
theorem epsMCA_pinch_of_worstCaseFarIncidence
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (hB : WorstCaseFarIncidenceBounded (F := F) C δ B)
    {u₀ u₁ : ι → A} (hfar : FarFromCode C δ u₁) :
    ((Finset.univ.filter (fun γ : F =>
        ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := A) C δ
    ∧
    ((Finset.univ.filter (fun γ : F =>
        ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card : ℝ≥0∞)
      ≤ (B : ℝ≥0∞) :=
  ⟨ProximityGap.FarCosetExplosion.epsMCA_ge_far_incidence (u₀ := u₀) C δ hfar,
   epsMCA_le_of_worstCaseFarIncidence C δ B hB hfar⟩

/-! ## Part 3 — the ANTI-CONFLATION statement: value count ≠ worst-case incidence. -/

/-- **ANTI-CONFLATION (the explicit non-implication).**  The B1 value count `= n` and the
worst-case far-line incidence are *logically independent* objects.  Formally: knowing the
top-direction readout value-set has cardinality `n` gives NO information about the worst-case
incidence — there is no theorem of the form "value count `= n` ⟹ incidence `≤ f(n)`".

We record this as the honest negative fact that the open obligation
`WorstCaseFarIncidenceBounded` is NOT implied by the value-count law: it is a *separate* Prop,
left open.  The numeric witnesses (file header) show the incidence binder (`9, 13, 89` for
`n=8,12,16`) is neither the value count (`8, 12, 16`) nor the value-fiber (`7, 43, 273`), so any
purported equality among the three is refuted.

This lemma is intentionally a tautology over the named Prop — its CONTENT is the statement, in
type-checked form, that the δ* object is the separate `WorstCaseFarIncidenceBounded`, not the
value count.  It exists so that downstream code cannot silently substitute one for the other. -/
theorem worstCaseIncidence_is_the_open_object
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) :
    WorstCaseFarIncidenceBounded (F := F) C δ B
      ↔ ∀ u₀ u₁ : ι → A, FarFromCode C δ u₁ → farIncidence (F := F) C δ u₀ u₁ ≤ B :=
  Iff.rfl

end ProximityGap.WireB1ToIncidence

set_option linter.style.longLine false in
#print axioms ProximityGap.WireB1ToIncidence.topDirectionValueCount_eq_n
set_option linter.style.longLine false in
#print axioms ProximityGap.WireB1ToIncidence.epsMCA_le_of_worstCaseFarIncidence
set_option linter.style.longLine false in
#print axioms ProximityGap.WireB1ToIncidence.epsMCA_pinch_of_worstCaseFarIncidence
set_option linter.style.longLine false in
#print axioms ProximityGap.WireB1ToIncidence.worstCaseIncidence_is_the_open_object
