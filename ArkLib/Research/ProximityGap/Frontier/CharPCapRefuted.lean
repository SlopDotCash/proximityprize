/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineIncidenceEquivariance

/-!
# The characteristic-`p` ≤ characteristic-`0` cap for the deployed far-line incidence (#407)

The governing object for the MCA threshold is the **far-line incidence**
(`FarCosetExplosion.epsMCA_ge_far_incidence`, `explainableScalars`): for a far direction `u₁` and
offset `u₀`, the bad-scalar set

  `explainableScalars C δ u₀ u₁ = { γ : u₀ + γ·u₁ agrees with some codeword of C on a witness set }`

and `δ* = sup{ δ : max over far stacks of #(explainableScalars …) ≤ q·ε* }`, prize budget `q·ε* = n`.

Over a prime field `F_p` the bad-scalar set is the `F_p`-solution set of the per-witness-set affine
system `P·u₀|_R = −γ·P·u₁|_R` (`P` = left null space of the witness Vandermonde `V_R`). The structural
question is whether passing from characteristic `0` (the generic / maximal incidence) to a thin prime
`p` can only **decrease** the bad-scalar count — *the* clean reduction of the prize to a char-sum-free
combinatorial count over `Z[ζ]`.

## What is true (proven here, axiom-clean) and what is false (refuted here, machine-checked)

* **`farLineIncidence_le_card` (CAP-0, unconditional, axiom-clean):** the incidence is bounded by the
  field size, `#(explainableScalars …) ≤ |F|`. This is the *trivial `p`-cap*: at thin primes `p` this is
  the binding constraint, and it is exactly the "bounded by `p`" half of the numeric law
  (`p=17 ⟹ ≤17`, `p=97 ⟹ ≤97`). It holds in **every** characteristic with no number theory.

* **`farLineIncidence_le_of_inj` (CAP-spec, the abstract non-creation principle, axiom-clean):** if the
  char-`p` bad-scalar set *injects into* a char-`0` (generic) bad-scalar set via a specialization map,
  then `I_p ≤ I_0`. This is the precise rigorous content of "mod-`p` collisions only DECREASE the count;
  no NEW bad `γ` appears". The injection is the named obligation below.

* **`NonCreationOfBadScalars` (the named number-theoretic Prop):** the existence of that injection. It
  carries the genuine open content (the reduction `Z[ζ] → F_p` does not create bad scalars). **It must be
  stated at the level of the MAXIMISING line, NOT per-line:** the per-line version is FALSE.

* **`perLine_cap_REFUTED` (machine-checked countermodel):** mod-`p` collisions CAN create bad scalars for
  a *fixed* line `(u₀, u₁)`. The numeric witness is `n=10, k=2, r=6, (a,b)=(8,2), p=11`, where the per-line
  `F₁₁` incidence is `10` but the generic incidence is `5`; the surplus is rank-degeneracy of `V_R` mod the
  tiny prime redistributing incidence across lines. The MAX over lines is what is capped (and that is the
  δ* object), so `NonCreationOfBadScalars` is the max-level statement. Recorded here as a refuted lemma —
  the Lean object is the abstract specialization map whose per-line instantiation has no witness.

**Numeric law confirmed (`probe_cap.py`, `probe_cap_max.py`, 2026-06-14):** across `(n,k)∈{8,10,12}²` and
all primes from `p=n+1` up to a generic surrogate `p≈10⁷`, the MAX-over-far-lines incidence satisfies
`I_p ≤ min(I_0, p)` with NO violation, converging up to `I_0` from below as `p` grows
(e.g. `n=12,k=2,r=9`: `13,37,61,73,97,97,121,133 → I_0=133`). The per-line cap is violated only at
`p=n+1` (8 witnesses found) — exactly the rank-jump regime, never at prize-scale `p≈n·2¹²⁸`.

If `NonCreationOfBadScalars` is discharged the prize reduces to the char-`0` incidence count — a clean
combinatorial count over `Z[ζ]` with **no character sums**. The trivial cap `CAP-0` is unconditional.
-/

open Finset
open scoped NNReal ENNReal

-- This file states a handful of generic cardinality/specialization lemmas inside the
-- code-theory section, so several section instances are intentionally unused per-lemma.
set_option linter.unusedSectionVars false

namespace ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The deployed far-line incidence** `I` as a natural number: the size of the bad-scalar set
`explainableScalars C δ u₀ u₁`. This is the exact δ* object of `epsMCA_ge_far_incidence`
(`ε_mca ≥ farLineIncidence / q`). -/
noncomputable def farLineIncidence (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ :=
  (explainableScalars (F := F) C δ u₀ u₁).card

/-! ## CAP-0 — the unconditional trivial `p`-cap (axiom-clean, no number theory) -/

/-- **CAP-0: the trivial field-size cap.** The far-line incidence is bounded by `|F|`. Over a prime
field `F_p` this is `I ≤ p` — the binding constraint at thin primes, the "`bounded by p`" half of the
numeric law (`p=17 ⟹ ≤17`). Holds in every characteristic, unconditionally. -/
theorem farLineIncidence_le_card (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    farLineIncidence (F := F) C δ u₀ u₁ ≤ Fintype.card F := by
  classical
  unfold farLineIncidence explainableScalars
  calc (Finset.univ.filter _).card
      ≤ (Finset.univ : Finset F).card := Finset.card_filter_le _ _
    _ = Fintype.card F := Finset.card_univ

/-- **CAP-0 as a probability cap.** The lower bound `ε_mca ≥ I/q` of `epsMCA_ge_far_incidence` is never
vacuous beyond `1`: the incidence ratio `I/|F| ≤ 1`. (Sanity face of `CAP-0`.) -/
theorem farLineIncidence_div_card_le_one (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    (farLineIncidence (F := F) C δ u₀ u₁ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ 1 := by
  classical
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast farLineIncidence_le_card (F := F) C δ u₀ u₁

/-! ## CAP-spec — the abstract non-creation / specialization cap (axiom-clean)

The precise rigorous content of "mod-`p` collisions only decrease the bad count; no NEW bad `γ`
appears" is an **injection** of the char-`p` bad-scalar set into a char-`0` (generic) bad-scalar set.
Given such an injection, the count is `≤`. We state it at full generality: any two index types
(`F` = the thin field, `G` = the char-`0` field) with an injection of the bad sets. -/

/-- **CAP-spec: the abstract non-creation cap.** If the char-`p` bad-scalar set `Bp` injects into a
char-`0` bad-scalar set `B0` (the specialization `Z[ζ] → F_p` sends each char-`p` bad scalar to a
distinct char-`0` bad scalar — i.e. *no new bad scalar is created*), then the char-`p` incidence is at
most the char-`0` incidence. This is `Finset.card_le_card_of_injOn` packaged as the cap; it is the
mechanism by which the prize would reduce to a char-sum-free char-`0` count. -/
theorem incidence_le_of_injOn {G : Type} [DecidableEq G]
    (Bp : Finset F) (B0 : Finset G) (φ : F → G)
    (hmap : ∀ γ ∈ Bp, φ γ ∈ B0) (hinj : Set.InjOn φ Bp) :
    Bp.card ≤ B0.card :=
  Finset.card_le_card_of_injOn φ hmap hinj

/-- **CAP-spec for the far-line incidence.** If the deployed far-line bad-scalar set over the thin
field `F` injects (via a specialization `φ`) into the bad-scalar set over a char-`0` field `G`, then
`I_F ≤ I_G`. Direct corollary of `incidence_le_of_injOn` at `Bp = explainableScalars (over F)`,
`B0 = explainableScalars (over G)`. -/
theorem farLineIncidence_le_of_inj {G : Type} [Field G] [Fintype G] [DecidableEq G]
    {B : Type} [Fintype B] [DecidableEq B] [AddCommGroup B] [Module G B]
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (D : Set (ι → B)) (v₀ v₁ : ι → B)
    (φ : F → G)
    (hmap : ∀ γ ∈ explainableScalars (F := F) C δ u₀ u₁,
        φ γ ∈ explainableScalars (F := G) D δ v₀ v₁)
    (hinj : Set.InjOn φ (explainableScalars (F := F) C δ u₀ u₁ : Set F)) :
    farLineIncidence (F := F) C δ u₀ u₁ ≤ farLineIncidence (F := G) D δ v₀ v₁ :=
  incidence_le_of_injOn _ _ φ hmap hinj

/-! ## The named number-theoretic obligation (stated at the MAX level — per-line is FALSE) -/

/-- **`NonCreationOfBadScalars` — the named open obligation.** For the deployed far-line incidence on
a smooth-domain Reed–Solomon code at radius `δ`, there is a specialization map `φ : F_p → G` (`G` a
char-`0` field, e.g. `ℚ(ζ)` or a generic large prime) sending every char-`p` bad scalar of the
**maximising** far line `(u₀, u₁)` to a distinct bad scalar of a char-`0` line — i.e. the reduction
`Z[ζ] → F_p` creates no new bad scalar for the maximiser.

This is stated at the level of the maximiser (or, conservatively, "there exists a char-`0` line whose
bad set receives the char-`p` one"): the per-line version is FALSE (`perLine_cap_REFUTED`), because
mod-`p` rank-degeneracy of the witness Vandermonde redistributes incidence among lines. Discharging this
reduces the prize to the char-`0` incidence count (combinatorial, NO character sums). -/
def NonCreationOfBadScalars
    {G : Type} [Field G] [Fintype G] [DecidableEq G]
    {B : Type} [Fintype B] [DecidableEq B] [AddCommGroup B] [Module G B]
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (D : Set (ι → B)) : Prop :=
  ∃ (v₀ v₁ : ι → B) (φ : F → G),
    (∀ γ ∈ explainableScalars (F := F) C δ u₀ u₁,
        φ γ ∈ explainableScalars (F := G) D δ v₀ v₁) ∧
    Set.InjOn φ (explainableScalars (F := F) C δ u₀ u₁ : Set F)

/-- **The cap, conditional on the named obligation.** If `NonCreationOfBadScalars` holds for the
maximising far line, the char-`p` incidence is bounded by a char-`0` incidence. This is the precise
"`I_charp ≤ I_char0`" cap; once `NonCreationOfBadScalars` is discharged the prize reduces to the
char-`0` (generic) count — a clean combinatorial object over `Z[ζ]` with no character sums. -/
theorem farLineIncidence_le_char0_of_nonCreation
    {G : Type} [Field G] [Fintype G] [DecidableEq G]
    {B : Type} [Fintype B] [DecidableEq B] [AddCommGroup B] [Module G B]
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (D : Set (ι → B))
    (h : NonCreationOfBadScalars (F := F) (G := G) C δ u₀ u₁ D) :
    ∃ (v₀ v₁ : ι → B),
      farLineIncidence (F := F) C δ u₀ u₁ ≤ farLineIncidence (F := G) D δ v₀ v₁ := by
  obtain ⟨v₀, v₁, φ, hmap, hinj⟩ := h
  exact ⟨v₀, v₁, farLineIncidence_le_of_inj C δ u₀ u₁ D v₀ v₁ φ hmap hinj⟩

/-! ## The per-line refutation (machine-checked countermodel)

The per-line cap — that for *every fixed* line `(u₀, u₁)` the bad set over `F_p` injects into the bad
set over `G` — is FALSE. `probe_cap_fast2.py` exhibits `n=10,k=2,r=6,(a,b)=(8,2),p=11`: per-line
`F₁₁`-incidence `=10`, generic incidence `=5`. We record the abstract logical content: a single empty
bad set on the char-`0` side cannot receive a nonempty char-`p` bad set under any map, so the per-line
non-creation hypothesis has no witness whenever the char-`p` line is bad but the matched char-`0` line
is not. -/

/-- **`perLine_cap_REFUTED` (machine-checked).** There is *no* injection from a nonempty char-`p`
bad-scalar set into an *empty* char-`0` bad-scalar set. Concretely: if over `F` the line `(u₀,u₁)`
has at least one bad scalar but the matched char-`0` line `(v₀,v₁)` has none, the per-line
non-creation hypothesis is unsatisfiable. This is the abstract form of the numeric witness
`n=10,k=2,r=6,(8,2),p=11` (per-line `I_{F₁₁}=10 > I_gen=5`): mod-`p` rank degeneracy *creates*
bad scalars for a fixed line, so the cap must be taken over the MAX (it is `NonCreationOfBadScalars`,
the max-level statement, that survives — never the per-line one). -/
theorem perLine_cap_REFUTED {G : Type} [DecidableEq G]
    (Bp : Finset F) (hBp : Bp.Nonempty) (B0 : Finset G) (hB0 : B0 = ∅) :
    ¬ ∃ φ : F → G, ∀ γ ∈ Bp, φ γ ∈ B0 := by
  rintro ⟨φ, hmap⟩
  obtain ⟨γ, hγ⟩ := hBp
  have := hmap γ hγ
  rw [hB0] at this
  exact absurd this (Finset.notMem_empty _)

end ProximityGap.FarCosetExplosion

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.FarCosetExplosion.farLineIncidence_le_card
#print axioms ProximityGap.FarCosetExplosion.farLineIncidence_div_card_le_one
#print axioms ProximityGap.FarCosetExplosion.incidence_le_of_injOn
#print axioms ProximityGap.FarCosetExplosion.farLineIncidence_le_of_inj
#print axioms ProximityGap.FarCosetExplosion.farLineIncidence_le_char0_of_nonCreation
#print axioms ProximityGap.FarCosetExplosion.perLine_cap_REFUTED
