/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.Erasure

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance

/-!
# Erasure correction for codes over a finite alphabet

* `HasErasureDecoder C` — the *functional* erasure-correction predicate: some
  function (not necessarily computable, let alone efficient) recovers any
  codeword `u ∈ C` from a partial observation `f : ι → Option F` with strictly
  fewer than `minDist C` erasures, and returns `none` otherwise.
* `SupportsErasureCorrection C ecor` — the ABF26 Definition 6.4 shape, which
  carries a correction-time parameter `ecor`. **The parameter is inert**: no
  algorithm or cost semantics is modelled, so `SupportsErasureCorrection C e`
  is definitionally `HasErasureDecoder C` for every `e`
  (`supportsErasureCorrection_iff`). Do not read any value of `ecor` as a
  certified running time.
* `hasErasureDecoder` — every set `C` has a functional erasure decoder (classical
  choice of the unique agreeing codeword, uniqueness from the canonical
  `eq_of_consistent_with_erased`). This is decoder *existence* only; it is not
  the efficient-decoding content of [GRS25].

Lives in `Data/CodingTheory/` rather than at the protocol layer (where the
ABF26 toy problem originally introduced it) because the predicate is generic
across proof systems — any reduction whose extractor erasure-decodes its
oracles consumes the same shape.

## References

This predicate is paper-tagged to ABF26 D6.4 (Arnon-Boneh-Fenzi 2026, §6.2);
the corresponding "every additive code can be erasure decoded in polynomial
time" lemma is L6.5 in the same paper (citing GRS25 = Guruswami-Rudra-Sudan,
*Essential Coding Theory*). Only its functional (existence) part is formalized.
-/

namespace CodingTheory

open Code

variable {ι F : Type*} [Fintype ι]

/-- **Functional erasure decoder** (the correctness part of ABF26 Definition 6.4).

A code `C ⊆ (ι → F)` has an erasure decoder if there is a function
`E_C : (ι → Option F) → Option (ι → F)` that, on any input `f`:

  (i)  if `f` has strictly fewer than `minDist C` erasures and there exists a
       (necessarily unique) codeword `u ∈ C` agreeing with `f` off the
       erasures, returns `some u`;
  (ii) otherwise returns `none`.

Clause (ii) — easy to miss in a quick port from the paper — is what makes the
predicate non-vacuous: without it, `E := fun _ ↦ some <arbitrary>` satisfies
the recovery clause for any `f` whose preconditions fail.

Nothing here constrains *how* `E_C` computes: this predicate says nothing about
running time or even computability. -/
def HasErasureDecoder [DecidableEq F] (C : Set (ι → F)) : Prop :=
  ∃ E : (ι → Option F) → Option (ι → F),
    ∀ (f : ι → Option F),
      -- (i) recovery clause
      (∀ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) →
        ((Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C →
          E f = some u)) ∧
      -- (ii) failure clause: ⊥ unless both small-erasures AND a witness exist
      (¬ (∃ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) ∧
            (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C) →
        E f = none)

/-- **ABF26 Definition 6.4** (erasure-correction predicate), paper shape.

The paper says `C` supports erasure correction *with correction time `ecor`*.
Only the functional content is formalized: the time bound `_ecor` is an
**inert** parameter (no algorithm/cost semantics is modelled), so this is
definitionally `HasErasureDecoder C` for every value of `_ecor`
(`supportsErasureCorrection_iff`). In particular instances at `ecor = 0`,
`ecor = 1`, or any other value are interchangeable, and no theorem stated with
this predicate certifies a running time. -/
def SupportsErasureCorrection [DecidableEq F]
    (C : Set (ι → F)) (_ecor : ℕ) : Prop :=
  HasErasureDecoder C

/-- The correction-time parameter of `SupportsErasureCorrection` is inert. -/
theorem supportsErasureCorrection_iff [DecidableEq F] (C : Set (ι → F)) (ecor : ℕ) :
    SupportsErasureCorrection C ecor ↔ HasErasureDecoder C :=
  Iff.rfl

/-- **Every code has a functional erasure decoder.** When fewer than `minDist C`
symbols are erased the agreeing codeword is unique
(`eq_of_consistent_with_erased`), so the classical decoder returning that
witness (and `none` when there is none) satisfies both clauses. No additivity
is needed, and no efficiency is claimed: the decoder is defined by
`Classical.choose`. -/
theorem hasErasureDecoder [DecidableEq F] (C : Set (ι → F)) : HasErasureDecoder C := by
  classical
  let good : (ι → Option F) → (ι → F) → Prop :=
    fun f u ↦ u ∈ C ∧ (∀ i, f i = some (u i) ∨ f i = none) ∧
      (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C
  let E : (ι → Option F) → Option (ι → F) :=
    fun f ↦ if h : ∃ u, good f u then some h.choose else none
  refine ⟨E, fun f ↦ ⟨?_, ?_⟩⟩
  · intro u huC hagree hsmall
    have hex : ∃ u, good f u := ⟨u, huC, hagree, hsmall⟩
    change E f = some u
    rw [show E f = some hex.choose from dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨hcC, hca, _⟩ := hex.choose_spec
    exact congrArg some (eq_of_consistent_with_erased hcC huC hca hagree hsmall)
  · intro hno
    have : ¬ ∃ u, good f u := by
      rintro ⟨u, huC, hagree, hsmall⟩
      exact hno ⟨u, huC, hagree, hsmall⟩
    change E f = none
    exact dite_eq_right_of_eq_false (eq_false this)

/-- Paper-shape corollary: `SupportsErasureCorrection C ecor` holds for **every**
`ecor` — a direct witness that the parameter carries no runtime content. -/
theorem supportsErasureCorrection [DecidableEq F] (C : Set (ι → F)) (ecor : ℕ) :
    SupportsErasureCorrection C ecor :=
  hasErasureDecoder C

end CodingTheory
