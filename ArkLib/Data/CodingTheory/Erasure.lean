/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Erasure correction for codes over a finite alphabet

A generic erasure-correction predicate `SupportsErasureCorrection C ecor`
asserting that a deterministic algorithm exists that recovers any codeword
`u ∈ C` from a partial observation `f : ι → Option F` with strictly fewer
than `δ_min(C) · |ι|` erasures, and returns `⊥` otherwise.

Lives in `Data/CodingTheory/` rather than at the protocol layer (where the
ABF26 toy problem originally introduced it) because the predicate is generic
across proof systems — any reduction whose extractor erasure-decodes its
oracles consumes the same shape.

## References

This predicate is paper-tagged to ABF26 D6.4 (Arnon-Boneh-Fenzi 2026, §6.2);
the corresponding "every additive code can be erasure decoded in polynomial
time" lemma is L6.5 in the same paper (citing GRS25 = Guruswami-Rudra-Sudan,
*Essential Coding Theory*).
-/

namespace CodingTheory

open Code

variable {ι F : Type*} [Fintype ι]

/-- **ABF26 Definition 6.4** (erasure-correction predicate).

A code `C ⊆ (ι → F)` supports **erasure correction with correction
time `ecor`** if there exists a deterministic algorithm `E_C` that, on
any input `f : ι → Option F`:

  (i)  if `f` has strictly fewer than `δ_min(C) · |ι|` erasures and
       there exists a (necessarily unique) codeword `u ∈ C` agreeing
       with `f` off the erasures, then `E_C(f) = some u`;
  (ii) otherwise `E_C(f) = none`.

Clause (ii) — easy to miss in a quick port from the paper — is what
makes the predicate non-vacuous: without it,
`E := fun _ ↦ some <arbitrary>` satisfies the recovery clause for any
`f` whose preconditions fail, hollowing the definition out.

The running-time bound `ecor` is carried as a numeric parameter for
downstream complexity bookkeeping (e.g. ABF26 L6.5's
`O((s · n)^3)` cost claim) but is not encoded operationally here. -/
def SupportsErasureCorrection [DecidableEq F]
    (C : Set (ι → F)) (_ecor : ℕ) : Prop :=
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

end CodingTheory
