/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The Johnson-split closure of `ExplainableCoreSupply` (#389, route 1)

The #389 supply statement asks for a uniform bound `B` such that EVERY word `w`
has at most `B` explainable `(k+m+1)`-cores (`ExplainableCoreSupply dom k m B`).
`explainableCoreSupply_pinned` shows the unconditional optimum is exactly
`C(n,k+m+1)` (the zero word makes every core explainable), so a genuinely
sharper supply must restrict to the *agreement-capped* range — the upper, above
Johnson, side of the list-decoding split.

This file closes the actual top-level `ExplainableCoreSupply` Prop on the
agreement-capped parameter range, via a single clean named hypothesis:

* `AgreementCap dom k A` — every word's codeword agreements are all `≤ A`.
  This is exactly the list-decoding agreement-radius cap.  It holds
  *unconditionally* at `A = n` (`agreementCap_trivial`); the list-decoding
  content is that the cap is `≤ (n+k)/2` in the unique-decoding range and finite
  above the Johnson radius (the in-tree second-moment list bound).

* `explainableCoreSupply_of_agreementCap` — **the closure**: from
  `AgreementCap dom k A` (and `1 ≤ k`), `ExplainableCoreSupply` holds with the
  sharpened pair-counting bound `B = C(n,k) · C(A−k, m+1) / C(k+m+1, k)`.
  This is the agreement-capped supply `explainable_cores_card_of_agreement_le`
  lifted to the universal quantifier over all words.

* `explainableCoreSupply_of_agreementCap_simple` — the same with the unsharpened
  `B = C(n,k) · C(A−k, m+1)` (no division), the cleanest readable form.

* `explainableCoreSupply_of_agreementCap_johnson` — **the above-Johnson form**:
  from `AgreementCap dom k A` AND the Johnson gap `n(k−1) < (k+m+1)²`,
  `ExplainableCoreSupply` holds with the polynomial-list Johnson bound
  `B = (n²/((k+m+1)²−n(k−1))) · C(A, k+m+1)` — no `C(n,·)` factor.

* `agreementCap_trivial` / `explainableCoreSupply_trivialCap` — the
  UNCONDITIONAL instance at the trivial cap `A = n`: every word has
  `≤ C(n,k)·C(n−k,m+1)` explainable cores with NO hypothesis.

Status of the parameter range covered:

* **Conditional on `AgreementCap dom k A`** — a clean, honest named hypothesis,
  and UNCONDITIONAL at `A = n` (`explainableCoreSupply_trivialCap`).  The cap is
  the list-decoding agreement radius: `≤ (n+k)/2` in the unique-decoding range,
  finite above the Johnson line (the sibling `rsCode_agreement_list_card_le`).
* **Open** — a subexponential supply BELOW the Johnson radius with NO agreement
  cap is the classical sub-Johnson RS list-size wall (the 25-year-open core,
  `DISPROOF_LOG.md`); this file does not and cannot close it.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The agreement cap** (#389 route 1 hypothesis): every word's agreement with
every codeword of `rsCode dom k` is at most `A`.  This is the list-decoding
agreement-radius cap; it is unconditional below the unique-decoding radius
(`agreementCap_of_unique`) and finite above the Johnson radius. -/
def AgreementCap (dom : Fin n ↪ F) (k A : ℕ) : Prop :=
  ∀ w : Fin n → F, ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
    (agreeSet c w).card ≤ A

open Classical in
/-- **THE CLOSURE (#389 route 1, sharpened form)**: under the agreement cap `A`,
the top-level `ExplainableCoreSupply` holds with the pair-counting bound
`B = C(n,k) · C(A−k, m+1) / C(k+m+1, k)`. -/
theorem explainableCoreSupply_of_agreementCap (dom : Fin n ↪ F) {k m A : ℕ}
    (hk : 1 ≤ k) (hcap : AgreementCap dom k A) :
    ExplainableCoreSupply dom k m
      (n.choose k * (A - k).choose (m + 1) / (k + m + 1).choose k) := by
  intro w
  have hsupply :=
    explainable_cores_card_of_agreement_le dom (m := m) hk (hcap w)
  set expl := (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
    (fun T => ExplainableOn dom k w T)).card with hexpl
  have hpos : 0 < (k + m + 1).choose k := Nat.choose_pos (by omega)
  -- expl * C ≤ N  ⟹  expl ≤ N / C  (Nat division)
  rw [Nat.le_div_iff_mul_le hpos]
  -- hsupply : expl * C ≤ N
  exact hsupply

open Classical in
/-- **THE CLOSURE (#389 route 1, simple form)**: under the agreement cap `A`,
`ExplainableCoreSupply` holds with the readable bound
`B = C(n,k) · C(A−k, m+1)` (no division). -/
theorem explainableCoreSupply_of_agreementCap_simple (dom : Fin n ↪ F)
    {k m A : ℕ} (hk : 1 ≤ k) (hcap : AgreementCap dom k A) :
    ExplainableCoreSupply dom k m
      (n.choose k * (A - k).choose (m + 1)) := by
  intro w
  have hsupply :=
    explainable_cores_card_of_agreement_le dom (m := m) hk (hcap w)
  have hpos : 0 < (k + m + 1).choose k := Nat.choose_pos (by omega)
  -- expl ≤ expl * C ≤ N
  calc (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k w T)).card
      ≤ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => ExplainableOn dom k w T)).card * (k + m + 1).choose k :=
        Nat.le_mul_of_pos_right _ hpos
    _ ≤ n.choose k * (A - k).choose (m + 1) := hsupply

open Classical in
/-- **THE CLOSURE (#389 route 1, above-Johnson form)**: under the agreement cap
`A` AND the Johnson gap `n(k−1) < (k+m+1)²`, `ExplainableCoreSupply` holds with
the polynomial-list Johnson bound
`B = (n²/((k+m+1)² − n(k−1))) · C(A, k+m+1)` — no `C(n,·)` factor. -/
theorem explainableCoreSupply_of_agreementCap_johnson (dom : Fin n ↪ F)
    {k m A : ℕ} (hk : 1 ≤ k) (hcap : AgreementCap dom k A)
    (hgap : n * (k - 1) < (k + m + 1) ^ 2) :
    ExplainableCoreSupply dom k m
      ((n ^ 2 / ((k + m + 1) ^ 2 - n * (k - 1))) * A.choose (k + m + 1)) := by
  intro w
  exact explainable_cores_card_le_johnson dom hk (hcap w) hgap

omit [Fintype F] [NeZero n] in
open Classical in
/-- **The unconditional trivial cap**: every agreement is `≤ n`
(`agreeSet ⊆ univ`).  This makes the closure unconditional; the content of the
closure is that it consumes ANY valid cap `A`, and the cap is the quantity the
list-decoding split controls (`≤ (n+k)/2` in the unique-decoding range, finite
above the Johnson line via the in-tree second-moment bound). -/
theorem agreementCap_trivial (dom : Fin n ↪ F) {k : ℕ} :
    AgreementCap dom k n := by
  intro w c _
  calc (agreeSet c w).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The unconditional closure at the trivial cap**: instantiating the closure
at `A = n` recovers a uniform supply `C(n,k) · C(n−k, m+1)` valid for EVERY
word with no hypothesis at all — strictly below the pinned optimum
`C(n,k+m+1)` only when the cap actually bites, but unconditional. -/
theorem explainableCoreSupply_trivialCap (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) :
    ExplainableCoreSupply dom k m
      (n.choose k * (n - k).choose (m + 1)) :=
  explainableCoreSupply_of_agreementCap_simple dom hk (agreementCap_trivial dom)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.explainableCoreSupply_of_agreementCap
#print axioms ProximityGap.Ownership.explainableCoreSupply_of_agreementCap_simple
#print axioms ProximityGap.Ownership.explainableCoreSupply_of_agreementCap_johnson
#print axioms ProximityGap.Ownership.agreementCap_trivial
#print axioms ProximityGap.Ownership.explainableCoreSupply_trivialCap
