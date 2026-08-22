/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorSuccessorPmin64Good
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorSuccessorScanResult

/-!
# The realizability-table successor counterexample at rung 5 → 6 (#466, lane _W10)

## Position in the successor obligation (workbench §5(2), `CandidateListExactSuccessor`)

The obligation asked for "`CandidateListExactSuccessor` or its adjacent-rung counterexample".
Existing state:

* `_FloorSuccessorScanResult.lean` refuted the successor **for the canonical-resultant model**
  `FloorBad0` (break at rung `4 → 5`, driven by the second resultant prime `641`), with the
  explicit caveat that under the true *adjacent-realizability* predicate the `4 → 5` step is
  fine (`floor-bad(32) = {97}` exactly), so that refutation does not touch the realizability
  route.
* FS1 (kb `deltastar-466-floorbad64-decided-2026-07-03.md`) then DECIDED, by a complete
  symmetry-reduced MITM scan, that `193 = p_min(64)` is **not** floor-bad at `n = 64` — the
  realizability successor breaks at `5 → 6`.
* `_FloorSuccessorPmin64Good.lean` landed the conditional socket
  `not_candidateListExactSuccessor_of_five_exact_and_pmin64_good`, whose hypothesis pair
  (`CandidateListExactAt FloorBad 5` AND `¬ FloorBad 64 193`) consumed the FS1 certificate as
  named hypotheses — but nothing in-tree exhibits a predicate satisfying that pair, so the
  socket's non-vacuity was unverified.

## What this file lands

`FloorBadR`, the concrete decidable **realizability-table model**: the finite table
transcribing the external adjacent-realizability verdicts of record

* `floor-bad(16) = {17}`   (complete residual + complement scans),
* `floor-bad(32) = {97}`   (complete MITM == brute complement count, engine-validated),
* `193 ∉ floor-bad(64)`    (FS1 complete symmetry-reduced MITM, 10,424,700 × 3,312,400 keys),

and, for this model, the **unconditional Lean theorems**:

* rungs `a = 4` and `a = 5` are EXACT (`candidateListExactAt_floorBadR_four/_five`);
* rung `a = 6` FAILS (`not_candidateListExactAt_floorBadR_six`) — the candidate is `193`;
* hence `¬ CandidateListExactSuccessor FloorBadR` with the adjacent break at `5 → 6`
  (`not_candidateListExactSuccessor_floorBadR`), and
  `¬ CandidateListExactSmallestFamily FloorBadR`;
* **non-vacuity of the FS1 socket** (`pmin64Good_socket_nonvacuous`): the hypothesis pair of
  `not_candidateListExactSuccessor_of_five_exact_and_pmin64_good` is instantiable — the
  conditional refutation is not a theorem about an empty class.

Together with `_FloorSuccessorScanResult.lean` this completes the model-level picture: the
resultant superset model breaks at `4 → 5`, the realizability model breaks at `5 → 6`; under
BOTH concrete floor-bad semantics in the tree, the uniform singleton least-prime successor law
is false in Lean, each with its explicit adjacent exact-then-failing pair.

## The honest caveat

`FloorBadR` is a *model*: a finite table faithful to the external scans of record at the pairs
the theorems consult (`(16, ·)`, `(32, ·)`, `(64, 193)`).  Exactness at rungs 4/5 is
definitional for the table; its fidelity to the true realizability predicate over ALL split
primes is exactly the scans' coverage (the scans of record are complete over their stated
families, but the true predicate at pairs the table calls "good" beyond them is external
input, not Lean content).  The theorem-or-nothing part of the obligation — proving the
successor for the TRUE realizability predicate — remains what FS1 showed it to be: FALSE at
`5 → 6` given the external certificate; this file makes the Lean side of that refutation
unconditional for the faithful table and proves the certificate socket consumes a non-empty
hypothesis class.  This is OFF-WALL substrate bookkeeping: it does NOT touch the BGK/Paley
`δ*` core.

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 262144

namespace ArkLib.ProximityGap.Frontier.W10SuccessorRealizabilityModel

open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorClosureContract
open ArkLib.ProximityGap.Frontier.FloorLinnikRung
open ArkLib.ProximityGap.Frontier.FloorSuccessorScanResult
open ArkLib.ProximityGap.Frontier.FloorSuccessorPmin64Good

/-- The concrete decidable **realizability-table** floor-bad model: the finite explicit table of
adjacent-realizability bad split primes established by the scans of record
(`floor_scan_exact.c` rank predicate; FS1 complete MITM at `n = 64`):

* `n = 16` : bad split primes `{17}`;
* `n = 32` : bad split primes `{97}` (NOT the resultant superset `{97, 641, 673, 1153}`);
* everything else good — in particular `FloorBadR 64 193` is false (the FS1 decision).

Contrast with `FloorSuccessorScanResult.FloorBad0` (the canonical-resultant superset model). -/
def FloorBadR (n p : ℕ) : Prop :=
  (n = 16 ∧ p = 17) ∨ (n = 32 ∧ p = 97)

instance (n p : ℕ) : Decidable (FloorBadR n p) := by
  unfold FloorBadR; infer_instance

/-- The FS1 headline, at the table: `193 = p_min(64)` is not floor-bad. -/
theorem not_floorBadR_64_193 : ¬ FloorBadR 64 193 := by
  unfold FloorBadR; decide

/-! ### Rung `a = 4` is EXACT for the realizability table -/

/-- **Rung a = 4 is EXACT.**  Every prime `p ≡ 1 mod 16` is table-bad iff it is the single
candidate `17`.  (Candidate value pinned by `FloorSuccessorScanResult.candidate16_eq`.) -/
theorem candidateListExactAt_floorBadR_four : CandidateListExactAt FloorBadR 4 := by
  show CandidateListExactInAP FloorBadR (2 ^ 4) [smallestPrime1ModN (2 ^ 4) (2 ^ (5 * 4))]
  rw [candidate16_eq]
  intro p hp hmod
  constructor
  · rintro (⟨_, hp17⟩ | ⟨hn, _⟩)
    · simp [hp17]
    · exact absurd hn (by decide)
  · intro hmem
    have hp' : p = 17 := by simpa using hmem
    exact Or.inl ⟨rfl, hp'⟩

/-! ### Rung `a = 5` is EXACT for the realizability table

This is where the realizability table departs from the resultant model `FloorBad0`: the
resultant's second prime `641` is NOT realizability-bad (`floor-bad(32) = {97}` by the exact
scans), so the singleton rule survives one rung longer. -/

/-- **Rung a = 5 is EXACT.**  Every prime `p ≡ 1 mod 32` is table-bad iff it is the single
candidate `97` (candidate pinned by `FloorLinnikRung.smallestPrime1ModN_32_pow25_eq_97`). -/
theorem candidateListExactAt_floorBadR_five : CandidateListExactAt FloorBadR 5 := by
  show CandidateListExactInAP FloorBadR (2 ^ 5) [smallestPrime1ModN (2 ^ 5) (2 ^ (5 * 5))]
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [h32, smallestPrime1ModN_32_pow25_eq_97]
  intro p hp hmod
  constructor
  · rintro (⟨hn, _⟩ | ⟨_, hp97⟩)
    · exact absurd hn (by decide)
    · simp [hp97]
  · intro hmem
    have hp' : p = 97 := by simpa using hmem
    exact Or.inr ⟨rfl, hp'⟩

/-! ### Rung `a = 6` FAILS — the FS1 break -/

/-- **Rung a = 6 FAILS** for the realizability table: the candidate is `193 = p_min(64)`
(`FloorSuccessorPmin64Good.smallestPrime1ModN_64_pow30_eq_193`), and the FS1 complete scan
verdict transcribed in the table says `193` is good.  Consumed through the landed socket
`not_candidateListExactAt_six_of_pmin64_good`. -/
theorem not_candidateListExactAt_floorBadR_six : ¬ CandidateListExactAt FloorBadR 6 :=
  not_candidateListExactAt_six_of_pmin64_good FloorBadR not_floorBadR_64_193

/-! ### The successor verdict for the realizability table -/

/-- **The adjacent exact-then-failing pair at `5 → 6`** — the realizability-shaped adjacent-rung
counterexample the workbench §5(2) successor obligation asked for, at the table level.
(Compare `FloorSuccessorScanResult.exact_rung_four_next_five_fails`: the resultant model breaks
one rung earlier, at `4 → 5`.) -/
theorem exact_rung_five_next_six_fails :
    (4 : ℕ) ≤ 5 ∧ CandidateListExactAt FloorBadR 5 ∧ ¬ CandidateListExactAt FloorBadR 6 :=
  ⟨by norm_num, candidateListExactAt_floorBadR_five, not_candidateListExactAt_floorBadR_six⟩

/-- The successor propagation theorem `CandidateListExactSuccessor` is **false** for the
realizability table: exactness at rung `5` does not propagate to rung `6`. -/
theorem not_candidateListExactSuccessor_floorBadR :
    ¬ CandidateListExactSuccessor FloorBadR :=
  (not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails FloorBadR).mpr
    ⟨5, by norm_num, candidateListExactAt_floorBadR_five, not_candidateListExactAt_floorBadR_six⟩

/-- The uniform singleton-exactness input is **false** for the realizability table. -/
theorem not_candidateListExactSmallestFamily_floorBadR :
    ¬ CandidateListExactSmallestFamily FloorBadR :=
  not_candidateListExactSmallestFamily_of_next_failure FloorBadR (a := 5) (by norm_num)
    not_candidateListExactAt_floorBadR_six

/-- Scanner normal form: the base rung is exact and the (unique possible) failure mode is an
adjacent exact-then-failing rung — here `5 → 6`, with an exact verified prefix `4, 5`. -/
theorem floorBadR_failure_is_adjacent_exact_then_failing :
    CandidateListExactAt FloorBadR 4 ∧
      ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBadR a ∧
        ¬ CandidateListExactAt FloorBadR (a + 1) :=
  ⟨candidateListExactAt_floorBadR_four,
    5, by norm_num, candidateListExactAt_floorBadR_five, not_candidateListExactAt_floorBadR_six⟩

/-! ### Non-vacuity of the FS1 conditional socket -/

/-- **The `_FloorSuccessorPmin64Good` socket is non-vacuous**: there exists a floor-bad
predicate satisfying BOTH hypotheses of
`not_candidateListExactSuccessor_of_five_exact_and_pmin64_good` (rung-5 exactness AND the
`p_min(64)`-good certificate) — namely the realizability table itself.  The conditional
refutation therefore quantifies over a non-empty hypothesis class. -/
theorem pmin64Good_socket_nonvacuous :
    ∃ FloorBad : ℕ → ℕ → Prop,
      CandidateListExactAt FloorBad 5 ∧ ¬ FloorBad 64 193 :=
  ⟨FloorBadR, candidateListExactAt_floorBadR_five, not_floorBadR_64_193⟩

/-- The socket applied to its own witness reproduces the refutation end-to-end (plumbing
faithfulness check, mirroring `FloorSuccessorScanResult`'s use of the `a = 4 → 5` scanner). -/
theorem socket_applied_to_witness :
    ¬ CandidateListExactSuccessor FloorBadR :=
  not_candidateListExactSuccessor_of_five_exact_and_pmin64_good FloorBadR
    candidateListExactAt_floorBadR_five not_floorBadR_64_193

#print axioms not_floorBadR_64_193
#print axioms candidateListExactAt_floorBadR_four
#print axioms candidateListExactAt_floorBadR_five
#print axioms not_candidateListExactAt_floorBadR_six
#print axioms exact_rung_five_next_six_fails
#print axioms not_candidateListExactSuccessor_floorBadR
#print axioms not_candidateListExactSmallestFamily_floorBadR
#print axioms floorBadR_failure_is_adjacent_exact_then_failing
#print axioms pmin64Good_socket_nonvacuous
#print axioms socket_applied_to_witness

end ArkLib.ProximityGap.Frontier.W10SuccessorRealizabilityModel
