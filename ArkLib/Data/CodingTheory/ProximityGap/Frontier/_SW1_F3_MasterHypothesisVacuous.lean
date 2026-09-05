/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#1, SW1 lane F3)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ42Realizability

/-!
# SW1-F3 — the strip master hypotheses (SYZ40 / SYZ41 / SYZ42) are contradictory

**Observation.**  Every strip master hypothesis carries the realizability field

> `realizability : ∀ Ucard, k ≤ Ucard → Ucard ≤ n → Nonempty (SuperadditiveUnion n k Ucard)`

(SYZ42's `realizabilityCore` field is the same statement through `RealizabilityCore`, which
transports back to `SuperadditiveUnion` by `toSuperadditiveUnion`).  But SYZ20's own
`union_card_lt_length` derives `2 (Ucard − k) + 1 ≤ 2 (n − k)` from any `SuperadditiveUnion n k
Ucard`, which is false at `Ucard = n`.  Hence `SuperadditiveUnion n k Ucard` is **empty for every
`Ucard ≥ n`** (`superadditiveUnion_isEmpty_of_le`), and each master hypothesis is refuted at the
instance `Ucard := n` as soon as `k ≤ n`:

* `not_stripMasterHypothesis`   — SYZ40 `StripMasterHypothesis K V n k`;
* `not_stripMasterHypothesis'`  — SYZ41 `StripMasterHypothesis' K V n k`;
* `not_stripMasterHypothesis''` — SYZ42 `StripMasterHypothesis'' K V n k`;
* `syz46_antecedent_false`      — the antecedent of SYZ46
  `deltaStar_bracket_of_strip_master_hypothesis` (`n = 2^30`, `k = 2^29`, any `K`, any `V`).

**Honest classification.**  Refutation-no-go of a *formalization*, not of mathematics: the
conditional δ* bracket `357913941/2³⁰ ≤ δ* ≤ 358612991/2³⁰` of SYZ46 is `False → …`, so it
carries no information about δ*, and no F1/F2/F3 progress can ever "discharge" it in its
present form.  The intended content (a union budget `|U| ≤ n − 1` for the witness supports of a
genuine over-budget stack) must be re-carried by a per-stack statement.  The companion file
`_SW1_F3_UnionRankExact.lean` shows that even the per-stack rank equality `hrank` at
`Ucard = |U|` is false for every `mcaEvent` stack, so the re-carrier cannot be a rank
*equality* either.  CORE OPEN / ON-BGK.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SW1F3

open ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `SuperadditiveUnion n k Ucard` is empty whenever `Ucard ≥ n`: its own consequence
`union_card_lt_length` reads `2 (Ucard − k) + 1 ≤ 2 (n − k)`, impossible for `Ucard ≥ n`. -/
theorem superadditiveUnion_isEmpty_of_le {n k Ucard : ℕ} (h : n ≤ Ucard) :
    IsEmpty (SuperadditiveUnion (F := K) (V := V) n k Ucard) :=
  ⟨fun cfg => by
    have := union_card_lt_length cfg
    omega⟩

/-- SYZ40's master hypothesis is unsatisfiable for `k ≤ n` (instance `Ucard := n`). -/
theorem not_stripMasterHypothesis (n k : ℕ) (hkn : k ≤ n) :
    ¬ ArkLib.ProximityGap.SYZ40.StripMasterHypothesis K V n k :=
  fun H => (superadditiveUnion_isEmpty_of_le le_rfl).false (H.realizability n hkn le_rfl).some

/-- SYZ41's master hypothesis is unsatisfiable for `k ≤ n`. -/
theorem not_stripMasterHypothesis' (n k : ℕ) (hkn : k ≤ n) :
    ¬ ArkLib.ProximityGap.SYZ41.StripMasterHypothesis' K V n k :=
  fun H => (superadditiveUnion_isEmpty_of_le le_rfl).false (H.realizability n hkn le_rfl).some

/-- SYZ42's master hypothesis (the one SYZ46's δ* bracket consumes) is unsatisfiable for
`k ≤ n`. -/
theorem not_stripMasterHypothesis'' (n k : ℕ) (hkn : k ≤ n) :
    ¬ ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' K V n k :=
  fun H => (superadditiveUnion_isEmpty_of_le le_rfl).false
    (H.realizabilityCore n hkn le_rfl).some.toSuperadditiveUnion

/-- The antecedent of SYZ46 `deltaStar_bracket_of_strip_master_hypothesis` (`n = 2^30`,
`k = 2^29`) is false over every field and every finite-dimensional `V`. -/
theorem syz46_antecedent_false :
    ¬ ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' K V (2 ^ 30) (2 ^ 29) :=
  not_stripMasterHypothesis'' _ _ (by norm_num)

end ArkLib.ProximityGap.SW1F3

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SW1F3.superadditiveUnion_isEmpty_of_le
#print axioms ArkLib.ProximityGap.SW1F3.not_stripMasterHypothesis
#print axioms ArkLib.ProximityGap.SW1F3.not_stripMasterHypothesis'
#print axioms ArkLib.ProximityGap.SW1F3.not_stripMasterHypothesis''
#print axioms ArkLib.ProximityGap.SW1F3.syz46_antecedent_false
