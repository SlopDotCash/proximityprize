/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B25 — One-sided dyadic lift of the bad-set count (target E5, #444)

## The target (E5)

The empirical dyadic cascade recursion (kb `deltastar-444-empirical-formulas...`, E5) reads

  `D*_{2n}(m) = D*_n(m−1)`   (holds at shallow depth)

but **breaks at the binding** through *plateau-doubling*: at the binding depth a doubled rung
appears, so the clean equality fails and the honest, *always-true* statement is the **one-sided
lift**

  `D*_{2n}(m) ≤ D*_n(m−1) + (plateau term).`

Here `D*_n(m)` is the worst-direction over-determined far-line incidence count at level `n`,
over-determination depth `m` — concretely a `Finset.card` of a bad-α set (the object whose
budget-crossing `OrbitCountCrossingLaw.crossing_law` governs).

## What is proven here (axiom-clean, no `sorry`)

The lift is a **covering / cardinality** fact, independent of the precise dynamics of the
doubling map. The mathematical content of "doubling embeds the level-`n` bad set into level
`2n`" is exactly:

  the level-`2n`, depth-`m` bad set `B'` is **covered** by
  `φ '' B  ∪  P`,

where
* `φ : ι → κ` is the doubling embedding (`α ↦ α` under `μ_n ↪ μ_{2n}`, on bad-set indices),
* `B : Finset ι` is the level-`n`, depth-`(m−1)` bad set (the *carried-over* contributions),
* `P : Finset κ` is the **plateau set** — the *new* (doubled-rung) contributions at level `2n`
  that do not come from a level-`n` bad index.

From a covering `B' ⊆ φ '' B ∪ P` one gets, by `card_image_le` + `card_union_le`,

  `|B'| ≤ |B| + |P|`,                         (`bad_count_lift`)

which is exactly `D*_{2n}(m) ≤ D*_n(m−1) + |P|` with plateau term `|P|`.

We additionally feed this through the **orbit-count substrate** (`OrbitCountCrossingLaw`):
when each side carries the free-action structure (`|B| = N·S`, `|B'| = N'·S'`, `|P| = N_P·S_P`),
the lift is equivalently a bound on the orbit counts (`bad_count_lift_orbit`), and — packaged with
the supply identity `S·d = n` — it yields the budget-crossing consequence

  if `D*_n(m−1) + |P| ≤ 2n` then `D*_{2n}(m) ≤ 2n`   (`lift_crossing`),

i.e. **a binding at level `n` depth `m−1` together with a small plateau forces a binding at level
`2n` depth `m`** — the one-sided propagation of `m*` up the tower (E5: `m*(2n) ≤ m*(n)+1`).

## Honest scope (what is NOT proven)

This brick is the **covering ⟹ count-lift** half. It does NOT establish:
* that the doubling embedding `φ` actually realizes the covering `B' ⊆ φ '' B ∪ P`
  (that is the *dynamics* of the 2-adic Gauss-period recursion P4, an input here), nor
* that the plateau term `|P|` is small (`O(1)` or `O(n)`); the *plateau excess per tower level*
  is precisely the open quantity flagged in E5 / E7 (BCHKS 1.12).
Both are taken as hypotheses (`hcover`, and the numeric bound in `lift_crossing`). This is an
honest **REDUCED-style** assembly stated as clean axiom-clean bricks: given the covering and a
plateau budget, the one-sided lift and its crossing consequence follow unconditionally.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB25

open ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {ι : Type*} [DecidableEq ι] {κ : Type*} [DecidableEq κ]

/-- **The one-sided bad-count lift (E5).**  If the level-`2n` depth-`m` bad set `B'` is covered by
the doubling-image `φ '' B` of the level-`n` depth-`(m−1)` bad set `B` together with the plateau
set `P`, then
  `|B'| ≤ |B| + |P|`,
i.e. `D*_{2n}(m) ≤ D*_n(m−1) + |P|` with plateau term `|P|`.

Pure covering cardinality: `card_le_card` on the cover, `card_union_le`, `card_image_le`. -/
theorem bad_count_lift
    (B' : Finset κ) (B : Finset ι) (P : Finset κ) (φ : ι → κ)
    (hcover : B' ⊆ B.image φ ∪ P) :
    B'.card ≤ B.card + P.card := by
  calc
    B'.card ≤ (B.image φ ∪ P).card := Finset.card_le_card hcover
    _ ≤ (B.image φ).card + P.card := Finset.card_union_le _ _
    _ ≤ B.card + P.card := Nat.add_le_add_right (Finset.card_image_le) _

/-- **The lift in orbit-count form.**  Substituting the free-action identities
`|B| = N·S` (level `n`) and `|P| = N_P·S_P` (plateau) into `bad_count_lift` re-expresses the lift
of the level-`2n` count `|B'|` purely through the orbit counts `N`, `N_P` and orbit sizes `S`,
`S_P`. -/
theorem bad_count_lift_orbit
    (B' : Finset κ) (B : Finset ι) (P : Finset κ) (φ : ι → κ)
    {N S N_P S_P : ℕ}
    (hcover : B' ⊆ B.image φ ∪ P)
    (hB : B.card = N * S) (hP : P.card = N_P * S_P) :
    B'.card ≤ N * S + N_P * S_P := by
  have h := bad_count_lift B' B P φ hcover
  rwa [hB, hP] at h

/-- **The crossing consequence of the lift (E5 propagation of `m*`).**  Working at level `2n`
(budget `2n`), if the carried-over level-`n` depth-`(m−1)` count plus the plateau term is within
the level-`2n` budget,
  `D*_n(m−1) + |P| ≤ 2n`,
then the lift forces the level-`2n` depth-`m` count under budget,
  `D*_{2n}(m) ≤ 2n`.
Concretely, with `|B'| = N'·S'` (free action at level `2n`) and the supply identity `S'·d' = 2n`,
this binding is equivalent to the orbit-count test `N' ≤ d'` (via `crossing_law`).  So a binding at
level `n` depth `m−1` (with small plateau) propagates to a binding at level `2n` depth `m`. -/
theorem lift_crossing
    (B' : Finset κ) (B : Finset ι) (P : Finset κ) (φ : ι → κ)
    {N' S' d' twon : ℕ}
    (hcover : B' ⊆ B.image φ ∪ P)
    (hbudget : B.card + P.card ≤ twon)
    (hS' : 0 < S') (hsupply : S' * d' = twon) (hid' : B'.card = N' * S') :
    B'.card ≤ twon ∧ (B'.card ≤ twon ↔ N' ≤ d') := by
  refine ⟨le_trans (bad_count_lift B' B P φ hcover) hbudget, ?_⟩
  exact crossing_law hS' hsupply hid'

/-- **Non-vacuity / sanity.**  A concrete instance of the lift: level-`n` bad set `B = {0,1} ⊆ ℕ`,
doubling embedding `φ = (2··)` (so `φ '' B = {0,2}`), plateau `P = {1,3}`; then the level-`2n` bad
set `B' = {0,1,2,3}` is covered by `φ '' B ∪ P = {0,1,2,3}`, and indeed
`|B'| = 4 ≤ |B| + |P| = 2 + 2`. -/
example :
    ({0, 1, 2, 3} : Finset ℕ).card
      ≤ ({0, 1} : Finset ℕ).card + ({1, 3} : Finset ℕ).card := by
  apply bad_count_lift ({0, 1, 2, 3} : Finset ℕ) ({0, 1} : Finset ℕ)
    ({1, 3} : Finset ℕ) (fun x => 2 * x)
  decide

end ArkLib.ProximityGap.BridgeB25

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB25.bad_count_lift
#print axioms ArkLib.ProximityGap.BridgeB25.bad_count_lift_orbit
#print axioms ArkLib.ProximityGap.BridgeB25.lift_crossing
