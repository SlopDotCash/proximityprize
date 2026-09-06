/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Close C25 — discharging B25's covering hypothesis (`hcover`), target E5, #444

## What B25 left open

`_BridgeB25.bad_count_lift` proves the one-sided dyadic lift

  `|B'| ≤ |B| + |P|`,    i.e.   `D*_{2n}(m) ≤ D*_n(m−1) + |P|`

**from a covering hypothesis** `hcover : B' ⊆ B.image φ ∪ P`.  B25's own honest-scope note flags
that hypothesis as the half it does *not* establish — "that the doubling embedding `φ` actually
realizes the covering".

## What this file closes (axiom-clean, no `sorry`)

The covering `B' ⊆ B.image φ ∪ P` is **not** a piece of dynamics that needs the 2-adic
Gauss-period recursion (P4) — it is a *definitional* fact, *once the plateau set `P` is named
correctly*.  The genuinely-new plateau elements are, by definition,

  `P := B' \ B.image φ`

= the level-`2n` bad-γ that do **not** come from a level-`n` bad-γ under the doubling embedding
`φ`.  With `P` so defined, the dichotomy

  every level-`2n` bad-γ is *either* in `B.image φ` (carried over from level `n`)
  *or* in `P` (genuinely new)

holds **unconditionally** by pure set theory (`Finset.sdiff` / `subset_union`).  We therefore:

1. `doubling_cover` — prove the covering `B' ⊆ B.image φ ∪ P` for the canonical plateau
   `P = B' \ B.image φ`, with **no hypothesis** (it is `Finset` set theory: `a ∈ B' ⟹`
   `a ∈ B.image φ ∨ a ∈ B' \ B.image φ` by excluded middle on membership).

2. `bad_count_lift_closed` — feed `doubling_cover` into the cardinality bound, getting the lift

     `|B'| ≤ |B| + |B' \ B.image φ|`

   with the **plateau width `|B' \ B.image φ|` as the named open quantity** — no `hcover` input.

3. `plateau_width_def` / `plateau_eq_card_sub_image_inter` — pin the plateau width exactly
   (`|P| = |B'| − |B' ∩ B.image φ|`), so the lift's overhead is *visibly* the count of new
   level-`2n` bad-γ.

4. `lift_crossing_closed` — the crossing consequence (E5 propagation of `m*`) with the covering
   discharged: a level-`n` depth-`(m−1)` binding **plus a plateau budget on `|B' \ B.image φ|`**
   forces the level-`2n` depth-`m` binding.  The crossing equivalence (`N' ≤ d'`) is reused
   verbatim from the substrate `OrbitCountCrossingLaw.crossing_law`.

## Honest scope — what remains open (the wall, B28)

The covering is now **free**.  What is *not* (and cannot be — it is the prize input) closed here is
the **SIZE** of the plateau width `|B' \ B.image φ|`: that it stays `O(1)` (or `O(n)`) per tower
level is exactly the *plateau-excess / `m*`-growth* bound = **BCHKS Conjecture 1.12** (E5/E7),
named as an explicit `Prop` in B28/B31/B32/B50 and never discharged.  This file removes the
*covering* assumption from B25's lift and isolates the plateau width as the lone open quantity.
-/

open Finset

namespace ArkLib.ProximityGap.Close25

open ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {ι : Type*} [DecidableEq ι] {κ : Type*} [DecidableEq κ]

/-- **The doubling cover is free (discharge of B25's `hcover`).**

For the *canonical* plateau set `P := B' \ B.image φ`, the covering

  `B' ⊆ B.image φ ∪ (B' \ B.image φ)`

holds **with no hypothesis**: every level-`2n` bad-γ `a ∈ B'` is *either* carried over from a
level-`n` bad-γ (`a ∈ B.image φ`) *or* genuinely new (`a ∈ B' \ B.image φ`).  This is the
set-theoretic dichotomy `B' ⊆ B.image φ ∪ (B' \ B.image φ)` = `Finset.subset_union_of_sdiff`-style
reasoning, here by excluded middle on `a ∈ B.image φ`. -/
theorem doubling_cover (B' : Finset κ) (B : Finset ι) (φ : ι → κ) :
    B' ⊆ B.image φ ∪ (B' \ B.image φ) := by
  intro a ha
  rw [Finset.mem_union]
  by_cases hb : a ∈ B.image φ
  · exact Or.inl hb
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨ha, hb⟩)

/-- **The one-sided bad-count lift with the covering discharged.**

Combining `doubling_cover` (the *free* covering, no `hcover`) with the cardinality argument
(`card_le_card` + `card_union_le` + `card_image_le`) gives the one-sided lift

  `|B'| ≤ |B| + |B' \ B.image φ|`,

i.e. `D*_{2n}(m) ≤ D*_n(m−1) + |P|` with the **canonical plateau `P = B' \ B.image φ`** — and no
hypothesis beyond the data `B', B, φ`.  The plateau width `|B' \ B.image φ|` is the lone open
quantity (the wall, B28). -/
theorem bad_count_lift_closed (B' : Finset κ) (B : Finset ι) (φ : ι → κ) :
    B'.card ≤ B.card + (B' \ B.image φ).card := by
  calc
    B'.card ≤ (B.image φ ∪ (B' \ B.image φ)).card :=
      Finset.card_le_card (doubling_cover B' B φ)
    _ ≤ (B.image φ).card + (B' \ B.image φ).card := Finset.card_union_le _ _
    _ ≤ B.card + (B' \ B.image φ).card := Nat.add_le_add_right (Finset.card_image_le) _

/-- **Plateau width, exactly.**  The canonical plateau width is the count of level-`2n` bad-γ that
are *not* carried over from level `n`:

  `|B' \ B.image φ| = |B'| − |B' ∩ B.image φ|`.

So the lift's overhead is *visibly* the number of genuinely-new level-`2n` bad-γ. -/
theorem plateau_eq_card_sub_image_inter (B' : Finset κ) (B : Finset ι) (φ : ι → κ) :
    (B' \ B.image φ).card = B'.card - (B' ∩ B.image φ).card :=
  Nat.eq_sub_of_add_eq (Finset.card_sdiff_add_card_inter B' (B.image φ))

/-- **Plateau width is the carried-over deficit.**  Equivalently, the number of carried-over
level-`2n` bad-γ plus the plateau width recovers `|B'|`:

  `|B' ∩ B.image φ| + |B' \ B.image φ| = |B'|`.

This makes the lift *tight in structure*: the level-`2n` count splits exactly into the part
explained by level `n` and the new plateau part. -/
theorem inter_add_plateau_eq (B' : Finset κ) (B : Finset ι) (φ : ι → κ) :
    (B' ∩ B.image φ).card + (B' \ B.image φ).card = B'.card := by
  rw [Finset.card_inter_add_card_sdiff]

/-- **The crossing consequence with the covering discharged (E5 propagation of `m*`).**

Working at level `2n` (budget `twon = 2n`): if the carried-over level-`n` depth-`(m−1)` count `|B|`
plus the **canonical plateau width** `|B' \ B.image φ|` is within budget,

  `D*_n(m−1) + |B' \ B.image φ| ≤ 2n`,

then `bad_count_lift_closed` forces the level-`2n` depth-`m` count under budget,

  `D*_{2n}(m) ≤ 2n`,

and — via the free-action identity `|B'| = N'·S'` and the supply identity `S'·d' = 2n` — this
binding is equivalent (`crossing_law`, reused from the substrate) to the orbit-count test
`N' ≤ d'`.  Unlike B25's `lift_crossing`, **no `hcover` hypothesis is taken**: the covering is
discharged by `doubling_cover`.  The only remaining input is the plateau *budget* `hbudget`, whose
unconditional validity is the open `m*`-growth bound (B28). -/
theorem lift_crossing_closed
    (B' : Finset κ) (B : Finset ι) (φ : ι → κ)
    {N' S' d' twon : ℕ}
    (hbudget : B.card + (B' \ B.image φ).card ≤ twon)
    (hS' : 0 < S') (hsupply : S' * d' = twon) (hid' : B'.card = N' * S') :
    B'.card ≤ twon ∧ (B'.card ≤ twon ↔ N' ≤ d') := by
  refine ⟨le_trans (bad_count_lift_closed B' B φ) hbudget, ?_⟩
  exact crossing_law hS' hsupply hid'

/-- **Non-vacuity / sanity (genuine, not a `False`-hypothesis tautology).**

Level-`n` bad set `B = {0,1} ⊆ ℕ`, doubling embedding `φ = (2··)` (so `B.image φ = {0,2}`),
level-`2n` bad set `B' = {0,1,2,3}`.  The canonical plateau is the genuinely-new part
`B' \ B.image φ = {1,3}` (width `2`), and the lift gives `|B'| = 4 ≤ |B| + 2 = 2 + 2`, with the
covering `doubling_cover` discharging the assumption automatically. -/
example :
    ({0, 1, 2, 3} : Finset ℕ).card
      ≤ ({0, 1} : Finset ℕ).card
        + (({0, 1, 2, 3} : Finset ℕ) \ (({0, 1} : Finset ℕ).image (fun x => 2 * x))).card :=
  bad_count_lift_closed ({0, 1, 2, 3} : Finset ℕ) ({0, 1} : Finset ℕ) (fun x => 2 * x)

/-- **Sanity: the canonical plateau here is exactly `{1,3}` (width 2).** -/
example :
    (({0, 1, 2, 3} : Finset ℕ) \ (({0, 1} : Finset ℕ).image (fun x => 2 * x))).card = 2 := by
  decide

end ArkLib.ProximityGap.Close25

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Close25.doubling_cover
#print axioms ArkLib.ProximityGap.Close25.bad_count_lift_closed
#print axioms ArkLib.ProximityGap.Close25.plateau_eq_card_sub_image_inter
#print axioms ArkLib.ProximityGap.Close25.inter_add_plateau_eq
#print axioms ArkLib.ProximityGap.Close25.lift_crossing_closed
