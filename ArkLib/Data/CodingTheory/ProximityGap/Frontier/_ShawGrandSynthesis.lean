/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorDischarged

/-!
# The grand Shaw-value synthesis: prize ⇔ Sh(n)=O(1), and door (iv) is the only door (#444)

Shaw's "Shaw Value" essay (#444, 2026-06-18) produced TWO separable results that the campaign has
each formalized axiom-clean in their own files, but which were never composed into a single
statement:

* **The reduction** (`_ShawValueCapstone`): on a positive-scale prize family, the slogan
  `prize ⇔ Sh(n)=O(1)` is the literal equivalence
  `ShawOOneOn q n M ↔ CorePrizeBoundOn q n M`
  (`ShawValueCapstone.shawOOneOn_iff_corePrizeBoundOn`) — bounding the dimensionless Shaw value by an
  absolute constant is *exactly* the prize-scale `√(n·log(q/n))` CORE bound, with the same constant
  and no hidden loss.

* **The no-fifth-door discharge** (`_NoFifthDoorDischarged`): at the concrete proven door scales, in
  the prize regime, any `Mechanism` that certifies a prize-scale (`√n`) bound must be door (iv)
  (`NoFifthDoorDischarged.forces_doorIV_atProvenScale`) — the classical doors (i)/(ii)/(iii) are
  discharged from theorems (completion = √q ceiling; moment/EVT = SOTA `C·n^{1−δ}`), with no abstract
  `hclassicalOvershoots` postulate.

This file is the **composition capstone**: a single named theorem that conjoins the two halves, plus
the headline corollary stating both facts together. No file previously imported BOTH the Shaw-value
capstone and the no-fifth-door capstone, and no theorem conjoined the reduction with the door
discharge; that single conjoined statement is the Boneh-grade deliverable a referee cites — "the
proximity prize reduces to bounding Shaw's value, AND door (iv) is the only mechanism that can
supply that bound."

## Honesty
This is PURE COMPOSITION of two already-proven, already-axiom-clean theorems
(`shawOOneOn_iff_corePrizeBoundOn` and `forces_doorIV_atProvenScale`). It introduces **no new
mathematical content**: no CORE / cancellation / completion / moment-saving / anti-concentration /
capacity claim, and it does NOT prove door (iv) is *achievable*. The CORE inequality
`M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**. The contribution is purely organizational — assembling the
two standing results into the single citable synthesis statement, so the synthesis itself is
kernel-checked rather than left as prose connecting two separate files.

Note: the two halves use intentionally distinct scales. The reduction half is stated against the
campaign's Shaw scale `shawScale q n = √(n·log(q/n))` (the BGK-shaped normalization target). The door
half is stated against the genuine prize floor `prizeScale n = √n`. They are *different objects* and
this synthesis does NOT identify them; it conjoins the two independent facts. Identifying the two
scales is exactly the open `√L`-gap that door (iv) must close, and which this file makes no claim
about.
-/

namespace ArkLib.ProximityGap.Frontier.ShawGrandSynthesis

open ProximityGap.Frontier.ShawValueCapstone
open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
open ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged

/-- **The grand synthesis (conjoined form).**  Fix a positive-scale prize family
`q n M : ι → ℝ` (so the Shaw normalization is well defined) and a single classical-door mechanism `m`
sitting at its proven scale in the per-instance prize regime `(n₀, L₀, q₀)` with SOTA constant `C`,
exponent `δ < 1/2`, `L₀ > 1`, `n₀·L₀ ≤ q₀`, and the proven SOTA domination
`bgkScale n₀ L₀ ≤ C·n₀^{1−δ}`.  Then BOTH:

* (reduction)  `ShawOOneOn q n M ↔ CorePrizeBoundOn q n M`  — bounding Shaw's value by an absolute
  constant is exactly the prize-scale CORE bound; and
* (no fifth door)  if `m` certifies a `prizeScale n₀ = √n₀` bound, then `m.door = newEvaluation` —
  door (iv) is the only door that can supply it.

Both conjuncts are the literal statements proven in `_ShawValueCapstone` and `_NoFifthDoorDischarged`;
this theorem only packages them together. -/
theorem prize_reduces_to_doorIV
    {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι, 0 < shawScale (q i) (n i))
    {m : Mechanism} {n₀ L₀ q₀ C δ : ℝ}
    (hn₀ : 0 < n₀) (hL₀ : 1 < L₀) (hq₀ : n₀ * L₀ ≤ q₀)
    (hsota : bgkScale n₀ L₀ ≤ C * n₀ ^ (1 - δ))
    (hatScale : AtProvenScale m n₀ q₀ C δ) :
    (ShawOOneOn q n M ↔ CorePrizeBoundOn q n M) ∧
      (m.certScale ≤ prizeScale n₀ → m.door = DoorType.newEvaluation) :=
  ⟨shawOOneOn_iff_corePrizeBoundOn hscale,
    fun hcert => forces_doorIV_atProvenScale hn₀ hL₀ hq₀ hsota hatScale hcert⟩

/-- **The grand synthesis (prize-regime scale guard).**  Same conjoined statement, but the Shaw-scale
positivity is supplied from the prize-regime guard `q_i > n_i > 0` on the family, so no separate scale
hypothesis is needed for the reduction half. -/
theorem prize_reduces_to_doorIV_of_pos_lt
    {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i)
    {m : Mechanism} {n₀ L₀ q₀ C δ : ℝ}
    (hn₀ : 0 < n₀) (hL₀ : 1 < L₀) (hq₀ : n₀ * L₀ ≤ q₀)
    (hsota : bgkScale n₀ L₀ ≤ C * n₀ ^ (1 - δ))
    (hatScale : AtProvenScale m n₀ q₀ C δ) :
    (ShawOOneOn q n M ↔ CorePrizeBoundOn q n M) ∧
      (m.certScale ≤ prizeScale n₀ → m.door = DoorType.newEvaluation) :=
  prize_reduces_to_doorIV
    (fun i => shawScale_pos_of_pos_lt (hn i) (hnq i)) hn₀ hL₀ hq₀ hsota hatScale

/-- **Headline (eventual, family form).**  The fully discharged synthesis: for any SOTA constant
`C > 0`, exponent `δ < 1/2`, prize-regime `L > 1`, there is a threshold `N₀` such that for every
prize-family with Shaw-scale positivity and every prize-regime instance `n ≥ N₀` (and `≥ 2`),
`n·L ≤ q`:

* the reduction equivalence `ShawOOneOn ↔ CorePrizeBoundOn` holds for the family, AND
* every proven-scale mechanism that certifies a `√n` prize-scale bound is door (iv).

This is the headline a referee cites: in the prize regime, asymptotically, the proximity prize is
*equivalent* to bounding Shaw's value AND can *only* be supplied by door (iv).  Pure composition of
`shawOOneOn_iff_corePrizeBoundOn` with `forces_doorIV_eventually`; CORE stays open. -/
theorem prize_reduces_to_doorIV_eventually
    {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι, 0 < shawScale (q i) (n i))
    {L q₀ C δ : ℝ} (hC : 0 < C) (hL : 1 < L) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    (ShawOOneOn q n M ↔ CorePrizeBoundOn q n M) ∧
      ∃ N₀ : ℝ, ∀ n' : ℝ, N₀ ≤ n' → 2 ≤ n' → n' * L ≤ q₀ →
        ∀ m : Mechanism, AtProvenScale m n' q₀ C δ → m.certScale ≤ prizeScale n' →
          m.door = DoorType.newEvaluation :=
  ⟨shawOOneOn_iff_corePrizeBoundOn hscale,
    forces_doorIV_eventually (L := L) (q := q₀) hC hL hLnn hδ⟩

end ArkLib.ProximityGap.Frontier.ShawGrandSynthesis
