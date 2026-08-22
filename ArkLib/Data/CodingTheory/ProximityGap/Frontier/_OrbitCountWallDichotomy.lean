/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A2OnsetLatticeMinimum

/-!
# The orbit-count wall, named — the saddle dichotomy `onset-saves ∨ orbit-wall-carries` (#444, Lane 2)

Shaw's `_A2OnsetLatticeMinimum` (`ef3305f3f`) names — *in prose only* — the surviving obligation:

> the conjecture `A_r ≤ (q−1)·Wick_r` does NOT follow from onset/`λ₁`; it requires the **orbit-count
> growth** … to stay `≤ Wick_r/n` uniformly over the worst prime — the BGK/Paley wall.
> … once a short relation exists at depth `≤ r` (which the pigeonhole forces at prize scale),
> `OnsetSavesSaddle` FAILS, so the saddle bound must come from `OrbitCountWall`.

Only `OnsetSavesSaddle` is a kernel Prop; `OrbitCountWall` and the dichotomy are prose. This file
turns them into kernel-checked statements, closing that gap.

## What this file defines + proves (Lane-2 reduction backbone — no probe asserted)

* `OrbitCountWall m g r Wick n` — the **per-shell orbit-count obligation**: the number `orbitCount`
  of `ζ`-orbits of nonzero short lattice vectors of `ℓ¹`-weight `≤ 2r` is at most `Wick / n` (the
  saddle budget divided by the orbit `n`-factor). This is exactly the BGK/Paley wall named in prose.

* `saddle_obligation_dichotomy` — the **named dichotomy**: at the saddle depth `r`, *either*
  `OnsetSavesSaddle` (the lattice has no short vector, `W_r = 0`, onset discharges it) *or*
  `¬OnsetSavesSaddle` (onset fails) — in which case the surviving obligation is `OrbitCountWall`,
  *provided* the orbit→moment transfer `OrbitWallImpliesSaddle` holds. The transfer (orbit-count
  control ⟹ saddle moment bound) is carried as an **explicit hypothesis**, never larped.

* `saddle_bound_of_onset_fail_and_wall` — the **onset-fails branch**: if onset fails and both the
  orbit-count wall and the transfer hold, the saddle moment bound `SaddleBound` follows. This is the
  exact content of "the saddle bound must come from `OrbitCountWall`".

* `pigeonhole_routes_to_orbit_wall` — wires Shaw's pigeonhole: at prize scale (`p < S.card`) onset
  *provably* fails, so the saddle bound — if it holds at all — is routed entirely through the
  orbit-count wall, never through onset.

## Honest scope

Lane-2 reduction backbone. Real kernel for the onset side (Shaw's pigeonhole) and the boolean
structure of the dichotomy; the orbit→moment transfer `OrbitWallImpliesSaddle` is an **explicit
hypothesis** (the orbit-count → moment-bound implication lives in the deep-band orbit machinery and
is itself conditional on the worst-prime control = the open wall). No CORE upper bound, no
cancellation, no completion, no anti-concentration, no capacity claim; the orbit-count wall itself
(`OrbitCountWall` uniform over the worst prime) is exactly the open core and is **not** proved here.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy

open ProximityGap.Frontier.A2OnsetLatticeMinimum

/-- The **per-shell orbit-count wall** (named). `orbitCount r` is the number of `ζ`-orbits of nonzero
short lattice vectors of `ℓ¹`-weight `≤ 2r`; the wall is that it stays within the saddle budget
`Wick` divided by the orbit `n`-factor. This is the BGK/Paley obligation that survives once onset
fails. Stated abstractly: `n · orbitCount r ≤ Wick r`. -/
def OrbitCountWall (orbitCount : ℕ → ℝ) (Wick : ℕ → ℝ) (n : ℝ) (r : ℕ) : Prop :=
  n * orbitCount r ≤ Wick r

/-- The orbit→moment **transfer** (carried as a hypothesis, not larped): for the depth `r`, if onset
fails *and* the per-shell orbit-count wall holds, then the saddle moment bound `SaddleBound r` holds.
The implication is exactly the deep-band orbit→moment step, itself conditional on worst-prime control
(= the open wall), so we keep it as an explicit predicate. -/
def OrbitWallImpliesSaddle
    (m : ℕ) {p : ℕ} (g : ZMod p)
    (orbitCount Wick : ℕ → ℝ) (n : ℝ) (SaddleBound : ℕ → Prop) : Prop :=
  ∀ r : ℕ, ¬ OnsetSavesSaddle m g r → OrbitCountWall orbitCount Wick n r → SaddleBound r

/-- **The saddle dichotomy (named).** At depth `r`, either `OnsetSavesSaddle` discharges the saddle
(no short vector, `W_r = 0`), or onset fails and the obligation passes to the orbit-count wall. This
is the boolean backbone of Shaw's prose verdict. -/
theorem saddle_obligation_dichotomy
    (m : ℕ) {p : ℕ} (g : ZMod p) (r : ℕ) :
    OnsetSavesSaddle m g r ∨ ¬ OnsetSavesSaddle m g r :=
  Classical.em _

/-- **The onset-fails branch.** If onset fails at depth `r`, the per-shell orbit-count wall holds,
and the orbit→moment transfer holds, then the saddle moment bound follows. This is the exact content
of "the saddle bound must come from `OrbitCountWall`". -/
theorem saddle_bound_of_onset_fail_and_wall
    (m : ℕ) {p : ℕ} (g : ZMod p) (r : ℕ)
    (orbitCount Wick : ℕ → ℝ) (n : ℝ) (SaddleBound : ℕ → Prop)
    (htransfer : OrbitWallImpliesSaddle m g orbitCount Wick n SaddleBound)
    (honsetFail : ¬ OnsetSavesSaddle m g r)
    (hwall : OrbitCountWall orbitCount Wick n r) :
    SaddleBound r :=
  htransfer r honsetFail hwall

/-- **Pigeonhole routes to the orbit wall.** At prize scale, the `ℓ¹`-ball of short relations
(`p < S.card`, weight `≤ w ≤ r`) makes onset *provably* fail (Shaw's
`not_onsetSavesSaddle_of_card_gt`), so the saddle moment bound — granted the orbit-count wall and the
transfer — is routed entirely through `OrbitCountWall`, never through onset. -/
theorem pigeonhole_routes_to_orbit_wall
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ)) (hSw : ∀ a ∈ S, l1 a ≤ w) (hcard : p < S.card)
    (orbitCount Wick : ℕ → ℝ) (n : ℝ) (SaddleBound : ℕ → Prop)
    (htransfer : OrbitWallImpliesSaddle m g orbitCount Wick n SaddleBound)
    (hwall : OrbitCountWall orbitCount Wick n r) :
    ¬ OnsetSavesSaddle m g r ∧ SaddleBound r :=
  ⟨not_onsetSavesSaddle_of_card_gt p g w r hwr S hSw hcard,
   htransfer r (not_onsetSavesSaddle_of_card_gt p g w r hwr S hSw hcard) hwall⟩

end ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy
