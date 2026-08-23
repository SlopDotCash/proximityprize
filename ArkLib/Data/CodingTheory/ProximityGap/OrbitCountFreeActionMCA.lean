/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountFreeActionWeld
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountConsumerBridge

/-!
# Free-action MCA consumers (#444) — the prize shape from a genuine free `MulAction`

`OrbitCountConsumerBridge.mca_prize_of_orbit_partition` / `_poly` discharge the *hypothesized*
real inequality `Vcard ≤ N·S` of the `BridgeLoop43/44` MCA reductions from the **abstract**
orbit-count identity `card_eq_orbitCount_mul_size`, but they still carry that identity's raw
`hfib` (constant fibre size) hypothesis.  `OrbitCountFreeActionWeld` proved `hfib` follows from a
genuine **free `MulAction`** of a finite group `G` (orbit size `= |G|`).

This file composes the two: it states the MCA prize consumers taking a **free group action**
in place of the raw `hfib`.  After this, the path

  free `MulAction` of finite `G`  ⟹  `|B| = (#orbits)·|G|`  ⟹  MCA term `≤` Conjecture-1.1 shape

is fully assembled with **no hypothesized constant-fibre-size placeholder anywhere** — the only
input that stays open is the orbit-count *bound* itself (`N ≤ K` constant, or `N ≤ (2^m)^d`
polynomial), which is the genuine BGK research question.

## What is formalized here (axiom-clean, no `sorry`)

* `mca_prize_of_free_action` — `BridgeLoop43`'s constant-orbit-count MCA prize, with the partition
  hypothesis supplied by a free `MulAction` (`hfib` from `freeSMul_card_orbit_filter`): from the
  free action + the open *constant* bound `#orbits ≤ K`, the MCA term `|B|/q² ≤ K/q`.
* `mca_prize_of_free_action_poly` — the same for `BridgeLoop44`'s *polynomial* orbit-count bound:
  from the free action + `#orbits ≤ (2^m)^d`, `|B|/q² ≤ (1/q)·(2^m)^{d+1}`.

## Honest scope

Pure plumbing / weld, identical in spirit to `OrbitCountFreeActionWeld`.  It removes the last
*structural* placeholder (the constant-fibre-size hypothesis) from the orbit-count MCA-prize chain
by sourcing it from a free group action.  It does **NOT** bound the orbit count — the open content
(`#orbits ≤ poly(n)`, let alone `O(1)`, at constant rate in the small-gap window; orbit count
`= BGK` at the window interior, refuted as `O(1)` at `n=8`) remains the live wall.  CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset

namespace ArkLib.ProximityGap.OrbitCountFreeActionMCA

open ArkLib.ProximityGap.OrbitCountFreeActionWeld
open ArkLib.ProximityGap.OrbitCountConsumerBridge

/-- **MCA prize from a free action (constant orbit-count bound).**
`OrbitCountConsumerBridge.mca_prize_of_orbit_partition` with its `hfib` supplied from a genuine
free `MulAction` of finite `G` (each `rep`-fibre over `B` a full free `G`-orbit of size `|G|`).
From the free action + the open *constant* orbit-count bound `#orbits ≤ K` and `|G| ≤ 2^m ≤ q`,
the MCA term `|B|/q²` is at most the Conjecture-1.1 prize shape `K/q`. -/
theorem mca_prize_of_free_action
    {G β : Type*} [Group G] [Fintype G] [DecidableEq β]
    (B : Finset β) (rep : β → β)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep,
        (B.filter (fun a => rep a = u)).card = Fintype.card G)
    {q K : ℝ} {m : ℕ}
    (hq : 0 < q) (hKnn : 0 ≤ K)
    (hN : ((B.image rep).card : ℝ) ≤ K)
    (hS : (Fintype.card G : ℝ) ≤ (2 : ℝ) ^ m)
    (hqbig : (2 : ℝ) ^ m ≤ q) :
    (B.card : ℝ) / q ^ 2 ≤ K / q :=
  mca_prize_of_orbit_partition B rep (Fintype.card G) hmap hfib hq hKnn hN hS hqbig

/-- **MCA prize from a free action (polynomial orbit-count bound).**
`OrbitCountConsumerBridge.mca_prize_of_orbit_partition_poly` with `hfib` from a free `MulAction`.
From the free action + the open *polynomial* orbit-count bound `#orbits ≤ (2^m)^d` and
`|G| ≤ 2^m`, the MCA term `|B|/q²` lands on the weaker prize RHS `(1/q)·(2^m)^{d+1}`. -/
theorem mca_prize_of_free_action_poly
    {G β : Type*} [Group G] [Fintype G] [DecidableEq β]
    (B : Finset β) (rep : β → β)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep,
        (B.filter (fun a => rep a = u)).card = Fintype.card G)
    {q : ℝ} {m d : ℕ}
    (hq : 1 ≤ q)
    (hN : ((B.image rep).card : ℝ) ≤ ((2 : ℝ) ^ m) ^ d)
    (hS : (Fintype.card G : ℝ) ≤ (2 : ℝ) ^ m) :
    (B.card : ℝ) / q ^ 2 ≤ (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) :=
  mca_prize_of_orbit_partition_poly B rep (Fintype.card G) hmap hfib hq hN hS

end ArkLib.ProximityGap.OrbitCountFreeActionMCA

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.mca_prize_of_free_action
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.mca_prize_of_free_action_poly
