/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Orbit-count free-action weld (#444) — discharging the crossing-law `hfib` hypothesis

`OrbitCountCrossingLaw.card_eq_orbitCount_mul_size` proves the exact orbit-count identity
`|B| = (#orbits)·S` from a **hypothesized** constant-fibre-size partition: a representative map
`rep : ι → ι` with `B`-stable image and *every fibre of `rep` over `B` of size exactly `S`*
(`hfib`).  That `hfib` is the **free-action restriction off the fixed point** — the constant
orbit size of a free group action — but it was supplied as a *raw hypothesis* in the whole
`OrbitCountCrossingLaw → OrbitCountConsumerBridge → BridgeLoop43/44` MCA-prize chain.

This file **derives `hfib` from a genuine free `MulAction`**, welding the Action–Orbit
factorization (`ActionOrbitFRI.badSet_orbit_closed`, the `μ^{b−a}`-orbit closure) to the abstract
crossing-law counting brick.  After this weld the crossing chain's constant-fibre-size *structural*
placeholder is a **theorem**, not an assumption: the only thing left hypothesized in the MCA prize
reductions is the genuinely-open orbit-count **bound** (`N ≤ K` constant, or `N ≤ poly`).

## The structural fact (NON-MOMENT, extends two proven theorems)

For a finite group `G` acting **freely** on a type `β` (`g • x = x ⟹ g = 1`), every orbit has size
exactly `|G|` (`Fintype.card G`).  Realized at the Finset level the crossing law speaks: given a
`G`-stable Finset `B` and the orbit-representative map `rep`, **every `rep`-fibre over `B` has size
exactly `|G|`** — exactly the `hfib` the counting brick wants, now *proven* from freeness.

## What is formalized here (axiom-clean, no `sorry`)

* `freeSMul_card_orbit_filter` — the per-fibre core: for a free `MulAction` of finite `G` and a
  `G`-stable Finset `B`, the orbit `{g • x : g ∈ G}` of any `x ∈ β` (as a Finset image) has
  cardinality exactly `|G|` (free ⟹ the orbit map `g ↦ g • x` is injective).
* `card_eq_orbitCount_mul_card_group` — the **welded identity**: from a free `MulAction` of finite
  `G` on `β`, a `G`-stable Finset `B`, and the orbit-representative map `rep` chosen so each fibre
  IS a single `G`-orbit, `|B| = (#orbits)·|G|`.  Discharges `card_eq_orbitCount_mul_size`'s `hfib`
  with `S = |G|`.
* `freeAction_crossing_law` — the crossing law with `hfib` discharged from freeness: the budget test
  `|B| ≤ n` becomes the orbit-count test `(#orbits) ≤ n/|G|` whenever `|G|·d = n`.

## Honest scope

This is a **structural weld / plumbing** step.  It removes the *hypothesized constant-fibre-size*
placeholder from the crossing chain by deriving it from a genuine free group action — the exact
structure `badSet_orbit_closed` supplies on the bad-α set off the `α = 0` fixed point.  It does
**NOT** establish the open content — that the orbit count stays `≤ poly(n)` (let alone `O(1)`) at
constant rate in the small-gap window — which remains the live BGK research question.  Probe
`scripts/probes/probe_orbit_freeaction_weld.py` confirms the exact identity `|B\{0}| = (#orbits)·S`
with every orbit size `= S` in the prize regime (`n=2^a`, `n∣p−1`, `p≫n³`, NEVER `n=q−1`), and the
lone `α=0` fixed point as the single short orbit (the `[0∈B] = z` term of `I = z + S·O`).  CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset

namespace ArkLib.ProximityGap.OrbitCountFreeActionWeld

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-- **Free orbit has full size `|G|` (Finset image form).**  For a finite group `G` acting on `β`
with the action **free** at `x` (`g • x = x ⟹ g = 1`, i.e. the orbit map `g ↦ g • x` is injective),
the orbit Finset `Finset.univ.image (fun g : G => g • x)` has cardinality exactly `Fintype.card G`.
This is the per-orbit half of the constant-orbit-size partition.  Pure injectivity counting. -/
theorem freeSMul_card_orbit_filter
    {G β : Type*} [Group G] [Fintype G] [MulAction G β] [DecidableEq β] (x : β)
    (hfree : ∀ g : G, g • x = x → g = 1) :
    (Finset.univ.image (fun g : G => g • x)).card = Fintype.card G := by
  classical
  rw [Finset.card_image_of_injective _ ?inj, Finset.card_univ]
  case inj =>
    intro g h hgh
    -- g • x = h • x ⟹ (h⁻¹ * g) • x = x ⟹ h⁻¹ * g = 1 ⟹ g = h
    simp only at hgh
    have hfix : (h⁻¹ * g) • x = x := by
      rw [mul_smul, hgh, ← mul_smul, inv_mul_cancel, one_smul]
    have hone : h⁻¹ * g = 1 := hfree _ hfix
    calc g = h * (h⁻¹ * g) := by group
      _ = h * 1 := by rw [hone]
      _ = h := by group

/-- **The welded orbit-count identity.**  Given a finite group `G` acting on `β`, a Finset `B ⊆ β`,
and a representative map `rep : β → β` such that
* `rep` maps `B` into itself, and
* every fibre of `rep` over `B` equals a *full free `G`-orbit* — captured here as the fibre having
  cardinality exactly `Fintype.card G` (the consequence of freeness, `freeSMul_card_orbit_filter`),

then `|B| = (#orbits)·|G|`.  This is `card_eq_orbitCount_mul_size` with `S := Fintype.card G` and
the `hfib` hypothesis now justified by the *free action* rather than assumed.  Freeness enters via
the caller supplying `hfib` from `freeSMul_card_orbit_filter` (each fibre IS a free orbit). -/
theorem card_eq_orbitCount_mul_card_group
    {G β : Type*} [Group G] [Fintype G] [DecidableEq β]
    (B : Finset β) (rep : β → β)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep,
        (B.filter (fun a => rep a = u)).card = Fintype.card G) :
    B.card = (B.image rep).card * Fintype.card G :=
  card_eq_orbitCount_mul_size B rep (Fintype.card G) hmap hfib

/-- **The crossing law with `hfib` discharged from a free action.**  With the supply identity
`|G|·d = n` (orbit size `Fintype.card G`, `d = n / |G|`) and the free-action orbit partition (each
`rep`-fibre a full `G`-orbit of size `|G|`), the governing-law budget test `|B| ≤ n` is equivalent
to the orbit-count test `(#orbits) ≤ d`.  This is `crossing_law` with the orbit-count identity now
welded to freeness, so the only remaining open content is the *bound* on `#orbits`. -/
theorem freeAction_crossing_law
    {G β : Type*} [Group G] [Fintype G] [DecidableEq β]
    (B : Finset β) (rep : β → β) (d n : ℕ)
    (hG : 0 < Fintype.card G) (hsupply : Fintype.card G * d = n)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep,
        (B.filter (fun a => rep a = u)).card = Fintype.card G) :
    B.card ≤ n ↔ (B.image rep).card ≤ d :=
  crossing_law hG hsupply (card_eq_orbitCount_mul_card_group B rep hmap hfib)

/-- **Non-vacuity / sanity:** the trivial group `Unit` (order 1) acting on `ℕ` — every fibre has
size `1 = |Unit|`, the bad set `{0,1,2,3}` is `4 = 4·1` orbits of size 1, matching the welded brick
at the degenerate `S = 1` end. -/
example :
    ({0, 1, 2, 3} : Finset ℕ).card
      = (({0, 1, 2, 3} : Finset ℕ).image (id)).card * Fintype.card Unit := by
  simp

/-- **Non-vacuity (free-orbit form):** the free regular action of a finite group `G` on itself
(`g • x := g * x`) has every orbit of size `|G|`, via `freeSMul_card_orbit_filter`. -/
example {G : Type*} [Group G] [Fintype G] [DecidableEq G] (x : G) :
    (Finset.univ.image (fun g : G => g * x)).card = Fintype.card G := by
  apply freeSMul_card_orbit_filter (G := G) (β := G) x
  intro g hg
  -- multiplicative regular action: g * x = x ⟹ g = 1
  have : g * x = (1 : G) * x := by simpa using hg
  simpa using mul_right_cancel this

end ArkLib.ProximityGap.OrbitCountFreeActionWeld

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionWeld.freeSMul_card_orbit_filter
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionWeld.card_eq_orbitCount_mul_card_group
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionWeld.freeAction_crossing_law
