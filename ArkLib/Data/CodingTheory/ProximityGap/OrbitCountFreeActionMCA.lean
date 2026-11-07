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

This file composes the two.  (Audit PG-066: an earlier version of this file advertised a free
action but its two theorems still took the raw `hfib` and had no `MulAction`, action or freeness
hypothesis at all.  Those two theorems are kept, renamed to what they are —
`mca_prize_of_constant_fibre` / `_poly` — and the genuine free-action consumers are new.)

* **Free-action route (new).**  Given a `MulAction` of a finite group `G` on `β`, a Finset `B`
  that is `G`-stable, freeness on `B` (`g • x = x → g = 1` for `x ∈ B`), and a representative
  map `rep` that is compatible with the orbits — `G`-invariant on `B` (`rep (g • a) = rep a`) and
  sending each `a ∈ B` into its own orbit (`rep a = g • a` for some `g`) — every `rep`-fibre over
  `B` *is* the full orbit of its representative (`fibre_eq_orbit_of_invariant_rep`), hence has
  size `|G|` by `freeSMul_card_orbit_filter` (`hfib_of_free_action`).  So `hfib` (and `hmap`)
  are **derived**, not assumed, in `mca_prize_of_free_action` / `_poly`.
* **Constant-fibre route (unchanged consumers).**  `mca_prize_of_constant_fibre` / `_poly` take
  `hfib` directly; they are the old orbit-partition consumers with `S := |G|` and use nothing of
  `G` beyond its cardinality.

## What is formalized here (axiom-clean, no `sorry`)

* `fibre_eq_orbit_of_invariant_rep`, `hfib_of_free_action` — the structural discharge above.
* `mca_prize_of_free_action` — from the free action + orbit-compatible `rep` + the open *constant*
  bound `#orbits ≤ K` (and `|G| ≤ 2^m ≤ q`): `|B|/q² ≤ K/q`.
* `mca_prize_of_free_action_poly` — the same with the *polynomial* bound `#orbits ≤ (2^m)^d`:
  `|B|/q² ≤ (1/q)·(2^m)^{d+1}`.
* `mca_prize_of_constant_fibre`, `mca_prize_of_constant_fibre_poly` — the `hfib`-taking wrappers.

## Honest scope

Plumbing.  The free-action theorems remove the constant-fibre-size hypothesis *only relative to*
the stated action, freeness and orbit/representative-compatibility hypotheses; no concrete
action on an actual bad-scalar set, and no freeness or compatible representative map for it, is
constructed here (for multiplicative dilation the zero scalar is a fixed point and must be split
off, cf. `OrbitCountFixedPointSplit`).  The quantity bounded is the abstract `|B|/q²`; the bridge
identifying it with the actual MCA event probability / bad count normalization is separate
(audit PG-053).  It does **NOT** bound the orbit count — the open content (`#orbits ≤ poly(n)`,
let alone `O(1)`, at constant rate in the small-gap window; orbit count `= BGK` at the window
interior, refuted as `O(1)` at `n=8`) remains the live wall.  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`)
stays OPEN.
-/

open Finset

namespace ArkLib.ProximityGap.OrbitCountFreeActionMCA

open ArkLib.ProximityGap.OrbitCountFreeActionWeld
open ArkLib.ProximityGap.OrbitCountConsumerBridge

/-! ### Structural discharge of `hfib` from a free action -/

/-- **Orbit/representative compatibility makes every fibre a full orbit.**  If `B` is `G`-stable,
`rep` is `G`-invariant on `B`, and each `a ∈ B` is sent by `rep` into its own `G`-orbit, then for
every representative `u ∈ rep '' B` the `rep`-fibre over `B` is exactly the orbit
`{g • u : g ∈ G}`. -/
theorem fibre_eq_orbit_of_invariant_rep
    {G β : Type*} [Group G] [Fintype G] [MulAction G β] [DecidableEq β]
    (B : Finset β) (rep : β → β)
    (hstable : ∀ g : G, ∀ a ∈ B, g • a ∈ B)
    (hrepinv : ∀ g : G, ∀ a ∈ B, rep (g • a) = rep a)
    (hrepOrbit : ∀ a ∈ B, ∃ g : G, rep a = g • a) :
    ∀ u ∈ B.image rep,
      B.filter (fun a => rep a = u) = Finset.univ.image (fun g : G => g • u) := by
  intro u hu
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨g₀, hg₀⟩ := hrepOrbit a₀ ha₀
  have hrepB : rep a₀ ∈ B := by rw [hg₀]; exact hstable g₀ a₀ ha₀
  have hidem : rep (rep a₀) = rep a₀ := by rw [hg₀, hrepinv g₀ a₀ ha₀]; exact hg₀
  ext a
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨haB, hra⟩
    obtain ⟨g, hg⟩ := hrepOrbit a haB
    exact ⟨g⁻¹, by rw [← hra, hg, inv_smul_smul]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨hstable g _ hrepB, by rw [hrepinv g _ hrepB, hidem]⟩

/-- **`hfib` from a free action.**  Under the hypotheses of `fibre_eq_orbit_of_invariant_rep`
plus freeness of the action on `B`, every `rep`-fibre over `B` has exactly `|G|` elements
(`freeSMul_card_orbit_filter`). -/
theorem hfib_of_free_action
    {G β : Type*} [Group G] [Fintype G] [MulAction G β] [DecidableEq β]
    (B : Finset β) (rep : β → β)
    (hstable : ∀ g : G, ∀ a ∈ B, g • a ∈ B)
    (hfree : ∀ x ∈ B, ∀ g : G, g • x = x → g = 1)
    (hrepinv : ∀ g : G, ∀ a ∈ B, rep (g • a) = rep a)
    (hrepOrbit : ∀ a ∈ B, ∃ g : G, rep a = g • a) :
    ∀ u ∈ B.image rep,
      (B.filter (fun a => rep a = u)).card = Fintype.card G := by
  intro u hu
  have huB : u ∈ B := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨g, hg⟩ := hrepOrbit a ha
    rw [hg]; exact hstable g a ha
  rw [fibre_eq_orbit_of_invariant_rep B rep hstable hrepinv hrepOrbit u hu]
  exact freeSMul_card_orbit_filter u (hfree u huB)

/-- `rep` maps `B` into `B` when it sends each point into its own orbit of a `G`-stable `B`. -/
theorem rep_mem_of_orbit
    {G β : Type*} [Group G] [MulAction G β]
    (B : Finset β) (rep : β → β)
    (hstable : ∀ g : G, ∀ a ∈ B, g • a ∈ B)
    (hrepOrbit : ∀ a ∈ B, ∃ g : G, rep a = g • a) :
    ∀ a ∈ B, rep a ∈ B := by
  intro a ha
  obtain ⟨g, hg⟩ := hrepOrbit a ha
  rw [hg]; exact hstable g a ha

/-! ### Free-action MCA consumers -/

/-- **MCA prize from a free action (constant orbit-count bound).**  For a `MulAction` of a finite
group `G` that is free on the `G`-stable Finset `B`, and an orbit-compatible representative map
`rep` (invariant on `B`, sending each point into its own orbit), the fibre-size hypothesis is
*derived* (`hfib_of_free_action`).  With the open *constant* orbit-count bound `#orbits ≤ K` and
`|G| ≤ 2^m ≤ q`, the abstract term `|B|/q²` is at most `K/q`. -/
theorem mca_prize_of_free_action
    {G β : Type*} [Group G] [Fintype G] [MulAction G β] [DecidableEq β]
    (B : Finset β) (rep : β → β)
    (hstable : ∀ g : G, ∀ a ∈ B, g • a ∈ B)
    (hfree : ∀ x ∈ B, ∀ g : G, g • x = x → g = 1)
    (hrepinv : ∀ g : G, ∀ a ∈ B, rep (g • a) = rep a)
    (hrepOrbit : ∀ a ∈ B, ∃ g : G, rep a = g • a)
    {q K : ℝ} {m : ℕ}
    (hq : 0 < q) (hKnn : 0 ≤ K)
    (hN : ((B.image rep).card : ℝ) ≤ K)
    (hS : (Fintype.card G : ℝ) ≤ (2 : ℝ) ^ m)
    (hqbig : (2 : ℝ) ^ m ≤ q) :
    (B.card : ℝ) / q ^ 2 ≤ K / q :=
  mca_prize_of_orbit_partition B rep (Fintype.card G) (rep_mem_of_orbit B rep hstable hrepOrbit)
    (hfib_of_free_action B rep hstable hfree hrepinv hrepOrbit) hq hKnn hN hS hqbig

/-- **MCA prize from a free action (polynomial orbit-count bound).**  As
`mca_prize_of_free_action`, with the open *polynomial* orbit-count bound `#orbits ≤ (2^m)^d` and
`|G| ≤ 2^m`: the abstract term `|B|/q²` is at most `(1/q)·(2^m)^{d+1}`. -/
theorem mca_prize_of_free_action_poly
    {G β : Type*} [Group G] [Fintype G] [MulAction G β] [DecidableEq β]
    (B : Finset β) (rep : β → β)
    (hstable : ∀ g : G, ∀ a ∈ B, g • a ∈ B)
    (hfree : ∀ x ∈ B, ∀ g : G, g • x = x → g = 1)
    (hrepinv : ∀ g : G, ∀ a ∈ B, rep (g • a) = rep a)
    (hrepOrbit : ∀ a ∈ B, ∃ g : G, rep a = g • a)
    {q : ℝ} {m d : ℕ}
    (hq : 1 ≤ q)
    (hN : ((B.image rep).card : ℝ) ≤ ((2 : ℝ) ^ m) ^ d)
    (hS : (Fintype.card G : ℝ) ≤ (2 : ℝ) ^ m) :
    (B.card : ℝ) / q ^ 2 ≤ (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) :=
  mca_prize_of_orbit_partition_poly B rep (Fintype.card G)
    (rep_mem_of_orbit B rep hstable hrepOrbit)
    (hfib_of_free_action B rep hstable hfree hrepinv hrepOrbit) hq hN hS

/-! ### Constant-fibre consumers (the raw-`hfib` wrappers, renamed) -/

/-- **Constant-fibre MCA consumer (constant orbit-count bound).**  This is
`OrbitCountConsumerBridge.mca_prize_of_orbit_partition` with `S := Fintype.card G`: it takes the
constant-fibre hypothesis `hfib` as a raw assumption and uses nothing about `G` beyond its
cardinality (no action, no freeness).  Formerly (misleadingly) named `mca_prize_of_free_action`;
for the version that derives `hfib` from a free action see `mca_prize_of_free_action`. -/
theorem mca_prize_of_constant_fibre
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

/-- **Constant-fibre MCA consumer (polynomial orbit-count bound).**
`OrbitCountConsumerBridge.mca_prize_of_orbit_partition_poly` with `S := Fintype.card G` and the
raw `hfib` hypothesis (no action, no freeness).  Formerly named `mca_prize_of_free_action_poly`;
see `mca_prize_of_free_action_poly` for the free-action version. -/
theorem mca_prize_of_constant_fibre_poly
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
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.fibre_eq_orbit_of_invariant_rep
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.hfib_of_free_action
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.mca_prize_of_free_action
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.mca_prize_of_free_action_poly
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.mca_prize_of_constant_fibre
#print axioms ArkLib.ProximityGap.OrbitCountFreeActionMCA.mca_prize_of_constant_fibre_poly

/-! ## Non-vacuity: the regular action of a finite group on itself -/

/-- The left-regular action of a finite group on itself is free, `B = univ` is stable, and the
constant map to `1` is an orbit-compatible representative: so `hfib_of_free_action` applies and
gives the single fibre size `|G|`. -/
example {G : Type*} [Group G] [Fintype G] [DecidableEq G] :
    ∀ u ∈ (Finset.univ : Finset G).image (fun _ => (1 : G)),
      ((Finset.univ : Finset G).filter (fun _ => (1 : G) = u)).card = Fintype.card G :=
  ArkLib.ProximityGap.OrbitCountFreeActionMCA.hfib_of_free_action (G := G)
    Finset.univ (fun _ => 1)
    (fun _ _ _ => Finset.mem_univ _)
    (fun _ _ _ h => by simpa [smul_eq_mul] using h)
    (fun _ _ _ => rfl)
    (fun a _ => ⟨a⁻¹, by simp [smul_eq_mul]⟩)
