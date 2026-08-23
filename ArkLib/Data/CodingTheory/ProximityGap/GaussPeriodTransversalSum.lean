/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOrbitPartition

/-!
# Subgroup-order divisibility via the `μ_n`-orbit partition of `F^×` (#389, #407)

`GaussPeriodOrbitPartition` lands the *per-orbit* block sum (`sum_eta_pow_over_orbit`:
`∑_{c ∈ G·b₀} f c = n • f b₀` for orbit-constant `f`). This file composes the blocks across the
whole unit group `F^×`, via the orbit map `g : b ↦ G.image (· * b)` (the orbit-as-`Finset`, a
choice-free invariant of the orbit), to land the **`n ∣ (q − 1)`** Lagrange count:

* **`1 ∈ G`** (`one_mem_of_bij`): a nonempty closed-as-bijection `Finset` contains the identity.
* **Orbit-`Finset` is orbit-constant** (`orbit_finset_eq_of_mem`): `G·(u·b) = G·b` for `u ∈ G`, so
  the orbit map `g` is constant on each orbit — its fibers (restricted to `F^×`) are exactly the
  orbits.
* **`n ∣ (q − 1)`** (`card_dvd_card_units`): `F^×` is the disjoint union of the size-`n` orbit
  fibers of `g`, so `q − 1 = (#orbits)·n` (via `Finset.card_eq_sum_card_fiberwise`) — the subgroup
  order divides `q − 1`. Proven *within* this `Finset`/closure-as-bijection framework, no
  `Subgroup Fˣ` coercion needed. This is the integrality of `m = (q−1)/n` that the coset reduction
  (`cosetReduced_eta_pow_le`'s `/n`) and the second-moment census (`/m`) implicitly assume.

NON-MOMENT (free-action / orbit-partition combinatorics); extends `eta_mul_left`. Axiom-clean.
Issues #389, #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction
open ArkLib.ProximityGap.GaussPeriodOrbitPartition

namespace ArkLib.ProximityGap.GaussPeriodTransversalSum

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A nonempty closed-as-bijection `Finset` of a field contains `1`.** For `x ∈ G` with
`x·G = G`, surjectivity gives `x = x·y` for some `y ∈ G`, so `y = 1` by left-cancellation
(`x ≠ 0` since `0 ∉ G`). -/
theorem one_mem_of_bij {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty) :
    (1 : F) ∈ G := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  have hxG : G.image (fun y => x * y) = G := hbij x hx
  have : x ∈ G.image (fun y => x * y) := by rw [hxG]; exact hx
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp this
  have : x * y = x * 1 := by rw [hxy, mul_one]
  have hy1 : y = 1 := mul_left_cancel₀ hx0 this
  exact hy1 ▸ hy

/-- **The orbit map sends `F^×` into the set of orbit-`Finset`s, and is `G`-invariant.** For `b ≠ 0`
and `u ∈ G`, `G·(u·b) = G·b` (closure-as-bijection): the orbit-as-`Finset` is constant along the
orbit. -/
theorem orbit_finset_eq_of_mem {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G)
    {u : F} (hu : u ∈ G) (b : F) :
    G.image (fun w => w * (u * b)) = G.image (fun w => w * b) := by
  classical
  ext c
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w * u, by rw [← hbij u hu]; exact Finset.mem_image.mpr ⟨w, hw, mul_comm u w⟩,
      by ring⟩
  · rintro ⟨w, hw, rfl⟩
    -- w * b = (w * u⁻¹) * (u * b); need w * u⁻¹ ∈ G. Since uG = G, w = u * w' for some w' ∈ G.
    have huG : G.image (fun y => u * y) = G := hbij u hu
    have : w ∈ G.image (fun y => u * y) := by rw [huG]; exact hw
    obtain ⟨w', hw', hww'⟩ := Finset.mem_image.mp this
    exact ⟨w', hw', by rw [← hww']; ring⟩

/-- **Subgroup order divides `q − 1`.** `F^× = univ.erase 0` is the disjoint union of the
`μ_n`-orbits `G·b` (`b ≠ 0`), each of card exactly `|G|` (`orbit_card_eq`), so `|G| ∣ (q − 1)`.
Proven by `Finset.card_eq_sum_card_fiberwise` over the orbit map `b ↦ G·b`: every fiber has card a
multiple of `|G|`... here we route through the cleaner `Finset.dvd_card` style via the orbit being a
uniform block. Concretely: pick the orbit map `g b = G.image (·*b)`; each nonempty fiber is a single
orbit of card `|G|`, so `(q−1) = (#orbits)·|G|`. -/
theorem card_dvd_card_units {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty) :
    G.card ∣ (Fintype.card F - 1) := by
  classical
  -- The orbit map on F^×.
  set S : Finset F := Finset.univ.erase (0 : F) with hS
  set g : F → Finset F := fun b => G.image (fun w => w * b) with hg
  -- Reduce the target `|G| ∣ q - 1` to `|G| ∣ |S|`.
  have hScard : S.card = Fintype.card F - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [← hScard]
  -- Each fiber of g over a value in its image, restricted to S, is exactly an orbit of card |G|.
  -- Use card_eq_sum_card_fiberwise: |S| = ∑_{t ∈ image} |fiber t|, and show each |fiber t| = |G|.
  have hmaps : ∀ b ∈ S, g b ∈ S.image g := fun b hb => Finset.mem_image_of_mem g hb
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  -- Show every fiber has card = |G|, then the sum is (#image)·|G|, divisible by |G|.
  have hfiber : ∀ t ∈ S.image g, (S.filter (fun b => g b = t)).card = G.card := by
    intro t ht
    obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp ht
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hbS
    -- The fiber {b' ∈ S : G·b' = G·b} equals the orbit G·b.
    have hfib_eq : S.filter (fun b' => g b' = g b) = G.image (fun w => w * b) := by
      ext c
      simp only [Finset.mem_filter, hg, hS, Finset.mem_image]
      constructor
      · rintro ⟨hcS, hc⟩
        -- `g c = g b`; since `1 ∈ G`, `c = 1·c ∈ G·c = g c = g b`, so `c ∈ G·b`.
        have h1 : (1 : F) ∈ G := one_mem_of_bij hbij h0 hne
        have hc_mem : c ∈ G.image (fun w => w * c) :=
          Finset.mem_image.mpr ⟨1, h1, one_mul c⟩
        rw [hc] at hc_mem
        exact Finset.mem_image.mp hc_mem
      · rintro ⟨w, hw, rfl⟩
        refine ⟨Finset.mem_erase.mpr ⟨mul_ne_zero (fun h => h0 (h ▸ hw)) hb0, Finset.mem_univ _⟩, ?_⟩
        exact orbit_finset_eq_of_mem hbij hw b
    rw [hfib_eq, orbit_card_eq G hb0]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const]
  exact Dvd.intro_left _ rfl

end ArkLib.ProximityGap.GaussPeriodTransversalSum

#print axioms ArkLib.ProximityGap.GaussPeriodTransversalSum.one_mem_of_bij
#print axioms ArkLib.ProximityGap.GaussPeriodTransversalSum.orbit_finset_eq_of_mem
#print axioms ArkLib.ProximityGap.GaussPeriodTransversalSum.card_dvd_card_units
