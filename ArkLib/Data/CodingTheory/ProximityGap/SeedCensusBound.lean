/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothSupplyTowerBridge

/-!
# Bounding the seed-count of the smooth-domain census (#389, partial — NOT a closure)

`SmoothSupplyTowerBridge.lean` reduced the deployed smooth-domain `ExplainableCoreSupply`
to the named residual `SeedCensus g h S seeds` (= `seeds` is a `⟨g⟩`-orbit transversal of the
bad spectrum `S`), with `smooth_supply_of_seedCensus` giving `#spectrum ≤ seeds.card · h`.

The OPEN quantitative piece is bounding `seeds.card` — the number of distinct `⟨g⟩`-orbits the
bad spectrum meets — by `O(log n)`. **This file does NOT prove that bound.** It supplies the
**structural reduction** of the census count to a *cleaner* named quantity: the bad-spectrum
cardinality `S.card`. The point is that for the 2-power smooth domain the action of the
order-`h` generator `g` on `S` is **free** (multiplication by a root of unity is a permutation
of the punctured group, with full orbits of size `h`), so the orbit count is *exactly*
`S.card / h`. Hence:

  **`SeedCensus` with `seeds.card = O(log n)` ⟺ `S.card = O(h · log n) = O(n log n)`.**

This converts the orbit-count census into a *spectrum-cardinality* census, which is the
quantity the in-tree `KKH26`/coset machinery actually estimates.

## What is proved here (axiom-clean)

* `gAct_pow` / `gAct_mul` — basic group-action laws of `gAct`.
* `seedCensus_image_section` — **the explicit transversal.** Given an orbit-invariant section
  `rep : F → F` landing in the orbit and in `S`, the set `seeds := S.image rep` is a genuine
  `SeedCensus` transversal. (Existence of the abstract census from a section.)
* `seeds_card_le_of_section` — the cheap direction: `seeds.card ≤ S.card`.
* `orbit_card_le` — every `⟨g⟩`-orbit fiber inside `S` has size `≤ h` (since `g ^ h = 1`).
* `seeds_card_mul_h_ge` — from the fiber decomposition, `S.card ≤ seeds.card · h`
  (automatic; this is the direction `smooth_supply` already exploits).
* `seedCensus_seeds_card_le_of_free` — **THE REDUCTION.** If the orbit fibers all have size
  exactly `h` (the free-action hypothesis — true for root-of-unity multiplication on the
  punctured group), then `seeds.card · h = S.card`, hence `seeds.card = S.card / h` and the
  census `seeds.card ≤ B` is *equivalent to* the spectrum bound `S.card ≤ B · h`.

## Honesty

This is a **reduction**, not a closure: it replaces the orbit-count residual with the
spectrum-cardinality residual `S.card ≤ O(n log n)`, which remains the open input (the
KKH26-style line/coset incidence count). No `O(log n)` bound is asserted. The free-action
hypothesis is supplied as an explicit argument, matching the named-residual convention.
-/

open Finset

namespace ProximityGap.SmoothSupply

variable {F : Type} [Field F] [DecidableEq F]

/-- `gAct g i` iterated: `gAct g i x = g ^ i * x`. Powers compose additively. -/
theorem gAct_pow (g : F) (i : ℕ) (x : F) : gAct g i x = g ^ i * x := rfl

/-- The action law: `gAct g (i + j) x = gAct g i (gAct g j x)`. -/
theorem gAct_mul (g : F) (i j : ℕ) (x : F) :
    gAct g (i + j) x = gAct g i (gAct g j x) := by
  simp only [gAct, pow_add]; ring

/-- **The explicit transversal from an orbit section.** Suppose `rep : F → F` is a section that,
on `S`, lands back in the same `⟨g⟩`-orbit (`rep x = g ^ i · x` for some `i < h`) and lands in
`S`'s chosen seed set image. Then `seeds := S.image rep` is a genuine `SeedCensus` transversal:
every `x ∈ S` is `g ^ k · seed` for some `seed ∈ seeds`, `k < h`.

The hypothesis `hrep` packages exactly "`rep x` is in the orbit of `x`": there is `i < h` with
`gAct g i (rep x) = x`, i.e. `x` is reachable from its representative. -/
theorem seedCensus_image_section (g : F) (h : ℕ) (S : Finset F) (rep : F → F)
    (hrep : ∀ x ∈ S, ∃ i : Fin h, gAct g (i : ℕ) (rep x) = x) :
    SeedCensus g h S (S.image rep) := by
  intro x hx
  obtain ⟨i, hi⟩ := hrep x hx
  exact ⟨rep x, Finset.mem_image_of_mem _ hx, i, hi.symm⟩

/-- The cheap direction: the seed transversal `S.image rep` has size at most `S.card`. -/
theorem seeds_card_le_of_section (S : Finset F) (rep : F → F) :
    (S.image rep).card ≤ S.card :=
  Finset.card_image_le

/-- **Orbit fibers are small.** Group the bad spectrum `S` by the section value `rep`. If `rep`
is constant on orbits (`rep` invariant under `x ↦ g · x` within `S`), each fiber is a subset of
the `⟨g⟩`-orbit of its representative, which — since `g ^ h = 1` — has at most `h` elements. We
record the clean consequence used below: any subset `O ⊆ S` on which `g` acts with `g ^ h = 1`
and which is the orbit `{g ^ k · s : k < h}` has `O.card ≤ h`. -/
theorem orbit_card_le (g : F) (h : ℕ) (s : F) :
    ((Finset.range h).image (fun k => gAct g k s)).card ≤ h := by
  calc ((Finset.range h).image (fun k => gAct g k s)).card
      ≤ (Finset.range h).card := Finset.card_image_le
    _ = h := Finset.card_range h

/-- **The fiber-sum decomposition (automatic direction).** Writing `S` as the disjoint union of
its `rep`-fibers, `S.card = Σ_{s ∈ seeds} (fiber s).card`. If every fiber has cardinality at
most `h` then `S.card ≤ seeds.card · h`. This is the direction the consumer
`smooth_supply_of_seedCensus` already uses; we restate it at the cardinality level. -/
theorem seeds_card_mul_h_ge (h : ℕ) (S : Finset F) (rep : F → F)
    (hfib : ∀ s ∈ S.image rep,
      (S.filter (fun x => rep x = s)).card ≤ h) :
    S.card ≤ (S.image rep).card * h := by
  classical
  have hmaps : ∀ x ∈ S, rep x ∈ S.image rep :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ s ∈ S.image rep, (S.filter (fun x => rep x = s)).card
      ≤ ∑ _s ∈ S.image rep, h := Finset.sum_le_sum hfib
    _ = (S.image rep).card * h := by rw [Finset.sum_const, smul_eq_mul]

/-- **THE REDUCTION.** Suppose the `rep`-fibers of the bad spectrum all have cardinality
*exactly* `h` (the free-action hypothesis: each `⟨g⟩`-orbit meeting `S` has `h` distinct
elements — true for multiplication by a primitive `h`-th root of unity on the punctured group).
Then the seed count is pinned: `seeds.card · h = S.card`, i.e. `seeds.card = S.card / h`.

Consequently the census `seeds.card ≤ B` holds **iff** the spectrum bound `S.card ≤ B · h`
holds: the open orbit-count residual is *equivalent* to the spectrum-cardinality residual.
This is the structural reduction toward the `O(log n)` census — it does not supply the
`O(log n)` bound itself, only converts it to the cleaner `S.card = O(n log n)` form. -/
theorem seedCensus_seeds_card_le_of_free (h : ℕ) (S : Finset F) (rep : F → F)
    (hfib : ∀ s ∈ S.image rep,
      (S.filter (fun x => rep x = s)).card = h) :
    (S.image rep).card * h = S.card := by
  classical
  have hmaps : ∀ x ∈ S, rep x ∈ S.image rep :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

/-- **Census ⟺ spectrum bound (free action).** With the free-fiber hypothesis, the census
`seeds.card ≤ B` is equivalent to `S.card ≤ B · h`. (`h > 0` rules out the degenerate
empty-orbit case.) -/
theorem census_iff_spectrum_bound_of_free (h B : ℕ) (hh : 0 < h)
    (S : Finset F) (rep : F → F)
    (hfib : ∀ s ∈ S.image rep,
      (S.filter (fun x => rep x = s)).card = h) :
    (S.image rep).card ≤ B ↔ S.card ≤ B * h := by
  have hpin := seedCensus_seeds_card_le_of_free h S rep hfib
  constructor
  · intro hle
    calc S.card = (S.image rep).card * h := hpin.symm
      _ ≤ B * h := Nat.mul_le_mul_right h hle
  · intro hle
    have : (S.image rep).card * h ≤ B * h := by rw [hpin]; exact hle
    exact Nat.le_of_mul_le_mul_right this hh

/-! ## A concrete free-orbit instance (axiom-clean witness)

We exhibit a concrete small smooth case where the census holds with a *single* seed
(`seeds.card = 1`): the full order-`h` orbit of one root, where `g` is a primitive `h`-th root
of unity. This is the `S = ⟨g⟩` single-orbit case: the orbit count is exactly `1` and the
spectrum size is exactly `h`. It is the base witness that the free-action reduction is
non-vacuous and that `seeds.card` can genuinely be a constant (here, `1`) on a smooth orbit. -/

/-- **Single-orbit instance.** If `g` is a primitive `h`-th root of unity (`h > 0`) and
`S` is the full orbit `{g ^ k : k < h}`, then `S` is `g`-closed and the census holds with the
single seed `seeds = {1}` — `seeds.card = 1`, the smallest possible. The spectrum count then
reads `#spectrum ≤ 1 · h = h`. -/
theorem single_orbit_seedCensus (g : F) (h : ℕ) (hh : 0 < h)
    (hg : IsPrimitiveRoot g h) :
    SeedCensus g h ((Finset.range h).image (fun k => g ^ k)) {1} := by
  intro x hx
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨1, Finset.mem_singleton_self 1, ⟨k % h, Nat.mod_lt k hh⟩, by
    simp only [gAct, mul_one]
    rw [← pow_mod_orderOf]
    congr 1
    exact (hg.eq_orderOf) ▸ rfl⟩

/-- The single-orbit instance has seed count `1` (a *constant*, the target asymptotic shape). -/
theorem single_orbit_seeds_card : ({1} : Finset F).card = 1 := Finset.card_singleton 1

end ProximityGap.SmoothSupply

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — NO sorryAx)
#print axioms ProximityGap.SmoothSupply.gAct_pow
#print axioms ProximityGap.SmoothSupply.gAct_mul
#print axioms ProximityGap.SmoothSupply.seedCensus_image_section
#print axioms ProximityGap.SmoothSupply.seeds_card_le_of_section
#print axioms ProximityGap.SmoothSupply.orbit_card_le
#print axioms ProximityGap.SmoothSupply.seeds_card_mul_h_ge
#print axioms ProximityGap.SmoothSupply.seedCensus_seeds_card_le_of_free
#print axioms ProximityGap.SmoothSupply.census_iff_spectrum_bound_of_free
#print axioms ProximityGap.SmoothSupply.single_orbit_seedCensus
#print axioms ProximityGap.SmoothSupply.single_orbit_seeds_card
