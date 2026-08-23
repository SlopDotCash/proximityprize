/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetExactCount

/-!
# Fiber-count reduction of the bad-spectrum cardinality to the coset-level count (#389, partial — NOT a closure)

The seed-census chain (`SmoothSupplyTowerBridge.lean` → `SeedCensusBound.lean`) reduced the
deployed smooth-domain `ExplainableCoreSupply` to bounding the bad-spectrum cardinality
`S.card` (the deep-band bad-scalar count), via
`census_iff_spectrum_bound_of_free : seeds.card ≤ B ↔ S.card ≤ B · h`. So the whole supply
reduces to `S.card = O(n log n)`.

This file performs the **next clean reduction step**: it groups the bad spectrum `S ⊆ μ_n`
by the `h`-th power map `x ↦ x^h` (whose fibers are exactly the `μ_h`-cosets, each of size
exactly `h` by `CosetExactCount.fiber_card_eq`) and concludes the pure pigeonhole fact

  **`S.card ≤ (#distinct coset-levels meeting S) · h`,**  where  `#levels = (S.image (·^h)).card`.

This converts `S.card = O(n log n)` to the cleaner **tower-depth residual**
`#coset-levels = O(log n)`. The fiber-values `c = x^h` all lie in `μ_{n/h}`, the order-`n/h`
subgroup whose tower descent (`CensusTowerFinite.tower_closed_finite`,
`CensusTowerDescent.tower_closed_of_dyadic_sums_zero`) structures the spectrum into dyadic
levels — so `#coset-levels` is exactly the count of dyadic tower levels the spectrum meets.

## What is proved here (axiom-clean)

* `spectrum_card_le_levels_mul_h` — **THE REDUCTION.** For any finite `S ⊆ μ_n` (with `h ∣ n`,
  `ζ` a primitive `n`-th root), each `(·^h)`-fiber of `S` is contained in a full `μ_h`-coset of
  size `h` (`fiber_card_eq`), so `S.card ≤ (S.image (·^h)).card · h`. Pure pigeonhole.
* `spectrum_levels_subset_subgroup` — the fiber-values are graded: `S.image (·^h) ⊆ μ_{n/h}`,
  i.e. every coset-level `c = x^h` is an `(n/h)`-th root of unity. This is the bridge that
  identifies `#coset-levels` with the count of tower levels (the residual the dyadic descent
  bounds).

## Honesty

This is a **reduction**, not a closure: it replaces `S.card ≤ O(n log n)` with the cleaner
named residual `#coset-levels = (S.image (·^h)).card ≤ O(log n)` (the tower-depth count).
No `O(log n)` bound is asserted here; pinning `#coset-levels` is the dyadic tower-descent
problem, which reduces toward the recognized open core (#357/#389). The named-residual
convention applies.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset

namespace ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-- **THE REDUCTION (fiber-count / pigeonhole).** Let `ζ` be a primitive `n`-th root of unity
in `F`, `0 < h`, `h ∣ n`, and let `S ⊆ μ_n` be any finite set of `n`-th roots of unity
(the bad spectrum). Grouping `S` by the `h`-th power map `x ↦ x^h`, each fiber
`{x ∈ S | x^h = c}` is a subset of the full `μ_h`-coset `fiber n h c`, which has exactly `h`
elements (`fiber_card_eq`); hence each fiber has size `≤ h`. By pigeonhole
(`Finset.card_le_mul_card_image`):

  `S.card ≤ (S.image (·^h)).card · h`.

The right factor `(S.image (·^h)).card` is the number of distinct coset-levels `c = x^h` the
spectrum meets. This reduces the `S.card = O(n log n)` bound to the cleaner tower-depth
residual `#coset-levels ≤ O(log n)`. -/
theorem spectrum_card_le_levels_mul_h {ζ : F} {n h : ℕ} (hn : 0 < n) (hh : 0 < h) (hdvd : h ∣ n)
    (hζ : IsPrimitiveRoot ζ n) (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F)) :
    S.card ≤ (S.image (fun x => x ^ h)).card * h := by
  -- per-fiber bound: each `(·^h)`-fiber of `S` has at most `h` elements.
  have hfib : ∀ c ∈ S.image (fun x => x ^ h),
      (S.filter (fun x => x ^ h = c)).card ≤ h := by
    intro c hc
    obtain ⟨g, hgS, hgc⟩ := Finset.mem_image.mp hc
    have hgn : g ^ n = 1 := (mem_nthRootsFinset hn (1 : F)).1 (hS hgS)
    -- the `S`-fiber is contained in the full coset `fiber n h c`
    have hsub : S.filter (fun x => x ^ h = c) ⊆ fiber n h c := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [mem_fiber hn]
      exact ⟨(mem_nthRootsFinset hn (1 : F)).1 (hS hx.1), hx.2⟩
    calc (S.filter (fun x => x ^ h = c)).card
        ≤ (fiber n h c).card := Finset.card_le_card hsub
      _ = h := fiber_card_eq hn hdvd hζ hgn hgc
  -- pigeonhole: `S.card ≤ h * #image`, reorder to `#image * h`.
  have hpig := Finset.card_le_mul_card_image S h hfib
  rw [mul_comm] at hpig
  exact hpig

/-- **Coset-levels are graded into the order-`n/h` subgroup.** Every fiber-value `c = x^h`
(`x ∈ S ⊆ μ_n`) is an `(n/h)`-th root of unity: `c ∈ μ_{n/h}`. Hence `#coset-levels` counts a
subset of `μ_{n/h}` — the subgroup whose 2-adic tower descent
(`CensusTowerFinite.tower_closed_finite`) structures the spectrum into dyadic levels. This is
the bridge identifying the pigeonhole right factor with the tower-level count. -/
theorem spectrum_levels_subset_subgroup {n h : ℕ} (hn : 0 < n) (hdvd : h ∣ n)
    (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F)) :
    S.image (fun x => x ^ h) ⊆ nthRootsFinset (n / h) (1 : F) := by
  have hh : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega)
  have hnh : 0 < n / h := Nat.div_pos (Nat.le_of_dvd hn hdvd) hh
  intro c hc
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hc
  have hxn : x ^ n = 1 := (mem_nthRootsFinset hn (1 : F)).1 (hS hxS)
  rw [mem_nthRootsFinset hnh]
  rw [← pow_mul, Nat.mul_div_cancel' hdvd, hxn]

end ArkLib.ProximityGap.Rigidity

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — NO sorryAx)
#print axioms ArkLib.ProximityGap.Rigidity.spectrum_card_le_levels_mul_h
#print axioms ArkLib.ProximityGap.Rigidity.spectrum_levels_subset_subgroup
