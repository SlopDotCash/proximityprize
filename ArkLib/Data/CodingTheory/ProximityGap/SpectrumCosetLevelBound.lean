/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetExactCount

/-!
# Fiber-count bound for subsets of `μ_n` by their coset values (#389, NOT a closure)

The seed-census chain (`SmoothSupplyTowerBridge.lean` → `SeedCensusBound.lean`) relates the
deployed smooth-domain `ExplainableCoreSupply` to the bad-spectrum cardinality `S.card` (the
deep-band bad-scalar count), via
`census_iff_spectrum_bound_of_free : seeds.card ≤ B ↔ S.card ≤ B · h`, and states the supply
target as `S.card = O(n log n)`. As explained in the correction below, under this file's
hypothesis `S ⊆ μ_n` that target is trivially true.

This file groups a set `S ⊆ μ_n` by the `h`-th power map `x ↦ x^h` (whose fibers are exactly
the `μ_h`-cosets, each of size exactly `h` by `CosetExactCount.fiber_card_eq`) and proves the
pure pigeonhole fact

  **`S.card ≤ (#distinct coset values meeting S) · h`,**  where  `#values = (S.image (·^h)).card`.

## Correction (audit 2026-10-28, PG-104): under `S ⊆ μ_n` the stated target is already trivial

An earlier version of this header said that this pigeonhole step converts `S.card = O(n log n)`
into a "tower-depth residual" `#coset-levels = O(log n)`, and that `#coset-levels` is the number of
dyadic tower levels the spectrum meets. Both statements are wrong:

* **The `O(n log n)` target needs no descent estimate under this file's hypothesis.** With
  `S ⊆ μ_n` and `ζ` a primitive `n`-th root, `S.card ≤ n` directly
  (`spectrum_card_le_n` below). So a residual of the form `S.card ≤ C · n log n` with `S ⊆ μ_n`
  carries no open content; if the intended bad spectrum is a genuinely open quantity, it must live
  in a larger ambient set (e.g. scalars of the full field `F`, not of `μ_n`), and its budget must be
  restated against that ambient set before this reduction can be used.
* **`O(log n)` is far stronger than what the target needs.** Through
  `S.card ≤ #values · h`, the bound `S.card ≤ C · n log n` follows from
  `#values ≤ C · (n/h) · log n`, which is already implied by the trivial bound
  `#values ≤ n/h` (`spectrum_levels_card_le` below). Asking for `#values = O(log n)` discards the
  `n/h` factor and is a much stronger, unmotivated statement.
* **Coset values are not dyadic tower depths.** `S.image (·^h) ⊆ μ_{n/h}` counts field values
  (equivalently `μ_h`-cosets met by `S`), not subgroup-depth indices: at `h = 1`, `S = μ_n` the
  image has `n` values while `μ_n` (for `n = 2^a`) has only `log₂ n + 1` dyadic subgroup depths.

The proved inequalities below are correct; only the earlier interpretation was wrong. No
`O(log n)` bound on `#values` is asserted, and none is needed for the `O(n log n)` target.

## What is proved here (axiom-clean)

* `spectrum_card_le_levels_mul_h` — for any finite `S ⊆ μ_n` (with `h ∣ n`, `ζ` a primitive `n`-th
  root), each `(·^h)`-fiber of `S` is contained in a full `μ_h`-coset of size `h`
  (`fiber_card_eq`), so `S.card ≤ (S.image (·^h)).card · h`. Pure pigeonhole.
* `spectrum_levels_subset_subgroup` — every coset value `c = x^h` is an `(n/h)`-th root of unity:
  `S.image (·^h) ⊆ μ_{n/h}`.
* `spectrum_card_le_n`, `spectrum_levels_card_le` — the trivial bounds `S.card ≤ n` and
  `#values ≤ n/h`, recorded to make the degeneracy above explicit.
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

The right factor `(S.image (·^h)).card` is the number of distinct coset values `c = x^h` the set
meets (a count of field values in `μ_{n/h}`, not of dyadic tower depths). Under `S ⊆ μ_n` the
bound `S.card ≤ n` already holds trivially (`spectrum_card_le_n`), so this inequality does not
reduce any open `O(n log n)` target; see the module docstring (PG-104). -/
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

/-- **Coset values lie in the order-`n/h` subgroup.** Every fiber-value `c = x^h`
(`x ∈ S ⊆ μ_n`) is an `(n/h)`-th root of unity: `c ∈ μ_{n/h}`. Hence the pigeonhole right factor
counts a subset of `μ_{n/h}` (field values / `μ_h`-cosets met by `S`). It is **not** a count of
dyadic tower depths: at `h = 1`, `S = μ_n` it equals `n`, whereas `μ_{2^a}` has only `a + 1`
subgroup depths (PG-104). -/
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

/-- **The trivial cardinality bound (PG-104).** Under this file's domain hypothesis `S ⊆ μ_n`
(with `ζ` a primitive `n`-th root), `S.card ≤ n`. In particular any target of the form
`S.card ≤ C · n log n` (`C ≥ 1`, `n ≥ 3`) needs no descent estimate. -/
theorem spectrum_card_le_n {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (S : Finset F)
    (hS : S ⊆ nthRootsFinset n (1 : F)) :
    S.card ≤ n :=
  (Finset.card_le_card hS).trans hζ.card_nthRootsFinset.le

/-- **The trivial coset-value bound (PG-104).** The number of distinct coset values met by
`S ⊆ μ_n` is at most `n/h`. Through `spectrum_card_le_levels_mul_h` this alone already gives
`S.card ≤ n`, so a residual `#values = O(log n)` is far stronger than any `O(n log n)` target
requires. -/
theorem spectrum_levels_card_le {ζ : F} {n h : ℕ} (hn : 0 < n) (hdvd : h ∣ n)
    (hζ : IsPrimitiveRoot ζ n) (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F)) :
    (S.image (fun x => x ^ h)).card ≤ n / h := by
  have hζ' : IsPrimitiveRoot (ζ ^ h) (n / h) := hζ.pow hn (Nat.mul_div_cancel' hdvd).symm
  exact (Finset.card_le_card (spectrum_levels_subset_subgroup hn hdvd S hS)).trans
    hζ'.card_nthRootsFinset.le

end ArkLib.ProximityGap.Rigidity

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — NO sorryAx)
#print axioms ArkLib.ProximityGap.Rigidity.spectrum_card_le_levels_mul_h
#print axioms ArkLib.ProximityGap.Rigidity.spectrum_levels_subset_subgroup
#print axioms ArkLib.ProximityGap.Rigidity.spectrum_card_le_n
#print axioms ArkLib.ProximityGap.Rigidity.spectrum_levels_card_le
