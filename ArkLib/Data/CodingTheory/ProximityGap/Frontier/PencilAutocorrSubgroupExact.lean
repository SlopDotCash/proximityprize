/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrelation

/-!
# The EXACT subgroup autocorrelation: `|H ∩ ρ·H| = |H|·[ρ∈H]` (#444)

`PencilAutocorrelation.autocorr_ge_coset_core` proves the LOWER bound `|S ∩ ρ·S| ≥ |H|` when the
root set `S` *contains* a subgroup `H` and `ρ ∈ H`. For the actual prize object the root set
**IS** the thin subgroup `S = H = μ_n` — and there the multiplicative autocorrelation is not merely
bounded below, it has an **EXACT closed form**:

> **`(H ∩ dilate ρ H).card = if ρ ∈ H then H.card else 0`.**

The dilation pencil overlap of a multiplicative subgroup is *all-or-nothing*: full (`= |H|`) at
every shift inside the subgroup, and empty everywhere else. This is the maximally-degenerate
autocorrelation profile, and it pins the pencil/Fisher (`LEVER K`) route's Johnson collapse
**exactly** for the true object (not just from below):

* every nontrivial `ρ ∈ H` realizes the maximal autocorrelation `|H|` itself (not `n/2` — the WHOLE
  subgroup is the overlap), so the Kelley–Owen autocorrelation maximum is `M(H) = |H|`;
* the global double-count `∑_{ρ∈G} |H ∩ ρH| = |H|²` (`PencilAutocorrSumDoubleCount.autocorr_sum_eq_sq`)
  is carried ENTIRELY by the `|H|` shifts inside `H` (each contributing `|H|`), with zero mass
  outside — so the unsigned overlap count has no spreading to exploit. The √(log) cancellation must
  live in the SIGNED phase, never the unsigned subgroup autocorrelation.

## Mechanism (NON-MOMENT, sign-free additive combinatorics, EXTEND-proven)

`H` is closed under `*` and `⁻¹` and contains `1`. For `ρ ∈ H`: `dilate ρ H = H` (both inclusions
by closure — `subgroup_subset_dilate_self` gives `⊆`, and `ρ⁻¹ ∈ H` gives `⊇`), so
`H ∩ dilate ρ H = H`. For `ρ ∉ H`: the intersection is EMPTY — if `x ∈ H` and `x ∈ dilate ρ H` then
`ρ⁻¹ x ∈ H`, whence `ρ = x · (ρ⁻¹ x)⁻¹ ∈ H`, contradiction.

PROBE `scripts/probes/probe_subgroup_autocorr_exact.py`: `|μ_n ∩ ρ·μ_n| = n·[ρ∈μ_n]` EXACT in
66848/66848 configs (proper thin `μ_n`, `n = 2^a`, `p ≡ 1 mod n` incl. `p > n³` + Fermat 257,
NEVER `n = q−1`, over ALL `ρ ∈ F_p^*`).

**Honest scope.** NOT a CORE closure, NOT a refutation. It SHARPENS the in-tree lower bound
`autocorr_ge_coset_core` to the exact value for the case `S = H` (the actual prize object), pinning
the pencil-route Johnson collapse exactly: the unsigned autocorrelation is all-or-nothing, so the
LEVER-K / Fisher double-count cannot beat Johnson. NON-MOMENT, field- and thickness-universal,
EXTEND-proven (consumes `subgroup_subset_dilate_self` + `dilate`/`mem_dilate`). No
capacity/beyond-Johnson/cliff-at-n/2 claim. `CORE M(μ_n) ≤ C·√(n·log(q/n))` OPEN.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.PencilAutocorrelation

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- For a subgroup `H` and `ρ ∈ H`, the dilate is `H` itself: `dilate ρ H = H`. Both inclusions are
multiplicative closure (`subgroup_subset_dilate_self` gives `H ⊆ dilate ρ H`; the reverse uses
`ρ⁻¹ ∈ H`). -/
theorem dilate_eq_self_of_mem {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {ρ : G} (hρ : ρ ∈ H) :
    dilate ρ H = H := by
  apply Finset.Subset.antisymm
  · -- dilate ρ H ⊆ H : y = ρ * x with x ∈ H, and ρ ∈ H ⟹ ρ * x ∈ H
    intro y hy
    rw [mem_dilate] at hy
    -- hy : ρ⁻¹ * y ∈ H. Then y = ρ * (ρ⁻¹ * y) ∈ H by closure.
    have : y = ρ * (ρ⁻¹ * y) := by group
    rw [this]
    exact hmul ρ hρ _ hy
  · exact subgroup_subset_dilate_self hmul hinv hρ

/-- For a subgroup `H` and `ρ ∉ H`, the dilate is DISJOINT from `H`: `H ∩ dilate ρ H = ∅`. If
`x ∈ H ∩ dilate ρ H` then `ρ⁻¹ x ∈ H`, so `ρ = x · (ρ⁻¹ x)⁻¹ ∈ H` — contradiction. -/
theorem inter_dilate_eq_empty_of_not_mem {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {ρ : G} (hρ : ρ ∉ H) :
    H ∩ dilate ρ H = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  rw [Finset.mem_inter, mem_dilate] at hx
  obtain ⟨hxH, hρx⟩ := hx
  -- hxH : x ∈ H,  hρx : ρ⁻¹ * x ∈ H.  Then ρ = x * (ρ⁻¹ * x)⁻¹ ∈ H.
  apply hρ
  have hk : (ρ⁻¹ * x)⁻¹ ∈ H := hinv _ hρx
  have : ρ = x * (ρ⁻¹ * x)⁻¹ := by group
  rw [this]
  exact hmul x hxH _ hk

/-- **THE EXACT SUBGROUP AUTOCORRELATION (headline).** For a multiplicative subgroup `H` (closed
under `*`, `⁻¹`, containing `1`), the dilation autocorrelation is all-or-nothing:

  `(H ∩ dilate ρ H).card = if ρ ∈ H then H.card else 0`.

Full (`= |H|`) at every shift inside the subgroup, empty everywhere else. -/
theorem subgroup_autocorr_exact {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (ρ : G) :
    (H ∩ dilate ρ H).card = if ρ ∈ H then H.card else 0 := by
  by_cases hρ : ρ ∈ H
  · rw [if_pos hρ, dilate_eq_self_of_mem hmul hinv hρ, Finset.inter_self]
  · rw [if_neg hρ, inter_dilate_eq_empty_of_not_mem hmul hinv hρ, Finset.card_empty]

/-- For `ρ ∈ H`, the subgroup autocorrelation is FULL: `(H ∩ dilate ρ H).card = H.card`. -/
theorem subgroup_autocorr_full {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {ρ : G} (hρ : ρ ∈ H) :
    (H ∩ dilate ρ H).card = H.card := by
  rw [subgroup_autocorr_exact hmul hinv ρ, if_pos hρ]

/-- For `ρ ∉ H`, the subgroup autocorrelation VANISHES: `(H ∩ dilate ρ H).card = 0`. -/
theorem subgroup_autocorr_zero {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {ρ : G} (hρ : ρ ∉ H) :
    (H ∩ dilate ρ H).card = 0 := by
  rw [subgroup_autocorr_exact hmul hinv ρ, if_neg hρ]

/-- **The Kelley–Owen autocorrelation MAXIMUM is EXACTLY `|H|`** (not `n/2`): the whole subgroup
is the overlap at every nontrivial inside shift. Existence half — there is a nontrivial `ρ ≠ 1` in
`H` with autocorrelation exactly `|H|`, given `|H| ≥ 2`. -/
theorem exists_nontrivial_shift_autocorr_eq_card {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hcard : 2 ≤ H.card) :
    ∃ ρ : G, ρ ≠ 1 ∧ (H ∩ dilate ρ H).card = H.card := by
  -- `H` has `≥ 2` elements, so it contains some `ρ ≠ 1`.
  obtain ⟨ρ, hρH, hρne⟩ : ∃ ρ ∈ H, ρ ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : H ⊆ {1} := by
      intro x hx; rw [Finset.mem_singleton]; exact h x hx
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this; omega
  exact ⟨ρ, hρne, subgroup_autocorr_full hmul hinv hρH⟩

/-- **Upper companion: the autocorrelation NEVER exceeds `|H|`.** `(H ∩ dilate ρ H).card ≤ H.card`
for every `ρ` (trivially, `H ∩ · ⊆ H`). Combined with `exists_nontrivial_shift_autocorr_eq_card`,
the Kelley–Owen maximum `M(H) := max_{ρ≠1} |H ∩ ρH|` is EXACTLY `|H|`. -/
theorem subgroup_autocorr_le_card {H : Finset G} (ρ : G) :
    (H ∩ dilate ρ H).card ≤ H.card :=
  Finset.card_le_card (Finset.inter_subset_left)

/-- **The double-count is carried ENTIRELY inside `H`.** The nonzero-autocorrelation shifts are
EXACTLY the elements of `H`: `(H ∩ dilate ρ H).card ≠ 0 ↔ ρ ∈ H`. So the global double-count
`∑_ρ |H ∩ ρH| = |H|²` (`autocorr_sum_eq_sq`) is supported on the `|H|` inside-shifts, each
contributing `|H|` — `|H| · |H| = |H|²`, with ZERO mass outside `H`. The unsigned overlap has no
spreading to exploit. -/
theorem subgroup_autocorr_support {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hne : H.Nonempty)
    (ρ : G) :
    (H ∩ dilate ρ H).card ≠ 0 ↔ ρ ∈ H := by
  rw [subgroup_autocorr_exact hmul hinv ρ]
  by_cases hρ : ρ ∈ H
  · simp only [hρ, iff_true]
    obtain ⟨a, ha⟩ := hne
    exact Finset.card_ne_zero_of_mem ha
  · simp [hρ]

/-- **The EXACT multiplicative energy of a subgroup is `|H|³`.** The multiplicative energy
`E_×(H) = #{(a,b,c,d)∈H⁴ : a·b = c·d} = ∑_ρ |H ∩ ρ·H|²` is, by the exact all-or-nothing
autocorrelation, carried by the `|H|` inside-shifts each contributing `|H|²`:

  `∑_ρ (H ∩ dilate ρ H).card² = |H|·|H|² = |H|³`.

This is the MAXIMAL multiplicative energy (`E_× = |H|³` is the largest possible for an `|H|`-set,
since `∑_ρ a_ρ = |H|²` with each `a_ρ ≤ |H|` is maximized by concentrating on `|H|` full shifts).
It CONTRASTS with the MINIMAL additive energy `E_+(μ_n) = Θ(|H|²)` (ABF26, `RootsOfUnityAdditiveEnergy`):
the subgroup is simultaneously additively spread (min energy) and multiplicatively rigid (max energy) —
the sum-product extremality at the heart of why μ_n is the hard thin-set, and a direct exact corollary
of the all-or-nothing autocorrelation. -/
theorem subgroup_multiplicativeEnergy_eq_card_cube [Fintype G] {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) :
    ∑ ρ : G, ((H ∩ dilate ρ H).card) ^ 2 = H.card ^ 3 := by
  -- each summand is (if ρ∈H then |H| else 0)^2 = if ρ∈H then |H|^2 else 0
  have hpt : ∀ ρ : G, ((H ∩ dilate ρ H).card) ^ 2
      = if ρ ∈ H then H.card ^ 2 else 0 := by
    intro ρ
    rw [subgroup_autocorr_exact hmul hinv ρ]
    by_cases hρ : ρ ∈ H
    · simp [hρ]
    · simp [hρ]
  rw [Finset.sum_congr rfl (fun ρ _ => hpt ρ)]
  -- ∑_ρ (if ρ∈H then |H|^2 else 0) = (#{ρ : ρ∈H}) • |H|^2 = |H| • |H|^2 = |H|^3
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
  rw [smul_eq_mul]
  ring

end ProximityGap.Frontier.PencilAutocorrelation
