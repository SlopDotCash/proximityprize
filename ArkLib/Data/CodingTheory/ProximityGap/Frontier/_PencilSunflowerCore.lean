/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._KelleyOwenDilationPencil

/-!
# LEVER K, graded: the sunflower (common-`M`-core) dilation-pencil count (#407/#444)

`_KelleyOwenDilationPencil.pencil_card_core` proves the `M = 1` extreme of the dilation-pencil
count: `r` size-`r` blocks through a common point `p`, pairwise meeting in **exactly** `{p}`, force
`r·(r−1) + 1 ≤ |G|` (the Stepanov `√N` root count for the trinomial `t = 3` face). Its own honest
scope note records the degradation for the general `t = k+2` agreement polynomial: the dilation
pencil is `k`-dimensional, two members can share up to `~k` common roots, and the same double-count
then yields only `r² ≲ k·N`, the **Johnson** radius, never sub-Johnson. That degradation statement
lived only in **prose** in both `_KelleyOwenDilationPencil` and `PencilAutocorrRootBound`; it was
never formalized.

This file formalizes the clean, **exactly-generalizing** rung of that degradation: the
**sunflower** case, where the `r` blocks pairwise meet in a *common* core set `T` of size `M`
(`p ∈ T`). It extends `pencil_card_core` from the singleton core `T = {p}` (`M = 1`) to a general
`M`-element core, with the headline bound

  `r·(r − M) + M ≤ |G|`,        (`pencil_sunflower_core`)

which **recovers `pencil_card_core` exactly at `M = 1`** (`r·(r−1) + 1 ≤ |G|`), and the `√`
extraction

  `(r − M)² < |G|`,             (`pencil_sunflower_sqrt_bound`)

i.e. `r ≤ M + √|G|`, the explicit "`Johnson + core-offset`" root count. The `M = 1` case is
`r ≤ 1 + √|G|` (Kelley–Owen); the prize worst-case core `M ≍ n/2` pushes the offset to `n/2`, the
Johnson scale, exactly matching `_KelleyOwenDilationPencil`'s prose degradation and
`PencilAutocorrelation.autocorr_ge_coset_core`'s `M(S) ≥ n/2` obstruction.

## Proof (sunflower punctured-disjointness)

The `T`-punctured blocks `Cᵢ := Bᵢ \ T` have size `r − M`, are pairwise **disjoint** (any common
point would lie in `Bᵢ ∩ Bⱼ = T`, contradicting `∉ T`), and are all disjoint from `T`. So
`T ⊔ ⨆ᵢ Cᵢ ⊆ G` is a disjoint union of cardinality `M + r·(r − M)`, giving the bound. This is the
same punctured-disjointness mechanism as `pencil_card_core`, with the singleton `{p}` replaced by
the core `T`.

## Honest scope (the sunflower hypothesis is STRONGER than the prize pairwise bound)

This is **NOT** a closure of the prize and **NOT** the autocorrelation-route bound. The sunflower
hypothesis (`Bᵢ ∩ Bⱼ = T` a *single common* core for all pairs) is **strictly stronger** than the
prize-relevant pairwise hypothesis (`|Bᵢ ∩ Bⱼ| ≤ M` with *possibly different* intersections per
pair, the form `PencilAutocorrelation.pencil_overlap_le_of_autocorr` actually delivers from a
bounded multiplicative autocorrelation). So this brick is the clean sunflower rung of the
degradation, not the general-position Fisher bound. The general pairwise-`≤ M` core (`r² ≲ M·N` by a
Cauchy–Schwarz/Fisher double-count, with no common `T`) is the harder honest target and stays a
separate brick. The prize CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**. Probe-verified on genuine
sunflowers (`scripts/probes/probe_sunflower_pencil.py`): every common-`M`-core family satisfies
`r·(r−M) + M ≤ n` and `(r−M)² < n`, recovering the `M = 1` numbers of `pencil_card_core`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.PencilSunflowerCore

/-- **Sunflower dilation-pencil cardinality core.** Suppose `univ : Finset G` carries a family of
`r` "blocks" `B : Fin r → Finset G`, each of size `r`, sharing a **common core** `T` (`T ⊆ Bᵢ` for
every `i`) of size `M`, and pairwise meeting in **exactly** `T` (`Bᵢ ∩ Bⱼ = T` for `i ≠ j`). Then

  `r·(r − M) + M ≤ |univ|`.

The `M = 1`, `T = {p}` case is `pencil_card_core` (`r·(r−1) + 1 ≤ |univ|`).
Proof: the `T`-punctured blocks `Cᵢ = Bᵢ \ T` are pairwise disjoint (a shared point would lie in
`Bᵢ ∩ Bⱼ = T`), each of size `r − M`, all disjoint from `T`; the disjoint union
`T ⊔ ⨆ᵢ Cᵢ ⊆ univ` has card `M + r·(r − M)`. -/
theorem pencil_sunflower_core {G : Type*} [DecidableEq G] (univ : Finset G)
    (r M : ℕ) (hr : 1 ≤ r) (B : Fin r → Finset G) (T : Finset G)
    (hsub : ∀ i, B i ⊆ univ)
    (hsize : ∀ i, (B i).card = r)
    (hTsize : T.card = M)
    (hTsub : ∀ i, T ⊆ B i)
    (hpair : ∀ i j, i ≠ j → B i ∩ B j = T) :
    r * (r - M) + M ≤ univ.card := by
  classical
  have hrpos : 0 < r := hr
  -- punctured blocks
  set C : Fin r → Finset G := fun i => (B i) \ T with hC
  have hMler : M ≤ r := by
    have : T.card ≤ (B ⟨0, hrpos⟩).card := Finset.card_le_card (hTsub _)
    rw [hTsize, hsize] at this; exact this
  have hCcard : ∀ i, (C i).card = r - M := by
    intro i
    rw [hC, Finset.card_sdiff_of_subset (hTsub i), hsize i, hTsize]
  have hCdisjT : ∀ i, Disjoint T (C i) := by
    intro i
    rw [hC]; exact Finset.sdiff_disjoint.symm
  have hCdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [hC, Finset.mem_sdiff] at hxi hxj
    have hmem : x ∈ B i ∩ B j := Finset.mem_inter.mpr ⟨hxi.1, hxj.1⟩
    rw [hpair i j hij] at hmem
    exact hxi.2 hmem
  set D : Finset G := Finset.univ.biUnion C with hD
  have hDcard : D.card = r * (r - M) := by
    rw [hD, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun i _ => hCcard i)]
      simp [Finset.sum_const, Finset.card_univ]
    · intro i _ j _ hij; exact hCdisj i j hij
  have hTD : Disjoint T D := by
    rw [hD, Finset.disjoint_biUnion_right]
    intro i _; exact hCdisjT i
  -- T ⊔ D ⊆ univ
  have hTsubU : T ⊆ univ := (hTsub ⟨0, hrpos⟩).trans (hsub _)
  have hDsubU : D ⊆ univ := by
    intro x hx
    rw [hD, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    rw [hC, Finset.mem_sdiff] at hxi
    exact hsub i hxi.1
  have hunionsub : T ∪ D ⊆ univ := Finset.union_subset hTsubU hDsubU
  have hcardTD : (T ∪ D).card = M + r * (r - M) := by
    rw [Finset.card_union_of_disjoint hTD, hTsize, hDcard]
  have := Finset.card_le_card hunionsub
  rw [hcardTD] at this
  omega

/-- **The `√|G|` extraction for the sunflower core.** From `r·(r − M) + M ≤ N` the offset root
count satisfies

  `(r − M)·(r − M) < N`,

i.e. `r − M < √N`, `r < M + √N` ("Johnson radius `√N` plus a core offset `M`"). At `M = 1` this is
`(r − 1)² < N` (`KelleyOwenDilationPencil.stepanov_sqrt_bound`); the prize core `M ≍ n/2` makes the
offset the dominant Johnson-scale term. The hypothesis `1 ≤ M` is the nonempty-core condition
(`p ∈ T`, so `M = |T| ≥ 1`), under which `M ≤ N` forces `N > 0` even in the degenerate `r ≤ M`
branch. -/
theorem pencil_sunflower_sqrt_bound {r M N : ℕ} (hM : 1 ≤ M)
    (h : r * (r - M) + M ≤ N) :
    (r - M) * (r - M) < N := by
  rcases lt_or_ge M r with hlt | hle
  · -- r > M : (r-M)^2 ≤ r*(r-M) < r*(r-M)+M ≤ N
    have hpos : 0 < r - M := by omega
    have h1 : (r - M) * (r - M) ≤ r * (r - M) := by
      apply Nat.mul_le_mul_right; omega
    omega
  · -- r ≤ M : r - M = 0, and 0 < M ≤ r*(r-M)+M ≤ N, so 0 = 0*0 < N.
    have hrM : r - M = 0 := by omega
    rw [hrM]
    omega

end ProximityGap.Frontier.PencilSunflowerCore

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.PencilSunflowerCore.pencil_sunflower_core
#print axioms ProximityGap.Frontier.PencilSunflowerCore.pencil_sunflower_sqrt_bound
