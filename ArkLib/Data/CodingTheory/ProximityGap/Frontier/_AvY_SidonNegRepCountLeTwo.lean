/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UnitCircleSidon
import Mathlib.Tactic

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# `μ_n` is Sidon-except-negation: the count form (#444)

`unitCircle_sidon` (in `UnitCircleSidon.lean`) shows that for `n`-th roots of unity, equal
nonzero sums force equal unordered pairs. This file repackages it as the **representation-count
bound** the additive-energy / Wick ladder consumes directly:

> For any nonzero target `c ≠ 0` (which excludes the single antipodal/negation diagonal),
> the number of ordered pairs `(x, y)` of `n`-th roots of unity with `x + y = c` is **at most 2**.

This is "Sidon-except-negation" stated as a `Finset.card ≤ 2` over a fixed finite carrier
`S : Finset ℂ` of `n`-th roots of unity, exactly the form the depth-`r` additive-energy count
needs to bound off-diagonal contributions by perfect matchings.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **Sidon-except-negation, count form.** Let `S : Finset ℂ` consist of `n`-th roots of unity
(`hS : ∀ x ∈ S, x ^ n = 1`, `n ≠ 0`). For any nonzero `c`, the set of ordered pairs
`(x, y) ∈ S × S` with `x + y = c` has at most two elements. (The only target with more
representations is `c = 0`, the negation diagonal.) -/
theorem sidon_neg_repCount_le_two {n : ℕ} (hn : n ≠ 0) (S : Finset ℂ)
    (hS : ∀ x ∈ S, x ^ n = 1) {c : ℂ} (hc : c ≠ 0) :
    ((S ×ˢ S).filter (fun p : ℂ × ℂ => p.1 + p.2 = c)).card ≤ 2 := by
  classical
  set F := (S ×ˢ S).filter (fun p : ℂ × ℂ => p.1 + p.2 = c) with hF
  rcases F.eq_empty_or_nonempty with hempty | ⟨q, hq⟩
  · simp [hempty]
  · obtain ⟨a, b⟩ := q
    rw [hF, mem_filter, mem_product] at hq
    obtain ⟨⟨haS, hbS⟩, hab⟩ := hq
    have hane : (a : ℂ) + b ≠ 0 := by rw [hab]; exact hc
    have hsub : F ⊆ {(a, b), (b, a)} := by
      intro p hp
      rw [hF, mem_filter, mem_product] at hp
      obtain ⟨⟨hxS, hyS⟩, hxy⟩ := hp
      obtain ⟨x, y⟩ := p
      have hsum : x + y = a + b := by rw [hxy, hab]
      rcases unitCircle_sidon hn (hS x hxS) (hS y hyS) (hS a haS) (hS b hbS) hsum
        (by rw [hsum]; exact hane) with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · simp [hx, hy]
      · simp [hx, hy]
    calc F.card ≤ ({(a, b), (b, a)} : Finset (ℂ × ℂ)).card := card_le_card hsub
      _ ≤ 2 := card_insert_le _ _ |>.trans (by simp)

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.sidon_neg_repCount_le_two
