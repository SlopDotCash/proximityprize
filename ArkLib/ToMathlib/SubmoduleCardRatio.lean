/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Subspace cardinality ratio as a dimension exponent

For a finite-dimensional vector space `K` over a finite field `F` and a subspace `W ⊆ K`,
the cardinality ratio `|W| / |K|` is exactly `q ^ (dim W − dim K)` where `q = |F|` (a
negative exponent: `dim W ≤ dim K`).  This file packages that as a real-`rpow` inequality:

* `rpow_le_card_submodule_ratio` — the analytic bound `q^(β−1) ≤ |W|/|K|` holds as soon as
  the **bare dimension comparison** `β − 1 ≤ dim_F W − dim_F K` does.

This is the cleanest form of the BKR06 *dimension-threshold* condition for the extension-field
list-size lower bound: it reduces the closeness *parameter inequality*
`q^(β−1) ≤ |W|/|K|` (the `hparam` hypothesis of
`BKR06.evalOnPoints_mem_closeCodewordsRel_of_param`) to a single linear comparison of
dimensions.  Nothing about the actual BKR06 parameter regime is asserted here — only the
exact algebraic equivalence between the cardinality ratio and the dimension exponent.

Mathlib-only; `sorry`/`axiom`-free; axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open scoped Classical

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [Fintype K] [Module F K] [FiniteDimensional F K]

/-- `|W| = q ^ dim_F W` as a real number (`q = |F|`). -/
lemma card_submodule_eq_rpow_finrank (W : Submodule F K) [Fintype W] :
    (Fintype.card W : ℝ) = (Fintype.card F : ℝ) ^ (Module.finrank F W : ℕ) := by
  have h : Fintype.card W = Fintype.card F ^ Module.finrank F W :=
    Module.card_eq_pow_finrank (K := F) (V := W)
  rw [h]
  push_cast
  ring

/-- **Cardinality ratio ⟹ dimension exponent (the extension-form parameter inequality).**
For a subspace `W` of the finite `F`-space `K` (`q = |F|`), the analytic bound
`q^(β−1) ≤ |W|/|K|` holds whenever the dimension comparison `β − 1 ≤ dim_F W − dim_F K`
does.  This discharges the `hparam` hypothesis of
`BKR06.evalOnPoints_mem_closeCodewordsRel_of_param` from a bare dimension threshold. -/
lemma rpow_le_card_submodule_ratio (W : Submodule F K) [Fintype W] (β : ℝ)
    (hq : (1 : ℝ) ≤ Fintype.card F)
    (hdim : β - 1 ≤ (Module.finrank F W : ℝ) - (Module.finrank F K : ℝ)) :
    (Fintype.card F : ℝ) ^ (β - 1) ≤ (Fintype.card W : ℝ) / (Fintype.card K : ℝ) := by
  have hqpos : (0 : ℝ) < Fintype.card F := by
    have : (0 : ℝ) < 1 := one_pos
    linarith
  -- rewrite both cardinalities as `q`-powers of their dimensions
  have hW : (Fintype.card W : ℝ) = (Fintype.card F : ℝ) ^ (Module.finrank F W : ℕ) :=
    card_submodule_eq_rpow_finrank W
  -- `K` itself, as a submodule (`⊤`), or directly:
  have hK : (Fintype.card K : ℝ) = (Fintype.card F : ℝ) ^ (Module.finrank F K : ℕ) := by
    have h : Fintype.card K = Fintype.card F ^ Module.finrank F K :=
      Module.card_eq_pow_finrank (K := F) (V := K)
    rw [h]; push_cast; ring
  rw [hW, hK]
  -- ratio of `rpow`s of nat powers = single `rpow` of the dimension difference
  rw [← Real.rpow_natCast (Fintype.card F : ℝ) (Module.finrank F W),
      ← Real.rpow_natCast (Fintype.card F : ℝ) (Module.finrank F K),
      ← Real.rpow_sub hqpos]
  -- monotone in the exponent
  exact Real.rpow_le_rpow_of_exponent_le hq hdim
