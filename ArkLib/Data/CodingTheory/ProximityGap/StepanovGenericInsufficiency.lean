/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovHighMultVanisher
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# THE GENERIC STEPANOV ENGINE CANNOT BEAT THE TRIVIAL BOUND (#389) — honest-negative

The Stepanov substrate has two halves, both **built and axiom-clean**:
* the **Wronskian non-vanishing / linear independence** of the generator family
  (`stepanov_generators_linearIndependent`, `linearIndependent_of_wronskianDet_ne_zero'`,
  `hasseWronskian_distinctDeg_ne_zero`), and
* the **existence + counting** engines (`exists_highMult_vanisher`,
  `stepanov_card_mul_M_le_natDegree`).

It is tempting to conclude these *already* yield the Garcia–Voloch bound `r(c) ≤ 4t^{2/3}`.
**They do not.**  This file proves, rigorously, that the *generic* assembly
(linearly-independent generators of bounded degree fed to the dimension-count existence engine)
**cannot beat the trivial bound `r(c) ≤ t`** — for an information-theoretic reason:

> **`generic_stepanov_degree_ge`** — a linearly-independent family of `F[X]` of degree `≤ B`
> has at most `B+1` members; so if the existence engine is to apply *unconditionally* (i.e.
> `t·M < #generators`, using `r(c) ≤ t`), then `t·M ≤ B`, whence the output bound `B/M ≥ t`.

The mechanism: a linearly-independent family living in the `(B+1)`-dimensional space
`degreeLT F (B+1)` has cardinality `≤ B+1`.  To make `exists_highMult_vanisher` fire without
assuming `r(c)` is already small, one needs `#generators > t·M`; combined with `#generators ≤ B+1`
this forces `B ≥ t·M`, so the counting conclusion `r(c)·M ≤ B` only gives `r(c) ≤ B/M`, and
`B/M ≥ t` is **vacuous** (`r(c) ≤ t` always).

**Consequence for the route map.**  The genuine Garcia–Voloch/Heath-Brown–Konyagin leverage does
*not* come from the generic dimension count.  It must come from the **degeneracy of the order-`M`
vanishing conditions on `A = G ∩ (G+c)`** — using that on `A` both `x^t = 1` and `(x−c)^t = 1`, so
the Hasse-derivative conditions collapse and have *effective* rank far below `r(c)·M`, letting an
auxiliary of degree `≪ t·M` vanish to order `M`.  That collapse is exactly what the explicit
order-2 auxiliary `Q = (c−X)^{n+1}+X^{n+1}−c` (file `RepCountStepanovOrderTwo.lean`, giving the
*non-generic* bound `r(c) ≤ (n+1)/2`) exploits, and what the sharp `t^{2/3}` bound needs at order
`~t^{1/3}`.  The Wronskian is built; the open core is the conditions-degeneracy count.  Issue #389.
-/

open Polynomial

namespace ArkLib.ProximityGap.StepanovGenericInsufficiency

variable {F : Type*} [Field F]

/-- A linearly-independent family of polynomials of degree `≤ B` has at most `B+1` members
(it lives in the `(B+1)`-dimensional space `degreeLT F (B+1)`). -/
theorem card_le_of_linearIndependent_degree_le {ι : Type*} [Fintype ι] (g : ι → F[X])
    (hg : LinearIndependent F g) {B : ℕ} (hB : ∀ i, (g i).natDegree ≤ B) :
    Fintype.card ι ≤ B + 1 := by
  classical
  -- every `g i` lies in the `(B+1)`-dimensional submodule `degreeLT F (B+1)`
  have hmem : ∀ i, g i ∈ degreeLT F (B + 1) := by
    intro i
    rw [mem_degreeLT]
    calc (g i).degree ≤ ((g i).natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (B : WithBot ℕ) := by exact_mod_cast hB i
      _ < ((B + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self B
  -- lift to the submodule and use `card ≤ finrank`
  set g' : ι → degreeLT F (B + 1) := fun i => ⟨g i, hmem i⟩ with hg'def
  have hg' : LinearIndependent F g' := by
    refine LinearIndependent.of_comp (degreeLT F (B + 1)).subtype ?_
    have : (degreeLT F (B + 1)).subtype ∘ g' = g := rfl
    rw [this]; exact hg
  haveI : Module.Finite F (degreeLT F (B + 1)) :=
    Module.Finite.of_surjective (degreeLTEquiv F (B + 1)).symm.toLinearMap
      (degreeLTEquiv F (B + 1)).symm.surjective
  have hfin : Module.finrank F (degreeLT F (B + 1)) = B + 1 := by
    rw [(degreeLTEquiv F (B + 1)).finrank_eq, Module.finrank_pi, Fintype.card_fin]
  have hcard : Fintype.card ι ≤ Module.finrank F (degreeLT F (B + 1)) :=
    hg'.fintype_card_le_finrank
  rw [hfin] at hcard
  exact hcard

/-- **THE GENERIC-STEPANOV INSUFFICIENCY.**  If a linearly-independent generator family of
degree `≤ B` is large enough for the existence engine to fire unconditionally on a point set of
size `≤ t` (i.e. `t·M < #generators`), then `t·M ≤ B` — so the resulting Stepanov bound `B/M` is
`≥ t`, no better than the trivial `r(c) ≤ |G| = t`. The generic dimension count is provably
incapable of a sub-trivial Garcia–Voloch bound. -/
theorem generic_stepanov_degree_ge {ι : Type*} [Fintype ι] (g : ι → F[X])
    (hg : LinearIndependent F g) {B M t : ℕ} (hB : ∀ i, (g i).natDegree ≤ B)
    (hexist : t * M < Fintype.card ι) : t * M ≤ B := by
  have hcard := card_le_of_linearIndependent_degree_le g hg hB
  omega

end ArkLib.ProximityGap.StepanovGenericInsufficiency

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.StepanovGenericInsufficiency.card_le_of_linearIndependent_degree_le
#print axioms ArkLib.ProximityGap.StepanovGenericInsufficiency.generic_stepanov_degree_ge
