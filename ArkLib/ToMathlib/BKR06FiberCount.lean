/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly

/-!
# BKR06 subspace-polynomial value-fiber count (Lemma 3.5 algebraic engine)

This file formalizes the *algebraic engine* of BKR06 Lemma 3.5
(Ben-Sasson–Kopparty–Radhakrishnan, *Subspace Polynomials and List Decoding of
Reed–Solomon Codes*, FOCS 2006): the linearized subspace polynomial `P_W` of an
`𝔽_q`-subspace `W ⊆ 𝕂` of dimension `d` is an additive (`𝔽_q`-linear) map whose
**kernel is exactly `W`**, hence it takes *each value in its image exactly `q^d`
times*.  That uniform fiber size `q^d` is the genuine counting heart that BKR06's
roots→close-codewords conversion turns into a large RS close-codeword family.

Concretely, with `L_x = #{y | P_W(y) = x}`:

* `BKR06.subspacePolyHom_zeroFiber_eq_subFinset` — the zero fiber is `subFinset W`.
* `BKR06.card_subspacePolyHom_zeroFiber` — `L_0 = |W| = q^d = P_W.natDegree`.
* `BKR06.card_subspacePolyHom_fiber_eq` — every in-range fiber equals `L_0`.
* `BKR06.card_subspacePolyHom_fiber_eq_natDegree` — every in-range fiber has size
  exactly `P_W.natDegree = q^d`.

These are fully proven, `sorry`-free, and (as audited below) axiom-clean
(`[propext, Classical.choice, Quot.sound]`).  They isolate the *counting*
content from the still-external geometric step (turning equal-size value fibers
into Reed–Solomon codewords close to a fixed received word).
-/

noncomputable section

open Polynomial BigOperators Finset

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Module F K]

omit [Fintype K] [DecidableEq K] in
/-- A point lies in the zero fiber of `subspacePolyHom W` iff it lies in `W`. -/
lemma mem_subspacePolyHom_zero_iff (W : Submodule F K) [Fintype W] (x : K) :
    subspacePolyHom W x = 0 ↔ x ∈ W := by
  show (subspacePoly (subFinset W)).eval x = 0 ↔ x ∈ W
  rw [show (subspacePoly (subFinset W)).eval x = 0 ↔ (subspacePoly (subFinset W)).IsRoot x from
        Iff.rfl,
      subspacePoly_isRoot_iff, mem_subFinset]

/-- **BKR06 Lemma 3.5 (zero fiber).** The zero fiber `{y | P_W(y) = 0}` of the
linearized subspace-polynomial map is exactly the carrier finset of `W`. -/
lemma subspacePolyHom_zeroFiber_eq_subFinset (W : Submodule F K) [Fintype W] :
    ({x : K | subspacePolyHom W x = 0} : Finset K) = subFinset W := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_subFinset]
  exact mem_subspacePolyHom_zero_iff W x

/-- **BKR06 Lemma 3.5 (zero-fiber count).** The zero fiber of the subspace-polynomial
map has exactly `|W| = (subspacePoly W).natDegree = q^d` elements. -/
lemma card_subspacePolyHom_zeroFiber (W : Submodule F K) [Fintype W] :
    #{x : K | subspacePolyHom W x = 0}
      = (subspacePoly (subFinset W)).natDegree := by
  rw [subspacePolyHom_zeroFiber_eq_subFinset, subspacePoly_natDegree]

/-- **BKR06 Lemma 3.5 (uniform fiber size).** Every value `c` in the image of the
linearized map `P_W` is attained by the same number of points as the value `0`.
This is the additive-group fiber-equinumerosity for the hom `subspacePolyHom W`. -/
lemma card_subspacePolyHom_fiber_eq (W : Submodule F K) [Fintype W]
    {c : K} (hc : c ∈ Set.range (subspacePolyHom W)) :
    #{x : K | subspacePolyHom W x = c}
      = #{x : K | subspacePolyHom W x = 0} :=
  AddMonoidHom.card_fiber_eq_of_mem_range (subspacePolyHom W) hc
    ⟨0, map_zero _⟩

/-- **BKR06 Lemma 3.5 (uniform fiber size = `q^d`).** Every value `c` in the image of
the linearized subspace polynomial `P_W` of a `d`-dimensional `𝔽_q`-subspace `W ⊆ 𝕂`
is attained at exactly `(subspacePoly W).natDegree = q^d` points.

This is the genuine *counting* heart of BKR06 Lemma 3.5: a degree-`q^d` linearized
polynomial takes each value in its image exactly `q^d` times. -/
theorem card_subspacePolyHom_fiber_eq_natDegree (W : Submodule F K) [Fintype W]
    {c : K} (hc : c ∈ Set.range (subspacePolyHom W)) :
    #{x : K | subspacePolyHom W x = c}
      = (subspacePoly (subFinset W)).natDegree := by
  rw [card_subspacePolyHom_fiber_eq W hc, card_subspacePolyHom_zeroFiber]

/-- **BKR06 Lemma 3.5 (uniform fiber size = `q^d`, finrank form).** With `q = |𝔽|`,
every in-range value of `P_W` has fiber size exactly `q^{dim_𝔽 W}`. -/
theorem card_subspacePolyHom_fiber_eq_pow_finrank [Fintype F]
    (W : Submodule F K) [Fintype W]
    {c : K} (hc : c ∈ Set.range (subspacePolyHom W)) :
    #{x : K | subspacePolyHom W x = c}
      = (Fintype.card F) ^ (Module.finrank F W) := by
  rw [card_subspacePolyHom_fiber_eq_natDegree W hc, subspacePoly_natDegree_eq_pow_finrank]

end BKR06

-- Axiom audit on the freshly elaborated declarations.
#print axioms BKR06.subspacePolyHom_zeroFiber_eq_subFinset
#print axioms BKR06.card_subspacePolyHom_zeroFiber
#print axioms BKR06.card_subspacePolyHom_fiber_eq
#print axioms BKR06.card_subspacePolyHom_fiber_eq_natDegree
#print axioms BKR06.card_subspacePolyHom_fiber_eq_pow_finrank
