/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Roots

/-!
# The GENERAL depth-`h` symmetric-function Sidon core (#444, §0)

The `B_h`-Sidon depth ladder for `μ_n` was built rung by rung —
`unitCircle_sidon` (2), `unitCircle_sidon_triple` (3), `unitCircle_sidon_quad` (4),
`unitCircle_sidon_quint` (5) — each proving the char-free integral-domain core
"equal elementary symmetric functions `e₁,…,e_h` ⟹ equal unordered `h`-multiset" by an explicit
`linear_combination` root-membership identity plus a leftover reduction.  This file proves that
char-free core **for ALL `h` at once**, directly from Vieta + the fact that a `∏ (X - C·rᵢ)`
polynomial determines its multiset of roots:

> **`multiset_eq_of_esymm_eq`** — over a commutative ring that is an integral domain, two multisets
> `s, t` of the **same cardinality** with `s.esymm j = t.esymm j` for **every** `j` are **equal**.

This is the depth-uniform statement underlying the per-rung algebraic cores: it is exactly the
input "equal `e₁,…,e_h` ⟹ equal multiset" with no bound on `h`.

**Mechanism (clean, no per-`h` `linear_combination`).**  By Vieta
(`Multiset.prod_X_sub_X_eq_sum_esymm`) the coefficients of `∏_{r ∈ s} (X - C r)` are determined by
`s.esymm` and `card s`.  Equal cardinalities and equal `esymm` (all `j`) therefore give equal
product polynomials; applying `Multiset.roots_multiset_prod_X_sub_C` (the roots of `∏ (X - C r)`
over a multiset are that multiset) to both sides recovers `s = t`.

**Honest scope.**  This is the *char-free, depth-uniform* algebraic core — the field-universal half
of the Sidon ladder (it is NOT thinness-specific: it holds for any multiset over a domain).  It is
**NOT** a CORE closure and **NOT** a refutation.  The roots-of-unity / thinness content (recovering
the conjugate-paired symmetric functions `eₖ = e_h·conj(e_{h−k})` for free, so that only the anchors
and the unpaired middle data need hypothesizing) lives in the per-`n` wrappers
(`unitCircle_sidon_*`); this file supplies the algebraic engine those wrappers feed.  No capacity /
beyond-Johnson / cliff-at-`n/2` claim (ASYMPTOTIC GUARD untouched); `M(μ_n) ≤ C√(n·log(p/n))` OPEN.
NON-MOMENT (pure symmetric-function / polynomial-root algebra).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The `∏ (X − C·r)` polynomial is determined by `card` and all `esymm`.**  For multisets `s, t`
over a commutative ring with equal cardinality and equal elementary symmetric functions at every
index, the monic products `∏_{r ∈ s} (X − C r)` and `∏_{r ∈ t} (X − C r)` are equal.  (Vieta:
the coefficients are exactly the signed `esymm`.) -/
theorem prod_X_sub_C_eq_of_esymm_eq {R : Type*} [CommRing R] {s t : Multiset R}
    (hcard : Multiset.card s = Multiset.card t)
    (hesymm : ∀ j, s.esymm j = t.esymm j) :
    (s.map fun r => X - C r).prod = (t.map fun r => X - C r).prod := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hcard]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hesymm j]

/-- **The GENERAL char-free depth-`h` Sidon core.**  Over an integral domain, two multisets of the
**same cardinality** with **equal elementary symmetric functions at every index** are **equal**.
This is the depth-uniform "equal `e₁,…,e_h` ⟹ equal unordered `h`-multiset" underlying every rung
of the `B_h`-Sidon ladder (`triple_eq_of_esymm_eq`, `quadruple_eq_of_esymm_eq`,
`quintuple_eq_of_esymm_eq`), proved here for all `h` at once via Vieta + root recovery. -/
theorem multiset_eq_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R] {s t : Multiset R}
    (hcard : Multiset.card s = Multiset.card t)
    (hesymm : ∀ j, s.esymm j = t.esymm j) :
    s = t := by
  have hpoly := prod_X_sub_C_eq_of_esymm_eq hcard hesymm
  have hs := Polynomial.roots_multiset_prod_X_sub_C s
  have ht := Polynomial.roots_multiset_prod_X_sub_C t
  rw [← hs, ← ht, hpoly]

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.prod_X_sub_C_eq_of_esymm_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.multiset_eq_of_esymm_eq
