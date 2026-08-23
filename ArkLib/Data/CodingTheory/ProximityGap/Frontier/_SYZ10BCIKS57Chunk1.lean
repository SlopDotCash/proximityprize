/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan

/-!
# SYZ10 — BCIKS20 Claim 5.7 program, Chunk 1: the surface / interpolation existence step

This file opens the multi-chunk program that discharges the (strictly-smaller) Johnson-lane
residual `CellPackageSupplyDiscLocus` (`Frontier/_SYZ8CellPackageSupply.lean`) — the
per-cell disc-locus form of the [BCIKS20] Claim 5.7 heavy-agreement package supply.

`CellPackageSupplyDiscLocus` asks, for each *large* cell, for a full `DiscLocusCellData`
bundle.  The classical construction of that bundle (BCIKS20 §5–§6) proceeds in stages; this
file lands the **first** stage: the Guruswami–Sudan *interpolation surface* existence.  This
is the polynomial-method dimension-count: over `n` interpolation points there is a **nonzero**
bivariate polynomial `Q(X,Y)` of bounded `(1, k−1)`-weighted degree vanishing to order `≥ m`
at every point.  This is the raw surface out of which the later chunks select an irreducible
place curve `H`, its centre `x₀`, the `Y`-root divisor `w`, and the discriminant geometry.

The heavy mathematics of this stage is **already fully proven and axiom-clean in-tree**:
`GuruswamiSudan.gs_existence` (`ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean`).
Per the SYZ10 chunk plan, Chunk 1 is therefore the *adaptor*: it names the surface-existence
step as a reusable interface Prop `SurfaceInterpolantSupply`, discharges it from
`gs_existence`, and exposes the projection accessors (`Q ≠ 0`, weighted-degree bound,
root/multiplicity) that the later chunks (irreducible-factor selection producing `H` and its
`Hypotheses`) consume.  Naming the interface Prop is what lets Chunk 2 compose on top without
re-deriving the interpolation dimension count.

## Interface Prop exported for later chunks

* `SurfaceInterpolantSupply k n m ωs f : Prop` — existence of a GS interpolation surface at the
  rate-corrected degree bound `gs_degree_bound k n m`.
* `surfaceInterpolantSupply` — its discharge from `gs_existence` (`1 < k`, `n ≠ 0`, `1 ≤ m`).
* `SurfaceInterpolantSupply.{surface, surface_conditions, surface_ne_zero,
  surface_weightedDegree_le, surface_roots, surface_multiplicity}` — accessors bridging to the
  fields chunk 2 selects `H` from.

## Attribution / honesty

The substantive content (the linear-algebra dimension count that produces the nonzero
interpolant) is entirely `gs_existence`; this file adds no new mathematics — it fixes the
interface boundary.  All declarations are `#print axioms`-audited at the foot of the file and
are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only), matching `gs_existence`.
-/

namespace BCIKS20.CellPencilJohnson.SYZ10

open Polynomial Polynomial.Bivariate GuruswamiSudan

variable {F : Type} [Field F] [DecidableEq F]

/-- **Chunk-1 interface Prop: the GS interpolation-surface existence step.**

For interpolation points `(ωs i, f i)` (`i : Fin n`) there is a nonzero bivariate polynomial
`Q(X, Y)` whose `(1, k−1)`-weighted degree is at most the rate-corrected bound
`gs_degree_bound k n m` and which vanishes to order `≥ m` at every point.  This is the raw
[BCIKS20] §5 surface: the later chunks select the irreducible place curve `H`, the centre
`x₀`, the `Y`-root divisor `w`, and the discriminant geometry inside its factorization.

Named as a Prop so Chunk 2 can consume the surface without re-running the dimension count. -/
def SurfaceInterpolantSupply (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : Prop :=
  ∃ Q : F[X][Y], GuruswamiSudan.Conditions k m (gs_degree_bound k n m) ωs f Q

/-- **Chunk 1 (discharge).**  The surface-existence step holds whenever `1 < k`, `n ≠ 0`,
`1 ≤ m`.  This is a verbatim repackaging of the in-tree, axiom-clean
`GuruswamiSudan.gs_existence` — no new mathematics; the dimension count lives there. -/
theorem surfaceInterpolantSupply {k n m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    SurfaceInterpolantSupply k n m ωs f :=
  GuruswamiSudan.gs_existence k n ωs f hk hn hm

namespace SurfaceInterpolantSupply

variable {k n m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}

/-- The chosen interpolation surface `Q`. -/
noncomputable def surface (h : SurfaceInterpolantSupply k n m ωs f) : F[X][Y] :=
  Exists.choose h

/-- The chosen surface satisfies the GS conditions at `gs_degree_bound k n m`. -/
theorem surface_conditions (h : SurfaceInterpolantSupply k n m ωs f) :
    GuruswamiSudan.Conditions k m (gs_degree_bound k n m) ωs f h.surface :=
  Exists.choose_spec h

/-- The chosen surface is nonzero (accessor for chunk 2's factor selection). -/
theorem surface_ne_zero (h : SurfaceInterpolantSupply k n m ωs f) : h.surface ≠ 0 :=
  (h.surface_conditions).Q_ne_0

/-- The chosen surface has bounded `(1, k−1)`-weighted degree. -/
theorem surface_weightedDegree_le (h : SurfaceInterpolantSupply k n m ωs f) :
    Polynomial.Bivariate.weightedDegree h.surface 1 (k - 1)
      ≤ gs_degree_bound k n m :=
  (h.surface_conditions).Q_deg

/-- The chosen surface vanishes at every interpolation point. -/
theorem surface_roots (h : SurfaceInterpolantSupply k n m ωs f) :
    ∀ i, (h.surface.eval (Polynomial.C (f i))).eval (ωs i) = 0 :=
  (h.surface_conditions).Q_roots

/-- The chosen surface vanishes to order `≥ m` at every interpolation point (bivariate
`Polynomial.Bivariate.rootMultiplicity`, valued in `Option ℕ`). -/
theorem surface_multiplicity (h : SurfaceInterpolantSupply k n m ωs f) :
    ∀ i, m ≤ Polynomial.Bivariate.rootMultiplicity h.surface (ωs i) (f i) :=
  (h.surface_conditions).Q_multiplicity

end SurfaceInterpolantSupply

end BCIKS20.CellPencilJohnson.SYZ10

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ10.surfaceInterpolantSupply
#print axioms BCIKS20.CellPencilJohnson.SYZ10.SurfaceInterpolantSupply.surface_ne_zero
#print axioms BCIKS20.CellPencilJohnson.SYZ10.SurfaceInterpolantSupply.surface_weightedDegree_le
#print axioms BCIKS20.CellPencilJohnson.SYZ10.SurfaceInterpolantSupply.surface_roots
#print axioms BCIKS20.CellPencilJohnson.SYZ10.SurfaceInterpolantSupply.surface_multiplicity
