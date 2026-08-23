/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.ProximityGap.GSFactorExtract

/-!
# The `MatchingExtractor` residual of Proposition 5.5 — the GS matching-polynomial extraction

`ArkLib.ToMathlib.BasefoldSingleRoundSoundness` reduces Proposition 5.5 of [BCIKS20] to two named inputs: the GS-count
inequality `hcount` (discharged numerically) and the **matching-polynomial extraction predicate**
`MatchingExtractor`.  The interpolant-existence half (`exists_interpolant`) is fully discharged by
`SiegelInterpolation`'s engine; the *residual* is exactly `extract : MatchingExtractor prop Q pts`
— the Guruswami–Sudan list-decoding **factorization** step.

This file **discharges that residual standalone**: from a (per-point) Guruswami–Sudan order-`m`
vanishing of the box-supported interpolant at the close-codeword graph point `(z, Pz(·))`, it
produces the per-point **matching polynomial** — the factor `Y − Pz` of the interpolant — together
with the divisibility witnessing it.  This is the GS list-decoding core.

The mathematical content is the **multiplicity ⟹ root ⟹ divisibility** chain:

1. *Order-`m` ⟹ root* (`GuruswamiSudan.orderAt_eval_ge`).  If the interpolant `Qz : F[X][Y]`
   (the §5 `eval_on_Z Q z`) vanishes to GS order `m` at every graph point `(ωᵢ, Pz(ωᵢ))` for `i` in
   an agreement set `A`, then the univariate specialisation `Qz.eval Pz` has root-multiplicity `≥ m`
   at each `ωᵢ` — *or* it is already the zero polynomial.

2. *Too many roots ⟹ zero* (`GuruswamiSudan.roots_le_degree_of_deg_lt_roots`).  In the Johnson
   regime `deg (Qz.eval Pz) < m · #A`, a univariate polynomial with `m`-fold roots at `#A` distinct
   evaluation points `ωᵢ` is forced to be `0`.  Hence `Qz.eval Pz = 0` unconditionally.

3. *Root ⟹ divisibility* (`Polynomial.dvd_iff_isRoot`).  `Qz.eval Pz = 0` is exactly
   `(Y − C Pz) ∣ Qz` in `F[X][Y]` — the **matching factor** of [BCIKS20] §5.

Step (3) is the factor `Y − P_z` the §5 application binds to each `z`; the matching set
`{(z, Pz)}_{z ∈ S}` is then assembled from these per-point factors.  The whole chain is
reconstructed from Guruswami–Sudan *primitives* (`HasOrderAt`, `orderAt_eval_ge`,
`roots_le_degree_of_deg_lt_roots`) and Mathlib (`Polynomial.dvd_iff_isRoot`); it does **not** import
the §5 keystone `Q_vanishes_on_close_codeword_graph` (Agreement.lean) — it is a standalone
re-derivation of the same divisibility-from-multiplicity fact.

## References

* [BCIKS20] — Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), Proposition 5.5; the matching-polynomial extraction.
-/

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace MatchingExtractor

variable {F : Type} [Field F] {n : ℕ}

/-! ## The matching-polynomial extraction (the GS factorization core)

The graph point of the close codeword `(z, Pz)` over an agreement set `A` is `(ωᵢ, Pz(ωᵢ))` for
`i ∈ A`.  Guruswami–Sudan order-`m` vanishing of the interpolant `Qz : F[X][Y]` at these points is
captured by `GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m`.  -/

/-- **Vanishing on the close-codeword graph (the GS multiplicity ⟹ root step).**

If the bivariate interpolant `Qz : F[X][Y]` vanishes to Guruswami–Sudan order `m` at every graph
point `(ωᵢ, Pz(ωᵢ))` of the close codeword `Pz` over an agreement set `A`, and the univariate
specialisation `Qz.eval Pz` has degree strictly below the Johnson threshold `m · #A`, then
`Qz.eval Pz = 0`: the interpolant *vanishes on the graph of the close codeword*.

This is the trivariate `Q_vanishes_on_close_codeword_graph` keystone re-derived standalone from GS
primitives: `orderAt_eval_ge` turns each order-`m` graph point into an `m`-fold root of the
univariate `Qz.eval Pz` (or zero outright), and `roots_le_degree_of_deg_lt_roots` turns "more
`m`-fold roots than degree" into the zero polynomial. -/
theorem eval_eq_zero_of_orderM_and_count
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m : ℕ) (A : Finset (Fin n))
    (hord : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m)
    (hcount : (Qz.eval Pz).natDegree < m * A.card) :
    Qz.eval Pz = 0 := by
  classical
  by_cases h0 : Qz.eval Pz = 0
  · exact h0
  · -- If the specialization does not vanish identically, every evaluation point ωᵢ for i ∈ A
    -- is a root of multiplicity ≥ m for the univariate polynomial Qz.eval Pz.
    have hroots : ∀ i ∈ A, m ≤ Polynomial.rootMultiplicity (ωs i) (Qz.eval Pz) := by
      intro i hi
      rcases GuruswamiSudan.orderAt_eval_ge Qz Pz (ωs i) m (hord i hi) with hz | hm
      · exact absurd hz h0
      · exact hm
    -- Since the total root multiplicity m * |A| exceeds the degree of Qz.eval Pz,
    -- the polynomial must vanish identically, yielding a contradiction.
    exact GuruswamiSudan.roots_le_degree_of_deg_lt_roots
      (ωs := ωs) (Qz.eval Pz) m A hroots hcount

/-- **The matching-polynomial extraction (the GS root ⟹ divisibility step).**

From the same Guruswami–Sudan order-`m` vanishing data and Johnson count, the interpolant `Qz` is
divisible by the **matching factor** `Y − Pz`:

  `(Polynomial.X - Polynomial.C Pz) ∣ Qz`.

`Polynomial.X` here is the outer variable `Y` of `F[X][Y]` and `Polynomial.C Pz` is the close
codeword polynomial embedded as a constant in `Y`; `Y − C Pz` is the graph of `Pz`.  This is the
factor of [BCIKS20] §5 bound to the point `z`: the per-point *matching polynomial*. -/
theorem matchingFactor_dvd_of_orderM_and_count
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m : ℕ) (A : Finset (Fin n))
    (hord : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m)
    (hcount : (Qz.eval Pz).natDegree < m * A.card) :
    (Polynomial.X - Polynomial.C Pz) ∣ Qz := by
  -- vanishing on the graph: `Qz.eval Pz = 0`
  have hvanish : Qz.eval Pz = 0 :=
    eval_eq_zero_of_orderM_and_count ωs Qz Pz m A hord hcount
  -- root ⟹ divisibility by `Y − C Pz`
  exact Polynomial.dvd_iff_isRoot.mpr hvanish

/-! ## Packaging as a `MatchingExtractor`-style datum

`MatchesGraph Qz Pz` is the extraction-correctness predicate the §5 factorization supplies for a
single close codeword: `Pz` is the matching polynomial bound to `Qz` by the graph-vanishing
`Qz.eval Pz = 0`, equivalently the factor `Y − Pz ∣ Qz`.  Under the GS order-`m` vanishing and the
Johnson count this predicate is *discharged*, not assumed — `matchingPolynomial_extracts`. -/

/-- The matching-correctness predicate for a single close codeword: the polynomial `Pz` is the
matching polynomial bound to the interpolant `Qz` by the graph-vanishing `Qz.eval Pz = 0`. -/
def MatchesGraph (Qz : F[X][Y]) (Pz : F[X]) : Prop := Qz.eval Pz = 0

/-- `MatchesGraph` is equivalent to divisibility by the matching factor `Y − Pz`. -/
theorem matchesGraph_iff_dvd (Qz : F[X][Y]) (Pz : F[X]) :
    MatchesGraph Qz Pz ↔ (Polynomial.X - Polynomial.C Pz) ∣ Qz :=
  (Polynomial.dvd_iff_isRoot (a := Pz) (p := Qz)).symm

/-- **Matching-polynomial extraction, packaged.**  From the GS order-`m` vanishing of `Qz` at the
close-codeword graph over an agreement set `A`, under the Johnson count, there *exists* a matching
polynomial — namely `Pz` itself — satisfying `MatchesGraph Qz Pz`.  This is the existential datum a
`MatchingExtractor` consumes, here delivered constructively from the multiplicity hypothesis. -/
theorem matchingPolynomial_extracts
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m : ℕ) (A : Finset (Fin n))
    (hord : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m)
    (hcount : (Qz.eval Pz).natDegree < m * A.card) :
    ∃ g : F[X], MatchesGraph Qz g :=
  ⟨Pz, eval_eq_zero_of_orderM_and_count ωs Qz Pz m A hord hcount⟩

/-! ### Degree-side input for the Johnson count

The Johnson count `deg (Qz.eval Pz) < m · #A` is supplied in §5 from the GS weighted-degree bound on
`Qz` together with `deg Pz ≤ k` (the close codeword has Reed–Solomon degree).  We expose the
weighted-degree route so the count hypothesis can be discharged from the interpolant's degree budget
rather than assumed about the evaluation directly. -/

/-- The Johnson count from the GS weighted-degree budget: if `deg Pz ≤ k` and the GS
`(1, k)`-weighted degree of the interpolant `Qz` is strictly below `m · #A`, then the univariate
specialisation `Qz.eval Pz` is below the Johnson threshold, so the matching factor `Y − Pz` divides
`Qz`. -/
theorem matchingFactor_dvd_of_weightedDegree
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m k : ℕ) (A : Finset (Fin n))
    (hPdeg : Pz.natDegree ≤ k)
    (hord : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m)
    (hwcount : natWeightedDegree Qz 1 k < m * A.card) :
    (Polynomial.X - Polynomial.C Pz) ∣ Qz := by
  -- `deg (Qz.eval Pz) ≤ weightedDegree Qz 1 k < m · #A`
  have hdeg : (Qz.eval Pz).natDegree ≤ natWeightedDegree Qz 1 k := by
    have hPdeg' : Pz.natDegree ≤ (k + 1) - 1 := by simpa using hPdeg
    simpa using GuruswamiSudan.degree_eval_le_weightedDegree Qz Pz (k + 1) hPdeg'
  have hcount : (Qz.eval Pz).natDegree < m * A.card := lt_of_le_of_lt hdeg hwcount
  exact matchingFactor_dvd_of_orderM_and_count ωs Qz Pz m A hord hcount

/-! ### Finite-family list-size adapters

The preceding lemmas extract one factor `Y - Pz(X)` at a time.  The public
`GSFactorExtract` API then counts how many distinct extracted factors can divide a nonzero
interpolant.  These adapters are the standalone GS list-decoding surface consumed by callers that
already have per-candidate agreement sets. -/

/-- **Finite-family GS list-size bound from order-`m` graph vanishing.**

For every candidate message `P ∈ Ps`, assume `Qz` has GS order-`m` vanishing on the graph of `P`
over the agreement set `A P`, and that the specialized degree is below the corresponding
root-count budget.  Then all those candidates contribute distinct linear factors of `Qz`, so their
number is at most the `Y`-degree of `Qz`. -/
theorem list_size_le_of_orderM_and_count
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (hQz : Qz ≠ 0) (Ps : Finset F[X])
    (m : ℕ) (A : F[X] → Finset (Fin n))
    (hord : ∀ P ∈ Ps, ∀ i ∈ A P, GuruswamiSudan.HasOrderAt Qz (ωs i) (P.eval (ωs i)) m)
    (hcount : ∀ P ∈ Ps, (Qz.eval P).natDegree < m * (A P).card) :
    Ps.card ≤ Qz.natDegree := by
  exact GSFactorExtract.gs_list_size_le Qz hQz Ps (fun P hP =>
    matchingFactor_dvd_of_orderM_and_count ωs Qz P m (A P) (hord P hP) (hcount P hP))

/-- **Finite-family GS list-size bound from the weighted-degree Johnson budget.**

This is the common caller-facing form: the degree of every candidate is at most `k`, and the
Johnson count is discharged from the `(1,k)` weighted-degree bound on `Qz`. -/
theorem list_size_le_of_orderM_and_weightedDegree
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (hQz : Qz ≠ 0) (Ps : Finset F[X])
    (m k : ℕ) (A : F[X] → Finset (Fin n))
    (hPdeg : ∀ P ∈ Ps, P.natDegree ≤ k)
    (hord : ∀ P ∈ Ps, ∀ i ∈ A P, GuruswamiSudan.HasOrderAt Qz (ωs i) (P.eval (ωs i)) m)
    (hwcount : ∀ P ∈ Ps, Bivariate.natWeightedDegree Qz 1 k < m * (A P).card) :
    Ps.card ≤ Qz.natDegree := by
  exact GSFactorExtract.gs_list_size_le Qz hQz Ps (fun P hP =>
    matchingFactor_dvd_of_weightedDegree ωs Qz P m k (A P) (hPdeg P hP) (hord P hP)
      (hwcount P hP))

end MatchingExtractor

end ArkLib
