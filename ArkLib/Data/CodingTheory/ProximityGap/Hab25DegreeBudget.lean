/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Hab25 GS-interpolant degree budget (hYbound) (issue #68)

card_natDegreePos_normalizedFactors_le_natDegree + gsInterp_card_natDegreePos_factors_le_natDegreeY:
the count of positive-Y-degree distinct factors of the GS interpolant is bounded by natDegreeY,
from pure mathlib UFM/normalizedFactors. Discharges the S3 degree-budget field of Hab25JohnsonResiduals.
-/

open Polynomial UniqueFactorizationMonoid Finset

namespace Issue68Hab25

/-! ## The abstract separability-free degree count (non-field coefficient ring) -/

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
  [UniqueFactorizationMonoid (Polynomial R)] [NormalizationMonoid (Polynomial R)]

/-- **S3/S4 abstract core (proven).** Separability-free: over a (possibly non-field) integral
domain `R`, the number of *distinct positive-degree* normalized factors of a nonzero polynomial
`p : R[X]` is at most `p.natDegree`.  The degree-0 (content) factors are discarded by the filter,
so — unlike the field case — no separability and no field hypothesis is needed. -/
theorem card_natDegreePos_normalizedFactors_le_natDegree
    (p : Polynomial R) (hp0 : p ≠ 0) :
    #(((normalizedFactors p).toFinset).filter (fun q => 0 < q.natDegree))
      ≤ p.natDegree := by
  classical
  set s : Multiset (Polynomial R) := normalizedFactors p with hs
  have hs0 : (0 : Polynomial R) ∉ s := by
    simpa [hs] using (UniqueFactorizationMonoid.zero_notMem_normalizedFactors p)
  -- The positive-degree sub-multiset, and the goal-finset rewritten as its `toFinset`.
  set sPos : Multiset (Polynomial R) := s.filter (fun q => 0 < q.natDegree) with hsPos
  have hfin_eq :
      ((normalizedFactors p).toFinset).filter (fun q => 0 < q.natDegree) = sPos.toFinset := by
    rw [hsPos]
    -- `Multiset.toFinset_filter : (s.filter P).toFinset = s.toFinset.filter P`
    rw [Multiset.toFinset_filter, hs]
  rw [hfin_eq]
  -- (1) `#sPos.toFinset ≤ sPos.card`.
  have h1 : sPos.toFinset.card ≤ sPos.card := Multiset.toFinset_card_le sPos
  -- (2) every factor in `sPos` has `1 ≤ natDegree`, so `sPos.card ≤ (sPos.map natDegree).sum`.
  have hmem : ∀ x ∈ sPos.map Polynomial.natDegree, 1 ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
    rw [hsPos] at hq
    exact (Multiset.mem_filter.mp hq).2
  have h2 : sPos.card ≤ (sPos.map Polynomial.natDegree).sum := by
    have key := Multiset.card_nsmul_le_sum hmem
    simpa [Multiset.card_map, smul_eq_mul, mul_one] using key
  -- (3) the positive-degree degree-sum is ≤ the full degree-sum (content factors add ≥ 0).
  have hsplit :
      (s.map Polynomial.natDegree).sum
        = (sPos.map Polynomial.natDegree).sum
          + ((s.filter (fun q => ¬ 0 < q.natDegree)).map Polynomial.natDegree).sum := by
    conv_lhs => rw [← Multiset.filter_add_not (fun q => 0 < q.natDegree) s]
    rw [Multiset.map_add, Multiset.sum_add, hsPos]
  have h3 : (sPos.map Polynomial.natDegree).sum ≤ (s.map Polynomial.natDegree).sum := by
    rw [hsplit]; exact Nat.le_add_right _ _
  -- (4) the full degree-sum equals `p.natDegree`.
  have hsum_eq : (s.map Polynomial.natDegree).sum = p.natDegree := by
    have hprod : s.prod.natDegree = (s.map Polynomial.natDegree).sum :=
      Polynomial.natDegree_multiset_prod (t := s) hs0
    have hassoc : Associated s.prod p := by
      simpa [hs] using (UniqueFactorizationMonoid.prod_normalizedFactors (a := p) hp0)
    have hdeg : s.prod.natDegree = p.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hassoc)
    rw [← hprod, hdeg]
  -- Chain.
  calc sPos.toFinset.card
      ≤ sPos.card := h1
    _ ≤ (sPos.map Polynomial.natDegree).sum := h2
    _ ≤ (s.map Polynomial.natDegree).sum := h3
    _ = p.natDegree := hsum_eq

/-- Degree-budget corollary (the direct `hYbound` shape): if an external construction bounds
`p.natDegree` by `ℓ`, then the number of distinct positive-degree factors is bounded by `ℓ`. -/
theorem card_natDegreePos_normalizedFactors_le_of_natDegree_le
    (p : Polynomial R) (hp0 : p ≠ 0) {ℓ : ℕ} (hp : p.natDegree ≤ ℓ) :
    #(((normalizedFactors p).toFinset).filter (fun q => 0 < q.natDegree)) ≤ ℓ :=
  (card_natDegreePos_normalizedFactors_le_natDegree p hp0).trans hp

/-! ## Specialisation to the GS interpolant `Q : F[Z][X][Y]`

The factor type is `F[Z][X][Y] = (F[Z][X])[Y]`.  Here the base ring of the outer polynomial is
`R := F[Z][X] = Polynomial (Polynomial F)`, an integral domain (`F` a field).  Plugging `p := Q`
and rewriting `Q.natDegree = Bivariate.natDegreeY Q = Trivariate.D_Y Q` gives the S3/S4 `D_Y`
bound. -/

section GS

variable {F : Type*} [Field F] [DecidableEq F]

/-- Local mirror of `Polynomial.Bivariate.natDegreeY` from CompPoly
(`CompPoly/ToMathlib/Polynomial/BivariateDegree.lean:62`), reproduced verbatim
(`natDegreeY f := Polynomial.natDegree f`) so the GS specialisation compiles under bare
`import Mathlib` (the scratch file does not import CompPoly).  Definitionally identical, so the
`D_Y`/`natDegreeY` vocabulary and the `rfl` bridge below transfer unchanged. -/
noncomputable def Polynomial.Bivariate.natDegreeY {F : Type*} [Field F]
    (f : Polynomial (Polynomial (Polynomial F))) : ℕ :=
  Polynomial.natDegree f

/-- `Bivariate.natDegreeY` is definitionally the outer `Polynomial.natDegree`; kept explicit so the
specialisation reads in the `D_Y`/`natDegreeY` vocabulary of the GS development. -/
theorem natDegreeY_eq_natDegree (Q : Polynomial (Polynomial (Polynomial F))) :
    Polynomial.Bivariate.natDegreeY Q = Q.natDegree := rfl

/-- **S3/S4 GS specialisation (proven, modulo only `Q ≠ 0`).** The number of distinct
positive-`Y`-degree irreducible factors of a nonzero GS interpolant `Q : F[Z][X][Y]` is at most
`Bivariate.natDegreeY Q` (`= Trivariate.D_Y Q`).  This is the `hYbound` count `Index.card ≤ ℓ`
with `ℓ = D_Y Q`, DERIVED (not assumed) from the elementary degree count.

`Q ≠ 0` is supplied in the GS substrate by `ModifiedGuruswami.Q_ne_0`. -/
theorem gsInterp_card_natDegreePos_factors_le_natDegreeY
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ0 : Q ≠ 0) :
    #(((normalizedFactors Q).toFinset).filter (fun q => 0 < q.natDegree))
      ≤ Polynomial.Bivariate.natDegreeY Q := by
  rw [natDegreeY_eq_natDegree]
  exact card_natDegreePos_normalizedFactors_le_natDegree Q hQ0

/-- The S3/S4 factor index set: the distinct positive-`Y`-degree irreducible factors of the GS
interpolant `Q`, as a concrete `Finset` over the factor type `F[Z][X][Y]`. -/
noncomputable def gsFactorIndex
    (Q : Polynomial (Polynomial (Polynomial F))) :
    Finset (Polynomial (Polynomial (Polynomial F))) :=
  ((normalizedFactors Q).toFinset).filter (fun q => 0 < q.natDegree)

/-- **`hYbound` discharged (proven).** With the concrete index set `gsFactorIndex Q` and
`ℓ := Bivariate.natDegreeY Q = D_Y Q`, the residual
`Hab25JohnsonAlgebraicData.hYbound : Index.card ≤ ℓ` holds. -/
theorem gsFactorIndex_card_le_natDegreeY
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ0 : Q ≠ 0) :
    (gsFactorIndex Q).card ≤ Polynomial.Bivariate.natDegreeY Q :=
  gsInterp_card_natDegreePos_factors_le_natDegreeY Q hQ0

end GS

end Issue68Hab25
