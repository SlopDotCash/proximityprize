/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.MDSIncidenceBound
import ArkLib.Data.CodingTheory.HigherOrderMDSFrame
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon

/-!
# Feeding the incidence bound from the MDS-frame tower (#389)

`MDSIncidenceBound.lean` proves the general dimension-`d` incidence list bound
`|Heavy| · C(k,d) ≤ C(n,d)` from an order-`d` MDS hypothesis stated as `det (N ∘ σ) ≠ 0` for every
injective `σ : Fin d → ι`.  This file connects that hypothesis to the repository's higher-order-MDS
tower: the predicate `ArkLib.HigherOrderMDS.IsMDSFrame` (every `≤ d` columns linearly independent)
discharges it directly, because `d` independent columns form a unit `d × d` matrix
(`Matrix.linearIndependent_rows_iff_isUnit` + `Matrix.isUnit_iff_isUnit_det`).

`mds_incidence_card_le_of_isMDSFrame` is the resulting drop-in, and
`reedSolomonFrame_incidence_card_le` specializes it to the explicit Vandermonde frame
`(1, Dᵢ, …, Dᵢ^{d-1})` at distinct points via `reedSolomonFrame_isMDS` — so the incidence list
bound holds for the actual Reed–Solomon frame object, with no extra hypothesis beyond distinctness.
Axiom-clean.
-/

open Finset Matrix ArkLib.HigherOrderMDS

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]

/-- An `IsMDSFrame` normal frame discharges the order-`d` MDS hypothesis of
`mds_incidence_card_le`: every `d` columns are independent, so the `d × d` minor is a unit. -/
theorem mds_incidence_card_le_of_isMDSFrame {d : ℕ} (N : ι → (Fin d → F))
    (hN : IsMDSFrame F N) (c : ι → F) {k : ℕ}
    (Heavy : Finset (Fin d → F))
    (hHeavy : ∀ p ∈ Heavy,
      k ≤ (univ.filter (fun i => N i ⬝ᵥ p = c i)).card) :
    Heavy.card * k.choose d ≤ (Fintype.card ι).choose d := by
  refine mds_incidence_card_le N c (fun σ hσ => ?_) Heavy hHeavy
  -- the d chosen columns are linearly independent (MDS), hence the matrix is a unit
  have hJcard : (Finset.image σ univ).card = d := by
    rw [Finset.card_image_of_injective _ hσ, Finset.card_univ, Fintype.card_fin]
  have hle : (Finset.image σ univ).card ≤ Module.finrank F (Fin d → F) := by
    rw [hJcard, Module.finrank_fin_fun]
  have hLIsub : LinearIndependent F (fun i : (Finset.image σ univ) => N i) := hN.2 _ hle
  have he : Function.Injective
      (fun b : Fin d => (⟨σ b, Finset.mem_image_of_mem σ (Finset.mem_univ b)⟩ :
        (Finset.image σ univ : Finset ι))) := by
    intro a b hab
    exact hσ (congrArg Subtype.val hab)
  have hLI : LinearIndependent F (fun b : Fin d => N (σ b)) := hLIsub.comp _ he
  have hUnit : IsUnit (Matrix.of (fun b => N (σ b)) : Matrix (Fin d) (Fin d) F) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hLI
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hUnit).ne_zero

/-- The explicit Reed–Solomon frame `(1, Dᵢ, …, Dᵢ^{d-1})` at distinct points feeds the incidence
list bound unconditionally (`reedSolomonFrame_isMDS`). -/
theorem reedSolomonFrame_incidence_card_le {d : ℕ} (D : ι → F) (hD : Function.Injective D)
    (hd : 2 ≤ d) (c : ι → F) {k : ℕ} (Heavy : Finset (Fin d → F))
    (hHeavy : ∀ p ∈ Heavy,
      k ≤ (univ.filter (fun i => reedSolomonFrame D d i ⬝ᵥ p = c i)).card) :
    Heavy.card * k.choose d ≤ (Fintype.card ι).choose d :=
  mds_incidence_card_le_of_isMDSFrame (reedSolomonFrame D d)
    (reedSolomonFrame_isMDS hD hd) c Heavy hHeavy
