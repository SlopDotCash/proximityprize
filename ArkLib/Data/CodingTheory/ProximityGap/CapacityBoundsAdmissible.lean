/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ReedSolomon.AdmissibleSubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon.FRSGeomSubspaceDesign

/-!
# CapacityBounds wrappers from order-bounded FRS admissibility

This file keeps `CapacityBounds.lean` from growing further while exposing direct T4.14/GG25
front doors that compose the eta-route wrapper with the order/inter-orbit and order/coset
T2.18 front doors from `AdmissibleSubspaceDesign.lean`.
-/

namespace CodingTheory

section SubspaceDesignFRSAdmissible

/-- T4.14 eta-route wrapper from the order/inter-orbit T2.18 front door.

This specializes `frs_epsMCA_capacity_gg25_of_subspaceDesign_eta` with the
CZ25-profile folded-RS subspace-design instance supplied by
`frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter`. The remaining mathematical input is
the public GG25/T4.13 instance at that profile; the radius and bound arithmetic are handled by
the existing eta-route theorem. -/
theorem frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
          domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  let hT218 :=
    frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
      domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    hη_pos hη_lt hs_gt t ht hts hT218 hT413 hη htη

/-- Packaged `t ≤ 2 / η` T4.14 frontier from the order/inter-orbit T2.18 front door.

This exposes the residual package consumed by `frs_epsMCA_capacity_gg25_of_tle_frontier`, rather
than immediately closing the public Prop endpoint. -/
noncomputable def frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_inter_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
          domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25TLeFrontier domain k s ω η := by
  let hT218 :=
    frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
      domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord
  exact
    { hη_pos := hη_pos
      hη_lt := hη_lt
      hs_gt := hs_gt
      τ := fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1
      t := t
      ht := ht
      hT218 := hT218
      hT413 := hT413
      hRadius := frs_capacity_radius_eq_of_eta s k (Fintype.card ι) η t hts hη
      htη := htη }

/-- Raw-bound T4.14 frontier from the order/inter-orbit T2.18 front door.

This is the compatibility `FRSEpsMCACapacityGG25Frontier` view of
`frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_inter_eta`; the raw `hBound` field is
derived by the checked `FRSEpsMCACapacityGG25TLeFrontier.toFrontier` arithmetic bridge. -/
noncomputable def frs_epsMCA_capacity_gg25_frontier_of_orderOf_ge_of_inter_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
          domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25Frontier domain k s ω η :=
  (frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_inter_eta
    domain k s ω η hη_pos hη_lt hs_gt L hL_dom h0 hω0 hs_order hinter hkLs hkord
    t ht hts hT413 hη htη).toFrontier

/-- T4.14 eta-route wrapper from the order/coset-separation T2.18 front door.

This is the coset-separation companion to
`frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta`, using the fully packaged
`frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep` profile wrapper. -/
theorem frs_epsMCA_capacity_gg25_of_orderOf_ge_of_cosetSep_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
          domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  let hT218 :=
    frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
      domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    hη_pos hη_lt hs_gt t ht hts hT218 hT413 hη htη

/-- Packaged `t ≤ 2 / η` T4.14 frontier from the order/coset-separation T2.18 front door. -/
noncomputable def frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_cosetSep_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
          domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25TLeFrontier domain k s ω η := by
  let hT218 :=
    frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
      domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord
  exact
    { hη_pos := hη_pos
      hη_lt := hη_lt
      hs_gt := hs_gt
      τ := fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1
      t := t
      ht := ht
      hT218 := hT218
      hT413 := hT413
      hRadius := frs_capacity_radius_eq_of_eta s k (Fintype.card ι) η t hts hη
      htη := htη }

/-- Raw-bound T4.14 frontier from the order/coset-separation T2.18 front door.

This is the compatibility `FRSEpsMCACapacityGG25Frontier` view of
`frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_cosetSep_eta`; the raw `hBound` field is
derived by the checked `FRSEpsMCACapacityGG25TLeFrontier.toFrontier` arithmetic bridge. -/
noncomputable def frs_epsMCA_capacity_gg25_frontier_of_orderOf_ge_of_cosetSep_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
          domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25Frontier domain k s ω η :=
  (frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_cosetSep_eta
    domain k s ω η hη_pos hη_lt hs_gt L hL_dom h0 hω0 hs_order hcoset hkLs hkord
    t ht hts hT413 hη htη).toFrontier

/-- T4.14 eta-route wrapper on the canonical GR08 geometric folded-RS domain.

The T2.18/CZ25-profile input is discharged by
`ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile`; callers supply only the
T4.13 `subspaceDesign_epsMCA_gg25` instance at that profile and the usual paper choice of `t`
and `η`. -/
theorem frs_epsMCA_capacity_gg25_of_geomDomain_eta
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [NeZero n]
    (γ : F) (k s : ℕ)
    (hs : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (r : ℝ) + 1)
          else 1)
        (ReedSolomon.Folded.frsCode
          (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ)
        (ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
          γ k s n hs (Nat.pos_of_ne_zero (NeZero.ne n)) hγ hsn hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card (Fin n) + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25
      (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ
      η hη_pos hη_lt hs_gt := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let hT218 := ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
    γ k s n hs hn hγ hsn hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    (domain := ReedSolomon.Folded.geomDomainEmb γ s n hs hsn)
    (k := k) (s := s) (ω := γ) (η := η)
    hη_pos hη_lt hs_gt t ht hts hT218 hT413 hη htη

/-- Packaged `t ≤ 2 / η` T4.14 frontier on the canonical GR08 geometric folded-RS domain. -/
noncomputable def frs_epsMCA_capacity_gg25_tleFrontier_of_geomDomain_eta
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [NeZero n]
    (γ : F) (k s : ℕ)
    (hs : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (r : ℝ) + 1)
          else 1)
        (ReedSolomon.Folded.frsCode
          (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ)
        (ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
          γ k s n hs (Nat.pos_of_ne_zero (NeZero.ne n)) hγ hsn hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card (Fin n) + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25TLeFrontier
      (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ η := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let hT218 := ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
    γ k s n hs hn hγ hsn hkLs hkord
  exact
    { hη_pos := hη_pos
      hη_lt := hη_lt
      hs_gt := hs_gt
      τ := fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (r : ℝ) + 1)
      else 1
      t := t
      ht := ht
      hT218 := hT218
      hT413 := hT413
      hRadius := frs_capacity_radius_eq_of_eta s k (Fintype.card (Fin n)) η t hts hη
      htη := htη }

/-- Raw-bound T4.14 frontier on the canonical GR08 geometric folded-RS domain.

This is the compatibility `FRSEpsMCACapacityGG25Frontier` view of
`frs_epsMCA_capacity_gg25_tleFrontier_of_geomDomain_eta`; the raw `hBound` field is derived by
the checked `FRSEpsMCACapacityGG25TLeFrontier.toFrontier` arithmetic bridge. -/
noncomputable def frs_epsMCA_capacity_gg25_frontier_of_geomDomain_eta
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [NeZero n]
    (γ : F) (k s : ℕ)
    (hs : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (r : ℝ) + 1)
          else 1)
        (ReedSolomon.Folded.frsCode
          (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ)
        (ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
          γ k s n hs (Nat.pos_of_ne_zero (NeZero.ne n)) hγ hsn hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card (Fin n) + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25Frontier
      (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ η :=
  (frs_epsMCA_capacity_gg25_tleFrontier_of_geomDomain_eta
    (γ := γ) (k := k) (s := s) (n := n)
    hs hγ hsn hkLs hkord η hη_pos hη_lt hs_gt t ht hts hT413 hη htη).toFrontier

end SubspaceDesignFRSAdmissible

end CodingTheory

#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_inter_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_frontier_of_orderOf_ge_of_inter_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_of_orderOf_ge_of_cosetSep_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_cosetSep_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_frontier_of_orderOf_ge_of_cosetSep_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_of_geomDomain_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_tleFrontier_of_geomDomain_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_frontier_of_geomDomain_eta
