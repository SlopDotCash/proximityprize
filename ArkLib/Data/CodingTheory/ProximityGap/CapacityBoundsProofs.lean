/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBoundsAdmissible
import ArkLib.Data.CodingTheory.ReedSolomon.AdmissibleSubspaceDesign

/-!
# Residual-obligation-backed proofs for CapacityBounds external Prop statements

This file packages the genuinely external paper results catalogued in `CapacityBounds.lean`.
Each paper theorem is represented as an explicit `Prop` residual, so downstream capstones can
depend on the obligation without installing it as a trusted Lean axiom.

## Covered issues

- **#84** (T4.11): GKL24 1.5-Johnson MCA + BGKS20 η-margin CA
- **#87** (T4.9.2): BCHKS25 RS epsCA in the δ_min/3-to-Johnson regime
- **#85** (T4.12): BCHKS25 Johnson-range RS epsMCA
- **#81** (T4.16): BCHKS25+KK25 near-capacity epsCA lower bound (construction)
- **#82** (T4.17): CS25 complete CA breakdown
- **#83** (T4.18): BCHKS25 Johnson-jump witness family
- **#86** (T4.13/T4.14): GG25 subspace-design MCA + FRS capacity MCA

## References

- [GKL24] Guruswami, Kopparty, Li.
- [BGKS20] Ben-Sasson, Goldberg, Kopparty, Saraf. Lemma 3.2.
- [BCHKS25] Ben-Sasson, Carmon, Haramaty, Kopparty, Sudan. Thm 1.3, Thm 4.6, Cor 1.7.
- [KK25] Kopparty, Kim.
- [CS25] Cheng, Sudan. Corollary 1.
- [GG25] Guruswami, Guo. Cor 4.9, Cor 4.10.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ENNReal
open ProximityGap

/-! ## §1 General linear codes (T4.11) — Issues #84 -/

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **[GKL24 Theorem 3]** residual ∛-radius / 1.5-Johnson MCA bound for general
linear codes. -/
def gkl24_cubeRoot_mca_bound_residual : Prop :=
  ∀ (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0),
    ∀ (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι),
    ∀ (hη : 0 < η) (hη_lt_δ_min : η < δ_min),
    ∀ (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))),
    linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

/-- **[BGKS20 Lemma 3.2]** residual η-margin fold/interleave CA bound in the
1.5-Johnson regime. -/
def bgks20_etaMargin_ca_bound_residual : Prop :=
  ∀ (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0),
    ∀ (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι),
    ∀ (hη : 0 < η) (hη_lt_δ_min : η < δ_min),
    ∀ (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))),
    linear_epsCA_1_5_johnson_bgks20 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

theorem linear_epsMCA_1_5_johnson_gkl24_proven
    (hGKL24 : gkl24_cubeRoot_mca_bound_residual (ι := ι) (F := F) (A := A))
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ :=
  hGKL24 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

theorem linear_epsCA_1_5_johnson_bgks20_proven
    (hBGKS20 : bgks20_etaMargin_ca_bound_residual (ι := ι) (F := F) (A := A))
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    linear_epsCA_1_5_johnson_bgks20 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ :=
  hBGKS20 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

end General

/-! ## §2 Reed-Solomon codes — Issues #87, #85, #81, #82, #83 -/

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **[BCHKS25 Theorem 1.3]** residual RS epsCA in the δ_min/3-to-Johnson regime
(T4.9.2, Issue #87). -/
def bchks25_rs_epsCA_item2_residual : Prop :=
  ∀ (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0),
    ∀ (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                  / Fintype.card ι / 3 ≤ δ_fld),
    ∀ (h_lt : δ_fld < δ_int),
    rs_epsCA_bchks25_item2 domain k δ_fld δ_int h_dmin h_lt

theorem rs_epsCA_bchks25_item2_proven
    (hBCHKS25 : bchks25_rs_epsCA_item2_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (h_lt : δ_fld < δ_int) :
    rs_epsCA_bchks25_item2 domain k δ_fld δ_int h_dmin h_lt :=
  hBCHKS25 domain k δ_fld δ_int h_dmin h_lt

/-- **[BCHKS25 Theorem 4.6]** residual Johnson-range RS epsMCA bound
(T4.12, Issue #85). -/
def bchks25_rs_epsMCA_johnson_range_residual : Prop :=
  ∀ (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0),
    ∀ (hη : 0 < η),
    ∀ (hδ : rs_epsMCA_johnson_range_condition domain k η δ),
    rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ

theorem rs_epsMCA_johnson_range_bchks25_proven
    (hBCHKS25 : bchks25_rs_epsMCA_johnson_range_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η)
    (hδ : rs_epsMCA_johnson_range_condition domain k η δ) :
    rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ :=
  hBCHKS25 domain k η δ hη hδ

/-- **[BCHKS25+KK25]** residual near-capacity epsCA lower bound construction
(T4.16, Issue #81). -/
def bchks25_kk25_rs_epsCA_lower_capacity_residual : Prop :=
  ∀ (c : ℝ≥0) (hc : 0 < c) (ρ : ℝ≥0)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < (1 / 2 : ℝ≥0)),
    rs_epsCA_lower_capacity_bchks25_kk25 c hc ρ hρ_pos hρ_lt

theorem rs_epsCA_lower_capacity_bchks25_kk25_proven
    (hBCHKS25_KK25 : bchks25_kk25_rs_epsCA_lower_capacity_residual)
    (c : ℝ≥0) (hc : 0 < c) (ρ : ℝ≥0) (hρ_pos : 0 < ρ) (hρ_lt : ρ < (1 / 2 : ℝ≥0)) :
    rs_epsCA_lower_capacity_bchks25_kk25 c hc ρ hρ_pos hρ_lt :=
  hBCHKS25_KK25 c hc ρ hρ_pos hρ_lt

/-- **[CS25 Corollary 1]** Complete CA breakdown (T4.17, Issue #82).
The hard ≥1 lower-bound half of ε_ca = 1 in the entropy band. -/
def cs25_rs_epsCA_breakdown_lower_residual : Prop :=
  ∀ (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0),
    ∀ (hq_ge : 10 ≤ Fintype.card F),
    ∀ (hδ_lo :
          1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
              + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                  / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
            ≤ (k : ℝ) / Fintype.card ι),
    ∀ (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)),
    rs_epsCA_breakdown_cs25_entropyBallLowerWitness domain k δ hq_ge hδ_lo hδ_hi

theorem rs_epsCA_breakdown_cs25_proven
    (hCS25 : cs25_rs_epsCA_breakdown_lower_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi :=
  rs_epsCA_breakdown_cs25_of_lower_bound domain k δ hq_ge hδ_lo hδ_hi
    (hCS25 domain k δ hq_ge hδ_lo hδ_hi)

/-- **[BCHKS25 Corollary 1.7]** residual Johnson-jump witness family
(T4.18, Issue #83). -/
def bchks25_rs_epsCA_johnson_jump_residual : Prop :=
  ∀ {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2],
    ∀ (ε : ℝ≥0) (hε : 0 < ε),
    rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε

theorem rs_epsCA_johnson_jump_bchks25_proven
    (hBCHKS25 : bchks25_rs_epsCA_johnson_jump_residual)
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (hε : 0 < ε) :
    rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε :=
  hBCHKS25 ε hε

end ReedSolomon

/-! ## §3 Subspace-design / FRS MCA (T4.13, T4.14) — Issue #86 -/

section SubspaceDesign

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **[GG25 Corollary 4.9]** residual τ-subspace-design MCA bound
(T4.13, Issue #86). -/
def gg25_subspaceDesign_epsMCA_residual : Prop :=
  ∀ (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)),
    ∀ (h : IsSubspaceDesign s τ C),
    ∀ (t : ℕ) (ht : 0 < t),
    subspaceDesign_epsMCA_gg25 s τ C h t ht

theorem subspaceDesign_epsMCA_gg25_proven
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F))
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (t : ℕ) (ht : 0 < t) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht :=
  hGG25 s τ C h t ht

/-- **T4.14 derived from T4.13 + the *proved* T2.18 instance — no independent T4.14 axiom.**

For a folded-RS code whose evaluation domain satisfies the explicit GK16 admissibility conditions
(`0 ∉ L`, `s ≤ orderOf ω`, inter-orbit separation, degree budgets), the FRS subspace-design
property (T2.18) is *proved* in-tree by
`frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter`. Combined with the GG25 subspace-design
MCA bound (T4.13, the `gg25_subspaceDesign_epsMCA_residual`) at the honest paper parameter choice
`η = τ_FRS(t+1) - ρ + 3/(2t)` with `t ≤ 2/η` and `t + 1 ≤ s`, the capstone
`frs_epsMCA_capacity_gg25_of_subspaceDesign_eta` (whose radius/bound arithmetic residuals are both
proved) yields folded-RS MCA-up-to-capacity statements under the explicit admissibility data.

This witnesses the checked part of T4.14 as a genuine corollary of **T4.13 alone** (T2.18 being now
proved for these admissible FRS front doors), without a standalone T4.14 axiom. -/
theorem frs_epsMCA_capacity_gg25_proven_of_t413
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  have hT218 := frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
    domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    domain k s ω η hη_pos hη_lt hs_gt t ht hts hT218
    (hGG25 s _ (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht)
    hη htη

/-- Coset-separation companion to `frs_epsMCA_capacity_gg25_proven_of_t413`.

This uses the fully packaged order/coset folded-RS T2.18 front door, so callers can instantiate
the T4.14-from-T4.13 proof supply from `0 ∉ L`, `s ≤ orderOf ω`, and the coset-separation
condition directly. -/
theorem frs_epsMCA_capacity_gg25_proven_of_t413_cosetSep
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  have hT218 := frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
    domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    domain k s ω η hη_pos hη_lt hs_gt t ht hts hT218
    (hGG25 s _ (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht)
    hη htη

/-- Canonical geometric-domain companion to `frs_epsMCA_capacity_gg25_proven_of_t413`.

This routes the GR08 folded-RS domain `i ↦ γ^(s*i)` through the proved geometric-domain
T2.18/CZ25-profile wrapper, then uses the GG25 T4.13 proof supply to derive the public
T4.14 capacity statement without the standalone T4.14 axiom. -/
theorem frs_epsMCA_capacity_gg25_proven_of_t413_geomDomain
    {n : ℕ} [NeZero n]
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := Fin n) (F := F))
    (γ : F) (k s : ℕ)
    (hs : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card (Fin n) + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25
      (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ
      η hη_pos hη_lt hs_gt := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let hT218 := ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
    γ k s n hs hn hγ hsn hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_geomDomain_eta
    (γ := γ) (k := k) (s := s) (n := n)
    hs hγ hsn hkLs hkord η hη_pos hη_lt hs_gt t ht hts
    (hGG25 s _
      (ReedSolomon.Folded.frsCode
        (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ)
      hT218 t ht)
    hη htη

/-- T4.13-backed `t ≤ 2 / η` frontier for the order/inter-orbit FRS route.

This packages the same proof supply as `frs_epsMCA_capacity_gg25_proven_of_t413`, but returns the
frontier object consumed by `frs_epsMCA_capacity_gg25_of_tle_frontier` instead of immediately
closing the public Prop endpoint. -/
noncomputable def frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25TLeFrontier domain k s ω η := by
  let hT218 := frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
    domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord
  exact frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_inter_eta
    domain k s ω η hη_pos hη_lt hs_gt L hL_dom h0 hω0 hs_order hinter hkLs hkord
    t ht hts
    (hGG25 s _
      (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht)
    hη htη

/-- Coset-separation companion to
`frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413`. -/
noncomputable def frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_cosetSep
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25TLeFrontier domain k s ω η := by
  let hT218 := frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
    domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord
  exact frs_epsMCA_capacity_gg25_tleFrontier_of_orderOf_ge_of_cosetSep_eta
    domain k s ω η hη_pos hη_lt hs_gt L hL_dom h0 hω0 hs_order hcoset hkLs hkord
    t ht hts
    (hGG25 s _
      (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht)
    hη htη

/-- Canonical geometric-domain T4.13-backed `t ≤ 2 / η` frontier. -/
noncomputable def frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_geomDomain
    {n : ℕ} [NeZero n]
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := Fin n) (F := F))
    (γ : F) (k s : ℕ)
    (hs : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card (Fin n) + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25TLeFrontier
      (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ η := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let hT218 := ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
    γ k s n hs hn hγ hsn hkLs hkord
  exact frs_epsMCA_capacity_gg25_tleFrontier_of_geomDomain_eta
    (γ := γ) (k := k) (s := s) (n := n)
    hs hγ hsn hkLs hkord η hη_pos hη_lt hs_gt t ht hts
    (hGG25 s _
      (ReedSolomon.Folded.frsCode
        (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ)
      hT218 t ht)
    hη htη

/-- T4.13-backed raw-bound frontier for the order/inter-orbit FRS route.

This is the older `FRSEpsMCACapacityGG25Frontier` API, obtained from the honest
`t ≤ 2 / η` frontier by the checked arithmetic conversion
`FRSEpsMCACapacityGG25TLeFrontier.toFrontier`. -/
noncomputable def frs_epsMCA_capacity_gg25_frontier_proven_of_t413
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25Frontier domain k s ω η :=
  (frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413
    hGG25 domain k s ω η hη_pos hη_lt hs_gt t ht hts
    L hL_dom h0 hω0 hs_order hinter hkLs hkord hη htη).toFrontier

/-- Coset-separation companion to
`frs_epsMCA_capacity_gg25_frontier_proven_of_t413`. -/
noncomputable def frs_epsMCA_capacity_gg25_frontier_proven_of_t413_cosetSep
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F))
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25Frontier domain k s ω η :=
  (frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_cosetSep
    hGG25 domain k s ω η hη_pos hη_lt hs_gt t ht hts
    L hL_dom h0 hω0 hs_order hcoset hkLs hkord hη htη).toFrontier

/-- Canonical geometric-domain T4.13-backed raw-bound frontier. -/
noncomputable def frs_epsMCA_capacity_gg25_frontier_proven_of_t413_geomDomain
    {n : ℕ} [NeZero n]
    (hGG25 : gg25_subspaceDesign_epsMCA_residual (ι := Fin n) (F := F))
    (γ : F) (k s : ℕ)
    (hs : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1) (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card (Fin n) + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    FRSEpsMCACapacityGG25Frontier
      (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ η :=
  (frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_geomDomain
    hGG25 (n := n) γ k s hs hγ hsn hkLs hkord η hη_pos hη_lt hs_gt
    t ht hts hη htη).toFrontier

end SubspaceDesign

#print axioms CodingTheory.linear_epsMCA_1_5_johnson_gkl24_proven
#print axioms CodingTheory.linear_epsCA_1_5_johnson_bgks20_proven
#print axioms CodingTheory.rs_epsCA_bchks25_item2_proven
#print axioms CodingTheory.rs_epsMCA_johnson_range_bchks25_proven
#print axioms CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25_proven
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_proven
#print axioms CodingTheory.rs_epsCA_johnson_jump_bchks25_proven
#print axioms CodingTheory.subspaceDesign_epsMCA_gg25_proven
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_proven_of_t413
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_proven_of_t413_cosetSep
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_proven_of_t413_geomDomain
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_cosetSep
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_tleFrontier_proven_of_t413_geomDomain
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_frontier_proven_of_t413
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_frontier_proven_of_t413_cosetSep
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_frontier_proven_of_t413_geomDomain

end CodingTheory
