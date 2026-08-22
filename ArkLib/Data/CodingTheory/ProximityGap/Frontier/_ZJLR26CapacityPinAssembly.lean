/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZW17RecursivePeeling
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanDimension
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon.FRSGeomSubspaceDesign

/-!
# ZJLR26 capacity-pin assembly: [JLR26] 5.9 → 5.10 at the CZ25 capacity list bound (#334/#466)

**The named gap this closes.**  The in-tree [JLR26] (arXiv 2601.10047) folded-RS chain had two
disconnected halves: (i) the ABF26 T3.4 [CZ25 B.5] capacity `Λ`-bound for τ-subspace-design
codes, PROVEN conditional on the single deep residual `CZ25SpanBound'`
(`subspaceDesign_list_decoding_cz25`, `ListDecoding/Bounds/SubspaceDesign.lean`); and (ii) the
[JLR26] Lemma 5.10 recursive multi-curve peeling engine, PROVEN unconditionally with the
list-decodability input as an explicit integer-radius Finset hypothesis
(`ZW17RecursivePeeling.curveDecodable_of_listDecodable`,
`Frontier/_ZW17RecursivePeeling.lean`).  Nothing composed them: the missing piece was purely
mechanical — the `Λ` (ℕ∞ / `Set.ncard` / real-relative-radius) → Finset/integer-radius bridge
plus the floor arithmetic fitting the peeling radius `(ℓ+1)·⌊δn⌋` under the capacity radius
`(1 − τ(⌊1/η⌋) − η)·n`.  This file builds that bridge and lands the composition:

* `ball_finset_card_le_of_lambda_le` — **the Λ→Finset bridge** (unconditional): any Finset of
  codewords inside an integer-radius-`D` Hamming ball with `D ≤ δ'·n` injects into
  `closeCodewordsRel` at relative radius `δ'`, so a `Λ(C, δ') ≤ bound ≤ L` cap bounds its
  cardinality by `L`.
* `subspaceDesign_curveDecodable_capacity_of_spanBound` — **the [JLR26] 5.9→5.10 capacity
  composition** for EVERY τ-subspace-design code, conditional on the ONE named deep input
  `CZ25SpanBound'`: with `L ≥ (1 − τ(⌊1/η⌋))/η` (the CZ25 capacity list cap, `poly(1/η)` for
  the FRS profile) and the radius fit `(ℓ+1)·⌊δn⌋ ≤ (1 − τ(⌊1/η⌋) − η)·n`, the code is
  `(ℓ, δ, (t₂−1)·L + ℓ + 1, t₂)`-curve-decodable for every `t₂`, whenever `q > (L+1)·L·ℓ`.
  This strictly supersedes the crude `|F|^(r−1)` count of `_W17CurveDecodStitching.lean` on
  the subspace-design arm: the close-set threshold is now additive in the `poly(1/η)` list cap.
* `subspaceDesign_curveListSizeLe_capacity_of_spanBound` — the cover form: the same
  hypotheses give curve list-size `≤ L + ℓ` (`CurveListSizeLe`), feeding the in-tree one-level
  pigeonhole engine `curveDecodable_of_curveListSize`; the direct composition above is
  strictly sharper.
* `subspaceDesign_mca_capacity_of_spanBound` — **[JLR26] Lemma 5.10 instantiated at capacity,
  down to per-instance MCA** ([GG25] Theorem 3.3 tail, in-tree
  `all_seeds_relClose_of_curveDecodable`): for `t₂ > ℓ`, any tested stack whose close set
  reaches `(t₂−1)·L + ℓ + 1` seeds is explained by a SINGLE codeword curve within relative
  radius `(t₂/(t₂−ℓ))·δ` at EVERY seed.
* `cz25Tau` / `frs_cz25Design_of_admissible` / `frs_geomDomain_cz25Design` — the sharp CZ25
  capacity τ-profile `τ(r) = s·ρ/(s−r+1)` on `[s]` and the two in-tree T2.18 instantiations
  (admissible domain; canonical geometric domain — both unconditional theorems).
* `frs_curveDecodable_capacity_of_spanBound` / `frs_mca_capacity_of_spanBound` /
  `frs_geomDomain_curveDecodable_capacity_of_spanBound` — the folded-RS endpoints: for an
  admissible (resp. canonical geometric) folded-RS code, capacity curve-decodability and
  per-instance MCA conditional ONLY on `CZ25SpanBound'` at the sharp profile (all T2.18
  side conditions discharged by the landed unconditional bridges).

**Honest scope (read before citing).**
* Every theorem below is `sorry`-free and axiom-clean; the ONLY analytic conditional input is
  `CZ25SpanBound'` (`ListDecoding/CZ25SpanDimension.lean:257`) — the Guruswami–Wang
  agreement-budget / list-span theorem at capacity, [JLR26]'s Definition 5.9 input, equivalent
  in-tree to `CZ25DimensionCount` and implied by `CZ25CoordFiberCap`; its folded avatar is the
  named OPEN Prop `FrsCloseListSpanBound` (`Frontier/_FoldedPinBrick1.lean`).  It is consumed
  VISIBLY as the hypothesis `hSB` — never silently assumed.  The remaining parameter
  hypotheses (`hL`, `hrad`, `hq`) are concrete arithmetic side conditions, dischargeable at
  any instantiated parameter point.
* This lane is **FRS/subspace-design only** and does NOT touch the plain-RS prize core:
  `FoldingTransferNoGo.folding_transfer_no_go` proves folded agreement cannot transfer to the
  plain-RS δ* window, and for plain RS (`s = 1`) the needed list bound at the peeling radius
  IS the open list-size wall (`RSCurveListSizeResidual` / BCHKS Conjecture 1.12).
* What remains for the full [JLR26] Thm 5.12 / GG25 T4.14 folded capacity ε-pin after this
  file: (a) discharging `CZ25SpanBound'` itself (weeks-scale multivariate-interpolation
  formalization — the one genuinely new-mathematics item); (b) the T4.13 ε-packaging
  arithmetic (`gg25_subspaceDesign_epsMCA_residual`, `CapacityBoundsProofs.lean:193`) welding
  this file's MCA endpoint into the `ε_mca ≤ (t·n + 4t²)/|F|` budget shape via the T4.21
  pattern (`LineDecodingT421Faithful.lean` / `Frontier/_FoldedPinBrick3.lean`).

**Provenance.**  All inputs are imported from olean-backed in-tree modules; nothing is copied:
`subspaceDesign_list_decoding_cz25` + `CZ25SpanBound'` (ListDecoding),
`curveDecodable_of_listDecodable` + `curveListSizeLe_of_marked_listDecodable` +
`markedCurveDecodable_interpolation` (peeling/stitching),
`all_seeds_relClose_of_curveDecodable` (GG25 T3.3), `mem_closeCodewordsRel_iff_real`
(CZ25DesignToLambda), `frs_is_subspaceDesign_cz25Profile_of_admissible` +
`frs_geomDomain_isSubspaceDesign_cz25Profile` (T2.18 sharp profile).

## References
* [JLR26] Jeronimo–Liu–Rajpal, arXiv 2601.10047, §5 (Def 5.9, Lemma 5.10, Thm 5.12).
* [CZ25] Chen–Zhang; ABF26 Theorem 3.4 = CZ25 Theorem B.5 (capacity list bound).
* [GG25] Guo–Guruswami, ePrint 2025/2054, Thm 3.3 (curve-decodable ⟹ MCA).
* [GK16] Guruswami–Kopparty (FRS subspace-design, T2.18).
Issue #334 (Tier-3 folded pin), campaign #466.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.ZJLR26Assembly

open CodingTheory ListDecodable
open _root_.ProximityGap _root_.ProximityGap.GG25Lemma32
open ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The Λ → Finset integer-radius bridge -/

/-- **The Λ→Finset bridge (unconditional).**  A Finset `S` of codewords of `C` inside the
integer-radius-`D` Hamming ball around `y`, with `D ≤ δ'·n`, injects into the relative-radius
list `closeCodewordsRel C y δ'`; so a maximised-list cap `Λ(C, δ') ≤ bound ≤ L` bounds
`|S| ≤ L`.  This is the mechanical (ℕ∞ / `ncard` / real-radius) → (Finset / integer-radius)
conversion that lets the CZ25 capacity `Λ`-bound feed the ZW17 peeling engine's
list-decodability hypothesis. -/
theorem ball_finset_card_le_of_lambda_le
    {s : ℕ} (C : Submodule F (ι → Fin s → F)) {δ' bound : ℝ} {L D : ℕ}
    (hΛ : (Lambda ((C : Set (ι → Fin s → F))) δ' : ENNReal) ≤ ENNReal.ofReal bound)
    (hbound : bound ≤ (L : ℝ))
    (hD : (D : ℝ) ≤ δ' * Fintype.card ι)
    (y : ι → Fin s → F) (S : Finset (ι → Fin s → F))
    (hS : ∀ c ∈ S, c ∈ C ∧ hammingDist y c ≤ D) :
    S.card ≤ L := by
  classical
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  -- Step 1: `S` sits inside the relative-radius-`δ'` list around `y`.
  have hsub : (↑S : Set (ι → Fin s → F)) ⊆
      closeCodewordsRel ((C : Set (ι → Fin s → F))) y δ' := by
    intro c hc
    obtain ⟨hcC, hcd⟩ := hS c (Finset.mem_coe.mp hc)
    rw [mem_closeCodewordsRel_iff_real]
    refine ⟨hcC, ?_⟩
    have hcast : ((Code.relHammingDist y c : ℚ≥0) : ℝ)
        = (hammingDist y c : ℝ) / (Fintype.card ι : ℝ) := by
      simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
    rw [hcast, div_le_iff₀ hn_pos]
    calc (hammingDist y c : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcd
      _ ≤ δ' * Fintype.card ι := hD
  have hcard1 : S.card ≤ (closeCodewordsRel ((C : Set (ι → Fin s → F))) y δ').ncard := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  -- Step 2: the point list around `y` is dominated by the maximised `Λ`, hence by `L`.
  have hpoint : (((closeCodewordsRel ((C : Set (ι → Fin s → F))) y δ').ncard : ℕ∞))
      ≤ Lambda ((C : Set (ι → Fin s → F))) δ' := by
    unfold ListDecodable.Lambda
    exact le_iSup
      (fun g => (((closeCodewordsRel ((C : Set (ι → Fin s → F))) g δ').ncard : ℕ∞))) y
  have hchain :
      (((closeCodewordsRel ((C : Set (ι → Fin s → F))) y δ').ncard : ℕ) : ENNReal)
        ≤ ((L : ℕ) : ENNReal) := by
    calc (((closeCodewordsRel ((C : Set (ι → Fin s → F))) y δ').ncard : ℕ) : ENNReal)
        = ((((closeCodewordsRel ((C : Set (ι → Fin s → F))) y δ').ncard : ℕ∞)) :
            ENNReal) := by simp
      _ ≤ (Lambda ((C : Set (ι → Fin s → F))) δ' : ENNReal) := ENat.toENNReal_mono hpoint
      _ ≤ ENNReal.ofReal bound := hΛ
      _ ≤ ENNReal.ofReal (L : ℝ) := ENNReal.ofReal_le_ofReal hbound
      _ = ((L : ℕ) : ENNReal) := ENNReal.ofReal_natCast L
  have hncard : (closeCodewordsRel ((C : Set (ι → Fin s → F))) y δ').ncard ≤ L := by
    exact_mod_cast hchain
  exact le_trans hcard1 hncard

/-! ### The [JLR26] 5.9 → 5.10 capacity composition for τ-subspace-design codes -/

/-- **The capacity composition ([JLR26] Lemma 5.10 at the CZ25 list bound, design form).**
For a τ-subspace-design code `C` (ABF26 D2.16), conditional ONLY on the deep residual
`CZ25SpanBound'` (the Guruswami–Wang list-span input, [JLR26] Def 5.9): with

* `L ≥ (1 − τ(⌊1/η⌋))/η` — the CZ25 capacity list cap (T3.4), `poly(1/η)`;
* `(ℓ+1)·⌊δn⌋ ≤ (1 − τ(⌊1/η⌋) − η)·n` — the peeling radius fits under the capacity radius;
* `q > (L+1)·L·ℓ` — the field is large enough for the collision-free seed;

`C` is `(ℓ, δ, (t₂−1)·L + ℓ + 1, t₂)`-curve-decodable for EVERY `t₂`.  Proof: T3.4
(`subspaceDesign_list_decoding_cz25`, conditional on `hSB`) gives the `Λ`-cap at the capacity
radius; the Λ→Finset bridge converts it into the integer-radius list hypothesis; the ZW17
peeling engine (`curveDecodable_of_listDecodable`, with the [Jo26] Lemma 5.2 interpolation
stitching for free) concludes. -/
theorem subspaceDesign_curveDecodable_capacity_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s τ C h η hη)
    (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hL : (1 - τ (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - τ (Nat.floor (1 / η)) - η) * Fintype.card ι)
    (hq : (L + 1) * L * ℓ < Fintype.card F) (t₂ : ℕ) :
    CurveDecodable (F := F) ((C : Set (ι → Fin s → F))) ℓ δ ((t₂ - 1) * L + (ℓ + 1)) t₂ := by
  have hΛ := subspaceDesign_list_decoding_cz25 s τ C h η hη hSB
  refine curveDecodable_of_listDecodable C ℓ δ (L := L) ?_ hq t₂
  intro y S hS
  exact ball_finset_card_le_of_lambda_le C hΛ hL hrad y S hS

/-- **The cover form: capacity curve list-size `L + ℓ`.**  Same hypotheses, cover-shaped
conclusion `CurveListSizeLe C ℓ δ (L + ℓ)` (via the ZW17 peeled cover with the interpolation
stitching `a = t₁ = ℓ+1`), feeding the in-tree one-level pigeonhole engine
`curveDecodable_of_curveListSize`.  On the subspace-design arm this strictly supersedes the
crude `|F|^(r−1)` count of `_W17CurveDecodStitching.lean`; the direct composition
`subspaceDesign_curveDecodable_capacity_of_spanBound` is sharper still (additive threshold). -/
theorem subspaceDesign_curveListSizeLe_capacity_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s τ C h η hη)
    (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hL : (1 - τ (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - τ (Nat.floor (1 / η)) - η) * Fintype.card ι)
    (hq : (L + 1) * L * ℓ < Fintype.card F) :
    CurveListSizeLe (F := F) ((C : Set (ι → Fin s → F))) ℓ δ (L + ℓ) := by
  have hΛ := subspaceDesign_list_decoding_cz25 s τ C h η hη hSB
  have hcover := curveListSizeLe_of_marked_listDecodable C
    (markedCurveDecodable_interpolation C ℓ δ (le_refl (ℓ + 1)) (le_refl (ℓ + 1)))
    (Nat.lt_succ_self ℓ)
    (D := (ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)
    (by
      have h1 : ℓ + 1 - ℓ = 1 := by omega
      rw [h1, one_mul])
    (fun y S hS => ball_finset_card_le_of_lambda_le C hΛ hL hrad y S hS)
    hq
  rw [show L + (ℓ + 1 - 1) = L + ℓ from by omega] at hcover
  exact hcover

/-- **Per-instance MCA at capacity ([JLR26] Lemma 5.10 → [GG25] Theorem 3.3, design form).**
Under the same hypotheses, for any `t₂ > ℓ`: every tested stack `u` and codeword-valued `f`
whose close set reaches `(t₂−1)·L + ℓ + 1` seeds is explained by a SINGLE codeword curve
within relative Hamming radius `(t₂/(t₂−ℓ))·δ` at EVERY seed — the mutual-correlated-agreement
conclusion, at the capacity list cap `L ≈ (1−τ)/η = poly(1/η)`, in-tree for the first time. -/
theorem subspaceDesign_mca_capacity_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s τ C h η hη)
    (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hL : (1 - τ (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - τ (Nat.floor (1 / η)) - η) * Fintype.card ι)
    (hq : (L + 1) * L * ℓ < Fintype.card F)
    {t₂ : ℕ} (ht₂ : ℓ < t₂)
    {u : Fin (ℓ + 1) → ι → Fin s → F} {f : F → ι → Fin s → F}
    (hf : ∀ α, f α ∈ (C : Set (ι → Fin s → F)))
    (hclose : (t₂ - 1) * L + (ℓ + 1) ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → Fin s → F, (∀ j, cs j ∈ (C : Set (ι → Fin s → F))) ∧
      ∀ β : F, ((relHammingDist (comb u β) (comb cs β) : ℚ≥0) : ℝ≥0)
        ≤ ((t₂ : ℝ≥0) / ((t₂ - ℓ : ℕ) : ℝ≥0)) * δ :=
  all_seeds_relClose_of_curveDecodable ht₂
    (subspaceDesign_curveDecodable_capacity_of_spanBound s τ C h η hη hSB ℓ δ hL hrad hq t₂)
    hf hclose

/-! ### The folded-RS endpoints at the sharp CZ25 profile -/

/-- The sharp CZ25 capacity τ-profile for folded RS (`n` block positions, degree bound `k`,
folding `s`): `τ(r) = s·k/(n·(s − r + 1))` on `r ∈ [1, s]`, and `1` off `[1, s]`.  This is
exactly the profile of the T2.18 bridges `frs_is_subspaceDesign_cz25Profile_of_*` and of the
C3.5 capacity reduction; at `ρ = k/n` it reads `τ(r) = s·ρ/(s − r + 1)`. -/
noncomputable def cz25Tau (n k s : ℕ) : ℕ → ℝ := fun r ↦
  if r ∈ Finset.Icc 1 s then (s : ℝ) * (k : ℝ) / (n : ℝ) / ((s : ℝ) - (r : ℝ) + 1) else 1

/-- **T2.18 at the sharp profile, admissible-domain form** (wrapper of the landed
unconditional bridge `frs_is_subspaceDesign_cz25Profile_of_admissible`, restated against
`cz25Tau`). -/
theorem frs_cz25Design_of_admissible
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (P : Finset F) (hP_dom : ∀ i : ι, domain i ∈ P)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible P s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    IsSubspaceDesign s (cz25Tau (Fintype.card ι) k s)
      (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_cz25Profile_of_admissible domain k s ω P hP_dom hω0 hadm hkLs hkord

/-- **The folded-RS capacity curve-decodability endpoint (admissible domain).**  For an
admissible folded-RS code, curve-decodability at the capacity parameters, conditional ONLY on
`CZ25SpanBound'` at the sharp CZ25 profile — every other ingredient (T2.18, T3.4 packaging,
the 5.10 peeling, the Λ→Finset bridge) is a landed in-tree theorem. -/
theorem frs_curveDecodable_capacity_of_spanBound
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (P : Finset F) (hP_dom : ∀ i : ι, domain i ∈ P)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible P s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s (cz25Tau (Fintype.card ι) k s)
      (ReedSolomon.Folded.frsCode domain k s ω)
      (frs_cz25Design_of_admissible domain k s ω P hP_dom hω0 hadm hkLs hkord) η hη)
    (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hL : (1 - cz25Tau (Fintype.card ι) k s (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - cz25Tau (Fintype.card ι) k s (Nat.floor (1 / η)) - η) * Fintype.card ι)
    (hq : (L + 1) * L * ℓ < Fintype.card F) (t₂ : ℕ) :
    CurveDecodable (F := F)
      ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) ℓ δ
      ((t₂ - 1) * L + (ℓ + 1)) t₂ :=
  subspaceDesign_curveDecodable_capacity_of_spanBound s (cz25Tau (Fintype.card ι) k s)
    (ReedSolomon.Folded.frsCode domain k s ω)
    (frs_cz25Design_of_admissible domain k s ω P hP_dom hω0 hadm hkLs hkord)
    η hη hSB ℓ δ hL hrad hq t₂

/-- **The folded-RS per-instance MCA endpoint at capacity (admissible domain).**  The
[JLR26] 5.10-at-capacity MCA conclusion for folded RS, conditional ONLY on `CZ25SpanBound'`
at the sharp profile: for `t₂ > ℓ`, a close set of `(t₂−1)·L + ℓ + 1` seeds forces a single
folded-RS codeword curve within `(t₂/(t₂−ℓ))·δ` of the tested stack at every seed. -/
theorem frs_mca_capacity_of_spanBound
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (P : Finset F) (hP_dom : ∀ i : ι, domain i ∈ P)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible P s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s (cz25Tau (Fintype.card ι) k s)
      (ReedSolomon.Folded.frsCode domain k s ω)
      (frs_cz25Design_of_admissible domain k s ω P hP_dom hω0 hadm hkLs hkord) η hη)
    (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hL : (1 - cz25Tau (Fintype.card ι) k s (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - cz25Tau (Fintype.card ι) k s (Nat.floor (1 / η)) - η) * Fintype.card ι)
    (hq : (L + 1) * L * ℓ < Fintype.card F)
    {t₂ : ℕ} (ht₂ : ℓ < t₂)
    {u : Fin (ℓ + 1) → ι → Fin s → F} {f : F → ι → Fin s → F}
    (hf : ∀ α, f α ∈ (ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F)))
    (hclose : (t₂ - 1) * L + (ℓ + 1) ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → Fin s → F,
      (∀ j, cs j ∈ (ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) ∧
      ∀ β : F, ((relHammingDist (comb u β) (comb cs β) : ℚ≥0) : ℝ≥0)
        ≤ ((t₂ : ℝ≥0) / ((t₂ - ℓ : ℕ) : ℝ≥0)) * δ :=
  all_seeds_relClose_of_curveDecodable ht₂
    (frs_curveDecodable_capacity_of_spanBound domain k s ω P hP_dom hω0 hadm hkLs hkord
      η hη hSB ℓ δ hL hrad hq t₂)
    hf hclose

/-! ### The canonical geometric domain -/

/-- **T2.18 at the sharp profile on the canonical geometric domain** (wrapper of the landed
unconditional `frs_geomDomain_isSubspaceDesign_cz25Profile`, restated against `cz25Tau`). -/
theorem frs_geomDomain_cz25Design
    (γ : F) (k s n : ℕ)
    (hs : 0 < s) (hn : 0 < n) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ) :
    IsSubspaceDesign s (cz25Tau (Fintype.card (Fin n)) k s)
      (ReedSolomon.Folded.frsCode (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ) :=
  ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
    γ k s n hs hn hγ hsn hkLs hkord

/-- **The folded-RS capacity curve-decodability endpoint on the canonical geometric domain.**
Fully explicit domain `{γ^{s·i} : i ∈ Fin n}` with folding element `γ`; conditional ONLY on
`CZ25SpanBound'` at the sharp profile (all geometric/admissibility side conditions are landed
unconditional theorems). -/
theorem frs_geomDomain_curveDecodable_capacity_of_spanBound
    (γ : F) (k s n : ℕ) [Nonempty (Fin n)]
    (hs : 0 < s) (hn : 0 < n) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s (cz25Tau (Fintype.card (Fin n)) k s)
      (ReedSolomon.Folded.frsCode (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ)
      (frs_geomDomain_cz25Design γ k s n hs hn hγ hsn hkLs hkord) η hη)
    (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hL : (1 - cz25Tau (Fintype.card (Fin n)) k s (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((ℓ + 1) * ⌊δ * (Fintype.card (Fin n) : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - cz25Tau (Fintype.card (Fin n)) k s (Nat.floor (1 / η)) - η)
          * Fintype.card (Fin n))
    (hq : (L + 1) * L * ℓ < Fintype.card F) (t₂ : ℕ) :
    CurveDecodable (F := F)
      ((ReedSolomon.Folded.frsCode (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ :
        Set (Fin n → Fin s → F))) ℓ δ ((t₂ - 1) * L + (ℓ + 1)) t₂ :=
  subspaceDesign_curveDecodable_capacity_of_spanBound s (cz25Tau (Fintype.card (Fin n)) k s)
    (ReedSolomon.Folded.frsCode (ReedSolomon.Folded.geomDomainEmb γ s n hs hsn) k s γ)
    (frs_geomDomain_cz25Design γ k s n hs hn hγ hsn hkLs hkord)
    η hη hSB ℓ δ hL hrad hq t₂

end ArkLib.ProximityGap.Frontier.ZJLR26Assembly

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.ProximityGap.Frontier.ZJLR26Assembly.ball_finset_card_le_of_lambda_le
#print axioms
  ArkLib.ProximityGap.Frontier.ZJLR26Assembly.subspaceDesign_curveDecodable_capacity_of_spanBound
#print axioms
  ArkLib.ProximityGap.Frontier.ZJLR26Assembly.subspaceDesign_curveListSizeLe_capacity_of_spanBound
#print axioms
  ArkLib.ProximityGap.Frontier.ZJLR26Assembly.subspaceDesign_mca_capacity_of_spanBound
#print axioms ArkLib.ProximityGap.Frontier.ZJLR26Assembly.frs_cz25Design_of_admissible
#print axioms
  ArkLib.ProximityGap.Frontier.ZJLR26Assembly.frs_curveDecodable_capacity_of_spanBound
#print axioms ArkLib.ProximityGap.Frontier.ZJLR26Assembly.frs_mca_capacity_of_spanBound
#print axioms ArkLib.ProximityGap.Frontier.ZJLR26Assembly.frs_geomDomain_cz25Design
#print axioms
  ArkLib.ProximityGap.Frontier.ZJLR26Assembly.frs_geomDomain_curveDecodable_capacity_of_spanBound
