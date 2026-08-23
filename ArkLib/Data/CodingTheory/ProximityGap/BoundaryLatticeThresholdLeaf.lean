/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Field.ZMod
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidual

/-!
# The lattice leaf of the corrected boundary route: quantitative threshold + §5 extraction

The corrected boundary obligation (O76/O78) carries the §5 probability threshold at a
floor-matched strict radius `δ' < δ = 1 − √ρ`.  At a **lattice** endpoint (`deg·n` a perfect
square, so `δ·n` is integral) no floor-matched strict radius exists
(`ArkLib.BoundaryCardResidual.not_exists_lt_floor_eq_of_lattice`), and the §5-form threshold
`Pr > k · errorBound δ` is vacuous there (`errorBound = 0` at the boundary,
`ArkLib.BoundaryDischarge.errorBound_eq_zero_at_boundary`): the in-tree threshold-to-cardinality
conversion (`ProximityGap.goodCoeffsCurve_card_bounds_of_prob_threshold`) has unsatisfiable side
conditions at the boundary, since they require `k ≤ k · errorBound · |F| = 0`.

This file supplies the lattice leaf's honest replacement: the **field-quantitative threshold**

  `Pr[curve δ-close] > k · (n+1)/|F|`   (`latticeThresholdEps`),

which stays positive at the boundary, converts unconditionally into the two cardinality bounds
the assembly bridge consumes (`card_gt_of_prob_gt_latticeThreshold`), and reduces the refuted
three-input lattice package (`BoundaryCardLatticeData`: two cardinality bounds + extraction) to
the **single** §5 coefficient-polynomial extraction residual:

* `jointAgreement_of_latticeThreshold_of_coeffPolys` — per stack: quantitative threshold +
  extraction ⟹ `jointAgreement`, at every radius `δ` (in particular the exact lattice endpoint).
* `LatticeCoeffPolyExtraction` — the extraction-only residual surface (the genuine open core:
  BCIKS20 §5 list-decoding at the endpoint).
* `correlatedAgreementCurves_of_latticeExtraction` — consumer shape: the extraction supply alone
  yields `δ_ε_correlatedAgreementCurves` with `ε = (n+1)/|F|`.
* `BoundaryCardLatticeThresholdResidual` + `boundaryCardLatticeThresholdResidual_of_extraction`
  — the corrected lattice-leaf surface (mirroring the *refuted* nonemptiness surface
  `BoundaryCardLatticeResidual` with the quantitative threshold in place of nonemptiness), and
  its reduction to extraction only.

**The extraction hypothesis cannot be dropped.**  The falsify-first probe
(`scripts/probes/probe_boundary_lattice_threshold.py`, 4 lattice endpoints: `q=11/17, n=8,
deg=2, k=1`; `q=11, n=9, deg=1, k=1`; `q=29, n=8, deg=2, k=2`) found a stack over
`GF(11)`, `n=8`, `deg=2`, `k=1` with good-set cardinality `10 > 9 = (n+1)k` and **no**
`jointAgreement` (the per-z decoding lists admit a choice `P` with no coefficient polynomial
`B`, exhaustively checked) — so the quantitative threshold *alone* is false as a lattice-leaf
hypothesis.  The composite (threshold + extraction) survived all 4 points with 0 violations.

The witness namespace instantiates the per-stack theorem end-to-end at a genuine lattice
endpoint (`ZMod 11`, `n = 8`, `deg = 2`, `deg·n = 16 = 4²`, `δ·n = 4` integral): the zero stack
satisfies the quantitative threshold (`Pr = 1 > 9/11`) and the extraction (every admissible
per-`z` decoding is forced to `P z = 0`: a polynomial of `natDegree < 2` vanishing on `≥ 4` of
the `8` distinct evaluation points is zero), so the hypothesis spine is simultaneously
satisfiable — no statement here hides behind an unsatisfiable assumption.  (The witness
conclusion is of course trivially true for the zero stack; the witness certifies
satisfiability, not new boundary mathematics.)

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (list-decoding agreement chain), §6.2 (closed Johnson boundary at `1 − √ρ`).
-/

namespace ArkLib

namespace BoundaryLatticeThresholdLeaf

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The field-quantitative lattice threshold** `ε = (n+1)/|F|`.  Unlike `errorBound`, this
stays strictly positive at the closed Johnson boundary, so the lattice endpoint — where
`errorBound = 0` makes the §5-form threshold vacuous and no floor-matched strict sub-radius
exists — retains a non-vacuous probability hypothesis. -/
noncomputable def latticeThresholdEps (ι F : Type) [Fintype ι] [Fintype F] : ℝ≥0 :=
  ((Fintype.card ι + 1 : ℕ) : ℝ≥0) / ((Fintype.card F : ℕ) : ℝ≥0)

omit [Nonempty ι] [DecidableEq F] in
/-- The lattice threshold is strictly positive — in contrast with the boundary-degenerate
`errorBound (1 − √ρ) = 0`. -/
theorem latticeThresholdEps_pos : 0 < latticeThresholdEps ι F := by
  refine div_pos ?_ ?_
  · exact_mod_cast Nat.succ_pos (Fintype.card ι)
  · exact_mod_cast Fintype.card_pos (α := F)

omit [Nonempty ι] in
/-- **Quantitative threshold ⟹ the assembly cardinality bound, unconditionally.**  If the
probability that a random parameter places the curve `δ`-close to the code exceeds
`k · (n+1)/|F|`, then the good-coefficient set has more than `(n+1)·k` elements.  This replaces
the in-tree `goodCoeffsCurve_card_bounds_of_prob_threshold`, whose `errorBound`-side conditions
are unsatisfiable at the boundary. -/
theorem card_gt_of_prob_gt_latticeThreshold {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob : Pr_{let r ← $ᵖ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ ]
      > k * latticeThresholdEps ι F) :
    (Fintype.card ι + 1) * k
      < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card := by
  classical
  have hq0 : ((Fintype.card F : ℕ) : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  have hprob' : Pr_{let r ← $ᵖ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i,
      (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ ]
      > (((k : ℝ≥0) * latticeThresholdEps ι F : ℝ≥0) : ENNReal) := by
    simpa [ENNReal.coe_mul, ENNReal.coe_natCast] using hprob
  have h := ProximityGap.goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (η := (k : ℝ≥0) * latticeThresholdEps ι F) u hprob'
  have hηq : ((k : ℝ≥0) * latticeThresholdEps ι F) * ((Fintype.card F : ℕ) : ℝ≥0)
      = (((Fintype.card ι + 1) * k : ℕ) : ℝ≥0) := by
    unfold latticeThresholdEps
    rw [mul_assoc, div_mul_cancel₀ _ hq0]
    push_cast
    ring
  have h2 : (((Fintype.card ι + 1) * k : ℕ) : ENNReal)
      < ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) := by
    calc (((Fintype.card ι + 1) * k : ℕ) : ENNReal)
        = ((((k : ℝ≥0) * latticeThresholdEps ι F) * ((Fintype.card F : ℕ) : ℝ≥0) :
            ℝ≥0) : ENNReal) := by
          rw [hηq]; exact (ENNReal.coe_natCast _).symm
      _ = (((k : ℝ≥0) * latticeThresholdEps ι F : ℝ≥0) : ENNReal) *
            ((Fintype.card F : ℕ) : ENNReal) := by
          rw [ENNReal.coe_mul, ENNReal.coe_natCast]
      _ < _ := h
  exact_mod_cast h2

/-- **The lattice leaf, per stack: quantitative threshold + §5 extraction ⟹
`jointAgreement`.**  Holds at *every* radius `δ`; at the exact lattice boundary endpoint it is
the only non-vacuous threshold route (no floor-matched strict sub-radius exists and
`errorBound = 0`).  Together with the threshold conversion above, this reduces the refuted
three-input `BoundaryCardLatticeData` to the single extraction input.  The extraction
hypothesis is load-bearing: see the probe counterexample recorded in the module docstring. -/
theorem jointAgreement_of_latticeThreshold_of_coeffPolys {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg] (hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι)
    (hprob : Pr_{let r ← $ᵖ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ ]
      > k * latticeThresholdEps ι F)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  have hcard := card_gt_of_prob_gt_latticeThreshold (k := k) (deg := deg)
    (domain := domain) (δ := δ) u hprob
  refine ProximityGap.goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core
    (deg := deg) (domain := domain) (δ := δ) hk ?_ ?_ hcoeffPoly
  · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left k (Nat.succ_pos (Fintype.card ι))) hcard
  · exact Nat.le_of_lt hcard

omit [Nonempty ι] in
/-- **The extraction-only residual surface.**  The §5 coefficient-polynomial extraction for
every stack whose good set exceeds the quantitative threshold count.  After this file, the
lattice leaf of the corrected boundary route rests on *this* alone — the genuine BCIKS20 §5
list-decoding content at the endpoint — instead of the three-input `BoundaryCardLatticeData`. -/
def LatticeCoeffPolyExtraction {k deg : ℕ} (domain : ι ↪ F) (δ : ℝ≥0) : Prop :=
  ∀ u : WordStack F (Fin (k + 1)) ι,
    (Fintype.card ι + 1) * k
        < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z

/-- **Consumer shape: extraction supply ⟹ curve correlated agreement with
`ε = (n+1)/|F|`.**  At any radius — in particular at a lattice boundary endpoint, where this is
the honest replacement for the refuted nonemptiness export and for the vacuous
`ε = errorBound (1 − √ρ) = 0`. -/
theorem correlatedAgreementCurves_of_latticeExtraction {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg] (hk : 0 < k)
    (hExt : LatticeCoeffPolyExtraction (k := k) (deg := deg) (domain := domain) δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := latticeThresholdEps ι F) := by
  intro u hprob
  exact jointAgreement_of_latticeThreshold_of_coeffPolys hk u hprob
    (hExt u (card_gt_of_prob_gt_latticeThreshold u hprob))

omit [Nonempty ι] in
/-- **The corrected lattice-leaf surface.**  Mirrors the *refuted* nonemptiness surface
`ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual`, with the bare `0 < card` hypothesis
replaced by the quantitative threshold `Pr > k · (n+1)/|F|` — the correction the
strict-interior refutation (O76) mandates, specialized to the lattice endpoint where the
floor-matched strict-radius route is provably unavailable. -/
def BoundaryCardLatticeThresholdResidual {k deg : ℕ} (domain : ι ↪ F) (δ : ℝ≥0) : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    δ = 1 - ReedSolomon.sqrtRate deg domain →
    (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι →
    Pr_{let r ← $ᵖ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ ]
      > k * latticeThresholdEps ι F →
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)

/-- The corrected lattice leaf reduces to the extraction residual alone. -/
theorem boundaryCardLatticeThresholdResidual_of_extraction {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg]
    (hExt : LatticeCoeffPolyExtraction (k := k) (deg := deg) (domain := domain) δ) :
    BoundaryCardLatticeThresholdResidual (k := k) (deg := deg) (domain := domain) δ :=
  fun hk u _ _ hprob =>
    jointAgreement_of_latticeThreshold_of_coeffPolys hk u hprob
      (hExt u (card_gt_of_prob_gt_latticeThreshold u hprob))

/-!
### Next reduction layer: the canonical-family form of the lattice extraction

`LatticeCoeffPolyExtraction` quantifies over *every* decoded family `P`.  What BCIKS20 §5
actually supplies at the endpoint is more structured: ONE canonical decoded family `P₀` (the
GS-factor roots), coefficient-polynomial witnesses for it, and uniqueness of decoding on the
good set.  `LatticeCanonicalCoeffPolyExtraction` is that canonical surface — the exact lattice
mirror of `ProximityGap.StrictCanonicalCoeffPolysResidual` (`BCIKS20/Curves.lean`) with the
strict-Johnson window hypotheses replaced by the quantitative count threshold
`(n+1)·k < card` — and `latticeCoeffPolyExtraction_of_canonical` discharges the all-families
residual from it via the (radius-generic, proven) canonical-agreement transport
`coeff_polys_for_all_decoded_of_canonical_agreement`.

This is a reduction layer, not a closure: the canonical Prop is still open (its content is
BCIKS20 §5 list-decoding at the exact endpoint — same open core as
`StrictCanonicalCoeffPolysResidual`, with the strict-radius slack no longer available). -/

omit [Nonempty ι] in
/-- **Canonical-family form of the lattice extraction residual.**  For every stack over the
quantitative count threshold there is one decoded family `P₀` carrying coefficient-polynomial
witnesses and unique among decoded families on the good set. -/
def LatticeCanonicalCoeffPolyExtraction {k deg : ℕ} (domain : ι ↪ F) (δ : ℝ≥0) : Prop :=
  ∀ u : WordStack F (Fin (k + 1)) ι,
    (Fintype.card ι + 1) * k
        < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    ∃ P₀ : F → Polynomial F,
      (∃ B : ℕ → Polynomial F,
        (∀ j < deg, (B j).natDegree < k + 1) ∧
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            P z = P₀ z

omit [Nonempty ι] in
/-- **The reduction.**  The canonical-family form discharges the all-families extraction
residual, by the proven canonical-agreement transport. -/
theorem latticeCoeffPolyExtraction_of_canonical {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hCanon :
      LatticeCanonicalCoeffPolyExtraction (k := k) (deg := deg) (domain := domain) δ) :
    LatticeCoeffPolyExtraction (k := k) (deg := deg) (domain := domain) δ := by
  intro u hcard P hP
  obtain ⟨P₀, hCoeff₀, huniq⟩ := hCanon u hcard
  exact coeff_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hCoeff₀ huniq P hP

/-- The corrected lattice leaf from the canonical-family residual alone. -/
theorem boundaryCardLatticeThresholdResidual_of_canonical {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg]
    (hCanon :
      LatticeCanonicalCoeffPolyExtraction (k := k) (deg := deg) (domain := domain) δ) :
    BoundaryCardLatticeThresholdResidual (k := k) (deg := deg) (domain := domain) δ :=
  boundaryCardLatticeThresholdResidual_of_extraction
    (latticeCoeffPolyExtraction_of_canonical hCanon)

/-- Consumer shape from the canonical-family residual: curve correlated agreement with
`ε = (n+1)/|F|`. -/
theorem correlatedAgreementCurves_of_latticeCanonical {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg] (hk : 0 < k)
    (hCanon :
      LatticeCanonicalCoeffPolyExtraction (k := k) (deg := deg) (domain := domain) δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := latticeThresholdEps ι F) :=
  correlatedAgreementCurves_of_latticeExtraction hk
    (latticeCoeffPolyExtraction_of_canonical hCanon)

end BoundaryLatticeThresholdLeaf

namespace BoundaryLatticeThresholdWitness

open ArkLib.BoundaryLatticeThresholdLeaf
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩

abbrev Iw : Type := Fin 8
abbrev Fw : Type := ZMod 11

/-- Eight distinct evaluation points in `ZMod 11`: a genuine lattice endpoint, since
`deg · n = 2 · 8 = 16 = 4²` is a perfect square. -/
def domainW : Iw ↪ Fw where
  toFun i := ((i : ℕ) : Fw)
  inj' := by
    intro a b h
    apply Fin.ext
    have h' : (((a : ℕ) : ZMod 11) = ((b : ℕ) : ZMod 11)) := h
    have hmod := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) 11).mp h'
    have ha : (a : ℕ) < 11 := by have := a.isLt; omega
    have hb : (b : ℕ) < 11 := by have := b.isLt; omega
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod

/-- `√ρ · n = √(2·8) = √16 = 4`, exactly. -/
theorem sqrtRateW_mul_card :
    ReedSolomon.sqrtRate 2 domainW * (Fintype.card Iw : ℝ≥0) = 4 := by
  have hsq := ArkLib.BoundaryCardResidual.sqrtRate_mul_card_sq_eq_deg_mul_card
    (domain := domainW) (deg := 2) (by norm_num [Iw])
  have h16 : ((2 * Fintype.card Iw : ℕ) : ℝ≥0) = 16 := by norm_num [Iw]
  rw [h16] at hsq
  have hs := congrArg NNReal.sqrt hsq
  rwa [NNReal.sqrt_sq, show (16 : ℝ≥0) = 4 ^ 2 by norm_num, NNReal.sqrt_sq] at hs

/-- The boundary scale is integral: `δ · n = (1 − √(2/8)) · 8 = 4`. -/
theorem deltaW_mul_card :
    (1 - ReedSolomon.sqrtRate 2 domainW) * (Fintype.card Iw : ℝ≥0) = 4 := by
  rw [tsub_mul, one_mul, sqrtRateW_mul_card,
    show ((Fintype.card Iw : ℕ) : ℝ≥0) = 8 by norm_num [Iw],
    tsub_eq_iff_eq_add_of_le (by norm_num : (4 : ℝ≥0) ≤ 8)]
  norm_num

/-- `⌊δ · n⌋ = 4`. -/
theorem floorW :
    Nat.floor ((1 - ReedSolomon.sqrtRate 2 domainW) * (Fintype.card Iw : ℝ≥0)) = 4 := by
  rw [deltaW_mul_card]
  norm_num

/-- **The witness endpoint is a genuine lattice point**: `⌊δ · n⌋ = δ · n` — exactly the
branch on which the floor-matched strict-radius route is provably unavailable. -/
theorem latticeW :
    (Nat.floor ((1 - ReedSolomon.sqrtRate 2 domainW) * (Fintype.card Iw : ℝ≥0)) : ℝ≥0)
      = (1 - ReedSolomon.sqrtRate 2 domainW) * (Fintype.card Iw : ℝ≥0) := by
  rw [floorW, deltaW_mul_card]
  norm_num

/-- The zero stack. -/
def uZ : WordStack Fw (Fin (1 + 1)) Iw := fun _ _ => 0

theorem curve_uZ (z : Fw) :
    (∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • uZ t) = (0 : Iw → Fw) := by
  funext i
  simp [uZ]

/-- The zero stack's good set is everything: every curve point is the zero codeword. -/
theorem goodW_eq_univ :
    RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domainW) uZ
      (1 - ReedSolomon.sqrtRate 2 domainW) = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro z
  have hzero_mem : (0 : Iw → Fw) ∈ (ReedSolomon.code domainW 2 : Set (Iw → Fw)) :=
    (ReedSolomon.code domainW 2).zero_mem
  have hrel : δᵣ((0 : Iw → Fw), (ReedSolomon.code domainW 2 : Set (Iw → Fw)))
      ≤ (1 - ReedSolomon.sqrtRate 2 domainW : ℝ≥0) := by
    rw [Code.relDistFromCode_eq_distFromCode_div,
      Code.distFromCode_of_mem (ReedSolomon.code domainW 2 : Set (Iw → Fw)) hzero_mem]
    simp
  simp only [RS_goodCoeffsCurve, curve_uZ, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hrel

theorem latticeThresholdEpsW : latticeThresholdEps Iw Fw = 9 / 11 := by
  unfold latticeThresholdEps
  norm_num [Iw, Fw, ZMod.card]

/-- **The hypothesis spine is simultaneously satisfiable, and the composite fires
end-to-end**: at the genuine lattice endpoint `(ZMod 11, n = 8, deg = 2, k = 1,
δ = 1 − √(2/8))`, the zero stack satisfies the quantitative threshold (`Pr = 1 > 1 · 9/11`)
and the §5 extraction (any admissible decoding is forced to `P z = 0`: a polynomial of
`natDegree < 2` vanishing on `≥ 4` of the `8` distinct evaluation points is zero), so
`jointAgreement` follows through `jointAgreement_of_latticeThreshold_of_coeffPolys`. -/
theorem witness_jointAgreement :
    jointAgreement (C := ReedSolomon.code domainW 2)
      (δ := 1 - ReedSolomon.sqrtRate 2 domainW) (W := uZ) := by
  classical
  refine jointAgreement_of_latticeThreshold_of_coeffPolys (k := 1) (deg := 2)
    (domain := domainW) (δ := 1 - ReedSolomon.sqrtRate 2 domainW)
    Nat.one_pos uZ ?_ ?_
  · -- the quantitative threshold: `Pr = 1 > 1 · (9/11)`.
    rw [ProximityGap.prob_close_curve_eq_card_goodCoeffsCurve_div_card
      (k := 1) (deg := 2) (domain := domainW)
      (δ := 1 - ReedSolomon.sqrtRate 2 domainW) uZ]
    rw [goodW_eq_univ, Finset.card_univ, latticeThresholdEpsW,
      show ((Fintype.card Fw : ℕ) : ℝ≥0) = 11 by norm_num [Fw, ZMod.card]]
    rw [ENNReal.div_self (by exact_mod_cast (by norm_num : (11 : ℝ≥0) ≠ 0))
      ENNReal.coe_ne_top]
    have h911 : (((9 : ℝ≥0) / 11 : ℝ≥0) : ENNReal) < 1 := by
      rw [← ENNReal.coe_one, ENNReal.coe_lt_coe,
        div_lt_one (by norm_num : (0 : ℝ≥0) < 11)]
      norm_num
    calc ((1 : ℕ) : ENNReal) * (((9 : ℝ≥0) / 11 : ℝ≥0) : ENNReal)
        = (((9 : ℝ≥0) / 11 : ℝ≥0) : ENNReal) := by rw [Nat.cast_one, one_mul]
      _ < 1 := h911
  · -- the §5 extraction for the zero stack: every admissible decoding is forced to `0`.
    intro P hP
    have hPzero : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domainW) uZ
        (1 - ReedSolomon.sqrtRate 2 domainW), P z = 0 := by
      intro z hz
      obtain ⟨hdeg, hdist⟩ := hP z hz
      rw [curve_uZ] at hdist
      have hΔ := (Code.pairRelDist_le_iff_pairDist_le (u := (0 : Iw → Fw))
        (v := (P z).eval ∘ domainW) (δ := 1 - ReedSolomon.sqrtRate 2 domainW)).mp hdist
      rw [floorW] at hΔ
      -- the disagreement set has `≤ 4` points, so `P z` vanishes on `≥ 4` domain points.
      set D : Finset Iw := Finset.univ.filter
        (fun i => (0 : Iw → Fw) i ≠ ((P z).eval ∘ domainW) i) with hD
      have hDcard : D.card ≤ 4 := by simpa [hammingDist, hD] using hΔ
      have hcompl : 4 ≤ Dᶜ.card := by
        rw [Finset.card_compl, show Fintype.card Iw = 8 by norm_num [Iw]]
        omega
      have heval : ∀ a ∈ Dᶜ.image domainW, (P z).eval a = 0 := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        have hi' : i ∉ D := Finset.mem_compl.mp hi
        rw [hD] at hi'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not,
          Function.comp_apply, Pi.zero_apply] at hi'
        exact hi'.symm
      have hs : 4 ≤ (Dᶜ.image domainW).card := by
        rwa [Finset.card_image_of_injective Dᶜ domainW.injective]
      exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (P z)
        (Dᶜ.image domainW) heval (by omega)
    refine ⟨fun _ => 0, fun j _ => by simp, ?_⟩
    intro z hz j _
    rw [hPzero z hz]
    simp

end BoundaryLatticeThresholdWitness

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps_pos
#print axioms ArkLib.BoundaryLatticeThresholdLeaf.card_gt_of_prob_gt_latticeThreshold
#print axioms
  ArkLib.BoundaryLatticeThresholdLeaf.jointAgreement_of_latticeThreshold_of_coeffPolys
#print axioms
  ArkLib.BoundaryLatticeThresholdLeaf.correlatedAgreementCurves_of_latticeExtraction
#print axioms
  ArkLib.BoundaryLatticeThresholdLeaf.boundaryCardLatticeThresholdResidual_of_extraction
#print axioms
  ArkLib.BoundaryLatticeThresholdLeaf.latticeCoeffPolyExtraction_of_canonical
#print axioms
  ArkLib.BoundaryLatticeThresholdLeaf.boundaryCardLatticeThresholdResidual_of_canonical
#print axioms
  ArkLib.BoundaryLatticeThresholdLeaf.correlatedAgreementCurves_of_latticeCanonical
#print axioms ArkLib.BoundaryLatticeThresholdWitness.sqrtRateW_mul_card
#print axioms ArkLib.BoundaryLatticeThresholdWitness.latticeW
#print axioms ArkLib.BoundaryLatticeThresholdWitness.goodW_eq_univ
#print axioms ArkLib.BoundaryLatticeThresholdWitness.witness_jointAgreement
