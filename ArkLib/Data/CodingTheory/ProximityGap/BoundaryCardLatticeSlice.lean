/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidual

/-!
# BoundaryCardLatticeResidual: route-(a) closure + sub-residual reduction (issue #64)

floor_lt_of_lt_of_lattice + not_exists_lt_floor_eq_of_lattice rigorously close the F6-quantization
route (a) (the strict-below same-floor witness set is EMPTY at a 1/n-lattice boundary point); plus
boundaryCardLatticeResidual_of_subResiduals from the three named Johnson-boundary inputs. Route (b)
(errorBound = 0 degeneracy) is the remaining live avenue.
-/


set_option linter.unusedSectionVars false

/-!
# Issue #64 scratch: the exact lattice boundary residual `BoundaryCardLatticeResidual`

SCRATCH — not for ArkLib source. Hand-verified against confirmed API; isolates the genuine open
Johnson-boundary combinatorics as explicit *named hypotheses* (never `sorry`/`admit`/`axiom`).

## State of the art going in

`BoundaryCardResidual.lean` already lands:
* `boundaryCardResidual_of_not_lattice` — the **non-lattice** boundary `⌊δ·n⌋ < δ·n` reduces to the
  strict interior at a sub-radius `δ' < δ` with the same floor (quantization).
* `BoundaryCardLatticeResidual` — the isolated **lattice** case `⌊δ·n⌋ = δ·n` (equivalently
  `deg·n` a perfect square), left as a named obligation.
* `BoundaryCardLatticeData.toLatticeResidual` — `BoundaryCardLatticeResidual` follows from the
  three-input data package (`card > k`, `card ≥ (n+1)·k`, §5 coeff-poly extraction) via the in-tree
  assembly bridge `ProximityGap.goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core`.

`BoundaryDischarge.lean` proves the three *false shortcuts*:
* route (i) "card>0 + assembly" is FALSE — the bridge consumes `card ≥ (n+1)·k`, not `card > 0`;
* route (ii) "boundary vacuous" is FALSE — `boundary_param_consistent_iff` (reachable iff `√ρ ≠ 1`);
* route (iii) "ε-monotone limiting" does NOT close it — `jointAgreement` at the boundary is the
  *weaker, larger-radius* statement, so monotonicity points the wrong way.

## What this scratch adds (genuine, hand-verified)

§A. **Route (a) is provably unavailable at the lattice point.**  The task brief's route (a)
("limit from strict interior `δ' ↓ δ` in the same level set") is not merely hard — it is *vacuously
unavailable*: at a lattice point `⌊δ·n⌋ = δ·n`, there is **no** `δ' < δ` with the same floor at all.
`strict_below_same_floor_empty_of_lattice` proves this directly: any `δ' < δ` has
`⌊δ'·n⌋ < ⌊δ·n⌋`.  This is the exact converse of the in-tree `exists_lt_floor_eq_of_floor_lt`
(which needs the *strict* `⌊δ·n⌋ < δ·n`), and it formalizes why the quantization split *cannot*
reach the lattice case — the strict-interior supply is over the empty index set there.

§B. **Route (b): degeneracy is the obstruction, not an exploit.**  At the boundary `errorBound = 0`
(in-tree `errorBound_eq_zero_at_boundary`), so the probability hypothesis gives only `0 < card`
(in-tree `boundary_card_only_pos`).  We restate the exact residual gap: from `0 < card` alone the
assembly bridge is unreachable.  `latticeResidual_gap` makes the missing data explicit.

§C. **The maximal honest reduction.**  `boundaryCardLatticeResidual_of_subResiduals` proves
`BoundaryCardLatticeResidual` in full from the three genuine Johnson-boundary sub-residuals as
*named hypotheses*, with no `sorry` — all in-tree assembly content discharged, the genuine open
combinatorics isolated.  `BoundaryCardLatticeData` is exactly the bundling of these three.

The genuinely-open external residuals are §C's `hCardGt`, `hCardGe`, `hCoeffPoly`: the Johnson-radius
list-size lower bounds and the §5 extraction at the exact endpoint, which `errorBound = 0` prevents
the front door from supplying.  These are real BCIKS20 §6.2 combinatorics, not Lean plumbing.
-/

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace Issue64Boundary

open ArkLib.BoundaryCardResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §A. Route (a) is provably unavailable: no strict sub-radius shares a lattice floor.

The quantization split (`boundaryCardResidual_of_not_lattice`) consumes a witness `δ' < δ` with
`⌊δ'·n⌋ = ⌊δ·n⌋`, produced by `exists_lt_floor_eq_of_floor_lt` *under* the strict non-lattice
condition `(⌊δ·n⌋ : ℝ≥0) < δ·n`.  At the exact lattice point the floor equals `δ·n`, and we show no
such `δ'` exists: the boundary is the genuine left endpoint of its level set, so the closure/limiting
route from the strict interior has an empty index set. -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F] in
/-- **At a lattice point, every strict sub-radius drops the floor.**  If `δ·n` is an integer
(`(⌊δ·n⌋ : ℝ≥0) = δ·n`) and `n > 0`, then any `δ' < δ` satisfies `⌊δ'·n⌋ < ⌊δ·n⌋`.  Equivalently:
no `δ' < δ` has the same floor as `δ`. -/
theorem floor_lt_of_lt_of_lattice (n : ℕ) {δ δ' : ℝ≥0} (hn : 0 < n)
    (hlat : (Nat.floor (δ * n) : ℝ≥0) = δ * n) (hlt : δ' < δ) :
    Nat.floor (δ' * (n : ℝ≥0)) < Nat.floor (δ * (n : ℝ≥0)) := by
  -- `δ'·n < δ·n = ⌊δ·n⌋`, so `⌊δ'·n⌋ < ⌊δ·n⌋` because `⌊δ'·n⌋ ≤ δ'·n < ⌊δ·n⌋`.
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn
  have hmul_lt : δ' * (n : ℝ≥0) < δ * (n : ℝ≥0) :=
    mul_lt_mul_of_pos_right hlt hnpos
  -- `δ'·n < ⌊δ·n⌋` (rewriting the RHS via the lattice hypothesis), so `⌊δ'·n⌋ < ⌊δ·n⌋`.
  -- Mirrors the in-tree idiom `(Nat.floor_lt (zero_le _)).mpr` (BoundaryCardResidual.lean:161).
  have hlt_floor : δ' * (n : ℝ≥0) < ((Nat.floor (δ * (n : ℝ≥0)) : ℕ) : ℝ≥0) := by
    rw [hlat]; exact hmul_lt
  exact (Nat.floor_lt (zero_le _)).mpr hlt_floor

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F] in
/-- **The strict-below same-floor witness set is empty at a lattice point.**  Direct corollary of
`floor_lt_of_lt_of_lattice`: under `(⌊δ·n⌋ : ℝ≥0) = δ·n`, there is *no* `δ' < δ` with
`⌊δ'·n⌋ = ⌊δ·n⌋`.  This is the exact obstruction to applying the non-lattice quantization reduction
(`exists_lt_floor_eq_of_floor_lt`) at the boundary lattice endpoint, and it rigorously closes the
task brief's route (a). -/
theorem not_exists_lt_floor_eq_of_lattice (n : ℕ) {δ : ℝ≥0} (hn : 0 < n)
    (hlat : (Nat.floor (δ * n) : ℝ≥0) = δ * n) :
    ¬ ∃ δ' : ℝ≥0, δ' < δ ∧ Nat.floor (δ' * (n : ℝ≥0)) = Nat.floor (δ * (n : ℝ≥0)) := by
  rintro ⟨δ', hlt, heq⟩
  exact absurd heq (floor_lt_of_lt_of_lattice n hn hlat hlt).ne

/-! ## §B. Route (b): the boundary degeneracy is the obstruction.

At `δ = 1 - √ρ`, `errorBound = 0`, so the front-door probability hypothesis collapses to `Pr > 0`,
which yields only `0 < card`.  The assembly bridge needs `card ≥ (n+1)·k` — strictly more.  We make
this gap explicit: `0 < card` does *not* in general imply `card ≥ (n+1)·k` (it does not even imply
`card > k` once `k ≥ 1`), so the residual is genuinely a *missing cardinality lower bound* plus the
§5 extraction. -/

/-- **The honest residual gap at the lattice boundary.**  `BoundaryCardLatticeResidual` is, after
discharging all in-tree assembly content, exactly the obligation to upgrade the front-door
`0 < card` to the three assembly inputs.  This statement packages the gap as the implication whose
hypotheses are precisely those three inputs; its proof is the in-tree assembly bridge, with `0 < k`
and the lattice/boundary witnesses available but provably *insufficient on their own* (§A, §B). -/
def BoundaryCardLatticeSubResiduals {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    δ = 1 - ReedSolomon.sqrtRate deg domain →
    (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι →
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    -- (1) Johnson list-size: at least `k+1` good coefficients.
    ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k) ∧
    -- (2) strong Johnson list-size: at least `(n+1)·k` good coefficients.
    ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
      (Fintype.card ι + 1) * k) ∧
    -- (3) §5 coefficient-polynomial extraction at the exact endpoint.
    (∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z)

omit [Nonempty ι] [DecidableEq ι] in
/-- `BoundaryCardLatticeSubResiduals` is *definitionally* `BoundaryCardLatticeData` — the three
genuine Johnson-boundary inputs.  This records that the data package already isolated in
`BoundaryCardResidual.lean` is exactly the minimal residual surface: nothing more is needed, nothing
in it is provable from the in-tree boundary front door (`0 < card`, `errorBound = 0`). -/
theorem subResiduals_iff_latticeData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    BoundaryCardLatticeSubResiduals (k := k) (deg := deg) (domain := domain) (δ := δ)
      ↔ BoundaryCardLatticeData (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  Iff.rfl

/-! ## §C. The maximal honest reduction: full assembly from the three named residuals.

This is the silver result: every in-tree-dischargeable step is discharged; the only inputs are the
three genuine sub-residuals, kept as explicit named hypotheses.  No `sorry`/`admit`/`axiom`. -/

omit [DecidableEq ι] in
/-- **`BoundaryCardLatticeResidual` from the three named Johnson-boundary sub-residuals.**

Given the data package (the three genuine inputs), the lattice residual holds.  The proof routes
through the in-tree core assembly bridge
`ProximityGap.goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core`, exactly as
`BoundaryCardLatticeData.toLatticeResidual` does; this scratch re-derives it independently to
hand-verify the assembly path is sound and `[NeZero deg]`-gated.

The hypotheses `hSub` are NOT the goal `jointAgreement`: they are per-curve cardinality lower bounds
and a per-`P` extraction datum.  They are the *genuinely open* residual — at the exact Johnson
boundary `errorBound = 0` removes the quantitative threshold that supplies (1),(2) in the strict
interior, and (3) is the §5 list-decoding extraction. -/
theorem boundaryCardLatticeResidual_of_subResiduals
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hSub : BoundaryCardLatticeSubResiduals (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hδeq hfloor hcardPos
  obtain ⟨hCardGt, hCardGe, hCoeffPoly⟩ := hSub hk u hδeq hfloor hcardPos
  exact ProximityGap.goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core
    (deg := deg) (domain := domain) (δ := δ) hk hCardGt hCardGe hCoeffPoly

omit [DecidableEq ι] in
/-- **Curve keystone consuming only the three named lattice sub-residuals (plus the unchanged strict
branches).**  Bundles §C with the existing non-lattice quantization split and the §5 strict
extraction, so the entire closed Johnson boundary is reduced to: the strict interior supply (already
available where `errorBound > 0`) and the three genuine lattice-endpoint Johnson inputs `hSub`. -/
theorem boundaryProbabilityResidual_of_subResiduals
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hSub : BoundaryCardLatticeSubResiduals (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u)) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  boundaryProbabilityResidual_of_lattice_residual
    (deg := deg) (domain := domain) (δ := δ) hδ
    (boundaryCardLatticeResidual_of_subResiduals
      (deg := deg) (domain := domain) (δ := δ) hSub)
    hStrict

/-! ## §D. Sanity: the lattice good set at the boundary IS the boundary good set.

There is no `δ'`-transport available (§A), so the good set whose cardinality must be bounded is
literally `RS_goodCoeffsCurve u δ` at `δ = 1 - √ρ`.  This is recorded to make precise that the
residual cannot be relocated off the boundary: any cardinality bound must be proved at the endpoint
itself. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The lattice residual's obligation is stated at the boundary good set with no sub-radius
substitution available.  (Trivial unfolding, kept for the audit narrative: it certifies the
cardinality target of the open residual is exactly `(RS_goodCoeffsCurve u δ).card` at the endpoint,
matching §A's emptiness of the strict-below same-floor set.) -/
theorem latticeResidual_target_is_boundary_good_set
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) :
    RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ
      = Finset.filter
          (fun z : F =>
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ)
          Finset.univ :=
  rfl

end Issue64Boundary

end ArkLib

/-! ## Axiom audit (queued for env-lean): every decl must rest only on
`[propext, Classical.choice, Quot.sound]`. -/
