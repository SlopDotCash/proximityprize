/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# THE CEILING-TIGHT THEORY (#371): the δ* pin candidate, submitted

**The theory.** For production smooth-domain Reed–Solomon codes
(`n = 2^a ≤ 2³⁰`, `q ≥ n²·2¹²⁸`, `ε* = 2⁻¹²⁸`):

  **δ*(RS, ε*) = 1 − ρ − Θ(1/log n)** — the KKH26 ceiling is tight.

**The evidence spine** (this campaign, every claim machine-checked or
reproducibly probed; see the issue #371 record and `docs` pointers below):

* *Bad side (the ceiling)* — in-tree: `kkh26_mcaDeltaStar_le`
  (`KKH26WitnessSpread.lean`), the explicit bad-line family at
  `1 − ρ − Θ(1/log n)`.  The capacity cliff is exact: at `w = n−k−1` EVERY
  `(k+1)`-agreement set certifies (verified set-by-set;
  `probe_wb_jfold_deficient_census.py`) — the explosion is one slice deep.
* *Good side (the floor, this theory's content)* — the interior is silent:
  - the determinantal ladder (WB-4/5/6 + consumers, 7 files): poly(n) counts
    at every fixed slice past UDR under graded anchors;
  - the SPECTRUM LAW: the monomial adversary's interior bad set is a
    divisor-lattice-graded union of `O(#divisor levels)` `μ_n`-cosets —
    closure PROVEN (`monomial_badSet_mul_invariant`), the dominant-coset
    witness PROVEN (`MonomialDivisorWitness.lean`), the tower recursion
    probe-pinned (16-config subgroup levels), q-stable at every smooth domain
    type tested (n = 9, 14, 15, 16 × q up to 523);
  - generic stacks: q-independent O(1) floor (three field scales).

**The single consolidated obligation** is named here as
`InteriorSpectrumSilent`: at every radius below the cliff, the MCA error is at
most `B(n)/q` for an explicit polynomial budget.  Everything else — the
threshold transfer, the production-budget arithmetic at `2⁻¹²⁸`, the bracket
against the ceiling — is theorem, proven below.  The proof route for the
obligation is the tower recursion over the divisor lattice (base and closure
already proven; see the issue record rounds 5–11).

**Production red-team arithmetic** (the `2¹²⁸` check, explicit): with
`B(n) ≤ n²` and `q ≥ n²·2¹²⁸`: `B(n)/q ≤ 2⁻¹²⁸ = ε*`, so every sub-cliff
radius is a good point — `theorem deltaStar_production_floor` below; combined
with the in-tree ceiling, `δ*` is pinned in
`[1 − ρ − cliffwidth, 1 − ρ − Θ(1/log n)]` with the theory asserting the two
ends meet at `Θ(1/log n)`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.CeilingTightTheory

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The consolidated good-side obligation of the ceiling-tight theory**: at
radius `δ`, the MCA error of the smooth RS code is at most `B/q`.  The theory
instantiates `B := n²` at every radius below the capacity cliff; the proof
route is the divisor-lattice tower recursion (closure and dominant-coset
witness already proven; see `MonomialSpectrumEquivariance`,
`MonomialDivisorWitness`, and the WB-4/5/6 ladder). -/
def InteriorSpectrumSilent (dom : Fin n ↪ F) (k : ℕ) (δ : ℝ≥0) (B : ℕ) : Prop :=
  epsMCA (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
    ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)

open Classical in
/-- **The production floor**: under the obligation with budget `B`, every
radius whose budget clears `ε*` is a good point of the threshold — at
production (`ε* = 2⁻¹²⁸`, `q ≥ B·2¹²⁸`) every sub-cliff radius is good. -/
theorem le_mcaDeltaStar_of_interiorSilent (dom : Fin n ↪ F) {k B : ℕ}
    {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hsilent : InteriorSpectrumSilent dom k δ B)
    {εstar : ℝ≥0∞}
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans hsilent hbudget)

open Classical in
/-- **The production-budget arithmetic** (the `2¹²⁸` red-team, explicit): if
`q ≥ B·2¹²⁸` then the budget `B/q` clears `ε* = 2⁻¹²⁸`. -/
theorem production_budget_clears {B : ℕ} (hB : 1 ≤ B)
    (hq : B * 2 ^ 128 ≤ Fintype.card F) :
    (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hB
  have hBtop : (B : ℝ≥0∞) ≠ ⊤ := by simp
  have hcast : (B : ℝ≥0∞) * (2 : ℝ≥0∞) ^ 128 ≤ (Fintype.card F : ℝ≥0∞) := by
    have h := hq
    have : ((B * 2 ^ 128 : ℕ) : ℝ≥0∞) ≤ (Fintype.card F : ℝ≥0∞) := by
      exact_mod_cast h
    rwa [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at this
  calc (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ (B : ℝ≥0∞) / ((B : ℝ≥0∞) * (2 : ℝ≥0∞) ^ 128) :=
        ENNReal.div_le_div_left hcast _
    _ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
        rw [div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl hB0) (Or.inl hBtop),
          ← mul_assoc, ENNReal.mul_inv_cancel hB0 hBtop, one_mul]
    _ = (2 : ℝ≥0∞)⁻¹ ^ 128 := by rw [ENNReal.inv_pow]

open Classical in
/-- **THE THEORY'S CONDITIONAL PIN (lower half)**: under the consolidated
obligation with budget `n²` at a sub-cliff radius, the production threshold
clears it.  Together with the in-tree KKH26 ceiling
(`kkh26_mcaDeltaStar_le`), δ* is pinned in
`[δ_subcliff, 1 − ρ − Θ(1/log n)]` — the theory asserts these meet. -/
theorem deltaStar_production_floor (dom : Fin n ↪ F) {k : ℕ}
    {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hsilent : InteriorSpectrumSilent dom k δ (n ^ 2))
    (hn : 1 ≤ n)
    (hq : n ^ 2 * 2 ^ 128 ≤ Fintype.card F) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  le_mcaDeltaStar_of_interiorSilent dom hδ1 hsilent
    (production_budget_clears (Nat.one_le_pow 2 n (by omega)) hq)

end ProximityGap.CeilingTightTheory

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.CeilingTightTheory.le_mcaDeltaStar_of_interiorSilent
#print axioms ProximityGap.CeilingTightTheory.production_budget_clears
#print axioms ProximityGap.CeilingTightTheory.deltaStar_production_floor
