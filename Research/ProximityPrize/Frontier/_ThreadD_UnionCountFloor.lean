/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# THREAD D — the realized-incidence floor `hfloor` is dischargeable by the union-count, but the
# union-count `≤ q·ε*` IS the open distinct-γ growth law (NOT the per-line field-independent count)

Context (#444, ABF26 §6.7 `PrizeConditionalPin`).  The prize δ* is pinned to the explicit edge
value `(1−ρ) − 1/(C·L)` by exactly ONE open hypothesis:

  `hfloor : epsMCA (evalCode g n ((r−2)·m)) (prizeEdge …) ≤ ε*`

(the realized worst-case bad-scalar count at the edge stays within the prize budget).  THREAD D
asks whether `hfloor` can be discharged **directly** by the *realized-incidence structure* — the
p-independent distinct-γ union-count `|⋃_R {γ_R}| ≤ n` (the orbit-collapse `O → 1` at binding) —
rather than via the sup-norm `M`, whose only `M → epsMCA` route (`|G| + q·B`) is vacuous at the
prize budget.

## What this file establishes (axiom-clean)

`epsMCA` is, by definition, `⨆_u Pr_γ[mcaEvent C δ (u 0) (u 1) γ]` — a supremum over word-stacks
`u` of the *uniform* γ-probability, which equals `#{bad γ for u}/q`.  So an upper bound
`epsMCA C δ ≤ ε*` follows from a **per-stack bad-scalar count bound** plus a budget fit:

* `epsMCA_le_of_uniform_badCount_bound` — **THE THREAD-D REDUCTION (PROVEN).**  If for every
  stack `u` the bad-scalar count is `≤ B`, and `B/q ≤ ε*`, then `epsMCA C δ ≤ ε*`.  This is the
  *exact* mechanism that turns a union-count bound into `hfloor`: the realized far-line distinct-γ
  count IS that per-stack `#{bad γ}`, and the budget fit `B/q ≤ ε*` is exactly `B ≤ q·ε*`.

* `unionCountFloorClosesPrize` — applied at `B = n` (the union-count claim): if every stack's
  bad-scalar count is `≤ n` AND `n/q ≤ ε*`, then `epsMCA C δ ≤ ε*`.  So the union-count `≤ n`
  DOES discharge `hfloor` — provided it holds, and provided the budget admits `n/q ≤ ε*` (which
  the prize regime does, see the data note below).

## The honest verdict (the `≤ n` hypothesis is the open growth law, NOT the proven per-line count)

`UnionCountBadStacks C δ B` (every stack has `≤ B` bad scalars) is the hypothesis fed in.  At
`B = n` this is exactly the in-tree open obligation
`Frontier.FarLineCollapse.DstarPlateauLeBudget` (the plateau of the distinct-γ count is `≤ n`).
It is **NOT** the proven `ResolveFieldIndependent.badWeight_card_mul_le` bound: that bounds the
count `(s−w)·N ≤ s` PER FIXED ERROR LINE `(e₀, e₁)` (= per pair of nearby codewords / per fixed
target codeword).  The realized far-line distinct-γ count is the UNION over the whole codeword
list of those per-line sets — `D = S·O + z` with `O = #codeword-orbits` — and the per-line bound
controls only one term.  Empirically (probe `orbfast`):

  - at binding `O = 1` ⟹ `D = S + z ≤ n + 1` (union-count holds), while
  - just below binding `O > 1` ⟹ `D ≈ S·O ≫ n` (union-count fails).

So `UnionCountBadStacks _ _ n` ⟺ `O = 1 at binding` ⟺ the distinct-γ growth-law collapse — a
p-independent (field-cardinality-independent, by `ResolveFieldIndependent`), char-0 combinatorial
statement OFF the BGK/Paley sup-norm wall, but **open**.

**Verdict.**  THREAD D does NOT close `PrizeConditionalPin`.  It REDUCES `hfloor` cleanly and
provably (this file) to the union-count `≤ n` = the distinct-γ growth law `DstarPlateauLeBudget`.
That growth law is the genuine open core — it is NOT the BGK wall (it is p-independent, the wall
is p-dependent), but it is not closed here either.  The reduction is the contribution; the closure
is not claimed.

## Data note (the budget admits the union-count, prize-wide)

For `p ~ n^4` and the CEILING budget `ε* < 2^r·C(2^{μ-1}, r)/p`, one has `n/p < 2^r·C(2^{μ-1},r)/p`
for ALL `μ ≥ 4` (including the prize `μ = 30`), so a valid `ε* ∈ [n/p, budget)` exists for which
`n/q ≤ ε*` — i.e. the budget side of `unionCountFloorClosesPrize` is satisfiable.  (Reproduced by
`/tmp/budget_check.py`; recorded as data, not formalized.)

## References
- `Errors.lean` (`epsMCA`, `mcaEvent`), `MCAWitnessSpread.lean` (the `iSup_le` + `prob_uniform`
  upper-bound pattern this file generalizes), `Frontier/PrizeConditionalPinCapstone.lean`
  (`hfloor`), `Frontier/_DstarCollapseLaw.lean` (`DstarPlateauLeBudget`),
  `Frontier/ResolveFieldIndependent.lean` (the per-line p-independent count), `FarCosetExplosion.lean`.
-/

open Finset Code
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.ThreadD

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The per-stack realized bad-scalar count is uniformly `≤ B`.**  This is the realized-incidence
object: for EVERY word-stack `u`, the number of scalars `γ` triggering `mcaEvent` at radius `δ` is
at most `B`.  At `B = n` this is the union-count `|⋃_R {γ_R}| ≤ n` (= the distinct-γ growth law,
the open `Frontier.FarLineCollapse.DstarPlateauLeBudget`). -/
def UnionCountBadStacks (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    (Finset.univ.filter
      (fun γ : F => ProximityGap.mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ B

open Classical in
/-- **THE THREAD-D REDUCTION (PROVEN, axiom-clean).**  `epsMCA C δ ≤ ε*` follows from a per-stack
bad-scalar count bound `B` together with the budget fit `B/q ≤ ε*`.

`epsMCA C δ = ⨆_u Pr_γ[mcaEvent …]`, and for the uniform distribution
`Pr_γ[mcaEvent …] = #{bad γ for u} / q`.  Bounding every term by `B/q` and using `B/q ≤ ε*` gives
the supremum bound.  This is the exact mechanism by which the realized far-line distinct-γ count
(the per-stack `#{bad γ}`) discharges the prize floor `hfloor`. -/
theorem epsMCA_le_of_uniform_badCount_bound (C : Set (ι → A)) (δ : ℝ≥0)
    {B : ℕ} {εstar : ℝ≥0∞}
    (hcount : UnionCountBadStacks (F := F) (A := A) C δ B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    epsMCA (F := F) (A := A) C δ ≤ εstar := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  refine le_trans ?_ hbudget
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast hcount u

open Classical in
/-- **The union-count `≤ n` discharges `hfloor`.**  Specialization of the reduction at `B = n`
(the union-count claim `|⋃_R {γ_R}| ≤ n`): if every stack's realized bad-scalar count is `≤ n`,
and the budget admits `n/q ≤ ε*`, then `epsMCA C δ ≤ ε*` — i.e. `hfloor` holds.

⚠️ The `≤ n` premise is the OPEN distinct-γ growth law (`DstarPlateauLeBudget`), p-independent and
off the BGK wall, but NOT proven here (and NOT the per-fixed-line `ResolveFieldIndependent` count).
This theorem states the reduction, not a closure. -/
theorem unionCountFloorClosesPrize (C : Set (ι → A)) (δ : ℝ≥0) {εstar : ℝ≥0∞}
    (hunion : UnionCountBadStacks (F := F) (A := A) C δ (Fintype.card ι))
    (hbudget : (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    epsMCA (F := F) (A := A) C δ ≤ εstar :=
  epsMCA_le_of_uniform_badCount_bound C δ hunion hbudget

open Classical in
/-- **Sanity: the reduction is monotone in the count bound and the budget.**  A smaller per-stack
count and a larger budget only make `hfloor` easier — confirming the union-count is the *only*
quantity that matters (no hidden field-cardinality input beyond `q` in the budget). -/
theorem unionCount_mono (C : Set (ι → A)) (δ : ℝ≥0) {B B' : ℕ}
    (hBB' : B ≤ B') (hcount : UnionCountBadStacks (F := F) (A := A) C δ B) :
    UnionCountBadStacks (F := F) (A := A) C δ B' :=
  fun u => le_trans (hcount u) hBB'

end ProximityGap.Frontier.ThreadD

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.ThreadD.epsMCA_le_of_uniform_badCount_bound
#print axioms ProximityGap.Frontier.ThreadD.unionCountFloorClosesPrize
#print axioms ProximityGap.Frontier.ThreadD.unionCount_mono
