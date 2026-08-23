/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentSupplyIdentity

/-!
# Moment–supply saturation: the sharp `C(n,j)` ceiling and its codeword witness (#389/#444 §6.5)

`MomentSupplyIdentity` proves the exact identity `Σ_c C(|A_c|, j) = N_j(w)` for `j ≥ k`
(`moment_supply_identity`), and pins the base level `j = k` at the word-independent value
`Σ_c C(|A_c|, k) = C(n,k)` (`moment_identity_base`).  This file supplies the two structural
end-points of the whole moment-supply sequence `j ↦ N_j(w)`, which §6.5 of #444 flags as the
sole live structural tool (the coset-union / incidence generating function `Z(t)=Σ_j N_j t^j`):

* **`degenerateSets_card_le`** — the SHARP CEILING `N_j(w) ≤ C(n,j)` for *every* word `w`
  and every `j` (the degenerate-`j`-sets are a sub-family of all `j`-sets).  Via the identity
  this is `Σ_c C(|A_c|, j) ≤ C(n,j)` for `j ≥ k`: the `j`-th binomial moment of the agreement
  spectrum never exceeds the total number of `j`-sets.

* **`degenerateSets_codeword`** / **`moment_supply_codeword`** — the EQUALITY WITNESS: if the
  word `w` is itself a codeword of `rsCode dom k`, then EVERY `j`-set is degenerate (explained
  by `w` itself), so `N_j(w) = C(n,j)` for *all* `j` — the ceiling is *saturated*, at every
  level, by a codeword word.  Hence the `C(n,j)` ceiling of `degenerateSets_card_le` is sharp
  for all `j` simultaneously, not just `j = k` (where `moment_identity_base` already gives the
  frozen value).  The supply sequence of a codeword word is the full binomial row `C(n,·)`.

Probe-validated (exact mod-`p`, PROPER `μ_n`, `p ≫ n^3`, `p ≡ 1 (mod n)`, NEVER `n = q-1`,
multi-prime, n=8/16/32): for a codeword word `N_j = C(n,j)` at every `j ≥ k`; for a generic
(random) word `N_j = 0` for `j > k` (the supply collapses to the frozen base), confirming the
codeword word is the unique per-level maximiser of the moment-supply sequence.

HONEST SCOPE (rule-3, rule-6): this is supply-side IDENTITY infrastructure on the
moment-supply sequence — a sharp ceiling with its equality witness.  It is NOT a CORE
closure and is not thinness-essential by itself; it provides the exact end-points
(`j=k` frozen, ceiling `C(n,j)`, codeword saturator) that any generating-function /
pole-structure argument for the `m*` growth law (§6.5) must respect.  CORE (BGK
`M(μ_n) ≤ C√(n log(p/n))`) remains OPEN.

Issue #389 / #444 §6.5.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The sharp `C(n,j)` ceiling.**  For every word `w` and every level `j`, the number of
degenerate `j`-sets is at most the total number of `j`-sets — the degenerate sets form a
sub-family of all `j`-subsets.  Combined with `moment_supply_identity` (`j ≥ k`) this is the
moment ceiling `Σ_c C(|A_c|, j) ≤ C(n, j)`. -/
theorem degenerateSets_card_le (dom : Fin n ↪ F) (k j : ℕ) (w : Fin n → F) :
    (degenerateSets dom k j w).card ≤ n.choose j := by
  classical
  calc (degenerateSets dom k j w).card
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard j).card := by
        refine Finset.card_le_card ?_
        unfold degenerateSets
        exact Finset.filter_subset _ _
    _ = n.choose j := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The moment ceiling** (`j ≥ k`): the `j`-th binomial moment of the agreement spectrum
never exceeds the total number of `j`-sets, `Σ_c C(|A_c|, j) ≤ C(n, j)`.  (The `j = k` case is
the frozen equality `moment_identity_base`.) -/
theorem moment_supply_le (dom : Fin n ↪ F) {k j : ℕ} (hkj : k ≤ j) (w : Fin n → F) :
    ∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose j) ≤ n.choose j := by
  rw [moment_supply_identity dom hkj w]
  exact degenerateSets_card_le dom k j w

open Classical in
/-- **Codeword saturation (set form).**  If the word `w` is itself a codeword of `rsCode dom k`,
every `j`-subset is degenerate — `w` explains it — so the degenerate-`j`-sets are ALL `j`-sets. -/
theorem degenerateSets_codeword (dom : Fin n ↪ F) (k j : ℕ) {w : Fin n → F}
    (hw : w ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    degenerateSets dom k j w = (Finset.univ : Finset (Fin n)).powersetCard j := by
  classical
  unfold degenerateSets
  refine Finset.filter_true_of_mem ?_
  intro S _
  -- `w` itself is a codeword agreeing with `w` everywhere on `S`.
  exact ⟨w, hw, fun i _ => rfl⟩

open Classical in
/-- **Codeword saturation (count form).**  A codeword word saturates the `C(n,j)` ceiling at
EVERY level `j`: `N_j(w) = C(n,j)` for all `j`.  The supply sequence of a codeword word is the
full binomial row. -/
theorem degenerateSets_codeword_card (dom : Fin n ↪ F) (k j : ℕ) {w : Fin n → F}
    (hw : w ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (degenerateSets dom k j w).card = n.choose j := by
  rw [degenerateSets_codeword dom k j hw, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **Codeword moment saturation** (`j ≥ k`): for a codeword word the `j`-th binomial moment of
the agreement spectrum hits the ceiling, `Σ_c C(|A_c|, j) = C(n, j)`, at every `j ≥ k`.  Hence
the ceiling `moment_supply_le` is sharp for all `j` simultaneously (the `j = k` frozen value
`moment_identity_base` is the special case). -/
theorem moment_supply_codeword (dom : Fin n ↪ F) {k j : ℕ} (hkj : k ≤ j) {w : Fin n → F}
    (hw : w ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    ∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose j) = n.choose j := by
  rw [moment_supply_identity dom hkj w]
  exact degenerateSets_codeword_card dom k j hw

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.degenerateSets_card_le
#print axioms ProximityGap.PairRank.moment_supply_le
#print axioms ProximityGap.PairRank.degenerateSets_codeword
#print axioms ProximityGap.PairRank.degenerateSets_codeword_card
#print axioms ProximityGap.PairRank.moment_supply_codeword
