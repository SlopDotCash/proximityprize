/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._BSG_DRC1
import ArkLib.Research.ProximityGap.Frontier._BSG_EX_E4a
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# BSG — assembling the `BareDRCExtract` extraction

This file assembles the proven dependent-random-choice (DRC) extraction sub-lemmas
(`_BSG_EX_*`, `_BSG_DRC1`) into the interface `BareDRCExtract`, which an older plan treated as the
single remaining input to the chain
`BareDRCExtract → BareDRC (bareDRC_of_extract) → BSGCore → BGK → δ*-floor`.

**Status correction.** `BareDRCExtract` and `DRCRefinedReps` are both **false for every choice of
constants** (`bareDRCExtract_false`, `drcRefinedReps_false` in
`_BSG_EX_BareDRCExtractFalse.lean`): at `K = 1` the complete graph on a large Sidon set meets all
graph hypotheses, yet no constant-fraction subset has linear doubling. The chain above is
therefore vacuous at its first link and does **not** make BGK or the δ*-floor unconditional modulo
anything satisfiable. The counting lemmas proven here (E2b, E4b, E4b′) are valid and reusable; the
energy-coupled replacement interface is `DRCKernelEnergy` (`_BSGC_attempt4.lean`), still open.

## What is proven here (axiom-clean)

The intermediate counting layer of the extraction, which converts the DRC statistics into the
size and difference-set bookkeeping that `BareDRCExtract` demands:

* `card_goodPairs_ge` (E2b) — from a cherry mass `∑_b deg(b)² ≥ #A²·3t`, the good-pair
  common-neighbour *mass* exceeds `#A²·2t` (uses the proven `sum_commonNeighbors_goodPairs_ge`).
* `card_diffSet_mul_le_of_reps_ge` (E4b) — if every difference in `A'' - A''` has `≥ t`
  representations as an ordered pair from `A''`, then `#(A'' - A'') · t ≤ #A''²`
  (pure E4a fiberwise double-count + pointwise lower bound; **no Cauchy–Schwarz**).
* `bareDRCExtract_of_refinedReps` — the **assembly**: `BareDRCExtract` follows from the single
  named hypothesis `DRCRefinedReps`, with ALL the size/nonemptiness/difference-set bookkeeping
  (E0/E1 size half + E4b) discharged here.

## The named hypothesis `DRCRefinedReps` (REFUTED for all constants)

`DRCRefinedReps` asks for a constant-fraction **refinement** `A''` of the good neighbourhood inside
which *every* difference has many representations. The *naive* elementary representation route for
it is machine-checked **false** in `_BSG_EX_E4cObstruction` (the factorisation
`a - a' = (a-w) - (a'-w)` does NOT land in `A'' ×ˢ A''`). More decisively, `DRCRefinedReps` itself
is unsatisfiable: `bareDRCExtract_of_refinedReps` (proved below) shows it implies
`BareDRCExtract`, which is false for every choice of constants, so `drcRefinedReps_false` holds.
Like `BareDRCExtract`, it uses only graph data and discards the additive-energy information that
a correct Ruzsa/Plünnecke–Petridis argument needs; no such argument can discharge it.

Thus the BGK chain is **not** unconditional modulo `DRCRefinedReps`: that hypothesis is false,
and the assembly theorem below is a valid but vacuous implication.

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29 + Corollary 2.30.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## E2b — good-pair mass lower bound -/

/-- **E2b — good pairs carry `≥ #A²·2t` cherries.** From the cherry double-count lower bound
(`sum_commonNeighbors_goodPairs_ge`) and a cherry mass `∑_b deg(b)² ≥ #A²·3t`, together with
`#(A×ˢA) = #A²`, the good-pair (`cn ≥ t`) common-neighbour mass exceeds `#A²·2t`.

Quantitatively: `#A²·3t ≤ ∑deg² ≤ goodmass + #A²·t`, so `goodmass ≥ #A²·3t − #A²·t = #A²·2t`. -/
theorem card_goodPairs_ge (A : Finset α) (G : Finset (α × α)) (t : ℕ)
    (hcherrylb : #A ^ 2 * (3 * t) ≤ ∑ b ∈ A, rDeg A G b ^ 2) :
    #A ^ 2 * (2 * t) ≤
      ∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2 := by
  classical
  have hgood := sum_commonNeighbors_goodPairs_ge A G t
  have hprod : #(A ×ˢ A) = #A ^ 2 := by rw [Finset.card_product, sq]
  rw [hprod] at hgood
  nlinarith [hcherrylb, hgood]

/-! ## E4b — difference-set card bound from a uniform representation lower bound -/

/-- **E4b — small difference set from many representations.** If every difference `d` in
`A'' - A''` has at least `t` representations as an ordered pair `(x, y) ∈ A'' ×ˢ A''` with
`x - y = d`, then `#(A'' - A'') · t ≤ #A''²`.

Proof: by E4a, `∑_{d ∈ A''-A''} r d = #A''²`; each summand is `≥ t`, so
`#(A''-A'') · t = ∑_{d} t ≤ ∑_d r d = #A''²`. -/
theorem card_diffSet_mul_le_of_reps_ge (A'' : Finset α) (t : ℕ)
    (hreps : ∀ d ∈ A'' - A'', t ≤ #{p ∈ A'' ×ˢ A'' | p.1 - p.2 = d}) :
    #(A'' - A'') * t ≤ #A'' ^ 2 := by
  classical
  calc #(A'' - A'') * t
      = ∑ _d ∈ A'' - A'', t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ d ∈ A'' - A'', #{p ∈ A'' ×ˢ A'' | p.1 - p.2 = d} := Finset.sum_le_sum hreps
    _ = #A'' ^ 2 := diffReps_sum_eq_card_sq A''

/-- **E4b′ — the clean small-doubling form.** Under the same uniform representation lower bound,
if additionally `#A'' ≤ s · t` (the threshold dominates the size up to a factor `s`) and `t > 0`,
then `#(A'' - A'') ≤ s · #A''`. This is the shape `BareDRCExtract` consumes: a *linear* doubling
bound `#(A''-A'') ≤ (const) · #A''`. -/
theorem card_diffSet_le_of_reps_ge (A'' : Finset α) (t s : ℕ) (ht : 0 < t)
    (hsize : #A'' ≤ s * t)
    (hreps : ∀ d ∈ A'' - A'', t ≤ #{p ∈ A'' ×ˢ A'' | p.1 - p.2 = d}) :
    #(A'' - A'') ≤ s * #A'' := by
  classical
  have h1 : #(A'' - A'') * t ≤ #A'' ^ 2 := card_diffSet_mul_le_of_reps_ge A'' t hreps
  -- `#A''² = #A'' * #A'' ≤ #A'' * (s*t) = (s*#A'')*t`, so `#(A''-A'')*t ≤ (s*#A'')*t`.
  have h2 : #A'' ^ 2 ≤ (s * #A'') * t := by
    have : #A'' * #A'' ≤ #A'' * (s * t) := Nat.mul_le_mul_left _ hsize
    nlinarith [this]
  have h3 : #(A'' - A'') * t ≤ (s * #A'') * t := le_trans h1 h2
  exact Nat.le_of_mul_le_mul_right h3 ht

/-! ## The (refuted) refined representation supply -/

/-- **`DRCRefinedReps` — the popular-difference refinement interface (REFUTED for all constants;
see `drcRefinedReps_false` in `_BSG_EX_BareDRCExtractFalse.lean`).**

Given the post-averaging data of `BareDRCExtract` (a good vertex `b₀` with a large neighbourhood
`N = leftNbhd A G b₀`, the cherry-richness, the edge-density), this asserts the existence of:

* a **refinement** `A'' ⊆ N` that is still a constant fraction of `N`
  (`s · #A'' ≥ #N`, so `A''` is within a factor `s = s(K)` of the whole neighbourhood), and
* a threshold `t > 0` with `#A'' ≤ s · t` (so the threshold dominates the refined size), and
* a uniform representation lower bound: *every* difference `d ∈ A'' - A''` has `≥ t`
  representations as an ordered pair from `A''`.

These three facts are exactly the input that the proven E4b (`card_diffSet_le_of_reps_ge`) turns
into the doubling bound `#(A''-A'') ≤ s·#A''`, and the size relation chains to the
`BareDRCExtract` size conclusion. The naive route to the representation lower bound is refuted
(`naiveDiffReps_REFUTED`), and the interface as a whole is false for every choice of constants
(`drcRefinedReps_false`): its graph-only hypotheses hold for the complete graph on a large Sidon
set at `K = 1`.

The parameter `s` is the (`K`-polynomial) refinement factor; `DRCRefinedReps C₁ C₂ c` fixes its
growth as `s ≤ C₂ * K ^ c` and ties the size factor to `C₁`. -/
def DRCRefinedReps (C₁ C₂ c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ (A'' : Finset α) (t s : ℕ),
        A'' ⊆ leftNbhd A G b₀ ∧ A''.Nonempty ∧ 0 < t ∧
        s ≤ C₂ * K ^ c ∧
        C₁ * K * #A'' ≥ #A ∧
        #A'' ≤ s * t ∧
        (∀ d ∈ A'' - A'', t ≤ #{p ∈ A'' ×ˢ A'' | p.1 - p.2 = d})

/-- **`BareDRCExtract` from `DRCRefinedReps`.** The assembly: the refined set `A''` is the output
`A'`. Its nonemptiness and the size bound `C₁ K #A'' ≥ #A` come directly from `DRCRefinedReps`;
the containment `A'' ⊆ A` follows from `A'' ⊆ leftNbhd A G b₀ ⊆ A`; and the doubling bound
`#(A''-A'') ≤ C₂ K^c #A''` is the proven `card_diffSet_le_of_reps_ge` applied with the supplied
threshold `t`, size relation `#A'' ≤ s·t`, and representation lower bound, using `s ≤ C₂ K^c`.

The implication is valid, and its contrapositive is how `drcRefinedReps_false` is derived; but
since `DRCRefinedReps` is false for all constants, it supplies no instance of `BareDRCExtract`. -/
theorem bareDRCExtract_of_refinedReps {C₁ C₂ c : ℕ} (hR : DRCRefinedReps C₁ C₂ c) :
    BareDRCExtract C₁ C₂ c := by
  intro α _ _ A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  classical
  obtain ⟨A'', t, s, hsub, hne, ht, hsbd, hsize, hst, hreps⟩ :=
    hR A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  -- containment `A'' ⊆ A`
  have hsubA : A'' ⊆ A := hsub.trans (Finset.filter_subset _ _)
  refine ⟨A'', hsubA, hne, hsize, ?_⟩
  -- doubling: `#(A''-A'') ≤ s·#A''` from E4b, then `s ≤ C₂K^c`.
  have hdoub : #(A'' - A'') ≤ s * #A'' := card_diffSet_le_of_reps_ge A'' t s ht hst hreps
  calc #(A'' - A'') ≤ s * #A'' := hdoub
    _ ≤ (C₂ * K ^ c) * #A'' := Nat.mul_le_mul_right _ hsbd
    _ = C₂ * K ^ c * #A'' := by ring

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.card_goodPairs_ge
#print axioms Finset.BSG.card_diffSet_mul_le_of_reps_ge
#print axioms Finset.BSG.card_diffSet_le_of_reps_ge
#print axioms Finset.BSG.bareDRCExtract_of_refinedReps
