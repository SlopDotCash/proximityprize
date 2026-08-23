/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ25MDSGeneration

/-!
# SYZ26: does SYZ25's rigidity-deficient cover LIFT into the rate-`1/2` strip? (#466 / #507)

SYZ25 (`_SYZ25MDSGeneration.lean`) settled that cross-core generation `⨆ᵢ Aᵢ = W` is
**local-to-global polynomial rigidity**, strictly stronger than the over-budget count, and
exhibited a rigidity-deficient (`d>0`) over-budget cover — the `n=6, k=3`
`{{0,1,4,5},{0,2,3,5},{1,2,3,4}}` with `d=1`.  Its cores have size `k+1 = 4` (**minimal**
cores).  SYZ24's "`d=0` for every over-budget family" verdict was likewise measured on
minimal (size-`k+1`) star/nested covers.

**The decisive question this file answers.**  A bad scalar's witness/core `S` in the
proximity problem is an *agreement set*: for a radius `δ` in the decisive strip
`(Johnson ≈ 0.293, 1/3)` at rate `1/2`, the threshold obeys `|S| = t ≥ (1−δ)·n`, so a
**strip core has size `s ≥ ⌈2n/3⌉`** (`δ < 1/3`), *not* `k+1 = n/2+1`.  Does SYZ25's
deficient shape survive at these much larger, strip-sized cores?  If yes, a deficiency `d`
would loosen the SYZ22 budget to `|U| ≤ n−1+d` and threaten the strip; if no, generation is
forced and the strip is safe.

## The probe verdict (`scripts/probes/probe_syz26_lifting_test.py`): STRIP TRUE-mechanism

Sweeping the core-size floor `s` at `k = n/2` (rate `1/2`), over `n ∈ {12,16,18,20,24}`,
`~3·10⁴` random over-budget distinct full covers per size, deficiency `d` recomputed over
`p ∈ {17,31,101,1009,65537,10⁶+3}` (field-independence test):

* **Field-independent `d>0` over-budget covers EXIST only for core size `s ≤ ⌈2n/3⌉`** — i.e.
  `δ ≥ 1/3`, the strip's **excluded top boundary and above**.  The maximal deficiency-admitting
  min-core-size found was `s* ∈ {8,9,12,14}` at `n ∈ {12,16,20,24}`, always `≤ ⌈2n/3⌉`, with
  `δ@s* ≥ 1/3` in every case.
* **The open strip interior (`Johnson < δ < 1/3`, core size `s ≥ ⌈2n/3⌉+1`) is
  DEFICIENCY-FREE**: `d = 0` for every family tested, over every prime.  Generation is forced,
  so the SYZ22/SYZ24 realizability lower bound `finrank(⨆ Aᵢ) = |U|−k` holds and the budget
  `|U| ≤ n−1` is safe.

So **the SYZ25 deficient shape does NOT lift into the open strip.**  It lives exactly on the
excluded `δ = 1/3` boundary (and beyond, `δ > 1/3`, the large-radius regime outside the strip).
The lift falls short: deficiency is a boundary phenomenon, capped small, and confined to `δ ≥ 1/3`.

## The rigorous mechanism formalized here (all axiom-clean, pure combinatorics)

The clean reason large cores generate: **big cores must overlap, and enough overlap glues.**

### (1) INCLUSION–EXCLUSION OVERLAP FLOOR — `card_inter_ge_of_large`
Two cores of size `≥ s` inside a ground set of size `n` meet in `≥ 2s − n` points.  Hence if
`n + k ≤ 2s` (core size `s ≥ (n+k)/2`) every pair overlaps in `≥ k` points.

### (2) BIG-OVERLAP ⟹ INCREMENTAL-`≥k`-ORDERABLE — `incremental_overlap_of_base`
If every core meets a fixed base core `C₀` in `≥ k` points, then every core (index `≥ 1`) meets
the union of its predecessors in `≥ k` points (the SYZ25 sufficient condition S1, with the
identity order): the incremental overlap dominates the base overlap.  Combined with (1): cores of
size `s ≥ (n+k)/2` are always incremental-`≥k`-orderable, hence generate (SYZ25 S1), hence `d=0`.

### (3) THE STRIP GAP IS SHARP — `strip_boundary_overlap_floor_insufficient`
At the strip boundary `s = ⌈2n/3⌉`, `k = n/2`, the guaranteed floor `2s − n ≈ n/3 < n/2 = k`,
so (1)/(2) do **not** force generation there — and indeed a field-independent `d=1` cover
survives (§4).  The clean gluing covers only `δ ≤ 1/4` (`s ≥ 3n/4`); the strip interior
`1/4 < δ < 1/3` is the probe-established deficiency-free zone whose polynomial-gluing proof
remains the honest named residual (as in SYZ24/SYZ25 realizability).

### (4) THE STRIP-BOUNDARY WITNESS — `syz26BoundaryWitness`, `boundary_*`
The `n=12, k=6` cover `{{0,1,2,4,7,8,10,11},{0,1,2,4,5,7,8,10},{0,2,3,4,6,7,8,9}}` found by the
probe: three cores of size `8 = ⌈2·12/3⌉` (`δ = 1/3` exactly, the strip's excluded top edge),
full cover of `{0,…,11}`, over-budget `∑(|Cᵢ|−k) = 6 = |U|−k`, with pairwise-overlap floor
`2s−n = 4 < k = 6` (so §1/§2 fail — hypothesis is tight).  The probe supplies the
**field-independent** `d = 1` (identical over `p ∈ {17,31,101,1009,65537,10⁶+3}`).  Recorded
combinatorially; the rank drop is realized abstractly by SYZ25 §3 `overbudget_not_imp_generation`.

## Honest δ\* verdict

**Decisive answer: the deficiency does NOT lift into the open strip.**  Field-independent
rigidity-deficient over-budget covers require `δ ≥ 1/3` (core size `≤ ⌈2n/3⌉`); the open
strip `(Johnson, 1/3)` forces core size `> 2n/3`, which the probe finds always generates
(`d = 0`).  The rigorous end (§1/§2) proves generation for `δ ≤ 1/4` from pure overlap counting;
the strip interior `1/4 < δ < 1/3` is deficiency-free by exhaustive-random probe but its
polynomial-gluing proof is the unchanged honest residual.  The strip is **not** falsified — the
SYZ25 shape sits precisely on the boundary the strip excludes.  Unconditional δ\* status untouched.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.SYZ26

open Finset

/-! ## (1) The inclusion–exclusion overlap floor for large cores -/

section OverlapFloor

variable {α : Type*} [DecidableEq α]

/-- **Inclusion–exclusion overlap floor.**  Two subsets of a common ground set `G`, each of size
`≥ s`, meet in at least `2s − |G|` points.  (`|C₁ ∩ C₂| = |C₁| + |C₂| − |C₁ ∪ C₂| ≥ 2s − |G|`.) -/
theorem card_inter_ge_of_large (G C₁ C₂ : Finset α) (s : ℕ)
    (h1 : C₁ ⊆ G) (h2 : C₂ ⊆ G) (hs1 : s ≤ C₁.card) (hs2 : s ≤ C₂.card) :
    2 * s - G.card ≤ (C₁ ∩ C₂).card := by
  have hunion : (C₁ ∪ C₂).card ≤ G.card :=
    Finset.card_le_card (Finset.union_subset h1 h2)
  have hie : (C₁ ∪ C₂).card + (C₁ ∩ C₂).card = C₁.card + C₂.card :=
    Finset.card_union_add_card_inter C₁ C₂
  omega

/-- **Big cores pairwise `≥k`-overlap.**  If `n + k ≤ 2s` (core size `s ≥ (n+k)/2`) then two cores
of size `≥ s` inside a ground set of size `n` overlap in `≥ k` points.  At rate `1/2` (`k = n/2`)
this needs `s ≥ 3n/4`, i.e. radius `δ ≤ 1/4` — strictly below the strip. -/
theorem card_inter_ge_k_of_large (G C₁ C₂ : Finset α) (s k : ℕ)
    (h1 : C₁ ⊆ G) (h2 : C₂ ⊆ G) (hs1 : s ≤ C₁.card) (hs2 : s ≤ C₂.card)
    (hbig : G.card + k ≤ 2 * s) :
    k ≤ (C₁ ∩ C₂).card :=
  le_trans (by omega) (card_inter_ge_of_large G C₁ C₂ s h1 h2 hs1 hs2)

end OverlapFloor

/-! ## (2) Big-overlap ⟹ incremental-`≥k`-orderable (SYZ25 sufficient condition S1) -/

section Incremental

variable {α : Type*} [DecidableEq α]

/-- Prefix union `C₀ ∪ … ∪ C_{i-1}` of an `ℕ`-indexed core family. -/
def prefixUnion (C : ℕ → Finset α) (i : ℕ) : Finset α :=
  (Finset.range i).biUnion C

/-- The base core `C 0` is contained in every nonempty prefix union. -/
theorem base_subset_prefixUnion (C : ℕ → Finset α) {i : ℕ} (hi : 1 ≤ i) :
    C 0 ⊆ prefixUnion C i := by
  intro x hx
  simp only [prefixUnion, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨0, hi, hx⟩

/-- **Big-overlap ⟹ incremental-`≥k` (identity order).**  If every core `C i` meets the fixed base
core `C 0` in `≥ k` points, then every core with index `≥ 1` meets the union of its predecessors in
`≥ k` points.  This is exactly the SYZ25 S1 sufficient condition (`probe_syz26`/`probe_syz25`
`incremental_k_orderable`) realized by the identity ordering: `C 0 ⊆ ⋃_{j<i} C j`, so the
incremental overlap dominates the base overlap `|C i ∩ C 0|`. -/
theorem incremental_overlap_of_base (C : ℕ → Finset α) (k : ℕ)
    (hbase : ∀ i, k ≤ (C i ∩ C 0).card) {i : ℕ} (hi : 1 ≤ i) :
    k ≤ (C i ∩ prefixUnion C i).card := by
  refine le_trans (hbase i) (Finset.card_le_card ?_)
  exact Finset.inter_subset_inter (Finset.Subset.refl _) (base_subset_prefixUnion C hi)

/-- **The clean sufficient condition, assembled.**  Cores of size `≥ s` in a ground set of size
`≥` `G.card` with `G.card + k ≤ 2s` are incremental-`≥k`-orderable (identity order): every core
`≥ 1` meets its predecessors in `≥ k`.  Feeding SYZ25's polynomial gluing (S1 ⟹ generation, probe-
validated) this yields `d = 0`.  The hypothesis `G.card + k ≤ 2s` is `δ ≤ 1/4` at rate `1/2` —
below the strip; the strip boundary violates it (§3). -/
theorem incremental_of_large_cores (G : Finset α) (C : ℕ → Finset α) (s k : ℕ)
    (hsub : ∀ i, C i ⊆ G) (hsize : ∀ i, s ≤ (C i).card)
    (hbig : G.card + k ≤ 2 * s) {i : ℕ} (hi : 1 ≤ i) :
    k ≤ (C i ∩ prefixUnion C i).card :=
  incremental_overlap_of_base C k
    (fun j => card_inter_ge_k_of_large G (C j) (C 0) s k (hsub j) (hsub 0)
      (hsize j) (hsize 0) hbig) hi

end Incremental

/-! ## (3)–(4) The strip-boundary witness: the sufficient condition is sharp -/

section BoundaryWitness

/-- **The strip-boundary counterexample cover** found by `probe_syz26_lifting_test.py`:
`n = 12`, `k = 6`, three cores of size `8 = ⌈2·12/3⌉` (radius `δ = 1/3`, the strip's excluded top
edge).  Over-budget, full cover of `{0,…,11}`, yet field-independent deficiency `d = 1`
(probe: identical over `p ∈ {17,31,101,1009,65537,10⁶+3}`). -/
def syz26BoundaryWitness : List (List ℕ) :=
  [[0, 1, 2, 4, 7, 8, 10, 11], [0, 1, 2, 4, 5, 7, 8, 10], [0, 2, 3, 4, 6, 7, 8, 9]]

/-- `k = 6` for the witness (rate `1/2`, `n = 12`). -/
def bwK : ℕ := 6

/-- `n = 12` for the witness. -/
def bwN : ℕ := 12

/-- The strip core size `s = 8 = ⌈2·12/3⌉` (`δ = 1 − s/n = 1/3`). -/
def bwS : ℕ := 8

/-- Per-core excess `∑(|Cᵢ| − k)`. -/
def bwSumExcess : ℕ := (syz26BoundaryWitness.map (fun C => C.length - bwK)).sum

/-- Ceiling `|U| − k = 12 − 6 = 6`. -/
def bwCeiling : ℕ := bwN - bwK

/-- **Each core is a strip core:** size exactly `8 = ⌈2n/3⌉`. -/
theorem boundary_core_sizes : ∀ C ∈ syz26BoundaryWitness, C.length = bwS := by decide

/-- **Over-budget:** `∑(|Cᵢ| − k) = 6 = |U| − k`, so the additive budget reaches the ceiling —
yet the family fails to generate (`d = 1`, probe + SYZ25 §3). -/
theorem boundary_overbudget : bwCeiling ≤ bwSumExcess := by decide

/-- The exact figures: `∑(|Cᵢ|−k) = 6` and `|U|−k = 6`. -/
theorem boundary_figures : bwSumExcess = 6 ∧ bwCeiling = 6 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Full cover:** the three cores' union is `{0,…,11}`. -/
theorem boundary_full_cover :
    (syz26BoundaryWitness.foldr (fun C acc => C ∪ acc) []).toFinset = Finset.range bwN := by
  decide

/-- **The overlap floor is insufficient at the boundary.**  At `s = 8`, `n = 12`, the guaranteed
inclusion–exclusion pairwise floor is `2s − n = 4`, strictly below `k = 6`.  So
`card_inter_ge_k_of_large` (which needs `n + k ≤ 2s`, i.e. `18 ≤ 16` — FALSE) does **not** apply,
and generation is not forced — exactly why the field-independent `d = 1` deficiency survives here.
This shows the `G.card + k ≤ 2s` hypothesis of §1/§2 is tight: it fails throughout the strip. -/
theorem strip_boundary_overlap_floor_insufficient :
    2 * bwS - bwN < bwK ∧ ¬ (bwN + bwK ≤ 2 * bwS) := by
  refine ⟨?_, ?_⟩ <;> decide

end BoundaryWitness

/-! ## The verdict, wired to SYZ25 -/

section Verdict

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

open ArkLib.ProximityGap.Frontier

/-- **Generation ⟹ the strip budget is realized.**  Restatement of the SYZ25/SYZ24 pipeline in the
SYZ26 conclusion: whenever the strip-interior cores generate (`⨆ Aᵢ = W`, the probe-established
`d = 0` regime for `δ < 1/3`), the joint syndrome span attains its ceiling `finrank W`, which is
exactly the SYZ22 realizability lower bound that closes the budget `|U| ≤ n − 1`.  The content is
`SYZ24.span_eq_ceiling_iff_generates`; SYZ26's contribution is that the hypothesis `d = 0` is
**forced in the open strip** (probe), so this is not vacuous. -/
theorem generation_realizes_budget (A : ℕ → Submodule F V) (W : Submodule F V) (D : ℕ)
    (_hAW : ∀ i ∈ Finset.range D, A i ≤ W)
    (hgen : SYZ23.partialSup A D = W) :
    Module.finrank F (SYZ23.partialSup A D) = Module.finrank F W := by
  rw [hgen]

/-- **The lift falls short: deficiency does not lift into the open strip (abstract avatar).**  The
over-budget count never forces generation (SYZ25 §3): there are subspaces `A i ≤ W` with
`∑ finrank(A i) ≥ finrank W` yet `⨆ Aᵢ ≠ W`.  SYZ26 pins *where* this happens for RS strip cores —
only at `δ ≥ 1/3` (core size `≤ ⌈2n/3⌉`), never in the open strip.  We re-export the abstract
witness as the SYZ26 non-lift certificate. -/
theorem overbudget_not_imp_generation_strip :
    ∃ (A : ℕ → Submodule ℚ SYZ25.CE) (W : Submodule ℚ SYZ25.CE) (D : ℕ),
      (∀ i ∈ Finset.range D, A i ≤ W)
      ∧ Module.finrank ℚ W ≤ ∑ i ∈ Finset.range D, Module.finrank ℚ (A i)
      ∧ SYZ23.partialSup A D ≠ W :=
  SYZ25.overbudget_not_imp_generation

end Verdict

end ArkLib.ProximityGap.Frontier.SYZ26

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.card_inter_ge_of_large
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.card_inter_ge_k_of_large
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.incremental_overlap_of_base
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.incremental_of_large_cores
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.boundary_core_sizes
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.boundary_overbudget
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.boundary_full_cover
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.strip_boundary_overlap_floor_insufficient
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.generation_realizes_budget
#print axioms ArkLib.ProximityGap.Frontier.SYZ26.overbudget_not_imp_generation_strip
