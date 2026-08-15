/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ21ShorteningAndCoverage
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# SYZ23: directness of the anchored-annihilator sum — dual distance, the honest sum
  lower bound, and why support-cardinality accounting leaks (issue #466 / #507)

SYZ22 (`_SYZ22StripBridge.lean`) reduced the rate-`1/2` decisive strip `(Johnson, 1/3)` to a
single residual: a **lower bound** on the joint span dimension of an over-budget family's
syndrome functionals (`SuperadditiveUnion.union_span_rank`, currently a *hypothesis* field).
SYZ20's `plantable_span_cap` supplies the matching upper bound `finrank (span) + 1 ≤ 2(n−k)`
unconditionally; the strip closes iff the lower bound `finrank (span) ≥ 2(|U|−k)` (equivalently,
`≥ ∑ᵢ (|Cᵢ|−k)` up to the inclusion–exclusion correction) can be *proved* for an actual family.

That lower bound is exactly a **directness** statement about the anchored dual-annihilator
subspaces
  `Aᵢ := dualAnnihilator (range (evalOnS α k Cᵢ))`  (dual codewords supported inside `Cᵢ`).
If the sum `∑ᵢ Aᵢ` were *direct*, its dimension would be `∑ᵢ (|Cᵢ|−k)`, which — combined with
the merge/union budget — closes the strip. This file works that directness out honestly.

## What is proven here

### (1) DUAL DISTANCE — `anchored_dual_small_support_eq_bot` / `_eq_zero`
A dual codeword of `RS[α,k]` supported inside a set `W` with `|W| ≤ k` is **zero**. This is a
three-line consequence of SYZ21's `shortening_dim_of_card_le` (the anchored annihilator has
`finrank 0`, hence is `⊥`). It is the primal route to the MDS dual distance `k+1`.

### (2) PAIRWISE DIRECTNESS — `pairwise_direct_of_inter_zero`
If two anchored spaces meet in `finrank 0` (delivered by (1) whenever their supports intersect
in `≤ k` points), their sum is a direct sum: `finrank (A ⊔ B) = finrank A + finrank B`. Pure
linear algebra via `finrank_sup_add_finrank_inf_eq`.

### (3) THE HONEST SUM LOWER BOUND — `finrank_iSup_ge_sum_sub_overlaps`
For **any** finite family of subspaces `A : ℕ → Submodule F V`, an exact inclusion–exclusion
lower bound, provable by induction from the modular law:

  `∑_{i<D} finrank (A i)  ≤  finrank (⨆_{i<D} A i) + ∑_{i<D} finrank (A i ⊓ ⨆_{j<i} A j)`.

Equivalently `finrank (⨆ Aᵢ) ≥ ∑ finrank(Aᵢ) − ∑ finrank(Aᵢ ⊓ Σ_{j<i}Aⱼ)`. This is the
induction the campaign asked for: it charges the joint span by the per-core dimensions **minus
the incremental overlaps** — and it is the *correct* accounting. The residual is now sharply
localised: **bound the overlap terms** `finrank (Aᵢ ⊓ ⨆_{j<i} Aⱼ)`.

### (4) THE LEAK — `support_accounting_leaks_strip`
The natural attempt is to bound each overlap term by the SYZ21 shortening dimension of the
*support intersection*: `finrank (Aᵢ ⊓ ⨆_{j<i} Aⱼ) ≤ max(0, |Cᵢ ∩ ∪_{j<i}Cⱼ| − k)` (true, since
the intersection is supported in `Cᵢ ∩ ∪_{j<i}Cⱼ`). **This bound is too weak and the resulting
LP leaks across the entire strip.** A core whose support *nests* inside the union of its
predecessors (`|Cᵢ ∩ ∪Cⱼ| = |Cᵢ|`, realizable by spreading `Cᵢ` over `⌈|Cᵢ|/(k−1)⌉`
predecessors, each sharing `≤ k−1`) has support-overlap cost

  `(|Cᵢ|−k) − max(0, |Cᵢ|−k)  =  0`   (`crudeCost_nested`),

yet positive bad-scalar yield. So arbitrarily many nested cores drive the support-accounting
lower bound to a **bounded** constant while the certified yield grows without bound. We exhibit
a concrete support-consistent profile at `n = 64, k = 32, t = 45` whose support-lower-bound is
`≤ n−k−1 = 31` but whose yield is `> B = 64` (`support_accounting_leaks_strip`), and the general
`crudeCost_nested` shows the leak is not a boundary artifact — it is present throughout
`(0, 1/2)`.

## Honest δ\* verdict

The pure **support-cardinality** accounting *cannot* close the strip: directness of `∑ Aᵢ` is a
genuine **linear-algebra** fact about GRS dual codes (MDS position of the anchored annihilators),
**not** reducible to counting `|Cᵢ ∩ ∪Cⱼ|`. This sharpens SYZ22's residual: the missing
`union_span_rank` lower bound is precisely the statement that the overlap terms
`finrank (Aᵢ ⊓ ⨆_{j<i} Aⱼ)` are governed by the MDS structure (they vanish pairwise by (1)/(2),
but for `D ≥ 3` the union support can exceed `k`, and the true overlap is *smaller* than the
support bound — that gap is the fact G87 abstracts as "abstract-H realizability"). SYZ23 proves
the dual distance, the pairwise directness, and the correct sum lower bound unconditionally, and
proves the support-only route dead. The unconditional δ\* status is untouched.

Axiom-clean; `#print axioms` at the bottom. No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.SYZ23

open Module Submodule ArkLib.CS25
open ArkLib.ProximityGap.Frontier.SYZ21

/-! ## (1) Dual distance: an anchored dual codeword on `≤ k` points is zero -/

section DualDistance

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]

/-- **Dual distance (annihilator form).**  The space of dual codewords of `RS[α,k]` supported
inside a set `W` with `|W| ≤ k` is the zero subspace.  Immediate from SYZ21's
`shortening_dim_of_card_le` (`finrank 0`) via `Submodule.finrank_eq_zero`. -/
theorem anchored_dual_small_support_eq_bot (α : ι ↪ F) (k : ℕ) (W : Finset ι) (hW : W.card ≤ k) :
    Submodule.dualAnnihilator (LinearMap.range (evalOnS α k W)) = ⊥ := by
  classical
  haveI : FiniteDimensional F (W → F) := inferInstance
  have h0 : finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k W))) = 0 :=
    shortening_dim_of_card_le α k W hW
  exact Submodule.finrank_eq_zero.mp h0

/-- **Dual distance (element form).**  Any dual codeword supported inside `W`, `|W| ≤ k`, is `0`.
The MDS/GRS dual distance `k+1`, obtained via SYZ21's primal shortening route. -/
theorem anchored_dual_small_support_eq_zero (α : ι ↪ F) (k : ℕ) (W : Finset ι) (hW : W.card ≤ k)
    (φ : Module.Dual F (W → F)) (hφ : φ ∈ Submodule.dualAnnihilator (LinearMap.range (evalOnS α k W))) :
    φ = 0 := by
  have hbot := anchored_dual_small_support_eq_bot α k W hW
  rw [hbot] at hφ
  simpa using hφ

end DualDistance

/-! ## (2) Pairwise directness from a zero intersection -/

section Pairwise

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **Zero-intersection ⟹ trivial intersection.**  A finite-dimensional subspace intersection of
`finrank 0` is `⊥`. -/
theorem inf_eq_bot_of_finrank_zero (A B : Submodule F V) (h : finrank F (A ⊓ B : Submodule F V) = 0) :
    (A ⊓ B : Submodule F V) = ⊥ :=
  Submodule.finrank_eq_zero.mp h

/-- **Pairwise directness.**  If two subspaces meet in `finrank 0` (e.g. two anchored
dual-annihilators whose supports intersect in `≤ k` points, by dual distance), their sum is
direct: `finrank (A ⊔ B) = finrank A + finrank B`. -/
theorem pairwise_direct_of_inter_zero (A B : Submodule F V)
    (h : finrank F (A ⊓ B : Submodule F V) = 0) :
    finrank F (A ⊔ B : Submodule F V) = finrank F A + finrank F B := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [h] at hsum
  omega

end Pairwise

/-! ## (3) The honest inclusion–exclusion lower bound on the joint span -/

section SumLowerBound

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The partial union of the first `n` subspaces of a family `A : ℕ → Submodule F V`. -/
def partialSup (A : ℕ → Submodule F V) (n : ℕ) : Submodule F V :=
  ⨆ j ∈ Finset.range n, A j

@[simp] theorem partialSup_zero (A : ℕ → Submodule F V) : partialSup A 0 = ⊥ := by
  simp [partialSup]

theorem partialSup_succ (A : ℕ → Submodule F V) (n : ℕ) :
    partialSup A (n + 1) = A n ⊔ partialSup A n := by
  rw [partialSup, partialSup, Finset.range_add_one, Finset.iSup_insert]

/-- **The honest sum lower bound (inclusion–exclusion).**  For any finite family of subspaces of
a finite-dimensional space, the sum of the per-subspace dimensions is bounded above by the joint
span dimension plus the sum of the *incremental overlaps* `finrank (A i ⊓ (⨆_{j<i} A j))`.

Rearranged: `finrank (⨆_{i<D} A i) ≥ ∑_{i<D} finrank (A i) − ∑_{i<D} finrank (A i ⊓ ⨆_{j<i} A j)`.
This is the correct charge of the joint syndrome span by the per-core shortening dimensions,
minus the overlaps.  Proven by induction on `D` from the modular law
`finrank_sup_add_finrank_inf_eq`. -/
theorem finrank_iSup_ge_sum_sub_overlaps (A : ℕ → Submodule F V) (D : ℕ) :
    ∑ i ∈ Finset.range D, finrank F (A i)
      ≤ finrank F (partialSup A D)
        + ∑ i ∈ Finset.range D, finrank F (A i ⊓ partialSup A i : Submodule F V) := by
  induction D with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    -- modular law on the top step: A n ⊔ P n
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq (A n) (partialSup A n)
    rw [← partialSup_succ A n] at hmod
    -- hmod : finrank (P (n+1)) + finrank (A n ⊓ P n) = finrank (A n) + finrank (P n)
    -- IH : ∑_{i<n} finrank (A i) ≤ finrank (P n) + ∑_{i<n} overlap i
    omega

/-- **Directness corollary.**  If every incremental overlap vanishes (the sum is direct), the
joint span dimension equals the sum of the per-subspace dimensions — the additive budget the
strip closure wants. -/
theorem finrank_iSup_eq_sum_of_direct (A : ℕ → Submodule F V) (D : ℕ)
    (hdir : ∀ i ∈ Finset.range D, finrank F (A i ⊓ partialSup A i : Submodule F V) = 0) :
    ∑ i ∈ Finset.range D, finrank F (A i) ≤ finrank F (partialSup A D) := by
  have h := finrank_iSup_ge_sum_sub_overlaps A D
  have hz : ∑ i ∈ Finset.range D, finrank F (A i ⊓ partialSup A i : Submodule F V) = 0 :=
    Finset.sum_eq_zero hdir
  omega

end SumLowerBound

/-! ## (4) The leak: support-cardinality accounting cannot close the strip -/

section Leak

/-- Bad-scalar yield of one core of size `s` (length `n`, threshold `t`, truncated `ℕ`). -/
def yieldS (n t s : ℕ) : ℕ := if t ≤ s then n - s else (n - s) / (t - s)

/-- The **support-overlap cost** of a core of size `s` whose support meets the running union in
`o` points: the SYZ21 shortening bound `max(0,s−k)` minus the support-intersection bound
`max(0,o−k)`, the only per-core charge the support-cardinality accounting can force. -/
def crudeCost (k s o : ℕ) : ℕ := (s - k) - (o - k)

/-- **Nested cores are free under support accounting.**  A core whose support is fully contained
in the running union (`o = s ≥ k`) has support-overlap cost `0`.  This is the leak mechanism: it
holds for *every* `k ≤ s`, at every rate — not a strip-boundary artifact. -/
theorem crudeCost_nested (k s : ℕ) (h : k ≤ s) : crudeCost k s s = 0 := by
  simp only [crudeCost]; omega

/-- Total support-overlap cost of an ordered profile (list of `(size, running-overlap)`). -/
def profileCost (k : ℕ) (P : List (ℕ × ℕ)) : ℕ :=
  (P.map (fun p => crudeCost k p.1 p.2)).sum

/-- Total certified yield of a profile. -/
def profileYield (n t : ℕ) (P : List (ℕ × ℕ)) : ℕ :=
  (P.map (fun p => yieldS n t p.1)).sum

/-- A concrete support-consistent leak profile at `n = 64, k = 32`: two seed cores of size `33`
(running overlap `0`), then `63` nested cores of size `33` (running overlap `33`, realizable
since two predecessors of size `33` each share `≤ 31 = k−1` with the nested core and their union
has `≥ 33` points). -/
def leakProfile64 : List (ℕ × ℕ) :=
  (List.replicate 2 (33, 0)) ++ (List.replicate 63 (33, 33))

/-- **The strip does not close under support-cardinality accounting (`n = 64, k = 32, t = 45`).**
The support-overlap lower bound on the joint span for `leakProfile64` is `2 ≤ n−k−1 = 31`
(well within the `plantable_span_cap` ceiling), yet the certified bad-scalar yield is
`130 > B = 64`.  So the support accounting fails to force the span large enough to invoke the
cap: it cannot certify the strip.  (Contrast: the *correct* accounting of §3 needs the true
overlap `finrank (Aᵢ ⊓ ⨆Aⱼ)`, which the support bound `max(0,o−k)` overestimates for nested
cores.) -/
theorem support_accounting_leaks_strip :
    profileCost 32 leakProfile64 ≤ 64 - 32 - 1 ∧ 64 < profileYield 64 45 leakProfile64 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The nested tail carries all the yield at zero support cost: dropping the two seeds, a family
of `D` nested size-`33` cores has support cost `0` and yield `2·D` — unbounded in `D` while the
support lower bound stays `0`.  (General-`D` form of the leak; instantiated for the concrete
`decide` certificate above.) -/
theorem nested_tail_cost_zero (D : ℕ) :
    profileCost 32 (List.replicate D (33, 33)) = 0 := by
  simp [profileCost, List.map_replicate, List.sum_replicate, crudeCost]

end Leak

end ArkLib.ProximityGap.Frontier.SYZ23

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.anchored_dual_small_support_eq_bot
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.anchored_dual_small_support_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.pairwise_direct_of_inter_zero
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.finrank_iSup_ge_sum_sub_overlaps
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.finrank_iSup_eq_sum_of_direct
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.crudeCost_nested
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.support_accounting_leaks_strip
#print axioms ArkLib.ProximityGap.Frontier.SYZ23.nested_tail_cost_zero
