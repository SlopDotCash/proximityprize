/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilHarvestCap

/-!
# Fiber-Chebyshev refinement: the `(k−1)` vote cap on foreign aligned regions —
# and the honest refutation of the boundary-moving hope

Issue #466, P1 rate-quarter — tenth round of the 2026-07-11 session, executing
the cross-cone round's bonus finding.

**The mechanism, audited exactly** (probe
`scripts/probes/probe_rate_quarter_p1_fiber_chebyshev.py`):

* The `(k−1)` fiber cap requires the fiber to be the zero set of a NONZERO
  deg `< k` polynomial — i.e. BOTH components of the ratio map must be
  codewords.
* **Codeword-pair case (REAL, this file)**: a rider `γ` of pencil `a` voting at
  a coordinate of pencil `b`'s aligned region satisfies
  `(wb₀ − wa₀)(i) + γ·(wb₁ − wa₁)(i) = 0` — the zero set of the CODEWORD
  `r₀ + γ·r₁`.  For every non-exceptional `γ` (all but at most the single
  proportionality scalar) the foreign votes number `≤ k − 1`
  (`foreign_vote_fiber_le`; cap TIGHT at μ_256: fiber `= k−1` realized).
* **U-relative case (REFUTED, honesty-critical)**: the derecursion stall
  ledger's ratio map `ρ = (u₁ − w)/D` has NEITHER component a codeword; an
  adversarial `u₁ = w + s₀·D` on 200 coordinates realizes a fiber of size
  `200 ≫ k − 1 = 63` at μ_256.  **The stall boundary `F₀ = 75018133` does NOT
  move by this mechanism** — the coordinator's step-(1) recomputation hope is
  refuted, and no such recomputation is attempted here.

**Kernel-checked** (prize shape):

* `codeword_zero_set_le` — a nonzero codeword has `≤ k − 1` zeros (via
  `predecessor_sep` against the zero codeword).
* `foreign_vote_fiber_le` — non-exceptional riders collect `≤ k − 1` votes
  inside a foreign aligned region.
* `exceptional_scalar_subsingleton` — at most one exceptional scalar per
  pencil pair.
* `foreign_region_rider_energy` — **the fiber-Chebyshev second moment**: any
  set `S` of non-exceptional scalars each collecting `≥ m` foreign votes in
  `R` satisfies `S.card · m² ≤ (k−1)·|R|` — refining the disjointness bound
  `S.card · m ≤ |R|` exactly when `m > k − 1`.
* `no_fully_foreign_rider` — since `k − 1 < N − T`, no non-exceptional rider
  can collect `N − T`-scale votes inside one foreign aligned region
  (`k − 1 = 268435455 < 480946858 = N − T`).
* Rungs: `refinement_crossover` (effective iff `A < T − k + 1 = 324359511`;
  the pair-pencil floor `2T − N = 111848108` is deep inside),
  `refinement_factor_floor`, `no_fully_foreign_ledger`
  (`(k−1)(T−1) < (N−T)²`).

**What does NOT change** (honesty): the derecursion boundary `F₀`, the stall
band, `SwarmResidual`, and δ* are all untouched.  The refinement bounds
foreign-region votes (the covered slice of the swarm); swarm members voting on
junk/uncovered coordinates are not constrained — the residual is NOT
redefined.  Bracket `3/8 ≤ δ* ≤ 43/96 + ε` untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterFiberChebyshevRefinement

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

local instance localInstance_P1RateQuarterFiberChebyshevRefinement_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterFiberChebyshevRefinement_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The codeword fiber cap -/

section FiberCap

variable (dom : Fin N ↪ F)

/-- A nonzero codeword has at most `k − 1` zeros (on any subset): `k` zeros
would make it agree with the zero codeword on `k` points, forcing it to vanish
(`predecessor_sep`). -/
theorem codeword_zero_set_le {v : Fin N → F} (hv : v ∈ predecessorCode dom)
    (hne : v ≠ 0) (S : Finset (Fin N)) :
    (S.filter (fun i => v i = 0)).card ≤ k - 1 := by
  classical
  by_contra hbig
  push Not at hbig
  have hk : k ≤ (S.filter (fun i => v i = 0)).card := by
    have hk0 : 0 < k := by norm_num [k]
    omega
  refine hne (predecessor_sep dom v hv 0 (Submodule.zero_mem _)
    (S.filter (fun i => v i = 0)) hk (fun x hx => ?_))
  simpa using (Finset.mem_filter.mp hx).2

/-- **The foreign-vote fiber cap**: a rider `γ` of pencil `(wa₀, wa₁)` whose
combination `r₀ + γ·r₁` of the difference rows (`r = wb − wa`) is nonzero
collects at most `k − 1` votes inside pencil `(wb₀, wb₁)`'s aligned region. -/
theorem foreign_vote_fiber_le (u₀ u₁ : Fin N → F)
    {wa₀ wa₁ wb₀ wb₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (γ : F)
    (hexc : (wb₀ - wa₀) + γ • (wb₁ - wa₁) ≠ 0) :
    (voteSet u₀ u₁ wa₀ wa₁ γ ∩ alignedSet u₀ u₁ wb₀ wb₁).card ≤ k - 1 := by
  classical
  have hv : (wb₀ - wa₀) + γ • (wb₁ - wa₁) ∈ predecessorCode dom :=
    Submodule.add_mem _ (Submodule.sub_mem _ hwb₀ hwa₀)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ hwb₁ hwa₁))
  have hsub : voteSet u₀ u₁ wa₀ wa₁ γ ∩ alignedSet u₀ u₁ wb₀ wb₁ ⊆
      Finset.univ.filter
        (fun i => ((wb₀ - wa₀) + γ • (wb₁ - wa₁)) i = 0) := by
    intro i hi
    obtain ⟨hvote, halign⟩ := Finset.mem_inter.mp hi
    rw [mem_voteSet_iff] at hvote
    rw [mem_alignedSet_iff] at halign
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h := hvote.2
    rw [← halign.1, ← halign.2] at h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination -h
  calc (voteSet u₀ u₁ wa₀ wa₁ γ ∩ alignedSet u₀ u₁ wb₀ wb₁).card
      ≤ (Finset.univ.filter
          (fun i => ((wb₀ - wa₀) + γ • (wb₁ - wa₁)) i = 0)).card :=
        Finset.card_le_card hsub
    _ ≤ k - 1 := codeword_zero_set_le dom hv hexc Finset.univ

/-- **At most one exceptional scalar** per distinct pencil pair: if
`r₀ + γ·r₁ = 0` and `r₀ + γ'·r₁ = 0` with `(r₀, r₁) ≠ (0, 0)`, then `γ = γ'`. -/
theorem exceptional_scalar_subsingleton {r₀ r₁ : Fin N → F}
    (hne : ¬ (r₀ = 0 ∧ r₁ = 0)) {γ γ' : F}
    (h : r₀ + γ • r₁ = 0) (h' : r₀ + γ' • r₁ = 0) :
    γ = γ' := by
  by_contra hγ
  have hr₁ : r₁ = 0 := by
    funext i
    have hi := congrFun h i
    have hi' := congrFun h' i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi hi'
    have hsub : (γ - γ') * r₁ i = 0 := by linear_combination hi - hi'
    rcases mul_eq_zero.mp hsub with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hγ
    · simpa using h0
  have hr₀ : r₀ = 0 := by
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      hr₁] at hi
    simpa using hi
  exact hne ⟨hr₀, hr₁⟩

end FiberCap

/-! ## The fiber-Chebyshev second moment -/

section Energy

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)

/-- **Fiber-Chebyshev rider energy**: a set `S` of non-exceptional scalars each
collecting at least `m` votes of pencil `a` inside pencil `b`'s aligned region
`R` satisfies `S.card · m² ≤ (k − 1)·|R|` — the second-moment refinement of
the disjointness bound `S.card · m ≤ |R|`, strictly better whenever
`m > k − 1`. -/
theorem foreign_region_rider_energy
    {wa₀ wa₁ wb₀ wb₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (S : Finset F) (m : ℕ)
    (hexc : ∀ γ ∈ S, (wb₀ - wa₀) + γ • (wb₁ - wa₁) ≠ 0)
    (hm : ∀ γ ∈ S,
      m ≤ (voteSet u₀ u₁ wa₀ wa₁ γ ∩ alignedSet u₀ u₁ wb₀ wb₁).card) :
    S.card * (m * m) ≤ (k - 1) * (alignedSet u₀ u₁ wb₀ wb₁).card := by
  classical
  set R := alignedSet u₀ u₁ wb₀ wb₁ with hR
  set c : F → ℕ := fun γ => (voteSet u₀ u₁ wa₀ wa₁ γ ∩ R).card with hc
  have hcap : ∀ γ ∈ S, c γ ≤ k - 1 := fun γ hγ =>
    foreign_vote_fiber_le dom u₀ u₁ hwa₀ hwa₁ hwb₀ hwb₁ γ (hexc γ hγ)
  have hdisj : ∀ γ ∈ S, ∀ γ' ∈ S, γ ≠ γ' →
      Disjoint (voteSet u₀ u₁ wa₀ wa₁ γ ∩ R)
        (voteSet u₀ u₁ wa₀ wa₁ γ' ∩ R) := by
    intro γ _ γ' _ hne
    exact Finset.disjoint_left.mpr fun i hi hi' =>
      (Finset.disjoint_left.mp (voteSet_disjoint u₀ u₁ wa₀ wa₁ hne))
        (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi').1
  have hsumR : ∑ γ ∈ S, c γ ≤ R.card := by
    calc ∑ γ ∈ S, c γ
        = (S.biUnion (fun γ => voteSet u₀ u₁ wa₀ wa₁ γ ∩ R)).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ R.card := Finset.card_le_card (by
          intro i hi
          obtain ⟨γ, _, hiγ⟩ := Finset.mem_biUnion.mp hi
          exact (Finset.mem_inter.mp hiγ).2)
  calc S.card * (m * m) = ∑ _γ ∈ S, m * m := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ S, c γ * (k - 1) :=
        Finset.sum_le_sum fun γ hγ =>
          Nat.mul_le_mul (hm γ hγ) ((hm γ hγ).trans (hcap γ hγ))
    _ = (∑ γ ∈ S, c γ) * (k - 1) := by rw [Finset.sum_mul]
    _ ≤ R.card * (k - 1) := Nat.mul_le_mul_right _ hsumR
    _ = (k - 1) * R.card := Nat.mul_comm _ _

/-- **No fully-foreign rider**: `k − 1 = 268435455 < 480946858 = N − T`, so a
non-exceptional rider can never collect `(N − T)`-scale votes inside a single
foreign aligned region — its fiber cap forbids it outright. -/
theorem no_fully_foreign_rider
    {wa₀ wa₁ wb₀ wb₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (γ : F) (hexc : (wb₀ - wa₀) + γ • (wb₁ - wa₁) ≠ 0) :
    (voteSet u₀ u₁ wa₀ wa₁ γ ∩ alignedSet u₀ u₁ wb₀ wb₁).card <
      N - predecessorThreshold := by
  have h := foreign_vote_fiber_le dom u₀ u₁ hwa₀ hwa₁ hwb₀ hwb₁ γ hexc
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hk : k = 268435456 := by norm_num [k]
  omega

end Energy

/-! ## Calibration rungs -/

/-- **The crossover**: the fiber-Chebyshev refinement beats the disjointness
vote bound exactly when the vote demand exceeds `k − 1`, i.e. for foreign
regions of alignment `A < T − k + 1 = 324359511`; the pair-pencil floor
`2T − N = 111848108` lies deep inside the refined range. -/
theorem refinement_crossover :
    predecessorThreshold - (k - 1) = 324359511 ∧
    2 * predecessorThreshold - N < 324359511 := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

/-- The refinement factor at the swarm floor: `k − 1 < N − T < 2(k − 1)` — the
second moment improves the per-region rider cap by a factor
`(N−T)/(k−1) ≈ 1.79` there. -/
theorem refinement_factor_floor :
    k - 1 < N - predecessorThreshold ∧
    N - predecessorThreshold < 2 * (k - 1) := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

/-- The no-fully-foreign ledger: `(k−1)(T−1) = 159127186151484075 <
(N−T)² = 231309880220072164` — even the AGGREGATE second moment over a maximal
foreign region cannot host a single `(N−T)`-vote rider. -/
theorem no_fully_foreign_ledger :
    (k - 1) * (predecessorThreshold - 1) <
      (N - predecessorThreshold) * (N - predecessorThreshold) := by
  norm_num [predecessorThreshold_eq, N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterFiberChebyshevRefinement

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterFiberChebyshevRefinement

#print axioms codeword_zero_set_le
#print axioms foreign_vote_fiber_le
#print axioms exceptional_scalar_subsingleton
#print axioms foreign_region_rider_energy
#print axioms no_fully_foreign_rider
#print axioms refinement_crossover
#print axioms refinement_factor_floor
#print axioms no_fully_foreign_ledger
