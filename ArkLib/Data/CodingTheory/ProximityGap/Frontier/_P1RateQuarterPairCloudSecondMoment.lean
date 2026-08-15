/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilHarvestCap

/-!
# Pair-cloud second moment: the jaws do NOT close — but Cauchy–Schwarz caps the
# near-full pencils at FIVE, unconditionally

Issue #466, P1 rate-quarter — pair-cloud round following the pencil-cover theorem.

**The exact calculation** (done in Python first, constants below are kernel-pinned):

* **Second-moment jaw at the pair-pencil floor `a = 2T − N = 111848108`: OPEN.**
  The Cauchy–Schwarz packing bound on `(≥ a)`-aligned pencils closes only when
  `a² > N(k−1)`, and in fact `23·a² ≤ N(k−1) < 24·a²` — the floor sits a factor
  `23.04` BELOW the Johnson threshold (`secondMoment_floor_slack`).
* **Packing jaw: NEVER binds.**  The Bonferroni coverage demand `P(T−1) − N` stays
  under the pairwise budget `C(P,2)(k−1)` for EVERY `P` (minimum margin at
  `P = 3`); quadratic beats linear (`packing_jaw_never_binds`, universal in `P`).
* Hence the two counting jaws cannot squeeze `B ≤ N` for pair-clouds: **the
  many-pencil regime is NOT closable by pair-counting + second moment** — a no-go
  theorem for this route, kernel-pinned so no future campaign re-attempts it.

**The round's positive gem — an UNCONDITIONAL cap on near-full pencils:**
for sets of size `≥ T − 5` with pairwise intersections `≤ k − 1`, Cauchy–Schwarz
DOES bind at `P = 6`: `S₀(S₀ − N) = 8831558712238801572 > 30·N·(k−1) =
8646911252339097600`.  Kernel-checked in full
(`six_near_full_sets_impossible`, via an exact incidence double count +
`sq_sum_le_card_mul_sum_sq`):

* **any stack `(u₀, u₁)` admits at most FIVE pairwise-distinct pencils with
  aligned sets `≥ T − 5`** (`six_near_full_pencils_impossible`), i.e. among any
  six pairwise-distinct pencils, at least one satisfies the margin-5 hypothesis
  of the harvest-cap theorems (`sixPencil_margin_forced`).
* Five full pencils remain counting-feasible (`five_full_pencils_feasible`) — the
  gap between the unconditional `≤ 5` and the generic-rank `≤ 2`
  (dimension-deficit round) is exactly the Bezout-escape content.

This unconditionally shrinks the round-3 residual: `FullyAlignedTripleFree`
quantified over triples is needed only for 3–5 near-full pencils; six and beyond
are now THEOREM-level impossible.

**Honesty**: `StallResidual(μ_{2^30})` remains OPEN — the pair-cloud regime
(thousands of `(2T−N)`-aligned pencils, each far below Johnson) is exactly what
the no-go rungs show counting cannot kill; the live open content is the 3-to-5
near-full cluster (Bezout/generic-rank) plus the sub-Johnson swarm.  No δ*
movement; bracket `3/8 ≤ δ* ≤ 43/96 + ε` untouched.

Probe: `scripts/probes/probe_rate_quarter_p1_pencil_cover.py` (pair-cloud
statistics) + the exact jaw computation reproduced in this file's constants.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPairCloudSecondMoment

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

local instance localInstance_P1RateQuarterPairCloudSecondMoment_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterPairCloudSecondMoment_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The incidence second moment: six near-full sets are impossible -/

/-- **Six sets of size `≥ T − 5` with pairwise intersections `≤ k − 1` cannot
coexist in `Fin N`** — the exact Cauchy–Schwarz second moment:
`S² ≤ N(S + 30(k−1))` fails for `S ≥ 6(T−5)` since
`S₀(S₀−N) = 8831558712238801572 > 30N(k−1) = 8646911252339097600`. -/
theorem six_near_full_sets_impossible
    (A : Fin 6 → Finset (Fin N))
    (hA : ∀ π, predecessorThreshold - 5 ≤ (A π).card)
    (hpair : ∀ π π', π ≠ π' → (A π ∩ A π').card ≤ k - 1) :
    False := by
  classical
  set d : Fin N → ℕ := fun i => (Finset.univ.filter (fun π => i ∈ A π)).card
    with hd
  -- first moment: ∑ d = ∑ |A π|
  have hswap : ∑ i, d i = ∑ π, (A π).card := by
    simp only [hd, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp
  -- second moment: ∑ d² = ∑_{π,π'} |A π ∩ A π'|
  have hpt : ∀ i : Fin N, d i ^ 2 =
      ∑ π : Fin 6, ∑ π' : Fin 6, if i ∈ A π ∩ A π' then 1 else 0 := by
    intro i
    have hdi : d i = ∑ π : Fin 6, if i ∈ A π then 1 else 0 := by
      simp only [hd, Finset.card_filter]
    rw [sq, hdi, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun π' _ => ?_
    by_cases h1 : i ∈ A π <;> by_cases h2 : i ∈ A π' <;>
      simp [h1, h2, Finset.mem_inter]
  have hsq : ∑ i, d i ^ 2 = ∑ π : Fin 6, ∑ π' : Fin 6, (A π ∩ A π').card := by
    calc ∑ i, d i ^ 2
        = ∑ i, ∑ π : Fin 6, ∑ π' : Fin 6, if i ∈ A π ∩ A π' then 1 else 0 :=
          Finset.sum_congr rfl fun i _ => hpt i
      _ = ∑ π : Fin 6, ∑ i, ∑ π' : Fin 6, if i ∈ A π ∩ A π' then 1 else 0 :=
          Finset.sum_comm
      _ = ∑ π : Fin 6, ∑ π' : Fin 6, ∑ i, if i ∈ A π ∩ A π' then 1 else 0 :=
          Finset.sum_congr rfl fun π _ => Finset.sum_comm
      _ = ∑ π : Fin 6, ∑ π' : Fin 6, (A π ∩ A π').card := by
          refine Finset.sum_congr rfl fun π _ =>
            Finset.sum_congr rfl fun π' _ => ?_
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
            smul_eq_mul, mul_one]
  -- diagonal split: ∑_{π,π'} |∩| ≤ ∑ |A π| + 30(k−1)
  have hoff : ∑ π : Fin 6, ∑ π' : Fin 6, (A π ∩ A π').card ≤
      (∑ π, (A π).card) + 6 * (5 * (k - 1)) := by
    have hsplit : ∀ π : Fin 6, ∑ π' : Fin 6, (A π ∩ A π').card ≤
        (A π).card + 5 * (k - 1) := by
      intro π
      have herase : ∑ π' ∈ Finset.univ.erase π, (A π ∩ A π').card +
          (A π ∩ A π).card = ∑ π' : Fin 6, (A π ∩ A π').card :=
        Finset.sum_erase_add _ _ (Finset.mem_univ π)
      have hbound : ∑ π' ∈ Finset.univ.erase π, (A π ∩ A π').card ≤
          5 * (k - 1) := by
        calc ∑ π' ∈ Finset.univ.erase π, (A π ∩ A π').card
            ≤ (Finset.univ.erase π).card • (k - 1) :=
              Finset.sum_le_card_nsmul _ _ _
                (fun π' hπ' => hpair π π' (Finset.ne_of_mem_erase hπ').symm)
          _ = 5 * (k - 1) := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ π), smul_eq_mul]
              simp
      have hdiag : (A π ∩ A π).card = (A π).card := by
        rw [Finset.inter_self]
      omega
    calc ∑ π : Fin 6, ∑ π' : Fin 6, (A π ∩ A π').card
        ≤ ∑ π : Fin 6, ((A π).card + 5 * (k - 1)) :=
          Finset.sum_le_sum fun π _ => hsplit π
      _ = (∑ π, (A π).card) + 6 * (5 * (k - 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const]
          simp
  -- Cauchy–Schwarz over ℕ
  have hCS : (∑ i, d i) ^ 2 ≤ N * ∑ i, d i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin N))) (f := fun i => d i)
    simpa [Finset.card_univ] using h
  -- assemble: S² ≤ N·S + 30N(k−1) with S ≥ 6(T−5)
  have hS0 : 3556769766 ≤ ∑ i, d i := by
    rw [hswap]
    have h6 : ∑ _π : Fin 6, (predecessorThreshold - 5) ≤ ∑ π, (A π).card :=
      Finset.sum_le_sum fun π _ => hA π
    rw [Finset.sum_const] at h6
    have hT := predecessorThreshold_eq
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h6
    omega
  have hfin : (∑ i, d i) * (∑ i, d i) ≤
      N * (∑ i, d i) + N * (6 * (5 * (k - 1))) := by
    have h1 : (∑ i, d i) ^ 2 ≤ N * ((∑ π, (A π).card) + 6 * (5 * (k - 1))) :=
      hCS.trans (Nat.mul_le_mul_left N (le_of_eq_of_le hsq hoff))
    rw [← hswap, Nat.mul_add, pow_two] at h1
    exact h1
  -- pure arithmetic finale
  have hkey : ∀ S : ℕ, 3556769766 ≤ S →
      S * S ≤ N * S + N * (6 * (5 * (k - 1))) → False := by
    intro S hSge hSfin
    have hE : N * (6 * (5 * (k - 1))) = 8646911252339097600 := by
      norm_num [N, k]
    have hN : N = 1073741824 := by norm_num [N]
    have hSN : N ≤ S := by omega
    have hsub : 2483027942 ≤ S - N := by omega
    have hprod : 3556769766 * 2483027942 ≤ S * (S - N) :=
      Nat.mul_le_mul hSge hsub
    have hpn : (3556769766 : ℕ) * 2483027942 = 8831558712238801572 := by
      norm_num
    have hsplit : S * (S - N) + S * N = S * S := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hSN]
    have hcomm : S * N = N * S := Nat.mul_comm S N
    omega
  exact hkey _ hS0 hfin

/-! ## The pencil corollaries -/

section Pencils

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)

/-- **At most five near-full pencils, unconditionally**: no stack admits six
pairwise-distinct codeword pencils all aligned on `≥ T − 5` coordinates. -/
theorem six_near_full_pencils_impossible
    (W : Fin 6 → (Fin N → F) × (Fin N → F))
    (hmem : ∀ π, (W π).1 ∈ predecessorCode dom ∧ (W π).2 ∈ predecessorCode dom)
    (hdist : ∀ π π', π ≠ π' → W π ≠ W π')
    (halign : ∀ π,
      predecessorThreshold - 5 ≤ (alignedSet u₀ u₁ (W π).1 (W π).2).card) :
    False := by
  classical
  refine six_near_full_sets_impossible
    (fun π => alignedSet u₀ u₁ (W π).1 (W π).2) halign
    (fun π π' hne => ?_)
  refine alignedSet_inter_card_lt_k dom u₀ u₁
    (hmem π).1 (hmem π).2 (hmem π').1 (hmem π').2 ?_
  intro h
  exact hdist π π' hne (by
    have h1 : (W π).1 = (W π').1 := congrArg Prod.fst h
    have h2 : (W π).2 = (W π').2 := congrArg Prod.snd h
    exact Prod.ext h1 h2)

/-- **Margin forced at six**: among any six pairwise-distinct pencils, at least
one satisfies the margin-5 hypothesis of the harvest-cap budget theorems.  This
unconditionally confines the round-3 residual to clusters of 3–5 near-full
pencils. -/
theorem sixPencil_margin_forced
    (W : Fin 6 → (Fin N → F) × (Fin N → F))
    (hmem : ∀ π, (W π).1 ∈ predecessorCode dom ∧ (W π).2 ∈ predecessorCode dom)
    (hdist : ∀ π π', π ≠ π' → W π ≠ W π') :
    ∃ π, (alignedSet u₀ u₁ (W π).1 (W π).2).card + 5 ≤ predecessorThreshold := by
  by_contra hall
  push Not at hall
  refine six_near_full_pencils_impossible dom u₀ u₁ W hmem hdist (fun π => ?_)
  have h := hall π
  have hT := predecessorThreshold_eq
  omega

end Pencils

/-! ## The no-go rungs: the counting jaws cannot close the pair-cloud regime -/

/-- **Second-moment jaw at the pair-pencil floor is OPEN by a factor 23**:
`23·(2T−N)² ≤ N(k−1) < 24·(2T−N)²`.  The `(2T−N)`-aligned pair-pencil cloud sits
far below the Johnson threshold where Cauchy–Schwarz packing would bind. -/
theorem secondMoment_floor_slack :
    23 * (111848108 * 111848108) ≤ N * (k - 1) ∧
    N * (k - 1) < 24 * (111848108 * 111848108) ∧
    2 * predecessorThreshold - N = 111848108 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- **The packing jaw never binds**: for EVERY pencil count `P`, the Bonferroni
coverage demand of `P` fully-aligned pencils stays within the pairwise MDS budget:
`2·P·(T−1) ≤ 2N + P(P−1)(k−1)`.  Quadratic beats linear — pure pairwise packing
can never bound the cloud (no-go for this route). -/
theorem packing_jaw_never_binds (Pc : ℕ) :
    2 * (Pc * (predecessorThreshold - 1)) ≤ 2 * N + Pc * (Pc - 1) * (k - 1) := by
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hk : k = 268435456 := by norm_num [k]
  rcases Nat.lt_or_ge Pc 6 with hP | hP
  · interval_cases Pc <;> omega
  · -- P ≥ 6: (P−1)(k−1) ≥ 5(k−1) ≥ 2(T−1)
    have h5 : 2 * (predecessorThreshold - 1) ≤ (Pc - 1) * (k - 1) := by
      have : 5 * (k - 1) ≤ (Pc - 1) * (k - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    calc 2 * (Pc * (predecessorThreshold - 1))
        = Pc * (2 * (predecessorThreshold - 1)) := by ring
      _ ≤ Pc * ((Pc - 1) * (k - 1)) := Nat.mul_le_mul_left _ h5
      _ = Pc * (Pc - 1) * (k - 1) := by ring
      _ ≤ 2 * N + Pc * (Pc - 1) * (k - 1) := Nat.le_add_left _ _

/-- Five full pencils remain counting-feasible:
`5(T−1)·(5(T−1) − N) ≤ 20·N·(k−1)` — the gap between the unconditional `≤ 5` and
the generic-rank `≤ 2` (dimension-deficit round) is exactly the Bezout-escape
content. -/
theorem five_full_pencils_feasible :
    5 * (predecessorThreshold - 1) * (5 * (predecessorThreshold - 1) - N) ≤
      20 * (N * (k - 1)) := by
  norm_num [predecessorThreshold_eq, N, k]

/-- The `P = 6` contradiction constants (the kernel core of
`six_near_full_sets_impossible`): `6(T−5)·(6(T−5) − N) > 30·N·(k−1)`. -/
theorem six_pencil_contradiction_constants :
    30 * (N * (k - 1)) < 6 * (predecessorThreshold - 5) *
      (6 * (predecessorThreshold - 5) - N) := by
  norm_num [predecessorThreshold_eq, N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterPairCloudSecondMoment

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterPairCloudSecondMoment

#print axioms six_near_full_sets_impossible
#print axioms six_near_full_pencils_impossible
#print axioms sixPencil_margin_forced
#print axioms secondMoment_floor_slack
#print axioms packing_jaw_never_binds
#print axioms five_full_pencils_feasible
#print axioms six_pencil_contradiction_constants
