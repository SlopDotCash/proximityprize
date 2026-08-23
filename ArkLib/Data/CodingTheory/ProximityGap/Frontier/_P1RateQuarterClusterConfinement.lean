/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilHarvestCap

/-!
# Cluster confinement: compounded rank-drop floors, dyadic blocking at m = 4, 5,
# the five-pencil master budget, and the final residual form

Issue #466, P1 rate-quarter — eighth round of the 2026-07-11 arc, following the
pair-cloud second moment (near-full clusters confined to sizes 3–5).

**Exact calculation** (Python-verified, kernel-pinned below):

* **Compounded rank-drop floors.**  An `m`-cluster of near-full pencils has an
  `(m−1)`-dimensional difference lattice (telescoping) with per-row parameter
  budget `(m−1)k` against overlap demand `Σ|ov| ≥ m(T−5) − N` — generic deficit
  `X_m = m(T−5) − N − (m−1)k`:
  `X₃ = 167772147`, `X₄ = 492131652`, `X₅ = 816491157`, growing by
  `(T−5) − k = 324359505` per pencil (`cluster_rank_drop_floors`).  A Bezout
  escape at cluster size `m` must achieve rank drop `≥ X_m` — the requirement
  COMPOUNDS (round 5's single-identity drop was `1.67·10⁸`; a 5-cluster needs
  `8.16·10⁸`).
* **Dyadic blocking at every cluster size.**  The binomial-constructor window at
  size `m` is `[⌈(m(T−5) − N)/C(m,2)⌉, k−1]`: `[234881020, 268435455]`,
  `[216239670, 268435455]`, `[189023299, 268435455]` for `m = 3, 4, 5` — ALL
  inside the dyadic gap `(2²⁷, 2²⁸)`, which contains no power of two
  (`dyadic_gap`, `cluster_windows_dyadic_free`): on `μ_{2^30}` every known
  constructor class is blocked at every confined cluster size.
* **Overlap-mass floor for m-clusters** (`cluster_overlap_mass`, structural, via
  the general Bonferroni inequality `bonferroni_double` proved here by induction):
  `2·Σ|A_π| ≤ 2N + Σ_{π≠π'}|A_π ∩ A_π'|` — the coincidence mass any cluster must
  realize.

**The master budget** (kernel):

* `six_sets_impossible_param` — the second-moment six-set impossibility,
  parametric in the size threshold; instantiated at `θ = T − 12` to force
  **margin ≥ 13 among any six pairwise-distinct pencils**
  (`sixPencil_margin13_forced`).
* `margined_riders_le_of_thirteen` — margin-13 pencils harvest `≤ 36995913`.
* `stall_budget_of_five_pencil_cover` — two arbitrary pencils + three margin-13
  pencils: `#bad ≤ 2·480946859 + 3·36995913 = 1072881457 ≤ N` (slack `860367`).
* **The final residual form** (`stallResidual_of_swarmResidual`):
  `StallResidual dom ⟸ SwarmResidual dom`, where `SwarmResidual` is the budget
  restricted to families admitting NO five-pencil margined cover
  (`FiveCoverForm`) — every five-pencil-coverable family is now discharged
  unconditionally given the cover, and (per `sixPencil_margin13_forced` +
  round-3's triple residual) covers with ≤ 2 near-full members always fit the
  form.  The open content of the P1 counting branch is EXACTLY: (i) 3-to-5
  near-full clusters (rank drops `≥ X_m`, all known constructors dyadically
  blocked), (ii) the sub-Johnson swarm (`SwarmResidual`, counting-immune per the
  pair-cloud no-gos).

**Honesty**: `StallResidual(μ_{2^30})` remains OPEN — this round reduces it to
`SwarmResidual` (a strictly weaker statement) and pins the cluster escape floors;
it does not discharge the swarm.  No δ* movement; bracket
`3/8 ≤ δ* ≤ 43/96 + ε` untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterClusterConfinement

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

local instance localInstance_P1RateQuarterClusterConfinement_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterClusterConfinement_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## General Bonferroni and the m-cluster overlap mass -/

/-- **General Bonferroni (double-sum form)**: for any finite family of finsets,
`3·Σ|A_i| ≤ 2·|⋃ A_i| + Σ_{i,j}|A_i ∩ A_j|` (the double sum includes the
diagonal `Σ|A_i|`; subtracting it gives the classical
`Σ|A| − |⋃| ≤ Σ_{i<j}|ov|`). -/
theorem bonferroni_double {ι' : Type*} [DecidableEq ι'] (s : Finset ι')
    (A : ι' → Finset (Fin N)) :
    3 * ∑ i ∈ s, (A i).card ≤
      2 * (s.biUnion A).card + ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    have hinner : ∀ i, ∑ j ∈ insert a s, (A i ∩ A j).card =
        (A i ∩ A a).card + ∑ j ∈ s, (A i ∩ A j).card :=
      fun i => Finset.sum_insert ha
    have hdouble : ∑ i ∈ insert a s, ∑ j ∈ insert a s, (A i ∩ A j).card =
        (A a).card + (∑ j ∈ s, (A a ∩ A j).card + (∑ i ∈ s, (A i ∩ A a).card +
          ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).card)) := by
      rw [Finset.sum_insert ha, hinner a, Finset.inter_self]
      have hrest : ∑ i ∈ s, ∑ j ∈ insert a s, (A i ∩ A j).card =
          ∑ i ∈ s, (A i ∩ A a).card + ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).card := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hinner i
      rw [hrest]
      ring
    have hsym : ∑ i ∈ s, (A i ∩ A a).card = ∑ j ∈ s, (A a ∩ A j).card :=
      Finset.sum_congr rfl fun i _ => by rw [Finset.inter_comm]
    have hunion : ((A a) ∪ s.biUnion A).card + ((A a) ∩ s.biUnion A).card =
        (A a).card + (s.biUnion A).card :=
      Finset.card_union_add_card_inter _ _
    have hcap : ((A a) ∩ s.biUnion A).card ≤ ∑ j ∈ s, (A a ∩ A j).card := by
      calc ((A a) ∩ s.biUnion A).card
          = (s.biUnion fun j => A a ∩ A j).card := by
            rw [Finset.inter_biUnion]
        _ ≤ ∑ j ∈ s, (A a ∩ A j).card := Finset.card_biUnion_le
    omega

/-- **m-cluster overlap mass**: a family of `θ`-aligned sets forces coincidence
mass `2(Σθ − N) ≤ Σ_{i,j}|A_i ∩ A_j| − Σ|A_i|` (stated addition-only). -/
theorem cluster_overlap_mass {ι' : Type*} [DecidableEq ι'] (s : Finset ι')
    (A : ι' → Finset (Fin N)) (θ : ℕ) (hA : ∀ i ∈ s, θ ≤ (A i).card) :
    2 * (s.card * θ) + ∑ i ∈ s, (A i).card ≤
      2 * N + ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).card := by
  classical
  have hbon := bonferroni_double s A
  have hN : (s.biUnion A).card ≤ N := by
    have h := Finset.card_le_univ (s.biUnion A)
    simpa [Finset.card_univ, Fintype.card_fin] using h
  have hθ : s.card * θ ≤ ∑ i ∈ s, (A i).card := by
    calc s.card * θ = ∑ _i ∈ s, θ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ s, (A i).card := Finset.sum_le_sum hA
  omega

/-! ## Compounded rank-drop floors and dyadic blocking (kernel rungs) -/

/-- **Compounded rank-drop floors**: the generic deficit of the `m`-cluster
difference lattice, `X_m = m(T−5) − N − (m−1)k`, at the confined cluster sizes:
`X₃ = 167772147`, `X₄ = 492131652`, `X₅ = 816491157`, growth
`(T−5) − k = 324359505` per pencil.  A Bezout escape at size `m` must defeat
`X_m` independent evaluation constraints. -/
theorem cluster_rank_drop_floors :
    3 * (predecessorThreshold - 5) - N - 2 * k = 167772147 ∧
    4 * (predecessorThreshold - 5) - N - 3 * k = 492131652 ∧
    5 * (predecessorThreshold - 5) - N - 4 * k = 816491157 ∧
    (predecessorThreshold - 5) - k = 324359505 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- **The dyadic gap**: no power of two lies strictly between `2²⁷` and `2²⁸`. -/
theorem dyadic_gap (j : ℕ) : ¬ (2 ^ 27 < 2 ^ j ∧ 2 ^ j < 2 ^ 28) := by
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_ge 27 j with hj | hj
  · have h : (2 : ℕ) ^ 28 ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) hj
    omega
  · have h : (2 : ℕ) ^ j ≤ 2 ^ 27 :=
      Nat.pow_le_pow_right (by norm_num) hj
    omega

/-- **All confined cluster-constructor windows are dyadically empty**: the
binomial-escape window at cluster size `m ∈ {3,4,5}` is
`[⌈(m(T−5) − N)/C(m,2)⌉, k−1]`, and every one sits inside the dyadic gap
`(2²⁷, 2²⁸)` — on `μ_{2^30}` no subgroup order fits any of them. -/
theorem cluster_windows_dyadic_free :
    2 ^ 27 < 234881020 ∧ (3 * (predecessorThreshold - 5) - N + 2) / 3 = 234881020 ∧
    2 ^ 27 < 216239670 ∧ (4 * (predecessorThreshold - 5) - N + 5) / 6 = 216239670 ∧
    2 ^ 27 < 189023299 ∧ (5 * (predecessorThreshold - 5) - N + 9) / 10 = 189023299 ∧
    k - 1 < 2 ^ 28 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-! ## The parametric six-set impossibility and margin-13 forcing -/

/-- **Parametric six-set impossibility**: six subsets of `Fin N` of size `≥ θ`
with pairwise intersections `≤ k−1` cannot coexist whenever
`30N(k−1) < 6θ·(6θ − N)` (the exact Cauchy–Schwarz second moment). -/
theorem six_sets_impossible_param (θ : ℕ)
    (hbig : 30 * (N * (k - 1)) < (6 * θ) * (6 * θ - N)) (hθN : N ≤ 6 * θ)
    (A : Fin 6 → Finset (Fin N))
    (hA : ∀ π, θ ≤ (A π).card)
    (hpair : ∀ π π', π ≠ π' → (A π ∩ A π').card ≤ k - 1) :
    False := by
  classical
  set d : Fin N → ℕ := fun i => (Finset.univ.filter (fun π => i ∈ A π)).card
    with hd
  have hswap : ∑ i, d i = ∑ π, (A π).card := by
    simp only [hd, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp
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
  have hCS : (∑ i, d i) ^ 2 ≤ N * ∑ i, d i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin N))) (f := fun i => d i)
    simpa [Finset.card_univ] using h
  have hS0 : 6 * θ ≤ ∑ i, d i := by
    rw [hswap]
    have h6 : ∑ _π : Fin 6, θ ≤ ∑ π, (A π).card :=
      Finset.sum_le_sum fun π _ => hA π
    rw [Finset.sum_const] at h6
    simpa using h6
  have hfin : (∑ i, d i) * (∑ i, d i) ≤
      N * (∑ i, d i) + N * (6 * (5 * (k - 1))) := by
    have h1 : (∑ i, d i) ^ 2 ≤ N * ((∑ π, (A π).card) + 6 * (5 * (k - 1))) :=
      hCS.trans (Nat.mul_le_mul_left N (le_of_eq_of_le hsq hoff))
    rw [← hswap, Nat.mul_add, pow_two] at h1
    exact h1
  -- pure arithmetic finale, parametric in θ
  have hkey : ∀ S : ℕ, 6 * θ ≤ S →
      S * S ≤ N * S + N * (6 * (5 * (k - 1))) → False := by
    intro S hSge hSfin
    have hE : N * (6 * (5 * (k - 1))) = 30 * (N * (k - 1)) := by ring
    have hSN : N ≤ S := le_trans hθN hSge
    have hθSN : 6 * θ - N ≤ S - N := by omega
    have hprod : (6 * θ) * (6 * θ - N) ≤ S * (S - N) :=
      Nat.mul_le_mul hSge hθSN
    have hY : 30 * (N * (k - 1)) < S * (S - N) := lt_of_lt_of_le hbig hprod
    have hsplit : S * (S - N) + S * N = S * S := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hSN]
    have hcomm : S * N = N * S := Nat.mul_comm S N
    omega
  exact hkey _ hS0 hfin

section MarginForcing

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)

/-- **Margin ≥ 13 forced among any six**: any six pairwise-distinct pencils
contain one whose aligned set satisfies `card + 13 ≤ T` (the six-set
impossibility at `θ = T − 12`). -/
theorem sixPencil_margin13_forced
    (W : Fin 6 → (Fin N → F) × (Fin N → F))
    (hmem : ∀ π, (W π).1 ∈ predecessorCode dom ∧ (W π).2 ∈ predecessorCode dom)
    (hdist : ∀ π π', π ≠ π' → W π ≠ W π') :
    ∃ π, (alignedSet u₀ u₁ (W π).1 (W π).2).card + 13 ≤ predecessorThreshold := by
  by_contra hall
  push Not at hall
  refine six_sets_impossible_param (predecessorThreshold - 12) ?_ ?_
    (fun π => alignedSet u₀ u₁ (W π).1 (W π).2) (fun π => ?_)
    (fun π π' hne => ?_)
  · norm_num [predecessorThreshold_eq, N, k]
  · norm_num [predecessorThreshold_eq, N]
  · show predecessorThreshold - 12 ≤ (alignedSet u₀ u₁ (W π).1 (W π).2).card
    have h := hall π
    have hT := predecessorThreshold_eq
    omega
  · refine alignedSet_inter_card_lt_k dom u₀ u₁
      (hmem π).1 (hmem π).2 (hmem π').1 (hmem π').2 ?_
    intro h
    exact hdist π π' hne (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

end MarginForcing

/-! ## The five-pencil master budget -/

section FiveCover

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- Margin-13 pencils harvest at most `36995913 = ⌊(N−T+13)/13⌋`. -/
theorem margined_riders_le_of_thirteen {w₀ w₁ : Fin N → F}
    (h : RidesAll dom u₀ u₁ w₀ w₁ G Sf)
    (hD : (alignedSet u₀ u₁ w₀ w₁).card + 13 ≤ predecessorThreshold) :
    G.card ≤ 36995913 := by
  have hmul := underAligned_riders_mul_le dom u₀ u₁ w₀ w₁ G Sf 13 h hD
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- **The five-pencil master budget**: a bad family covered by two arbitrary
pencils plus three margin-13 pencils obeys the `StallResidual` budget:
`2·480946859 + 3·36995913 = 1072881457 ≤ N` (slack `860367`). -/
theorem stall_budget_of_five_pencil_cover
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ wd₀ wd₁ we₀ we₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hmc : (alignedSet u₀ u₁ wc₀ wc₁).card + 13 ≤ predecessorThreshold)
    (hmd : (alignedSet u₀ u₁ wd₀ wd₁).card + 13 ≤ predecessorThreshold)
    (hme : (alignedSet u₀ u₁ we₀ we₁).card + 13 ≤ predecessorThreshold)
    (hcover : ∀ γ ∈ G, pf γ = wa₀ + γ • wa₁ ∨ pf γ = wb₀ + γ • wb₁ ∨
      pf γ = wc₀ + γ • wc₁ ∨ pf γ = wd₀ + γ • wd₁ ∨ pf γ = we₀ + γ • we₁) :
    G.card ≤ N := by
  classical
  set G₁ := G.filter (fun γ => pf γ = wa₀ + γ • wa₁) with hG₁
  set R1 := G.filter (fun γ => pf γ ≠ wa₀ + γ • wa₁) with hR1
  set G₂ := R1.filter (fun γ => pf γ = wb₀ + γ • wb₁) with hG₂
  set R2 := R1.filter (fun γ => pf γ ≠ wb₀ + γ • wb₁) with hR2
  set G₃ := R2.filter (fun γ => pf γ = wc₀ + γ • wc₁) with hG₃
  set R3 := R2.filter (fun γ => pf γ ≠ wc₀ + γ • wc₁) with hR3
  set G₄ := R3.filter (fun γ => pf γ = wd₀ + γ • wd₁) with hG₄
  set G₅ := R3.filter (fun γ => pf γ ≠ wd₀ + γ • wd₁) with hG₅
  have hsubR1 : R1 ⊆ G := Finset.filter_subset _ _
  have hsubR2 : R2 ⊆ G := (Finset.filter_subset _ _).trans hsubR1
  have hsubR3 : R3 ⊆ G := (Finset.filter_subset _ _).trans hsubR2
  have hr₁ : RidesAll dom u₀ u₁ wa₀ wa₁ G₁ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata
      (Finset.filter_subset _ _) (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₂ : RidesAll dom u₀ u₁ wb₀ wb₁ G₂ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata
      ((Finset.filter_subset _ _).trans hsubR1)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₃ : RidesAll dom u₀ u₁ wc₀ wc₁ G₃ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata
      ((Finset.filter_subset _ _).trans hsubR2)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₄ : RidesAll dom u₀ u₁ wd₀ wd₁ G₄ Sf :=
    ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata
      ((Finset.filter_subset _ _).trans hsubR3)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hr₅ : RidesAll dom u₀ u₁ we₀ we₁ G₅ Sf := by
    refine ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata
      ((Finset.filter_subset _ _).trans hsubR3) (fun γ hγ => ?_)
    have h5 := Finset.mem_filter.mp hγ
    have h4 := Finset.mem_filter.mp h5.1
    have h3 := Finset.mem_filter.mp h4.1
    have h2 := Finset.mem_filter.mp h3.1
    rcases hcover γ h2.1 with h | h | h | h | h
    · exact absurd h h2.2
    · exact absurd h h3.2
    · exact absurd h h4.2
    · exact absurd h h5.2
    · exact h
  have h₁ : G₁.card ≤ 480946859 :=
    riders_card_le_uniform dom u₀ u₁ wa₀ wa₁ G₁ Sf hwa₀ hwa₁ hr₁
  have h₂ : G₂.card ≤ 480946859 :=
    riders_card_le_uniform dom u₀ u₁ wb₀ wb₁ G₂ Sf hwb₀ hwb₁ hr₂
  have h₃ : G₃.card ≤ 36995913 :=
    margined_riders_le_of_thirteen dom u₀ u₁ G₃ Sf hr₃ hmc
  have h₄ : G₄.card ≤ 36995913 :=
    margined_riders_le_of_thirteen dom u₀ u₁ G₄ Sf hr₄ hmd
  have h₅ : G₅.card ≤ 36995913 :=
    margined_riders_le_of_thirteen dom u₀ u₁ G₅ Sf hr₅ hme
  have hs1 : G.card = G₁.card + R1.card := by
    rw [hG₁, hR1]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wa₀ + γ • wa₁) (s := G)).symm
  have hs2 : R1.card = G₂.card + R2.card := by
    rw [hG₂, hR2]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wb₀ + γ • wb₁) (s := R1)).symm
  have hs3 : R2.card = G₃.card + R3.card := by
    rw [hG₃, hR3]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wc₀ + γ • wc₁) (s := R2)).symm
  have hs4 : R3.card = G₄.card + G₅.card := by
    rw [hG₄, hG₅]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun γ => pf γ = wd₀ + γ • wd₁) (s := R3)).symm
  have hN : N = 1073741824 := by norm_num [N]
  omega

end FiveCover

/-! ## The final residual form -/

/-- A bad family admits a **margined five-pencil cover**: two arbitrary code
pencils plus three margin-13 pencils covering every witness. -/
def FiveCoverForm (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) (G : Finset F)
    (pf : F → Fin N → F) : Prop :=
  ∃ wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ wd₀ wd₁ we₀ we₁ : Fin N → F,
    wa₀ ∈ predecessorCode dom ∧ wa₁ ∈ predecessorCode dom ∧
    wb₀ ∈ predecessorCode dom ∧ wb₁ ∈ predecessorCode dom ∧
    (alignedSet u₀ u₁ wc₀ wc₁).card + 13 ≤ predecessorThreshold ∧
    (alignedSet u₀ u₁ wd₀ wd₁).card + 13 ≤ predecessorThreshold ∧
    (alignedSet u₀ u₁ we₀ we₁).card + 13 ≤ predecessorThreshold ∧
    ∀ γ ∈ G, pf γ = wa₀ + γ • wa₁ ∨ pf γ = wb₀ + γ • wb₁ ∨
      pf γ = wc₀ + γ • wc₁ ∨ pf γ = wd₀ + γ • wd₁ ∨ pf γ = we₀ + γ • we₁

/-- **Named residual (OPEN): the swarm budget.**  The `StallResidual` obligation
restricted to bad families admitting NO margined five-pencil cover — the
sub-Johnson direction swarm (plus 3-to-5 near-full clusters whose companions
cannot be arranged into the form).  Everything five-pencil-coverable is
discharged by `stall_budget_of_five_pencil_cover`. -/
def SwarmResidual (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N))
    (pf : F → Fin N → F),
    BadFamilyData dom u₀ u₁ G Sf pf →
    (∀ γ₀ ∈ G, 75018134 ≤ (Dsupport u₀ u₁ (pf γ₀) γ₀).card) →
    ¬ FiveCoverForm dom u₀ u₁ G pf →
    G.card ≤ N

/-- **The final residual form of the P1 counting branch**:
`SwarmResidual dom → StallResidual dom` — the stall budget is reduced EXACTLY to
the no-five-cover regime; every family with a margined five-pencil cover obeys
the budget unconditionally. -/
theorem stallResidual_of_swarmResidual (dom : Fin N ↪ F)
    (hswarm : SwarmResidual dom) : StallResidual dom := by
  intro u₀ u₁ G Sf pf hdata hpools
  by_cases hcov : FiveCoverForm dom u₀ u₁ G pf
  · obtain ⟨wa₀, wa₁, wb₀, wb₁, wc₀, wc₁, wd₀, wd₁, we₀, we₁,
      hwa₀, hwa₁, hwb₀, hwb₁, hmc, hmd, hme, hcover⟩ := hcov
    exact stall_budget_of_five_pencil_cover dom u₀ u₁ G Sf pf hdata
      hwa₀ hwa₁ hwb₀ hwb₁ hmc hmd hme hcover
  · exact hswarm u₀ u₁ G Sf pf hdata hpools hcov

/-- The master ledger: `2·480946859 + 3·36995913 = 1072881457 ≤ N`, slack
`860367`. -/
theorem master_ledger :
    480946859 + 480946859 + (36995913 + 36995913 + 36995913) = 1072881457 ∧
    1072881457 + 860367 = N := by
  constructor <;> norm_num [N]

end ArkLib.ProximityGap.Frontier.P1RateQuarterClusterConfinement

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterClusterConfinement

#print axioms bonferroni_double
#print axioms cluster_overlap_mass
#print axioms cluster_rank_drop_floors
#print axioms dyadic_gap
#print axioms cluster_windows_dyadic_free
#print axioms six_sets_impossible_param
#print axioms sixPencil_margin13_forced
#print axioms margined_riders_le_of_thirteen
#print axioms stall_budget_of_five_pencil_cover
#print axioms stallResidual_of_swarmResidual
#print axioms master_ledger
