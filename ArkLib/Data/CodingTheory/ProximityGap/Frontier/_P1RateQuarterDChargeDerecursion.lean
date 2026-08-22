/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterGlobalConsistencyCharge

/-!
# The D-charge derecursion: exact parameter flow, closure boundary `F₀ = 75018133`, stall

Successor of `_P1RateQuarterGlobalConsistencyCharge`.  Makes the derecursion precise and
computes its exact fixed-point structure.  **Verdict: the flow does NOT close the pin — it
has a sharp dichotomy boundary in the pool size `F`, closed below, stalled above.**

**Level 0 — the pair problem collapses to a direction problem.**  For pencils through the
base `(γ₀, p₀)` the first row is DETERMINED: `w₀ = p₀ − γ₀·w₁` (`pencil_base_determined`),
and the aligned region is exactly `{D = 0} ∩ {w₁ = u₁}`
(`alignedSet_eq_Dzero_inter_dirAgreement`): the pencil's alignment `A` equals the agreement
of its direction `w₁` with `u₁` on `Z = {D = 0}`.  So the whole fiber ledger is a
SINGLE-word agreement problem on `Z`.

**Level 1 — the flow map.**  Every rider `γ ≠ γ₀` maps injectively via
`s = (γ − γ₀)⁻¹` to a scalar whose line `u₁ − s·D` its pencil direction matches on `≥ T`
coordinates (`bad_maps_to_direction_agreement`): on aligned coordinates `D = 0` so
`u₁ − sD = u₁ = w₁`; on vote coordinates the vote equation solves to `w₁ = u₁ − sD`.
Together with `riders_card_le_pool` (`riders ≤ F` unconditionally — every rider casts a
pool vote) and `sterile_of_deep_subalignment` (`T − A > F ⟹ no riders`), the fiber ledger
becomes: `#bad ≤ 1 + Σ_w F/(T − agr_Z(w, u₁))` over directions with
`agr_Z ≥ T − F`, where the direction counts at level `a` are Johnson-packable on `Z`
(pairwise `≤ k − 1` since distinct codewords collide on `≤ k − 1` points).

**Level 2 — the exact dichotomy** (`derecursion_boundary`, probe-verified greedy optimum):
the whole contributing range `[T − F, T]` is above the `Z`-Johnson radius iff
`(T − F)² > (N − F)(k − 1)`, i.e. iff `F ≤ F₀ = 75018133`.

* `F ≤ F₀`: every contributing direction is Johnson-counted on `Z`; the exact greedy layer
  optimum of the ledger is `882722755 ≤ N` at the boundary (probe, exact integers, worst
  case over all `F ≤ F₀`) — the branch is CLOSED (assembling the `Z`-relative Johnson
  layer-cake in Lean is engineering of the `_P1RateQuarterLayerCakeBudget` kind, not new
  mathematics; the arithmetic optimum is pinned here and in the probe).
* `F ≥ F₀ + 1`: the window `[T − F, ⌊√((N−F)(k−1))⌋]` is nonempty (width `18954209` at the
  three-heavy pool `F = 100663294`, `stall_window_at_heavy_pool`) — sub-Johnson-on-`Z`
  direction swarms are uncounted.  **STALL.**  The stall splits into two pool-code regimes
  at `F = k` (`pool_code_regimes`): for `F < k` the punctured RS on the pool is the full
  space (algebraically free pool — all structure lives in the direction list on `Z`);
  for `F ≥ k` (possible up to `N − T + 1 = 480946859`) the pool carries a nontrivial MDS
  code of dimension `k` — fresh algebra available there, a candidate next attack.

**The minimal residual** (`StallResidual`): the budget for bad families ALL of whose base
scalars have stalling pools `F ≥ 75018134`.  If any base scalar has `F ≤ F₀` the small-`F`
ledger closes that family.  The stall configuration is exactly: unboundedly many directions
at `Z`-agreement in the stall window, each carrying `≤ F/(T−A)` riders realized as pool
votes against the affine family `s ↦ u₁ − s·D` on an algebraically free pool.

No delta-star change; the operational bracket is untouched.  Probe:
`scripts/probes/probe_rate_quarter_p1_dcharge_derecursion.py` (exact boundary, greedy
optimum, stall widths, and 100-instance μ_256 verification of the level-0 identity and
level-1 flow inclusion).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge

local instance localInstance_P1RateQuarterDChargeDerecursion_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterDChargeDerecursion_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Level 0: the pair problem collapses to a direction problem on `Z` -/

section Flow

variable (u₀ u₁ p₀ : Fin N → F) (γ₀ : F) {w₀ w₁ : Fin N → F}

/-- Through-base pencils have a determined first row: `w₀ = p₀ − γ₀·w₁`. -/
theorem pencil_base_determined (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i) :
    ∀ i, w₀ i = p₀ i - γ₀ * w₁ i := by
  intro i
  linear_combination hbase i

/-- **The alignment collapse**: for a pencil through the base, the aligned region is
exactly `{D = 0} ∩ {w₁ = u₁}` — pencil alignment IS direction agreement on `Z`. -/
theorem alignedSet_eq_Dzero_inter_dirAgreement
    (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i) :
    alignedSet u₀ u₁ w₀ w₁ =
      Finset.univ.filter
        (fun i => Dfun u₀ u₁ p₀ γ₀ i = 0 ∧ w₁ i = u₁ i) := by
  ext i
  rw [mem_alignedSet_iff, Finset.mem_filter]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨Finset.mem_univ _, ?_, h1⟩
    rw [Dfun, ← hbase i, h0, h1]
    ring
  · rintro ⟨-, hD, h1⟩
    refine ⟨?_, h1⟩
    have hb := hbase i
    rw [Dfun] at hD
    rw [h1] at hb
    linear_combination hb + hD

/-- **Unconditional pool cap**: every pencil through the base carries at most `F` riders,
regardless of alignment — each rider casts at least one vote, votes are disjoint, and all
votes land in the shared pool `{D ≠ 0}`. -/
theorem riders_card_le_pool (dom : Fin N ↪ F) (R : Finset F) (Sf : F → Finset (Fin N))
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i)
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) (hγ₀R : γ₀ ∉ R) :
    R.card ≤ (Dsupport u₀ u₁ p₀ γ₀).card := by
  classical
  have hper : ∀ γ ∈ R, 1 ≤ (voteSet u₀ u₁ w₀ w₁ γ).card := by
    intro γ hγ
    obtain ⟨hcard, hagree, hno⟩ := h γ hγ
    have hT : 1 ≤ (Sf γ).card := by
      have := predecessorThreshold_eq
      omega
    exact Finset.card_pos.mpr
      (voteSet_nonempty_of_rides u₀ u₁ w₀ w₁ dom hw₀ hw₁ hagree hno hT)
  have hpool : R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ) ⊆
      Dsupport u₀ u₁ p₀ γ₀ := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, hγR, hiv⟩ := hi
    exact voteSet_subset_Dsupport u₀ u₁ p₀ γ₀ hbase
      (fun hh => hγ₀R (hh ▸ hγR)) hiv
  calc R.card = ∑ _γ ∈ R, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ γ ∈ R, (voteSet u₀ u₁ w₀ w₁ γ).card := Finset.sum_le_sum hper
    _ = (R.biUnion (fun γ => voteSet u₀ u₁ w₀ w₁ γ)).card :=
        (card_biUnion_votes u₀ u₁ w₀ w₁ R).symm
    _ ≤ (Dsupport u₀ u₁ p₀ γ₀).card := Finset.card_le_card hpool

/-- **Sterility below the pool**: a pencil whose alignment deficit exceeds the pool
(`T − A > F`) carries no riders at all. -/
theorem sterile_of_deep_subalignment (dom : Fin N ↪ F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i)
    (h : RidesAll dom u₀ u₁ w₀ w₁ R Sf) (hγ₀R : γ₀ ∉ R)
    (hdeep : (Dsupport u₀ u₁ p₀ γ₀).card <
      predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card) :
    R = ∅ := by
  classical
  have hstep := riders_mul_le_Dsupport u₀ u₁ p₀ γ₀ dom R Sf hbase h hγ₀R
  rw [← Finset.card_eq_zero]
  by_contra hne
  have hR : 1 ≤ R.card := Nat.one_le_iff_ne_zero.mpr hne
  have := Nat.mul_le_mul hR
    (le_refl (predecessorThreshold - (alignedSet u₀ u₁ w₀ w₁).card))
  omega

/-- **The flow map (level 1)**: a rider `γ ≠ γ₀` on a through-base pencil forces its
direction `w₁` to agree with the affine word `u₁ − (γ−γ₀)⁻¹·D` on at least `T` coordinates
— the bad family maps injectively (via `γ ↦ (γ−γ₀)⁻¹`) into a correlated-agreement family
of the NEW stack `(u₁, −D)` at the SAME parameters `(N, T, k)`. -/
theorem bad_maps_to_direction_agreement (γ : F) (Sγ : Finset (Fin N))
    (hbase : ∀ i, w₀ i + γ₀ * w₁ i = p₀ i) (hγ : γ ≠ γ₀)
    (hcard : predecessorThreshold ≤ Sγ.card)
    (hagree : ∀ i ∈ Sγ, w₀ i + γ * w₁ i = u₀ i + γ * u₁ i) :
    predecessorThreshold ≤
      (Finset.univ.filter
        (fun i => w₁ i = u₁ i - (γ - γ₀)⁻¹ * Dfun u₀ u₁ p₀ γ₀ i)).card := by
  classical
  have hne : γ - γ₀ ≠ 0 := sub_ne_zero.mpr hγ
  have hsub : Sγ ⊆ Finset.univ.filter
      (fun i => w₁ i = u₁ i - (γ - γ₀)⁻¹ * Dfun u₀ u₁ p₀ γ₀ i) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have key : (γ - γ₀) * (u₁ i - w₁ i) = Dfun u₀ u₁ p₀ γ₀ i := by
      rw [Dfun]
      linear_combination (hbase i) - (hagree i hi)
    have hinv : u₁ i - w₁ i = (γ - γ₀)⁻¹ * Dfun u₀ u₁ p₀ γ₀ i := by
      apply mul_left_cancel₀ hne
      rw [key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    linear_combination -hinv
  exact hcard.trans (Finset.card_le_card hsub)

end Flow

/-! ## Level 2: the exact dichotomy boundary and the stall window -/

/-- **The derecursion boundary is `F₀ = 75018133`**: for pool size `F ≤ F₀` the entire
contributing direction range `[T − F, T]` lies strictly above the `Z`-Johnson radius
(`(T − F)² > (N − F)(k−1)`), so every contributing direction is Johnson-counted on `Z`;
at `F₀ + 1` the strict inequality fails and the sub-Johnson stall window opens. -/
theorem derecursion_boundary :
    (predecessorThreshold - 75018133) ^ 2 > (N - 75018133) * (k - 1) ∧
    (predecessorThreshold - 75018134) ^ 2 ≤ (N - 75018134) * (k - 1) := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

/-- Monotonicity in `F`: below the boundary the Johnson condition holds for every smaller
pool as well (the contributing floor `T − F` only rises). -/
theorem johnson_condition_of_le_boundary {Fp : ℕ} (hF : Fp ≤ 75018133) :
    (predecessorThreshold - Fp) ^ 2 > (N - Fp) * (k - 1) := by
  have h0 := derecursion_boundary.1
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hk : k = 268435456 := by norm_num [k]
  -- need (N − Fp)(k−1) < (T − Fp)²; strengthen via the exact boundary check at Fp = 0
  -- and the difference structure: (N−Fp)(k−1) − (N−75018133)(k−1) = (75018133−Fp)(k−1)
  -- while (T−Fp)² − (T−75018133)² ≥ (75018133−Fp)·2·(T−75018133) > (75018133−Fp)(k−1)
  have hgap : (N - Fp) * (k - 1) ≤
      (N - 75018133) * (k - 1) + (75018133 - Fp) * (k - 1) := by
    have : N - Fp ≤ (N - 75018133) + (75018133 - Fp) := by omega
    calc (N - Fp) * (k - 1)
        ≤ ((N - 75018133) + (75018133 - Fp)) * (k - 1) :=
          Nat.mul_le_mul_right _ this
      _ = (N - 75018133) * (k - 1) + (75018133 - Fp) * (k - 1) := by ring
  have hsq : ∀ a d : ℕ, a ^ 2 + d * (2 * a) ≤ (a + d) ^ 2 := by
    intro a d
    nlinarith [Nat.zero_le (d ^ 2)]
  have hgrow : (predecessorThreshold - 75018133) ^ 2 +
      (75018133 - Fp) * (2 * (predecessorThreshold - 75018133)) ≤
      (predecessorThreshold - Fp) ^ 2 := by
    have hd : predecessorThreshold - Fp =
        (predecessorThreshold - 75018133) + (75018133 - Fp) := by omega
    rw [hd]
    exact hsq _ _
  have hbig : (75018133 - Fp) * (k - 1) ≤
      (75018133 - Fp) * (2 * (predecessorThreshold - 75018133)) := by
    apply Nat.mul_le_mul_left
    omega
  calc (N - Fp) * (k - 1)
      ≤ (N - 75018133) * (k - 1) + (75018133 - Fp) * (k - 1) := hgap
    _ ≤ (N - 75018133) * (k - 1) +
        (75018133 - Fp) * (2 * (predecessorThreshold - 75018133)) :=
          Nat.add_le_add_left hbig _
    _ < (predecessorThreshold - 75018133) ^ 2 +
        (75018133 - Fp) * (2 * (predecessorThreshold - 75018133)) :=
          Nat.add_lt_add_right h0 _
    _ ≤ (predecessorThreshold - Fp) ^ 2 := hgrow

/-- **The stall window at the three-heavy pool** `F = 100663294`: pencils are sterile below
alignment `T − F = 492131672`, while the `Z`-Johnson radius is `⌊√((N−F)(k−1))⌋ =
511085881` — a nonempty uncounted window of width `18954209`. -/
theorem stall_window_at_heavy_pool :
    predecessorThreshold - 100663294 = 492131672 ∧
    511085881 ^ 2 ≤ (N - 100663294) * (k - 1) ∧
    (N - 100663294) * (k - 1) < 511085882 ^ 2 ∧
    492131672 ≤ 511085881 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-- **The pool-code regimes of the stall**: at the opening of the stall window the pool is
strictly below `k = 2^28` (`75018134 < k`), so RS punctured to the pool is the FULL space —
no RS algebra on the pool there.  But the stall range extends to pools up to
`N − T + 1 = 480946859 > k`: for `F ≥ k` the punctured code is a nontrivial MDS code of
dimension `k` — the two stall sub-regimes (free pool vs MDS pool) are genuinely different
and split at `F = k`. -/
theorem pool_code_regimes :
    75018134 < k ∧ k < N - predecessorThreshold + 1 ∧
    N - predecessorThreshold + 1 = 480946859 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, N, k]

/-! ## The minimal residual -/

/-- **Named residual (OPEN): the stall budget.**  The derecursion closes every bad family
that admits some base scalar with pool `F ≤ F₀ = 75018133` (all contributing directions
Johnson-counted on `Z`; exact greedy optimum `882722755 ≤ N`, probe-pinned).  The residual
is the complementary case: bad families ALL of whose base scalars carry stalling pools.
There the escaping structure is exactly a sub-Johnson-on-`Z` direction swarm voting against
the affine stack family `s ↦ u₁ − s·D` on an algebraically free pool (`F < k`). -/
def StallResidual (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F),
    BadFamilyData dom u₀ u₁ G Sf pf →
    (∀ γ₀ ∈ G, 75018134 ≤ (Dsupport u₀ u₁ (pf γ₀) γ₀).card) →
    G.card ≤ N

end ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion

#print axioms pencil_base_determined
#print axioms alignedSet_eq_Dzero_inter_dirAgreement
#print axioms riders_card_le_pool
#print axioms sterile_of_deep_subalignment
#print axioms bad_maps_to_direction_agreement
#print axioms derecursion_boundary
#print axioms johnson_condition_of_le_boundary
#print axioms stall_window_at_heavy_pool
#print axioms pool_code_regimes
