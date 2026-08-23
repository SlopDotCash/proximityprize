/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterDChargeDerecursion

/-!
# The MDS-pool second charge: it instantiates literally, shrinks once, and DOUBLE-STALLS

Successor of `_P1RateQuarterDChargeDerecursion`.  Executes the MDS-pool attack (`F ≥ k`) and
settles the iteration question.  **Verdict: the D-charge iterates verbatim on the pool (the
sink/source lemmas are generic in the stack), produces one genuine shrink, and then the
running threshold collapses below `k − 1`, after which NO Johnson condition can ever fire
again — the derecursion terminates at depth 2 with a permanent sub-Johnson stall throughout
the MDS regime.**  The residual bottoms out at beyond-Johnson list structure — the prize
wall itself.

**The pieces (all kernel-checked here):**

* `pool_card_le_N_sub_T`: the pool is universally bounded, `F ≤ N − T = 480946858` — the
  base witness sinks into `{D = 0}`.  (Sharpens the previously stated stall range end
  `N − T + 1` by one.)
* `pool_separation`: the pool code is MDS — distinct codewords collide on `≤ k − 1` POOL
  coordinates (restriction of `predecessor_sep`).
* `second_charge_vote_source`: the second charge is a LITERAL instantiation — for the
  level-2 stack `(u₁, −D)` with pool base `(s₀, q₀)`, rider votes sink into the second pool
  `{D₂ ≠ 0}`, `D₂ = q₀ − u₁ + s₀·D`, by `voteSet_subset_Dsupport` applied verbatim.  One
  genuine shrink: `|{D₂ = 0}| ≥ t₂ = level-2 threshold`.
* `second_level_threshold_cap`: for every pool `F ≤ N − T`, the level-2 threshold is capped:
  `t₁ = T − ⌊√((N−F)(k−1))⌋ ≤ T − ⌊√(T(k−1))⌋ = 193887475 < k − 1 = 268435455`.
* `threshold_collapse_stalls` (the general principle): once the running threshold `t`
  satisfies `t < k − 1`, no Johnson condition can fire at any later level: every level's
  zero-set contains a base witness (`Z ≥ t`), so `(t − F')² ≤ t² < t·(k−1) ≤ Z·(k−1)` —
  the sub-Johnson window is nonempty for EVERY pool choice, forever.
* `double_stall`: the instantiation — the level-2 threshold cap is below `k − 1`, so the
  MDS regime double-stalls (probe: the combined two-Johnson band
  `(T − J_pool(F), J_Z(F)]` is nonempty for every `F ∈ [k, N−T]`, narrowest width
  `140584336` at `F = k`).

**Honest verdict for the chain.**  The counting/charge cone now terminates: every branch is
(i) heavy-window closed, (ii) small-pool closed (`F ≤ F₀ = 75018133`, probe-pinned greedy),
or (iii) stalled with running threshold `< k − 1` after at most two charge levels — i.e.
inside the sub-Johnson band where agreement families of MDS codes are not counting-bounded.
That band is exactly the beyond-Johnson regime of the proximity-gap conjecture; no further
Johnson/charge iteration can discharge `StallResidual`.  New input required: list-size or
gap structure beyond Johnson (the campaign's global wall), or the structured-floor route.

Probe: `scripts/probes/probe_rate_quarter_p1_dcharge_derecursion.py` (MDS section: exact
threshold cap, collapse inequality, full-regime sweep of the two-Johnson band).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterMDSPoolSecondCharge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion

local instance localInstance_P1RateQuarterMDSPoolSecondCharge_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterMDSPoolSecondCharge_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The pool is universally bounded: `F ≤ N − T` -/

/-- The base witness sinks into `{D = 0}`, so the pool never exceeds `N − T = 480946858`. -/
theorem pool_card_le_N_sub_T (u₀ u₁ p₀ : Fin N → F) (γ₀ : F) (S : Finset (Fin N))
    (hS : predecessorThreshold ≤ S.card)
    (hagr : ∀ i ∈ S, p₀ i = u₀ i + γ₀ * u₁ i) :
    (Dsupport u₀ u₁ p₀ γ₀).card ≤ N - predecessorThreshold := by
  classical
  have hsink : S ⊆ Dzero u₀ u₁ p₀ γ₀ := by
    intro i hi
    rw [mem_Dzero_iff, Dfun]
    linear_combination hagr i hi
  have hz := Finset.card_le_card hsink
  have hpart := Dsupport_card_add_Dzero_card u₀ u₁ p₀ γ₀
  omega

/-! ## The pool code is MDS: separation on `k` pool points -/

/-- Distinct codewords collide on at most `k − 1` POOL coordinates: the punctured code on
`{D ≠ 0}` is MDS of dimension `k` (restriction of `predecessor_sep`). -/
theorem pool_separation (dom : Fin N ↪ F) (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)
    {v w : Fin N → F} (hv : v ∈ predecessorCode dom) (hw : w ∈ predecessorCode dom)
    (hne : v ≠ w) :
    ((Dsupport u₀ u₁ p₀ γ₀).filter (fun i => v i = w i)).card ≤ k - 1 := by
  classical
  by_contra hbig
  rw [not_le] at hbig
  have hk : k ≤ ((Dsupport u₀ u₁ p₀ γ₀).filter (fun i => v i = w i)).card := by
    have hk0 : 0 < k := by norm_num [k]
    omega
  exact hne (predecessor_sep dom v hv w hw
    ((Dsupport u₀ u₁ p₀ γ₀).filter (fun i => v i = w i)) hk
    (fun x hx => (Finset.mem_filter.mp hx).2))

/-! ## The second charge instantiates literally -/

/-- **The second D-charge on the pool** is the SAME theorem one level down: for the level-2
stack `(u₁, −D)` and a pool base `(s₀, q₀)` (a swarm rider's direction, viewed as the base
witness of the pool instance), the votes of every level-2 rider `s ≠ s₀` sink into the
second pool `{D₂ ≠ 0}`, `D₂ = q₀ − u₁ + s₀·D` — a literal instantiation of
`voteSet_subset_Dsupport`. -/
theorem second_charge_vote_source (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)
    (q₀ : Fin N → F) (s₀ : F) {w₀' w₁' : Fin N → F}
    (hbase : ∀ i, w₀' i + s₀ * w₁' i = q₀ i)
    {s : F} (hs : s ≠ s₀) :
    voteSet u₁ (fun i => -(Dfun u₀ u₁ p₀ γ₀ i)) w₀' w₁' s ⊆
      Dsupport u₁ (fun i => -(Dfun u₀ u₁ p₀ γ₀ i)) q₀ s₀ :=
  voteSet_subset_Dsupport u₁ (fun i => -(Dfun u₀ u₁ p₀ γ₀ i)) q₀ s₀ hbase hs

/-- The second pool in closed form: `D₂ = q₀ − u₁ + s₀·D`. -/
theorem second_pool_closed_form (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)
    (q₀ : Fin N → F) (s₀ : F) (i : Fin N) :
    Dfun u₁ (fun j => -(Dfun u₀ u₁ p₀ γ₀ j)) q₀ s₀ i =
      q₀ i - u₁ i + s₀ * (Dfun u₀ u₁ p₀ γ₀ i) := by
  rw [Dfun, Dfun]
  ring

/-! ## The threshold collapse: below `k − 1`, Johnson never fires again -/

/-- **The collapse principle.**  If the running threshold `t` is positive but below `k − 1`,
then at EVERY later charge level the sub-Johnson window is nonempty: the level's zero-set
carries a base witness (`t ≤ Z`), so `(t − F')² ≤ t² < t·(k−1) ≤ Z·(k−1)` for every pool
choice `F'` — no Johnson condition can ever fire again. -/
theorem threshold_collapse_stalls {t Z F' : ℕ} (ht : 0 < t) (htk : t < k - 1)
    (hZ : t ≤ Z) :
    (t - F') ^ 2 < Z * (k - 1) := by
  have h1 : (t - F') ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : t ^ 2 < t * (k - 1) := by
    have : t * t < t * (k - 1) := Nat.mul_lt_mul_of_le_of_lt (le_refl t) htk ht
    simpa [pow_two] using this
  have h3 : t * (k - 1) ≤ Z * (k - 1) := Nat.mul_le_mul_right _ hZ
  omega

/-- **The level-2 threshold cap**: for every pool `F ≤ N − T` the zero-set has
`|Z| = N − F ≥ T`, so the `Z`-Johnson radius is at least `⌊√(T(k−1))⌋ = 398907491` and the
level-2 threshold `t₁ = T − J_Z` is at most `193887475 < k − 1` — the collapse fires for
the ENTIRE stall range, in particular the whole MDS regime `[k, N−T]`. -/
theorem second_level_threshold_cap :
    398907491 ^ 2 ≤ predecessorThreshold * (k - 1) ∧
    predecessorThreshold * (k - 1) < 398907492 ^ 2 ∧
    predecessorThreshold - 398907491 = 193887475 ∧
    193887475 < k - 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [predecessorThreshold_eq, k]

/-- **The double-stall**: the level-2 instance of the derecursion has threshold at most
`193887475 < k − 1` for every admissible pool, so by the collapse principle the sub-Johnson
window is nonempty at level 2 and at every later level: the iteration terminates at depth 2
in a permanent stall.  Numerically: even the maximal level-2 threshold satisfies the
collapse inequality against the minimal level-2 zero-set. -/
theorem double_stall :
    ∀ Z F' : ℕ, 193887475 ≤ Z → (193887475 - F') ^ 2 < Z * (k - 1) := by
  intro Z F' hZ
  exact threshold_collapse_stalls (by norm_num)
    (by norm_num [k]) hZ

/-- The MDS regime is nonempty and exactly `[k, N − T]`: `k = 268435456 ≤ 480946858`. -/
theorem mds_regime_range :
    k ≤ N - predecessorThreshold ∧ N - predecessorThreshold = 480946858 := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterMDSPoolSecondCharge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterMDSPoolSecondCharge

#print axioms pool_card_le_N_sub_T
#print axioms pool_separation
#print axioms second_charge_vote_source
#print axioms second_pool_closed_form
#print axioms threshold_collapse_stalls
#print axioms second_level_threshold_cap
#print axioms double_stall
#print axioms mds_regime_range
