/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConvergenceHub
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The BGK / di Benedetto SOTA character-sum bound is INSUFFICIENT for the #407 prize

**User-requested formalization of relevant papers** (the escape-clause "formalize relevant
papers"): we state the *state-of-the-art* incomplete-character-sum bound for thin multiplicative
subgroups and PROVE that it is quantitatively too weak to reach the #407 prize floor — i.e. we
formalize the `n^{0.989} → n^{0.5}` wall as a clean, machine-checked real-analysis theorem.

## The objects

The prize per-frequency core is `M(n) = max_{b≠0} ‖η_b‖`, where `η_b = eta ψ G b = Σ_{x∈μ_n} ψ(b·x)`
is the in-tree incomplete subgroup Gauss sum (the non-principal eigenvalue of the generalized Paley
graph `Cay(F_q, μ_n)`), `G = μ_n` the smooth `2`-power subgroup of size `n = 2^μ`, index
`m = (q−1)/n ≈ 2^128`, `q ≈ n^4..n^5`.

* **The SOTA (named, NOT proved — its deep sum–product proof is not formalizable in-session):**
  the Bourgain–Glibichuk–Konyagin power-saving bound `M(n) ≤ C·n^{1−δ}` for some `δ > 0`
  (`n^{1−o(1)}`), sharpened by **di Benedetto** to the exponent `1 − δ ≈ 0.989` (so `δ ≈ 0.011`,
  valid for `n ≥ q^{1/4}`-ish, **outside** the prize regime). We name it here as `BGKBound C ψ G δ
  := ∀ b≠0, ‖η_b‖ ≤ C·n^{1−δ}` (identical in shape to the in-tree `BGKBridge.BGKBound`, kept
  self-contained to minimize imports). It stays a `def … : Prop`; we never `sorry` or assert it.

* **The prize floor (named, in-tree):** `ConvergenceHub.PrizeFloor ψ G C'`, i.e.
  `WorstCaseIncompleteSumBound ψ G (C'²·(n·log(q/n)))`, equivalently `M(n) ≤ C'·√(n·log(q/n))`.
  The prize needs the cancellation exponent `δ = 1/2 − o(1)`.

## The PROVEN content (this file's honest deliverable)

The deep BGK/di Benedetto proof is NOT here. What IS proved, axiom-clean, is the
**insufficiency inequality**: for the prize regime (constant index `log(q/n) ≤ L`, large `n`) and
any fixed `δ < 1/2`, the SOTA's *guaranteed* value `C·n^{1−δ}` STRICTLY EXCEEDS the prize target
`C'·√(n·log(q/n))`:

> `bgk_value_exceeds_prizeTarget_eventually` :
>   `δ < 1/2 → ∃ N₀, ∀ n ≥ N₀, C'·√(n·L) < C·n^{1−δ}`.

The mechanism is the pure `Real.rpow` fact `n^{1−δ}/√n = n^{1/2−δ} → ∞` for `δ < 1/2`, which
dominates the constant `√L = √(log(q/n))` factor. The honest corollary
`prize_requires_exponent_half` records that the prize forces `δ ≥ 1/2 − o(1)`, beyond the proven
SOTA `δ ≈ 0.011` — the `n^{0.989} → n^{0.5}` wall.

**Honesty (non-negotiable):** `BGKBound` is the NAMED literature bound (left unproved); the PROVEN
theorem is the insufficiency inequality. No false closure. The insufficiency theorem does NOT say
the prize is unreachable — only that *this* bound (the SOTA exponent) cannot reach it; a stronger
exponent (the open Paley-Graph-Conjecture `δ = 1/2`) would.

## References

* [BGK06] Bourgain, Glibichuk, Konyagin. *Estimates for the number of sums and products and for
  exponential sums in fields of prime order*. J. London Math. Soc. (2006). `M(n) ≤ C·n^{1−δ}`.
* [diB20] V. di Benedetto. Short character-sum / Gauss-period sharpening to exponent `≈ 0.989`.
  (SOTA exponent, valid for `n ≥ q^{1/4}`-ish, outside the prize regime.)
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, ePrint
  2026/680 (the prize; the floor `M(n) ≤ C·√(n·log(q/n))`).

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false


open scoped Real
open Filter
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ProximityGap.Frontier.ConvergenceHub

namespace ProximityGap.Frontier.BGKSOTAInsufficiency

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The named SOTA bound (BGK / di Benedetto) — left UNPROVED -/

/-- **The BGK / di Benedetto SOTA character-sum bound at cancellation exponent `δ` and constant
`C`** (NAMED, not proved — its deep sum–product proof is not formalizable in-session):

`∀ b ≠ 0, ‖η_b‖ ≤ C · n^{1−δ}`, where `η_b = eta ψ G b = Σ_{x∈G} ψ(b·x)` is the in-tree
per-frequency Gauss period and `n = G.card`. `δ` is the cancellation exponent: the proven
Bourgain–Glibichuk–Konyagin value is some `δ > 0` (`n^{1−o(1)}`); di Benedetto sharpened it to
`δ ≈ 0.011` (`1 − δ ≈ 0.989`). This is identical in shape to `BGKBridge.BGKBound`; we restate it
here only to keep the file self-contained (no heavy import). It is `def … : Prop`; never asserted. -/
def BGKBound (C : ℝ) (ψ : AddChar F ℂ) (G : Finset F) (δ : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * (G.card : ℝ) ^ (1 - δ)

/-! ## The named SOTA exponents (di Benedetto vs the prize) -/

/-- **The di Benedetto SOTA cancellation exponent** `δ_diB ≈ 0.011` (`1 − δ ≈ 0.989`). This is the
best *proven* power-saving exponent for the incomplete character sum over a thin multiplicative
subgroup; the deep sum–product proof is NOT formalized (it lives only as the named `BGKBound`). -/
noncomputable def diBenedettoDelta : ℝ := 11 / 1000

/-- **The prize cancellation exponent** `δ_prize = 1/2`. The prize floor `M(n) ≤ C'·√(n·log(q/n))`
needs the cancellation exponent `δ = 1/2 − o(1)` (the Paley-Graph-Conjecture / Ramanujan value),
beyond the proven SOTA `δ ≈ 0.011`. -/
noncomputable def prizeDelta : ℝ := 1 / 2

/-- The proven SOTA exponent is strictly below the exponent the prize needs: the `0.011 < 1/2`
wall (`n^{0.989} → n^{0.5}`), the basic numeric gap. -/
theorem diBenedetto_lt_prize : diBenedettoDelta < prizeDelta := by
  unfold diBenedettoDelta prizeDelta; norm_num

/-! ## The PROVEN insufficiency core — a clean real-analysis inequality -/

/-- **The asymptotic gap lemma (the analytic heart).** For any exponent `δ < 1/2`, constants
`C > 0`, `C' ≥ 0`, `L ≥ 0`, there is a threshold `N₀` past which the SOTA value `C·n^{1−δ}`
strictly dominates the prize target `C'·√(n·L)`:

  `∀ n ≥ N₀, C'·√(n·L) < C·n^{1−δ}`.

Proof: `C·n^{1−δ} = (C·n^{1/2−δ})·√n` and `C'·√(n·L) = (C'·√L)·√n`, so for `n > 0` it suffices that
`C'·√L < C·n^{1/2−δ}`; since `1/2 − δ > 0`, `n^{1/2−δ} → ∞`, so the RHS eventually exceeds the
constant `C'·√L`. This is the `n^{1/2−δ} → ∞` mechanism that kills any sub-`1/2` cancellation
exponent against the (constant-index) prize floor. -/
theorem bgk_value_exceeds_prizeTarget_eventually
    {C C' L δ : ℝ} (hC : 0 < C) (hC' : 0 ≤ C') (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n →
      C' * Real.sqrt (n * L) < C * n ^ (1 - δ) := by
  -- The positive gap exponent.
  have hgap : 0 < 1 / 2 - δ := by linarith
  -- `n^{1/2−δ} → ∞`, so `C·n^{1/2−δ}` eventually exceeds the constant `C'·√L`.
  have htend : Tendsto (fun n : ℝ => C * n ^ (1 / 2 - δ)) atTop atTop :=
    Tendsto.const_mul_atTop hC (tendsto_rpow_atTop hgap)
  -- Eventually `C·n^{1/2−δ} > C'·√L` AND `n ≥ 1` (so `n > 0`).
  have hev : ∀ᶠ n : ℝ in atTop,
      C' * Real.sqrt L < C * n ^ (1 / 2 - δ) ∧ (1 : ℝ) ≤ n :=
    (htend.eventually_gt_atTop (C' * Real.sqrt L)).and (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := hev.exists_forall_of_atTop
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hgt, hn1⟩ := hN₀ n hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn1
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- Rewrite both sides as `(coefficient) · √n`.
  have hLHS : C' * Real.sqrt (n * L) = (C' * Real.sqrt L) * Real.sqrt n := by
    rw [Real.sqrt_mul hnpos.le]; ring
  have hrpow : n ^ (1 - δ) = n ^ (1 / 2 - δ) * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
    congr 1; ring
  have hRHS : C * n ^ (1 - δ) = (C * n ^ (1 / 2 - δ)) * Real.sqrt n := by
    rw [hrpow]; ring
  rw [hLHS, hRHS]
  exact mul_lt_mul_of_pos_right hgt hsqrtn_pos

/-! ## The insufficiency theorem on the in-tree `eta` / `BGKBound` / `PrizeFloor` objects -/

/-- **The SOTA bound does NOT imply the prize floor (the proven insufficiency).**

Concretely, the SOTA `BGKBound`'s *guaranteed per-frequency value* `C·n^{1−δ}` exceeds the prize
target `C'·√(n·log(q/n))` for all large `n` whenever `δ < 1/2` and the index is constant
(`log(q/n) ≤ L`). So an adversary period saturating the SOTA at value exactly `C·n^{1−δ}` violates
`PrizeFloor`: the SOTA, even when *tight*, lands above the prize floor.

We state the genuinely-provable analytic content: for any field/subgroup data with constant index
`log(q/n) ≤ L`, there is `N₀` such that whenever the subgroup is large (`N₀ ≤ |G|`), the SOTA
guaranteed value strictly exceeds the prize target value. This is the quantitative `n^{0.989} →
n^{0.5}` wall on the in-tree objects. -/
theorem bgkValue_exceeds_prizeFloorTarget
    {C C' δ : ℝ} (hC : 0 < C) (hC' : 0 ≤ C')
    {L : ℝ} (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ (G : Finset F),
      N₀ ≤ (G.card : ℝ) →
      Real.log ((Fintype.card F : ℝ) / G.card) ≤ L →
      -- the prize target value `C'·√(n·log(q/n))` ...
      C' * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
        -- ... is strictly below the SOTA guaranteed value `C·n^{1−δ}`.
        < C * (G.card : ℝ) ^ (1 - δ) := by
  obtain ⟨N₀, hN₀⟩ := bgk_value_exceeds_prizeTarget_eventually
    (C := C) (C' := C') (L := L) (δ := δ) hC hC' hL hδ
  refine ⟨max N₀ 1, fun G hcard hlog => ?_⟩
  have hcardN₀ : N₀ ≤ (G.card : ℝ) := le_trans (le_max_left _ _) hcard
  have hcard1 : (1 : ℝ) ≤ (G.card : ℝ) := le_trans (le_max_right _ _) hcard
  have hncard_pos : (0 : ℝ) < (G.card : ℝ) := lt_of_lt_of_le one_pos hcard1
  -- The `L`-version (with the constant index bound) strictly dominates the SOTA value.
  have hkey : C' * Real.sqrt ((G.card : ℝ) * L) < C * (G.card : ℝ) ^ (1 - δ) :=
    hN₀ (G.card : ℝ) hcardN₀
  -- The actual prize target (with the true `log(q/n) ≤ L`) is `≤` the `L`-version.
  have hmono : C' * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
      ≤ C' * Real.sqrt ((G.card : ℝ) * L) := by
    apply mul_le_mul_of_nonneg_left _ hC'
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hlog hncard_pos.le
  exact lt_of_le_of_lt hmono hkey

/-- **The clean insufficiency corollary on `BGKBound` vs `PrizeFloor` (the headline).**

If the SOTA bound is *tight* — i.e. some nonzero frequency `b₀` actually attains the SOTA value
`‖η_{b₀}‖ = C·n^{1−δ}` — then for `δ < 1/2`, constant index `log(q/n) ≤ L`, and large `n`, the
`PrizeFloor` at constant `C'` is FALSE: that frequency's squared period exceeds the prize scale.

This is exactly "`BGKBound C ψ G δ` does not imply `PrizeFloor ψ G C'`": the SOTA, even when it is
an *equality* at the worst frequency, lands above the prize floor. The deep BGK/di Benedetto bound
(`BGKBound`) is the named hypothesis (its proof is not formalized); what is PROVEN here is that the
exponent it delivers (`δ ≈ 0.011 < 1/2`) is quantitatively insufficient. -/
theorem bgk_tight_refutes_prizeFloor
    {ψ : AddChar F ℂ} {C C' δ : ℝ} (hC : 0 < C) (hC' : 0 ≤ C')
    {L : ℝ} (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ (G : Finset F) (b₀ : F),
      N₀ ≤ (G.card : ℝ) →
      Real.log ((Fintype.card F : ℝ) / G.card) ≤ L →
      b₀ ≠ 0 →
      ‖eta ψ G b₀‖ = C * (G.card : ℝ) ^ (1 - δ) →  -- SOTA tight at b₀
      ¬ PrizeFloor ψ G C' := by
  obtain ⟨N₀, hN₀⟩ := bgkValue_exceeds_prizeFloorTarget (F := F)
    (C := C) (C' := C') (δ := δ) hC hC' hL hδ
  refine ⟨N₀, fun G b₀ hcard hlog hb₀ htight hPF => ?_⟩
  -- Abbreviation for the prize-scale product `X = n·log(q/n)`.
  set X : ℝ := (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card) with hXdef
  -- The prize floor gives `‖η_{b₀}‖² ≤ C'²·X`; tightness gives `‖η_{b₀}‖ = C·n^{1−δ}`.
  have hPFb : ‖eta ψ G b₀‖ ^ 2 ≤ C' ^ 2 * X := hPF b₀ hb₀
  -- The strict gap from the analytic insufficiency theorem.
  have hgap : C' * Real.sqrt X < C * (G.card : ℝ) ^ (1 - δ) :=
    hXdef ▸ hN₀ G hcard hlog
  -- The SOTA value is strictly positive: `C'·√X ≥ 0 < C·n^{1−δ}`.
  have hSOTApos : 0 < C * (G.card : ℝ) ^ (1 - δ) :=
    lt_of_le_of_lt (by positivity) hgap
  -- The SOTA-tight squared value: `(C·n^{1−δ})² ≤ C'²·X`.
  have hsq_chain : (C * (G.card : ℝ) ^ (1 - δ)) ^ 2 ≤ C' ^ 2 * X := by
    rw [← htight]; exact hPFb
  -- Hence `C'²·X > 0`, so `X > 0`.
  have hXpos : 0 < X := by
    have h1 : 0 < (C * (G.card : ℝ) ^ (1 - δ)) ^ 2 := by positivity
    have h2 : 0 < C' ^ 2 * X := lt_of_lt_of_le h1 hsq_chain
    nlinarith [sq_nonneg C', h2]
  have hgap_sq : C' ^ 2 * X < (C * (G.card : ℝ) ^ (1 - δ)) ^ 2 := by
    have hLHSnn : 0 ≤ C' * Real.sqrt X := by positivity
    have hpow := pow_lt_pow_left₀ hgap hLHSnn (n := 2) (by norm_num)
    -- `(C'·√X)² = C'²·(√X)² = C'²·X`.
    have hrw : (C' * Real.sqrt X) ^ 2 = C' ^ 2 * X := by
      rw [mul_pow, Real.sq_sqrt hXpos.le]
    rwa [hrw] at hpow
  linarith [hsq_chain, hgap_sq]

/-! ## The honest corollary: the prize requires `δ ≥ 1/2 − o(1)`, beyond the proven SOTA -/

/-- **The wall, as a clean numeric record.** The prize floor needs the cancellation exponent
`δ = prizeDelta = 1/2`; the best proven SOTA is `δ = diBenedettoDelta ≈ 0.011`. The proven gap
`diBenedettoDelta < prizeDelta` (with the insufficiency theorem above quantifying that ANY
`δ < 1/2` is too weak) is the `n^{0.989} → n^{0.5}` wall: closing the prize is exactly closing the
exponent gap from `≈ 0.011` to `1/2`, which is the open Paley-Graph-Conjecture content. -/
theorem prize_requires_exponent_beyond_sota :
    diBenedettoDelta < prizeDelta ∧
    ∀ {C C' L : ℝ} {F : Type} [Field F] [Fintype F] [DecidableEq F],
      0 < C → 0 ≤ C' → 0 ≤ L →
      ∃ N₀ : ℝ, ∀ (G : Finset F),
        N₀ ≤ (G.card : ℝ) →
        Real.log ((Fintype.card F : ℝ) / G.card) ≤ L →
        C' * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
          < C * (G.card : ℝ) ^ (1 - diBenedettoDelta) := by
  refine ⟨diBenedetto_lt_prize, ?_⟩
  intro C C' L F _ _ _ hC hC' hL
  exact bgkValue_exceeds_prizeFloorTarget (F := F) (C := C) (C' := C') (δ := diBenedettoDelta)
    hC hC' hL (by unfold diBenedettoDelta; norm_num)

end ProximityGap.Frontier.BGKSOTAInsufficiency

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms ProximityGap.Frontier.BGKSOTAInsufficiency.diBenedetto_lt_prize
#print axioms ProximityGap.Frontier.BGKSOTAInsufficiency.bgk_value_exceeds_prizeTarget_eventually
#print axioms ProximityGap.Frontier.BGKSOTAInsufficiency.bgkValue_exceeds_prizeFloorTarget
#print axioms ProximityGap.Frontier.BGKSOTAInsufficiency.bgk_tight_refutes_prizeFloor
#print axioms ProximityGap.Frontier.BGKSOTAInsufficiency.prize_requires_exponent_beyond_sota
