/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._W15SafeBranchLinearCeiling

/-!
# LANE W15 part 6 (#466, thread ll:low-profile-fiber): THE WIDTH-`k` GAP IS CLOSED —
# the secant-pair refuter kills `L_near = 1` inside the strip `2n < 3a < 2n + k`

## Position in the lane

The part-4 trichotomy left exactly one strip undecided for the `L_near = 1` question of
`LargeZeroSafeLineListBudgeted`: `2n < 3a < 2n + k`.  Where the older proofs fail there:

* the TWO-BLOCK refuter (part 4) fails at its LARGE-ZERO gate: its zero set has size
  `2(n − a)`, and `2(n − a) ≥ a ⟺ 3a ≤ 2n` — in the strip the two blocks no longer
  cover a large-zero direction;
* the UD-PLUS discharge (part 3) fails at its INCLUSION-EXCLUSION step: two appearing
  codewords force `2a ≤ z + (k − 1) + 2(n − z)`, contradictory for all `z ≥ a` only
  when `3a ≥ 2n + k`.  In the strip, two appearing codewords are numerically allowed —
  but only on a NARROW band `z ∈ [a, 2n + k − 1 − 2a]` of width `< k`.

## The strip refuter: the secant pair

Both failures are repaired at once by pairing `0` with a NON-constant codeword `e`
(monic, `deg = k − 1`, roots `R ⊆ Z`) and letting the two codewords SHARE `k − 1`
support votes on a set `W` where `e` is CONSTANT `c* ≠ 0` — possible exactly when the
elementary symmetric functions match: `e₁(R) = e₁(W)`, `e₂(R) = e₂(W)` (then
`e − ∏(x − w)` is the constant `c* = e₃(W) − e₃(R)`).  At `(n, k, a) = (16, 4, 11)`
every budget is TIGHT: `Z = R ⊔ D₀ ⊔ D₁` (3+4+4 = 11 = a), support `= W ⊔ {i₀, i₁}`
(3+1+1 = 5); `0` appears at `γ = 0` on `R ∪ D₀ ∪ W ∪ {i₀}` (11 points) and `e` appears
at `γ = c*` on `R ∪ D₁ ∪ W ∪ {i₁}` (11 points); safety holds structurally (`0` scores
`|R ∪ D₀| = 7 < 11` on `Z`, `e` scores `|R| + |D₁| ≤ (k−1) + 4 = 7`, generic codewords
`≤ 2(k − 1) = 6`).

Probe `scripts/probes/probe_466_w15_widthk_gap.py` (deterministic, exit 0) finds the
coincidence `R = {0,1,2}`, `W = {3,7,10}` over `F₁₇` (`e₁ = 3`, `e₂ = 2` both,
`c* = 6`) and verifies the assembled line exactly: `Λ = 2`, safe, large-zero.  Notably
the strip hill-climbs top out at `Λ ∈ {0, 1}`: random search CANNOT find this
configuration — the symmetric-function design is essential.

## Headlines

1. `not_budget_one_of_two_appearing` — abstract: any safe large-zero line carrying two
   distinct appearing codewords refutes `L = 1`.
2. `secantPair_not_largeZeroSafeLineListBudgeted_one` — the parametric secant-pair
   refuter: structural safety + the two appearance certificates ⇒ `¬ L = 1`.  Fully
   general in `F`, `dom`, `n`, `k`, `a`.
3. `strip_shape_16_4_11_L_one_refuted` — the CONCRETE strip instantiation over
   `F = ZMod 17` with the standard domain: `¬ LargeZeroSafeLineListBudgeted dom 4 11 1`.
   The strip is refuted at the canonical rate-quarter strip shape (`a = 11` is the ONLY
   strip value at `n = 16, k = 4`): with parts 3–5, the `L_near = 1` question at
   `n = 16, k = 4` is now decided at EVERY `a ≥ 9`: refuted for `9 ≤ a ≤ 11`
   (two-block for `a ∈ {9, 10}`, secant pair for `a = 11`), proved for `a ≥ 12`
   (UD-plus).  The trichotomy is a sharp dichotomy at this shape family.
4. `strip_gates_16_4_11`, `twoBlock_gate_fails_at_11`, `udplus_gate_fails_at_11` — the
   machine-pinned failure points of the older proofs inside the strip.

## Honesty

* The concrete refutation is per-shape (`F = ZMod 17`, standard domain, `a = 11`); the
  parametric theorem covers any field/domain admitting the symmetric coincidence
  (`e₁, e₂`-matching disjoint `(k−1)`-sets with distinct `e₃`).  A UNIFORM strip
  refutation for all fields/domains would need an existence lemma for such
  coincidences (they are two equations in `2(k−1)` domain unknowns — generically
  solvable, not proved here).  The dichotomy claim is therefore: discharge at
  `2n + k ≤ 3a` (uniform, part 3); refutation at `3a < 2n + k` for every shape where a
  two-block OR secant-pair configuration exists — which the probe and this file certify
  at all shapes examined, including the full `n = 16, k = 4` family.
* Nothing here touches the safe-branch `mcaEvent` floor/ceiling (parts 1–2) or the
  discharge corollary (part 3); the weld consequence is as in part 4, extended to the
  strip: the safe branch cannot close at `L = 1` anywhere below `2n + k ≤ 3a`.

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W15WidthKGapClosed

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LineListMCAWeld
open ProximityGap.Frontier.W15SafeBranchLinearCeiling

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. The abstract two-appearing refuter -/

open Classical in
/-- Any zero-direction-safe, large-zero line carrying two distinct appearing codewords
refutes the near-code list budget `L = 1`. -/
theorem not_budget_one_of_two_appearing
    (dom : Fin n ↪ F) {k a : ℕ} {u₀ u₁ : Fin n → F} {c₀ c₁ : Fin n → F}
    (hne : ¬ SupportEligibleLineDirection a u₁)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (h0 : c₀ ∈ lineAppearingCodewords dom k a u₀ u₁)
    (h1 : c₁ ∈ lineAppearingCodewords dom k a u₀ u₁)
    (hcc : c₀ ≠ c₁) :
    ¬ LargeZeroSafeLineListBudgeted dom k a 1 := by
  intro hL
  have hbudget := hL u₀ u₁ hne hsafe
  rw [LineListBudgeted] at hbudget
  exact absurd hbudget
    (Nat.not_le.mpr (Finset.one_lt_card.mpr ⟨c₀, h0, c₁, h1, hcc⟩))

/-! ### 2. The parametric secant-pair line -/

/-- The secant-pair direction: `1` exactly off `P ∪ D₁`. -/
def secantDirection (P D₁ : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ P ∪ D₁ then 0 else 1

/-- The secant-pair offset: `0` on `P` (the zero-block `R ∪ D₀`), `e` on `D₁`, and the
free support design `w` elsewhere. -/
def secantOffset (P D₁ : Finset (Fin n)) (e w : Fin n → F) : Fin n → F :=
  fun i => if i ∈ P then 0 else if i ∈ D₁ then e i else w i

open Classical in
theorem directionZeroSet_secant (P D₁ : Finset (Fin n)) :
    directionZeroSet (secantDirection (F := F) P D₁) = P ∪ D₁ := by
  ext i
  rw [directionZeroSet, Finset.mem_filter]
  constructor
  · rintro ⟨-, hz⟩
    by_contra hi
    simp only [secantDirection, if_neg hi] at hz
    exact one_ne_zero hz
  · intro hi
    exact ⟨Finset.mem_univ _, by simp only [secantDirection, if_pos hi]⟩

open Classical in
/-- **Structural safety of the secant-pair line.**  On `Z = P ∪ D₁`: the codeword `0`
scores exactly `P` (`≤ a − 1`, using `e ≠ 0` on `D₁`); the codeword `e` scores its
`≤ k − 1` zeros in `P` plus `D₁`; every other codeword scores `≤ 2(k − 1)`. -/
theorem secant_zeroDirectionSafeLine
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (e w : Fin n → F) (he : e ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hene : e ≠ 0)
    {P D₁ : Finset (Fin n)} (hPD : Disjoint P D₁)
    (heD₁ : ∀ i ∈ D₁, e i ≠ 0)
    (hPa : P.card + 1 ≤ a) (hD₁a : k - 1 + D₁.card + 1 ≤ a)
    (hak : 2 * (k - 1) + 1 ≤ a) :
    ZeroDirectionSafeLine dom k a (secantOffset P D₁ e w) (secantDirection P D₁) := by
  intro c hc
  rw [directionZeroAgreementSet, directionZeroSet_secant]
  have hsplit : ((P ∪ D₁).filter (fun i => c i = secantOffset P D₁ e w i)).card
      ≤ (P.filter (fun i => c i = 0)).card + (D₁.filter (fun i => c i = e i)).card := by
    have hsub : (P ∪ D₁).filter (fun i => c i = secantOffset P D₁ e w i)
        ⊆ (P.filter (fun i => c i = 0)) ∪ (D₁.filter (fun i => c i = e i)) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiZ, hieq⟩ := hi
      rcases Finset.mem_union.mp hiZ with hP | hD
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, ?_⟩)
        simpa [secantOffset, if_pos hP] using hieq
      · have hiP : i ∉ P := Finset.disjoint_right.mp hPD hD
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hD, ?_⟩)
        simpa [secantOffset, if_neg hiP, if_pos hD] using hieq
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  by_cases hc0 : c = 0
  · subst hc0
    have hD : (D₁.filter (fun i => (0 : Fin n → F) i = e i)).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.filter_eq_empty_iff.mpr fun i hi h => ?_
      exact heD₁ i hi (by simpa using h.symm)
    have hP : (P.filter (fun i => (0 : Fin n → F) i = 0)).card ≤ P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  by_cases hce : c = e
  · subst hce
    have hPz : (P.filter (fun i => c i = 0)).card ≤ k - 1 := by
      refine le_trans (Finset.card_le_card ?_)
        (rsCode_pairwise_agreeSet_card_le dom hk hc (Submodule.zero_mem _) hene)
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hi).2⟩
    have hD : (D₁.filter (fun i => c i = c i)).card ≤ D₁.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · have hPz : (P.filter (fun i => c i = 0)).card ≤ k - 1 := by
      refine le_trans (Finset.card_le_card ?_)
        (rsCode_pairwise_agreeSet_card_le dom hk hc (Submodule.zero_mem _) hc0)
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hi).2⟩
    have hD : (D₁.filter (fun i => c i = e i)).card ≤ k - 1 := by
      refine le_trans (Finset.card_le_card ?_)
        (rsCode_pairwise_agreeSet_card_le dom hk hc he hce)
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    omega

open Classical in
/-- **HEADLINE (parametric): the secant-pair refuter.**  Structural safety plus two
appearance certificates (for the codewords `0` and `e`, at any two scalars) refute the
near-code budget `L = 1`. -/
theorem secantPair_not_largeZeroSafeLineListBudgeted_one
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (e w : Fin n → F) (he : e ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hene : e ≠ 0)
    {P D₁ : Finset (Fin n)} (hPD : Disjoint P D₁)
    (heD₁ : ∀ i ∈ D₁, e i ≠ 0)
    (hzc : a ≤ P.card + D₁.card)
    (hPa : P.card + 1 ≤ a) (hD₁a : k - 1 + D₁.card + 1 ≤ a)
    (hak : 2 * (k - 1) + 1 ≤ a)
    {γ₀ γ₁ : F}
    (happ0 : a ≤ (agreeSet (0 : Fin n → F)
      (fun i => secantOffset P D₁ e w i + γ₀ • secantDirection P D₁ i)).card)
    (happe : a ≤ (agreeSet e
      (fun i => secantOffset P D₁ e w i + γ₁ • secantDirection P D₁ i)).card) :
    ¬ LargeZeroSafeLineListBudgeted dom k a 1 := by
  have hne : ¬ SupportEligibleLineDirection a (secantDirection (F := F) P D₁) := by
    rw [SupportEligibleLineDirection, directionZeroSet_secant]
    have := Finset.card_union_of_disjoint hPD
    omega
  refine not_budget_one_of_two_appearing dom
    (u₀ := secantOffset P D₁ e w) (u₁ := secantDirection P D₁) hne
    (secant_zeroDirectionSafeLine dom hk e w he hene hPD heD₁ hPa hD₁a hak)
    (c₀ := (0 : Fin n → F)) (c₁ := e) ?_ ?_ (fun h => hene h.symm)
  · rw [lineAppearingCodewords, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Submodule.zero_mem _, γ₀, happ0⟩
  · rw [lineAppearingCodewords, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, he, γ₁, happe⟩

/-! ### 3. The concrete strip instantiation: `F = ZMod 17`, `(n, k, a) = (16, 4, 11)`

Probe certificate: `R = {0,1,2}` (so `e = X(X−1)(X−2)`), `W = {3,7,10}`
(`e₁ = 3, e₂ = 2` match; `c* = e(3) = 6`), `D₀ = {4,5,6,8}`, `D₁ = {9,11,12,13}`,
`i₀ = 14`, `i₁ = 15`; `u₀(15) = e(15) − c* = 10 − 6 = 4`. -/

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The standard 16-point domain in `F₁₇`. -/
def dom17 : Fin 16 ↪ ZMod 17 where
  toFun i := (i.val : ZMod 17)
  inj' := by
    intro i j h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv

/-- The strip codeword: `e = X(X−1)(X−2)` evaluated on the standard domain. -/
def eStrip : Fin 16 → ZMod 17 :=
  fun i => dom17 i * (dom17 i - 1) * (dom17 i - 2)

/-- The zero-block `P = R ∪ D₀ = {0,1,2} ∪ {4,5,6,8}`. -/
def pStrip : Finset (Fin 16) := {0, 1, 2, 4, 5, 6, 8}

/-- The `e`-block `D₁ = {9, 11, 12, 13}`. -/
def dStrip : Finset (Fin 16) := {9, 11, 12, 13}

/-- The support design: `u₀ = 4` at index `15`, `0` at the other support points. -/
def wStrip : Fin 16 → ZMod 17 := fun i => if i = 15 then 4 else 0

theorem eStrip_mem_rsCode : eStrip ∈ (rsCode dom17 4 : Submodule (ZMod 17) _) := by
  refine ⟨X * (X - C 1) * (X - C 2), ?_, ?_⟩
  · have hm : (X * (X - C (1 : ZMod 17)) * (X - C 2)).Monic :=
      (monic_X.mul (monic_X_sub_C 1)).mul (monic_X_sub_C 2)
    have hdeg : (X * (X - C (1 : ZMod 17)) * (X - C 2)).natDegree = 3 := by
      rw [(monic_X.mul (monic_X_sub_C 1)).natDegree_mul (monic_X_sub_C 2),
        monic_X.natDegree_mul (monic_X_sub_C 1), natDegree_X, natDegree_X_sub_C,
        natDegree_X_sub_C]
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hdeg]
    exact_mod_cast (by norm_num : (3 : ℕ) < 4)
  · funext i
    simp [eStrip, eval_mul, eval_sub, eval_X, eval_C]

theorem eStrip_ne_zero : eStrip ≠ 0 := by
  intro h
  have h3 := congrFun h 3
  revert h3
  decide

/-- The appearance certificate set for the codeword `0` at `γ = 0`:
`P ∪ {3, 7, 10, 14}` (its zero-block plus the four support points where `u₀ = 0`). -/
def t0Strip : Finset (Fin 16) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 14}

/-- The appearance certificate set for the codeword `e` at `γ = c* = 6`:
`R ∪ D₁ ∪ W ∪ {15}`. -/
def t1Strip : Finset (Fin 16) := {0, 1, 2, 3, 7, 9, 10, 11, 12, 13, 15}

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The strip is REFUTED at its canonical rate-quarter shape.**  Over `F = ZMod 17`
with the standard 16-point domain: `L_near = 1` is FALSE at `(k, a) = (4, 11)` — the
unique strip value at `n = 16, k = 4` (`32 < 33 < 36`).  Together with parts 3–5, the
`L_near = 1` question at `n = 16, k = 4` is decided at every `a ≥ 9`: refuted for
`a ∈ {9, 10}` (two-block) and `a = 11` (secant pair), proved for `a ≥ 12` (UD-plus). -/
theorem strip_shape_16_4_11_L_one_refuted :
    ¬ LargeZeroSafeLineListBudgeted dom17 4 11 1 := by
  refine secantPair_not_largeZeroSafeLineListBudgeted_one dom17 (by norm_num)
    eStrip wStrip eStrip_mem_rsCode eStrip_ne_zero (P := pStrip) (D₁ := dStrip)
    (γ₀ := 0) (γ₁ := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) ?_ ?_
  · -- codeword 0 appears at γ = 0 on the 11-point certificate set t0Strip
    have hpt : ∀ i ∈ t0Strip,
        (0 : ZMod 17) = secantOffset pStrip dStrip eStrip wStrip i
          + (0 : ZMod 17) • secantDirection pStrip dStrip i := by decide
    have hsub : t0Strip ⊆ agreeSet (0 : Fin 16 → ZMod 17)
        (fun i => secantOffset pStrip dStrip eStrip wStrip i
          + (0 : ZMod 17) • secantDirection pStrip dStrip i) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hpt i hi⟩
    calc (11 : ℕ) = t0Strip.card := by decide
      _ ≤ _ := Finset.card_le_card hsub
  · -- codeword e appears at γ = 6 on the 11-point certificate set t1Strip
    have hpt : ∀ i ∈ t1Strip,
        eStrip i = secantOffset pStrip dStrip eStrip wStrip i
          + (6 : ZMod 17) • secantDirection pStrip dStrip i := by decide
    have hsub : t1Strip ⊆ agreeSet eStrip
        (fun i => secantOffset pStrip dStrip eStrip wStrip i
          + (6 : ZMod 17) • secantDirection pStrip dStrip i) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hpt i hi⟩
    calc (11 : ℕ) = t1Strip.card := by decide
      _ ≤ _ := Finset.card_le_card hsub

/-! ### 4. The machine-pinned failure points and gates -/

/-- `(16, 4, 11)` is inside the strip: `2n < 3a < 2n + k`. -/
theorem strip_gates_16_4_11 : 2 * 16 < 3 * 11 ∧ 3 * 11 < 2 * 16 + 4 := by norm_num

/-- The part-4 two-block refuter fails in the strip exactly at its large-zero gate. -/
theorem twoBlock_gate_fails_at_11 : ¬ (3 * 11 ≤ 2 * 16) := by norm_num

/-- The part-3 UD-plus discharge fails in the strip exactly at its counting gate. -/
theorem udplus_gate_fails_at_11 : ¬ (2 * 16 + 4 ≤ 3 * 11) := by norm_num

end ProximityGap.Frontier.W15WidthKGapClosed

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.not_budget_one_of_two_appearing
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.directionZeroSet_secant
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.secant_zeroDirectionSafeLine
#print axioms
  ProximityGap.Frontier.W15WidthKGapClosed.secantPair_not_largeZeroSafeLineListBudgeted_one
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.eStrip_mem_rsCode
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.eStrip_ne_zero
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.strip_shape_16_4_11_L_one_refuted
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.strip_gates_16_4_11
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.twoBlock_gate_fails_at_11
#print axioms ProximityGap.Frontier.W15WidthKGapClosed.udplus_gate_fails_at_11
