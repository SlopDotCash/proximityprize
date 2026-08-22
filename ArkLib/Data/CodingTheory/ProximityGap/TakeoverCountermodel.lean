/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusExtremalFloor

/-!
# The take-over countermodel: `CensusUpperExtremalFloor` is FALSE at the death radius

Second red-team kill in the census-conditional pin chain (#357). The floor repair
(`CensusExtremalFloor.lean`) asserted that at the adjacent family's death radii nothing
takes over beyond the universal `1/|F|` floor. The registered falsifier — the
higher-monomial scan at the death rung — found a take-over
(`probe_takeover_death_radius.py`, certificates re-verified by an independent fitter):

**At `(n,k) = (16,4)` over `F₉₇`, at the death rung `a = 7` (where the adjacent census is
empty), the half-order pair `(X⁹, X⁸)` has exactly `16 = n` bad scalars — the bad set is
the domain `μ₁₆` itself, field-independently (same at `p = 193`).**

The mechanism is fully transparent — **coset splitting**: on `μ₁₆`, `x⁸ = ±1` on the two
`μ₈`-cosets, so `x⁹ + λx⁸ = ±(x + λ)` is piecewise linear; a witness with six points on
one coset and the single crossing point `x` with `x = −λ`-cancellation on the other is
explained by the linear polynomial `±(X + λ)`, while neither row alone is explainable
there. This is the CS25/KK25-style splitting appearing as the take-over family below the
adjacent death radius.

This file machine-checks the kill:

* `census_16_4_7_empty` — the adjacent constrained census at `(16,4)`, `a = 7` over `F₉₇`
  is **empty** (kernel `decide` over all `C(16,7) = 11440` subsets — the O139/O141
  measurement, now a theorem at this instance).
* `event_lam1`, `event_lam8` — two explicit bad scalars for the `(X⁹, X⁸)` stack at the
  grid radius `1 − 7/16`, with explicit linear explanations (`96 + 96X`, `8 + X`) and the
  coset no-joint argument (a cubic agreeing with a constant on six points is that
  constant, and fails at the crossing point).
* `takeover_falsifies` — hence `ε_mca ≥ 2/97 > 1/97 = (census + 1)/|F|`:
  **`CensusUpperExtremalFloor` is false at `(16,4)` over `F₉₇` for every crossing
  `ac < 7`.**

**What survives, corrected.** The pin engine (`mcaDeltaStar_eq_of_censusCrossing`-family)
is agnostic to which census function is plugged in; `census_le_epsMCA` remains a valid
lower bound (now joined by the half-pair's). The corrected upper target must be stated
over the **excess census** — the bad-scalar counts of `(X^s, X^{s−1})` for all `s ≥ a`
(the agreement-matched `constrainedCensus` is the `s = a` slice; the take-over is the
`s = n/2 + 1` slice, with its own flat-`n` law). Formalizing the excess census law is the
census lane's next target; until then the campaign has **no standing upper-extremality
hypothesis**, and the honest δ* statement for this family is bracket-only.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the take-over probe and mechanism); `DISPROOF_LOG.md` entry of same date.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ProximityGap.TakeoverCountermodel

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound
open ProximityGap.CensusExtremalFloor

instance primeFact_TakeoverCountermodel_1 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The base field `F₉₇` (`16 ∣ 96`, so `μ₁₆ ⊆ F₉₇ˣ`). -/
abbrev F97 := ZMod 97

/-- The smooth domain `μ₁₆ = ⟨8⟩ ⊆ F₉₇ˣ` in generator order. -/
def gdom16 : Fin 16 → F97 :=
  ![1, 8, 64, 27, 22, 79, 50, 12, 96, 89, 33, 70, 75, 18, 47, 85]

theorem gdom16_injective : Function.Injective gdom16 := by decide

/-- The domain as a Finset. -/
def H16 : Finset F97 := {1, 8, 64, 27, 22, 79, 50, 12, 96, 89, 33, 70, 75, 18, 47, 85}

theorem image_gdom16 : Finset.univ.image gdom16 = H16 := by decide

/-! ## The kernel-checked empty census (the O139/O141 measurement, formal) -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **The adjacent census is empty at the death rung:** no 7-subset of `μ₁₆ ⊆ F₉₇` has
`e₂ = e₃ = 0`. Kernel `decide` over all `C(16,7) = 11440` subsets. -/
theorem census_16_4_7_empty : constrainedCensus H16 4 7 = ∅ := by decide

/-! ## The take-over stack and its two certificate scalars -/

/-- Row 0 of the take-over stack: `x ↦ x⁹`. -/
def urow : Fin 16 → F97 := fun i => gdom16 i ^ 9

/-- Row 1: `x ↦ x⁸` (the coset indicator: `±1` on the two `μ₈`-cosets). -/
def vrow : Fin 16 → F97 := fun i => gdom16 i ^ 8

/-- A cubic agreeing with a constant on four or more points is that constant, and then
cannot take a different value anywhere: the no-joint device for the coset argument. -/
theorem cubic_const_fail {q' : Polynomial F97} (hq' : q'.natDegree ≤ 3)
    {c y : F97} {P : Finset F97} (hPcard : 4 ≤ P.card)
    (hvan : ∀ x ∈ P, q'.eval x = c) {x₀ : F97} (hx₀ : q'.eval x₀ = y)
    (hne : y ≠ c) : False := by
  classical
  set g : Polynomial F97 := q' - C c with hg
  have hg0 : g = 0 := by
    by_contra hgne
    have hsub : P ⊆ g.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
      show g.IsRoot x
      rw [Polynomial.IsRoot, hg, Polynomial.eval_sub, Polynomial.eval_C,
        hvan x hx, sub_self]
    have hgdeg : g.natDegree ≤ 3 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [Polynomial.natDegree_C]
      exact max_le hq' (by omega)
    have : 4 ≤ g.natDegree := by
      calc 4 ≤ P.card := hPcard
        _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
        _ ≤ g.natDegree := Polynomial.card_roots' g
    omega
  have hq'c : q' = C c := by
    have := sub_eq_zero.mp hg0
    exact this
  rw [hq'c, Polynomial.eval_C] at hx₀
  exact hne hx₀.symm

/-- The explicit linear explanation `c₀ + c₁X` is a codeword of the degree-`<4` code. -/
theorem linear_mem (c₀ c₁ : F97) :
    (fun i => c₀ + c₁ * gdom16 i) ∈ (evalCode gdom16 4 : Set (Fin 16 → F97)) := by
  refine (mem_evalCode _).mpr ⟨C c₀ + C c₁ * X, ?_, fun i => ?_⟩
  · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · rw [Polynomial.natDegree_C]; omega
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_X]; omega
  · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- Builder for the two certificate events at radius `1 − 7/16`. -/
theorem event_of_certificate (lam c₀ c₁ : F97) (T : Finset (Fin 16))
    (hcard : 7 ≤ T.card)
    (hagree : ∀ i ∈ T, c₀ + c₁ * gdom16 i = urow i + lam * vrow i)
    (P : Finset F97) (hPcard : 4 ≤ P.card) (cP : F97)
    (hPval : ∀ i ∈ T, gdom16 i ∈ P → vrow i = cP)
    (hPsub : ∀ x ∈ P, ∃ i ∈ T, gdom16 i = x)
    (i₀ : Fin 16) (hi₀ : i₀ ∈ T) (y₀ : F97) (hy₀ : vrow i₀ = y₀) (hy₀ne : y₀ ≠ cP) :
    mcaEvent (F := F97) (A := F97) (evalCode gdom16 4 : Set (Fin 16 → F97))
      (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 16) : ℝ≥0)) urow vrow lam := by
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; norm_num)]
  refine ⟨T, hcard, ⟨fun i => c₀ + c₁ * gdom16 i, linear_mem c₀ c₁, fun i hi => ?_⟩, ?_⟩
  · rw [smul_eq_mul]
    exact hagree i hi
  · -- no joint explanation: row 1 agrees with the constant `cP` on ≥ 4 points of `P`
    -- but takes the value `y₀ ≠ cP` at `i₀ ∈ T`
    rintro ⟨w₀, _, w₁, hw₁, hag⟩
    obtain ⟨q', hq', hw₁'⟩ := (mem_evalCode w₁).mp hw₁
    have hq'deg : q'.natDegree ≤ 3 := hq'
    refine cubic_const_fail hq'deg hPcard (c := cP) (P := P) ?_
      (x₀ := gdom16 i₀) ?_ hy₀ne
    · intro x hx
      obtain ⟨i, hiT, rfl⟩ := hPsub x hx
      rw [← hw₁' i, (hag i hiT).2]
      exact hPval i hiT hx
    · rw [← hw₁' i₀, (hag i₀ hi₀).2, hy₀]

/-- Certificate `λ = 1`: witness `T = {1,3,5,7,8,9,11}` (six minus-coset points and the
crossing point `96 = −1`), explanation `96 + 96X`. -/
theorem event_lam1 :
    mcaEvent (F := F97) (A := F97) (evalCode gdom16 4 : Set (Fin 16 → F97))
      (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 16) : ℝ≥0)) urow vrow 1 := by
  refine event_of_certificate 1 96 96 ({1, 3, 5, 7, 8, 9, 11} : Finset (Fin 16))
    (by decide) (by decide)
    ({8, 27, 79, 12, 89, 70} : Finset F97) (by decide) 96
    (by decide) (by decide)
    8 (by decide) 1 (by decide) (by decide)

/-- Certificate `λ = 8`: witness `T = {0,2,4,6,8,9,10}` (six plus-coset points and one
crossing), explanation `8 + X`. -/
theorem event_lam8 :
    mcaEvent (F := F97) (A := F97) (evalCode gdom16 4 : Set (Fin 16 → F97))
      (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 16) : ℝ≥0)) urow vrow 8 := by
  refine event_of_certificate 8 8 1 ({0, 2, 4, 6, 8, 9, 10} : Finset (Fin 16))
    (by decide) (by decide)
    ({1, 64, 22, 50, 96, 33} : Finset F97) (by decide) 1
    (by decide) (by decide)
    9 (by decide) 96 (by decide) (by decide)

/-! ## The falsification -/

open Classical in
/-- The take-over stack has at least two bad scalars at the death rung. -/
theorem eps_ge_two_div :
    (2 : ℝ≥0∞) / 97 ≤ epsMCA (F := F97) (A := F97)
      (evalCode gdom16 4 : Set (Fin 16 → F97))
      (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 16) : ℝ≥0)) := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F97) (A := F97) _ _ ![urow, vrow])
  have h0 : (![urow, vrow] : WordStack F97 (Fin 2) (Fin 16)) 0 = urow := rfl
  have h1 : (![urow, vrow] : WordStack F97 (Fin 2) (Fin 16)) 1 = vrow := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  have hsub : ({1, 8} : Finset F97) ⊆ Finset.filter
      (fun lam : F97 => mcaEvent (F := F97) (A := F97)
        (evalCode gdom16 4 : Set (Fin 16 → F97))
        (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 16) : ℝ≥0)) urow vrow lam)
      Finset.univ := by
    intro lam hlam
    rw [Finset.mem_insert, Finset.mem_singleton] at hlam
    rcases hlam with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, event_lam1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, event_lam8⟩
  have hcard2 : 2 ≤ (Finset.filter
      (fun lam : F97 => mcaEvent (F := F97) (A := F97)
        (evalCode gdom16 4 : Set (Fin 16 → F97))
        (1 - ((7 : ℕ) : ℝ≥0) / (Fintype.card (Fin 16) : ℝ≥0)) urow vrow lam)
      Finset.univ).card := by
    calc 2 = ({1, 8} : Finset F97).card := by decide
      _ ≤ _ := Finset.card_le_card hsub
  have hF : (Fintype.card F97 : ℝ≥0∞) = 97 := by
    rw [ZMod.card]; norm_num
  rw [hF]
  gcongr
  exact_mod_cast hcard2

/-- **The take-over falsification:** `CensusUpperExtremalFloor` is false at `(16,4)` over
`F₉₇` for every crossing below the death rung — the half-order pair carries `≥ 2` bad
scalars where the adjacent census (plus floor) allows at most one. -/
theorem takeover_falsifies (ac : ℕ) (hac : ac < 7) :
    ¬ CensusUpperExtremalFloor (F := F97)
      (evalCode gdom16 4 : Set (Fin 16 → F97)) (Finset.univ.image gdom16) 4 ac := by
  intro hext
  have h := hext 7 hac (by rw [Fintype.card_fin]; norm_num)
  rw [image_gdom16, census_16_4_7_empty] at h
  simp only [Finset.card_empty, Nat.zero_add, Nat.cast_one] at h
  have hF : (Fintype.card F97 : ℝ≥0∞) = 97 := by
    rw [ZMod.card]; norm_num
  rw [hF] at h
  have hcontra := le_trans eps_ge_two_div h
  have h12 : (1 : ℝ≥0∞) / 97 < 2 / 97 := by
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    norm_num
  exact absurd hcontra (not_le.mpr h12)

/-! ## Source audit -/

#print axioms census_16_4_7_empty
#print axioms event_lam1
#print axioms eps_ge_two_div
#print axioms takeover_falsifies

end ProximityGap.TakeoverCountermodel
