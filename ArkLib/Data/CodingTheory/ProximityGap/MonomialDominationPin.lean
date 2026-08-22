/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralGapCensusLaw
import ArkLib.Data.CodingTheory.ProximityGap.SmoothLadderInstance

/-!
# The monomial-domination pin: the corrected conditional δ* answer (v3)

The census-conditional pin chain went through two red-team kills (`CensusExtremalFloor`,
`TakeoverCountermodel`): the agreement-matched census and its floor repair are both
false as upper-extremality surfaces. The corrected surface — supported by every exact
maximizer audit ((5,4,2) exhaustive, (12,6) exact-profile, (16,4)/(16,8) scans) and now
fully law-governed by the gap census law — is **monomial domination**: the MCA supremum
at each grid radius is attained (up to the stated inequality) on monomial-pair stacks.

This file states that surface as the campaign's named open hypothesis and rebuilds the
conditional pin on it:

* `monomialEps` — the monomial-pair MCA error: the `epsMCA`-style sup restricted to
  stacks `(x^s, x^t)`, `s, t < n` (on `μ_n` this loses nothing by `x^n = 1`); always a
  lower bound for `epsMCA` (`monomialEps_le_epsMCA`) — the conjectural content is only
  the reverse domination.
* `MonomialDomination` — the named hypothesis: above the crossing agreement,
  `ε_mca(C, 1 − a/n) ≤ monomialEps(a)`. By the gap census law, `monomialEps(a)·|F|` is
  the max over `(s, t)` of punctured-band witness counts — a finite, per-instance
  checkable family. **This surface survives both prior countermodels by construction**
  (the take-over stack and every probe maximizer are themselves monomial pairs).
* `mcaDeltaStar_eq_of_monomialCrossing` — **the v3 conditional pin**: monomial
  domination above `ac` + monomial-census numerics (`monomialEps ≤ ε*` above the
  crossing) + any lower witness at the crossing (e.g. the hypothesis-free ladder floor
  `smooth_ladder_eps_ge` whenever `ε* < (n/g)/|F|`) ⟹ `mcaDeltaStar = 1 − ac/n`
  exactly.
* `mcaDeltaStar_eq_of_monomial_ladder` — the smooth-domain packaging: on `μ_n` the
  crossing's bad half is **discharged by the ladder theorem** — the only remaining
  inputs are `MonomialDomination` and the finite census numerics.

The honest status ledger: lower side at the crossing = theorem (ladder); the radius
quantization = theorem; the bracket engine = theorem; the census laws = theorems;
**the single named open input is `MonomialDomination`** — the precise, falsifiable,
probe-supported form of "where in the window does δ* sit" after this session's arc.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the corrected architecture); `GeneralGapCensusLaw.lean` (the surface's
  law), `SmoothLadderInstance.lean` (the crossing's lower witness),
  `CensusConditionalPin.lean` (the quantization and jump engines).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MonomialDominationPin

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothLadderInstance

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} (dom : Fin n → F)

/-! ## The monomial-pair MCA error -/

open Classical in
/-- The MCA error restricted to monomial-pair stacks `(x^s, x^t)`, exponents below `n`
(on `μ_n` the cap is lossless: `x^n = 1`). -/
noncomputable def monomialEps (C : Set (Fin n → F)) (δ : ℝ≥0) : ENNReal :=
  ⨆ s : Fin n, ⨆ t : Fin n,
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (A := F) C δ
      (fun i => dom i ^ (s : ℕ)) (fun i => dom i ^ (t : ℕ)) γ]

open Classical in
/-- Monomial pairs are a sub-family of all stacks: the monomial error never exceeds the
full MCA error. The conjectural content of the corrected surface is only the reverse. -/
theorem monomialEps_le_epsMCA [Nonempty (Fin n)] (C : Set (Fin n → F)) (δ : ℝ≥0) :
    monomialEps dom C δ ≤ epsMCA (F := F) (A := F) C δ := by
  refine iSup_le fun s => iSup_le fun t => ?_
  exact mcaEvent_prob_le_epsMCA (F := F) (A := F) C δ
    ![fun i => dom i ^ (s : ℕ), fun i => dom i ^ (t : ℕ)]

/-- **The named open hypothesis (the corrected extremality surface, v3):** above the
crossing agreement, the full MCA error is dominated by the monomial-pair error. Survives
both prior countermodels by construction (their witnesses are monomial pairs); falsifier
= any non-monomial stack beating every monomial pair at some grid radius. -/
def MonomialDomination (C : Set (Fin n → F)) (ac : ℕ) : Prop :=
  ∀ a : ℕ, ac < a → a ≤ n →
    epsMCA (F := F) (A := F) C (1 - (a : ℝ≥0) / (n : ℝ≥0))
      ≤ monomialEps dom C (1 - (a : ℝ≥0) / (n : ℝ≥0))

/-! ## The v3 conditional pin -/

open Classical in
/-- **The monomial-domination δ\* pin (v3).** Monomial domination above the crossing,
monomial-census numerics above the crossing, and any bad witness at the crossing pin
`mcaDeltaStar = 1 − ac/n` exactly. -/
theorem mcaDeltaStar_eq_of_monomialCrossing [Nonempty (Fin n)]
    (C : Set (Fin n → F)) (εstar : ℝ≥0∞) {ac : ℕ} (hacn : ac ≤ n)
    (hdom : MonomialDomination dom C ac)
    (hnum : ∀ a : ℕ, ac < a → a ≤ n →
      monomialEps dom C (1 - (a : ℝ≥0) / (n : ℝ≥0)) ≤ εstar)
    (hbad : εstar < epsMCA (F := F) (A := F) C (1 - (ac : ℝ≥0) / (n : ℝ≥0))) :
    mcaDeltaStar (F := F) (A := F) C εstar = 1 - (ac : ℝ≥0) / (n : ℝ≥0) := by
  have hn : n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
  refine MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump C εstar tsub_le_self ?_ hbad
  intro δ hδ
  have hquant := epsMCA_eq_grid (F := F) (A := F) C δ
  rw [Fintype.card_fin] at hquant
  rw [hquant]
  set a := agreeOf n δ with ha
  have haf : agreeOf (Fintype.card (Fin n)) δ = a := by rw [Fintype.card_fin]
  have hale : a ≤ n := by
    rw [ha]
    exact agreeOf_le n δ
  have hac_lt : ac < a := by
    have h2 : (ac : ℝ≥0) / (n : ℝ≥0) < 1 - δ := by
      rw [lt_tsub_iff_right]
      calc (ac : ℝ≥0) / (n : ℝ≥0) + δ = δ + (ac : ℝ≥0) / (n : ℝ≥0) := add_comm _ _
        _ < 1 := by rwa [← lt_tsub_iff_right]
    have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by
      have : 0 < n := Fin.pos_iff_nonempty.mpr ‹Nonempty (Fin n)›
      exact_mod_cast this
    have h3 : (ac : ℝ≥0) < (1 - δ) * (n : ℝ≥0) := by
      have := mul_lt_mul_of_pos_right h2 hn0
      rwa [div_mul_cancel₀ _ (ne_of_gt hn0)] at this
    rw [ha]
    unfold agreeOf
    exact Nat.lt_ceil.mpr h3
  exact le_trans (hdom a hac_lt hale) (hnum a hac_lt hale)

open Classical in
/-- **The smooth-domain packaging:** on `μ_n = ⟨γ⟩` the crossing's bad half is the
hypothesis-free ladder floor — `ε* < (n/g)/|F|` at a ladder-admissible crossing
discharges it. The only remaining inputs are `MonomialDomination` and the finite
monomial-census numerics. -/
theorem mcaDeltaStar_eq_of_monomial_ladder (γ : F) {m e g : ℕ}
    (hord : orderOf γ = n) (hm : n = 2 * m) (hm1 : 1 ≤ m)
    (he1 : 1 ≤ e) (hek : e + 1 ≤ k) (hg : g = Nat.gcd e n) (hgm : g ∣ m)
    {ac : ℕ} (hkac : k + g ≤ ac) (hacm : ac ≤ m + g)
    (hchar : (-1 : F) ≠ 1) {εstar : ℝ≥0∞}
    (hdom : MonomialDomination (smoothDom γ n)
      (evalCode (smoothDom γ n) k : Set (Fin n → F)) ac)
    (hnum : ∀ a : ℕ, ac < a → a ≤ n →
      monomialEps (smoothDom γ n) (evalCode (smoothDom γ n) k : Set (Fin n → F))
        (1 - (a : ℝ≥0) / (n : ℝ≥0)) ≤ εstar)
    (hsmall : εstar < ((n / g : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
      (evalCode (smoothDom γ n) k : Set (Fin n → F)) εstar
      = 1 - (ac : ℝ≥0) / (n : ℝ≥0) := by
  have hn1 : 1 ≤ n := by omega
  have hnone : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hg1 : 1 ≤ g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgm' : g ≤ m := Nat.le_of_dvd hm1 hgm
  refine mcaDeltaStar_eq_of_monomialCrossing (smoothDom γ n) _ εstar
    (by omega) hdom hnum ?_
  have hfloor := smooth_ladder_eps_ge (γ := γ) (k := k) hord hm hm1 he1 hek hg hgm
    (a := ac) hkac hacm hchar
  rw [Fintype.card_fin] at hfloor
  exact lt_of_lt_of_le hsmall hfloor

/-! ## Source audit -/

#print axioms monomialEps_le_epsMCA
#print axioms mcaDeltaStar_eq_of_monomialCrossing
#print axioms mcaDeltaStar_eq_of_monomial_ladder

end ProximityGap.MonomialDominationPin
