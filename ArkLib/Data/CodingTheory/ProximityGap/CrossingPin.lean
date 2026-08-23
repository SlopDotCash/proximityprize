/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAFullLayerSupply
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The crossing pin: δ* as the inverse binomial staircase (#357, item 20)

Item 20 of the 26-thread review: the production crossing ("δ* localized to one
number per rate") as a **named conditional theorem**.  In the census regime, the
landed engines say `ε_mca(C, δ) = C(n, t)/q` at floor `t` (LYM ceiling above,
full-layer supply below).  This file assembles them through the step-function law
and the threshold ledger into the closed form:

**`mcaDeltaStar_eq_inverse_binomial`** — if `ε*` sits between two consecutive
binomial steps, `C(n,t*)/q ≤ ε* < C(n,t*−1)/q`, and the layer below the crossing is
supplied, then

  `mcaDeltaStar(C, ε*) = (n − t* + 1)/n`.

The price tag is explicit: one `FullLayerSupply` instance at the crossing floor
(probe-measurable per cell; verified at every tested cell).  At the target
parameters (`ε* = 2^{−128}`, `q < 2^{256}`) the crossing floor `t*` is the unique
solution of `C(n, t*) ≤ q·2^{−128} < C(n, t*−1)` — "one number per rate".  The
good side needs no supply at all: it is the unconditional LYM ceiling transported
along bands by the step-function law and the anti-monotonicity of binomials above
the middle.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.CrossingPin

open ProximityGap.MCAThresholdLedger ProximityGap.MCAStepFunction
open ProximityGap.MCALYMCeiling ProximityGap.MCAFullLayerSupply

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Binomials are anti-monotone above the middle: `C(n,b) ≤ C(n,a)` for
`a ≤ b` with `n ≤ 2a`. -/
theorem choose_anti_above_half {n a b : ℕ} (hab : a ≤ b) (hhalf : n ≤ 2 * a) :
    n.choose b ≤ n.choose a := by
  by_cases hbn : b ≤ n
  · -- pass to the reflection: C(n,b) = C(n, n−b), both below the middle
    rw [← Nat.choose_symm hbn, ← Nat.choose_symm (le_trans hab hbn)]
    have h1 : n - b ≤ n - a := by omega
    -- monotone below the middle, by induction on the gap
    have key : ∀ s r : ℕ, r + s ≤ n - a → n.choose r ≤ n.choose (r + s) →
        True := fun _ _ _ _ => trivial
    clear key
    -- direct induction: C(n, r) ≤ C(n, r+1) whenever r < n/2; chain from n−b to n−a
    have step : ∀ r : ℕ, 2 * (r + 1) ≤ n → n.choose r ≤ n.choose (r + 1) := by
      intro r hr
      exact Nat.choose_le_succ_of_lt_half_left (by omega)
    have chain : ∀ s r : ℕ, 2 * (r + s) ≤ n → n.choose r ≤ n.choose (r + s) := by
      intro s
      induction s with
      | zero => intro r _; simp
      | succ s ih =>
          intro r hr
          calc n.choose r ≤ n.choose (r + s) := ih r (by omega)
            _ ≤ n.choose (r + s + 1) := step (r + s) (by omega)
            _ = n.choose (r + (s + 1)) := by ring_nf
    have := chain ((n - a) - (n - b)) (n - b) (by omega)
    rwa [show n - b + ((n - a) - (n - b)) = n - a by omega] at this
  · -- b > n: C(n,b) = 0
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

open Classical in
/-- **The crossing pin (the inverse binomial staircase).**  If
`C(n,t*)/q ≤ ε* < C(n,t*−1)/q` with `n ≤ 2(t*−1)` and the layer `t*−1` is supplied
at its boundary radius, then

  `mcaDeltaStar(C, ε*) = (n − t* + 1)/n`. -/
theorem mcaDeltaStar_eq_inverse_binomial (C : Submodule F (ι → A))
    {tstar : ℕ} {εstar : ℝ≥0∞}
    (ht1 : 1 ≤ tstar) (htn : tstar ≤ Fintype.card ι)
    (hhalf : Fintype.card ι ≤ 2 * (tstar - 1))
    (hsupply : FullLayerSupply (F := F) (C : Set (ι → A))
      (((Fintype.card ι - tstar + 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0))
      (tstar - 1))
    (hlo : (((Fintype.card ι).choose tstar : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < (((Fintype.card ι).choose (tstar - 1) : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar
      = ((Fintype.card ι - tstar + 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  set n := Fintype.card ι with hn
  have hn0 : (n : ℝ≥0) ≠ 0 := by
    simp [hn, Fintype.card_ne_zero]
  set δbad : ℝ≥0 := ((n - tstar + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0) with hδbad
  have hδb1 : δbad ≤ 1 := by
    rw [hδbad, div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0))]
    exact_mod_cast (by omega : n - tstar + 1 ≤ n)
  -- the boundary radius arithmetic: (1 − δbad)·n = t* − 1
  have hbound : (1 - δbad) * (n : ℝ≥0) = ((tstar - 1 : ℕ) : ℝ≥0) := by
    rw [tsub_mul, one_mul, hδbad, div_mul_cancel₀ _ hn0]
    rw [← Nat.cast_tsub]
    congr 1
    omega
  refine le_antisymm ?_ ?_
  · -- bad side: supply at the crossing floor
    refine mcaDeltaStar_le_of_bad _ _ ?_
    have heq := epsMCA_eq_choose_div_of_fullLayerSupply (F := F) (A := A) C
      (δ := δbad) (t := tstar - 1) (le_of_eq hbound.symm) (by omega) hsupply
    rw [heq]
    exact hhi
  · -- good side: every radius strictly below δbad is good
    by_contra h
    push Not at h
    obtain ⟨c, hc1, hc2⟩ := exists_between h
    -- the band floor of c
    set tc : ℕ := ⌈(1 - c) * (n : ℝ≥0)⌉₊ with htc
    have htcge : tstar ≤ tc := by
      have hlt : ((tstar - 1 : ℕ) : ℝ≥0) < (1 - c) * (n : ℝ≥0) := by
        rw [← hbound]
        have hcb : c < δbad := hc2
        have h1 : (1 : ℝ≥0) - δbad < 1 - c := by
          exact tsub_lt_tsub_left_of_le hδb1 hcb
        have hn0' : (0 : ℝ≥0) < (n : ℝ≥0) :=
          lt_of_le_of_ne (zero_le _) (Ne.symm hn0)
        calc (1 - δbad) * (n : ℝ≥0) < (1 - c) * (n : ℝ≥0) := by gcongr
          _ = _ := rfl
      have := Nat.lt_ceil.mpr hlt
      omega
    have htcn : tc ≤ n := by
      rw [htc]
      refine Nat.ceil_le.mpr ?_
      calc (1 - c) * (n : ℝ≥0) ≤ 1 * (n : ℝ≥0) := by gcongr; exact tsub_le_self
        _ = (n : ℝ≥0) := one_mul _
    -- move to the band boundary, apply LYM, descend the binomials
    set δhat : ℝ≥0 := ((n - tc : ℕ) : ℝ≥0) / (n : ℝ≥0) with hδhat
    have hhatbound : (1 - δhat) * (n : ℝ≥0) = (tc : ℝ≥0) := by
      have h1 : δhat ≤ 1 := by
        rw [hδhat, div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0))]
        exact_mod_cast (by omega : n - tc ≤ n)
      rw [tsub_mul, one_mul, hδhat, div_mul_cancel₀ _ hn0, ← Nat.cast_tsub]
      congr 1
      omega
    have hceil : ⌈(1 - c) * (n : ℝ≥0)⌉₊ = ⌈(1 - δhat) * (n : ℝ≥0)⌉₊ := by
      rw [hhatbound, Nat.ceil_natCast, ← htc]
    have hgood : epsMCA (F := F) (A := A) (C : Set (ι → A)) c ≤ εstar := by
      calc epsMCA (F := F) (A := A) (C : Set (ι → A)) c
          = epsMCA (F := F) (A := A) (C : Set (ι → A)) δhat :=
            epsMCA_eq_of_ceil_eq _ hceil
        _ ≤ ((n.choose tc : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
            epsMCA_le_choose_div C δhat (le_of_eq hhatbound.symm) (by omega)
        _ ≤ ((n.choose tstar : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
            refine ENNReal.div_le_div_right ?_ _
            exact_mod_cast choose_anti_above_half htcge (by omega)
        _ ≤ εstar := hlo
    have hc1' : c ≤ 1 := le_of_lt (lt_of_lt_of_le hc2 hδb1)
    have hle := le_mcaDeltaStar_of_good (F := F) (A := A)
      (C : Set (ι → A)) εstar hc1' hgood
    exact absurd hle (not_le.mpr hc1)

end ProximityGap.CrossingPin

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.CrossingPin.choose_anti_above_half
#print axioms ProximityGap.CrossingPin.mcaDeltaStar_eq_inverse_binomial
