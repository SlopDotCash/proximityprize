/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAAntichainLYM
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactPin

/-!
# The family interior `δ*` pin (#357): parametric over the high-rate regime

`MCAWindowInteriorPin.lean` pinned `δ*` at one concrete interior point. This file lifts the
construction to a **parametric family**: for any linear code `C ⊆ Fⁿ` whose witness layer at
the jump radius is extremal, the interior `δ*` is pinned, parametric in `n` and a layer `t`:

  **`mcaDeltaStar(C, C(n,t+1)/q) = 1 − t/n`**  (`mcaDeltaStar_family_interior_pin`)

in the upper-half regime `n ≤ 2t`, conditional on the single named geometric hypothesis
`ExtremalWitnessLayer C t` (the jump radius attains the LYM ceiling). The good side is
**unconditional** (the sharp ceiling `epsMCA_le_choose_ceil_div`); only the extremal lower
bound is the named obligation — the modular pattern of the repo. The pin sits at the
granularity jump where the witness floor drops `t+1 → t`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger

namespace ProximityGap.MCAWindowInteriorFamily

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## Binomial antitonicity on the upper half -/

/-- `C(n, ·)` is antitone on the upper half: for `n ≤ 2a` and `a ≤ b ≤ n`, `C(n,b) ≤ C(n,a)`. -/
theorem choose_le_choose_upper (n : ℕ) {a b : ℕ}
    (hhalf : n ≤ 2 * a) (hab : a ≤ b) (hbn : b ≤ n) :
    n.choose b ≤ n.choose a := by
  have step : ∀ c : ℕ, n ≤ 2 * c → c < n → n.choose (c + 1) ≤ n.choose c := by
    intro c hc hcn
    have hsymm1 : n.choose (c + 1) = n.choose (n - (c + 1)) :=
      (Nat.choose_symm (by omega)).symm
    have hsymm2 : n.choose c = n.choose (n - c) := (Nat.choose_symm (by omega)).symm
    rw [hsymm1, hsymm2]
    have hlt : n - (c + 1) < n / 2 := by omega
    have h1 : n - (c + 1) + 1 = n - c := by omega
    have hmono := Nat.choose_le_succ_of_lt_half_left (n := n) (r := n - (c + 1)) hlt
    rwa [h1] at hmono
  rcases Nat.le.dest hab with ⟨d, rfl⟩
  clear hab
  revert hbn
  induction d with
  | zero => intro _; exact Nat.le_of_eq (by rw [Nat.add_zero])
  | succ e ih =>
      intro hbn
      have hae : a + e < n := by omega
      have hstep := step (a + e) (by omega) hae
      have hih := ih (by omega)
      rw [Nat.add_succ]
      exact le_trans hstep hih

/-! ## The named extremal-layer hypothesis -/

/-- **The extremal-witness-layer hypothesis** at layer `t`: the jump radius `δ_t = 1 − t/n`
attains the LYM ceiling, `ε_mca(C, δ_t) ≥ C(n,t)/q`. The only conditional input. -/
def ExtremalWitnessLayer (C : Set (ι → A)) (t : ℕ) : Prop :=
  ((Fintype.card ι).choose t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
    ≤ epsMCA (F := F) (A := A) C (1 - (t : ℝ≥0) / (Fintype.card ι : ℝ≥0))

/-! ## The two brackets -/

variable (C : Submodule F (ι → A))

/-- `(t : ℝ≥0) < (1−δ)·n` from `δ < 1 − t/n` (with `t < n`). -/
private theorem floor_lt_of_lt {t : ℕ} (htn : t < Fintype.card ι)
    {δ : ℝ≥0} (hδ : δ < 1 - (t : ℝ≥0) / (Fintype.card ι : ℝ≥0)) :
    (t : ℝ≥0) < ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) := by
  set n := Fintype.card ι with hn
  have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast (Fintype.card_pos (α := ι))
  have htn1 : (t : ℝ≥0) / n ≤ 1 := by
    rw [div_le_one hn0]; exact_mod_cast le_of_lt htn
  have hsub : (t : ℝ≥0) / n < 1 - δ := by
    rw [lt_tsub_iff_left]
    rw [lt_tsub_iff_right] at hδ
    exact hδ
  have := mul_lt_mul_of_pos_right hsub hn0
  rwa [div_mul_cancel₀ _ hn0.ne'] at this

theorem epsMCA_good_below_family {t : ℕ}
    (hhalf : Fintype.card ι ≤ 2 * t) (htn : t < Fintype.card ι)
    {δ : ℝ≥0} (hδ : δ < 1 - (t : ℝ≥0) / (Fintype.card ι : ℝ≥0)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((Fintype.card ι).choose (t + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  set n := Fintype.card ι with hn
  have hxR : (t : ℝ≥0) < ((1 : ℝ≥0) - δ) * (n : ℝ≥0) := floor_lt_of_lt htn hδ
  have hceil : t + 1 ≤ ⌈((1 : ℝ≥0) - δ) * (n : ℝ≥0)⌉₊ :=
    Nat.lt_ceil.mpr (by exact_mod_cast hxR)
  have hceil_le : ⌈((1 : ℝ≥0) - δ) * (n : ℝ≥0)⌉₊ ≤ n := by
    refine Nat.ceil_le.mpr ?_
    calc ((1 : ℝ≥0) - δ) * (n : ℝ≥0) ≤ 1 * (n : ℝ≥0) :=
          mul_le_mul_of_nonneg_right tsub_le_self (zero_le _)
      _ = (n : ℝ≥0) := one_mul _
  have hhalf' : n ≤ 2 * ⌈((1 : ℝ≥0) - δ) * (n : ℝ≥0)⌉₊ := by omega
  have hbound := ProximityGap.MCAAntichainLYM.epsMCA_le_choose_ceil_div
    (F := F) (A := A) C δ hhalf'
  refine hbound.trans ?_
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast choose_le_choose_upper n (by omega) hceil hceil_le

/-- **Bad at and above the jump.** Under `ExtremalWitnessLayer C t`, `ε_mca(C, δ) > C(n,t+1)/q`
for every `δ ≥ 1 − t/n`. The ceiling (witness floor `= t`) gives `ε_mca(C, δ_t) ≤ C(n,t)/q`, the
hypothesis gives `≥`, so `= C(n,t)/q`; and `C(n,t) > C(n,t+1)` in the upper half. Monotonicity
lifts it to all `δ ≥ δ_t`. -/
theorem epsMCA_bad_above_family {t : ℕ}
    (hhalf : Fintype.card ι ≤ 2 * t) (htn : t < Fintype.card ι)
    (hext : ExtremalWitnessLayer (F := F) (A := A) (C : Set (ι → A)) t)
    {δ : ℝ≥0} (hδ : 1 - (t : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ δ) :
    ((Fintype.card ι).choose (t + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      < epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  set n := Fintype.card ι with hn
  have hmono := epsMCA_mono (F := F) (A := A) (C : Set (ι → A)) hδ
  refine lt_of_lt_of_le ?_ (le_trans hext hmono)
  -- `C(n,t+1)/q < C(n,t)/q` since `C(n,t+1) < C(n,t)` in the upper half (`t ≥ n/2`)
  refine ENNReal.div_lt_div_right ?_ ?_ ?_
  · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _
  · -- `C(n,t+1) < C(n,t)`
    have hsucc : n.choose (t + 1) < n.choose t := by
      have hrec := Nat.choose_succ_right_eq n t
      have hpos : 0 < n.choose t := Nat.choose_pos (le_of_lt htn)
      have hnt : n - t < t + 1 := by omega
      have key : n.choose (t + 1) * (t + 1) < n.choose t * (t + 1) := by
        rw [hrec]; exact Nat.mul_lt_mul_of_pos_left hnt hpos
      exact Nat.lt_of_mul_lt_mul_right key
    exact_mod_cast hsucc

/-- **THE FAMILY INTERIOR PIN.** In the upper-half regime `n ≤ 2t`, with the extremal layer
hypothesis, `δ*(C, C(n,t+1)/q) = 1 − t/n` — pinned exactly at the granularity jump. Parametric
in the code and the layer `t`; the good side is unconditional. -/
theorem mcaDeltaStar_family_interior_pin {t : ℕ}
    (hhalf : Fintype.card ι ≤ 2 * t) (htn : t < Fintype.card ι)
    (hext : ExtremalWitnessLayer (F := F) (A := A) (C : Set (ι → A)) t) :
    mcaDeltaStar (F := F) (A := A) (C : Set (ι → A))
        (((Fintype.card ι).choose (t + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
      = 1 - (t : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  refine mcaDeltaStar_eq_of_good_below_of_bad_above
    (C : Set (ι → A)) _ tsub_le_self
    (fun δ hδ => epsMCA_good_below_family C hhalf htn hδ)
    (fun δ hδ => epsMCA_bad_above_family C hhalf htn hext hδ)

/-! ## The unconditional family lower bracket (the LYM reach) -/

/-- **The unconditional family `δ*` lower bracket.** In the upper-half regime `n ≤ 2t`, *whenever*
the threshold `ε*` absorbs the layer-`t` LYM ceiling (`C(n,t)/q ≤ ε*`), the threshold reaches at
least the jump radius: `1 − t/n ≤ δ*(C, ε*)`. **No extremal hypothesis** — this is the precise,
parametric reach of the LYM/antichain method, the floor any prize construction must beat. (At low
rate it is honest but loose, because `C(n,⌊n/2⌋)/q` is exponentially larger than the true count —
the localized open core.) -/
theorem le_mcaDeltaStar_lym_family {t : ℕ}
    (hhalf : Fintype.card ι ≤ 2 * t) (htn : t ≤ Fintype.card ι)
    {εstar : ℝ≥0∞}
    (hε : ((Fintype.card ι).choose t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    1 - (t : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar := by
  set n := Fintype.card ι with hn
  have hn0 : 0 < n := Fintype.card_pos
  have htn1 : (t : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn0)]; exact_mod_cast htn
  -- at radius `δ = 1 − t/n` the witness floor is exactly `t`, so the LYM ceiling is `C(n,t)/q ≤ ε*`
  have hdiff : (1 : ℝ≥0) - ((1 : ℝ≥0) - (t : ℝ≥0) / (n : ℝ≥0)) = (t : ℝ≥0) / (n : ℝ≥0) :=
    tsub_tsub_cancel_of_le htn1
  have hceil_eq : ⌈((1 : ℝ≥0) - ((1 : ℝ≥0) - (t : ℝ≥0) / (n : ℝ≥0))) * (n : ℝ≥0)⌉₊ = t := by
    rw [hdiff, div_mul_cancel₀ _ (by exact_mod_cast hn0.ne' : ((n : ℝ≥0)) ≠ 0), Nat.ceil_natCast]
  have hhalf' : n ≤ 2 * ⌈((1 : ℝ≥0) - ((1 : ℝ≥0) - (t : ℝ≥0) / (n : ℝ≥0))) * (n : ℝ≥0)⌉₊ := by
    rw [hceil_eq]; omega
  have hbound := ProximityGap.MCAAntichainLYM.epsMCA_le_choose_ceil_div
    (F := F) (A := A) C (1 - (t : ℝ≥0) / (n : ℝ≥0)) hhalf'
  rw [hceil_eq] at hbound
  exact le_mcaDeltaStar_of_good (F := F) (A := A) (C : Set (ι → A)) εstar tsub_le_self
    (le_trans hbound hε)

end ProximityGap.MCAWindowInteriorFamily

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.MCAWindowInteriorFamily.choose_le_choose_upper
#print axioms ProximityGap.MCAWindowInteriorFamily.epsMCA_good_below_family
#print axioms ProximityGap.MCAWindowInteriorFamily.mcaDeltaStar_family_interior_pin
#print axioms ProximityGap.MCAWindowInteriorFamily.le_mcaDeltaStar_lym_family
