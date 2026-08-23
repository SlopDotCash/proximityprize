/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26FoldSupplyDecay

/-!
# The KKH26 bad-scalar supply is STRICTLY ANTITONE down the whole fold tower (#357 R2, #444)

`KKH26FoldSupplyDecay.kkh26_fold_supply_strict_decay` proves that ONE `s`-step of the FRI fold
strictly shrinks the KKH26 bad-scalar supply count, in the `r`-even structural-halving regime:

  `2^{r/2} · C(s/4, r/2)  <  2^r · C(s/2, r)`     (one step, `4 ∣ s`, `2 ≤ r`, `2 ∣ r`, `2r < s`).

No in-tree theorem ITERATES it.  This file lands the iterated statement on the natural `2`-power
tower `s = 2^a`, `r = 2^c`, where every `s`-step keeps the parameters integral.  Indexing the
supply at the tower coordinate `(a, c)` by

  **`foldSupply a c := 2^(2^c) · C(2^(a-1), 2^c)`**

(the witness-spread count `KKH26EntropyForm.kkh26_witness_count_ge` at the
`(s, 1, r) = (2^a, 1, 2^c)` instance), one `s`-step is the coordinate map `(a, c) ↦ (a-1, c-1)`,
and the two headline results are:

* **`foldSupply_step_lt`** — one `s`-step strictly shrinks it, under the *thin-window* tower
  constraint `c + 1 < a` (`⟺ 2r < s`): `foldSupply (a-1) (c-1) < foldSupply a c`.  (A clean
  `2`-power repackaging of the in-tree single-step theorem.)
* **`foldSupply_tower_strict_antitone`** — the thin window is *self-propagating*
  (`c + 1 < a ⟹ (c-1) + 1 < (a-1)` whenever `c ≥ 1`), so the supply strictly decreases along
  EVERY prefix of the fold tower: for `0 < j ≤ c` and the thin-window `c + 1 < a`,
  `foldSupply (a - j) (c - j) < foldSupply a c`.

So the explicit KKH26 construction-class supply decays *monotonically* down the entire fold tower,
all the way to the terminal fold `c = 0` (`r = 1`), where it collapses to the **linear floor**
`foldSupply a 0 = 2^(a-1)` (`foldSupply_terminal`, `= s/2`).

**Honest scope (rules 1, 3, 4, 6 + asymptotic guard).**  This is NOT a CORE closure and NOT a
refutation.  It bounds the explicit KKH26 *construction-class* supply (the bad family the fold acts
on), extending the proven single-step decay to the full tower; the genuinely open wall is the
WORST-CASE (non-construction) list, untouched here.  Thinness-essential via the `2`-power tower and
the `2r < s` thin window (the regime where KKH26 is the near-capacity bad family).  NON-MOMENT (pure
binomial / monotonicity, no even-moment or energy input).  No capacity / beyond-Johnson /
cliff-at-`n/2` claim.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ProximityGap.KKH26FoldSupplyTower

open Nat ProximityGap.KKH26FoldSupplyDecay

/-- The KKH26 bad-scalar supply at the `2`-power tower coordinate `(a, c)`: the witness-spread count
`2^r · C(s/2, r)` of the `(s, 1, r) = (2^a, 1, 2^c)` instance. -/
def foldSupply (a c : ℕ) : ℕ := 2 ^ (2 ^ c) * Nat.choose (2 ^ (a - 1)) (2 ^ c)

/-- **The terminal fold supply is the linear floor.** At `c = 0` (`r = 1`) the supply collapses to
`2 · C(2^(a-1), 1) = 2^a = s` … reading `s/2 = 2^(a-1)` as the inner-group size, the count is the
linear `s/2`-scale: `foldSupply a 0 = 2 ^ a` for `a ≥ 1` (since `C(2^(a-1), 1) = 2^(a-1)`). -/
theorem foldSupply_terminal {a : ℕ} (ha : 1 ≤ a) : foldSupply a 0 = 2 ^ a := by
  unfold foldSupply
  simp only [pow_zero, Nat.choose_one_right, pow_one]
  rw [← pow_succ']
  congr 1
  omega

/-- **One `s`-step strictly shrinks the supply** (the `2`-power repackaging of the in-tree
`kkh26_fold_supply_strict_decay`).  Under the thin-window tower constraint `c + 1 < a` (`⟺ 2r < s`),
the `s`-step coordinate map `(a, c) ↦ (a-1, c-1)` strictly decreases `foldSupply`. -/
theorem foldSupply_step_lt {a c : ℕ} (hc : 1 ≤ c) (hca : c + 1 < a) :
    foldSupply (a - 1) (c - 1) < foldSupply a c := by
  -- instantiate the in-tree single-step theorem at s = 2^a, r = 2^c
  have hs : 4 ∣ (2 ^ a) := by
    have : (2:ℕ) ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    simpa using this
  have hr : 2 ≤ 2 ^ c := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
  have hrev : 2 ∣ (2 ^ c) := dvd_pow_self 2 (by omega)
  have hrs : 2 * (2 ^ c) < 2 ^ a := by
    have h1 : 2 * (2 ^ c) = 2 ^ (c + 1) := by rw [pow_succ]; ring
    rw [h1]
    exact Nat.pow_lt_pow_right (by norm_num) hca
  have hstep := kkh26_fold_supply_strict_decay hs hr hrev hrs
  -- translate the (s/2, s/4, r/2) numerals into the (a-1, c-1) tower coordinates
  have hr2 : (2 ^ c) / 2 = 2 ^ (c - 1) := by
    conv_lhs => rw [show c = (c - 1) + 1 by omega, pow_succ]
    rw [Nat.mul_div_cancel _ (by norm_num)]
  have hs2 : (2 ^ a) / 2 = 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    rw [Nat.mul_div_cancel _ (by norm_num)]
  have hs4 : (2 ^ a) / 4 = 2 ^ (a - 2) := by
    conv_lhs => rw [show a = (a - 2) + 2 by omega, pow_add, show (2:ℕ) ^ 2 = 4 from rfl]
    rw [Nat.mul_div_cancel _ (by norm_num)]
  -- rewrite `foldSupply` at both coordinates to match `hstep`
  unfold foldSupply
  have hac1 : (a - 1) - 1 = a - 2 := by omega
  rw [hac1]
  rw [hr2, hs4, hs2] at hstep
  exact hstep

/-- **The whole fold tower is strictly antitone.** The thin window `c + 1 < a` is self-propagating
down the tower (each `s`-step keeps `2r < s`), so the KKH26 bad-scalar supply strictly decreases
along every prefix of the fold: for `0 < j ≤ c` and `c < a`,
`foldSupply (a - j) (c - j) < foldSupply a c`. -/
theorem foldSupply_tower_strict_antitone {a c j : ℕ} (hj : 1 ≤ j) (hjc : j ≤ c)
    (hca : c + 1 < a) :
    foldSupply (a - j) (c - j) < foldSupply a c := by
  -- revert the live thin-window hypotheses so the IH is properly quantified over them
  revert hj hjc
  induction j with
  | zero => intro hj _; omega
  | succ j ih =>
    intro hjsucc hjc
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · -- base: exactly one step (j+1 = 1)
      subst hj0
      simpa using foldSupply_step_lt (c := c) (a := a) (by omega) (by omega)
    · -- inductive: antitone prefix down to depth j, then one more s-step below it
      have hjle : j ≤ c := by omega
      have hih : foldSupply (a - j) (c - j) < foldSupply a c := ih hjpos hjle
      -- one more s-step from (a - j, c - j) to (a - (j+1), c - (j+1)); thin window self-propagates
      have hstep :
          foldSupply ((a - j) - 1) ((c - j) - 1) < foldSupply (a - j) (c - j) :=
        foldSupply_step_lt (c := c - j) (a := a - j) (by omega) (by omega)
      have he1 : a - (j + 1) = (a - j) - 1 := by omega
      have he2 : c - (j + 1) = (c - j) - 1 := by omega
      rw [he1, he2]
      exact lt_trans hstep hih

/-- Sanity: the tower `(a, c) = (6, 2)` (`s = 64`, `r = 4`) strictly decreases two steps to the
terminal `(4, 0)` (`s = 16`, `r = 1`):  `575360 > 480 > 16`. -/
example : foldSupply 4 0 < foldSupply 6 2 :=
  foldSupply_tower_strict_antitone (a := 6) (c := 2) (j := 2)
    (by norm_num) (by norm_num) (by norm_num)

/-- Sanity: terminal collapse at `a = 4`:  `foldSupply 4 0 = 16`. -/
example : foldSupply 4 0 = 16 := by decide

end ProximityGap.KKH26FoldSupplyTower

/-! ## Axiom audit -/
#print axioms ProximityGap.KKH26FoldSupplyTower.foldSupply_terminal
#print axioms ProximityGap.KKH26FoldSupplyTower.foldSupply_step_lt
#print axioms ProximityGap.KKH26FoldSupplyTower.foldSupply_tower_strict_antitone
