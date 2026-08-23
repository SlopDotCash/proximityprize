/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungThresholdRouter
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# The level-1 rung instance (#371): F₁₂₂₈₉, n = 16, the 5/8 band

Wires the census/threshold routers to the concrete level-1 rung
(`p = 12289`, domain `μ₁₆ = ⟨4134⟩`, degree bound 2):

* `pow_emb` — the domain embedding `i ↦ g^i` for `g` of order `n`;
* `evalCode_eq_domCode` — the KKH26 evaluation code IS the domain code;
* `orderOf_4134'` — `4134` has order 16 in `ZMod 12289` (kernel decide:
  `4134⁸ = −1`);
* **`rung_interior_of_identityCensusBound`** — the interior obligation of
  the level-1 rung pin reduces to the single identity-level Prop
  `IdentityCensusBound dom4134 2 7 31`: every stack carries at most 31
  scalars with a size-≥7 non-joint defect-identity witness.

Probe state: census record 22 (`probe_wb371_blockladder2.py`), so the Prop
is plausibly true with margin 9; the pencil (16) and 2-block (20) families
saturate the proven per-class caps.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

section PowEmb

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Injectivity of `i ↦ g^i` below the order (field version, no
cancellation-monoid detour at `0`). -/
theorem pow_inj_below_orderOf {g : F} (h0 : g ≠ 0) {N : ℕ}
    (hN : orderOf g = N) {i j : ℕ} (hi : i < N) (hj : j < N)
    (heq : g ^ i = g ^ j) : i = j := by
  have main : ∀ a b : ℕ, a ≤ b → b < N → g ^ a = g ^ b → a = b := by
    intro a b hab hb he
    have hadd : a + (b - a) = b := by omega
    have h2 : g ^ a * g ^ (b - a) = g ^ a * 1 := by
      rw [mul_one, ← pow_add, hadd, he]
    have h3 : g ^ (b - a) = 1 := mul_left_cancel₀ (pow_ne_zero a h0) h2
    have h4 : N ∣ b - a := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : b - a = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le b a) hb)
    omega
  rcases le_total i j with hij | hji
  · exact main i j hij hj heq
  · exact (main j i hji hi heq.symm).symm

/-- The smooth-domain embedding `i ↦ g^i` for `g` of order `n`. -/
def pow_emb {n : ℕ} (g : F) (h0 : g ≠ 0) (hord : orderOf g = n) :
    Fin n ↪ F :=
  ⟨fun i => g ^ (i : ℕ), fun i j h =>
    Fin.ext (pow_inj_below_orderOf h0 hord i.isLt j.isLt h)⟩

/-- The KKH26 evaluation code is the domain code of the power embedding. -/
theorem evalCode_eq_domCode {p : ℕ} [Fact p.Prime] {n : ℕ} [NeZero n]
    {g : ZMod p} (h0 : g ≠ 0) (hord : orderOf g = n) (d : ℕ) :
    ArkLib.ProximityGap.KKH26.evalCode g n d
      = domCode (pow_emb g h0 hord) d := rfl

end PowEmb

section InstanceF12289

instance primeFact_RungInstanceF12289_1 : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- `4134⁸ = −1` in `ZMod 12289` (fast route: the congruence is checked on
`ℕ` where the kernel computes with binary arithmetic). -/
theorem pow_4134_eight : (4134 : ZMod 12289) ^ 8 = -1 := by
  have h : ((4134 ^ 8 : ℕ) : ZMod 12289) = ((12288 : ℕ) : ZMod 12289) := by
    rw [ZMod.natCast_eq_natCast_iff]
    decide
  have h2 : ((12288 : ℕ) : ZMod 12289) = -1 := by
    have h3 : ((12288 : ℕ) : ZMod 12289) + 1 = 0 := by
      have h4 : ((12288 + 1 : ℕ) : ZMod 12289) = 0 := by
        exact_mod_cast ZMod.natCast_self 12289
      push_cast at h4
      exact_mod_cast h4
    linear_combination h3
  calc (4134 : ZMod 12289) ^ 8
      = ((4134 : ℕ) : ZMod 12289) ^ 8 := by norm_cast
    _ = ((4134 ^ 8 : ℕ) : ZMod 12289) := by rw [Nat.cast_pow]
    _ = ((12288 : ℕ) : ZMod 12289) := h
    _ = -1 := h2

/-- `4134` has order 16 in `ZMod 12289`. -/
theorem orderOf_4134' : orderOf (4134 : ZMod 12289) = 16 := by
  haveI : Fact (2 < 12289) := ⟨by norm_num⟩
  have h16 : (4134 : ZMod 12289) ^ 16 = 1 := by
    rw [show (16 : ℕ) = 8 * 2 from rfl, pow_mul, pow_4134_eight, neg_one_sq]
  have hne : (4134 : ZMod 12289) ^ 8 ≠ 1 := by
    rw [pow_4134_eight]
    exact ZMod.neg_one_ne_one
  -- orderOf divides 2⁴ and does not divide 2³ ⟹ = 16
  have hdvd : orderOf (4134 : ZMod 12289) ∣ 2 ^ 4 :=
    orderOf_dvd_of_pow_eq_one (by rw [show (2 : ℕ) ^ 4 = 16 from rfl]; exact h16)
  have hnd : ¬ orderOf (4134 : ZMod 12289) ∣ 2 ^ 3 := by
    intro hd
    exact hne (by
      have h8' := orderOf_dvd_iff_pow_eq_one.mp hd
      rwa [show (2 : ℕ) ^ 3 = 8 from rfl] at h8')
  obtain ⟨i, hi, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · exact absurd (hd ▸ pow_dvd_pow 2 (by omega : i ≤ 3)) hnd
  · have hi4 : i = 4 := by omega
    rw [hd, hi4]
    norm_num

end InstanceF12289

end ProximityGap.WBPencil

namespace ProximityGap.WBPencil

open scoped NNReal ENNReal

section Reduction

/-- The level-1 rung domain: `i ↦ 4134^i` in `ZMod 12289`. -/
noncomputable def dom4134 : Fin 16 ↪ ZMod 12289 :=
  pow_emb (4134 : ZMod 12289) (by decide) orderOf_4134'

/-- **The interior obligation reduces to the identity census.**  The
good-side hypothesis of the swarm's `deltaStar_level1_pin_F12289_of_interior`
(at `ε* = 31/12289`, the top of the post-refutation deployment window
`[22/p, 32/p)`) follows from the single identity-level Prop
`IdentityCensusBound dom4134 2 7 31`. -/
theorem rung_interior_of_identityCensusBound
    (h : IdentityCensusBound dom4134 2 7 31) :
    ∀ δ : ℝ≥0, δ < 5 / 8 →
      epsMCA (F := ZMod 12289) (A := ZMod 12289)
        (ArkLib.ProximityGap.KKH26.evalCode (4134 : ZMod 12289) 16 2) δ
        ≤ (31 : ℝ≥0∞) / (12289 : ℝ≥0∞) := by
  intro δ hδ
  rw [show ArkLib.ProximityGap.KKH26.evalCode (4134 : ZMod 12289) 16 2
      = domCode dom4134 2 from rfl]
  have hcard : ((12289 : ℕ) : ℝ≥0∞) = (Fintype.card (ZMod 12289) : ℝ≥0∞) := by
    rw [ZMod.card]
  have hgoal := epsMCA_le_of_identityCensusBound_of_lt (F := ZMod 12289)
    dom4134 (δ := δ) (B := 31) ?_ h
  · refine le_trans hgoal ?_
    rw [ZMod.card]
    norm_num
  · rw [Fintype.card_fin]
    have h38 : (3 / 8 : ℝ≥0) < 1 - δ := by
      rw [lt_tsub_iff_right]
      calc (3 / 8 : ℝ≥0) + δ < 3 / 8 + 5 / 8 :=
            add_lt_add_of_le_of_lt le_rfl hδ
        _ = 1 := by norm_num
    calc ((7 - 1 : ℕ) : ℝ≥0) = (3 / 8 : ℝ≥0) * 16 := by norm_num
      _ < (1 - δ) * 16 := mul_lt_mul_of_pos_right h38 (by norm_num)

end Reduction

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.pow_inj_below_orderOf
#print axioms ProximityGap.WBPencil.orderOf_4134'
#print axioms ProximityGap.WBPencil.rung_interior_of_identityCensusBound
