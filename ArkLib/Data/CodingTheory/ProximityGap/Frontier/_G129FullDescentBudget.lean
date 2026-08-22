/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G128ProductionDescentBudget

/-!
# G129 (part 1): the conditional full-descent budget at production rung 110

G128 showed depths `0..102` of the descent overhead are free.  This file splits one rung
lower and adds the eight deepest sub-full depths: given DC-shape bounds
`q·E_s ≤ q·Wick_s + n^{2s}` at rungs `s = 102..109` ONLY, the FULL production descent
overhead fits inside a quarter of the DC mass (with ~2^14 headroom):

```text
4 · q · Σ_{s=0}^{109} (110)_{110−s}²·n^{110−s}·E_s ≤ n^{220}.
```

The quarter leaves three quarters of the DC mass for the disjoint census in the G126 gate —
the tower step: `DCEnergyBound` at rung `110` follows from the rung-110 disjoint census plus
DC at the eight predecessor rungs (part 2, the induction, consumes this).

**Honest scope.**  Conditional on the eight predecessor DC bounds; no claim they hold.  CORE
remains OPEN.  Issue #466 (G129 claim).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G129FullDescentBudget

open Finset
open ArkLib.ProximityGap.Frontier.G128ProductionDescentBudget

/-- Sharp form of the G128 shallow bound: the depths-`0..102` overhead is at most the
explicit two-term head. -/
theorem shallow_descent_sharp (q : ℕ) (hq : q ≤ 2 ^ 160)
    (E : ℕ → ℕ) (hE0 : E 0 ≤ 1)
    (hEs : ∀ s, 1 ≤ s → E s ≤ (2 ^ 30 : ℕ) ^ (2 * s - 1)) :
    q * ∑ s ∈ Finset.range 102,
        (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s)
      ≤ 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110
        + 2 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2 * (2 ^ 30) ^ 210) := by
  have hterm : ∀ i, i < 101 →
      q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
        ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
        ≤ descB q (109 - i) := by
    intro i hi
    have hidx : 110 - (i + 1) = 109 - i := by omega
    have hE := hEs (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
    have hpow : (2 ^ 30 : ℕ) ^ (109 - i) * (2 ^ 30) ^ (2 * (i + 1) - 1)
        = (2 ^ 30) ^ (219 - (109 - i)) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
          ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
          ≤ q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (110 - (i + 1)) * (2 ^ 30) ^ (2 * (i + 1) - 1))) := by
        gcongr
      _ = q * (Nat.descFactorial 110 (109 - i)) ^ 2 * (2 ^ 30) ^ (219 - (109 - i)) := by
        rw [hidx, hpow]
        ring
      _ = descB q (109 - i) := rfl
  rw [Finset.mul_sum, Finset.sum_range_succ']
  have h0 : q * ((Nat.descFactorial 110 (110 - 0)) ^ 2 *
      ((2 ^ 30) ^ (110 - 0) * E 0))
      ≤ 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110 := by
    have hds : Nat.descFactorial 110 110 = Nat.factorial 110 :=
      Nat.descFactorial_self 110
    calc
      q * ((Nat.descFactorial 110 (110 - 0)) ^ 2 *
          ((2 ^ 30) ^ (110 - 0) * E 0))
          ≤ 2 ^ 160 * ((Nat.factorial 110) ^ 2 * ((2 ^ 30) ^ 110 * 1)) := by
        simp only [Nat.sub_zero, hds]
        gcongr
      _ = 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110 := by ring
  have htail : ∑ i ∈ Finset.range 101,
      q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
        ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
      ≤ 2 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2 * (2 ^ 30) ^ 210) := by
    calc
      ∑ i ∈ Finset.range 101,
          q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
            ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1)))
          ≤ ∑ i ∈ Finset.range 101, descB q (109 - i) :=
        Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
      _ ≤ ∑ j ∈ Finset.range 102, descB q (110 - j) := by
        rw [Finset.sum_range_succ' (fun j => descB q (110 - j)) 101]
        exact Nat.le_add_right _ _
      _ ≤ 2 * descB q (110 - 101) := descB_tail q 101 (by norm_num)
      _ ≤ 2 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2 * (2 ^ 30) ^ 210) := by
        have h9 : (110 - 101 : ℕ) = 9 := by norm_num
        rw [h9]
        unfold descB
        have h210 : (219 - 9 : ℕ) = 210 := by norm_num
        rw [h210]
        gcongr
  calc
    (∑ i ∈ Finset.range 101,
        q * ((Nat.descFactorial 110 (110 - (i + 1))) ^ 2 *
          ((2 ^ 30) ^ (110 - (i + 1)) * E (i + 1))))
      + q * ((Nat.descFactorial 110 (110 - 0)) ^ 2 *
          ((2 ^ 30) ^ (110 - 0) * E 0))
        ≤ 2 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2 * (2 ^ 30) ^ 210)
          + 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110 :=
      Nat.add_le_add htail h0
    _ = 2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110
        + 2 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2 * (2 ^ 30) ^ 210) :=
      Nat.add_comm _ _

/-- The deep (top-eight) budget: one term of the conditional overhead. -/
def deepTerm (s : ℕ) : ℕ :=
  (Nat.descFactorial 110 (110 - s)) ^ 2 *
    ((2 ^ 30) ^ (110 - s) *
      (2 ^ 160 * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s) + (2 ^ 30) ^ (2 * s)))

/-- **The four-fold kernel gate**: four copies of the sharp shallow head plus four copies of
all eight deep terms fit the DC mass. -/
theorem production_gate_four :
    4 * (2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110
        + 2 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2 * (2 ^ 30) ^ 210))
      + 4 * (deepTerm 102 + deepTerm 103 + deepTerm 104 + deepTerm 105 + deepTerm 106
        + deepTerm 107 + deepTerm 108 + deepTerm 109)
      ≤ (2 ^ 30 : ℕ) ^ 220 := by
  norm_num [deepTerm, Nat.factorial, Nat.descFactorial, Nat.doubleFactorial]

/-- **Conditional full-descent budget.**  Given DC-shape bounds at rungs `102..109` only,
the full production descent overhead fits a quarter of the DC mass. -/
theorem production_full_descent_budget (q : ℕ) (hq : q ≤ 2 ^ 160)
    (E : ℕ → ℕ) (hE0 : E 0 ≤ 1)
    (hEs : ∀ s, 1 ≤ s → E s ≤ (2 ^ 30 : ℕ) ^ (2 * s - 1))
    (hDC : ∀ s, 102 ≤ s → s < 110 →
      q * E s ≤ q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
        + (2 ^ 30) ^ (2 * s)) :
    4 * (q * ∑ s ∈ Finset.range 110,
        (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s))
      ≤ (2 ^ 30 : ℕ) ^ 220 := by
  have hdeep : ∀ s, 102 ≤ s → s < 110 →
      q * ((Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s))
        ≤ deepTerm s := by
    intro s hs1 hs2
    have hE := hDC s hs1 hs2
    unfold deepTerm
    calc
      q * ((Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s))
          = (Nat.descFactorial 110 (110 - s)) ^ 2 *
              ((2 ^ 30) ^ (110 - s) * (q * E s)) := by ring
      _ ≤ (Nat.descFactorial 110 (110 - s)) ^ 2 *
            ((2 ^ 30) ^ (110 - s) *
              (q * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
                + (2 ^ 30) ^ (2 * s))) := by
        gcongr
      _ ≤ (Nat.descFactorial 110 (110 - s)) ^ 2 *
            ((2 ^ 30) ^ (110 - s) *
              (2 ^ 160 * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
                + (2 ^ 30) ^ (2 * s))) := by
        gcongr
  have hsplit : ∑ s ∈ Finset.range 110,
      (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s)
      = (∑ s ∈ Finset.range 102,
          (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s))
        + ∑ s ∈ Finset.Ico 102 110,
            (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le 102) (by norm_num)).symm
  have hdeepsum : q * ∑ s ∈ Finset.Ico 102 110,
      (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s)
      ≤ deepTerm 102 + deepTerm 103 + deepTerm 104 + deepTerm 105 + deepTerm 106
        + deepTerm 107 + deepTerm 108 + deepTerm 109 := by
    rw [Finset.mul_sum]
    have hexp : Finset.Ico 102 110 =
        ({102, 103, 104, 105, 106, 107, 108, 109} : Finset ℕ) := by decide
    rw [hexp]
    have h102 := hdeep 102 (by norm_num) (by norm_num)
    have h103 := hdeep 103 (by norm_num) (by norm_num)
    have h104 := hdeep 104 (by norm_num) (by norm_num)
    have h105 := hdeep 105 (by norm_num) (by norm_num)
    have h106 := hdeep 106 (by norm_num) (by norm_num)
    have h107 := hdeep 107 (by norm_num) (by norm_num)
    have h108 := hdeep 108 (by norm_num) (by norm_num)
    have h109 := hdeep 109 (by norm_num) (by norm_num)
    rw [show ({102, 103, 104, 105, 106, 107, 108, 109} : Finset ℕ)
        = insert 102 (insert 103 (insert 104 (insert 105 (insert 106
            (insert 107 (insert 108 ({109} : Finset ℕ))))))) from rfl]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    omega
  have hshallow := shallow_descent_sharp q hq E hE0 hEs
  calc
    4 * (q * ∑ s ∈ Finset.range 110,
        (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s))
        = 4 * (q * ∑ s ∈ Finset.range 102,
            (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s))
          + 4 * (q * ∑ s ∈ Finset.Ico 102 110,
            (Nat.descFactorial 110 (110 - s)) ^ 2 * ((2 ^ 30) ^ (110 - s) * E s)) := by
      rw [hsplit]
      ring
    _ ≤ 4 * (2 ^ 160 * (Nat.factorial 110) ^ 2 * (2 ^ 30) ^ 110
          + 2 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2 * (2 ^ 30) ^ 210))
        + 4 * (deepTerm 102 + deepTerm 103 + deepTerm 104 + deepTerm 105 + deepTerm 106
          + deepTerm 107 + deepTerm 108 + deepTerm 109) := by
      gcongr
    _ ≤ (2 ^ 30 : ℕ) ^ 220 := production_gate_four

/-! ## Part 2a: the explicit rung-110 tower step -/

section TowerStep

open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G126DisjointCensusGate
open ArkLib.ProximityGap.DCEnergyCorrection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The rung-110 tower step.**  At production shape, `DCEnergyBound` at rung `110` follows
from (i) DC-shape bounds at the eight predecessor rungs `102..109` and (ii) the rung-110
fully-disjoint census fitting the Wick budget plus three quarters of the DC mass. -/
theorem dcEnergyBound_110_of_census_and_predecessors
    (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hq : Fintype.card F ≤ 2 ^ 160)
    (hDC : ∀ s, 102 ≤ s → s < 110 →
      Fintype.card F * Finset.addREnergy s G
        ≤ Fintype.card F * (Nat.doubleFactorial (2 * s - 1) * (2 ^ 30) ^ s)
          + (2 ^ 30) ^ (2 * s))
    (hcensus : 4 * (Fintype.card F * depthFiber G 110 110)
        ≤ 4 * (Fintype.card F *
            (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110))
          + 3 * (2 ^ 30) ^ 220) :
    DCEnergyBound G 110 := by
  have hE0 : Finset.addREnergy 0 G ≤ 1 := by
    rw [Finset.addREnergy_def]
    simp
  have hEs : ∀ s, 1 ≤ s → Finset.addREnergy s G ≤ (2 ^ 30 : ℕ) ^ (2 * s - 1) := by
    intro s hs
    have := Finset.addREnergy_le hs G
    rwa [hcard] at this
  have hbudget := production_full_descent_budget (Fintype.card F) hq
    (fun s => Finset.addREnergy s G) hE0 hEs hDC
  have hover : descentOverhead G 110
      = ∑ s ∈ Finset.range 110,
          (Nat.descFactorial 110 (110 - s)) ^ 2 *
            ((2 ^ 30) ^ (110 - s) * Finset.addREnergy s G) := by
    unfold descentOverhead
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hcard]
  have hfour : 4 * (Fintype.card F *
      (depthFiber G 110 110 + descentOverhead G 110))
      ≤ 4 * (Fintype.card F *
          (Nat.doubleFactorial (2 * 110 - 1) * G.card ^ 110)
        + G.card ^ (2 * 110)) := by
    have hcard220 : G.card ^ (2 * 110) = (2 ^ 30 : ℕ) ^ 220 := by
      rw [hcard]
    have hcard110 : G.card ^ 110 = (2 ^ 30 : ℕ) ^ 110 := by rw [hcard]
    calc
      4 * (Fintype.card F * (depthFiber G 110 110 + descentOverhead G 110))
          = 4 * (Fintype.card F * depthFiber G 110 110)
            + 4 * (Fintype.card F * descentOverhead G 110) := by ring
      _ ≤ (4 * (Fintype.card F *
              (Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110))
            + 3 * (2 ^ 30) ^ 220) + (2 ^ 30) ^ 220 := by
        refine Nat.add_le_add hcensus ?_
        rw [hover]
        exact hbudget
      _ = 4 * (Fintype.card F *
            (Nat.doubleFactorial (2 * 110 - 1) * G.card ^ 110)
          + G.card ^ (2 * 110)) := by
        rw [hcard220, hcard110]
        ring
  have hgate : Fintype.card F * (depthFiber G 110 110 + descentOverhead G 110)
      ≤ Fintype.card F * (Nat.doubleFactorial (2 * 110 - 1) * G.card ^ 110)
        + G.card ^ (2 * 110) :=
    Nat.le_of_mul_le_mul_left hfour (by norm_num)
  exact dcEnergyBound_of_disjoint_census G 110 hgate

end TowerStep

end ArkLib.ProximityGap.Frontier.G129FullDescentBudget

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G129FullDescentBudget.shallow_descent_sharp
#print axioms ArkLib.ProximityGap.Frontier.G129FullDescentBudget.production_gate_four
#print axioms
  ArkLib.ProximityGap.Frontier.G129FullDescentBudget.production_full_descent_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G129FullDescentBudget.dcEnergyBound_110_of_census_and_predecessors
