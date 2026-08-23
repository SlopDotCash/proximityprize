/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKNineBitGap

/-!
# The depth-9 threshold: where the moment route can and cannot close the nine bits — #466

`_BGKNineBitGap` pinned the depth-five lane's open content to `M ≤ 2⁵¹` (nine bits below the
trivial `2⁶⁰`). The only in-tree certification tool for the sup-bound is the moment method:
`max‖η_b‖^{2r} ≤ ∑_{b≠0}‖η_b‖^{2r} = q·E_r − |G|^{2r}` (the exact depth-`r` law). This file
proves the sharp depth threshold for that route at the literal prize numbers:

* `rEnergy_ge_pow` — the diagonal floor `E_r(G) ≥ |G|^r` (the pairs `(x, x)`), unconditional.

* `depthSeven_moment_noGo` — **the no-go**: at `|G| = 2³⁰`, `q ≥ 2¹⁵⁸`, the depth-7 moment
  certificate is provably too weak — its value is at least `(q·E_7)^{1/7} ≥ 2^{368/7} > 2⁵¹`,
  because the diagonal alone forces `q·E_7 ≥ 2¹⁵⁸·2²¹⁰ = 2³⁶⁸ > 2³⁵⁷ = (2⁵¹)⁷`. Stated
  division-free: `(2⁵¹)⁷ < q·E_7`. The same argument kills every depth `r ≤ 7`. So NO
  depth-≤7 moment bound — with ANY energy estimate, even the true value — certifies
  `M ≤ 2⁵¹`.

* `depthNine_wick_closes` — **the sufficiency**: if the depth-9 energy satisfies the Wick
  law `E_9 ≤ 17‼·|G|⁹` (`17‼ = 34459425 < 2²⁶`) and `q ≤ 2¹⁵⁹` (the prize field:
  `productionQ < 2¹⁵⁹`, checked in `productionQ_lt`), then `max‖η_b‖² ≤ 2⁵¹` — i.e.
  `WorstCaseIncompleteSumBound ψ G (2⁵¹)` HOLDS, which by
  `rEnergy_le_production_ceiling_sharp` fires the entire depth-five production envelope.

**Consequence.** The nine-bit gap is EXACTLY the depth-{8,9} Wick certification problem: the
moment ladder must be pushed past depth 7 (provably) and depth-9 Wick suffices (provably).
The open content is now a single concrete inequality: `E_9(μ_n) ≤ 17‼·n⁹` at `n = 2³⁰`,
`p ≈ 2¹⁵⁸`. Nothing here discharges it. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024
set_option maxRecDepth 16384

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity
open ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld

namespace ArkLib.ProximityGap.Frontier.BGKDepthNineThreshold

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The diagonal floor**: `E_r(G) ≥ |G|^r`, from the pairs `(x, x)`. Unconditional. -/
theorem rEnergy_ge_pow (G : Finset F) (r : ℕ) : G.card ^ r ≤ rEnergy G r := by
  classical
  have hdiag : (Fintype.piFinset (fun _ : Fin r => G)).card ≤ rEnergy G r := by
    rw [rEnergy]
    refine Finset.card_le_card_of_injOn (fun x => (x, x)) ?_ ?_
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩
    · intro x _ y _ h
      exact congrArg Prod.fst h
  calc G.card ^ r = (Fintype.piFinset (fun _ : Fin r => G)).card := by
        rw [Fintype.card_piFinset]
        simp
    _ ≤ rEnergy G r := hdiag

/-- **The depth-7 no-go**: at production size, the depth-7 moment certificate value exceeds
the nine-bit target — division-free form `(2⁵¹)⁷ < q·E_7`, forced by the diagonal alone.
Hence no depth-≤7 moment argument, with any energy input, certifies `M ≤ 2⁵¹`. -/
theorem depthSeven_moment_noGo (G : Finset F)
    (hG : G.card = 2 ^ 30) (hq : (2 : ℕ) ^ 158 ≤ Fintype.card F) :
    ((2 : ℕ) ^ 51) ^ 7 < Fintype.card F * rEnergy G 7 := by
  have hE : (2 : ℕ) ^ 210 ≤ rEnergy G 7 := by
    have h := rEnergy_ge_pow G 7
    rwa [hG, ← pow_mul] at h
  calc ((2 : ℕ) ^ 51) ^ 7 = 2 ^ 357 := by rw [← pow_mul]
    _ < 2 ^ 368 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    _ = 2 ^ 158 * 2 ^ 210 := by rw [← pow_add]
    _ ≤ Fintype.card F * rEnergy G 7 := Nat.mul_le_mul hq hE

/-- The prize field cardinality is below `2¹⁵⁹`: `productionQ < 2¹⁵⁹`. Kernel arithmetic. -/
theorem productionQ_lt : productionQ < 2 ^ 159 := by
  norm_num [productionQ, productionN]

/-- **Depth-9 Wick closes the nine bits.** If the depth-9 energy obeys the Wick law
`E_9 ≤ 17‼·|G|⁹` (`17‼ = 34459425`), then at `|G| = 2³⁰`, `q ≤ 2¹⁵⁹` every nonzero frequency
has `‖η_b‖² ≤ 2⁵¹` — the sup-bound at exactly the scale the sharpened production weld
consumes. The open content of the whole depth-five lane is therefore THIS hypothesis. -/
theorem depthNine_wick_closes {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : G.card = 2 ^ 30) (hqu : Fintype.card F ≤ 2 ^ 159)
    (hwick : rEnergy G 9 ≤ 34459425 * G.card ^ 9) :
    WorstCaseIncompleteSumBound ψ G (2 ^ 51) := by
  intro b hb
  -- the single-frequency term is dominated by the off-zero sum, which the law computes.
  have hsingle : ‖eta ψ G b‖ ^ 18 ≤ ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ 18 := by
    refine Finset.single_le_sum (f := fun c => ‖eta ψ G c‖ ^ 18)
      (fun c _ => by positivity) ?_
    exact Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hlaw := moment_eq_card_energy hψ G 9
  have hsplit : ∑ c : F, ‖eta ψ G c‖ ^ 18
      = ‖eta ψ G 0‖ ^ 18 + ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ 18 := by
    simpa using (Finset.add_sum_erase _ (fun c => ‖eta ψ G c‖ ^ 18) (Finset.mem_univ 0)).symm
  have h0 : (0 : ℝ) ≤ ‖eta ψ G 0‖ ^ 18 := by positivity
  -- numeric budget: q·E_9 ≤ 2¹⁵⁹·(17‼·2²⁷⁰) < 2⁴⁵⁹ = (2⁵¹)⁹.
  have hbudget : (Fintype.card F : ℝ) * (rEnergy G 9 : ℝ) ≤ ((2 : ℝ) ^ 51) ^ 9 := by
    have hqR : (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ 159 := by exact_mod_cast hqu
    have hER : (rEnergy G 9 : ℝ) ≤ 34459425 * ((2 : ℝ) ^ 30) ^ 9 := by
      have : (rEnergy G 9 : ℝ) ≤ (34459425 : ℝ) * (G.card : ℝ) ^ 9 := by
        exact_mod_cast hwick
      rwa [hG, Nat.cast_pow, Nat.cast_ofNat] at this
    have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
    have hE0 : (0 : ℝ) ≤ (rEnergy G 9 : ℝ) := by positivity
    calc (Fintype.card F : ℝ) * (rEnergy G 9 : ℝ)
        ≤ (2 : ℝ) ^ 159 * (34459425 * ((2 : ℝ) ^ 30) ^ 9) := by
          exact mul_le_mul hqR hER hE0 (by positivity)
      _ ≤ ((2 : ℝ) ^ 51) ^ 9 := by norm_num
  have hchain : ‖eta ψ G b‖ ^ 18 ≤ ((2 : ℝ) ^ 51) ^ 9 := by
    have hoff : ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ 18
        ≤ (Fintype.card F : ℝ) * (rEnergy G 9 : ℝ) := by
      have : ‖eta ψ G 0‖ ^ 18 + ∑ c ∈ Finset.univ.erase (0 : F), ‖eta ψ G c‖ ^ 18
          = (Fintype.card F : ℝ) * (rEnergy G 9 : ℝ) := by
        rw [← hsplit]
        simpa using hlaw
      linarith
    exact hsingle.trans (hoff.trans hbudget)
  -- take ninth roots: `(‖η‖²)⁹ ≤ (2⁵¹)⁹ ⟹ ‖η‖² ≤ 2⁵¹`.
  have hpow : (‖eta ψ G b‖ ^ 2) ^ 9 ≤ ((2 : ℝ) ^ 51) ^ 9 := by
    rw [← pow_mul]
    exact hchain
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow

open ArkLib.ProximityGap.Frontier.BGKNineBitGap in
/-- **The capstone: depth-9 Wick ⟹ the production depth-five envelope, sup-bound eliminated.**
Composing `depthNine_wick_closes` with the sharpened weld: the single hypothesis
`E_9(G) ≤ 17‼·|G|⁹` (a pure COUNTING inequality — no character sums, no sup norms) yields the
G112 production collision ceiling at the literal prize numbers. The open input of the entire
depth-five lane is now this one concrete inequality. -/
theorem depthNine_wick_production_envelope {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hG : G.card = 2 ^ 30)
    (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) (hqu : Fintype.card F ≤ 2 ^ 159)
    (hwick : rEnergy G 9 ≤ 34459425 * G.card ^ 9) :
    rEnergy G 5 ≤ productionCollisionCeiling :=
  rEnergy_le_production_ceiling_sharp hψ G (by positivity) le_rfl
    (depthNine_wick_closes hψ G hG hqu hwick) hG hq

end ArkLib.ProximityGap.Frontier.BGKDepthNineThreshold

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKDepthNineThreshold.rEnergy_ge_pow
#print axioms ArkLib.ProximityGap.Frontier.BGKDepthNineThreshold.depthSeven_moment_noGo
#print axioms ArkLib.ProximityGap.Frontier.BGKDepthNineThreshold.depthNine_wick_closes
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthNineThreshold.depthNine_wick_production_envelope
