/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMomentLadder
import Mathlib.Tactic

/-!
# Exact `r`-fold additive energy of the two-element subgroup `μ_2 = {1,−1}` (#389)

The smallest negation-closed subgroup `μ_2 = {1,−1}` (char `≠ 2`) has its full additive-energy
spectrum in closed form. A tuple `x : Fin r → {1,−1}` is determined for the sum `∑ x` by its count
of `−1` entries, and in the no-wraparound regime (`char F = 0` or `char F > 2r`) the map
`a ↦ r − 2a` is injective, so `∑ x = ∑ z ↔ (#neg x = #neg z)`. The energy then counts pairs with
equal neg-count, `∑_a C(r,a)²`, which is `C(2r,r)` by Vandermonde:

> `twoElementEnergy_centralBinom` :  `E_r({1,−1}) = (2r).choose r`  (`= 1,2,6,20,70,…`),

and hence the exact Gauss-sum moment spectrum

> `twoElement_moment_spectrum` :  `∑_b ‖η_b‖^{2r} = q · C(2r,r)`.

This is the `n=2` base case of the negation-closed walk bound: `C(2r,r) ≤ (2r−1)!!·2^r` with equality
in leading order (`C(2r,r) ~ 4^r/√(πr)`, `(2r−1)!!·2^r = (2r)!/r!`). It is an exact, irrefutable
identity; the smallest case of the energy/AVERAGE side, NOT a δ\*/W4 advance. Axiom-clean.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.TwoElementEnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The count of `-1` entries in a tuple. -/
def cntNeg (r : ℕ) (x : Fin r → F) : ℕ := (Finset.univ.filter (fun i => x i = -1)).card

/-- For a tuple valued in `{1,-1}`, the sum equals `r - 2·(count of -1)` in `F`. -/
theorem sum_eq_of_two (r : ℕ) (x : Fin r → F)
    (hx : ∀ i, x i = 1 ∨ x i = -1) :
    (∑ i, x i) = (r : F) - 2 * (cntNeg r x : F) := by
  classical
  unfold cntNeg
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i = -1)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => x i = -1), x i
      = - (Finset.univ.filter (fun i => x i = -1)).card := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ x i = -1), x i
      = (Finset.univ.filter (fun i => ¬ x i = -1)).card := by
    have hcongr : ∑ i ∈ Finset.univ.filter (fun i => ¬ x i = -1), x i
        = ∑ _i ∈ Finset.univ.filter (fun i => ¬ x i = -1), (1 : F) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rcases hx i with h | h
      · exact h
      · exact absurd h (Finset.mem_filter.mp hi).2
    rw [hcongr]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2]
  have hle : (Finset.univ.filter (fun i => x i = -1)).card ≤ r := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin r)) (fun i => x i = -1)
    simpa using this
  have hcompl : (Finset.univ.filter (fun i => ¬ x i = -1)).card
      = r - (Finset.univ.filter (fun i => x i = -1)).card := by
    rw [Finset.filter_not]
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp
  rw [hcompl]
  push_cast [Nat.cast_sub hle]
  ring

/-- Under char `> 2r` (or char 0), the map `a ↦ (r:F) - 2*(a:F)` is injective on `{0,…,r}`. -/
theorem sum_inj_of_char (r : ℕ) (hchar : ringChar F = 0 ∨ ringChar F > 2 * r)
    {a a' : ℕ} (ha : a ≤ r) (ha' : a' ≤ r)
    (heq : (r : F) - 2 * (a : F) = (r : F) - 2 * (a' : F)) : a = a' := by
  classical
  have hz : ((2 * (a : ℤ) - 2 * (a' : ℤ) : ℤ) : F) = 0 := by
    push_cast
    linear_combination - heq
  haveI : CharP F (ringChar F) := ringChar.charP F
  rw [CharP.intCast_eq_zero_iff F (ringChar F)] at hz
  rcases hchar with h0 | hpos
  · rw [h0] at hz
    have : (2 * (a : ℤ) - 2 * (a' : ℤ)) = 0 := zero_dvd_iff.mp (by exact_mod_cast hz)
    omega
  · set k : ℤ := 2 * (a : ℤ) - 2 * (a' : ℤ) with hk
    set p := ringChar F with hp
    have hdvdnat : p ∣ k.natAbs := by
      have : (p : ℤ) ∣ k := hz
      exact Int.ofNat_dvd.mp (by simpa [Int.natAbs_dvd] using this)
    have hbound : k.natAbs < p := by
      have hkb : k.natAbs ≤ 2 * r := by omega
      omega
    have hzero : k.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvdnat hbound
    have : k = 0 := Int.natAbs_eq_zero.mp hzero
    omega

/-- The two-element negation-closed set `{1,−1}` (`= μ_2` when `char ≠ 2`). -/
def Gtwo (F : Type*) [Field F] [DecidableEq F] : Finset F := {1, -1}

/-- The fiber of tuples with exactly `a` copies of `-1` has size `C(r,a)`. -/
theorem fiber_card (hne : (1 : F) ≠ -1) (r a : ℕ) :
    ((Fintype.piFinset (fun _ : Fin r => Gtwo F)).filter (fun x => cntNeg r x = a)).card
      = r.choose a := by
  classical
  have hpc : r.choose a = (Finset.powersetCard a (Finset.univ : Finset (Fin r))).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hpc]
  refine Finset.card_bij
    (fun x _ => Finset.univ.filter (fun i => x i = -1))
    ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    have := hx.2; unfold cntNeg at this; exact this
  · intro x hx y hy hxy
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hx hy
    have hxymem : ∀ i, (x i = -1) ↔ (y i = -1) := by
      intro i
      have := Finset.ext_iff.mp hxy i
      simpa [Finset.mem_filter] using this
    funext i
    by_cases hi : x i = -1
    · rw [hi, ((hxymem i).mp hi)]
    · have hx1 : x i = 1 := by
        have := hx.1 i; rw [Gtwo, Finset.mem_insert, Finset.mem_singleton] at this
        tauto
      have hyi : y i ≠ -1 := fun h => hi ((hxymem i).mpr h)
      have hy1 : y i = 1 := by
        have := hy.1 i; rw [Gtwo, Finset.mem_insert, Finset.mem_singleton] at this
        tauto
      rw [hx1, hy1]
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    refine ⟨fun i => if i ∈ s then -1 else 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i ∈ s <;> simp [hi, Gtwo]
      · unfold cntNeg
        have : (Finset.univ.filter (fun i => (if i ∈ s then (-1 : F) else 1) = -1)) = s := by
          ext i
          rw [Finset.mem_filter]
          by_cases hi : i ∈ s
          · simp [hi]
          · simp only [hi, if_false, Finset.mem_univ, true_and, iff_false]
            exact hne
        rw [this, hs.2]
    · ext i
      rw [Finset.mem_filter]
      by_cases hi : i ∈ s
      · simp [hi]
      · simp only [hi, if_false, Finset.mem_univ, true_and, iff_false]
        exact hne

/-- Membership in `Gtwo` means value is `1` or `-1`. -/
theorem mem_Gtwo_iff (z : F) : z ∈ Gtwo F ↔ z = 1 ∨ z = -1 := by
  rw [Gtwo, Finset.mem_insert, Finset.mem_singleton]

/-- The count `cntNeg r x` is at most `r`. -/
theorem cntNeg_le (r : ℕ) (x : Fin r → F) : cntNeg r x ≤ r := by
  unfold cntNeg
  have := Finset.card_filter_le (Finset.univ : Finset (Fin r)) (fun i => x i = -1)
  simpa using this

/-- **Exact `r`-fold additive energy of `{1,−1}`.** In the no-wraparound regime
(`char F = 0` or `char F > 2r`), `E_r({1,−1}) = C(2r, r)` (the central binomial coefficient).
The energy counts pairs of `{1,−1}`-tuples with equal `−1`-count, `∑_a C(r,a)²`, which is `C(2r,r)`
by Vandermonde (`Nat.sum_range_choose_sq`). -/
theorem twoElementEnergy_centralBinom (hne : (1 : F) ≠ -1) (r : ℕ)
    (hchar : ringChar F = 0 ∨ ringChar F > 2 * r) :
    energyR (Gtwo F) r = (2 * r).choose r := by
  classical
  set P : Finset (Fin r → F) := Fintype.piFinset (fun _ : Fin r => Gtwo F) with hP
  have hsum_count : ∀ x ∈ P, ∀ z ∈ P, ((∑ i, x i = ∑ i, z i) ↔ cntNeg r x = cntNeg r z) := by
    intro x hx z hz
    rw [hP, Fintype.mem_piFinset] at hx hz
    have hx2 : ∀ i, x i = 1 ∨ x i = -1 := fun i => (mem_Gtwo_iff (x i)).mp (hx i)
    have hz2 : ∀ i, z i = 1 ∨ z i = -1 := fun i => (mem_Gtwo_iff (z i)).mp (hz i)
    rw [sum_eq_of_two r x hx2, sum_eq_of_two r z hz2]
    constructor
    · intro h
      exact sum_inj_of_char r hchar (cntNeg_le r x) (cntNeg_le r z) h
    · intro h; rw [h]
  have hE : energyR (Gtwo F) r
      = ∑ x ∈ P, (P.filter (fun z => cntNeg r z = cntNeg r x)).card := by
    rw [energyR, ← hP]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    by_cases h : cntNeg r z = cntNeg r x
    · have : ∑ i, x i = ∑ i, z i := (hsum_count x hx z hz).mpr h.symm
      simp [this, h]
    · have : ¬ (∑ i, x i = ∑ i, z i) := fun he => h ((hsum_count x hx z hz).mp he).symm
      simp [this, h]
  rw [hE]
  set fc : ℕ → ℕ := fun a => (P.filter (fun z => cntNeg r z = a)).card with hfc
  have hrw : ∑ x ∈ P, (P.filter (fun z => cntNeg r z = cntNeg r x)).card
      = ∑ x ∈ P, fc (cntNeg r x) := rfl
  rw [hrw]
  have hmaps : ∀ x ∈ P, cntNeg r x ∈ Finset.range (r + 1) := by
    intro x _; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (cntNeg_le r x)
  rw [← Finset.sum_fiberwise_of_maps_to' (t := Finset.range (r + 1)) hmaps fc]
  have hinner : ∀ a ∈ Finset.range (r + 1),
      (∑ _x ∈ P.filter (fun x => cntNeg r x = a), fc a) = (r.choose a) ^ 2 := by
    intro a _
    rw [Finset.sum_const, smul_eq_mul]
    simp only [hfc]
    have hcard : (P.filter (fun x => cntNeg r x = a)).card = r.choose a := by
      rw [hP]; exact fiber_card hne r a
    rw [hcard, sq]
  rw [Finset.sum_congr rfl hinner]
  rw [Nat.sum_range_choose_sq]

/-- **Exact Gauss-sum moment spectrum at `n=2`.** For a primitive `ψ`, the full `2r`-th moment of
the incomplete character sum over `{1,−1}` is `∑_b ‖η_b‖^{2r} = q · C(2r, r)` (no-wraparound regime).
Combines `subgroup_gaussSum_moment` (`∑_b ‖η_b‖^{2r} = q·E_r`) with the exact energy
`twoElementEnergy_centralBinom`. -/
theorem twoElement_moment_spectrum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hne : (1 : F) ≠ -1)
    (r : ℕ) (hchar : ringChar F = 0 ∨ ringChar F > 2 * r) :
    ∑ b : F, ‖eta ψ (Gtwo F) b‖ ^ (2 * r) = (Fintype.card F : ℝ) * (2 * r).choose r := by
  rw [subgroup_gaussSum_moment hψ (Gtwo F) r, twoElementEnergy_centralBinom hne r hchar]

end ArkLib.ProximityGap.TwoElementEnergy

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.TwoElementEnergy.twoElementEnergy_centralBinom
#print axioms ArkLib.ProximityGap.TwoElementEnergy.twoElement_moment_spectrum
