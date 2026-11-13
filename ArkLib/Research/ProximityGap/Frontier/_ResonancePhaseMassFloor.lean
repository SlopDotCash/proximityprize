/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# A UNIVERSAL phase-mass floor for the resonance moment (door-(iv), Lane 2/3)

The resonance moment `T r = ∑_c ‖phaseSum u r c‖²` (the `√p`-free open core of the prize) has the proven
trivial upper ceiling `T r ≤ m·(m-1)^{2(r-1)}` and probe truth `Θ(m^r)` for genuine unit phases.  This
file adds the matching *universal lower floor*, valid for **every** vector `u` (not just unit modulus),
expressed through the **phase mass** `S = ∑_{a≠0} u a`:

> **`T r ≥ |S|^{2r} / m`,  `S = ∑_{a ≠ 0} u a`.**

**Mechanism (a clean Cauchy–Schwarz, fully provable).**
1. Summing the phase-sums over all frequencies reconstructs the whole nonzero filter, which factors:
   `∑_c (phaseSum u r c) = (∑_{a≠0} u a)^r = S^r`  (`sum_phaseSum_eq_phaseMass_pow`).
2. Triangle + Cauchy–Schwarz over the `m` frequencies:
   `|S^r|² = |∑_c phaseSum u r c|² ≤ (∑_c ‖phaseSum u r c‖)² ≤ m·∑_c ‖phaseSum u r c‖² = m·T r`.

**Why this matters (door-(iv) constraint).**  The floor is *order-tight at the constant vector*: for
`u ≡ 1`, `S = m-1`, so `T r ≥ (m-1)^{2r}/m = Θ(m^{2r-1})`, which matches the trivial ceiling order — a
SECOND, independent certificate (companion to `_ResonanceConstantVectorCeiling`) that the DC-coherent
vector is the extremizer and that the trivial ceiling is order-attained.  Conversely, the floor *only*
controls `T r` through the scalar phase mass `|S|`: for genuine Gauss phases `S` is small (multiplicative
cancellation), so the floor goes weak and the open `Θ(m^r)` regime lives precisely where `|S|` collapses.
Thus any prize-relevant improvement must control the *phase distribution*, not merely the phase mass — the
phase-essential / thinness content of door-(iv).

Self-contained leaf (depends only on `GaussPhaseResonance`).  Axiom-clean
(`{propext, Classical.choice, Quot.sound}`).  No CORE / cancellation / completion / moment /
anti-concentration / capacity claim.  Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **The phase mass `S = ∑_{a ≠ 0} u a`** — the aggregate of the nonzero-residue phases. -/
noncomputable def phaseMass (u : ZMod m → ℂ) : ℂ :=
  ∑ a ∈ (Finset.univ.filter (fun a : ZMod m => a ≠ 0)), u a

/-- **Summing the phase-sums over all frequencies gives the `r`-th power of the phase mass.**
`∑_c phaseSum u r c = (∑_{a≠0} u a)^r = S^r`.  The frequency-sum reconstructs the entire
`(∀ i, X i ≠ 0)` filter, which factors over coordinates. -/
theorem sum_phaseSum_eq_phaseMass_pow (u : ZMod m → ℂ) (r : ℕ) :
    ∑ c : ZMod m, phaseSum u r c = (phaseMass u) ^ r := by
  unfold phaseSum phaseMass
  -- LHS: ∑_c ∑_{X : (∀i, X i ≠ 0) ∧ ∑X = c} ∏ u (X i)
  -- collapse the outer c-sum into the (∀ i, X i ≠ 0) filter via fiberwise summation on (∑ i, X i)
  have hfib :
      (∑ c : ZMod m, ∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m =>
          (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)), ∏ i, u (X i))
        = ∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0)),
            ∏ i, u (X i) := by
    rw [← Finset.sum_fiberwise
        (s := Finset.univ.filter (fun X : Fin r → ZMod m => ∀ i, X i ≠ 0))
        (g := fun X : Fin r → ZMod m => ∑ i, X i)
        (f := fun X => ∏ i, u (X i))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfib]
  -- factor the product over the nonzero filter into a power of the phase mass
  rw [Finset.sum_pow' (Finset.univ.filter (fun a : ZMod m => a ≠ 0)) u r]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext X
  simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Cauchy–Schwarz / triangle floor for the resonance moment via the phase mass.**
`‖S^r‖² ≤ m · T r`, i.e. `‖∑_c phaseSum u r c‖² ≤ m · resonanceMoment u r`. -/
theorem normSq_sum_phaseSum_le_card_mul_resonanceMoment (u : ZMod m → ℂ) (r : ℕ) :
    ‖∑ c : ZMod m, phaseSum u r c‖ ^ 2
      ≤ (Fintype.card (ZMod m) : ℝ) * resonanceMoment u r := by
  -- triangle: ‖∑ P c‖ ≤ ∑ ‖P c‖
  have htri : ‖∑ c : ZMod m, phaseSum u r c‖ ≤ ∑ c : ZMod m, ‖phaseSum u r c‖ :=
    norm_sum_le _ _
  have hnn : (0 : ℝ) ≤ ∑ c : ZMod m, ‖phaseSum u r c‖ :=
    Finset.sum_nonneg (fun c _ => norm_nonneg _)
  have hsq : ‖∑ c : ZMod m, phaseSum u r c‖ ^ 2 ≤ (∑ c : ZMod m, ‖phaseSum u r c‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖∑ c : ZMod m, phaseSum u r c‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 htri 2
  -- Cauchy–Schwarz over the m frequencies: (∑ f)^2 ≤ card * ∑ f^2
  have hcs : (∑ c : ZMod m, ‖phaseSum u r c‖) ^ 2
      ≤ ((Finset.univ : Finset (ZMod m)).card : ℝ) * ∑ c : ZMod m, ‖phaseSum u r c‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc ‖∑ c : ZMod m, phaseSum u r c‖ ^ 2
      ≤ (∑ c : ZMod m, ‖phaseSum u r c‖) ^ 2 := hsq
    _ ≤ (Finset.univ.card : ℝ) * ∑ c : ZMod m, ‖phaseSum u r c‖ ^ 2 := hcs
    _ = (Fintype.card (ZMod m) : ℝ) * resonanceMoment u r := by
        rw [resonanceMoment, Finset.card_univ]

/-- **The universal phase-mass floor for the resonance moment.**
`T r ≥ ‖S‖^{2r} / m`,  `S = ∑_{a≠0} u a` the phase mass.  Holds for **every** `u`.
(Equivalently `‖S‖^{2r} ≤ m · T r`.)  Companion lower bound to the proven trivial upper ceiling
`T r ≤ m·(m-1)^{2(r-1)}`; order-tight at `u ≡ 1` (`S = m-1`).  No CORE / cancellation / completion /
moment / anti-concentration / capacity claim. -/
theorem resonanceMoment_ge_phaseMass_pow_div_card (u : ZMod m → ℂ) (r : ℕ) :
    ‖phaseMass u‖ ^ (2 * r) ≤ (Fintype.card (ZMod m) : ℝ) * resonanceMoment u r := by
  have hsum := sum_phaseSum_eq_phaseMass_pow u r
  have hcs := normSq_sum_phaseSum_le_card_mul_resonanceMoment u r
  rw [hsum] at hcs
  -- ‖S^r‖^2 = ‖S‖^(2r)
  have : ‖(phaseMass u) ^ r‖ ^ 2 = ‖phaseMass u‖ ^ (2 * r) := by
    rw [norm_pow, ← pow_mul, Nat.mul_comm]
  rwa [this] at hcs

/-- **Packaged door-(iv) constraint lemma.**  The universal floor `‖S‖^{2r} ≤ m·T r` together with the
phase-mass evaluation `∑_c phaseSum u r c = S^r`.  Records that the resonance moment is bounded below
purely by the scalar phase mass `S = ∑_{a≠0} u a`; the open `Θ(m^r)` regime lives where `‖S‖` collapses
(genuine phase cancellation), so a prize-relevant improvement must control the phase distribution, not the
phase mass.  No CORE / cancellation / completion / moment / anti-concentration / capacity claim. -/
theorem phaseMass_floor_constraint (u : ZMod m → ℂ) (r : ℕ) :
    (∑ c : ZMod m, phaseSum u r c = (phaseMass u) ^ r)
      ∧ ‖phaseMass u‖ ^ (2 * r) ≤ (Fintype.card (ZMod m) : ℝ) * resonanceMoment u r :=
  ⟨sum_phaseSum_eq_phaseMass_pow u r, resonanceMoment_ge_phaseMass_pow_div_card u r⟩

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.sum_phaseSum_eq_phaseMass_pow
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.normSq_sum_phaseSum_le_card_mul_resonanceMoment
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ge_phaseMass_pow_div_card
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseMass_floor_constraint
