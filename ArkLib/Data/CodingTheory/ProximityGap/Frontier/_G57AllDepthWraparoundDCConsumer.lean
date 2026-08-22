/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G56AllDepthPatternDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.DCWorstCaseWiring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3NegSymConverse
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingLifting
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CollisionExcessPartition

/-!
# G57: from the all-depth folded-pattern census to the DC prize consumer

G56 gives the exact all-depth identity

`rEnergy (Gset ζ m) r = negSymCount (Gset ζ m) (2*r) + wraparoundExcessR ζ m r`.

This file supplies the smallest non-tautological consumer of that identity.

1. The balanced part is discharged unconditionally: every fiber-balanced tuple admits an
   index-level antipodal pairing, so `negSymCount G (2*r)` is at most the union of the
   `(2*r-1)‼` pairing cells, each of cardinality at most `|G|^r`.
2. Consequently, if the explicit G56 nonzero folded-pattern count fits inside the DC mass,
   `q * wraparoundExcessR ≤ |Gset|^(2*r)`, then `DCEnergyBound (Gset ζ m) r` holds.
3. At `r ≥ log q`, that concrete count hypothesis feeds the existing log-depth
   `WorstCaseIncompleteSumBound` consumer.

The wraparound inequality is still the open BGK/Paley content. This file does not rename an
open energy proposition or claim the prize is closed: it proves the balanced census bound and
reduces the remaining hypothesis to G56's explicit finite-cardinality object.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

open Finset Nat
open scoped Classical

namespace ArkLib.ProximityGap.Frontier.G57AllDepthWraparoundDCConsumer

open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.E3NegSymConverse (sum_eq_zero_of_fiber_balanced)
open ArkLib.ProximityGap.NegationClosedWalk
open ProximityGap.Frontier.CollisionExcessPartition
open ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition
open ArkLib.ProximityGap.DCEnergyCorrection (DCEnergyBound)
open ArkLib.ProximityGap.DCWorstCaseWiring (worstCaseBound_of_dcEnergyBound)
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum (WorstCaseIncompleteSumBound)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

variable {F : Type*} [Field F] [Fintype F]

private theorem negSymCount_le_pairableCount (G : Finset F) (r : ℕ)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) :
    negSymCount G (2 * r) ≤ pairableCount G r := by
  classical
  unfold negSymCount pairableCount pairableSet
  apply Finset.card_le_card
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  obtain ⟨hcG, hbal⟩ := hc
  have hcG' : ∀ i, c i ∈ G := by
    simpa only [Fintype.mem_piFinset] using hcG
  refine ⟨hcG, ?_, ?_⟩
  · exact sum_eq_zero_of_fiber_balanced h2 c (fun i hi => h0 (hi ▸ hcG' i)) hbal
  · unfold IsAntipodallyPairable
    apply exists_isPairing_of_count_balanced c
    · have hcount : ∀ w : F, (Finset.univ.val.map c).count w
          = ((Finset.univ : Finset (Fin (2 * r))).filter (fun i => c i = w)).card := by
        intro w
        rw [Multiset.count_map]
        simp only [Finset.filter]
        congr 1
        apply Multiset.filter_congr
        intro i _
        exact eq_comm
      intro w
      rw [hcount w, hcount (-w)]
      exact hbal w
    · intro i hself
      have hzero : c i = 0 := by
        have hmul : (2 : F) * c i = 0 := by linear_combination hself
        exact (mul_eq_zero.mp hmul).resolve_left h2
      exact h0 (hzero ▸ hcG' i)

/-- Fiber-balanced `2*r`-tuples fit in the Wick pairing budget. This is a closed
combinatorial theorem, not a residual: count balance produces a pairing, and the existing
pairing census bounds the union of all pairing cells. -/
theorem negSymCount_le_wick (G : Finset F) (r : ℕ)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) :
    negSymCount G (2 * r) ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r := by
  calc
    negSymCount G (2 * r) ≤ pairableCount G r :=
      negSymCount_le_pairableCount G r h2 h0
    _ ≤ (Finset.univ.filter
          (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card * G.card ^ r :=
      pairableCount_le_pairings G r
    _ = Nat.doubleFactorial (2 * r - 1) * G.card ^ r := by
      rw [pairings_card_eq_doubleFactorial]

private theorem two_ne_zero_of_primitive_even {K : Type*} [Field K]
    {ζ : K} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) : (2 : K) ≠ 0 := by
  intro h2
  have hneg : (-1 : K) = 1 := by linear_combination -h2
  have hzpow : ζ ^ m = 1 := (zeta_pow_m hm hprim).trans hneg
  exact hprim.pow_ne_one_of_pos_of_lt hm.ne' (by omega) hzpow

private theorem zero_not_mem_Gset {K : Type*} [Field K]
    {ζ : K} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (0 : K) ∉ Gset ζ m := by
  classical
  intro hzero
  obtain ⟨a, _ha, hpow⟩ := Finset.mem_image.mp hzero
  exact (pow_ne_zero a (zeta_ne_zero hm hprim)) hpow

/-- The explicit G56 wraparound count fits inside the DC mass, so the prize's
DC-subtracted energy bound holds. The balanced census is discharged by
`negSymCount_le_wick`; only the concrete nonzero folded-pattern count remains. -/
theorem dcEnergyBound_Gset_of_wraparoundExcessR_le_dc {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hwrap :
      (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
        ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)) :
    DCEnergyBound (Gset ζ m) r := by
  have hbalancedNat := negSymCount_le_wick (Gset ζ m) r
    (two_ne_zero_of_primitive_even hm hprim) (zero_not_mem_Gset hm hprim)
  have hbalanced :
      (negSymCount (Gset ζ m) (2 * r) : ℝ)
        ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * ((Gset ζ m).card : ℝ) ^ r := by
    exact_mod_cast hbalancedNat
  have hdecomp :
      (rEnergy (Gset ζ m) r : ℝ)
        = (negSymCount (Gset ζ m) (2 * r) : ℝ)
          + (wraparoundExcessR ζ m r : ℝ) := by
    exact_mod_cast rEnergy_Gset_eq_negSymCount_add_wraparoundExcessR hm hprim
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hbalancedScaled := mul_le_mul_of_nonneg_left hbalanced hq
  rw [Gset_card hm hprim] at hbalancedScaled
  unfold DCEnergyBound
  rw [hdecomp, Gset_card hm hprim]
  nlinarith [hbalancedScaled, hwrap]

/-- Log-depth prize consumer: the explicit G56 cardinality gate feeds the existing
DC worst-case incomplete-sum theorem at any moment order `r ≥ max(1, log q)`. -/
theorem worstCaseBound_Gset_of_wraparoundExcessR_le_dc {ζ : F} {m r : ℕ}
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r)
    (hwrap :
      (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
        ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)) :
    WorstCaseIncompleteSumBound ψ (Gset ζ m)
      (2 * Real.exp 1 * ((Gset ζ m).card : ℝ) * (r : ℝ)) :=
  worstCaseBound_of_dcEnergyBound hψ hr hrq
    (dcEnergyBound_Gset_of_wraparoundExcessR_le_dc hm hprim hwrap)

#print axioms negSymCount_le_wick
#print axioms dcEnergyBound_Gset_of_wraparoundExcessR_le_dc
#print axioms worstCaseBound_Gset_of_wraparoundExcessR_le_dc

end ArkLib.ProximityGap.Frontier.G57AllDepthWraparoundDCConsumer
