/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant

/-!
# Bridge B40 — tying the prize structural constant `Λ²` to `D*` via the period sum (P2)

This file ties the **prize structural constant**
`Λ²(ψ,G) = max_{b≠0} ‖η_b‖²` (`PrizeStructuralConstant.prizeRadiusSq`)
to the **far-line incidence L²-energy** of P2
(`IncidencePeriodBridge.incidence_l2_eq_period_l2`,
`∑_{s₀} I(s₀,0)² = q·∑_b ‖η_b‖²`).

The incidence L²-energy is the natural aggregate `D*`-proxy: it is the total
squared count of how far lines hit the ball, summed over offsets. P2 makes it
equal to `q·∑_b ‖η_b‖²`. The constant `Λ²` is the *sup* (per-direction worst
case) of the same period spectrum. So the two are tied by the elementary
sup/average pinch over the nonzero frequencies.

## What is proven here (unconditional, axiom-clean)

* **`period_energy_split`** — `∑_b ‖η_b‖² = n² + ∑_{b≠0} ‖η_b‖²`, peeling the
  principal frequency `η_0 = n`.

* **`incidence_l2_eq_principal_plus_nonprincipal`** — P2 read in the split form:
  `∑_{s₀} I(s₀,0)² = q·(n² + ∑_{b≠0} ‖η_b‖²)`.

* **`nonprincipal_energy_le_prizeRadiusSq`** — the *upper* tie:
  `∑_{b≠0} ‖η_b‖² ≤ (q−1)·Λ²` (every nonprincipal term `≤` the max `Λ²`).

* **`incidence_l2_le_prizeRadiusSq`** — combining the two: the far-line
  incidence L²-energy is controlled by `Λ²`,
  `∑_{s₀} I(s₀,0)² ≤ q·(n² + (q−1)·Λ²)`.

* **`incidence_l2_ge_prizeRadiusSq`** — the *lower* tie (`Λ² = max ≥` one term):
  picking the worst frequency `b*` attaining `Λ²`,
  `∑_{s₀} I(s₀,0)² ≥ q·(n² + Λ²)`  *fails in general* — instead the honest
  lower tie is via the floor, `∑_{s₀} I(s₀,0)² ≥ q·n²` together with the
  Parseval floor `Λ² ≥ (q·n − n²)/(q−1)`, recorded as
  `prizeRadiusSq_floor_via_energy`.

Both ties are pure `Finset.sup'`/second-moment algebra over additive-character
orthogonality; no field-size or regime hypotheses. Issue #444 (P2 ↔ Λ).
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge
open ArkLib.ProximityGap.PrizeStructuralConstant

namespace ArkLib.ProximityGap.BridgeB40

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The principal period is `η_0 = |G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  simp only [eta, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The period energy split**: peel the principal frequency `η_0 = |G|`,
`∑_b ‖η_b‖² = |G|² + ∑_{b≠0} ‖η_b‖²`. -/
theorem period_energy_split (ψ : AddChar F ℂ) (G : Finset F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 2)
      = (G.card : ℝ) ^ 2 + ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 := by
  classical
  rw [← Finset.add_sum_erase _ (fun b => ‖eta ψ G b‖ ^ 2) (Finset.mem_univ 0)]
  congr 1
  rw [eta_zero, Complex.norm_natCast]

/-- **P2 in split form.** The far-line incidence L²-energy equals `q` times the
principal period energy plus the nonprincipal period energy:
`∑_{s₀} I(s₀,0)² = q·(|G|² + ∑_{b≠0} ‖η_b‖²)`. -/
theorem incidence_l2_eq_principal_plus_nonprincipal {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) :
    (∑ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2)
      = (Fintype.card F : ℝ)
          * ((G.card : ℝ) ^ 2 + ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2) := by
  rw [incidence_l2_eq_period_l2 hψ G, period_energy_split ψ G]

/-- **The upper tie.** Every nonprincipal period `‖η_b‖²` is at most the prize
constant `Λ² = max_{b≠0} ‖η_b‖²`, so the total nonprincipal energy is
`≤ (q−1)·Λ²`. -/
theorem nonprincipal_energy_le_prizeRadiusSq (ψ : AddChar F ℂ) (G : Finset F) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2)
      ≤ ((Fintype.card F : ℝ) - 1) * prizeRadiusSq ψ G := by
  classical
  have hcard : ((Finset.univ.erase (0 : F)).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have : 1 ≤ Fintype.card F := Fintype.card_pos
    push_cast [Nat.cast_sub this]; ring
  calc ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      ≤ ∑ _b ∈ Finset.univ.erase (0 : F), prizeRadiusSq ψ G :=
        Finset.sum_le_sum (fun b hb => Finset.le_sup' (fun b => ‖eta ψ G b‖ ^ 2) hb)
    _ = ((Finset.univ.erase (0 : F)).card : ℝ) * prizeRadiusSq ψ G := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card F : ℝ) - 1) * prizeRadiusSq ψ G := by rw [hcard]

/-- **The B40 upper bridge.** The far-line incidence L²-energy (P2 aggregate,
the natural `D*`-energy proxy) is controlled by the prize structural constant
`Λ²`:
`∑_{s₀} I(s₀,0)² ≤ q·(|G|² + (q−1)·Λ²)`. -/
theorem incidence_l2_le_prizeRadiusSq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (∑ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((G.card : ℝ) ^ 2 + ((Fintype.card F : ℝ) - 1) * prizeRadiusSq ψ G) := by
  rw [incidence_l2_eq_principal_plus_nonprincipal hψ G]
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  apply mul_le_mul_of_nonneg_left _ hq
  gcongr
  exact nonprincipal_energy_le_prizeRadiusSq ψ G

/-- **The B40 lower bridge.** A *single* worst frequency already forces the
nonprincipal energy `≥ Λ²` (the max is one of the summed terms, the rest are
`≥ 0`), so
`∑_{s₀} I(s₀,0)² ≥ q·(|G|² + Λ²)`.
This is the honest `D*`-energy lower bound by `Λ²`: the worst per-direction
period drives the aggregate incidence energy. -/
theorem incidence_l2_ge_prizeRadiusSq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (Fintype.card F : ℝ) * ((G.card : ℝ) ^ 2 + prizeRadiusSq ψ G)
      ≤ (∑ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2) := by
  classical
  rw [incidence_l2_eq_principal_plus_nonprincipal hψ G]
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  apply mul_le_mul_of_nonneg_left _ hq
  gcongr
  -- `Λ² = sup' f` is attained at some `b* ∈ erase 0`; that single term is `≤` the sum (rest ≥0).
  obtain ⟨b, hb, hbeq⟩ :=
    Finset.exists_mem_eq_sup' erase_zero_nonempty (fun b => ‖eta ψ G b‖ ^ 2)
  rw [prizeRadiusSq, hbeq]
  refine Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ 2) ?_ hb
  intro i _; positivity

/-- **Floor restated through the energy bridge.** The Parseval floor on `Λ²`
(`prizeRadiusSq_parseval_floor`) combined with `incidence_l2_ge_prizeRadiusSq`
gives the incidence L²-energy floor through `Λ²`:
`∑_{s₀} I(s₀,0)² ≥ q·(|G|² + (q·|G| − |G|²)/(q−1))`. -/
theorem prizeRadiusSq_floor_via_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (Fintype.card F : ℝ)
        * ((G.card : ℝ) ^ 2
            + ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1))
      ≤ (∑ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2) := by
  refine le_trans ?_ (incidence_l2_ge_prizeRadiusSq hψ G)
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  apply mul_le_mul_of_nonneg_left _ hq
  gcongr
  exact prizeRadiusSq_parseval_floor hψ G

end ArkLib.ProximityGap.BridgeB40

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BridgeB40.incidence_l2_le_prizeRadiusSq
#print axioms ArkLib.ProximityGap.BridgeB40.incidence_l2_ge_prizeRadiusSq
#print axioms ArkLib.ProximityGap.BridgeB40.prizeRadiusSq_floor_via_energy
