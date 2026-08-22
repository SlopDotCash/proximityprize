/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import Mathlib.Tactic

/-!
# Sub-`√q` upper bound on the worst period in the Sidon regime (#389)

The `r = 2` instance of the dyadic square-root-cancellation conjecture, **proven** conditionally on the
Sidon (representation-≤ 2) property. From the fourth moment `∑_b ‖η_b‖⁴ = q·E(G)` and the minimal-energy
bound `E(G) ≤ 3|G|²` (which holds the moment `μ_n` is Sidon-mod-negation — i.e. `q > 2^n` via the
cyclotomic resultant lift):

> `worst_period_sidon_le` :  `‖η_b‖⁴ ≤ 3·q·|G|²`   for every `b`.

So `max_b ‖η_b‖ ≤ (3q)^{1/4}·√|G|`, which is **below the completion bound `√q`** exactly when
`|G| < q/3` — and for `|G| = n < √q` it is `≈ q^{1/4}√n ≪ √q`. This is a genuine sub-`√q` upper bound
on the worst subgroup Gaussian period, narrowing the bracket `[√n, √q]` on its proven (upper) side; the
conjecture asserts the analogous bound at every moment `r`, giving `√(n log f)`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.WorstPeriodSidon

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sub-`√q` worst-period bound in the Sidon regime.** If `G` is Sidon-mod-negation
(`repCount G t ≤ 2` for all `t ≠ 0`), then every Gaussian period satisfies `‖η_b‖⁴ ≤ 3·q·|G|²`, hence
`max_b ‖η_b‖ ≤ (3q)^{1/4}√|G|` — below the completion bound `√q` for `|G| < q/3`. -/
theorem worst_period_sidon_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ 2) (b : F) :
    ‖eta ψ G b‖ ^ 4 ≤ 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by
  classical
  -- single term ≤ total fourth moment = q · E(G)
  have hterm : ‖eta ψ G b‖ ^ 4 ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ 4 :=
    Finset.single_le_sum (f := fun b' => ‖eta ψ G b'‖ ^ 4)
      (fun _ _ => by positivity) (Finset.mem_univ b)
  rw [subgroup_gaussSum_fourthMoment hψ G] at hterm
  -- E(G) = additiveEnergy G ≤ 3|G|²  (Sidon / rep ≤ 2)
  have hE : (addEnergy G : ℝ) ≤ 3 * (G.card : ℝ) ^ 2 := by
    have hbridge := ArkLib.ProximityGap.AdditiveEnergyBridge.additiveEnergy_eq_addEnergy G
    have hle := additiveEnergy_le_three_of_repTwo G hrep
    rw [hbridge] at hle
    exact_mod_cast hle
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ 4
      ≤ (Fintype.card F : ℝ) * (addEnergy G : ℝ) := hterm
    _ ≤ (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hE hqnn
    _ = 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by ring

/-- **Exact Sidon sub-completion threshold, in fourth-power form.**  The Sidon fourth-moment
incidence bound beats the trivial completion fourth power `q²` as soon as `3 |G|² ≤ q`.  This
is the precise scale condition hidden in the informal fourth-root statement: the fourth-moment
Sidon route gives sub-`√q` control only in the very thin range `|G| ≤ √(q/3)`, so it is a
useful exact incidence brick but not a prize-regime CORE closure by itself. -/
theorem worst_period_sidon_le_completion_pow4 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ 2) (b : F)
    (hthin : 3 * G.card ^ 2 ≤ Fintype.card F) :
    ‖eta ψ G b‖ ^ 4 ≤ (Fintype.card F : ℝ) ^ 2 := by
  have hsidon := worst_period_sidon_le hψ G hrep b
  have hthinR : 3 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast hthin
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ 4
      ≤ 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := hsidon
    _ = (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2) := by ring
    _ ≤ (Fintype.card F : ℝ) * (Fintype.card F : ℝ) :=
        mul_le_mul_of_nonneg_left hthinR hqnn
    _ = (Fintype.card F : ℝ) ^ 2 := by ring

end ArkLib.ProximityGap.WorstPeriodSidon

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WorstPeriodSidon.worst_period_sidon_le
#print axioms ArkLib.ProximityGap.WorstPeriodSidon.worst_period_sidon_le_completion_pow4
