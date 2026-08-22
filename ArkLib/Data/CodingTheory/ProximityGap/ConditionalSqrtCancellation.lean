/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.GeneralEnergyBound
import Mathlib.Tactic

/-!
# Conditional square-root cancellation: the dyadic conjecture under the no-relation hypothesis (#389)

Chaining the moment-method sup-norm bound (`worst_period_moment_le`) with the general-`r` additive-energy
bound (`energyR_le_factorial`) gives, for EVERY `r`, the explicit worst-period bound

> `worst_period_le_factorial` :  `b ≠ 0  →  ‖η_b‖^{2r} ≤ q · r! · |G|^r`,

valid whenever `G` is *Sidon to order r* (`H`: every pair of equal-sum `r`-tuples is a permutation).
Taking `2r`-th roots gives the square-root-cancellation form `max_{b≠0} ‖η_b‖ ≤ (q · r! · |G|^r)^{1/2r}`.

**SCOPE WARNING (important).** `H` is *full* Sidon-to-`r` and is NOT satisfied by `μ_n`: since `μ_n` is
negation-closed, `(a, −a)` and `(b, −b)` have equal sum `0` without being permutations, so `H` fails
already at `r = 2` (`E₂(μ_n) = 3n²−3n > 2n²−n`). Hence this is a valid *general* lemma for genuinely
Sidon-to-`r` sets, but it does **not** apply to `μ_n` and does **not** prove the dyadic conjecture. The
correct `μ_n` bound is the *negation-closed* walk count `E_r(μ_n) ≤ (2r−1)!!·n^r` (accounting for the
antipodal relations); formalizing it ("K1") is the open step. The `r = 2` case `‖η_b‖⁴ ≤ 3qn²` IS valid
for `μ_n` via `repCount ≤ 2` (Sidon *mod negation*) — see `WorstPeriodSidonBound`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional square-root cancellation (per moment `r`).** If `G` has no nontrivial `r`-fold
additive relation, every nontrivial Gaussian period satisfies `‖η_b‖^{2r} ≤ q · r! · |G|^r`. Hence
`max_{b≠0} ‖η_b‖ ≤ (q · r! · |G|^r)^{1/2r}`, which optimized over `r ≈ log f` is `√(|G| log f)` — the
dyadic square-root-cancellation bound, proven under the no-relation hypothesis. -/
theorem worst_period_le_factorial {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (H : ∀ x ∈ Fintype.piFinset (fun _ : Fin r => G), ∀ z ∈ Fintype.piFinset (fun _ : Fin r => G),
          (∑ i, x i = ∑ i, z i) → ∃ σ : Equiv.Perm (Fin r), z = x ∘ σ)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * r.factorial * (G.card : ℝ) ^ r := by
  have h1 := worst_period_moment_le hψ G r hb
  have h2 : (energyR G r : ℝ) ≤ (r.factorial : ℝ) * (G.card : ℝ) ^ r := by
    exact_mod_cast energyR_le_factorial G r H
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) := h1
    _ ≤ (Fintype.card F : ℝ) * energyR G r := by
        have : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
        linarith
    _ ≤ (Fintype.card F : ℝ) * ((r.factorial : ℝ) * (G.card : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left h2 hqnn
    _ = (Fintype.card F : ℝ) * r.factorial * (G.card : ℝ) ^ r := by ring

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.worst_period_le_factorial
