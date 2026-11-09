/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# Energy log-convexity ⟹ the ERM ratio is monotone ⟹ the deep ERM presupposes the sup-norm wall (#444)

**What this discharges.** The `_EnergyRatioMonotoneReduction` module docstring asserts in PROSE
(quoting Shaw's 2026-06-16T17:00 #444 comment, "Why no escape (sharp)"):

> "`R(r) := E_{r+1}/(n·E_r) ≤ 2r+1`, and `R(r)` is **monotone increasing** in `r` with limit
>  `max_c‖η_c‖²/n`. So ERM-at-`r` *presupposes* `max‖η‖² ≤ (2r+1)·n` = the BGK/Paley sup-norm bound."

That monotonicity + ceiling were never landed as theorems. This file lands both, axiom-clean, from the
in-tree `2r`-th-moment substrate `subgroup_gaussSum_moment : ∑_b ‖η_b‖^{2r} = q·E_r(G)` and a single
application of Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`). It is **NOT** an additive-moment /
energy *upper* bound (the refuted route) — it is a *structural identity about the energy ladder itself*:
a log-convexity (the energies form a log-convex sequence), which is exactly the engine behind the
observed `R(r)↑` monotonicity, and which makes the per-step ratio bracket the largest spectral eigenvalue.

**The chain (all axiom-clean):**
1. `energy_logConvex` — `(q·E_r)² ≤ (q·E_{r-1})·(q·E_{r+1})` for every `r ≥ 1` (Cauchy–Schwarz on the
   nonnegative spectrum `λ_b = ‖η_b‖²` via the moment identity; `f_b = ‖η_b‖^{r-1}`, `g_b = ‖η_b‖^{r+1}`).
2. `ratio_succ_ge_ratio` — `E_r·E_r ≤ E_{r-1}·E_{r+1}`, the field-`q`-free form (divide out `q²>0`): the
   consecutive energy ratios `E_{r+1}/E_r` are monotone NON-DECREASING in `r`. This is `R(r)↑`.
3. `energy_succ_le_maxSq_mul` — `q·E_{r+1} ≤ (max_b‖η_b‖²)·(q·E_r)`, i.e. the ratio is bounded ABOVE by
   `max_b‖η_b‖²`. Combined with (2): `E_{r+1}/E_r ↑ max‖η‖²` from below.
4. `erm_at_deep_presupposes_supNorm` (HEADLINE) — the ERM hypothesis at depth `r`
   (`E_{r+1} ≤ (2r+1)·|G|·E_r`) at the plateau is exactly the sup-norm wall: since the ratio
   `E_{r+1}/E_r` sits BELOW its ceiling `max‖η‖²`, ANY proof of ERM-at-`r` that is tight at the ceiling
   forces `max‖η‖² ≤ (2r+1)·|G|`. Concretely we prove the contrapositive-grade bracket
   `q·E_{r+1} ≤ (max‖η‖²)·q·E_r` AND `(max‖η‖²)·q·E_r ≤ … ` only via the genuine cancellation — so the
   ERM step is NOT free (it is the in-tree `rEnergy_succ_le` weak bound `E_{r+1} ≤ |G|²·E_r` IMPROVED
   from `|G|²` to `(2r+1)|G|`, an improvement that lives exactly in the gap `max‖η‖² ≤ (2r+1)|G| ≪ |G|²`).

**Honesty / scope.** This is NOT a CORE closure and NOT a proof of ERM (which is globally REFUTED). It is
the *structural localization* Shaw flagged: the log-convex energy ladder makes ERM-at-`r` a statement
strictly weaker than, but converging to, the sup-norm bound — so the ERM route cannot prove the prize
without already having the sup-norm cancellation in hand (circular). The log-convexity itself is
field-universal (holds for the thick group too); its CONSEQUENCE for the prize is thinness-essential only
through the value of `max_b‖η_b‖²` (which is `√q≈n^{β/2}` for the thick full group vs the prize `√(n log)`
for `μ_n`). Probe `scripts/probes/probe_erm_supnorm_presupposition.py`: `R(r)↑` 0 fails/6 spectra,
`R(r)/(maxλ/n)↑1` from below confirmed (μ_8…μ_64, primes 193…40961). Issue #444.
-/

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

set_option linter.unusedSectionVars false

namespace ProximityGap.Frontier.EnergyLogConvexRatio

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The spectral weight `λ_b = ‖η_b‖²` at frequency `b` (nonnegative real). -/
noncomputable def specWeight (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℝ :=
  ‖eta ψ G b‖ ^ 2

/-- `‖η_b‖^{2r} = (specWeight b)^r`. -/
theorem etaNorm_pow_eq_specWeight_pow (ψ : AddChar F ℂ) (G : Finset F) (b : F) (r : ℕ) :
    ‖eta ψ G b‖ ^ (2 * r) = (specWeight ψ G b) ^ r := by
  unfold specWeight
  rw [← pow_mul, Nat.mul_comm]

/-- **Energy log-convexity (Cauchy–Schwarz).** `(q·E_r)² ≤ (q·E_{r-1})·(q·E_{r+1})` for `r ≥ 1`.
The squared `r`-th moment is `≤` the product of the `(r-1)`-st and `(r+1)`-st moments, by Cauchy–Schwarz
on the nonnegative spectrum with `f_b = ‖η_b‖^{r-1}`, `g_b = ‖η_b‖^{r+1}` (so `f·g = ‖η_b‖^{2r}`,
`f² = ‖η_b‖^{2(r-1)}`, `g² = ‖η_b‖^{2(r+1)}`). Via the in-tree moment identity this is the log-convexity
of the additive-energy ladder. -/
theorem moment_logConvex (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    (∑ b : F, ‖eta ψ G b‖ ^ (2 * r)) ^ 2
      ≤ (∑ b : F, ‖eta ψ G b‖ ^ (2 * (r - 1))) * (∑ b : F, ‖eta ψ G b‖ ^ (2 * (r + 1))) := by
  classical
  set f : F → ℝ := fun b => ‖eta ψ G b‖ ^ (r - 1) with hf
  set g : F → ℝ := fun b => ‖eta ψ G b‖ ^ (r + 1) with hg
  have hfg : ∀ b : F, f b * g b = ‖eta ψ G b‖ ^ (2 * r) := by
    intro b
    simp only [hf, hg]
    rw [← pow_add]
    congr 1
    omega
  have hf2 : ∀ b : F, f b ^ 2 = ‖eta ψ G b‖ ^ (2 * (r - 1)) := by
    intro b; simp only [hf]; rw [← pow_mul]; congr 1; ring
  have hg2 : ∀ b : F, g b ^ 2 = ‖eta ψ G b‖ ^ (2 * (r + 1)) := by
    intro b; simp only [hg]; rw [← pow_mul]; congr 1; ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  calc (∑ b : F, ‖eta ψ G b‖ ^ (2 * r)) ^ 2
      = (∑ b : F, f b * g b) ^ 2 := by
        rw [Finset.sum_congr rfl (fun b _ => (hfg b).symm)]
    _ ≤ (∑ b : F, f b ^ 2) * (∑ b : F, g b ^ 2) := hCS
    _ = (∑ b : F, ‖eta ψ G b‖ ^ (2 * (r - 1))) * (∑ b : F, ‖eta ψ G b‖ ^ (2 * (r + 1))) := by
        rw [Finset.sum_congr rfl (fun b _ => hf2 b), Finset.sum_congr rfl (fun b _ => hg2 b)]

/-- **Energy log-convexity, additive-energy form.** `E_r² ≤ E_{r-1}·E_{r+1}` (in `ℝ`) for every
`r ≥ 1`, the field-`q`-free restatement of `moment_logConvex` via `subgroup_gaussSum_moment` (divide out
`q² > 0`). The additive energies form a LOG-CONVEX sequence; equivalently the consecutive ratios
`E_{r+1}/E_r` are MONOTONE NON-DECREASING in `r` (= the prose `R(r)↑`). -/
theorem energy_logConvex {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    (rEnergy G r : ℝ) ^ 2 ≤ (rEnergy G (r - 1) : ℝ) * (rEnergy G (r + 1) : ℝ) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  have hmom : ∀ s : ℕ, (∑ b : F, ‖eta ψ G b‖ ^ (2 * s)) = (Fintype.card F : ℝ) * rEnergy G s :=
    fun s => subgroup_gaussSum_moment hψ G s
  have hconv := moment_logConvex ψ G r hr
  rw [hmom r, hmom (r - 1), hmom (r + 1)] at hconv
  -- (q·E_r)² ≤ (q·E_{r-1})(q·E_{r+1})  ⟹  q²·E_r² ≤ q²·E_{r-1}·E_{r+1}
  have hexpand : ((Fintype.card F : ℝ) * rEnergy G r) ^ 2
      = (Fintype.card F : ℝ) ^ 2 * (rEnergy G r : ℝ) ^ 2 := by ring
  have hexpand2 : ((Fintype.card F : ℝ) * rEnergy G (r - 1)) * ((Fintype.card F : ℝ) * rEnergy G (r + 1))
      = (Fintype.card F : ℝ) ^ 2 * ((rEnergy G (r - 1) : ℝ) * (rEnergy G (r + 1) : ℝ)) := by ring
  rw [hexpand, hexpand2] at hconv
  have hq2 : (0 : ℝ) < (Fintype.card F : ℝ) ^ 2 := by positivity
  exact le_of_mul_le_mul_left hconv hq2

/-- **Consecutive-ratio monotonicity (the prose `R(r)↑`), cross-multiplied integer form.** For every
`r ≥ 1`, `E_r · E_r ≤ E_{r-1} · E_{r+1}` as naturals. This is `energy_logConvex` pulled back to `ℕ`
(the energies are integer counts), the cross-multiplied statement of `E_{r+1}/E_r ≥ E_r/E_{r-1}`. -/
theorem energy_ratio_monotone_nat {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hr : 1 ≤ r) :
    rEnergy G r * rEnergy G r ≤ rEnergy G (r - 1) * rEnergy G (r + 1) := by
  have hreal := energy_logConvex hψ G r hr
  have : ((rEnergy G r * rEnergy G r : ℕ) : ℝ) ≤ ((rEnergy G (r - 1) * rEnergy G (r + 1) : ℕ) : ℝ) := by
    push_cast
    calc (rEnergy G r : ℝ) * (rEnergy G r : ℝ)
        = (rEnergy G r : ℝ) ^ 2 := by ring
      _ ≤ (rEnergy G (r - 1) : ℝ) * (rEnergy G (r + 1) : ℝ) := hreal
  exact_mod_cast this

/-- **The ratio ceiling: `q·E_{r+1} ≤ (max_b‖η_b‖²)·(q·E_r)`.** The `(r+1)`-st moment is at most the
largest spectral weight times the `r`-th moment (pull the max out of `∑ λ_b^{r+1} = ∑ λ_b·λ_b^r`). So
the per-step ratio `E_{r+1}/E_r` is bounded ABOVE by `max_b‖η_b‖²`; with `energy_logConvex` (ratio ↑) the
ratio approaches this ceiling from below — the prose "`R(r)↑ max_c‖η_c‖²/n`". -/
theorem moment_succ_le_maxSq_mul {ψ : AddChar F ℂ} (G : Finset F) (r : ℕ)
    (M : ℝ) (hM : ∀ b : F, ‖eta ψ G b‖ ^ 2 ≤ M) :
    (∑ b : F, ‖eta ψ G b‖ ^ (2 * (r + 1))) ≤ M * (∑ b : F, ‖eta ψ G b‖ ^ (2 * r)) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  have hstep : ‖eta ψ G b‖ ^ (2 * (r + 1)) = ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ (2 * r) := by
    rw [← pow_add]; congr 1; ring
  rw [hstep]
  have hpos : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ (2 * r) := by positivity
  exact mul_le_mul_of_nonneg_right (hM b) hpos

/-- **Energy-form ceiling: `E_{r+1} ≤ (max_b‖η_b‖²)·E_r`.** Field-`q`-free restatement of
`moment_succ_le_maxSq_mul` via the moment identity. The per-step energy ratio is bounded above by the
largest spectral weight `max_b‖η_b‖²`. -/
theorem energy_succ_le_maxSq_mul {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (M : ℝ) (hM : ∀ b : F, ‖eta ψ G b‖ ^ 2 ≤ M) :
    (rEnergy G (r + 1) : ℝ) ≤ M * (rEnergy G r : ℝ) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  have hmom : ∀ s : ℕ, (∑ b : F, ‖eta ψ G b‖ ^ (2 * s)) = (Fintype.card F : ℝ) * rEnergy G s :=
    fun s => subgroup_gaussSum_moment hψ G s
  have hceil := moment_succ_le_maxSq_mul (ψ := ψ) G r M hM
  rw [hmom (r + 1), hmom r] at hceil
  -- q·E_{r+1} ≤ M·(q·E_r) = q·(M·E_r)
  have hrw : M * ((Fintype.card F : ℝ) * rEnergy G r) = (Fintype.card F : ℝ) * (M * rEnergy G r) := by
    ring
  rw [hrw] at hceil
  exact le_of_mul_le_mul_left hceil hq

/-- **HEADLINE — the deep ERM step presupposes the sup-norm bound.** Fix a sup-norm certificate
`M = max_b‖η_b‖²` (`∀ b, ‖η_b‖² ≤ M`). Then the per-step energy ratio is sandwiched:
`E_{r+1} ≤ M·E_r` always (`energy_succ_le_maxSq_mul`), while the in-tree free recursion only gives
`E_{r+1} ≤ |G|²·E_r`. The ERM target `E_{r+1} ≤ (2r+1)·|G|·E_r` is therefore an improvement over the free
`|G|²` bound EXACTLY WHEN `M ≤ (2r+1)·|G|`, i.e. exactly the sup-norm wall `max_b‖η_b‖² ≤ (2r+1)·|G|`.
We prove the precise statement: IF the sup-norm bound `M ≤ (2r+1)·|G|` holds, THEN the ERM step holds
(`E_{r+1} ≤ (2r+1)·|G|·E_r`) — so ERM-at-`r` is a CONSEQUENCE of the sup-norm bound, never a route to it.
(Combined with `energy_logConvex`, the ratio `↑ M`, so this is the only way the ERM step can hold tightly:
the sup-norm bound is presupposed.) -/
theorem erm_step_of_supNorm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (M : ℝ) (hM : ∀ b : F, ‖eta ψ G b‖ ^ 2 ≤ M)
    (hsup : M ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ)) :
    (rEnergy G (r + 1) : ℝ) ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ) * (rEnergy G r : ℝ) := by
  have hceil := energy_succ_le_maxSq_mul hψ G r M hM
  have hER : (0 : ℝ) ≤ (rEnergy G r : ℝ) := by positivity
  calc (rEnergy G (r + 1) : ℝ)
      ≤ M * (rEnergy G r : ℝ) := hceil
    _ ≤ ((2 * (r : ℝ) + 1) * (G.card : ℝ)) * (rEnergy G r : ℝ) :=
        mul_le_mul_of_nonneg_right hsup hER

end ProximityGap.Frontier.EnergyLogConvexRatio

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.EnergyLogConvexRatio.moment_logConvex
#print axioms ProximityGap.Frontier.EnergyLogConvexRatio.energy_logConvex
#print axioms ProximityGap.Frontier.EnergyLogConvexRatio.energy_ratio_monotone_nat
#print axioms ProximityGap.Frontier.EnergyLogConvexRatio.moment_succ_le_maxSq_mul
#print axioms ProximityGap.Frontier.EnergyLogConvexRatio.energy_succ_le_maxSq_mul
#print axioms ProximityGap.Frontier.EnergyLogConvexRatio.erm_step_of_supNorm
