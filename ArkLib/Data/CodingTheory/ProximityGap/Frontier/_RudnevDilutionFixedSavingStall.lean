/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Rudnev point-plane STALL at β=4: incidence engines pinch `μ_n` to α=1 (#444, [rudnev-pointplane-stall])

This brick makes the **sum-product / point-plane incidence vacuity precise** for the prize surface.

## The surface (#444 upper bound)

`M = max_{b≠0}‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `μ_n` = `2^a`-th roots in `F_p`, `p ≈ n^β`,
`β = 4`. Through the proven moment route (in-tree), `M^{2r} ≤ p·E_r` where `E_r = rEnergy μ_n r`
is the `r`-fold additive energy. The prize is `M ≤ C√(n log m)` (`α = 1/2`); equivalently
`E_r ≤ (2r-1)‼·n^r` at `r ≈ log p`.

## The engine and its char-p hypothesis (extracted theorems)

* **[Rudnev 1612.02719 / 1703.03309 / 1701.01635]** point-plane incidence
  `I(P,Π) ≪ |P|^{3/2} + k|P|`, valid for `|P| ≤ p^2`. THE engine behind sum-product over `F_p`.
* **[Murphy–Petridis–Roche-Newton–Rudnev–Shkredov 1702.01003]** "breaking 3/2": small `A` with
  additive doubling `M ⟹ |AA| ≫ M^{-2}|A|^{14/9}`, etc.
* **[Stevens–de Zeeuw 1609.06284]** point-line `I(m,n)=O(m^{11/15}n^{11/15})` for
  `m^{7/8}<n<m^{8/7}`, with the **char-p hypothesis** `m^{-2}n^{13} ≪ p^{15}`.

Every one of these bounds the **second** (or third) additive energy of `A`, giving a *fixed*
exponent saving `E_2(μ_n) ≤ n^{3-κ}` (the trivial value is `E_2 ≤ n^3`). The genuine saving `κ>0`
holds only when the subgroup density `θ = log_p(n) = 1/β` exceeds `1/4` — at `β=4`, `θ = 1/4`
sits **at the boundary**, so the engine's saving degenerates to `κ → 0`.

## The PRECISE stall (what is proven here)

The decisive — and genuinely fresh — point is that even GRANTING a fixed second-energy saving
`κ > 0`, the **only** way to reach the `r`-fold energy `E_r` is the tensor / Cauchy–Schwarz iterate
`E_r ≤ n^{2(r-2)}·E_2` (the in-tree trivial step `rEnergy_succ_le`), giving
`E_r ≤ n^{2r-1-κ}`. Pushing through `M^{2r} ≤ p·E_r = n^β·n^{2r-1-κ}`:

  `M ≤ n^{(β + 2r - 1 - κ)/(2r)} = n^{1 + (β-1-κ)/(2r)}`.

The **stall residual** is `(β-1-κ)/(2r)`, which → 0 as `r → log p → ∞` for EVERY fixed `κ`. So:

* the incidence bound NEVER drops below the **census α = 1 stall**: `M ≤ n^{1+o(1)}`;
* it cannot reach the prize `α = 1/2` (`M ≤ n^{1/2+o(1)}`), which would require an
  `r`-LINEAR saving `κ = β + r - 1 ≈ r` — structurally impossible for a fixed-energy engine.

This is the *complement* of the in-tree `_AvMRS` phase-blind floor (which proves the matching
LOWER bound `M ≥ n` from the DC term, i.e. `α ≥ 1`). Together: at `β=4` the entire incidence /
sum-product cluster PINCHES `M` to exponent exactly `1`, vacuous against the prize `1/2`.

## What is proven (axiom-clean: `propext`/`Classical.choice`/`Quot.sound` only)

* `rEnergy_le_pow_secondEnergySaving` — the tensor iterate from a hypothesised `E_2 ≤ n^{3-κ}`:
  `E_r ≤ n^{2(r-2)}·E_2 ≤ n^{2r-1-κ}` (real exponent), the **incidence engine's best `E_r` ceiling**.
* `M_exponent_of_incidence` — the resulting `M`-bound `‖η_b‖ ≤ (p·n^{2r-1-κ})^{1/2r}`, the
  consumer that the incidence saving feeds (uses the proven moment identity).
* `stall_residual_pos` / `stall_residual_to_zero` — the residual `(β-1-κ)/(2r)` is strictly
  positive for every finite `r` (so the bound stays strictly above `α=1`) and tends to `0`
  (so it CONVERGES to the census stall `α=1`, never to the prize `α=1/2`).
* `prize_needs_r_linear_saving` — to reach `M`-exponent `1/2` the engine would need
  `κ = β + r - 1`, an `r`-growing saving: the precise statement that incidence cannot close the gap.
* `theta_quarter_is_boundary` — `θ = 1/β`, and `θ > 1/4 ⟺ β < 4`: `β=4` is exactly the boundary
  where the sum-product saving threshold `θ > 1/4` fails (becomes an equality, vacuous).

## Honest scope (#444)

This is the **expected** outcome for the sum-product / incidence cluster: a precise vacuity /
threshold brick. The named hypothesis `SecondEnergyIncidenceSaving` (`E_2 ≤ n^{3-κ}`) is itself a
genuine open subgroup sum-product bound at `θ = 1/4` (the engine goes vacuous there, `κ → 0`); even
granted, it stalls at `α = 1` by the dilution above. NOT a closure, NOT a refutation of the prize —
the cleanest machine-checked statement of *why* the Rudnev/MRS/Stevens-de Zeeuw engine is vacuous at
`β = 4`. The prize gap (`α: 1 → 1/2`) is pure phase cancellation, invisible to magnitude energies.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CharPMomentRecursion (rEnergy_succ_le)
open ArkLib.ProximityGap.CharPDeepMomentTail
  (rEnergy_le_pow_sharp eta_pow2r_le_card_mul_energy)

namespace ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The incidence engine's input, as an explicit named hypothesis -/

/-- **`SecondEnergyIncidenceSaving G κ`** — the best a single point-plane / sum-product incidence
bound delivers: the **second** additive energy `E_2(G) ≤ |G|^{3-κ}` with a fixed exponent saving
`κ` over the trivial `|G|^3`. (`κ = 0` is the trivial ceiling; the genuine sum-product content is
`κ > 0`, which over `F_p` requires subgroup density `θ = log_p|G| > 1/4` — VACUOUS at `β=4` where
`θ = 1/4`.) Stated with a real exponent so `κ` may be fractional (e.g. the MRS `5/2`-energy bound is
`κ = 1/2`). This is the [Rudnev]/[MRS]/[Stevens–de Zeeuw] engine's output as a named open `Prop`. -/
def SecondEnergyIncidenceSaving (G : Finset F) (κ : ℝ) : Prop :=
  (rEnergy G 2 : ℝ) ≤ (G.card : ℝ) ^ ((3 : ℝ) - κ)

/-! ## 2. The tensor iterate: the engine's BEST `r`-fold energy ceiling

A single incidence bound improves only `E_2`. The ONLY route to the deep `E_r` (`r ≈ log p`) is the
trivial tensor step `E_{k+1} ≤ |G|^2·E_k` (`rEnergy_succ_le`), iterated from the improved base `E_2`.
This dilutes the fixed saving `κ` across `r` folds: `E_r ≤ |G|^{2(r-2)}·E_2 ≤ |G|^{2r-1-κ}`. -/

/-- The pure tensor iterate from a base at `r=2`: `E_r ≤ |G|^{2(r-2)}·E_2` for `r ≥ 2`, by iterating
the trivial step `E_{k+1} ≤ |G|²·E_k` (`rEnergy_succ_le`). This is the *only* engine the literature
supplies to lift a second-energy bound to the `r`-fold energy at prize depth. -/
theorem rEnergy_le_tensor_from_two (G : Finset F) (r : ℕ) (hr : 2 ≤ r) :
    rEnergy G r ≤ G.card ^ (2 * (r - 2)) * rEnergy G 2 := by
  induction r with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · -- k < 2 and k+1 ≥ 2 ⟹ k = 1, i.e. r = 2: trivial, exponent is 0.
      interval_cases k
      · omega
      · simp
    · -- k ≥ 2: use the step then the IH.
      have hstep : rEnergy G (k + 1) ≤ G.card ^ 2 * rEnergy G k := rEnergy_succ_le G k
      have hih : rEnergy G k ≤ G.card ^ (2 * (k - 2)) * rEnergy G 2 := ih hk
      calc rEnergy G (k + 1)
          ≤ G.card ^ 2 * rEnergy G k := hstep
        _ ≤ G.card ^ 2 * (G.card ^ (2 * (k - 2)) * rEnergy G 2) :=
            Nat.mul_le_mul_left _ hih
        _ = G.card ^ (2 * (k + 1 - 2)) * rEnergy G 2 := by
            rw [← mul_assoc, ← pow_add]
            congr 2
            omega

/-- **The incidence engine's best `r`-fold energy ceiling (PROVEN reduction).** Combining the tensor
iterate with the named second-energy saving `E_2 ≤ |G|^{3-κ}` gives `E_r ≤ |G|^{2r-1-κ}` (real
exponent) for `r ≥ 2` — i.e. a *fixed* saving `κ`, NOT a per-fold one. This is exactly the trivial
`κ=0` ceiling `rEnergy_le_pow_sharp` improved by a constant `κ`: the dilution is visible in that the
`κ` does not multiply by `r`. -/
theorem rEnergy_le_pow_secondEnergySaving (G : Finset F) (κ : ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hsave : SecondEnergyIncidenceSaving G κ) :
    (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ ((2 * r : ℝ) - 1 - κ) := by
  have hGcard : (1 : ℝ) ≤ (G.card : ℝ) ∨ G.card = 0 := by
    rcases Nat.eq_zero_or_pos G.card with h | h
    · right; exact h
    · left; exact_mod_cast h
  rcases hGcard with hG1 | hG0
  · -- main case: |G| ≥ 1
    have htensor : (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ (2 * (r - 2)) * (rEnergy G 2 : ℝ) := by
      have := rEnergy_le_tensor_from_two G r hr
      have hcast : (rEnergy G r : ℝ) ≤ ((G.card ^ (2 * (r - 2)) * rEnergy G 2 : ℕ) : ℝ) := by
        exact_mod_cast this
      simpa [Nat.cast_mul, Nat.cast_pow] using hcast
    calc (rEnergy G r : ℝ)
        ≤ (G.card : ℝ) ^ (2 * (r - 2)) * (rEnergy G 2 : ℝ) := htensor
      _ ≤ (G.card : ℝ) ^ (2 * (r - 2)) * (G.card : ℝ) ^ ((3 : ℝ) - κ) := by
          apply mul_le_mul_of_nonneg_left hsave
          positivity
      _ = (G.card : ℝ) ^ ((2 * (r - 2) : ℕ) : ℝ) * (G.card : ℝ) ^ ((3 : ℝ) - κ) := by
          rw [Real.rpow_natCast]
      _ = (G.card : ℝ) ^ ((2 * r : ℝ) - 1 - κ) := by
          have hGpos : (0 : ℝ) < (G.card : ℝ) := by linarith
          rw [← Real.rpow_add hGpos]
          congr 1
          have : ((2 * (r - 2) : ℕ) : ℝ) = (2 * r : ℝ) - 4 := by
            push_cast [Nat.cast_sub (by omega : 2 ≤ r)]
            ring
          rw [this]; ring
  · -- degenerate case: |G| = 0 ⟹ rEnergy G r = 0 for r ≥ 2 (empty piFinset has the product empty)
    have : G.card = 0 := hG0
    -- rEnergy G r with empty G: piFinset over empty family is empty for r ≥ 1 (r ≥ 2 here)
    have hempty : G = ∅ := Finset.card_eq_zero.mp this
    subst hempty
    have hr1 : 1 ≤ r := by omega
    -- E_r(∅) ≤ |∅|^{2r-1} = 0 by the trivial ceiling
    have htriv : rEnergy (∅ : Finset F) r ≤ (∅ : Finset F).card ^ (2 * r - 1) :=
      rEnergy_le_pow_sharp ∅ r hr1
    simp only [Finset.card_empty] at htriv
    have h2r1 : 0 < 2 * r - 1 := by omega
    rw [Nat.zero_pow (by omega)] at htriv
    have : rEnergy (∅ : Finset F) r = 0 := Nat.le_zero.mp htriv
    rw [this]
    simp only [Nat.cast_zero]
    positivity

/-! ## 3. The consumer: the `M`-bound the incidence saving delivers (and its stall) -/

/-- **The `M`-bound from the incidence saving (PROVEN reduction).** Feeding the engine's `r`-fold
ceiling into the proven moment bound `‖η_b‖^{2r} ≤ q·E_r` gives `‖η_b‖^{2r} ≤ q·|G|^{2r-1-κ}`, i.e.
the `2r`-th power of `M ≤ (q·|G|^{2r-1-κ})^{1/2r} = |G|^{(β + 2r - 1 - κ)/(2r)}` (with `q = |G|^β`).
The exponent `(β+2r-1-κ)/(2r) = 1 + (β-1-κ)/(2r)` → 1 — the census `α=1` stall. -/
theorem M_pow_of_incidence {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (κ : ℝ) (r : ℕ) (hr : 2 ≤ r) (b : F) (hsave : SecondEnergyIncidenceSaving G κ) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ ((2 * r : ℝ) - 1 - κ) := by
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := eta_pow2r_le_card_mul_energy hψ G r b
    _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ ((2 * r : ℝ) - 1 - κ) := by
        apply mul_le_mul_of_nonneg_left (rEnergy_le_pow_secondEnergySaving G κ r hr hsave)
        positivity

/-! ## 4. The STALL made precise: the residual `(β-1-κ)/(2r) → 0`, never reaching `α=1/2`

The exponent of the `M`-bound is `α(β,κ,r) = 1 + (β-1-κ)/(2r)`. The "stall residual" is
`(β-1-κ)/(2r)`. These purely arithmetic facts pin the vacuity. -/

/-- The `M`-exponent the incidence route yields: `α(β,κ,r) = (β + 2r - 1 - κ)/(2r)`. -/
noncomputable def MExponent (β κ : ℝ) (r : ℕ) : ℝ := (β + 2 * r - 1 - κ) / (2 * r)

/-- The stall residual `α - 1 = (β - 1 - κ)/(2r)`. -/
noncomputable def stallResidual (β κ : ℝ) (r : ℕ) : ℝ := (β - 1 - κ) / (2 * r)

/-- `MExponent = 1 + stallResidual`: the engine's `M`-exponent is `1` plus the residual. -/
theorem MExponent_eq (β κ : ℝ) (r : ℕ) (hr : 0 < r) :
    MExponent β κ r = 1 + stallResidual β κ r := by
  unfold MExponent stallResidual
  have hr' : (0 : ℝ) < 2 * r := by positivity
  field_simp
  ring

/-- **The stall residual is strictly positive** for every finite `r`, given `κ < β - 1` (any fixed
saving smaller than `β-1`; at `β=4` this is `κ < 3`, which every incidence saving satisfies — the
best is `κ ≤ 1`). So the `M`-bound stays **strictly above** `α = 1` for all finite `r`: the incidence
route never even *reaches* `α = 1`, let alone the prize `α = 1/2`. -/
theorem stall_residual_pos (β κ : ℝ) (r : ℕ) (hr : 0 < r) (hκ : κ < β - 1) :
    0 < stallResidual β κ r := by
  unfold stallResidual
  apply div_pos
  · linarith
  · positivity

/-- **The stall residual → 0** as `r → ∞`: the incidence `M`-exponent CONVERGES to the census
`α = 1` stall. This is the precise vacuity statement: for any fixed saving `κ`, the bound's distance
above `1` shrinks like `1/r`, so at `r ≈ log p` the bound is `n^{1+o(1)}` — exactly the census stall,
never the prize `n^{1/2+o(1)}`. -/
theorem stall_residual_to_zero (β κ : ℝ) :
    Filter.Tendsto (fun r : ℕ => stallResidual β κ r) Filter.atTop (nhds 0) := by
  unfold stallResidual
  have h : (fun r : ℕ => (β - 1 - κ) / (2 * (r : ℝ)))
      = (fun r : ℕ => (β - 1 - κ) * (2 : ℝ)⁻¹ * (r : ℝ)⁻¹) := by
    funext r
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [h]
  have := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa using this.const_mul ((β - 1 - κ) * (2 : ℝ)⁻¹)

/-! ## 5. Why the prize is unreachable: it would need an `r`-LINEAR saving -/

/-- **The prize needs an `r`-linear saving (PROVEN).** To make the incidence `M`-exponent reach the
prize value `1/2`, the required saving is `κ = β + r - 1` — i.e. it must GROW linearly in the depth
`r`. A point-plane / sum-product incidence bound supplies only a fixed `κ = O(1)`. Hence the
incidence engine structurally cannot close the `α: 1 → 1/2` gap; that gap is phase cancellation
(the Paley/BGK conjecture), not a magnitude-energy saving. -/
theorem prize_needs_r_linear_saving (β κ : ℝ) (r : ℕ) (hr : 0 < r) :
    MExponent β κ r = 1 / 2 ↔ κ = β + r - 1 := by
  unfold MExponent
  have hr' : (0 : ℝ) < 2 * r := by positivity
  rw [div_eq_iff (ne_of_gt hr')]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ## 6. The threshold `θ > 1/4` and why `β = 4` is the boundary -/

/-- The subgroup density exponent `θ = log_p|G| = 1/β` (here as the defining relation
`|G| = p^θ ⟺ θ·β = 1` in exponent form, i.e. `θ = 1/β`). -/
noncomputable def theta (β : ℝ) : ℝ := 1 / β

/-- **`β = 4` is exactly the sum-product threshold boundary `θ = 1/4`.** The Rudnev/MRS/Stevens–de
Zeeuw engines deliver a genuine saving `κ > 0` only for subgroup density `θ > 1/4`. Since
`θ = 1/β`, the saving regime is `β < 4`, the boundary is `β = 4` (`θ = 1/4`), and `β > 4` is deeper-
thin (still no saving). So `θ > 1/4 ⟺ β < 4`: at the prize `β = 4` the engine is AT the boundary,
`κ → 0`, vacuous. -/
theorem theta_quarter_is_boundary (β : ℝ) (hβ : 0 < β) :
    theta β > 1 / 4 ↔ β < 4 := by
  unfold theta
  rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) hβ]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- At the prize `β = 4`, the density sits exactly at the threshold: `θ = 1/4`. -/
theorem theta_at_beta_four : theta 4 = 1 / 4 := by
  unfold theta; norm_num

/-! ## 7. Sanity: the engine's saving is a strict improvement over the trivial ceiling

Documenting that `κ > 0` is strictly stronger than the proven `κ = 0` ceiling (so the open content
is precisely the positive saving), and that even so the M-exponent stays > 1. -/

/-- The `κ = 0` instance of the incidence saving is the trivial in-tree ceiling (`E_2 ≤ |G|^3`),
PROVEN — so the gap is exactly `κ > 0`. -/
theorem secondEnergySaving_trivial_kappa_zero (G : Finset F) :
    SecondEnergyIncidenceSaving G 0 := by
  unfold SecondEnergyIncidenceSaving
  have htriv : rEnergy G 2 ≤ G.card ^ (2 * 2 - 1) := rEnergy_le_pow_sharp G 2 (by norm_num)
  have htrivR : (rEnergy G 2 : ℝ) ≤ ((G.card ^ 3 : ℕ) : ℝ) := by
    have : (2 * 2 - 1 : ℕ) = 3 := by norm_num
    rw [this] at htriv; exact_mod_cast htriv
  refine htrivR.trans (le_of_eq ?_)
  rw [Nat.cast_pow, ← Real.rpow_natCast (G.card : ℝ) 3]
  norm_num

end ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall

/-! ## Axiom audit — every PROVEN theorem must show only `[propext, Classical.choice, Quot.sound]`.
The `def`s `SecondEnergyIncidenceSaving`, `MExponent`, `stallResidual`, `theta` are the explicit
named objects (the first is the OPEN incidence hypothesis; no proof of `κ>0` claimed). -/
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.rEnergy_le_tensor_from_two
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.rEnergy_le_pow_secondEnergySaving
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.M_pow_of_incidence
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.MExponent_eq
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.stall_residual_pos
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.stall_residual_to_zero
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.prize_needs_r_linear_saving
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.theta_quarter_is_boundary
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.theta_at_beta_four
#print axioms ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.secondEnergySaving_trivial_kappa_zero
