/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A9 no-go: Kelley–Meka (2023) / PFR cannot cap the bad-γ / vanishing-subset locus past Johnson (#444)

ANGLE A9 (manifesto §IV.9): relocate the cancellation locus to *new structure theory* — the
now-proven Polynomial-Freiman-Ruzsa theorem (GGMT 2023) + Kelley–Meka exponentially-improved
Roth (2023). NEW LEMMA attempted: the bad-γ locus (a "3-term-progression-like / vanishing-subset"
additive object) is forced by KM/PFR into `≤ n` cosets of a bounded-index subgroup PAST the
Johnson radius, giving `M(μ_n) ≤ C√(n log)`.

VERDICT: **reduces-to-wall (energy/moment), via two independent named obstructions**, both
established by exact probes over proper subgroups `μ_n` (p prime, `n = 2^μ`, `n ∣ p−1`, `p ≫ n³`,
never `n = p−1`; `scripts/probes/probe_a9_vanishing_subset_km.py`,
`probe_a9_badgamma_pfr_fast.py`) and recorded here as axiom-clean Lean.

## Obstruction A — Kelley–Meka is the WRONG theorem (3AP-free + density-vacuity)

KM's theorem is one-directional: *a 3AP-FREE subset `A ⊆ 𝔽_p` of density `α` has*
`α ≤ exp(−c (log p)^{1/12})` *(equivalently, density `≳ 1/(log p)^{1+c}` forces a 3AP).* It only
constrains 3AP-free sets *from being large*. Two exact facts kill its use here:

* `μ_n` IS 3AP-free as an additive set (probe: `#3AP = 0` for `n = 8,16,32,64`, every proper
  `μ_n` — the 2-power subgroup carries no additive 3-term progression).
* but its density `α = n/p` is *catastrophically below* the KM ceiling: at the prize scale
  (`n = 2³⁰`, `p ≈ n·2¹²⁸ ≈ 2¹⁵⁸`) the KM 3AP ceiling is `≈ 2⁻⁷` while `α = 2⁻¹²⁸` —
  **121 bits below**. So KM's hypothesis-conclusion implication is *vacuously satisfied*: `μ_n`
  is exactly the kind of set KM permits to be 3AP-free, and the theorem gives no lower bound on
  any 3-term/relation count and *a fortiori* no bound on the sup-norm `M(μ_n)`.

`km_vacuous_below_ceiling` below records the logical core: if a set's density is already `≤` the
KM ceiling, the KM implication `(3AP-free → density ≤ ceiling)` provides **no** new information —
it cannot be triggered to force a 3AP and cannot contradict 3AP-freeness. (This is the same
density-vacuity already logged for the additive Bloom–Sisask/Sanders route in `DISPROOF_LOG.md`,
now isolated as the precise reason KM/PFR — the *post-2023* upgrade — does not change the verdict:
the improvement is in the *exponent of the ceiling*, but at `α = 2⁻¹²⁸` the route never reached
the ceiling to begin with.)

## Obstruction B — the locus is already at the Wick floor (no sub-Wick room for ANY structure thm)

Even granting a structure theorem, the only quantity it could improve is the additive energy
`E_r(μ_n)`, through which the worst-case reduces by the moment bound `M ≤ (p·E_r)^{1/2r}`. But the
exact energy is at the **Wick floor**: `E_r / ((2r−1)‼·n^r) → 1` from *below* (probe: E₂/Wick =
0.875, 0.938, 0.969, 0.984 for `n = 8,16,32,64`; same monotone-to-1 at `r = 3,4`). The char-0 Wick
value `(2r−1)‼·n^r` IS the true energy; a structure theorem can only ever *upper*-bound `E_r`, and
no upper bound below the truth exists. So PFR/KM cannot push `E_r` sub-Wick, and the moment route
delivers exactly the same `M ≍ √(n log q)` *Paley/BGK wall* — not past Johnson. `wick_is_floor`
records that `(p·E_r)^{1/2r} ≥ n` *whenever `E_r ≥ n^{2r}/p`* (the Cauchy–Schwarz floor, which Wick
respects), i.e. the moment bound cannot certify `M < n` regardless of which structure theorem feeds
the energy — re-using the `MomentMethodNoGo` floor with the A9-specific reading that KM/PFR live one
tensor order below the loss and on an energy already minimal.

## Net

A9 falls on the **energy/moment horn** (manifesto "PROVEN DEAD: all moment/energy = Johnson /
forced-anomaly"). The bad-γ set's genuine structure — that it is a *union of `μ_d`-cosets* (proven
group-like by the dilation/scaling identity, `deltastar-407-elekes-szabo-grouplike`) — is
**multiplicative**, not the additive-subgroup-coset structure PFR produces; PFR's conclusion is
both redundant (the coset structure is already a theorem) and of the wrong type (multiplicative vs
additive), and its quantitative input (additive doubling `K ≈ n/2`, maximal) makes the PFR cover
`K^C ≥ |B|` cosets = vacuous. KM's improvement is real mathematics but bites only 3AP-free sets
*at the density ceiling*, which `μ_n` is `2¹²¹×` below. New math, but the wrong universe for this
object.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.A9KelleyMekaPFRNoGo

/-! ## Obstruction A: the Kelley–Meka density implication is vacuous below its own ceiling -/

/-- **Kelley–Meka vacuity.**  Model the KM theorem as the implication
`is3APfree A → density A ≤ kmCeil` (a one-directional upper bound on the density of any 3AP-free
set). If a set's density is *already* `≤ kmCeil`, then KM is satisfied no matter whether `A` is
3AP-free or not — its contrapositive `density A > kmCeil → ¬ is3APfree A` (the only form that could
*produce* a 3AP / lower-bound a relation count) can never fire. Formally: from `density A ≤ kmCeil`
the KM implication holds trivially and yields no constraint linking `A`'s structure to its size.

This is the precise sense in which KM (the post-2023 exp-improvement) gives **nothing** for `μ_n`:
`density = n/p = 2⁻¹²⁸ ≤ 2⁻⁷ ≈ kmCeil` at prize scale, `121` bits of slack. -/
theorem km_vacuous_below_ceiling
    (density kmCeil : ℝ) (is3APfree : Prop)
    (hbelow : density ≤ kmCeil) :
    (is3APfree → density ≤ kmCeil) ∧
      -- the contrapositive trigger `density > kmCeil` is unavailable:
      ¬ (kmCeil < density) := by
  refine ⟨fun _ => hbelow, ?_⟩
  exact not_lt.mpr hbelow

/-- **The KM trigger is dead at the prize density gap.**  Concretely: with the prize-scale numbers
`kmCeil = 2⁻⁷` (the KM/Bloom–Sisask `1/(log p)^{1.04}` 3AP ceiling at `p ≈ 2¹⁵⁸`) and
`density = 2⁻¹²⁸`, the density is strictly below the ceiling, so the KM implication is vacuously
satisfied and cannot be used to force a 3-term progression / lower-bound any relation count.
(We use loose rational stand-ins `1/128 ≤ density ≤ 1/100` is *false*; here `2⁻¹²⁸ < 2⁻⁷` is what
matters and is immediate.) -/
theorem km_trigger_dead_prizescale :
    ¬ ((2 : ℝ) ^ (-(7 : ℤ)) < (2 : ℝ) ^ (-(128 : ℤ))) := by
  have h : (2 : ℝ) ^ (-(128 : ℤ)) ≤ (2 : ℝ) ^ (-(7 : ℤ)) := by
    apply zpow_le_zpow_right₀
    · norm_num
    · norm_num
  exact not_lt.mpr h

/-! ## Obstruction B: the energy is at the Wick floor; the moment bound cannot beat `n` -/

/-- **Cauchy–Schwarz energy floor (re-export, A9 reading).**  For a nonneg count `c` with total
mass `n^r` over a type of cardinality `p`, the energy `∑ c²` satisfies `n^{2r} ≤ p · ∑ c²`. The
Wick value `(2r−1)‼·n^r` for `E_r(μ_n)` *respects* this floor; any structure theorem (PFR/KM) could
only *raise* the lower bound or *lower* an upper bound, but the truth already equals Wick (probe:
`E_r/Wick → 1`), so no sub-Wick energy is available. -/
theorem energy_floor {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ^ (2 * r) ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset σ)) (f := c)
  rw [hcount] at h
  calc (n : ℝ) ^ (2 * r) = ((n : ℝ) ^ r) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 := by simpa [Finset.card_univ] using h

/-- **The moment route cannot certify `M < n` — independent of which structure theorem feeds the
energy.**  `(p · E_r)^{1/2r} ≥ n` whenever `∑ c = n^r`.  KM/PFR live one tensor order below the
loss (`r = 2`) and on an energy already at the Wick floor, so feeding them through the moment
identity yields `M ≥ n` exactly as the trivial bound — never the `√n` the prize needs.  This is the
A9-specialized statement of `MomentMethodNoGo.moment_bound_ge_card`. -/
theorem moment_route_ge_card {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) := by
  have hpow : (n : ℝ) ^ (2 * r) ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 :=
    energy_floor c n r hcount
  have hbase : (0 : ℝ) ≤ (n : ℝ) ^ (2 * r) := by positivity
  have hexp : (0 : ℝ) ≤ (((2 * r : ℕ) : ℝ))⁻¹ := by positivity
  have hmono := Real.rpow_le_rpow hbase hpow hexp
  have hlhs : ((n : ℝ) ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ))⁻¹ = (n : ℝ) :=
    Real.pow_rpow_inv_natCast (by positivity) (by omega)
  rwa [hlhs] at hmono

end ProximityGap.Frontier.A9KelleyMekaPFRNoGo

#print axioms ProximityGap.Frontier.A9KelleyMekaPFRNoGo.km_vacuous_below_ceiling
#print axioms ProximityGap.Frontier.A9KelleyMekaPFRNoGo.km_trigger_dead_prizescale
#print axioms ProximityGap.Frontier.A9KelleyMekaPFRNoGo.energy_floor
#print axioms ProximityGap.Frontier.A9KelleyMekaPFRNoGo.moment_route_ge_card
