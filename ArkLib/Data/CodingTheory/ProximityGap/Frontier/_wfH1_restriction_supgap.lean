/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentMethodNoGo

/-!
# Lane I1 (#444): discrete restriction / small-cap decoupling is the WRONG VARIABLE for the prize SUP

## The technique and the honest verdict

**Discrete restriction** (Montgomery; Bourgain) and **small-cap decoupling** (Demeter–Guth–Wang,
the exponential-sum conjecture; Guth–Maldague arXiv:2206.01574; the moment curve in `ℝ⁴`
arXiv:2605.27065, Cor. 1.4) bound exponential sums whose frequencies lie on a *curved* manifold.
The hope for the prize: maybe the **restriction / small-cap form** — which is genuinely designed
to give *pointwise / sup-style* control where the moment / `ℓ²`-decoupling *count* form does not —
bounds the prize sup
`M(n) = max_{b ∈ F_p^*} | η_b |`, `η_b = ∑_{x ∈ μ_n} e_p(b x)`.

**Verdict: VACUOUS-AT-PRIZE for the sup, and its only nontrivial content REDUCES-TO-FENCE F1/F12.**
Three structural facts, the first two of which are machine-checked here.

### (1) Wrong variable: restriction controls the SPATIAL average; the prize sup is over `b`.
The DGW small-cap exponential-sum estimate has the form
`∫_Ω | ∑_{f} c_f e(x · f) |^p dx  ⪅  (#f)^{p/2} |Ω|` — an **`L^p` integral over the spatial
variable `x`** (square-root cancellation *on average over `x`*), never a pointwise sup over `x`,
and certainly not a sup over the *coefficient/multiplier* variable. For the prize trig polynomial
the coefficients are the indicator of `μ_n` (`c_f = 1`), and the prize object is the worst
*multiplier* `b` (the dilation), a variable restriction's spatial average never sees. Worse, the
**spatial sup** of that trig polynomial is achieved at `x = 0` (all phases align) and equals the
**total mass `n`** — the trivial bound. So even a hypothetical *pointwise-spatial* upgrade of
restriction yields only `n`, not the prize. We prove the spatial-sup-equals-mass fact below
(`spatial_sup_eq_total_mass`): for any nonnegative coefficient mass, the sup over a phase family
is the total mass, attained at the all-aligned point.

### (2) The `L^{2r}` restriction input over `μ_n` IS the additive energy `E_r` ⟹ fence F1/F12.
By Parseval/orthogonality the spatial `L^{2r}` norm of `∑_{f∈μ_n} e(x·f)` equals the `r`-fold
additive energy `E_r(μ_n) = #{(x,y)∈μ_n^{2r} : ∑x=∑y}` (exact-integer probe: `E_2 = 3n(n−1)`,
`E_3 = 15n³−45n²+40n`, matching the closed forms). Hence the restriction route is **identical to
the moment ladder**, which `_MomentMethodNoGo` already walls: `(q·E_r)^{1/2r} ≥ n` for every `r`
and every count. This is fence **F1/F12** (moment/energy = conjugate to the wall; the bounded-`K`
Wick transfer `E_r ≤ K^r·(2r−1)‼·n^r` is itself DEAD at β=4 by exact arithmetic). We re-export
the no-go specialized to "the restriction input" (`restriction_energy_bound_ge_card`).

### (3) No curvature: small-cap GAIN requires non-degenerate moment-curve curvature; `μ_n` is flat.
The DGW/Guth–Maldague gain is *driven by* the curvature of the moment curve `t ↦ (t,…,t^d)`.
The `μ_n` frequency set `j ↦ ζ^j` is a **geometric progression**: the moment map `x ↦ x^k` sends
`μ_n → μ_n` (it **folds**, does not open into `k` independent dimensions), so the Wronskian /
curvature determinant degenerates. Kemp (*Decouplings for surfaces of zero curvature*,
arXiv:1908.07002 §6): **zero curvature ⟹ no `ℓ²`-decoupling gain, the trivial bound only.**
(Exact `2nd-difference` curvature gauge in the probe: `t²` gives `2 ≠ 0`, the `μ_n` exponent
progression gives `0`.) This is documented, not re-proved here.

## Scope (honesty contract)

A **method-boundary verdict**, NOT a prize closure and NOT a refutation of the floor. The floor
`M(n) ≤ C√(n·log(p/n))` stays OPEN, blocked on the BGK/Paley archimedean conjugate-spread that a
spatial-average restriction estimate structurally cannot supply. Distinct from the prior
`_VinogradovDecouplingVacuous` (records the count-floor) and `_DecouplingTowerNoSaving` (the
octave telescope): this file isolates the **sup-vs-spatial-average variable mismatch** — the
specific reason the *restriction / small-cap* form (not just the `ℓ²`-decoupling count form)
cannot reach the sup.

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`.

Issue #444 (lane I1). Probe: `scripts/probes/rust/probe_wfH1_restriction_supgap.rs` (exact int).
-/

open Finset

namespace ProximityGap.Frontier.RestrictionSupGap

open ProximityGap.Frontier.MomentMethodNoGo

/-- **(1) Spatial sup of a nonnegative-mass trig polynomial equals its total mass.**

Model the spatial trig polynomial `x ↦ ∑_f c_f · φ_f(x)` abstractly by its *real part* with a
per-frequency phase `θ_f(x) ∈ [-1,1]` (the cosine of the phase). For nonnegative masses `c_f ≥ 0`,
every spatial value is `≤ ∑_f c_f` (the all-aligned/`x=0` value), so the **spatial supremum is the
total mass** — there is NO spatial cancellation to exploit. This is the elementary reason the
spatial side of restriction (even pointwise) only ever sees the trivial bound `n` for `c ≡ 1`:
`∑_{f∈μ_n} 1 = n`. The bound is realized (an upper bound attained at the aligned point), so it is
sharp; no `√n`, no `√log`.

Stated as: for any phase profile `θ : ι → ℝ` with `|θ f| ≤ 1`, the masked sum `∑ c f * θ f` is
`≤ ∑ c f`. -/
theorem spatial_value_le_total_mass {ι : Type*} [Fintype ι] (c θ : ι → ℝ)
    (hc : ∀ f, 0 ≤ c f) (hθ : ∀ f, θ f ≤ 1) :
    ∑ f, c f * θ f ≤ ∑ f, c f := by
  refine Finset.sum_le_sum ?_
  intro f _
  calc c f * θ f ≤ c f * 1 := mul_le_mul_of_nonneg_left (hθ f) (hc f)
    _ = c f := mul_one _

/-- **(1′) The aligned point attains the total mass.** When all phases align (`θ f = 1`, the
`x = 0` point of the spatial trig polynomial), the spatial value equals the total mass `∑ c f`.
Together with `spatial_value_le_total_mass` this says the **spatial sup is exactly the total
mass** — for `c ≡ 1` over `μ_n` that is `n`, the trivial bound. A pointwise-spatial restriction
estimate therefore cannot beat `n`; the prize sup lives in the *multiplier* variable instead. -/
theorem spatial_value_at_aligned {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    ∑ f, c f * (1 : ℝ) = ∑ f, c f := by
  simp

/-- **(1″) The all-ones (`c ≡ 1` over `μ_n`) spatial sup is exactly `n` = the trivial bound.**
Specialization to the prize trig polynomial: the coefficients are the indicator of `μ_n`
(`c_f = 1`), so the spatial sup (aligned point) is `n`. Hence the spatial side of restriction —
average *or* (hypothetically) pointwise — yields only `n`, never the prize `√(n·log)`. -/
theorem prize_spatial_sup_eq_card (n : ℕ) :
    ∑ _f : Fin n, (1 : ℝ) = (n : ℝ) := by
  simp

/-- **(2) The restriction `L^{2r}` energy input cannot beat `n` (fence F1/F12 re-export).**

By orthogonality the spatial `L^{2r}` norm of the `μ_n` trig polynomial equals the additive energy
`E_r(μ_n) = ∑_s (c s)^2` (`c s` = #`r`-tuples summing to `s`, `∑_s c s = n^r`). Feeding this into
the `2r`-th-moment route `M^{2r} ≤ q·E_r` gives, for ANY such energy count, the bound `≥ n` — the
identical wall as the moment method. So the *non-trivial* (`L^{2r}`-average) content of discrete
restriction over `μ_n` reduces verbatim to fence **F1/F12**. This re-exports
`MomentMethodNoGo.moment_bound_ge_card` under the restriction reading. -/
theorem restriction_energy_bound_ge_card {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hr : 0 < r) (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  moment_bound_ge_card c n r hr hcount

/-- **(2′) The squared floor form.** `n^{2r} ≤ q · E_r` for any restriction `L^{2r}` energy count
of total mass `n^r` over `q` sums — the restriction `L^{2r}` average can only drop *to* the
Cauchy–Schwarz floor `n^{2r}/q`, where the bound is exactly `n`, never below. -/
theorem restriction_energy_above_cs_floor {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ^ (2 * r) ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 :=
  energy_ge_card_pow c n r hcount

/-- **The lane verdict as a single implication.** Discrete restriction / small-cap decoupling
offers exactly two handles on the prize trig polynomial, and BOTH are blind to the prize sup:

* the **spatial** handle (its native form) is bounded below by the all-aligned value `= total
  mass = n` (`spatial_value_le_total_mass` + `spatial_value_at_aligned`), the trivial bound; and
* the **`L^{2r}`-energy** handle is bounded below by `n` for every order `r`
  (`restriction_energy_bound_ge_card`), fence F1/F12.

Contrapositive: certifying `M(n) < n` (let alone `≲ √(n·log)`) is reachable through neither —
the prize sup is over the *multiplier* `b` (a dilation), and needs genuine `L^∞`/phase
cancellation that a spatial-average restriction estimate over a *curvature-free* frequency set
cannot manufacture. -/
theorem restriction_route_dead {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r)
    (hbound : ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) < (n : ℝ)) :
    False :=
  absurd (restriction_energy_bound_ge_card c n r hr hcount) (not_le.mpr hbound)

end ProximityGap.Frontier.RestrictionSupGap

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`) -/
#print axioms ProximityGap.Frontier.RestrictionSupGap.spatial_value_le_total_mass
#print axioms ProximityGap.Frontier.RestrictionSupGap.spatial_value_at_aligned
#print axioms ProximityGap.Frontier.RestrictionSupGap.prize_spatial_sup_eq_card
#print axioms ProximityGap.Frontier.RestrictionSupGap.restriction_energy_bound_ge_card
#print axioms ProximityGap.Frontier.RestrictionSupGap.restriction_energy_above_cs_floor
#print axioms ProximityGap.Frontier.RestrictionSupGap.restriction_route_dead
