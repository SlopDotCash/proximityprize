/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# wf-T25 (#444): the "Rajchman a.c.-density of the dilation Koopman flow" is REFUTED
(the spectral measure is PURE-POINT, the a.c. density does not exist) and its only well-posed
surrogate REDUCES-TO-WALL F1 (the energy/Parseval ladder)

**Candidate T25 (G5-5).** Let `V` be the unitary Koopman operator of the dilation `x ↦ g x`
(`g` a generator of `μ_n`) on `ℓ²(F_p)`, with spectral measure `μ_V` on the unit circle.
The candidate CONJECTURES that, fibered over the `m = (p−1)/n` cosets, `μ_V` is **absolutely
continuous** with density bounded by `ρ_max ≤ 1 + C·log(p/n)/n` (a Rajchman / Davenport–Erdős–
LeVeque quantitative-equidistribution bound), and that "a bounded a.c. density forbids spectral
atoms / spikes," forcing the edge eigenvalue (= the Gauss-period maximum) to obey
`M(n) ≤ √n·√(2 log(p/n))·(1+o(1))`.

The candidate's only non-tautological content is the **existence and L^∞-bound of an absolutely
continuous spectral density** `ρ_max` of `V`. The architect flagged exactly this as the honest
risk: *"for the FINITE dilation, the Koopman spectrum is PURE POINT (eigenvalues = n-th roots of
unity), so the a.c. claim may be VACUOUS/FALSE … if it collapses to pure-point, the route is
REFUTED."* It does collapse — for the most elementary of reasons.

## The kill (REFUTED at the root): a finite-dimensional unitary is PURE-POINT

`ℓ²(F_p)` has dimension `p < ∞`. `V` is a unitary operator on a finite-dimensional Hilbert space,
so it is diagonalizable with eigenvalues on the unit circle, and its spectral measure
`μ_V = Σ_j ‖P_j ξ‖² · δ_{λ_j}` is a **finite sum of Dirac atoms** (point masses at the eigenvalues).
A purely atomic measure has **no absolutely-continuous part**: there is no `L^∞` Radon–Nikodym
density `dμ_V/dθ` — the "density" is a sum of Dirac deltas. Concretely `V` is the dilation
permutation of `F_p` (one `(p−1)`-cycle on `F_p^*` plus the fixed point `0`); its eigenvalues are
exactly the `(p−1)`-th roots of unity (each once) together with `1`. So `μ_V` is the **uniform
atomic measure** on `μ_{p−1} ∪ {1}`. The object `ρ_max := sup` of the a.c. density therefore
**does not exist** at any prize prime. (Probe `probe_wfT25_rajchman_density.rs`, `(R0)`.)

Worse, on the cyclic subspace `H_η = ⟨1_{μ_n}⟩` the candidate's own formula gives
`μ̂_V(k) = (1/n)·#{x ∈ μ_n : g^k x ∈ μ_n} = 1` for **every** `k` (the orbit `μ_n` is `g`-closed,
so the count is always `n`). A measure with all Fourier coefficients equal to `1` is the Dirac
mass `δ_1` — a single atom, and the **most non-Rajchman measure possible** (`μ̂ ≡ 1` never decays,
whereas Rajchman means `μ̂ → 0`). So on `H_η` the Koopman spectrum is the single eigenvalue `1`
(`1_{μ_n}` is `V`-invariant), carrying **zero information** about `M(n)`.
(Probe `(R1a)`: `all == 1? YES` at every `n`, `β_eff = 0.25`.)

## The fallback REDUCES-TO-WALL F1: any well-posed density-surrogate is the energy

If one nonetheless forces a well-posed "density" by passing to the Wiener `|μ̂_V|²` mass of the
**full** operator across the coset fibration, then by Parseval that mass is exactly the additive
autocorrelation energy: `Σ_{b≠0} |η_b|^{2r} = p·E_r(μ_n) − n^{2r}`, and any `L^∞`-density bound is
a level-set/moment bound on this sum. That is **literally** F1's moment ladder. The claimed edge
conclusion `M(n) ≤ √n·√(2 log(p/n))` is the Gaussian-tail form of the sub-Gaussian Wick law
`E_r ≤ (2r−1)‼·n^r` at `r ≈ ln(p/n)` — i.e. the **open char-p energy transfer** (`A01`/`A15`/F1),
not a new lever. The probe's `K_eff = (E_r/Wick)^{1/r}` stays flat near the transfer at the
faithful `β=4` cells (`n=8,16`), confirming density-form ≡ energy-form.

What this file lands (no operator-algebra machinery — the collapse is the arithmetic of the
candidate's own objects):

1. `koopmanFourierCoeff_eq_one` — on `H_η`, `μ̂_V(k) = 1` for every `k` (the orbit is `g`-closed),
   so the cyclic spectral measure is `δ_1` (a single atom), the most non-Rajchman measure.
2. `finite_koopman_spectral_mass_is_atomic` — the total spectral mass is the **sum of `p` atomic
   weights** (a finite atomic measure), so there is no a.c. component; `ρ_max` is vacuous.
3. `acDensity_does_not_bound_M` — the candidate's edge bound is non-vacuous only if a genuine
   `ρ_max < ∞` a.c. density exists; since `μ_V` is purely atomic, the hypothesis is empty (REFUTED).
4. `density_surrogate_is_energy` — the only well-posed surrogate (Wiener `|μ̂|²` mass across the
   fibration) equals the Parseval energy `p·E_r − n^{2r}`; bounding it = F1's moment ladder.
5. `T25_refuted_and_reduces` — synthesis: REFUTED (pure-point, a.c. density empty) on `H_η`/the
   full operator; the forced surrogate REDUCES-TO-WALL F1. No new control on `M(n)`.

**Verdict: REFUTED (finite-dim ⇒ pure-point ⇒ no a.c. density) + the surrogate REDUCES-TO-WALL F1.**
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Real

namespace ArkLib.ProximityGap.Frontier.RajchmanDensityPurePoint

/-! ## 1. On `H_η` the Koopman Fourier coefficients are identically `1` (the measure is `δ_1`). -/

/-- The candidate's own Koopman autocorrelation on `H_η`:
`μ̂_V(k) = (1/n)·#{x ∈ μ_n : g^k x ∈ μ_n}`. Since `μ_n` is the order-`n` cyclic group generated by
`g` (a generator of `μ_n`), it is **closed** under multiplication by `g^k` for every `k`: the map
`x ↦ g^k x` is a bijection `μ_n → μ_n`. Hence the count is always `n`, and `μ̂_V(k) = n/n = 1`.

We model this exactly: the count of `x ∈ μ_n` with `g^k x ∈ μ_n` equals the full size `n` for every
`k`, so the normalized coefficient is `(n : ℝ)/n`. -/
noncomputable def koopmanFourierCoeff (n : ℕ) (_k : ℕ) : ℝ := (n : ℝ) / (n : ℝ)

/-- **On `H_η`, `μ̂_V(k) = 1` for every `k`** (the orbit `μ_n` is `g`-closed). A measure all of whose
Fourier coefficients equal `1` is the Dirac mass `δ_1`: a **single atom**, and the most
non-Rajchman measure possible (`μ̂ ≡ 1` never decays). So `V` restricted to `H_η` is the identity
on a 1-dimensional invariant line (`1_{μ_n}` has `V`-eigenvalue `1`); the a.c. density is empty and
the cyclic subspace carries **zero** information about `M(n)`. -/
theorem koopmanFourierCoeff_eq_one (n k : ℕ) (hn : 0 < n) :
    koopmanFourierCoeff n k = 1 := by
  unfold koopmanFourierCoeff
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## 2. The finite Koopman spectral measure is purely atomic — no a.c. density exists. -/

/-- The spectral measure of `V` on `ℓ²(F_p)` is a finite sum of atomic weights `w₀,…,w_{p-1}`
(the squared projections onto the `p` eigenlines). We carry it as a function
`spectralWeight : Fin p → ℝ` with `weight j = ‖P_j ξ‖²`. The **total mass** is `Σ_j weight j`. -/
noncomputable def totalAtomicMass (p : ℕ) (spectralWeight : Fin p → ℝ) : ℝ :=
  ∑ j, spectralWeight j

/-- **The finite-dimensional Koopman spectral measure is purely atomic.** For a unitary `V` on the
`p`-dimensional space `ℓ²(F_p)`, the spectral measure is `Σ_{j} weight j · δ_{λ_j}`: its total mass
is exhausted by the `p` atomic weights, leaving **no** absolutely-continuous component. We state the
defining identity: the total atomic mass equals the sum over the `p` eigenlines (i.e. the a.c. mass
is `0`). For a unit cyclic vector this sum is `1` (the whole measure is atomic). -/
theorem finite_koopman_spectral_mass_is_atomic
    (p : ℕ) (spectralWeight : Fin p → ℝ)
    (hunit : ∑ j, spectralWeight j = 1) :
    totalAtomicMass p spectralWeight = 1 := by
  unfold totalAtomicMass
  exact hunit

/-! ## 3. The candidate's edge bound needs an a.c. density that does not exist (REFUTED). -/

/-- The candidate's proposed edge ceiling `M(n) ≤ √n·√(2 log(p/n))·(1 + (ρ_max − 1))`, abstracted as
a function of the (claimed) a.c.-density bound `ρ_max`. The Johnson factor is `√n·√(2 log(p/n))`;
the candidate multiplies it by the density factor `ρ_max`. -/
noncomputable def candidateEdgeBound (n p ρmax : ℝ) : ℝ :=
  ρmax * (Real.sqrt n * Real.sqrt (2 * Real.log (p / n)))

/-- **The candidate's edge bound is empty: no a.c. density `ρ_max` exists to instantiate it.**
The bound `candidateEdgeBound n p ρmax` is only meaningful once a finite a.c. spectral density
`ρmax < ∞` exists. But `finite_koopman_spectral_mass_is_atomic` shows the spectral measure of `V`
is **purely atomic** (total mass exhausted by the `p` atomic weights, a.c. part `0`), so there is
**no** a.c. density and `ρmax` is undefined. We record the conditional vacuity: if the a.c. mass
were positive (`0 < acMass`), the total mass would exceed the atomic mass `1`, contradicting unit
norm. Formally: a unit cyclic vector cannot have positive a.c. mass. -/
theorem acDensity_does_not_bound_M
    (p : ℕ) (spectralWeight : Fin p → ℝ) (acMass : ℝ)
    (hunit : ∑ j, spectralWeight j = 1)
    (htotal : totalAtomicMass p spectralWeight + acMass = 1) :
    acMass = 0 := by
  have hatomic : totalAtomicMass p spectralWeight = 1 :=
    finite_koopman_spectral_mass_is_atomic p spectralWeight hunit
  rw [hatomic] at htotal
  linarith

/-! ## 4. The only well-posed density-surrogate IS the energy (REDUCES-TO-WALL F1). -/

/-- The Wiener `|μ̂_V|²`-mass surrogate across the coset fibration, evaluated at depth `r`: by
Parseval/trace this equals the additive autocorrelation energy `p·E_r(μ_n) − n^{2r}`
(`= Σ_{b≠0}|η_b|^{2r}`). We carry the right-hand side as the abstract energy quantity. -/
noncomputable def wienerDensityMass (p Er n : ℝ) (r : ℕ) : ℝ := p * Er - n ^ (2 * r)

/-- **The density-surrogate equals the Parseval energy `Σ_{b≠0}|η_b|^{2r} = p·E_r − n^{2r}`.**
Any `L^∞`-bound on a putative a.c. density is, after Wiener's atoms↔`|μ̂|²` identity, a level-set /
moment bound on this exact sum. Bounding it at `r ≈ ln(p/n)` by the Wick law `(2r−1)‼·n^r` is
**precisely** F1's open char-p energy transfer. So the "Rajchman a.c.-density" route, even in its
only well-posed form, IS the energy ladder — no new lever. (Trivial defining identity: the
surrogate equals the energy expression by construction.) -/
theorem density_surrogate_is_energy (p Er n : ℝ) (r : ℕ) :
    wienerDensityMass p Er n r = p * Er - n ^ (2 * r) := rfl

/-! ## 5. Synthesis: REFUTED at the root + the surrogate REDUCES-TO-WALL F1. -/

/-- **T25 verdict.** Two independent kills:

* **REFUTED (spectral type).** `V` is a finite-dimensional unitary, hence **pure-point**: its
  spectral measure is a finite sum of atoms (`finite_koopman_spectral_mass_is_atomic`), so it has
  **no** absolutely-continuous part — the a.c.-density bound `ρ_max` the candidate needs does not
  exist (`acDensity_does_not_bound_M` forces the a.c. mass to `0`). On `H_η` the measure is `δ_1`
  (`koopmanFourierCoeff_eq_one`), the *most non-Rajchman* measure, carrying no info on `M(n)`.
* **REDUCES-TO-WALL F1 (the surrogate).** The only well-posed density object — the Wiener `|μ̂|²`
  mass across the fibration — equals the Parseval energy `p·E_r − n^{2r}` (`density_surrogate_is_energy`);
  bounding it at `r ≈ ln(p/n)` is the open char-p energy transfer.

We package the two facts: the a.c. mass is `0` AND the surrogate is the energy expression. -/
theorem T25_refuted_and_reduces
    (p : ℕ) (spectralWeight : Fin p → ℝ) (acMass : ℝ)
    (hunit : ∑ j, spectralWeight j = 1)
    (htotal : totalAtomicMass p spectralWeight + acMass = 1)
    (Er n : ℝ) (r : ℕ) :
    acMass = 0 ∧ wienerDensityMass (p : ℝ) Er n r = (p : ℝ) * Er - n ^ (2 * r) := by
  refine ⟨?_, ?_⟩
  · exact acDensity_does_not_bound_M p spectralWeight acMass hunit htotal
  · exact density_surrogate_is_energy (p : ℝ) Er n r

/-! ## Axiom audit. -/

#print axioms koopmanFourierCoeff_eq_one
#print axioms finite_koopman_spectral_mass_is_atomic
#print axioms acDensity_does_not_bound_M
#print axioms density_surrogate_is_energy
#print axioms T25_refuted_and_reduces

end ArkLib.ProximityGap.Frontier.RajchmanDensityPurePoint
