/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
permutation of `F_p`.  Since `g` generates `μ_n`, it has multiplicative order `n`, so `x ↦ g x`
fixes `0` and splits `F_p^*` into the `m = (p−1)/n` cosets of `μ_n`, each an `n`-cycle (e.g. `p = 13`,
`g = 5` of order `4`: three `4`-cycles).  Its eigenvalues are therefore the `n`-th roots of unity,
each with multiplicity `m`, together with an extra eigenvalue `1` from the fixed point `0`
(audit correction CW-B19-10 / CW-DL08a-03: an earlier version said "one `(p−1)`-cycle" and
"the `(p−1)`-th roots of unity each once", which is wrong for `n < p−1`).  So every spectral
measure of `V` is atomic, supported on `μ_n ⊂ S¹`. The object `ρ_max := sup` of the a.c. density
therefore **does not exist** at any prize prime. (Probe `probe_wfT25_rajchman_density.rs`, `(R0)`.)

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

What this file lands.  Only item 1 is a genuine (if elementary) computation; items 2–5 are
**arithmetic placeholders** that restate their hypotheses or definitions and do not formalize the
Koopman operator, its spectral measure, or Parseval (audit CW-B19-10 / CW-DL08a-03).  The pure-point
verdict itself rests on the standard fact that a unitary on a finite-dimensional space is
diagonalizable, which is prose here.

1. `koopmanFourierCoeff_eq_one` — for a finite subgroup `H` (standing for `μ_n`) and `g ∈ H`,
   `#{x ∈ H : g^k x ∈ H} / #H = 1` for every `k`: the candidate's `μ̂_V(k)` on `H_η` is identically
   `1` because `H` is `g`-closed.
2. `finite_koopman_spectral_mass_is_atomic` — placeholder: if a family of weights sums to `1`, its
   `totalAtomicMass` (defined as that sum) is `1`.  The hypothesis is the conclusion.
3. `acDensity_does_not_bound_M` — placeholder: linear arithmetic, `1 + acMass = 1 ⇒ acMass = 0`, with
   the decomposition encoded as a hypothesis.
4. `density_surrogate_is_energy` — placeholder: `rfl` on the definition `wienerDensityMass := p·E_r −
   n^{2r}`; the Parseval identity it names is not proved.
5. `T25_refuted_and_reduces` — the conjunction of 3 and 4.

**Verdict: REFUTED (finite-dim ⇒ pure-point ⇒ no a.c. density) + the surrogate REDUCES-TO-WALL F1.**
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Real

namespace ArkLib.ProximityGap.Frontier.RajchmanDensityPurePoint

/-! ## 1. On `H_η` the Koopman Fourier coefficients are identically `1` (the measure is `δ_1`). -/

/-- The candidate's Koopman autocorrelation on `H_η`, for a finite subgroup `H` of a finite group
`G` (standing for `μ_n ≤ F_p^*`) and a dilation element `g`:
`μ̂_V(k) = (1/#H)·#{x ∈ H : g^k x ∈ H}`. -/
noncomputable def koopmanFourierCoeff {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [DecidablePred (· ∈ H)] (g : G) (k : ℕ) : ℝ :=
  ((Finset.univ.filter (fun x : G => x ∈ H ∧ g ^ k * x ∈ H)).card : ℝ)
    / ((Finset.univ.filter (fun x : G => x ∈ H)).card : ℝ)

/-- **On `H_η`, `μ̂_V(k) = 1` for every `k`** (the orbit `H = μ_n` is `g`-closed when `g ∈ H`).
A measure all of whose Fourier coefficients equal `1` is the Dirac mass `δ_1`: a single atom, the
most non-Rajchman measure possible (`μ̂ ≡ 1` never decays).  So `1_{μ_n}` is `V`-invariant and the
cyclic subspace carries no information about `M(n)`.  (The passage from Fourier coefficients to the
measure `δ_1` is prose.) -/
theorem koopmanFourierCoeff_eq_one {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [DecidablePred (· ∈ H)] {g : G} (hg : g ∈ H) (k : ℕ) :
    koopmanFourierCoeff H g k = 1 := by
  unfold koopmanFourierCoeff
  have hfilt : (Finset.univ.filter (fun x : G => x ∈ H ∧ g ^ k * x ∈ H))
      = Finset.univ.filter (fun x : G => x ∈ H) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun h => ⟨h, H.mul_mem (H.pow_mem hg k) h⟩⟩
  rw [hfilt]
  have hpos : (0 : ℝ) < ((Finset.univ.filter (fun x : G => x ∈ H)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, by simp [H.one_mem]⟩
  exact div_self hpos.ne'

/-! ## 2. The finite Koopman spectral measure is purely atomic — no a.c. density exists. -/

/-- The spectral measure of `V` on `ℓ²(F_p)` is a finite sum of atomic weights `w₀,…,w_{p-1}`
(the squared projections onto the `p` eigenlines). We carry it as a function
`spectralWeight : Fin p → ℝ` with `weight j = ‖P_j ξ‖²`. The **total mass** is `Σ_j weight j`. -/
noncomputable def totalAtomicMass (p : ℕ) (spectralWeight : Fin p → ℝ) : ℝ :=
  ∑ j, spectralWeight j

/-- **The finite-dimensional Koopman spectral measure is purely atomic.** For a unitary `V` on the
`p`-dimensional space `ℓ²(F_p)`, the spectral measure is `Σ_{j} weight j · δ_{λ_j}`: its total mass
is exhausted by the `p` atomic weights, leaving **no** absolutely-continuous component.

**Placeholder (audit CW-B19-10):** the Lean statement only says that a family of weights summing to
`1` has `totalAtomicMass = 1`; the hypothesis is the conclusion after unfolding.  Nothing about the
operator `V` or its spectral measure is formalized. -/
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
norm.

**Placeholder (audit CW-B19-10):** the Lean statement is linear arithmetic on the encoded
decomposition `totalAtomicMass + acMass = 1`; it does not derive that decomposition from `V`. -/
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
only well-posed form, IS the energy ladder — no new lever.

**Placeholder (audit CW-DL08a-03):** this is `rfl` on the definition of `wienerDensityMass`; the
Parseval identity `Σ_{b≠0}|η_b|^{2r} = p·E_r − n^{2r}` is prose, not proved here. -/
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

Lean content: only the conjunction of the two placeholders (`acDensity_does_not_bound_M` and
`density_surrogate_is_energy`); the spectral argument above is prose. -/
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
