/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# F1: the Gaussian moment step-law telescopes to the sub-Gaussian energy bound (#444, lane wf-F1)

## The lead (sub-Gaussian / hypercontractive structure of the nonprincipal periods)

For `G = μ_n` (`n = 2^μ`, `n | p-1`, `q = p = n^β`), write the **Gaussian-normalised raw moment**
`M_{2r} := (1/m)·∑_{cosets} η^{2r}` of the nonprincipal period vector (`m = (q-1)/n` cosets, each of
size `n`). Lane F1's exact numerics (`scripts/probes/rust/wf6F1_subgaussian_psi2.rs`,
`wf6F1_gaussian_step_ratio.rs`, exact integer/cos period sums over `F_p`, `β ≈ 4..5.3`, depth
`r ≈ 1.5·ln q`, `n = 16..512`) measured:

* the moment `ψ₂`-constant `sup_r (M_{2r}/[(2r-1)‼ n^r])^{1/r} = 1.0000(±4·10⁻⁴)` for ALL `n`,
  attained at `r = 1` (Parseval), strictly `< 1` for `r ≥ 2` (genuinely sub-Gaussian higher moments);
* the MGF variance-proxy `c = sup_λ 2·log E[e^{λη}]/(λ²n) = 1.0000` — periods are sub-Gaussian with
  variance proxy exactly `n` (the Gaussian value);
* the **step ratio** `ρ(r) := M_{2(r+1)}/(n·M_{2r})` satisfies `ρ(r) ≤ 2r+1` (the Gaussian step,
  `ρ(r)=2r+1` for `N(0,n)`) for ALL measured `r, n` in the prize regime `β ≳ 3.5`; the max of
  `ρ(r)/(2r+1)` is attained at `r=1` and equals `M_4/(3n·M_2) ≤ 0.99`.

Honest scope flag: the `r=1` cap / step-law is **β-conditional** — it holds robustly for `β ≳ 3.5`
(prize `β ≈ 5.27` at `n=2^30`, `q=2^158`) but is VIOLATED at small `β ≈ 2` (`wf6F1_beta_threshold.rs`:
`n=128, p=17921, β≈2.02` gives `maxR = 2.22 > R(1) = 0.89`). The prize regime is comfortably inside
the safe band; the small-`β` violation is documented, not swept under the rug.

## What this file proves (axiom-clean, pure-math telescope)

The key structural fact: the per-step **Gaussian step-law** `M_{2(r+1)} ≤ (2r+1)·s·M_{2r}` (variance
proxy `s`), together with the base `M_0 ≤ 1` (here `M_0 = 1` trivially / `M_2 ≤ s`), **telescopes**
to the full sub-Gaussian even-moment bound `M_{2r} ≤ (2r-1)‼·s^r` for ALL `r` — exactly the shape of
`GaussianEnergyBound`. This converts the open energy crux (a bound on every `E_r` simultaneously) into
a **single per-step inequality** `ρ(r) ≤ 2r+1`, the natural hypercontractive/log-Sobolev object
(`ρ` is a discrete cumulant ratio). The reduction is the F1 deliverable; the step-law itself is the
remaining (β-conditional, empirically true) analytic input.

* `MomentSeq` / `GaussianStepLaw` — the abstract moment sequence and the named per-step hypothesis.
* `gaussian_moment_bound_of_stepLaw` — **THE TELESCOPE** (axiom-clean): step-law + base ⟹
  `M(r) ≤ (2r-1)‼·s^r` for all `r`.
* `gaussianEnergyBound_of_rEnergy_stepLaw` — wires the telescope to the in-tree `GaussianEnergyBound`
  (so it feeds `GaussPeriodMomentBound.eta_pow_le_of_gaussianEnergyBound` → the prize per-frequency
  bound). The step-law on `rEnergy`/`q` is the named open input, in its **local per-step** form.

This is the project modularity convention (§6): the open core is now ONE local Prop `GaussianStepLaw`
(a single cumulant ratio bound), and `gaussian_moment_bound_of_stepLaw` is its proven consumer.
-/

namespace ArkLib.ProximityGap.Frontier.WF6F1

open Nat

/-! ## The abstract moment sequence and the Gaussian step-law -/

/-- The per-step **Gaussian step-law** for a nonnegative moment sequence `M : ℕ → ℝ` with variance
proxy `s ≥ 0`: each even-moment step grows by at most the Gaussian factor `(2r+1)·s`,
`M(r+1) ≤ (2r+1)·s·M(r)`. For a real Gaussian `N(0,s)` this is an *equality* (`M(r)=(2r-1)‼ s^r`); the
hypothesis asserts the periods are *sub*-Gaussian step-wise. This is the F1 lead in its local form. -/
def GaussianStepLaw (M : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ r : ℕ, M (r + 1) ≤ (2 * r + 1 : ℝ) * s * M r

/-- **THE TELESCOPE.** A nonnegative moment sequence obeying the Gaussian step-law from base
`M 0 ≤ 1` satisfies the full sub-Gaussian even-moment bound `M r ≤ (2r-1)‼·s^r` for every `r`.
Pure induction collapsing `(2r+1)·(2r-1)‼ = (2r+1)‼ = (2(r+1)-1)‼`. Axiom-clean. -/
theorem gaussian_moment_bound_of_stepLaw {M : ℕ → ℝ} {s : ℝ}
    (hs : 0 ≤ s) (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1)
    (hstep : GaussianStepLaw M s) :
    ∀ r : ℕ, M r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * s ^ r := by
  intro r
  induction r with
  | zero =>
    -- (2·0-1)‼ = 0‼ = 1 (ℕ truncated sub: 2*0-1=0), s^0 = 1, so RHS = 1.
    simpa [Nat.doubleFactorial] using hbase
  | succ k ih =>
    -- step:  M (k+1) ≤ (2k+1)·s·M k ≤ (2k+1)·s·[(2k-1)‼ s^k] = (2k+1)‼ · s^{k+1}
    have hstep_k : M (k + 1) ≤ (2 * k + 1 : ℝ) * s * M k := hstep k
    have hfac_nn : (0 : ℝ) ≤ (2 * k + 1 : ℝ) * s := by positivity
    have hchain : M (k + 1)
        ≤ (2 * k + 1 : ℝ) * s * ((Nat.doubleFactorial (2 * k - 1) : ℝ) * s ^ k) :=
      le_trans hstep_k (mul_le_mul_of_nonneg_left ih hfac_nn)
    -- collapse the RHS to (2(k+1)-1)‼ · s^{k+1}
    have hdf : (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ)
        = (2 * k + 1 : ℝ) * (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
      cases k with
      | zero => norm_num [Nat.doubleFactorial]
      | succ j =>
        -- 2*(k+1)-1 = 2*j+3 = (2*j+1)+2,  2*k-1 = 2*j+1
        have h1 : 2 * (j + 1 + 1) - 1 = (2 * j + 1) + 2 := by omega
        have h2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
        rw [h1, h2, Nat.doubleFactorial_add_two]
        push_cast
        ring
    calc M (k + 1)
        ≤ (2 * k + 1 : ℝ) * s * ((Nat.doubleFactorial (2 * k - 1) : ℝ) * s ^ k) := hchain
      _ = ((2 * k + 1 : ℝ) * (Nat.doubleFactorial (2 * k - 1) : ℝ)) * s ^ (k + 1) := by ring
      _ = (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) * s ^ (k + 1) := by rw [hdf]

/-! ## Wiring the telescope to the in-tree `GaussianEnergyBound` -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open ArkLib.ProximityGap.SubgroupGaussSumMoment in
/-- **The step-law on the additive-energy sequence discharges `GaussianEnergyBound` at every order.**
Let `M r := E_r(G) = rEnergy G r` (nonnegative, `E_0 = 1`). If the energy obeys the per-step Gaussian
law `E_{r+1} ≤ (2r+1)·n·E_r` (variance proxy `s = |G| = n`), then `E_r ≤ (2r-1)‼·n^r` for ALL `r` —
i.e. `GaussianEnergyBound G r` holds for every `r`, which feeds the moment-method per-frequency bound
`‖η_b‖^{2r} ≤ q·(2r-1)‼·n^r` (`GaussPeriodMomentBound.eta_pow_le_of_gaussianEnergyBound`).

This is the F1 reduction: the open energy crux (a bound on every `E_r`) becomes ONE local Prop —
the Gaussian step-law `ρ(r) = E_{r+1}/(n·E_r) ≤ 2r+1`, measured `≤ 0.99·(2r+1)` in the prize regime. -/
theorem gaussianEnergyBound_of_rEnergy_stepLaw (G : Finset F)
    (hbase : (rEnergy G 0 : ℝ) ≤ 1)
    (hstep : ∀ r : ℕ, (rEnergy G (r + 1) : ℝ)
        ≤ (2 * r + 1 : ℝ) * (G.card : ℝ) * (rEnergy G r : ℝ)) :
    ∀ r : ℕ, ArkLib.ProximityGap.GaussPeriodMomentBound.GaussianEnergyBound G r := by
  have hnn : ∀ r : ℕ, (0 : ℝ) ≤ (rEnergy G r : ℝ) := fun r => by positivity
  have hcard : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  have := gaussian_moment_bound_of_stepLaw (M := fun r => (rEnergy G r : ℝ))
    (s := (G.card : ℝ)) hcard hnn hbase hstep
  intro r
  exact this r

end ArkLib.ProximityGap.Frontier.WF6F1

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WF6F1.gaussian_moment_bound_of_stepLaw
#print axioms ArkLib.ProximityGap.Frontier.WF6F1.gaussianEnergyBound_of_rEnergy_stepLaw
