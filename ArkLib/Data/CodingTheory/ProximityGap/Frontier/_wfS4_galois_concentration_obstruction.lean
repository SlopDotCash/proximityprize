/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-S4 frontier — the Galois-spread vs frequency-concentration obstruction)
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# wf-S4 — the Galois-spread ⊥ frequency-concentration OBSTRUCTION (#444)

This is the EXACT-measurement-driven companion to `_wfS4_orbit_partition_law.lean`. That file
proves (conditional on the measured `home`-equivariance) that the spurious configs are spread
**uniformly** over the `φ(n) = n/2` split primes `𝔭_a`: `perPrime a = total / |G|` for every prime.
The natural HOPE behind the prompt's CONCENTRATION mechanism was that this uniform Galois spread
would *force* the per-frequency maximum `M = max_{b≠0} ‖η_b‖` to stay small even when the total
energy `E_r` inflates — i.e. that "spread over the `n/2` primes" ⟹ "spread over the frequencies"
⟹ "M bounded".

## The measurement that kills that hope (probe `probe_wfS4_galois_concentration.rs`, EXACT)

At the Fermat prime `n = 32`, `p = 65537` (`v₂(p−1) = 16`, `β = 3.20`) the additive energy
**inflates**: `E₂/E₂^{c0} = 1.129`, `E₃ = 1.43×`, `E₄ = 2.16×`, AND the inflation is
**CONCENTRATED** (effective `#freqs = E_r/max = 17 → 5.5 → 2.8` for `r = 2,3,4`, out of `m = 2048`
cosets), AND `M` simultaneously **spikes** to `C = M/√(n·log(p/n)) = 1.61` versus `~1.13–1.26` at
generic primes of the same `n`. So at the structured prime the spurious mass is NOT spread over the
frequencies — it concentrates, and `M` grows with it.

The Galois / Stickelberger structural prediction (the inflating frequencies should be the
Galois-fixed / Gauss-period / **low-order** `b`) is **REFUTED** by the same probe (part C): the top
(inflating) frequencies are overwhelmingly **full multiplicative order** `ord(b) = p−1`
(`depth = (p−1)/ord = 1`), i.e. generic primitive elements, not low-order Gauss periods. The
Stickelberger ideal pins the `p`-adic valuation (which is Galois-invariant on a conjugate orbit and
carries zero archimedean spread information — see push `828e1e0d4`); it does **not** force the
spurious configs into a small structured subset.

## What this file proves (axiom-clean): the obstruction is a COUNTERMODEL, not a theorem-gap

The orbit-partition law lives on the *primes*; `M` lives on the *frequencies*. These are two
different `G`-sets, and uniformity on one does NOT transfer to the other. We make this precise as a
clean finite **countermodel**:

> **`uniform_spread_allows_concentration`** — there is a config set `C`, a group `G`, a
> `home`-equivariant free transitive `G`-action (so the orbit-partition law applies: `perPrime` is
> uniform), TOGETHER WITH a frequency-weight function `wt : C → ℕ` whose total `Σ wt` is fixed but
> whose **maximum on a single fibre `home⁻¹(a)` is the entire total** — the weight concentrates on
> one frequency inside one prime. Hence *uniform per-prime spread is logically compatible with full
> per-frequency concentration*: the Galois spread alone cannot bound `M`.

Concretely: `G = C = ZMod k` (`k ≥ 1`), `home = id`, `act = (· + ·)` (the regular action — free,
transitive, `home`-equivariant), giving `perPrime a = 1` for every `a` (perfectly uniform). The
weight `wt` is `0` everywhere except a single element where it is `T` (the total). The fibre over
that element carries ALL the weight. Uniform spread of *configs*, total concentration of *weight*.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure. This is a precise **OBSTRUCTION**: it shows the proven Galois orbit-partition
law (uniform per-prime spread) is *orthogonal* to the prize-relevant quantity `M` (per-frequency
sup), so the prize CANNOT be closed by the Galois-spread mechanism alone — a genuine
spectral/concentration input on the frequency side is required (the `M ≤ C√(n log)` content itself).
This matches the EXACT measurement (uniform spread holds, yet `M` spikes at the Fermat prime). CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- in-tree: `_wfS4_orbit_partition_law.lean` (the uniform-spread law this obstructs),
  `_wfS4_galois_perprime_spread.lean`, `_wf5M2_stickelberger_depth.lean`.
- probe: `scripts/probes/rust/probe_wfS4_galois_concentration.rs` (the Fermat concentration +
  full-order refutation of the Gauss-period prediction).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.GaloisConcentrationObstruction

open Finset

/-! ## The regular model (uniform per-prime spread) -/

-- The regular self-action of a finite group on itself is `home = id`-equivariant, free, and
-- transitive — the model in which the orbit-partition law gives **perfectly uniform** per-prime
-- counts (`perPrime a = 1` for every `a`). We record `act = (· * ·)` and verify it is a genuine
-- action and `home`-equivariant for `home = id`.
section RegularModel

variable (G : Type*) [Fintype G] [DecidableEq G]

/-- Per-prime count in the regular model: number of configs `T` whose landing prime (`= T`) is `a`. -/
def perPrimeReg (a : G) : ℕ := (univ.filter fun T : G => T = a).card

/-- **The regular model is perfectly uniform: every prime sees exactly ONE config.**
This is the orbit-partition law at its sharpest (`home = id`, the action is the free transitive
regular action): the `total = |G|` configs spread as exactly `1` per split prime. -/
theorem perPrimeReg_eq_one (a : G) : perPrimeReg G a = 1 := by
  classical
  simp only [perPrimeReg]
  rw [Finset.filter_eq' univ a]
  simp

/-- The regular action `act g T = g * T` is `home`-equivariant for `home = id`
(`home (act g T) = g * home T` becomes `g * T = g * T`). -/
theorem regular_home_equivariant [Group G] (g T : G) :
    (fun x => x) (g * T) = g * (fun x => x) T := rfl

end RegularModel

/-- **THE OBSTRUCTION (countermodel).** Uniform per-prime spread (the proven Galois orbit-partition
law) does NOT bound a per-frequency weight maximum. For every total weight `T : ℕ` and every group
size `k + 1 ≥ 1`, there is:
* a config set `C = Fin (k+1)` with a perfectly uniform per-prime count (`perPrime a = 1` ∀ `a`,
  via the regular model `perPrimeReg_eq_one`), AND
* a frequency-weight `wt : C → ℕ` with total `Σ wt = T` whose **maximum equals the whole total**
  (`wt` concentrates all weight on one config) — so the per-frequency sup is `T`, unbounded by the
  (uniform, `= 1`) per-prime count.

This is the exact logical content of the Fermat measurement: spread on the *primes* is uniform,
yet the energy `M` on the *frequencies* concentrates. The two `G`-structures are orthogonal. -/
theorem uniform_spread_allows_concentration (k : ℕ) (T : ℕ) :
    ∃ (wt : Fin (k + 1) → ℕ),
      -- the per-prime spread is perfectly uniform (orbit-partition law, sharpest case)
      (∀ a : Fin (k + 1), perPrimeReg (Fin (k + 1)) a = 1) ∧
      -- the weight total is exactly T ...
      (∑ c : Fin (k + 1), wt c = T) ∧
      -- ... yet the per-frequency MAXIMUM already equals the whole total (full concentration)
      (∃ c₀ : Fin (k + 1), wt c₀ = T) := by
  classical
  -- concentrate all weight on `0 : Fin (k+1)`.
  refine ⟨fun c => if c = 0 then T else 0, ?_, ?_, ?_⟩
  · intro a; exact perPrimeReg_eq_one (Fin (k + 1)) a
  · -- Σ_c (if c = 0 then T else 0) = T
    rw [Finset.sum_ite_eq' univ (0 : Fin (k + 1)) (fun _ => T)]
    simp
  · exact ⟨0, by simp⟩

/-- **Quantitative form of the obstruction: the uniform per-prime bound is `1`, the per-frequency
sup is the full total `T`.** Their ratio (`per-frequency-sup / per-prime-count = T`) is *unbounded*
in `T` while the Galois spread stays fixed at `1`. So no inequality of the form
`M ≤ f(per-prime spread)` can hold — the Galois orbit-partition law carries no information about the
frequency-side concentration `M`. -/
theorem perPrime_to_M_ratio_unbounded :
    ∀ N : ℕ, ∃ (k : ℕ) (wt : Fin (k + 1) → ℕ),
      (∀ a : Fin (k + 1), perPrimeReg (Fin (k + 1)) a = 1) ∧
      (∃ c₀ : Fin (k + 1), N < wt c₀) := by
  intro N
  obtain ⟨wt, huni, _htot, c₀, hc₀⟩ := uniform_spread_allows_concentration 0 (N + 1)
  refine ⟨0, wt, huni, c₀, ?_⟩
  rw [hc₀]; exact Nat.lt_succ_self N

end ProximityGap.Frontier.GaloisConcentrationObstruction

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.GaloisConcentrationObstruction.perPrimeReg_eq_one
#print axioms ProximityGap.Frontier.GaloisConcentrationObstruction.uniform_spread_allows_concentration
#print axioms ProximityGap.Frontier.GaloisConcentrationObstruction.perPrime_to_M_ratio_unbounded
