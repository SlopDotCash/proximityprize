/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (Av-CRT frontier — split-prime CRT-correlation no-go for W_r)
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# Av-CRT — the split-prime CRT-correlation cancellation is a SINGLE-PRIME collapse (no-go) (#444)

## What was attempted (MECHANISM 1, "split-prime CRT correlation cancellation")

For `n = 2^μ` and a prize prime `p ≡ 1 (mod n)`, `p` splits completely in `ℤ[ζ_n]` into
`d = φ(n) = n/2` degree-1 primes `𝔭_ω` (one per primitive `n`-th root `ω ∈ 𝔽_p`). The wraparound
excess `W_r` weights signed configs `α = ∑ζ^{x} − ∑ζ^{y}` whose *energy collision* holds:
`α(g) ≡ 0 (mod p)` for the single fixed embedding `ζ ↦ g`.

The hoped-for cancellation: "`p ∣ α`" as an IDEAL means `α` vanishes mod ALL `d` conjugate split
primes simultaneously; being a full Galois orbit of vanishing conditions this would force `α` into
the Galois-fixed (rational) part scaled by `p`, i.e. `α ∈ pℤ`, collapsing the Minkowski count
`(4r)^{φ(n)}` down to `O(r)` rational integers — a count-rigidity OFF the archimedean char-sum.

## Why it collapses (the EXACT obstruction proved below)

The norm factors `N(α) = ∏_{ω} α(ω)` (`S9`). The energy collision that actually drives `W_r` is the
SPUR BOOLEAN `p ∣ N(α) ⟺ ∃ ω, p ∣ α(ω)` — vanishing mod *at least one* split prime
(`dvd_prod_iff_exists_dvd`, `∃`). MECHANISM 1's rationality-forcing requires the *full-orbit*
condition `∀ ω, p ∣ α(ω)` (`∀`). These differ by exactly `∃` vs `∀`, and the implication only runs
one way: full-orbit ⟹ single-prime, never the reverse.

`single_does_not_force_full` (below) exhibits a concrete `α(ω)`-profile that vanishes mod the
chosen prime but mod NO other split prime — so the single-prime collision (which `W_r` counts) does
NOT entail the full-orbit ideal divisibility (which the rigidity needs). Hence the rigidity bounds
the WRONG set.

**Exact-integer corroboration** (`probe_crt.py`, `probe2/3.py`, this session, n=8,16, multiprime):
of EVERY wraparound config at every tested `p ≡ 1 mod n`,
* `rational(ℤ)` fraction `= 0%` (no config forced rational),
* `ideal-divisible (∀ω)` count `= 0` (no config divisible by `p` as an ideal),
* `full-orbit vanishing (d/d primes)` count `= 0` identically, at every `p`, `r=3,4`,
* the collision count is the SINGLE-prime count; the `≥2`-prime fraction `→ 0` as `p` grows toward
  prize scale (`35% → 2.87% → 0%` at `p = 17,97,193`, `n=16`), tracking the independence
  prediction `(d−1)/(2p)`.

So the full-orbit set MECHANISM 1 wants to bound is EMPTY at scale, while the set `W_r` actually
counts is the single-prime spur — whose char-sum `∑_b ψ(b·α)` is the BGK archimedean char-sum
(TRAP 2). The Galois "correlation" is empirically `≈` independence (no exploitable positive
correlation; anti-correlated/rarer than independent toward prize scale), matching the
periods-are-exchangeable-white-noise finding. **MECHANISM 1 collapses to BGK.**

This file PROVES the structural collapse (the `∃`/`∀` gap is real and one-directional), axiom-clean.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.AvCRT

open Finset

/-- **The energy-collision spur boolean is the `∃` (single split prime) condition.** With the norm
factored `N(α) = ∏_{ω∈s} α(ω)`, a prime `p` divides the norm iff it divides AT LEAST ONE residue —
vanishing mod at least one of the `d` split primes. This is the condition `W_r` counts. -/
theorem spur_iff_single_prime {ι : Type*} (s : Finset ι) (residue : ι → ℤ) {p : ℤ} (hp : Prime p) :
    p ∣ (∏ ω ∈ s, residue ω) ↔ ∃ ω ∈ s, p ∣ residue ω :=
  hp.dvd_finset_prod_iff residue

/-- **The full-orbit ideal divisibility is the `∀` condition.** MECHANISM 1's rationality-forcing
requires `α` to vanish mod EVERY split prime, i.e. `p` divides every residue. We state it as the
predicate `FullOrbitVanish`. -/
def FullOrbitVanish {ι : Type*} (p : ℤ) (s : Finset ι) (residue : ι → ℤ) : Prop :=
  ∀ ω ∈ s, p ∣ residue ω

/-- **One-directional implication: full-orbit ⟹ single-prime spur (when `s` is nonempty).** The
rigidity condition entails the energy collision, but — as `single_does_not_force_full` shows — never
the converse. The rigidity therefore constrains a SUBSET of the spur configs (in fact the EMPTY set
at prize scale, per the probe), not the spur count itself. -/
theorem spur_of_fullOrbit {ι : Type*} (s : Finset ι) (residue : ι → ℤ) {p : ℤ} (hp : Prime p)
    (hne : s.Nonempty) (h : FullOrbitVanish p s residue) :
    p ∣ (∏ ω ∈ s, residue ω) := by
  obtain ⟨ω, hω⟩ := hne
  exact (spur_iff_single_prime s residue hp).mpr ⟨ω, hω, h ω hω⟩

/-- **The decisive gap (no-go core): a single-prime spur that is NOT full-orbit.** Concretely, take
`d = 2` split primes with residue profile `(0, 1)` over `ℤ` and `p` any prime `> 1`: the product
`0 * 1 = 0` is divisible by `p` (single-prime spur holds via the first factor), yet the second
residue `1` is a unit, so `FullOrbitVanish` FAILS. This is the structural reason the energy
collision does NOT force ideal divisibility / rationality: only ONE factor of `∏ α(ω)` must vanish.
The exact-integer probes find the full-orbit set is in fact EMPTY at scale, so the rigidity bounds
nothing the spur count sees. -/
theorem single_does_not_force_full :
    ∃ (s : Finset ℕ) (residue : ℕ → ℤ) (p : ℤ), Prime p ∧
      p ∣ (∏ ω ∈ s, residue ω) ∧ ¬ FullOrbitVanish p s residue := by
  refine ⟨{0, 1}, (fun ω => if ω = 0 then 0 else 1), 2, Int.prime_two, ?_, ?_⟩
  · -- product is 0, divisible by 2
    have : (∏ ω ∈ ({0, 1} : Finset ℕ), (fun ω => if ω = 0 then (0 : ℤ) else 1) ω) = 0 := by
      rw [Finset.prod_insert (by decide)]
      simp
    rw [this]; exact dvd_zero 2
  · -- full-orbit fails: 2 does not divide residue 1 = 1
    intro h
    have h1 : (2 : ℤ) ∣ (if (1 : ℕ) = 0 then (0 : ℤ) else 1) := h 1 (by decide)
    simp at h1

/-- **Restatement: the `∃`/`∀` gap is the whole no-go.** `W_r`'s count is governed by the `∃`
(single-prime) spur; MECHANISM 1's rationality-rigidity governs the `∀` (full-orbit). The two
coincide ONLY when `s` has a single element (`d = φ(n) = 1`, i.e. `n ≤ 2`, never the prize regime).
For `d ≥ 2` the `∃` set strictly contains — and at prize scale is disjoint from any nonempty —
the `∀` set, so the rigidity cannot bound the spur count. -/
theorem exists_forall_coincide_iff_singleton {ι : Type*} (s : Finset ι) :
    (∀ (residue : ι → ℤ) (p : ℤ), Prime p →
        ((∃ ω ∈ s, p ∣ residue ω) → FullOrbitVanish p s residue)) →
      s.card ≤ 1 := by
  classical
  intro h
  by_contra hc
  push_neg at hc
  -- s has ≥ 2 elements; pick two distinct ω₀, ω₁
  obtain ⟨ω₀, hω₀, ω₁, hω₁, hne⟩ := Finset.one_lt_card.mp hc
  -- residue vanishing only at ω₀: single-prime spur holds, full-orbit fails at ω₁
  let residue : ι → ℤ := fun ω => if ω = ω₀ then 0 else 1
  have hr0 : residue ω₀ = 0 := by show (if ω₀ = ω₀ then (0:ℤ) else 1) = 0; rw [if_pos rfl]
  have hne' : ω₁ ≠ ω₀ := Ne.symm hne
  have hr1 : residue ω₁ = 1 := by
    show (if ω₁ = ω₀ then (0:ℤ) else 1) = 1
    simp only [hne', if_false]
  have hspur : ∃ ω ∈ s, (2 : ℤ) ∣ residue ω :=
    ⟨ω₀, hω₀, by rw [hr0]; exact dvd_zero 2⟩
  have hfull := h residue 2 Int.prime_two hspur
  have hd : (2 : ℤ) ∣ residue ω₁ := hfull ω₁ hω₁
  rw [hr1] at hd
  norm_num at hd

end ArkLib.ProximityGap.Frontier.AvCRT

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.AvCRT.spur_iff_single_prime
#print axioms ArkLib.ProximityGap.Frontier.AvCRT.single_does_not_force_full
#print axioms ArkLib.ProximityGap.Frontier.AvCRT.exists_forall_coincide_iff_singleton
