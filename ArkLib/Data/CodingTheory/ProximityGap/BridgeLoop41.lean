/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 41 (BRIDGE) — verifying the unconditional core of Chai–Fan 2026/861 (Action–Orbit Theorem)

A June-2026 read of Chai–Fan eprint 2026/861 ("Action–Orbit FRI Soundness Above the Johnson
Radius") shows its prize-relevant soundness claim (Conjecture 1.1) is **conditional on two
conjectures**: Q1 (Conjecture 4.12, an explicit number-theoretic non-vanishing, rigorous only at
`d ∈ {4,8}`) and Q2 (Conjecture 7.1, *sparse-worst-case dominance*, only **empirically** verified at
deployment scale `(32,8)`). So the paper does **not** resolve the prize.

What it *does* contribute unconditionally is **Theorem 2.1 (Action–Orbit)** — the authors say so:
"the question, not the proof, is the contribution." This file verifies that core is genuinely sound
(loop step 5: prove the survivor), confirming the mechanism is rigorous and isolating **all**
conditionality into Q1/Q2 (handled separately in `CandidateProofLoop40.lean`).

Theorem 2.1: on a cyclic FRI evaluation domain `Lₙ = ⟨ω⟩`, for the two-monomial pencil
`hα(z) = z^a + α·z^b` and any `μ ∈ Lₙ`,

    dist(hα, RSₖ(Lₙ)) = dist(h_{α·μ^{b−a}}, RSₖ(Lₙ)),

so the *bad-α set* `{α : dist(hα, RSₖ) ≤ τ}` is closed under multiplication by `⟨ω^{b−a}⟩` — a union
of orbits. The proof chains five elementary facts; the only pencil-specific computation is the
**algebraic factoring** (step iv):

    hα(μz) = (μz)^a + α(μz)^b = μ^a · (z^a + (α·μ^{b−a})·z^b) = μ^a · h_{α·μ^{b−a}}(z).

This file proves, sorry-free and axiom-clean:

* `pencil_substitution` — the algebraic factoring (iv) as a `CommRing` identity (the genuine
  pencil-specific input). This is where any error in Theorem 2.1 would have to hide; it does not.
* `dist_orbit_invariant` / `bad_closed_under_orbit` — the abstract orbit-closure consequence: if a
  distance functional `D` is invariant under multiplication by `s` (the input that steps i, ii, v
  — Hamming permutation-invariance and `RSₖ`-linearity — supply for the RS distance), then `D` is
  constant on `⟨s⟩`-orbits and the bad set `{α : D α ≤ τ}` is closed under the whole cyclic orbit.

Together these are a faithful verified rendering of the unconditional mechanism of Theorem 2.1. The
remaining steps (i),(ii),(v) are standard (permutation-invariance of Hamming distance, linearity of
`RSₖ`) and enter as the hypothesis `hinv`. See `DISPROOF_LOG.md` (Loop41).
-/

namespace ArkLib.ProximityGap.BridgeLoop41

/-- **Action–Orbit step (iv): the pencil algebraic factoring.** For the two-monomial pencil
`hα(z) = z^a + α·z^b` over any commutative ring, evaluating at `μz` factors out `μ^a` and shifts the
coefficient `α ↦ α·μ^{b−a}`:

    (μ·z)^a + α·(μ·z)^b = μ^a · (z^a + (α·μ^{b−a})·z^b)   (for a ≤ b).

This is the single pencil-specific computation in Theorem 2.1's five-line proof. -/
theorem pencil_substitution {F : Type*} [CommRing F] (z μ α : F) {a b : ℕ} (hab : a ≤ b) :
    (μ * z) ^ a + α * (μ * z) ^ b = μ ^ a * (z ^ a + α * μ ^ (b - a) * z ^ b) := by
  have hμ : μ ^ a * μ ^ (b - a) = μ ^ b := by
    rw [← pow_add, Nat.add_sub_cancel' hab]
  rw [mul_pow, mul_pow, ← hμ]
  ring

/-- **Orbit invariance of the distance functional.** If `D` is invariant under multiplication by `s`
(`D (s * x) = D x` for all `x`), then it is invariant under every power `s^n` — i.e. `D` is
constant on `⟨s⟩`-orbits. This is the abstract content steps i, ii, v supply for the RS distance
(Hamming permutation-invariance under `z ↦ μz`, plus `RSₖ`-linearity). -/
theorem dist_orbit_invariant {F : Type*} [Monoid F]
    (D : F → ℝ) (s : F) (hinv : ∀ x, D (s * x) = D x) (α : F) :
    ∀ n : ℕ, D (s ^ n * α) = D α := by
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, hinv]; exact ih

/-- **The bad-α set is a union of `⟨s⟩`-orbits (Theorem 2.1's conclusion).** If `D` is invariant
under `×s` and `α` is bad (`D α ≤ τ`), then every orbit point `s^n · α` is bad too. So the bad set
`{α : D α ≤ τ}` is closed under the cyclic orbit `⟨s⟩` — exactly "the bad-α set is a union of
`⟨ω^{b−a}⟩`-orbits", with `s = ω^{b−a}`. -/
theorem bad_closed_under_orbit {F : Type*} [Monoid F]
    (D : F → ℝ) (τ : ℝ) (s : F) (hinv : ∀ x, D (s * x) = D x)
    {α : F} (hbad : D α ≤ τ) (n : ℕ) : D (s ^ n * α) ≤ τ := by
  rw [dist_orbit_invariant D s hinv α n]; exact hbad

end ArkLib.ProximityGap.BridgeLoop41

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeLoop41.pencil_substitution
#print axioms ArkLib.ProximityGap.BridgeLoop41.dist_orbit_invariant
#print axioms ArkLib.ProximityGap.BridgeLoop41.bad_closed_under_orbit
