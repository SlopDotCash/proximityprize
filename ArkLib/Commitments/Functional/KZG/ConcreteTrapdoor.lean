/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import ArkLib.Commitments.Functional.KZG.Algebra

/-!
# Trapdoor recovery from concrete prime-order SRS elements

The discrete-logarithm construction is adapted from upstream ArkLib PR #655
(`783068782ce0d4186c02eeb385ae15d41701e9db`),
`ArkLib/Scratch/KzgVacuity/KzgVacuity.lean`, retaining its attribution. It shows why
unrestricted Lean functions on concrete group elements do not model efficient adversaries:
`Classical.choose` can recover the private exponent from the public verifier SRS leg.
This is an algebraic prerequisite for the PR's probability-one attacks, not a generic-group
security theorem or a completed native migration of its t-SDH/ARSDH game refutations.
-/

namespace ArkLibVacuity

section Dlog

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The choice-definable discrete logarithm base a nontrivial `g` in a prime-order group.
This is *not* an algorithm: it is `Exists.choose` applied to ArkLib's own
`Groups.exists_zmod_power_of_generator`. It is nevertheless a perfectly legal
inhabitant of `ZMod p`, and that is the whole point. -/
noncomputable def dlogOf {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1)
    (x : G) : ZMod p :=
  (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg
    (Groups.orderOf_eq_prime_of_ne_one g hg) x).choose

/-- `dlogOf` inverts exponentiation base a nontrivial element of a prime-order group. -/
lemma dlogOf_pow {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1) (a : ZMod p) :
    dlogOf (p := p) hg (g ^ a.val) = a := by
  have hord : orderOf g = p := Groups.orderOf_eq_prime_of_ne_one g hg
  have hspec : g ^ a.val = g ^ (dlogOf (p := p) hg (g ^ a.val)).val :=
    (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg hord
      (g ^ a.val)).choose_spec
  have hdiv : g ^ (dlogOf (p := p) hg (g ^ a.val) - a).val = 1 := by
    rw [← Groups.gpow_div_eq hord _ a, ← hspec, div_self']
  exact sub_eq_zero.mp (Groups.zmod_eq_zero_of_gpow_eq_one hord hdiv)

/-- The public verifier leg of the generated SRS determines the trapdoor. -/
lemma dlogOf_generate {G₁ G₂ : Type} [Group G₁] [Group G₂] [PrimeOrderWith G₂ p]
    (g₁ : G₁) {g₂ : G₂} (hg₂ : g₂ ≠ 1) (D : ℕ) (τ : ZMod p) :
    dlogOf hg₂ (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).2[1] = τ := by
  simpa [Groups.PowerSrs.generate, Groups.PowerSrs.tower] using dlogOf_pow hg₂ τ

end Dlog
end ArkLibVacuity
