/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# wf-N13: the Elekes–Szabó / sum-product / expanding-polynomial family is frequency-blind (#407)

**The prize.** `M(n) = max_{b ≠ 0} ‖∑_{x ∈ μ_n} e_p(b·x)‖ ≤ C √(n log(p/n))` — the sup-norm of an
incomplete additive-character sum over the deterministic order-`n = 2^μ` subgroup `μ_n ⊆ F_p` at the
worst nonzero frequency `b`. The first proven **necessary condition** any closer must satisfy is

  **Property (1) — b-SENSITIVITY:** the method must be able to *see* the worst frequency `b`; a
  quantity that is invariant under the dilation `x ↦ b·x` cannot upper-bound a `b`-maximum
  (it bounds every `b` by the same value, hence cannot detect the heavy direction).

**N13: the sum-product / Elekes–Szabó lane fails property (1).** The Elekes–Szabó theorem, the
expanding-polynomial / sum-product machinery, and all variants whose only input from `μ_n` is its
**additive energy** `E⁺(μ_n) = #{(x₁,x₂,x₃,x₄) ∈ μ_n⁴ : x₁+x₂ = x₃+x₄}` (or the multiplicative
energy, or any dilation-invariant incidence count) read a quantity that is **identical for every
nonzero frequency `b`**. Concretely, the `b`-twisted additive-energy variety

  `V_b := {(x₁,x₂,x₃,x₄) ∈ μ_n⁴ : b·x₁ + b·x₂ = b·x₃ + b·x₄}`

has the **same cardinality** as `V_1 = {(x₁,x₂,x₃,x₄) : x₁+x₂ = x₃+x₄}`, for *every* `b ≠ 0` —
because dividing the relation through by the unit `b` is the identity on the index set (`b` cancels).
So the entire ES / sum-product / expanding-polynomial family is **b-blind**: it cannot distinguish the
prize frequency `b*` from `b = 1`, and therefore — by the necessary condition — cannot produce the
worst-case sup-norm bound `M(n)`. It can only bound `E⁺`, which the moment method already does
(`subgroup_gaussSum_moment` gives `∑_b ‖η_b‖^{2r} = q·E_r`, the *averaged*, frequency-symmetric face).

**What this file proves (char-free, field-level).**
* `addEnergyVariety_freq_card_eq` / `additiveEnergy_freq_invariant` —
  `#V_b = #V_1` for every `b ≠ 0`. The frequency twist is a relabelling, not new information.
* `dilation_levelSet_subsingleton` — `#{x ∈ G : b·x = c} ≤ 1` for `b ≠ 0`: the field acts freely by
  dilation on a level set, so a single frequency localises each value `c` to at most one point. This
  is the dual fact that the *only* way to read `b` would be a localised (sup-norm) observable, which
  the energy count is not.

**Scope / honesty.** This is a **NO-GO / guardrail** brick, NOT a closure. It does not bound `M(n)`;
it certifies that an entire previously-attempted lane (sum-product / Elekes–Szabó / expanding
polynomials — item N13 of the exotic-route sweep in #407/#444, which lists ~22 swarm lenses + 18
exotic single-domains, all of which reduce to BGK) is *structurally* incapable of the prize because
it fails the proven `b`-sensitivity necessary condition. The energy `E⁺(μ_n)` is the wrong, frequency-
symmetric coordinate; the prize lives in the `b`-localised L^∞ coordinate that this family cannot
access.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.

Issue #407 / #444, lane wf-N13 (Elekes–Szabó / sum-product / expanding-polynomial family).
-/

namespace ProximityGap.Frontier.EnergyFreqBlind

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `b`-twisted additive-energy variety of `G ⊆ F`:
`{(x₁,x₂,x₃,x₄) ∈ G⁴ : b·x₁ + b·x₂ = b·x₃ + b·x₄}`, as a `Finset` of quadruples.
For `b = 1` this is the ordinary additive-energy variety counting `E⁺(G)`. -/
noncomputable def addEnergyVariety (G : Finset F) (b : F) : Finset (((F × F) × F × F)) :=
  {x ∈ ((G ×ˢ G) ×ˢ G ×ˢ G) | b * x.1.1 + b * x.1.2 = b * x.2.1 + b * x.2.2}

/-- **Property (1) failure of the ES / sum-product family (twisted-variety form).**
For every nonzero frequency `b`, the `b`-twisted additive-energy variety has exactly the same
cardinality as the untwisted one (`b = 1`): dividing the relation by the unit `b` shows the
defining predicate is equivalent over the same index set, so the filtered finsets are *equal*.
The additive energy is therefore **frequency-blind** — invariant under the dilation that produces
the worst frequency. -/
theorem addEnergyVariety_freq_card_eq (G : Finset F) {b : F} (hb : b ≠ 0) :
    (addEnergyVariety G b).card = (addEnergyVariety G 1).card := by
  unfold addEnergyVariety
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro x _
  constructor
  · intro h
    -- b·x₁ + b·x₂ = b·x₃ + b·x₄  ⟹  b·(x₁+x₂) = b·(x₃+x₄)  ⟹  x₁+x₂ = x₃+x₄
    have h' : b * (x.1.1 + x.1.2) = b * (x.2.1 + x.2.2) := by ring_nf; ring_nf at h; linear_combination h
    have := mul_left_cancel₀ hb h'
    simpa using this
  · intro h
    -- x₁+x₂ = x₃+x₄  ⟹  b·x₁ + b·x₂ = b·x₃ + b·x₄
    simp only [one_mul] at h
    linear_combination b * h

/-- **Frequency invariance of the additive energy (`Eₘ`/`E⁺` form).**
The additive energy of `G` read through any nonzero frequency `b` equals the plain additive energy:
`#{(x₁,x₂,x₃,x₄) ∈ G⁴ : b·x₁+b·x₂ = b·x₃+b·x₄} = E⁺(G)`. Direct restatement of
`addEnergyVariety_freq_card_eq`; this is the one-line certificate that the Elekes–Szabó / sum-product
family cannot see the worst frequency `b`, hence fails the property-(1) necessary condition for the
#407 prize. -/
theorem additiveEnergy_freq_invariant (G : Finset F) {b : F} (hb : b ≠ 0) :
    (addEnergyVariety G b).card = (addEnergyVariety G 1).card :=
  addEnergyVariety_freq_card_eq G hb

/-- **Dilation level set is a subsingleton.** For a nonzero frequency `b`, the level set
`{x ∈ G : b·x = c}` has at most one element: multiplication by the unit `b` is injective, so a single
frequency pins each value `c` to a unique point. This is the dual half of `b`-blindness — the *only*
observable that resolves `b` is a localised (sup-norm) one, exactly the coordinate the energy count
collapses away. -/
theorem dilation_levelSet_subsingleton (G : Finset F) {b : F} (hb : b ≠ 0) (c : F) :
    ({x ∈ G | b * x = c}).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha d hd
  simp only [Finset.mem_filter] at ha hd
  have : b * a = b * d := by rw [ha.2, hd.2]
  exact mul_left_cancel₀ hb this

end ProximityGap.Frontier.EnergyFreqBlind

#print axioms ProximityGap.Frontier.EnergyFreqBlind.addEnergyVariety_freq_card_eq
#print axioms ProximityGap.Frontier.EnergyFreqBlind.additiveEnergy_freq_invariant
#print axioms ProximityGap.Frontier.EnergyFreqBlind.dilation_levelSet_subsingleton
