/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaw
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# The Guruswami–Sudan-aware `ε_ca` lower bound and the L4.6 collapse (`epsMCA = epsCA`)

This file supplies the **lower-bound side** of the ABF26 Lemma 4.6 hard-direction reduction. The
upper-bound side is fully in-tree (`ProximityGap.Errors`): under the unique-decoding regime (UDR)
`2·δ·n < δ_min(C)` and the faithful instance `[NoZeroSMulDivisors F A]` (which `Σ = Fˢ` satisfies
automatically),

  `epsMCA_le_max_epsCA_card_div_udr` :  `ε_mca(C, δ) ≤ max( ε_ca(C, δ, δ) , ⌊δ·n⌋ / |F| )`.

The whole hard direction therefore collapses to the **single numeric dominance**

  (★)  `⌊δ·n⌋ / |F| ≤ ε_ca(C, δ, δ)`.

The previous analysis (`research/proximity-prize/dispositions/pc-w1-L4.6-hard.md`,
`Errors.lean` S1–S5 wall, `LineDecodingCounting.double_coverage_counterexample`) established that
(★) is **invisible to the abstract `epsCA`**: a code with no non-jointly-close near-codewords has
`ε_ca = 0` while the count `⌊δ·n⌋/|F|` can be positive, so the naive route is kernel-refuted, and
the dominance can only be realised by an **explicit witness pair** `(u₀, u₁)` whose line
`u₀ + γ·u₁` is `δ`-close to `C` for `⌊δ·n⌋`-many combiners `γ` — the classical
[BCIKS20, Prop 1.1] / Guruswami–Sudan "one good `γ` per close codeword in the decoding list" lower
bound. This is precisely the **statement repair** the disposition calls for: (★) is not a theorem
about the bare `epsCA`, it is a *consequence of the GS-witness existence statement*, which this
file names and wires.

## The statement repair, made precise

* `GSWitnessLowerBound C δ m` — the **GS-aware lower-bound statement** (a `Prop`): there is a stack
  `u` that is **not** jointly `δ`-close to `C` and a finset `Γ` of at least `m` combiners `γ` at
  each of which the line `u 0 + γ • u 1` is `δ`-close to `C`. This is the explicit witness pair
  `(u 0, u 1)` built from a `δ`-close non-codeword: each close codeword in the line's decoding list
  contributes one good `γ`, and the GS degree structure caps/realises the count.

* `gsWitness_imp_epsCA_ge` (PROVEN, axiom-clean):
  `GSWitnessLowerBound C δ m → m / |F| ≤ ε_ca(C, δ, δ)`.
  This is the in-tree front door: the witness's good-`γ` set injects into the `epsCA` line-close
  filter (`epsCA_ge_card_good_gamma_div_card`), so the count becomes an `ε_ca` lower bound.

* `floorCount_le_epsCA_of_gsWitness` (PROVEN, axiom-clean) — the residual (★) itself:
  `GSWitnessLowerBound C δ ⌊δ·n⌋ → ⌊δ·n⌋/|F| ≤ ε_ca(C, δ, δ)`.

* `epsMCA_eq_epsCA_below_udr_of_gsWitness` (PROVEN, axiom-clean) — **the collapse.** Combining the
  in-tree UDR upper bound with the GS-witness lower bound on the floor count yields the full L4.6
  equality `ε_mca(C, δ) = ε_ca(C, δ, δ)` below UDR, with the residual reduced to the single named
  hypothesis `GSWitnessLowerBound C δ ⌊δ·n⌋` (the BCIKS20-style witness existence). The hard
  direction is thus delivered as a `_of_gsWitness` reduction whose only remaining surface is the
  precise, named GS-witness construction.

## Why `GSWitnessLowerBound` is the honest residual (not a weakening)

`GSWitnessLowerBound C δ ⌊δ·n⌋` is exactly [BCIKS20, Prop 1.1] / [ACFY25, Lemma 4.10]: the
existence of an interleaved word stack realising the proximity-gap discontinuity with `⌊δ·n⌋`
good combiners. It is *strictly sharper* than the prior opaque residual
`diffStackMCAResidualBelowUDR` of `Errors.lean`: that one was a per-stack probability bound on an
abstract `mcaEvent`; this one is the explicit, constructive witness-existence statement that the
disposition's kernel-checked walls proved is the *only* faithful route. Discharging it for a
concrete code family (e.g. the CS25 deep-hole RS construction, whose `δ`-close non-codeword lies
in a decoding list of `⌊δ·n⌋`-many codewords) closes L4.6 below UDR for that family.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon Codes*.
* [ACFY25] / [Hab25] — the Guruswami–Sudan exceptional-`γ` rearrangement.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace L46GS

section

-- Same universe/instance discipline as `ProximityGap.Errors` (PMF forces `Type 0`).
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The GS-aware `ε_ca` lower-bound statement (explicit witness-pair existence).**

There is a word stack `u = (u 0, u 1)` that is **not** jointly `δ`-close to `C`, together with a
finite set `Γ` of at least `m` scalar combiners `γ`, such that at each `γ ∈ Γ` the line
`u 0 + γ • u 1` is `δ`-close to `C`.

This is the formal content of [BCIKS20, Prop 1.1] for the affine-line case: the pair `(u 0, u 1)`
is built from a `δ`-close non-codeword (a deep hole / list-decoding point), and the good combiners
`Γ` are the `m`-many `γ` whose line picks up a *distinct* close codeword from the decoding list —
the Guruswami–Sudan degree structure both produces and caps this count. The stack is engineered to
be *not* jointly close precisely so that no single codeword pair explains all good combiners; this
is what makes its contribution visible to `ε_ca` (which zeros out jointly-close stacks).

It is the named residual the L4.6 hard-direction reduction terminates at: see
`floorCount_le_epsCA_of_gsWitness` and `epsMCA_eq_epsCA_below_udr_of_gsWitness`. -/
def GSWitnessLowerBound (C : Set (ι → A)) (δ : ℝ≥0) (m : ℕ) : Prop :=
  ∃ (u : WordStack A (Fin 2) ι) (Γ : Finset F),
    ¬ jointProximity (C := C) (u := u) δ ∧
    m ≤ Γ.card ∧
    ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ

/-- **GS-witness ⇒ `ε_ca` lower bound (PROVEN).** The good-combiner count of any GS witness is an
`ε_ca` lower bound: `GSWitnessLowerBound C δ m → m / |F| ≤ ε_ca(C, δ, δ)`.

The witness stack `u` is not jointly close, so the `epsCA` body at `u` is the line-close
probability, and its good-`γ` set `Γ` injects into the closeness filter; `m ≤ |Γ|` then gives the
numerator bound. This is `epsCA_ge_card_good_gamma_div_card` lifted to the existential statement. -/
theorem gsWitness_imp_epsCA_ge
    (C : Set (ι → A)) (δ : ℝ≥0) {m : ℕ}
    (h : GSWitnessLowerBound (F := F) C δ m) :
    (m : ENNReal) / (Fintype.card F : ENNReal) ≤ epsCA (F := F) C δ δ := by
  obtain ⟨u, Γ, hjp, hcard, hclose⟩ := h
  -- `m / |F| ≤ |Γ| / |F| ≤ ε_ca`.
  refine le_trans ?_ (epsCA_ge_card_good_gamma_div_card C δ δ u hjp Γ hclose)
  apply ENNReal.div_le_div_right
  -- `(m : ENNReal) ≤ ((Γ.card : ℝ≥0) : ENNReal)` from `m ≤ Γ.card`.
  have : (m : ENNReal) ≤ (Γ.card : ENNReal) := by exact_mod_cast hcard
  simpa using this

/-- **The L4.6 residual (★), as a `_of_gsWitness` reduction (PROVEN).**

`GSWitnessLowerBound C δ ⌊δ·n⌋ → ⌊δ·n⌋ / |F| ≤ ε_ca(C, δ, δ)`.

This is exactly the numeric dominance the L4.6 hard direction reduces to (the `(★)` of the module
docstring and of `Errors.lean`'s `epsMCA_eq_epsCA_below_udr`). It is *not* a theorem about the bare
`epsCA` — the disposition's kernel-checked walls show that — but it **is** a theorem about `epsCA`
plus the explicit BCIKS20-style witness existence, which is what `GSWitnessLowerBound` names. -/
theorem floorCount_le_epsCA_of_gsWitness
    (C : Set (ι → A)) (δ : ℝ≥0)
    (h : GSWitnessLowerBound (F := F) C δ (Nat.floor (δ * (Fintype.card ι : ℝ≥0)))) :
    (Nat.floor (δ * (Fintype.card ι : ℝ≥0)) : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsCA (F := F) C δ δ :=
  gsWitness_imp_epsCA_ge C δ h

/-- **ABF26 Lemma 4.6 hard direction, GS-witness route (PROVEN reduction).**

In the unique-decoding regime `2·δ·n < δ_min(C)`, with the faithful instance
`[NoZeroSMulDivisors F A]` (automatic for `Σ = Fˢ`), the full equality `ε_mca = ε_ca` follows from
the **single** named GS-witness hypothesis `GSWitnessLowerBound C δ ⌊δ·n⌋`.

Proof:
* `ε_ca ≤ ε_mca` is the in-tree `epsCA_le_epsMCA` (no UDR needed).
* `ε_mca ≤ ε_ca`: the in-tree UDR upper bound `epsMCA_le_max_epsCA_card_div_udr` gives
  `ε_mca ≤ max(ε_ca, ⌊δ·n⌋/|F|)`; the GS witness gives `⌊δ·n⌋/|F| ≤ ε_ca`
  (`floorCount_le_epsCA_of_gsWitness`), so the `max` collapses to `ε_ca`.

This delivers the hard direction as an honest reduction: its only residual surface is the precise,
named, constructive `GSWitnessLowerBound C δ ⌊δ·n⌋` (the BCIKS20 Prop 1.1-style witness existence),
strictly sharper than the prior abstract `diffStackMCAResidualBelowUDR`. -/
theorem epsMCA_eq_epsCA_below_udr_of_gsWitness [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist ((C : Set (ι → A))) : ℝ≥0))
    (h_gs : GSWitnessLowerBound (F := F) (A := A) (C : Set (ι → A)) δ
      (Nat.floor (δ * (Fintype.card ι : ℝ≥0)))) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ =
    epsCA (F := F) (A := A) ((C : Set (ι → A))) δ δ := by
  refine le_antisymm ?_ (epsCA_le_epsMCA C δ)
  -- UDR upper bound: `ε_mca ≤ max(ε_ca, ⌊δ·n⌋/|F|)`.
  refine le_trans (epsMCA_le_max_epsCA_card_div_udr C δ h_udr) ?_
  -- Collapse the `max` using the GS-witness lower bound `⌊δ·n⌋/|F| ≤ ε_ca`.
  rw [max_le_iff]
  exact ⟨le_refl _, floorCount_le_epsCA_of_gsWitness (C : Set (ι → A)) δ h_gs⟩

/-- **The GS-witness route discharges the abstract `diffStackMCAResidualBelowUDR` (PROVEN
bridge).** Under UDR with `[NoZeroSMulDivisors F A]`, the GS-witness floor-count hypothesis
implies the per-stack difference-stack residual `Errors.lean` carried as the hard-direction
obligation. Hence the older abstract residual is *also* discharged by the (sharper, constructive)
GS witness — the two residual surfaces are reconciled, and the GS witness is the canonical one.

Proof: `diffStackMCAResidualBelowUDR` asks, for jointly-close `u` and a codeword pair `(p₀, p₁)`,
that `Pr_γ[mcaEvent(C, δ, u 0 − p₀, u 1 − p₁)] ≤ ε_ca`. The difference stack `(u 0 − p₀, u 1 − p₁)`
either *is* jointly `δ`-close (then its `mcaEvent` mass is bounded by `⌊δ·n⌋/|F|` via the in-tree
`jointlyProximate_mcaEvent_Pr_le_card_div_udr`, which the GS witness dominates by `ε_ca`), or it is
not (then `mcaEvent_probability_le_epsCA_of_not_jointProximity` bounds it by `ε_ca` directly). -/
theorem diffStackResidual_of_gsWitness [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist ((C : Set (ι → A))) : ℝ≥0))
    (h_gs : GSWitnessLowerBound (F := F) (A := A) (C : Set (ι → A)) δ
      (Nat.floor (δ * (Fintype.card ι : ℝ≥0)))) :
    diffStackMCAResidualBelowUDR (F := F) (A := A) C δ := by
  intro u p₀ p₁ _hp₀ _hp₁ _hjp
  -- The difference stack `d := (u 0 − p₀, u 1 − p₁)`.
  by_cases hd_jp :
      jointProximity (C := (C : Set (ι → A))) (u := finMapTwoWords (u 0 - p₀) (u 1 - p₁)) δ
  · -- Jointly-close difference stack: bound the `mcaEvent` mass by `⌊δ·n⌋/|F| ≤ ε_ca`.
    have hbound :=
      jointlyProximate_mcaEvent_Pr_le_card_div_udr (F := F) C δ
        (finMapTwoWords (u 0 - p₀) (u 1 - p₁)) h_udr hd_jp
    -- `finMapTwoWords a b 0 = a`, `… 1 = b` (definitional row extraction).
    simp only [finMapTwoWords] at hbound
    refine le_trans hbound ?_
    exact floorCount_le_epsCA_of_gsWitness (C : Set (ι → A)) δ h_gs
  · -- Non-jointly-close difference stack: bound the `mcaEvent` mass by `ε_ca` directly.
    have hbound :=
      mcaEvent_probability_le_epsCA_of_not_jointProximity (F := F) (C := (C : Set (ι → A)))
        δ δ (finMapTwoWords (u 0 - p₀) (u 1 - p₁)) hd_jp
    simpa only [finMapTwoWords] using hbound

end

end L46GS

end ProximityGap
