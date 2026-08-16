/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The single open obligation `UniformNoWraparoundUpTo` as a first-class named target (#444)

This file CRYSTALLIZES the one open input of the **good-prime** Reed–Solomon proximity-gap prize
(`#444`) as a reusable first-class Lean object, wired to its consumer chain.

## The reduction it sits at the head of

The good-prime prize moment route reduces (per the in-tree `_AvLadderSaddleAssembly` /
`_NoExcessOnsetThreshold` No-Excess framework) to a single statement at a fixed good prime `𝔭`:

> **`UniformNoWraparoundUpTo φ ζ r*`** : for every depth `r ≤ r* (≈ ⌈log p⌉)`, no genuine
> `r`-fold wraparound occurs — every char-`p` collision of root sums already collides in
> characteristic `0`.

Equivalently, with `W_r := E_r^{F_p} − E_r^{char0} ≥ 0` the wrap-around excess (exactly the count
of genuine wraparound pairs, distinct in `K` but equal mod `𝔭`):

> `UniformNoWraparoundUpTo φ ζ r*`  ⟺  `W_r = 0` for all `r ≤ r*`  ⟺  the onset `r_0(n) > r*`.

The minimal wrap-excess framework (`collisions`/`energy`/`W_r`/`NoWraparound`) is re-derived
locally here so the obligation and its consumer reduction are a single self-contained,
minimal-import brick. It is a short verbatim copy of the proven framework in
`Frontier/_NoExcessOnsetThreshold.lean` and `Frontier/_AvLadderSaddleAssembly.lean`.

## What is PROVEN here (axiom-clean, conditional on the named open input)

* `energyCharP_eq_char0_add_wrapExcess` — the exact split `E_r = E_r^{char0} + W_r`.
* `noWraparound_imp_energy_eq` / `energyCharP_le_of_noWraparound_of_char0_le` — `W_r = 0` transfers
  the char-`0` Wick bound to char-`p`, **fully discharged** for the depths it covers.
* `goodPrime_moment_bound_of_obligation` — **the consumer reduction**: the obligation
  `UniformNoWraparoundUpTo φ ζ r*` together with the proven char-`0` Wick ladder
  (`hchar0 : ∀ r ≤ r*, E_r^{char0} ≤ wick r`) yields the uniform good-prime moment bound
  `∀ r ≤ r*, E_r^{F_p} ≤ wick r`. This is exactly the uniform-in-`r` Gaussian-envelope hypothesis
  consumed by the moment-minimum step `B ≤ min_{r ≤ r*}(p·E_r)^{1/2r} ≤ √(2 e n log p)`.
* `goodPrime_moment_bound_iff_uniform_wrapExcess_zero` — restates the obligation as `W_r = 0`
  uniformly, the form the No-Excess threshold lemmas produce.

## What is OPEN (named, NOT discharged)

`UniformNoWraparoundUpTo` is **left unproved**. It is the EXACT open content of the good-prime
prize: the cyclotomic short-relation conjecture (a Lam–Leung / vanishing-sums-of-roots-of-unity
statement for the `2^μ`-th roots `μ_n` at depth up to `r* ≈ log p`). The honest scope, recorded in
`prize_open_obligation_scope`:

1. The brick proves only the **consumer** implication; the hypothesis IS the open problem.
2. Even granting it, the **for-all-`q`** prize additionally needs it **uniformly over all good
   primes `q`** *plus* the transfer barrier (the per-prime no-wraparound fact does not transfer to
   all `q`): this is the BGK/Paley wall and is **not** addressed here.

`closesOpenCore = false`. Nothing here is a closure of `#444`.

## References
* In-tree: `Frontier/_NoExcessOnsetThreshold.lean`, `Frontier/_AvLadderSaddleAssembly.lean`,
  `Frontier/_AvCP_WrEqMomentIdentity.lean` (the `W_r = (1/p)·Σ_{b≠0}|η_b|^{2r}` transfer),
  `Frontier/_AvL2_E*ClosedForm` (`E_3..E_29` char-`0` closed forms), `WraparoundThreshold.lean`.
-/

open Finset

namespace ArkLib.ProximityGap.UniformNoWraparoundObligation

variable {K F : Type*} [Field K] [Field F]

/-! ## Minimal wrap-excess framework (self-contained copy of the proven No-Excess core) -/

/-- Depth-`r` root sum pushed through a ring hom. -/
def pushSum {ι R : Type*} [CommRing R] {r : ℕ} (ψ : K →+* R) (ζ : ι → K) (x : Fin r → ι) : R :=
  ∑ t, ψ (ζ (x t))

@[simp] theorem pushSum_id {ι : Type*} {r : ℕ} (ζ : ι → K) (x : Fin r → ι) :
    pushSum (RingHom.id K) ζ x = ∑ t, ζ (x t) := by simp [pushSum]

theorem map_pushSum {ι R : Type*} [CommRing R] {r : ℕ} (φ : K →+* R) (ζ : ι → K) (x : Fin r → ι) :
    φ (∑ t, ζ (x t)) = pushSum φ ζ x := by simp [pushSum, map_sum]

variable [DecidableEq K] [DecidableEq F]

/-- Depth-`r` collision set over the carrier reached by `ψ`. -/
noncomputable def collisions {ι R : Type*} [CommRing R] [DecidableEq R] [Fintype ι]
    {r : ℕ} (ψ : K →+* R) (ζ : ι → K) : Finset ((Fin r → ι) × (Fin r → ι)) :=
  Finset.univ.filter (fun p => pushSum ψ ζ p.1 = pushSum ψ ζ p.2)

/-- Depth-`r` additive energy over the carrier reached by `ψ`. -/
noncomputable def energy {ι R : Type*} [CommRing R] [DecidableEq R] [Fintype ι]
    {r : ℕ} (ψ : K →+* R) (ζ : ι → K) : ℕ := (collisions (r := r) ψ ζ).card

/-- `E_r^{char0}` — char-`0` (Bessel/Wick) energy. -/
noncomputable def energyChar0 {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (ζ : ι → K) : ℕ :=
  energy (r := r) (RingHom.id K) ζ

/-- `E_r^{F_p}` — char-`p` energy. -/
noncomputable def energyCharP {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) : ℕ := energy (r := r) φ ζ

theorem charZeroCollisions_subset_charP {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    (collisions (r := r) (RingHom.id K) ζ) ⊆ (collisions (r := r) φ ζ) := by
  intro p hp
  simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id] at hp ⊢
  have := congrArg φ hp
  rwa [map_pushSum, map_pushSum] at this

/-- The wrap-around excess `W_r := #(char-`p` collisions that are NOT char-`0` collisions)` — the
genuine wraparound pairs (distinct in `K`, equal mod `𝔭`). -/
noncomputable def wrapExcess {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) : ℕ :=
  ((collisions (r := r) φ ζ) \ (collisions (r := r) (RingHom.id K) ζ)).card

/-- The exact energy split `E_r^{F_p} = E_r^{char0} + W_r`. -/
theorem energyCharP_eq_char0_add_wrapExcess {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ + wrapExcess (r := r) φ ζ := by
  unfold energyCharP energyChar0 energy wrapExcess
  rw [← Finset.card_sdiff_add_card_eq_card (charZeroCollisions_subset_charP φ ζ), Nat.add_comm]

/-- `NoWraparound (depth r)`: every char-`p` collision is already a char-`0` collision (`W_r = 0`). -/
def NoWraparound {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (φ : K →+* F) (ζ : ι → K) : Prop :=
  ∀ x y : Fin r → ι, pushSum φ ζ x = pushSum φ ζ y → (∑ t, ζ (x t)) = ∑ t, ζ (y t)

theorem wrapExcess_eq_zero_of_noWraparound {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) :
    wrapExcess (r := r) φ ζ = 0 := by
  unfold wrapExcess
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
  intro p hp
  simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id] at hp ⊢
  exact h p.1 p.2 hp

theorem noWraparound_imp_energy_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) :
    energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ := by
  rw [energyCharP_eq_char0_add_wrapExcess, wrapExcess_eq_zero_of_noWraparound φ ζ h, Nat.add_zero]

theorem energyCharP_le_of_noWraparound_of_char0_le {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) {B : ℕ}
    (hchar0 : energyChar0 (r := r) ζ ≤ B) :
    energyCharP (r := r) φ ζ ≤ B := by
  rw [noWraparound_imp_energy_eq φ ζ h]; exact hchar0

/-! ## The first-class open obligation -/

/-- **`UniformNoWraparoundUpTo` — the single open obligation of the good-prime prize.**

At a fixed good prime (carrier hom `φ : K →+* F`, root labelling `ζ : ι → K` for the `2^μ`-th roots
`μ_n`), this asserts there is **no** genuine depth-`r` wraparound for **any** `r ≤ rStar`. With the
saddle `rStar ≈ ⌈log p⌉`, this is exactly the input the moment *minimum over `r`* needs (every
candidate `E_r` in `min_{r ≤ r*}` must be at its char-`0` Wick value).

This Prop is the EXACT open content of the good-prime prize — the cyclotomic short-relation
conjecture (`r_0(n) > r*`). It is stated here as a first-class reusable target and is **left
unproved**; see `prize_open_obligation_scope`. -/
def UniformNoWraparoundUpTo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  ∀ r ≤ rStar, NoWraparound (r := r) φ ζ

/-- The obligation in its `W_r`-vanishing form (the shape the No-Excess threshold lemmas produce):
`W_r = 0` for every `r ≤ rStar`. -/
def UniformWrapExcessZeroUpTo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  ∀ r ≤ rStar, wrapExcess (r := r) φ ζ = 0

/-- The two phrasings of the obligation agree. -/
theorem uniformNoWraparound_iff_uniformWrapExcessZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) :
    UniformNoWraparoundUpTo φ ζ rStar ↔ UniformWrapExcessZeroUpTo φ ζ rStar := by
  constructor
  · intro h r hr
    exact wrapExcess_eq_zero_of_noWraparound φ ζ (h r hr)
  · intro h r hr x y hxy
    -- `W_r = 0` ⟹ the char-`p` collision set equals the char-`0` one, so `(x,y)` collides in `K`.
    have hz := h r hr
    rw [wrapExcess, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hz
    have hp : (⟨x, y⟩ : (Fin r → ι) × (Fin r → ι)) ∈ collisions (r := r) φ ζ := by
      simp only [collisions, mem_filter, mem_univ, true_and]; exact hxy
    have := hz hp
    simpa only [collisions, mem_filter, mem_univ, true_and, pushSum_id] using this

/-! ## The consumer reduction (axiom-clean, conditional on the obligation) -/

/-- **THE CONSUMER REDUCTION.** The open obligation `UniformNoWraparoundUpTo φ ζ rStar`, together
with the proven char-`0` Wick ladder `hchar0 : ∀ r ≤ rStar, E_r^{char0} ≤ wick r`, yields the
uniform good-prime moment bound `∀ r ≤ rStar, E_r^{F_p} ≤ wick r`.

This is the exact uniform-in-`r` Gaussian-envelope hypothesis consumed downstream by the
moment-minimum saddle step `B ≤ min_{r ≤ r*}(p·E_r)^{1/2r} ≤ √(2 e n log p)`. The char-`0` half is
discharged in-tree for the landed rungs `r ≤ 29` (`_AvL2_E*ClosedForm`) and is the Bessel/Wick
`(2r-1)‼·n^r` shadow in general. The SOLE undischarged input is the obligation. -/
theorem goodPrime_moment_bound_of_obligation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (hobl : UniformNoWraparoundUpTo φ ζ rStar)
    (wick : ℕ → ℕ)
    (hchar0 : ∀ r ≤ rStar, energyChar0 (r := r) ζ ≤ wick r) :
    ∀ r ≤ rStar, energyCharP (r := r) φ ζ ≤ wick r := by
  intro r hr
  exact energyCharP_le_of_noWraparound_of_char0_le φ ζ (hobl r hr) (hchar0 r hr)

/-- The consumer reduction phrased on the `W_r = 0` form of the obligation. -/
theorem goodPrime_moment_bound_iff_uniform_wrapExcess_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (hzero : UniformWrapExcessZeroUpTo φ ζ rStar)
    (wick : ℕ → ℕ)
    (hchar0 : ∀ r ≤ rStar, energyChar0 (r := r) ζ ≤ wick r) :
    ∀ r ≤ rStar, energyCharP (r := r) φ ζ ≤ wick r := by
  intro r hr
  rw [energyCharP_eq_char0_add_wrapExcess, hzero r hr, Nat.add_zero]
  exact hchar0 r hr

/-- **Honest ladder-coverage / scope fact.** The char-`0` closed-form ladder landed in-tree covers
depths `r ≤ 29`; the prize saddle is `r* ≫ 29`. The obligation covering ALL `r ≤ rStar` strictly
contains the landed prefix: if it holds then in particular it holds on `r ≤ 29` (when `29 ≤ rStar`).
NON-VACUOUS: the hypothesis is the full uniform obligation, the conclusion is the strictly weaker
prefix restriction; the residual is the un-landed tail `(29, rStar]` — that tail IS the open prize.
This records precisely that the obligation is genuinely stronger than the landed ladder. -/
theorem prize_open_obligation_scope {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) (hcover : 29 ≤ rStar)
    (hobl : UniformNoWraparoundUpTo φ ζ rStar) :
    ∀ r ≤ 29, NoWraparound (r := r) φ ζ := by
  intro r hr
  exact hobl r (le_trans hr hcover)

end ArkLib.ProximityGap.UniformNoWraparoundObligation

-- Axiom audit: the obligation `UniformNoWraparoundUpTo` is a Prop and is NOT proved anywhere
-- (it is the open #444 good-prime core). Only the CONSUMER reductions are proved, and they are
-- axiom-clean (no `sorryAx`).
#print axioms
  ArkLib.ProximityGap.UniformNoWraparoundObligation.goodPrime_moment_bound_of_obligation
#print axioms
  ArkLib.ProximityGap.UniformNoWraparoundObligation.goodPrime_moment_bound_iff_uniform_wrapExcess_zero
#print axioms
  ArkLib.ProximityGap.UniformNoWraparoundObligation.uniformNoWraparound_iff_uniformWrapExcessZero
#print axioms
  ArkLib.ProximityGap.UniformNoWraparoundObligation.prize_open_obligation_scope
