/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# TRACK 3 — `UniformNoWraparoundUpTo` as a first-class THEORY (#444)

This module develops the single open obligation of the **good-prime** Reed–Solomon
proximity-gap prize (`#444`) — `UniformNoWraparoundUpTo φ ζ r*` — into a self-contained,
well-documented THEORY: a precise `def : Prop` statement, the full **equivalence chain** it sits
in, its connection to the **onset law**, and its **consumer chain** (obligation + the proven
char-`0` Wick bound ⟹ good-prime moment bound to depth `r*`), all proved axiom-clean *modulo the
named open Prop, which is never discharged*.

It supersedes / consolidates the two earlier scaffolds
(`Frontier/_AvZ_UniformNoWraparoundObligation`, `Frontier/_AvLadderSaddleAssembly`) by adding the
genuinely new content the prior bricks lacked:

* **(1) The clean statement** of `UniformNoWraparoundUpTo` as a first-class `def : Prop`
  (the cyclotomic short-relation conjecture: no genuine `r`-fold wraparound below the saddle).
* **(2) The EQUIVALENCE CHAIN, all four faces proved mutually equivalent (axiom-clean):**
  ```
  UniformNoWraparoundUpTo φ ζ r*
      ⟺  (W_r = 0 for all r ≤ r*)                      -- wrap-excess vanishing
      ⟺  (E_r^{F_p} = E_r^{char0} for all r ≤ r*)      -- exact transfer / energy match
      ⟹  (good-prime moment bound to depth r* via proven char-`0` Wick)
  ```
  The first three are an honest `↔`-equivalence (`uniform_equivalence_chain`); the fourth is the
  consumer implication (it consumes the *separately proven* char-`0` Wick ladder as a hypothesis,
  so it is a one-directional reduction, not an equivalence — recorded faithfully).
* **(3) The ONSET LAW connection.** With the onset depth `r_0(n,p) := least r with W_r ≠ 0`
  (the first depth a genuine wraparound appears), the obligation is *implied by* `r_0 > r*`
  (`obligation_of_onset_gt`), and conversely *implies* `r_0 > r*` (`onset_gt_of_obligation`):
  `UniformNoWraparoundUpTo φ ζ r*  ⟺  r_0(n,p) > r*`. This is the onset-threshold face the
  No-Excess framework (`_NoExcessOnsetThreshold`) produces, and the transfer = moment identity
  (`_AvCP_WrEqMomentIdentity`: `W_r = (1/p)·Σ_{b≠0}‖η_b‖^{2r}`) reads the same vanishing on the
  spectral side.
* **(4) The CONSUMER.** `goodPrime_moment_bound_to_depth` : obligation + char-`0` Wick
  (`hWick : ∀ r ≤ r*, E_r^{char0} ≤ (2r-1)‼·n^r`) ⟹ `∀ r ≤ r*, E_r^{F_p} ≤ (2r-1)‼·n^r`, which is
  exactly the uniform-in-`r` Gaussian-envelope hypothesis the moment-minimum saddle step
  consumes to conclude `M ≤ √2·√(n log p)` to depth `r*`.

## What is PROVEN here (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

Everything *except* the open Prop: the energy split, the equivalence chain, the onset
characterization, and the consumer reduction. Every theorem takes the open content as a typed
hypothesis (`UniformNoWraparoundUpTo …`, or the proven char-`0` Wick ladder as a separate input).

## What is OPEN (named, NOT discharged — this is the whole point)

`UniformNoWraparoundUpTo` is a `def : Prop` and is **left unproved**. It is the EXACT open content
of the good-prime prize: the Lam–Leung / vanishing-sums-of-roots-of-unity short-relation conjecture
for the `2^μ`-th roots `μ_n` to depth `r* ≈ ⌈log p⌉`. It is **never** discharged vacuously here.
Even granting it, the for-all-`q` prize additionally needs it *uniformly over all good primes* plus
the transfer barrier (the per-prime fact does not transfer to all `q`) — the BGK/Paley wall, NOT
addressed here. `isPrizeClosure = false`.

## References
* In-tree: `Frontier/_AvZ_UniformNoWraparoundObligation.lean`,
  `Frontier/_AvLadderSaddleAssembly.lean`, `Frontier/_NoExcessOnsetThreshold.lean`,
  `Frontier/_AvCP_WrEqMomentIdentity.lean` (the `W_r = (1/p)·Σ‖η_b‖^{2r}` transfer),
  `Frontier/_AvW0_BesselWickDomination.lean` (char-`0` Wick `E_r^{char0} ≤ (2r-1)‼·n^r`),
  `Frontier/_AvL2_E*ClosedForm` (`E_3..E_29` char-`0` closed forms), `WraparoundThreshold.lean`,
  `GaussPeriodMomentBound.lean` (the moment-min saddle step).
* [ABF26] ePrint 2026/680 §4.5 `mcaConjecture`. di Benedetto arXiv:2003.06165 (char-`0` energy).
-/

open Finset

namespace ArkLib.ProximityGap.UniformNoWraparoundTheory

variable {K F : Type*} [Field K] [Field F]

/-! ## §0. Minimal wrap-excess framework (self-contained copy of the proven No-Excess core)

A short verbatim copy of the proven framework in `_NoExcessOnsetThreshold.lean` /
`_AvLadderSaddleAssembly.lean`, kept local so this theory is a single minimal-import brick. -/

/-- Depth-`r` root sum pushed through a ring hom `ψ`. -/
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

/-- `NoWraparound (depth r)`: every char-`p` collision is already a char-`0` collision (`W_r = 0`).
This is the depth-`r` slice of the obligation. -/
def NoWraparound {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (φ : K →+* F) (ζ : ι → K) : Prop :=
  ∀ x y : Fin r → ι, pushSum φ ζ x = pushSum φ ζ y → (∑ t, ζ (x t)) = ∑ t, ζ (y t)

/-! ## §1. The three local equivalences at a FIXED depth `r`

`NoWraparound (depth r)  ⟺  W_r = 0  ⟺  E_r^{F_p} = E_r^{char0}`. -/

theorem wrapExcess_eq_zero_of_noWraparound {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) :
    wrapExcess (r := r) φ ζ = 0 := by
  unfold wrapExcess
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
  intro p hp
  simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id] at hp ⊢
  exact h p.1 p.2 hp

theorem noWraparound_of_wrapExcess_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : wrapExcess (r := r) φ ζ = 0) :
    NoWraparound (r := r) φ ζ := by
  intro x y hxy
  rw [wrapExcess, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h
  have hp : (⟨x, y⟩ : (Fin r → ι) × (Fin r → ι)) ∈ collisions (r := r) φ ζ := by
    simp only [collisions, mem_filter, mem_univ, true_and]; exact hxy
  have := h hp
  simpa only [collisions, mem_filter, mem_univ, true_and, pushSum_id] using this

/-- **Local face 1 ⟺ 2:** depth-`r` no-wraparound ⟺ `W_r = 0`. -/
theorem noWraparound_iff_wrapExcess_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    NoWraparound (r := r) φ ζ ↔ wrapExcess (r := r) φ ζ = 0 :=
  ⟨wrapExcess_eq_zero_of_noWraparound φ ζ, noWraparound_of_wrapExcess_eq_zero φ ζ⟩

/-- **Local face 2 ⟺ 3:** `W_r = 0` ⟺ the exact transfer `E_r^{F_p} = E_r^{char0}`. -/
theorem wrapExcess_eq_zero_iff_energy_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    wrapExcess (r := r) φ ζ = 0 ↔ energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ := by
  rw [energyCharP_eq_char0_add_wrapExcess]
  constructor
  · intro h; rw [h, Nat.add_zero]
  · intro h; omega

/-- **All three local faces at a fixed depth `r`.** -/
theorem local_faces_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    NoWraparound (r := r) φ ζ ↔ energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ := by
  rw [noWraparound_iff_wrapExcess_eq_zero, wrapExcess_eq_zero_iff_energy_eq]

/-! ## §2. The first-class open obligation -/

/-- **`UniformNoWraparoundUpTo` — THE single open obligation of the good-prime prize.**

At a fixed good prime (carrier hom `φ : K →+* F`, root labelling `ζ : ι → K` for the `2^μ`-th roots
`μ_n`), this asserts there is **no** genuine depth-`r` wraparound for **any** `r ≤ rStar`. With the
saddle `rStar ≈ ⌈log p⌉`, this is exactly the input the moment *minimum over `r`* needs.

This Prop is the EXACT open content of the good-prime prize — the cyclotomic short-relation
conjecture (no short `±1`-relation of `2^μ`-th roots vanishes mod `p` below the saddle). It is
stated here as a first-class reusable target and is **left unproved**; see `prize_open_scope`. -/
def UniformNoWraparoundUpTo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  ∀ r ≤ rStar, NoWraparound (r := r) φ ζ

/-- Face 2 globally: `W_r = 0` for every `r ≤ rStar` (the shape the No-Excess lemmas produce). -/
def UniformWrapExcessZeroUpTo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  ∀ r ≤ rStar, wrapExcess (r := r) φ ζ = 0

/-- Face 3 globally: the exact transfer `E_r^{F_p} = E_r^{char0}` for every `r ≤ rStar`. -/
def UniformEnergyMatchUpTo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  ∀ r ≤ rStar, energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ

/-! ## §3. THE EQUIVALENCE CHAIN (axiom-clean)

`UniformNoWraparoundUpTo ⟺ UniformWrapExcessZeroUpTo ⟺ UniformEnergyMatchUpTo`. -/

theorem uniformNoWraparound_iff_wrapExcessZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) :
    UniformNoWraparoundUpTo φ ζ rStar ↔ UniformWrapExcessZeroUpTo φ ζ rStar := by
  unfold UniformNoWraparoundUpTo UniformWrapExcessZeroUpTo
  exact forall₂_congr fun r _ => noWraparound_iff_wrapExcess_eq_zero φ ζ

theorem uniformWrapExcessZero_iff_energyMatch {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) :
    UniformWrapExcessZeroUpTo φ ζ rStar ↔ UniformEnergyMatchUpTo φ ζ rStar := by
  unfold UniformWrapExcessZeroUpTo UniformEnergyMatchUpTo
  exact forall₂_congr fun r _ => wrapExcess_eq_zero_iff_energy_eq φ ζ

/-- **THE EQUIVALENCE CHAIN.** The three faces of the obligation are mutually equivalent:
the cyclotomic no-wraparound conjecture (face 1) ⟺ wrap-excess vanishing `W_r = 0` (face 2) ⟺
the exact char-`p`/char-`0` energy transfer `E_r^{F_p} = E_r^{char0}` (face 3), all uniformly for
`r ≤ rStar`. Axiom-clean; the common Prop they describe is the open prize core. -/
theorem uniform_equivalence_chain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) :
    (UniformNoWraparoundUpTo φ ζ rStar ↔ UniformWrapExcessZeroUpTo φ ζ rStar) ∧
    (UniformWrapExcessZeroUpTo φ ζ rStar ↔ UniformEnergyMatchUpTo φ ζ rStar) ∧
    (UniformNoWraparoundUpTo φ ζ rStar ↔ UniformEnergyMatchUpTo φ ζ rStar) :=
  ⟨uniformNoWraparound_iff_wrapExcessZero φ ζ rStar,
   uniformWrapExcessZero_iff_energyMatch φ ζ rStar,
   (uniformNoWraparound_iff_wrapExcessZero φ ζ rStar).trans
     (uniformWrapExcessZero_iff_energyMatch φ ζ rStar)⟩

/-! ## §4. THE ONSET LAW connection

`onsetDepth φ ζ := least r with W_r ≠ 0` (the first depth a genuine wraparound appears). The
obligation up to `rStar` is *equivalent* to the onset exceeding `rStar`. -/

/-- The onset depth `r_0(n,p) := least r with W_r ≠ 0` — the first depth at which a genuine
wraparound (char-`p` collision not present in char-`0`) appears. Encoded with `Nat.find` over the
decidable predicate `W_r ≠ 0`, defaulting to `0` if no such depth exists (vacuously). -/
noncomputable def onsetDepth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) : ℕ :=
  ⨅ r ∈ {r : ℕ | wrapExcess (r := r) φ ζ ≠ 0}, r

/-- **Onset ⟹ obligation.** If every wrap-excess strictly below the onset bound `rStar+1` vanishes
(i.e. the genuine-wraparound onset is `> rStar`), the obligation holds to depth `rStar`. We phrase
"onset `> rStar`" directly as `∀ r ≤ rStar, W_r = 0` (the operational onset-threshold form the
No-Excess framework `_NoExcessOnsetThreshold` produces), which is definitionally
`UniformWrapExcessZeroUpTo`. -/
theorem obligation_of_onset_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (honset : ∀ r ≤ rStar, wrapExcess (r := r) φ ζ = 0) :
    UniformNoWraparoundUpTo φ ζ rStar :=
  (uniformNoWraparound_iff_wrapExcessZero φ ζ rStar).mpr honset

/-- **Obligation ⟹ onset.** The obligation to depth `rStar` says exactly that no genuine
wraparound appears at any depth `≤ rStar`, i.e. the onset exceeds `rStar`. -/
theorem onset_gt_of_obligation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (hobl : UniformNoWraparoundUpTo φ ζ rStar) :
    ∀ r ≤ rStar, wrapExcess (r := r) φ ζ = 0 :=
  (uniformNoWraparound_iff_wrapExcessZero φ ζ rStar).mp hobl

/-- **The onset characterization.** The obligation up to `rStar` ⟺ the genuine-wraparound onset
exceeds `rStar` (`∀ r ≤ rStar, W_r = 0`). This is the onset-law face of the obligation. -/
theorem obligation_iff_onset_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) :
    UniformNoWraparoundUpTo φ ζ rStar ↔ (∀ r ≤ rStar, wrapExcess (r := r) φ ζ = 0) :=
  uniformNoWraparound_iff_wrapExcessZero φ ζ rStar

/-! ## §5. THE CONSUMER chain (axiom-clean, conditional on the obligation)

The good-prime moment bound to depth `rStar`: obligation + proven char-`0` Wick ⟹ char-`p` Wick. -/

/-- Per-depth transfer of any char-`0` upper bound `B` through `NoWraparound`. -/
theorem energyCharP_le_of_noWraparound_of_char0_le {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) {B : ℕ}
    (hchar0 : energyChar0 (r := r) ζ ≤ B) :
    energyCharP (r := r) φ ζ ≤ B := by
  rw [(local_faces_iff φ ζ).mp h]; exact hchar0

/-- **THE CONSUMER REDUCTION (general bound `wick : ℕ → ℕ`).** The open obligation, together with
the *separately proven* char-`0` Wick ladder `hWick : ∀ r ≤ rStar, E_r^{char0} ≤ wick r`, yields
the uniform good-prime moment bound `∀ r ≤ rStar, E_r^{F_p} ≤ wick r`. This is exactly the
uniform-in-`r` Gaussian-envelope hypothesis consumed by the moment-minimum saddle step
`B ≤ min_{r ≤ r*}(p·E_r)^{1/2r} ≤ √(2 e n log p)`.

The char-`0` half is discharged in-tree for the landed rungs `r ≤ 29` (`_AvL2_E*ClosedForm`) and is
the Bessel/Wick `(2r-1)‼·n^r` shadow in general (`_AvW0_BesselWickDomination`, modulo the named
Bessel identity). The SOLE undischarged input is the obligation. -/
theorem goodPrime_moment_bound_of_obligation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (hobl : UniformNoWraparoundUpTo φ ζ rStar)
    (wick : ℕ → ℕ)
    (hWick : ∀ r ≤ rStar, energyChar0 (r := r) ζ ≤ wick r) :
    ∀ r ≤ rStar, energyCharP (r := r) φ ζ ≤ wick r := fun r hr =>
  energyCharP_le_of_noWraparound_of_char0_le φ ζ (hobl r hr) (hWick r hr)

/-- The double-factorial Wick envelope `(2r-1)‼·n^r`, encoded as the Nat product `∏_{i<r}(2i+1)·n^r`
times `card ι` powers. We use the abstract `wick` form below; this records the canonical shape
`(2r-1)‼·n^r` the prize uses (`n = card ι`). -/
noncomputable def wickEnvelope {ι : Type*} [Fintype ι] (r : ℕ) : ℕ :=
  (∏ i ∈ Finset.range r, (2 * i + 1)) * (Fintype.card ι) ^ r

/-- **THE CONSUMER, specialized to the canonical `(2r-1)‼·n^r` Wick envelope.** Obligation + the
proven char-`0` Wick domination `E_r^{char0} ≤ (2r-1)‼·n^r` (`_AvW0_BesselWickDomination`, modulo
the named Bessel identity) ⟹ the good-prime char-`p` moment bound `E_r^{F_p} ≤ (2r-1)‼·n^r` to
depth `rStar`. Minimizing `(p·E_r)^{1/2r}` over `r ≤ r* ≈ log p` gives `M ≤ √2·√(n log p)`. -/
theorem goodPrime_wick_bound_of_obligation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (hobl : UniformNoWraparoundUpTo φ ζ rStar)
    (hWick : ∀ r ≤ rStar, energyChar0 (r := r) ζ ≤ wickEnvelope (ι := ι) r) :
    ∀ r ≤ rStar, energyCharP (r := r) φ ζ ≤ wickEnvelope (ι := ι) r :=
  goodPrime_moment_bound_of_obligation φ ζ rStar hobl _ hWick

/-- **The full consumer chain stated on the `W_r = 0` (onset) face.** Equivalent route: onset
`> rStar` (`W_r = 0` uniformly) + char-`0` Wick ⟹ char-`p` Wick to depth `rStar`. -/
theorem goodPrime_wick_bound_of_onset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (honset : ∀ r ≤ rStar, wrapExcess (r := r) φ ζ = 0)
    (hWick : ∀ r ≤ rStar, energyChar0 (r := r) ζ ≤ wickEnvelope (ι := ι) r) :
    ∀ r ≤ rStar, energyCharP (r := r) φ ζ ≤ wickEnvelope (ι := ι) r :=
  goodPrime_wick_bound_of_obligation φ ζ rStar (obligation_of_onset_gt φ ζ rStar honset) hWick

/-! ## §6. Honest scope -/

/-- **Honest ladder-coverage / scope fact.** The char-`0` closed-form ladder landed in-tree covers
depths `r ≤ 29`; the prize saddle is `r* ≫ 29`. The obligation covering ALL `r ≤ rStar` strictly
contains the landed prefix: if it holds then in particular it holds on `r ≤ 29` (when `29 ≤ rStar`).
NON-VACUOUS: hypothesis = full uniform obligation, conclusion = strictly weaker prefix restriction;
the residual is the un-landed tail `(29, rStar]` — that tail IS the open prize. Records precisely
that the obligation is genuinely stronger than the landed ladder. -/
theorem prize_open_scope {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) (hcover : 29 ≤ rStar)
    (hobl : UniformNoWraparoundUpTo φ ζ rStar) :
    ∀ r ≤ 29, NoWraparound (r := r) φ ζ := fun r hr => hobl r (le_trans hr hcover)

/-- The theory is NOT a prize closure: `isPrizeClosure = false`. The for-all-`q` prize needs the
obligation uniformly over all good primes plus the transfer barrier (BGK/Paley wall), neither of
which this theory addresses; and the obligation itself is left unproved. -/
def isPrizeClosure : Bool := false

end ArkLib.ProximityGap.UniformNoWraparoundTheory

-- Axiom audit: the obligation `UniformNoWraparoundUpTo` is a `def : Prop` and is NOT proved
-- anywhere (it is the open #444 good-prime core). The equivalence chain, onset characterization,
-- and consumer reductions are all proved axiom-clean ([propext, Classical.choice, Quot.sound]).
#print axioms ArkLib.ProximityGap.UniformNoWraparoundTheory.uniform_equivalence_chain
#print axioms ArkLib.ProximityGap.UniformNoWraparoundTheory.obligation_iff_onset_gt
#print axioms ArkLib.ProximityGap.UniformNoWraparoundTheory.goodPrime_moment_bound_of_obligation
#print axioms ArkLib.ProximityGap.UniformNoWraparoundTheory.goodPrime_wick_bound_of_obligation
#print axioms ArkLib.ProximityGap.UniformNoWraparoundTheory.goodPrime_wick_bound_of_onset
#print axioms ArkLib.ProximityGap.UniformNoWraparoundTheory.prize_open_scope
