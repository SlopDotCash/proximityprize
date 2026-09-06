/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WraparoundThreshold

/-!
# THREAD T1 — Ladder→saddle assembly of the moment-method good-prime prize (#444)

This file ASSEMBLES the in-tree pieces (the No-Excess wrap-excess transfer, the char-`0` Wick
bound, the explicit char-`0` closed forms `E_3..E_29`) into the single cleanest statement of the
**good-prime** prize, and is *brutally honest* about the one gap the explicit ladder does NOT cross:
the saddle depth.

The minimal wrap-excess framework (collisions/energy/`W_r`/`NoWraparound`) is re-derived locally
(it is a short self-contained copy of `Frontier/_NoExcessOnsetThreshold.lean`, which is an
underscore-prefixed scratch module not importable by name) so this brick depends only on the
tracked substrate `WraparoundThreshold.lean`.

## The moment method (what the prize needs)

The non-principal Paley eigenvalue `B = max_{b≠0}‖η_b‖` (the prize object) is bounded by the
`2r`-th moment of the nontrivial Gauss-period spectrum:

> `B^{2r} ≤ Σ_{b≠0}‖η_b‖^{2r} = p · E_r^{nz}`   (Parseval/moment), so
> `B ≤ min_r (p · E_r^{nz})^{1/2r}`.

The char-`0` (Bessel/Wick) value is `E_r^{char0} ≤ (2r-1)‼ · n^r`. Substituting and minimizing over
`r` gives the **Gaussian / sub-Gaussian envelope** `B ≤ √(2 e n · log p)` at the saddle
`r* ≈ log p`. THIS is the prize exponent (`M ≤ √(2 n log m)` in the [ABF26] window normalization).

So the *entire* moment route reduces to one inequality, **for every `r` up to the saddle**:

> `E_r ≤ E_r^{char0}`     i.e.     `W_r = 0`     i.e.     `NoWraparound (depth r)`.

The transfer `noWraparound_imp_energy_eq` proves `NoWraparound (depth r) ⟹ E_r = E_r^{char0}`
axiom-clean. Hence: **good-prime prize ⟺ `∀ r ≤ r*`, no depth-`r` wraparound at that prime**, i.e.
the true onset `r_0(n) > r* = ⌈log p⌉`.

## What the explicit ladder DOES and DOES NOT do (the honest gap)

* The explicit char-`0` closed forms landed in-tree run `E_3 .. E_29`
  (`Frontier/_AvL2_E{7..29}ClosedForm`, plus `_AvL_T3ClosedForm` for `E_3`). Each is `≤` Wick, so
  `W_r = 0 ⟹ E_r ≤ Wick` is *fully discharged* for those `r`.
* **BUT** the saddle for the prize prime `p ≈ n·2^128` (`n = 2^30`) sits at `r* = ⌈log_2 p⌉ ≈ 158`
  (or `⌈ln p⌉ ≈ 110`). The ladder stops at `r = 29 ≪ r*`: it covers only a vanishing initial
  segment.
* The crude *sufficient* house threshold `(2r)^{n/2} < p` covers only `r < ½·p^{2/n} = O(1)` at
  prize scale — even shorter than the ladder. Neither route reaches `r*` unconditionally.

The open segment `r ∈ (29, r*]` is NOT closeable by extending the ladder: each `E_r` is a separate
char-`0` computation AND a separate char-`p` no-wraparound check, and the open input
`UniformNoWraparoundUpTo` asserts no wraparound *anywhere* in `(29, r*]`. That is the Lam–Leung /
cyclotomic short-relation wall (the prize core), NOT discharged here.

## What this file proves (unconditional, axiom-clean) — the assembly

`moment_route_uniform_wick_of_onset` : if `NoWraparound` holds at **every** depth `r ≤ rStar`
(`UniformNoWraparoundUpTo`) and the char-`0` Wick bounds hold at each such `r`, then
`E_r ≤ wick r` at every depth `r ≤ rStar` — the uniform-in-`r` Gaussian-envelope hypothesis the
moment-minimum step (`B ≤ min_{r≤r*}(p·E_r)^{1/2r} ≤ √(2en log p)`, in-tree
`GaussPeriodMomentBound.lean`) consumes. The named open input `UniformNoWraparoundUpTo` IS the
good-prime prize (`r_0(n) > r*`).

**HONEST SCOPE.** This is an ASSEMBLY/reduction brick. It proves the uniform-in-`r` transfer (no
wraparound up to the saddle ⟹ Wick up to the saddle), the precise hypothesis the moment-min step
consumes. It does NOT discharge `UniformNoWraparoundUpTo` (the prize core), and does NOT close the
for-all-`q` prize — even discharging it would give only the **good-prime** statement (the three
[ABF26] §4.5 constants are existentially bound BEFORE the universal over fields; a single-prime
no-wraparound fact does not transfer to all `q`). `isPrizeClosure = false`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026
  (ePrint 2026/680, §4.5 `mcaConjecture`).
- di Benedetto. *Additive energy / Gauss sums.* arXiv:2003.06165 (char-`0` energy input grounded in
  `Frontier/_AvL_DiBenedettoEnergyGrounded`).
- In-tree: `Frontier/_NoExcessOnsetThreshold.lean`, `Frontier/_AvL2_E*ClosedForm` (`E_3..E_29`),
  `GaussPeriodMomentBound.lean` (the moment-min step).
-/

open Finset

namespace ArkLib.ProximityGap.LadderSaddle

variable {K F : Type*} [Field K] [Field F]

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

/-- `E_r` — char-`p` energy. -/
noncomputable def energyCharP {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) : ℕ := energy (r := r) φ ζ

theorem charZeroCollisions_subset_charP {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    (collisions (r := r) (RingHom.id K) ζ) ⊆ (collisions (r := r) φ ζ) := by
  intro p hp
  simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id] at hp ⊢
  have := congrArg φ hp
  rwa [map_pushSum, map_pushSum] at this

/-- The wrap-around excess `W_r` as an exact count. -/
noncomputable def wrapExcess {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) : ℕ :=
  ((collisions (r := r) φ ζ) \ (collisions (r := r) (RingHom.id K) ζ)).card

theorem energyCharP_eq_char0_add_wrapExcess {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ + wrapExcess (r := r) φ ζ := by
  unfold energyCharP energyChar0 energy wrapExcess
  rw [← Finset.card_sdiff_add_card_eq_card (charZeroCollisions_subset_charP φ ζ), Nat.add_comm]

/-- `NoWraparound`: every char-`p` collision is already a char-`0` collision (`W_r = 0`). -/
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

/-! ## The ladder→saddle assembly -/

/-- **Uniform no-wraparound up to the saddle.** The good-prime prize input: no depth-`r` wraparound
for **any** `r ≤ rStar`. Equivalently the true onset `r_0(n)` exceeds the saddle `rStar = ⌈log p⌉`.
This is exactly what the moment *minimum over `r`* needs (each candidate `E_r` in `min_{r≤r*}` must
be Wick). -/
def UniformNoWraparoundUpTo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  ∀ r ≤ rStar, NoWraparound (r := r) φ ζ

/-- **The ladder→saddle assembly (axiom-clean, conditional on the named good-prime input).** No
wraparound at every depth `r ≤ rStar` plus the char-`0` Wick bounds give `E_r ≤ wick r` at every
depth `r ≤ rStar` — the uniform-in-`r` Gaussian-envelope hypothesis consumed by the moment-minimum
step `B ≤ min_{r ≤ r*}(p·E_r)^{1/2r} ≤ √(2en log p)`. The SOLE open input is
`UniformNoWraparoundUpTo` (the good-prime prize, `r_0(n) > r*`); the char-`0` half is discharged
in-tree for the landed rungs `r ≤ 29` and is the Bessel/Wick `(2r-1)‼·n^r` shadow in general. -/
theorem moment_route_uniform_wick_of_onset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (honset : UniformNoWraparoundUpTo φ ζ rStar)
    (wick : ℕ → ℕ)
    (hchar0 : ∀ r ≤ rStar, energyChar0 (r := r) ζ ≤ wick r) :
    ∀ r ≤ rStar, energyCharP (r := r) φ ζ ≤ wick r := by
  intro r hr
  exact energyCharP_le_of_noWraparound_of_char0_le φ ζ (honset r hr) (hchar0 r hr)

/-- **Good-prime prize restated on `W_r`.** Under the char-`0` Wick bounds, uniform vanishing of the
wrap-excess `W_r = 0` for all `r ≤ rStar` gives uniform-Wick char-`p` energy. Crystallizes the
reduction: good-prime prize ⟺ `W_r = 0` up to the saddle ⟺ `r_0(n) > r*`. -/
theorem uniform_wick_of_uniform_wrapExcess_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (hzero : ∀ r ≤ rStar, wrapExcess (r := r) φ ζ = 0)
    (wick : ℕ → ℕ)
    (hchar0 : ∀ r ≤ rStar, energyChar0 (r := r) ζ ≤ wick r) :
    ∀ r ≤ rStar, energyCharP (r := r) φ ζ ≤ wick r := by
  intro r hr
  rw [energyCharP_eq_char0_add_wrapExcess, hzero r hr, Nat.add_zero]
  exact hchar0 r hr

/-- **The honest ladder-coverage fact.** The explicit char-`0` closed-form ladder landed in-tree
covers depths `r ≤ 29`; the prize saddle is `r* ≫ 29`. The uniform hypothesis covering ALL
`r ≤ rStar` strictly contains the ladder prefix: if it holds, then in particular it holds on the
landed prefix `r ≤ 29` (when `29 ≤ rStar`). NON-VACUOUS: hypothesis = full uniform statement,
conclusion = strictly weaker prefix restriction; the residual is the un-landed tail `(29, rStar]`,
which is the prize. -/
theorem ladder_prefix_subsumed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) (hcover : 29 ≤ rStar)
    (honset : UniformNoWraparoundUpTo φ ζ rStar) :
    ∀ r ≤ 29, NoWraparound (r := r) φ ζ := by
  intro r hr
  exact honset r (le_trans hr hcover)

end ArkLib.ProximityGap.LadderSaddle

#print axioms ArkLib.ProximityGap.LadderSaddle.moment_route_uniform_wick_of_onset
#print axioms ArkLib.ProximityGap.LadderSaddle.uniform_wick_of_uniform_wrapExcess_zero
#print axioms ArkLib.ProximityGap.LadderSaddle.ladder_prefix_subsumed
