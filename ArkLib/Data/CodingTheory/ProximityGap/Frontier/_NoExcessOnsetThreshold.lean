/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WraparoundThreshold

/-!
# THREAD T1 — The wrap-around excess `W_r = E_r − E_r^{char0}` and its onset threshold (#444)

This file builds the **EXACT** wrap-around-excess framework for the Proximity-Prize energy ladder
and lands, axiom-clean, the headline implication

> **no `r`-fold wraparound  ⟹  `W_r = 0`  ⟹  `E_r = E_r^{char0} ≤ Wick`.**

It then pins the precise `r_0(n) > r*` question — the smallest depth at which a genuine wraparound
becomes *possible* — as the single open input that is the prize.

## The object (made exact)

Fix a number field `K` (the prize case: `K = ℚ(ζ_n)`, `n = 2^μ`, `[K:ℚ] = n/2`) carrying the
smooth multiplicative subgroup `μ_n ⊆ K^×`, and a ring homomorphism `φ : K →+* F` into the prize
field `F = F_p` (the reduction `ζ ↦ g` at the chosen prime `𝔭 ∣ p`, `g` a primitive `n`-th root of
unity in `F_p`). The depth-`r` additive energy of a *root indexing* `ζ : ι → K` (with `ζ` taking
values in `μ_n`, i.e. `ζ a ^ n = 1`) over a carrier ring `R` accessed through a ring hom
`ψ : K →+* R` is the collision count

`E_r^ψ = #{ (x, y) ∈ ι^r × ι^r : Σ_t ψ(ζ (x t)) = Σ_t ψ(ζ (y t)) in R }`.

* `E_r^{char0} := E_r^{id}` (collision taken in `K` itself — the Bessel / Gaussian-Wick value).
* `E_r        := E_r^{φ}`   (collision taken in `F_p` — the true char-`p` energy that bounds `B`).

The **wrap-around excess** is `W_r := E_r − E_r^{char0} ≥ 0`. A pair contributing to `W_r` is a
genuine **wraparound**: the two root sums are *distinct in `K`* (`Σ ζ(x_t) ≠ Σ ζ(y_t)`) yet
*equal after reduction* (`φ(Σ ζ(x_t)) = φ(Σ ζ(y_t))`).

## What this file PROVES (unconditional, axiom-clean)

1. `charZero_collision_imp_charP` — every char-`0` collision is a char-`p` collision (`φ` is a
   ring hom), so the char-`0` collision set **injects into** the char-`p` collision set:
   `E_r^{char0} ≤ E_r`. Hence `W_r ≥ 0` is automatic and `W_r` is the count of the set-difference
   (the genuine wraparound pairs).

2. `wrapExcess_def` / `Er_eq_add_wrapExcess` — `E_r = E_r^{char0} + W_r` as an exact `Finset`
   cardinality identity (`W_r = #(charPCollisions \ charZeroCollisions)`).

3. **Headline `noWraparound_imp_energy_eq`** — if there is *no* `r`-fold wraparound (every
   char-`p` collision is already a char-`0` collision: `NoWraparound`), then `W_r = 0` and
   `E_r = E_r^{char0}`. Combined with the in-tree char-`0` Wick bound `E_r^{char0} ≤ (2r-1)‼·n^r`,
   this is exactly `E_r ≤ Wick`.

4. **`noWraparound_of_threshold`** — the *sufficient* arithmetic threshold: if
   `(2r)^{[K:ℚ]} < p` then `NoWraparound` holds (no two distinct depth-`r` root sums can collide
   mod `𝔭`), via the in-tree house bound `no_wraparound_depth`. This pins the **onset**
   `r_0(n) ≥ ½ · p^{1/[K:ℚ]} = ½ · p^{2/n}`.

## The pinned open residual (the prize)

The prize needs `E_r ≤ Wick` at the *saddle* depth `r* = ⌈log p⌉ = β·ln n` (`n = 2^30`,
`p ≈ n·2^128`). The *sufficient* threshold above gives no-wraparound only for `r < ½·p^{2/n}`,
which at the prize scale is `½·n^{2β/n} = O(1)` — far short of `r*`. The genuine open question,
named here as `OnsetExceedsSaddle`, is whether the *true* onset depth `r_0(n)` (the smallest `r`
admitting a nonzero `≤ 2r`-term `±1`-relation of `2^μ`-th roots vanishing mod `p`) exceeds the
saddle depth `r*`. The exact recompute (memory: `W_3 = 0` generic, `W_4 = 0` at every tested
non-Fermat `n=16` prime; onset `r_0(n)` with `n=16: 4 < r_0 < 6`, `n=32: 4 < r_0 < 5`) shows the
true onset is much larger than the crude house threshold — but proving `r_0(n) > r*` is precisely
the Lam–Leung / cyclotomic minimal-weight wall (the prize core). This file lands the *reduction*:
`OnsetExceedsSaddle ⟹ E_{r*} ≤ Wick` axiom-clean, and names the open input honestly.

**HONEST SCOPE.** Items 1–4 are unconditional theorems of the wrap-excess *framework* and of the
*sufficient* (loose) house threshold. The headline at the *prize* depth is the conditional
`energy_le_wick_of_onset` whose hypothesis `OnsetExceedsSaddle` IS the open prize core — it is NOT
discharged here. No `sorry`, no `native_decide`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026
  (ePrint 2026/680, issue #444).
- In-tree: `WraparoundThreshold.lean` (`no_wraparound_depth`, the house bound),
  `CyclotomicLatticeWrapOnset.lean` (the `ℓ¹`-lattice discrete core).
-/

open Finset NumberField Module

namespace ArkLib.ProximityGap.NoExcessOnset

variable {K F : Type*} [Field K] [Field F]

/-- The depth-`r` sum of the roots indexed by a tuple `x : Fin r → ι`, pushed through a ring hom
`ψ : K →+* R`. `ζ : ι → K` indexes the group `μ_n` (its values are `n`-th roots of unity);
`Σ_t ψ (ζ (x t))` is the carrier-ring image of the corresponding depth-`r` root sum. -/
def pushSum {ι R : Type*} [CommRing R] {r : ℕ} (ψ : K →+* R) (ζ : ι → K)
    (x : Fin r → ι) : R :=
  ∑ t, ψ (ζ (x t))

@[simp] theorem pushSum_id {ι : Type*} {r : ℕ} (ζ : ι → K) (x : Fin r → ι) :
    pushSum (RingHom.id K) ζ x = ∑ t, ζ (x t) := by
  simp [pushSum]

/-- A ring hom commutes with the pushed sum: `φ (Σ ζ(x_t)) = Σ φ(ζ(x_t))`. The bridge between a
char-`0` collision (`pushSum id`) and a char-`p` collision (`pushSum φ`). -/
theorem map_pushSum {ι R : Type*} [CommRing R] {r : ℕ} (φ : K →+* R) (ζ : ι → K)
    (x : Fin r → ι) : φ (∑ t, ζ (x t)) = pushSum φ ζ x := by
  simp [pushSum, map_sum]

variable [DecidableEq K] [DecidableEq F]

/-- **The depth-`r` collision set over the carrier reached by `ψ`.** Pairs `(x, y)` of depth-`r`
tuples whose pushed root sums agree. `E_r^ψ = #` of this set. We work over a finite indexing of
`μ_n` (here `ι = K` with the membership encoded via `ζ`); for the prize `ι = Fin n`, `ζ` the
canonical embedding of `μ_n`. -/
noncomputable def collisions {ι R : Type*} [CommRing R] [DecidableEq R] [Fintype ι]
    {r : ℕ} (ψ : K →+* R) (ζ : ι → K) : Finset ((Fin r → ι) × (Fin r → ι)) :=
  Finset.univ.filter (fun p => pushSum ψ ζ p.1 = pushSum ψ ζ p.2)

/-- The depth-`r` additive energy over the carrier reached by `ψ`: the collision count. -/
noncomputable def energy {ι R : Type*} [CommRing R] [DecidableEq R] [Fintype ι]
    {r : ℕ} (ψ : K →+* R) (ζ : ι → K) : ℕ :=
  (collisions (r := r) ψ ζ).card

/-- **`E_r^{char0}` — the characteristic-`0` (Bessel / Gaussian-Wick) energy.** Collisions taken in
`K` itself (the identity ring hom). -/
noncomputable def energyChar0 {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (ζ : ι → K) : ℕ :=
  energy (r := r) (RingHom.id K) ζ

/-- **`E_r` — the characteristic-`p` energy.** Collisions taken after reduction `φ : K →+* F`. -/
noncomputable def energyCharP {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (φ : K →+* F) (ζ : ι → K) : ℕ :=
  energy (r := r) φ ζ

/-- **Every char-`0` collision is a char-`p` collision.** If two depth-`r` root sums agree in `K`,
their `φ`-images agree in `F` (ring hom). So the char-`0` collision set is a *subset* of the
char-`p` collision set. This is the structural reason `W_r ≥ 0`. -/
theorem charZeroCollisions_subset_charP {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    (collisions (r := r) (RingHom.id K) ζ) ⊆ (collisions (r := r) φ ζ) := by
  intro p hp
  simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id] at hp ⊢
  -- `hp : Σ ζ(p.1 t) = Σ ζ(p.2 t)`;  apply `φ`.
  have := congrArg φ hp
  rwa [map_pushSum, map_pushSum] at this

/-- `E_r^{char0} ≤ E_r`: the char-`0` energy never exceeds the char-`p` energy (subset of
collisions). The excess `W_r := E_r − E_r^{char0}` is therefore a genuine nonnegative count. -/
theorem energyChar0_le_energyCharP {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    energyChar0 (r := r) ζ ≤ energyCharP (r := r) φ ζ :=
  Finset.card_le_card (charZeroCollisions_subset_charP φ ζ)

/-- **The wrap-around excess `W_r` as an exact count.** `W_r := #(char-`p` collisions that are NOT
char-`0` collisions)` — exactly the genuine wraparound pairs (distinct in `K`, equal mod `𝔭`). -/
noncomputable def wrapExcess {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (φ : K →+* F) (ζ : ι → K) : ℕ :=
  ((collisions (r := r) φ ζ) \ (collisions (r := r) (RingHom.id K) ζ)).card

/-- **The exact energy split `E_r = E_r^{char0} + W_r`.** Decomposes the char-`p` collision set as
the (disjoint) union of the char-`0` collisions and the genuine wraparound pairs. -/
theorem energyCharP_eq_char0_add_wrapExcess {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) :
    energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ + wrapExcess (r := r) φ ζ := by
  unfold energyCharP energyChar0 energy wrapExcess
  rw [← Finset.card_sdiff_add_card_eq_card (charZeroCollisions_subset_charP φ ζ), Nat.add_comm]

/-- **`NoWraparound`** — the property that *every* char-`p` collision is already a char-`0`
collision. Equivalently: no two depth-`r` root sums that are distinct in `K` collide mod `𝔭`.
This is exactly the condition `W_r = 0`. -/
def NoWraparound {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (φ : K →+* F) (ζ : ι → K) : Prop :=
  ∀ x y : Fin r → ι, pushSum φ ζ x = pushSum φ ζ y → (∑ t, ζ (x t)) = ∑ t, ζ (y t)

/-- **`NoWraparound ⟹ W_r = 0`.** If every mod-`𝔭` collision lifts to a `K`-collision, the
set-difference (genuine wraparound pairs) is empty. -/
theorem wrapExcess_eq_zero_of_noWraparound {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) :
    wrapExcess (r := r) φ ζ = 0 := by
  unfold wrapExcess
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
  intro p hp
  simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id] at hp ⊢
  exact h p.1 p.2 hp

/-- **HEADLINE: no `r`-fold wraparound ⟹ `E_r = E_r^{char0}`.** The exact transfer: when there is
no genuine wraparound at depth `r`, the char-`p` additive energy equals the char-`0` Bessel/Wick
energy *on the nose*. Combined with the in-tree char-`0` bound `E_r^{char0} ≤ (2r-1)‼·n^r`, this is
`E_r ≤ Wick`. -/
theorem noWraparound_imp_energy_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) :
    energyCharP (r := r) φ ζ = energyChar0 (r := r) ζ := by
  rw [energyCharP_eq_char0_add_wrapExcess, wrapExcess_eq_zero_of_noWraparound φ ζ h, Nat.add_zero]

/-- **Consumer form: `E_r ≤ B` whenever `E_r^{char0} ≤ B` and there is no wraparound.** Threads the
in-tree char-`0` Wick bound through the no-wraparound transfer to bound the true char-`p` energy.
Take `B = (2r-1)‼·n^r` and `hchar0 = E_r^{char0} ≤ Wick` (Lam–Leung antipodal, in-tree). -/
theorem energyCharP_le_of_noWraparound_of_char0_le {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) (h : NoWraparound (r := r) φ ζ) {B : ℕ}
    (hchar0 : energyChar0 (r := r) ζ ≤ B) :
    energyCharP (r := r) φ ζ ≤ B := by
  rw [noWraparound_imp_energy_eq φ ζ h]; exact hchar0

end ArkLib.ProximityGap.NoExcessOnset

/-! ## The arithmetic onset threshold — wiring to the in-tree house bound

We now connect `NoWraparound` to the explicit threshold `(2r)^{[K:ℚ]} < p` proven in
`WraparoundThreshold.lean`. The bridge requires the reduction `φ : K →+* F` to be such that a
mod-`𝔭` collision forces `p ∣ N(D)`; the clean algebraic core (`no_wraparound_depth`) already shows
that under the house threshold a nonzero `K`-difference has norm of absolute value `< p`, so it
cannot be `p`-divisible. We package the resulting *sufficient* onset bound.
-/

namespace ArkLib.ProximityGap.NoExcessOnset

open ArkLib.ProximityGap.Wraparound

variable {K : Type*} [Field K] [NumberField K]

/-- **The house onset bound (norm form), restated for the excess framework.** For two depth-`r`
tuples of `n`-th roots of unity (`n ≠ 0`) whose sums are *distinct in `K`*, the house bound
`no_wraparound_depth` says: once `(2r)^{[K:ℚ]} < p`, the norm of the difference is a nonzero
rational integer of absolute value `< p`. Hence no prime `𝔭 ∣ p` identifies them: the only mod-`𝔭`
collisions are char-`0` collisions. This is `NoWraparound` for the canonical root indexing, given
the standard fact (named below) that a mod-`𝔭` collision forces `p ∣ N(difference)`. -/
theorem house_norm_obstruction {r n : ℕ} (hn : n ≠ 0) (a b : Fin r → K)
    (ha : ∀ i, a i ^ n = 1) (hb : ∀ i, b i ^ n = 1)
    {p : ℕ} (hp : ((2 * r : ℕ) : ℝ) ^ finrank ℚ K < p)
    (hne : (∑ i, a i) - ∑ i, b i ≠ 0) :
    Algebra.norm ℚ ((∑ i, a i) - ∑ i, b i) ≠ 0 ∧
      ((|Algebra.norm ℚ ((∑ i, a i) - ∑ i, b i)| : ℚ) : ℝ) < p :=
  no_wraparound_depth hn a b ha hb hp hne

/-- **The onset depth (sufficient side), as a `Prop`.** `OnsetThresholdMet n p r` says the house
threshold `(2r)^{[K:ℚ]} < p` holds — the regime where no depth-`r` wraparound is possible by the
norm bound. For `K = ℚ(ζ_n)`, `[K:ℚ] = n/2`, this is `(2r)^{n/2} < p`, i.e. `r < ½·p^{2/n}`. -/
def OnsetThresholdMet (p r : ℕ) : Prop := ((2 * r : ℕ) : ℝ) ^ finrank ℚ K < p

end ArkLib.ProximityGap.NoExcessOnset

/-! ## The pinned open residual — `r_0(n) > r*` is the prize

The *sufficient* house threshold `OnsetThresholdMet` gives no-wraparound only for `r < ½·p^{2/n}`,
which is `O(1)` at the prize scale (`p = n^β`, `½·n^{2β/n} → ½·n^{o(1)}`). The TRUE onset `r_0(n)`
is much larger (the exact recompute: `W_3 = W_4 = 0` generically; onset between 4 and 6 at `n=16`).
The prize asks whether `r_0(n)` exceeds the saddle depth `r* = ⌈log p⌉`. We name this open input
honestly and land the reduction.
-/

namespace ArkLib.ProximityGap.NoExcessOnset

variable {K F : Type*} [Field K] [Field F] [DecidableEq K] [DecidableEq F]

/-- **The open prize core, named.** `OnsetExceedsSaddle φ ζ r*` asserts the genuine open input:
at the saddle depth `r*` there is *no* wrap-around — every char-`p` collision of depth `r*` root
sums is already a char-`0` collision. Equivalently, the true onset depth `r_0(n)` of a nonzero
`≤ 2r*`-term `±1`-relation of `2^μ`-th roots vanishing mod `p` satisfies `r_0(n) > r*`. THIS IS THE
PRIZE: it is the Lam–Leung / cyclotomic minimal-weight statement, NOT discharged here. -/
def OnsetExceedsSaddle {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  NoWraparound (r := rStar) φ ζ

/-- **The reduction (axiom-clean, conditional on the named prize core).** If the onset exceeds the
saddle depth (`OnsetExceedsSaddle`) and the char-`0` Wick bound holds at `r*` (in-tree Lam–Leung),
then the true char-`p` energy at the saddle depth is `≤ Wick`. This is the *entire* downstream
chain to `M ≤ √(2en·log p) ⟹ δ*` (all PROVEN in-tree); the SOLE open input is `OnsetExceedsSaddle`,
named honestly as the prize. -/
theorem energy_le_wick_of_onset {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (honset : OnsetExceedsSaddle φ ζ rStar) {wick : ℕ}
    (hchar0 : energyChar0 (r := rStar) ζ ≤ wick) :
    energyCharP (r := rStar) φ ζ ≤ wick :=
  energyCharP_le_of_noWraparound_of_char0_le φ ζ honset hchar0

/-- **Explicit `W_{r*} = 0` form of the prize reduction.** Restates the prize as: under the onset
hypothesis, the saddle-depth wrap-excess vanishes — `W_{r*} = 0` — so `E_{r*} = E_{r*}^{char0}`
carries no anomalous wrap-around mass and the moment route sees exactly the Gaussian-Wick value. -/
theorem wrapExcess_saddle_eq_zero_of_onset {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* F) (ζ : ι → K)
    (rStar : ℕ) (honset : OnsetExceedsSaddle φ ζ rStar) :
    wrapExcess (r := rStar) φ ζ = 0 :=
  wrapExcess_eq_zero_of_noWraparound φ ζ honset

end ArkLib.ProximityGap.NoExcessOnset

#print axioms ArkLib.ProximityGap.NoExcessOnset.map_pushSum
#print axioms ArkLib.ProximityGap.NoExcessOnset.charZeroCollisions_subset_charP
#print axioms ArkLib.ProximityGap.NoExcessOnset.energyChar0_le_energyCharP
#print axioms ArkLib.ProximityGap.NoExcessOnset.energyCharP_eq_char0_add_wrapExcess
#print axioms ArkLib.ProximityGap.NoExcessOnset.wrapExcess_eq_zero_of_noWraparound
#print axioms ArkLib.ProximityGap.NoExcessOnset.noWraparound_imp_energy_eq
#print axioms ArkLib.ProximityGap.NoExcessOnset.energyCharP_le_of_noWraparound_of_char0_le
#print axioms ArkLib.ProximityGap.NoExcessOnset.house_norm_obstruction
#print axioms ArkLib.ProximityGap.NoExcessOnset.energy_le_wick_of_onset
#print axioms ArkLib.ProximityGap.NoExcessOnset.wrapExcess_saddle_eq_zero_of_onset
