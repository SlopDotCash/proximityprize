/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WraparoundThreshold

/-!
# THREAD T1 — The wrap-around excess `W_r = E_r − E_r^{char0}` and its onset threshold (#444)

This file builds the **EXACT** wrap-around-excess framework for the Proximity-Prize energy ladder
and lands, axiom-clean, the implication

> **no `r`-fold wraparound  ⟹  `W_r = 0`  ⟹  `E_r = E_r^{char0}`**

(hence `E_r ≤ Wick` whenever `E_r^{char0} ≤ Wick`).

## Audit correction (2026-10-28, R-113)

Earlier versions fixed `[Field K] [Field F]` and a ring hom `φ : K →+* F`, with `K` meant to be the
characteristic-`0` number field `ℚ(ζ_n)` and `F = F_p`. That model was defective:

* every ring hom from a field to a nontrivial ring is injective, so for a field source
  `NoWraparound` holds automatically, every collision set equals the char-`0` collision set and
  `wrapExcess = 0` at every depth (`noWraparound_of_field_source`,
  `wrapExcess_eq_zero_of_field_source`, `onsetExceedsSaddle_of_field_source`): the "open" predicate
  was a theorem;
* for the intended fields no such hom exists at all (`false_of_ringHom_charZero_charP`).
  Reduction modulo a prime `𝔭 ∣ p` is defined on the integer ring `𝓞_K = ℤ[ζ_n]` (or a suitable
  localization), not on the whole number field.

The framework is now stated for an arbitrary **commutative collision ring** `K` (intended
instance: `𝓞_K = ℤ[ζ_n]`, or `ℤ[ζ_n]` localized away from `p`) and an arbitrary commutative carrier
`F`, so that genuine wraparound can occur; `int_mod_three_wrapExcess_pos` is a checked nonzero
wrap instance (`ℤ → ZMod 3`, roots `±1`, depth `3`: `3 ≠ -3` in `ℤ` but both vanish mod `3`). The
actual residue hom `ℤ[ζ_n] → F_p` and its link to the field-domain energies used elsewhere in the
tree are NOT built here (remaining work).

Moreover the static saddle no-wrap statement is **not the prize** and is in fact **false** at
production parameters: the in-tree DC floor `n^{2r} ≤ p·E_r` with `n = 2^30`, `p < 2^159`, `r = 6`
gives `p·(2r−1)!!·n^r < 2^(159+14+180) = 2^353 < 2^360 = n^{2r}` since `(2·6−1)!! = 10395 < 2^14`,
so the actual `E_6` exceeds the char-`0` Wick ceiling and `W_6 > 0`; padding both tuples with common
roots propagates a wrap to every larger depth, including the saddle. The abstract form of this
obstruction is the checked `not_noWraparound_of_dcFloor` (with the DC floor and the char-`0` Wick
bound as explicit hypotheses), and `production_dcFloor_gap_r6` checks the arithmetic. The correct
target allows the DC contribution and asks for a quantitative DC-subtracted excess budget; that
remains open.

## The object (made exact)

Fix a commutative collision ring `K` (intended: `𝓞_K = ℤ[ζ_n]`, `n = 2^μ`) carrying the roots
`μ_n`, and a ring homomorphism `φ : K →+* F` into a carrier `F` (intended: the residue map
`ℤ[ζ_n] → 𝓞_K/𝔭 ≅ F_p`, `ζ ↦ g`, `g` a primitive `n`-th root of unity in `F_p`). The depth-`r`
additive energy of a *root indexing* `ζ : ι → K` (with `ζ` taking values in `μ_n`, i.e.
`ζ a ^ n = 1`) over a carrier ring `R` accessed through a ring hom `ψ : K →+* R` is the collision
count

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

3. **`noWraparound_imp_energy_eq`** — if there is *no* `r`-fold wraparound (every
   char-`p` collision is already a char-`0` collision: `NoWraparound`), then `W_r = 0` and
   `E_r = E_r^{char0}`. Combined with a char-`0` Wick bound `E_r^{char0} ≤ (2r-1)‼·n^r` (supplied
   as a hypothesis), this gives `E_r ≤ Wick`.

4. **`house_norm_obstruction`** — the *sufficient* arithmetic threshold at field level: if
   `(2r)^{[K:ℚ]} < p` then a nonzero difference of two depth-`r` root sums in a number field `K`
   has nonzero rational norm of absolute value `< p` (in-tree `no_wraparound_depth`). Turning this
   into `NoWraparound` for an integral residue hom needs the standard fact that a mod-`𝔭`
   collision forces `p ∣ N(difference)`, which is not formalized here. Heuristically this pins the
   onset `r_0(n) ≥ ½ · p^{1/[K:ℚ]} = ½ · p^{2/n}`.

5. **Model sanity checks** — `noWraparound_of_injective` and the field-source vacuity theorems,
   `false_of_ringHom_charZero_charP`, the genuine wrap instance `int_mod_three_wrapExcess_pos`,
   and the DC-floor obstruction `not_noWraparound_of_dcFloor` / `production_dcFloor_gap_r6`.

## The saddle no-wrap statement (corrected status)

The prize needs control of `E_r` at the *saddle* depth `r* = ⌈log p⌉ = β·ln n` (`n = 2^30`,
`p ≈ n·2^128`). The *sufficient* threshold above gives no-wraparound only for `r < ½·p^{2/n}`,
which at the prize scale is `½·n^{2β/n} = O(1)` — far short of `r*`. Earlier versions named
`OnsetExceedsSaddle` (no wraparound at depth `r*`) as "the open prize core". That is withdrawn:
with a field source it is automatic, and for the production residue map it is false by the DC
floor argument above (genuine wraps already exist at depth `6`). The exact small-`n` recomputes
(`W_3 = 0` generic, onset between `4` and `6` at `n = 16`) are finite evidence about small
parameters and do not transfer. The correct open target is a quantitative DC-subtracted excess
budget at the saddle; it is not formalized in this file.

**HONEST SCOPE.** Items 1–3 and 5 are unconditional theorems of the wrap-excess *framework*; item 4
is the field-level norm bound. `energy_le_wick_of_onset` is a valid conditional implication, but its
hypothesis `OnsetExceedsSaddle` is not an open prize input: it is vacuous for field sources and false
at production. No `sorry`, no `native_decide`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026
  (ePrint 2026/680, issue #444).
- In-tree: `WraparoundThreshold.lean` (`no_wraparound_depth`, the house bound),
  `CyclotomicLatticeWrapOnset.lean` (the `ℓ¹`-lattice discrete core).
-/

open Finset NumberField Module

namespace ArkLib.ProximityGap.NoExcessOnset

/- `K` is the commutative collision ring (intended: `ℤ[ζ_n]`), `F` the carrier of the reduction.
They are deliberately NOT fields: a ring hom out of a field is injective, which would make the
wraparound excess identically zero (audit R-113). -/
variable {K F : Type*} [CommRing K] [CommRing F]

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

/-! ### Model sanity checks (audit R-113)

The predicate `NoWraparound` is only meaningful when the reduction `φ` is NOT injective. -/

/-- **An injective reduction never wraps.** If `φ` is injective then every collision after `φ` is
already a collision in the source, so `NoWraparound` holds at every depth. -/
theorem noWraparound_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ) (ζ : ι → K) :
    NoWraparound (r := r) φ ζ := by
  intro x y hxy
  apply hφ
  rw [map_pushSum, map_pushSum]
  exact hxy

/-- **Field-source vacuity.** For a field source and a nontrivial carrier, every ring hom is
injective, so `NoWraparound` is automatic: this is why the earlier field-to-field version of this
framework could not express a genuine wraparound. -/
theorem noWraparound_of_field_source {L E : Type*} [Field L] [CommRing E] [Nontrivial E]
    [DecidableEq L] [DecidableEq E] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : L →+* E) (ζ : ι → L) :
    NoWraparound (r := r) φ ζ :=
  noWraparound_of_injective φ φ.injective ζ

/-- **Field-source vacuity, excess form.** For a field source the wrap excess is identically `0`
at every depth. -/
theorem wrapExcess_eq_zero_of_field_source {L E : Type*} [Field L] [CommRing E] [Nontrivial E]
    [DecidableEq L] [DecidableEq E] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : L →+* E) (ζ : ι → L) :
    wrapExcess (r := r) φ ζ = 0 :=
  wrapExcess_eq_zero_of_noWraparound φ ζ (noWraparound_of_field_source φ ζ)

/-- **No reduction from a characteristic-`0` field to a characteristic-`p` ring.** A ring hom
`φ : L →+* E` with `CharZero L` and `CharP E p`, `p` prime, would send the nonzero (hence
invertible) element `(p : L)` to `0`, contradicting injectivity. So reduction mod `𝔭` cannot be a
ring hom on the whole number field; it lives on the integer ring. -/
theorem false_of_ringHom_charZero_charP {L E : Type*} [Field L] [CharZero L] [CommRing E]
    [Nontrivial E] {p : ℕ} [CharP E p] (hp : p.Prime) (φ : L →+* E) : False := by
  have h1 : φ (p : L) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero E p
  have h2 : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  exact h2 (φ.injective (h1.trans (map_zero φ).symm))

/-- **A genuine nonzero wrap instance.** Collision ring `ℤ`, carrier `ZMod 3`, roots `±1`
(`μ_2 ⊆ ℤ`), depth `3`: the tuples `(1,1,1)` and `(-1,-1,-1)` have sums `3 ≠ -3` in `ℤ`, but both
sums vanish in `ZMod 3`. So the generalized framework can express a positive wrap excess. -/
theorem int_mod_three_wrapExcess_pos :
    0 < wrapExcess (r := 3) (Int.castRingHom (ZMod 3)) ![(1 : ℤ), -1] := by
  unfold wrapExcess
  rw [Finset.card_pos]
  refine ⟨(fun _ => 0, fun _ => 1), ?_⟩
  simp only [collisions, Finset.mem_sdiff, mem_filter, mem_univ, true_and, pushSum]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    RingHom.id_apply, eq_intCast, Int.cast_one, Int.cast_neg]
  decide

/-- **The DC-floor obstruction to saddle no-wrap (abstract form).** Suppose the char-`0` energy is
below a Wick ceiling `wick`, the char-`p` energy obeys a DC floor `n^{2r} ≤ p·E_r`, and
`p·wick < n^{2r}`. Then there IS a genuine wraparound at depth `r`. The DC floor and the char-`0`
ceiling are hypotheses here (they are proved or claimed elsewhere in the tree for the actual
subgroup); see `production_dcFloor_gap_r6` for the production arithmetic at `r = 6`. -/
theorem not_noWraparound_of_dcFloor {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (φ : K →+* F) (ζ : ι → K) {n p wick : ℕ}
    (hchar0 : energyChar0 (r := r) ζ ≤ wick)
    (hfloor : n ^ (2 * r) ≤ p * energyCharP (r := r) φ ζ)
    (hgap : p * wick < n ^ (2 * r)) :
    ¬ NoWraparound (r := r) φ ζ := by
  intro h
  have hE : energyCharP (r := r) φ ζ ≤ wick := energyCharP_le_of_noWraparound_of_char0_le φ ζ h hchar0
  have : p * energyCharP (r := r) φ ζ ≤ p * wick := Nat.mul_le_mul_left p hE
  omega

/-- **Production arithmetic at depth `6`.** With `n = 2^30`, any `p < 2^159` and the Wick ceiling
`(2·6−1)!!·n^6 = 10395·n^6`, one has `p·10395·n^6 < n^12`; combined with
`not_noWraparound_of_dcFloor` this shows the static no-wrap statement fails at depth `6` for the
production parameters (given the DC floor and the char-`0` Wick ceiling). -/
theorem production_dcFloor_gap_r6 {p : ℕ} (hp : p < 2 ^ 159) :
    p * (10395 * (2 ^ 30) ^ 6) < (2 ^ 30) ^ (2 * 6) := by
  have h1 : p * (10395 * (2 ^ 30) ^ 6) < 2 ^ 159 * (10395 * (2 ^ 30) ^ 6) :=
    Nat.mul_lt_mul_of_pos_right hp (by positivity)
  exact lt_of_lt_of_le h1 (by norm_num)

end ArkLib.ProximityGap.NoExcessOnset

/-! ## The arithmetic onset threshold — wiring to the in-tree house bound

We record the explicit threshold `(2r)^{[K:ℚ]} < p` proven in `WraparoundThreshold.lean`. It is a
field-level statement about a number field `K` (no reduction map appears). A bridge to
`NoWraparound` would use the integral residue hom `𝓞_K → 𝓞_K/𝔭` (the collision ring of the
framework above is then `𝓞_K`) and the fact that a mod-`𝔭` collision forces `p ∣ N(D)`; neither is
formalized here. The clean algebraic core (`no_wraparound_depth`) shows that under the house
threshold a nonzero difference has norm of absolute value `< p`, so it cannot be `p`-divisible.
-/

namespace ArkLib.ProximityGap.NoExcessOnset

open ArkLib.ProximityGap.Wraparound

variable {K : Type*} [Field K] [NumberField K]

/-- **The house onset bound (norm form), restated for the excess framework.** For two depth-`r`
tuples of `n`-th roots of unity (`n ≠ 0`) whose sums are *distinct in `K`*, the house bound
`no_wraparound_depth` says: once `(2r)^{[K:ℚ]} < p`, the norm of the difference is a nonzero
rational integer of absolute value `< p`. Hence no prime `𝔭 ∣ p` identifies them: the only mod-`𝔭`
collisions are char-`0` collisions. This would give `NoWraparound` for the integral residue hom on
`𝓞_K`, given the standard (unformalized here) fact that a mod-`𝔭` collision forces
`p ∣ N(difference)`. -/
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

/-! ## The saddle no-wrap statement — NOT the prize (corrected 2026-10-28, audit R-113)

The *sufficient* house threshold `OnsetThresholdMet` gives no-wraparound only for `r < ½·p^{2/n}`,
which is `O(1)` at the prize scale (`p = n^β`, `½·n^{2β/n} → ½·n^{o(1)}`). Earlier versions named
"`r_0(n) > r*`" (no wraparound at the saddle depth) as the open prize input. That is withdrawn:
for a field source the predicate is automatic (`onsetExceedsSaddle_of_field_source`), and for the
production integral residue map it is false — the DC floor forces `W_6 > 0` at `n = 2^30`,
`p < 2^159` (`not_noWraparound_of_dcFloor`, `production_dcFloor_gap_r6`), and padding propagates
the wrap to the saddle. The correct open target is a quantitative DC-subtracted excess budget. The
conditional implication below is kept because it is valid as an implication.
-/

namespace ArkLib.ProximityGap.NoExcessOnset

variable {K F : Type*} [CommRing K] [CommRing F] [DecidableEq K] [DecidableEq F]

/-- **Static saddle no-wrap predicate (NOT the prize).** `OnsetExceedsSaddle φ ζ r*` asserts that
at depth `r*` there is *no* wrap-around — every collision after `φ` of depth-`r*` root sums is
already a collision in the source ring. For a field source this is automatic
(`onsetExceedsSaddle_of_field_source`); for the production residue map `ℤ[ζ_n] → F_p` at the saddle
depth it is false by the DC floor (see the module docstring and `not_noWraparound_of_dcFloor`).
Earlier versions called this "the open prize core"; that claim is withdrawn. The live open target
is a quantitative DC-subtracted excess budget, not formalized here. -/
def OnsetExceedsSaddle {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* F) (ζ : ι → K) (rStar : ℕ) : Prop :=
  NoWraparound (r := rStar) φ ζ

/-- **Conditional implication.** If there is no wrap at depth `r*` (`OnsetExceedsSaddle`) and the
char-`0` Wick bound holds at `r*` (hypothesis), then the char-`p` energy at depth `r*` is `≤ Wick`.
Valid as an implication, but NOT a reduction of the prize to an open input: the hypothesis is
vacuous for field sources and false at production parameters (audit R-113). -/
theorem energy_le_wick_of_onset {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* F) (ζ : ι → K) (rStar : ℕ)
    (honset : OnsetExceedsSaddle φ ζ rStar) {wick : ℕ}
    (hchar0 : energyChar0 (r := rStar) ζ ≤ wick) :
    energyCharP (r := rStar) φ ζ ≤ wick :=
  energyCharP_le_of_noWraparound_of_char0_le φ ζ honset hchar0

/-- **Explicit `W_{r*} = 0` form of the conditional implication.** Under the (non-prize, see above)
no-wrap hypothesis the depth-`r*` wrap-excess vanishes. -/
theorem wrapExcess_saddle_eq_zero_of_onset {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : K →+* F) (ζ : ι → K)
    (rStar : ℕ) (honset : OnsetExceedsSaddle φ ζ rStar) :
    wrapExcess (r := rStar) φ ζ = 0 :=
  wrapExcess_eq_zero_of_noWraparound φ ζ honset

/-- **The old "prize core" is a theorem for field sources.** With a field source (the original,
defective model), `OnsetExceedsSaddle` holds for every hom and every depth. -/
theorem onsetExceedsSaddle_of_field_source {L E : Type*} [Field L] [CommRing E] [Nontrivial E]
    [DecidableEq L] [DecidableEq E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : L →+* E) (ζ : ι → L) (rStar : ℕ) :
    OnsetExceedsSaddle φ ζ rStar :=
  noWraparound_of_field_source φ ζ

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
#print axioms ArkLib.ProximityGap.NoExcessOnset.noWraparound_of_injective
#print axioms ArkLib.ProximityGap.NoExcessOnset.wrapExcess_eq_zero_of_field_source
#print axioms ArkLib.ProximityGap.NoExcessOnset.false_of_ringHom_charZero_charP
#print axioms ArkLib.ProximityGap.NoExcessOnset.int_mod_three_wrapExcess_pos
#print axioms ArkLib.ProximityGap.NoExcessOnset.not_noWraparound_of_dcFloor
#print axioms ArkLib.ProximityGap.NoExcessOnset.production_dcFloor_gap_r6
#print axioms ArkLib.ProximityGap.NoExcessOnset.onsetExceedsSaddle_of_field_source
