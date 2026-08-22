/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishRigidityModP

/-!
# Aggregate count-transfer of the `e₂ = 0` rigidity (#444 -- F10 minimal-relation rigidity)

`E2VanishRigidityModP` proves the **per-`U`** rigidity transfer: for an exponent set
`U ⊆ range(2^k)` whose folded `e₂`-relation is nonzero in characteristic `0`
(`e2Fold k U ≠ 0`), and a prime `p > ((card U)² + card U)^{2^{k−1}}` with a primitive `2^k`-th
root `g`, the `e₂ = 0` condition `(∑_{i∈U} g^i)² = ∑_{i∈U} g^{2i}` **fails** mod `p` -- there is no
*new* mod-`p` `e₂ = 0` solution beyond the char-`0` ones.

That file's docstring then asserts, in **prose only**, the aggregate consequence:

> *"Above that explicit threshold the `e₂ = 0` subsets over `F_p` are exactly the char-`0` ones,
> so the extremal-radius `e₂ = 0` count ... is the char-`0` count -- an absolute, `q`-independent
> constant."*

This file turns that prose into a **theorem**: over the whole family of bounded-width exponent
sets, the mod-`p` `e₂ = 0` filter **equals** the char-`0` `e₂ = 0` filter (hence equal
cardinality), for every prime above the *uniform* width-`w` threshold. This is exactly the F10
(Conway–Jones / Poonen–Rubinstein) **minimal-relation rigidity** statement at depth 2 in its
aggregate-count form: the count of vanishing weight-`≤ w` `e₂`-relations is `q`-independent above
an explicit, finite, `n`-dependent threshold: **no BGK character-sum wall on this algebraic face**.

## What is genuinely new here (vs. the per-`U` `E2VanishRigidityModP`)
- `e2Fold_eq_zero_of_charZero` -- the char-`0` **converse** of `e2Fold_ne_zero`: a char-`0` `e₂ = 0`
  set has `e2Fold k U = 0` (degree `< deg Φ_{2^k}` ⟹ a root at a primitive `2^k`-th root forces the
  zero polynomial). The per-`U` file only had the non-vanishing direction.
- `e2Cond_modp_iff_charZero` -- the per-`U` **two-sided** transfer above threshold (mod-`p`
  condition `↔` char-`0` condition), packaging the in-tree `e2_zero_rigidity_modp` (⟸-contra) with
  the new converse (⟹).
- `e2zero_filter_modp_eq_charZero` (HEADLINE) -- the **aggregate filter equality** over the whole
  bounded-width family `{U ∈ powersetCard ... range(2^k) : card U ≤ w}`, for `p` above the *uniform*
  threshold `(w² + w)^{2^{k−1}}`.
- `e2zero_count_modp_eq_charZero` -- the count corollary: `#(mod-p e₂=0) = #(char-0 e₂=0)` over the
  bounded-width family -- the `q`-independent census the prose claimed.

## Honest scope (rules 1, 3, 6 + asymptotic guard)
This is **NOT** a CORE closure and makes no sup-norm / BGK claim. It is a NON-MOMENT *algebraic*
rigidity count: it establishes that on the `e₂ = 0` (weight-2 collision) algebraic face there is no
char-`p` wall -- the locus is `q`-independent above an explicit threshold. The genuine prize wall
lives on the **analytic** sup-norm `M(μ_n)` face, untouched here. The threshold `(w²+w)^{2^{k−1}}`
is the crude (provable) resultant bound; the true crossover is `≈ n³` (probe-measured, a separate
sharpening lane), so in the prize regime `q ≈ n·2^{128} ≫ n³` the equality holds with massive
margin. No capacity / cliff-at-n/2 claim. Field-universal algebraic identity.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Polynomial Finset

attribute [local instance] Classical.propDecidable

namespace ArkLib.ProximityGap.E2RigidityCountTransfer

open ArkLib.ProximityGap.E2VanishRigidityModP

/-! ## The char-`0` converse: a vanishing `e₂` set folds to the zero polynomial -/

/-- **The char-`0` converse of `e2Fold_ne_zero`.** If the `e₂ = 0` condition holds in
characteristic `0` (at a primitive complex `2^k`-th root `ζ`), then the folded integer relation is
the **zero polynomial**. Mechanism: `e2Fold k U` has degree `< 2^{k−1} = deg Φ_{2^k}` and (via
`e2Fold_eval`) has `ζ` as a root; a polynomial of degree below the minimal polynomial of `ζ`
vanishing at `ζ` must be `0`. -/
theorem e2Fold_eq_zero_of_charZero {k : ℕ} (hk : 1 ≤ k) {U : Finset ℕ}
    (hU : ∀ i ∈ U, i < 2 ^ k) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hC : (∑ i ∈ U, ζ ^ i) ^ 2 = ∑ i ∈ U, ζ ^ (2 * i)) :
    e2Fold k U = 0 := by
  by_contra hne
  -- `ζ` is integral over `ℤ` (it is a root of unity), so its minimal polynomial divides any
  -- integer polynomial annihilating it.
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hint : IsIntegral ℤ ζ := hζ.isIntegral hpos
  -- `aeval ζ (e2Fold k U) = 0` (the fold evaluates to `(∑ζ^i)² − ∑ζ^{2i}` = 0 under `hC`).
  have haeval : (Polynomial.aeval ζ) (e2Fold k U) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    have : (algebraMap ℤ ℂ) = Int.castRingHom ℂ := rfl
    rw [this, e2Fold_eval hk hζ hU, hC, sub_self]
  -- ℤ is integrally closed, so `minpoly ℤ ζ ∣ e2Fold k U`.
  have hdvd : minpoly ℤ ζ ∣ e2Fold k U := minpoly.isIntegrallyClosed_dvd hint haeval
  -- Hence `deg (minpoly ℤ ζ) ≤ deg (e2Fold k U) < 2^{k-1}`.
  have hdegle : (minpoly ℤ ζ).natDegree ≤ (e2Fold k U).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hne
  -- But `totient (2^k) = 2^{k-1} ≤ deg (minpoly ℤ ζ)`.
  have htot : Nat.totient (2 ^ k) ≤ (minpoly ℤ ζ).natDegree := hζ.totient_le_degree_minpoly
  have htotval : Nat.totient (2 ^ k) = 2 ^ (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < j + 1)]
    simp
  have hlt := e2Fold_natDegree_lt k U
  omega

/-! ## The per-`U` two-sided transfer above threshold -/

/-- **The per-`U` two-sided transfer.** For `p > ((card U)² + card U)^{2^{k−1}}`, with `g` a
primitive `2^k`-th root mod `p` and `ζ` a primitive complex `2^k`-th root, the `e₂ = 0` condition
holds **mod `p`** iff it holds in **characteristic `0`**. The `⇐` (char-`0` ⇒ mod-`p`) direction is
the new converse `e2Fold_eq_zero_of_charZero` evaluated mod `p` via the faithful fold; the `⇒`
(mod-`p` ⇒ char-`0`) direction is the contrapositive of the in-tree `e2_zero_rigidity_modp`. -/
theorem e2Cond_modp_iff_charZero {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {U : Finset ℕ}
    (hU : ∀ i ∈ U, i < 2 ^ k) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hp : (U.card ^ 2 + U.card) ^ 2 ^ (k - 1) < p) :
    ((∑ i ∈ U, g ^ i) ^ 2 = ∑ i ∈ U, g ^ (2 * i))
      ↔ ((∑ i ∈ U, ζ ^ i) ^ 2 = ∑ i ∈ U, ζ ^ (2 * i)) := by
  constructor
  · -- mod-`p` ⇒ char-`0`: contrapositive of rigidity.
    intro hFp
    by_contra hCnz
    exact e2_zero_rigidity_modp hk hg hU (e2Fold_ne_zero hk hU hζ hCnz) hp hFp
  · -- char-`0` ⇒ mod-`p`: the fold is the zero polynomial, so it evaluates to `0` mod `p` too.
    intro hC
    have h0 : e2Fold k U = 0 := e2Fold_eq_zero_of_charZero hk hU hζ hC
    have heval := e2Fold_eval hk hg hU
    rw [h0] at heval
    simp only [Polynomial.map_zero, Polynomial.eval_zero] at heval
    linear_combination -heval

/-! ## The aggregate filter equality + count over the bounded-width family -/

/-- The exponent-set family: subsets of `range (2^k)` of width `≤ w`. -/
def widthLeFamily (k w : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (2 ^ k)).powerset.filter (fun U => U.card ≤ w)

/-- The mod-`p` `e₂ = 0` predicate on exponent sets (at the primitive root `g`). -/
def e2CondModP {p : ℕ} (g : ZMod p) (U : Finset ℕ) : Prop :=
  (∑ i ∈ U, g ^ i) ^ 2 = ∑ i ∈ U, g ^ (2 * i)

/-- The char-`0` `e₂ = 0` predicate on exponent sets (at the primitive root `ζ`). -/
def e2CondC (ζ : ℂ) (U : Finset ℕ) : Prop :=
  (∑ i ∈ U, ζ ^ i) ^ 2 = ∑ i ∈ U, ζ ^ (2 * i)

/-- **HEADLINE -- the aggregate filter equality.** Above the *uniform* width-`w` threshold
`(w² + w)^{2^{k−1}}`, the mod-`p` `e₂ = 0` subfamily of `widthLeFamily k w` **equals** the
char-`0` `e₂ = 0` subfamily. The mod-`p` `e₂ = 0` locus on bounded-width sets is *literally* the
char-`0` locus -- no new mod-`p` collisions appear. -/
theorem e2zero_filter_modp_eq_charZero {p : ℕ} [Fact p.Prime] {k w : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hp : (w ^ 2 + w) ^ 2 ^ (k - 1) < p) :
    (widthLeFamily k w).filter (fun U => e2CondModP g U)
      = (widthLeFamily k w).filter (fun U => e2CondC ζ U) := by
  classical
  apply Finset.filter_congr
  intro U hU
  simp only [widthLeFamily, Finset.mem_filter, Finset.mem_powerset] at hU
  obtain ⟨hsub, hcard⟩ := hU
  have hUlt : ∀ i ∈ U, i < 2 ^ k := by
    intro i hi
    have := hsub hi
    simpa [Finset.mem_range] using this
  -- the per-`U` threshold is dominated by the uniform one (monotone in `card U ≤ w`).
  have hpU : (U.card ^ 2 + U.card) ^ 2 ^ (k - 1) < p := by
    refine lt_of_le_of_lt ?_ hp
    exact Nat.pow_le_pow_left (by nlinarith [hcard]) _
  unfold e2CondModP e2CondC
  exact (e2Cond_modp_iff_charZero hk hg hUlt hζ hpU)

/-- **The count corollary** -- the prose claim made a theorem: above the uniform threshold the
mod-`p` `e₂ = 0` count over the bounded-width family **equals** the char-`0` count, an absolute,
`q`-independent (`p`-independent) constant. -/
theorem e2zero_count_modp_eq_charZero {p : ℕ} [Fact p.Prime] {k w : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hp : (w ^ 2 + w) ^ 2 ^ (k - 1) < p) :
    ((widthLeFamily k w).filter (fun U => e2CondModP g U)).card
      = ((widthLeFamily k w).filter (fun U => e2CondC ζ U)).card := by
  rw [e2zero_filter_modp_eq_charZero hk hg hζ hp]

end ArkLib.ProximityGap.E2RigidityCountTransfer

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.E2RigidityCountTransfer.e2Fold_eq_zero_of_charZero
#print axioms ArkLib.ProximityGap.E2RigidityCountTransfer.e2Cond_modp_iff_charZero
#print axioms ArkLib.ProximityGap.E2RigidityCountTransfer.e2zero_filter_modp_eq_charZero
#print axioms ArkLib.ProximityGap.E2RigidityCountTransfer.e2zero_count_modp_eq_charZero
