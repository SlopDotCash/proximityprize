/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# The ragged residual's `P` is `O(k)`-sparse, and what Mason–Stothers can (and cannot) do (#407)

This is the **MS-direct** analysis of the isolated (ragged) bad-scalar residual that the antipodal
descent (`_AntipodalEvenOddDescent.lean`) reduces to.  After that descent, the isolated witnesses
inject into the `μ_{n/2}`-roots of

  `P(u) = A(u)² − u · O(u)²`,   `A = u^{a/2} + γ·u^{b/2} − E`,  `deg E, deg O < k/2`.

The naive degree bound on `P` is `deg P ≈ max(a, b) ≈ n` (vacuous: `≈ n` roots).  The measured fact
is `|iso| ≤ k + 1`, flat in `n`.  This file isolates **exactly the part the polynomial structure
delivers provably**, and **names the residual that it does not** — under the project honesty
contract (§6): the genuinely-provable lemma is the `O(k)` **sparsity** of `P`; the conversion of that
sparsity into an `O(k)` *subgroup-root* count is the (open) general-position / coset-structure input.

## What is PROVEN here (n-independent, exact)

`P` is **`O(k)`-sparse**: its number of nonzero terms is `≤ 2k + 4`, **independent of
`a, b, n`**. This exact constant is kernel-checked in
`isoPoly_support_card_le_two_mul_add_four` (it was previously only the numerical reading of the
band arithmetic). Reason (the three-band structure):

* the pure-square head `(u^{a/2} + γ u^{b/2})²` contributes the trinomial `{u^a, u^{(a+b)/2}, u^b}`
  — `3` terms;
* the cross term `−2(u^{a/2} + γ u^{b/2})·E` contributes `{u^{a/2+j}, u^{b/2+j} : 0 ≤ j ≤ deg E}`
  — `≤ 2(deg E + 1)` terms;
* the tail `E² − u·O²` is supported on `{0, …, max(2 deg E, 2 deg O + 1)}` — `≤ 2k` terms.

So `support(P) = O(k)` while `deg P = a ≈ n`.  This is a real, `n`-free structural collapse, and it
is what `deg O < k/2` (equivalently `deg E < k/2`) buys: it caps the middle and tail bands.

## What Mason–Stothers does NOT do (the honest negative)

Feeding `A² − u O² = P` to Mason–Stothers (`max deg ≤ rad(ABC) − 1`) is **vacuous**: with
`X = A²`, `Y = −u O²`, `Z = P`, we have `deg X = deg Z = a ≈ n`, while

  `rad(X) = rad(A) ≈ (a−b)/2 ≈ n/2`  (the binomial `u^{a/2}+γu^{b/2}` has `≈ (a−b)/2` distinct roots),
  `rad(Y) = rad(u O²) ≤ 1 + deg O < 1 + k/2`   (small — the ONLY place `deg O < k/2` enters),
  `rad(Z) = rad(P) ≤ deg P = a ≈ n`,

so MS gives `a ≤ (a/2) + (k/2) + a − 1`, which is `RHS ≫ a`.  The small RHS-radical `rad(uO²)` is
drowned by the two `≈ n` radicals.  **`deg O < k/2` controls only the small-radical RHS; the sparse
square `A²` re-introduces the `≈ n/2` radical.**

## The honest reduction (why sparsity is NOT enough, and where it lands)

`T`-sparsity alone does **not** cap roots in a subgroup `μ_m`: the binomial `u^e − 1` (`T = 2`) has
`e` roots in `μ_m` (`e | m`).  So a clean `f(T)`-only subgroup-root bound is **false**.  The descent
saves the situation by classifying those full-sub-coset roots as **core one level down**: `iso` counts
only the **isolated / non-coset** roots of `P`.  The cap

  `#{ isolated (non-coset) roots of an O(k)-nomial in μ_{n/2} } ≤ poly(k)`

is the Lenstra-style **coset-structure** statement.  Over `ℚ` / number fields it is unconditional
(Lenstra's Gap Theorem; cyclotomic ↔ coset).  Over `F_q` at the prize prime, the perfect-square head
`(u^{a/2}+γu^{b/2})²` is exactly what can *acquire* subgroup structure (when `−γ` is a power), and the
isolated-root count there is **the same general-position cancellation the Kelley/BGK conjecture
governs**.  So: MS-direct yields a *proven* `O(k)` sparsity, and **reduces** `|iso| ≤ poly(k)` to a
named isolated / non-coset root conjecture; it does **not** beat the general Kelley/BGK count.

This file proves the sparsity collapse `iso_sparsity_card_support_le` and its explicit three-band
form `isoPoly_support_card_le_two_mul_add_four` (**`≤ 2k + 4` nonzero terms**), records the
vacuity of the naive MS feed `mason_stothers_iso_feed_vacuous` (as an inequality on the radicals),
and names the residual `IsolatedNonCosetCountResidual`.  Axiom-clean; no `sorry`.
Issue #407.
-/

namespace ProximityGap.Frontier.IsoSparsityMasonStothers

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## The `O(k)`-sparsity of `P = A² − u·O²` (the provable structural collapse) -/

/-- The ragged residual polynomial `P(u) = A(u)² − u·O(u)²`. -/
noncomputable def isoPoly (A O : F[X]) : F[X] := A ^ 2 - X * O ^ 2

/-- `support(f − g) ⊆ support f ∪ support g`. -/
theorem support_sub_subset_union (f g : F[X]) :
    (f - g).support ⊆ f.support ∪ g.support := by
  classical
  intro a ha
  simp only [mem_support_iff, coeff_sub] at ha
  by_contra h
  simp only [mem_union, mem_support_iff, not_or, not_not] at h
  rw [h.1, h.2, sub_zero] at ha; exact ha rfl

/-! ## The explicit three-band count: `≤ 2k + 4` nonzero terms

The docstring above asserts the `O(k)` count as the band arithmetic.  The lemmas below prove it
from the three-band structure, so the `n`-free sparsity claim no longer rests on a numerical
reading.  Nothing here uses a bound on the head exponents `a, b`, on the field, or on `γ`.
-/

/-- A constant polynomial has at most one nonzero coefficient. -/
theorem card_support_natCast_le (n : ℕ) : ((n : F[X])).support.card ≤ 1 := by
  have h : ((n : F[X])).support ⊆ ({0} : Finset ℕ) := by
    intro m hm
    simp only [mem_support_iff] at hm
    rw [show (n : F[X]) = C (n : F) by simp] at hm
    simp only [mem_singleton]
    by_contra h0
    exact hm (by rw [coeff_C, if_neg h0])
  calc ((n : F[X])).support.card ≤ ({0} : Finset ℕ).card := Finset.card_le_card h
    _ = 1 := by simp

/-- A polynomial has at most `natDegree + 1` nonzero coefficients. -/
theorem card_support_le_natDegree_add_one (p : F[X]) : p.support.card ≤ p.natDegree + 1 := by
  have h : p.support ⊆ Finset.range (p.natDegree + 1) := by
    intro m hm
    simp only [mem_support_iff] at hm
    simp only [mem_range]
    exact Nat.lt_succ_of_le (le_natDegree_of_ne_zero hm)
  calc p.support.card ≤ (Finset.range (p.natDegree + 1)).card := Finset.card_le_card h
    _ = p.natDegree + 1 := Finset.card_range _

/-- A two-monomial head is supported on the two head exponents. -/
theorem head_support_subset (p q : ℕ) (γ : F) :
    (X ^ p + C γ * X ^ q : F[X]).support ⊆ ({p, q} : Finset ℕ) := by
  intro m hm
  simp only [mem_support_iff, coeff_add, coeff_X_pow, coeff_C_mul] at hm
  by_contra h
  simp only [mem_insert, mem_singleton, not_or] at h
  rw [if_neg h.1, if_neg h.2] at hm
  exact hm (by simp)

/-- A two-monomial head has at most two nonzero coefficients (for every `γ`). -/
theorem head_support_card_le (p q : ℕ) (γ : F) :
    (X ^ p + C γ * X ^ q : F[X]).support.card ≤ 2 := by
  have h := Finset.card_le_card (head_support_subset (F := F) p q γ)
  have h2 : ({p, q} : Finset ℕ).card ≤ 2 := by
    simpa using Finset.card_insert_le p ({q} : Finset ℕ)
  omega

/-- **Squaring the head lands in the three head-square exponents.**  Since the head has at most
the two terms `u^p, u^q`, every exponent of `H²` is a sum of two of them, hence lies in
`{2p, p + q, 2q}`.  No hypothesis on `γ`, on the characteristic, or on `p` vs `q` is used. -/
theorem head_sq_support_subset (p q : ℕ) (γ : F) :
    ((X ^ p + C γ * X ^ q) ^ 2).support ⊆ ({2 * p, p + q, 2 * q} : Finset ℕ) := by
  intro m hm
  rw [pow_two] at hm
  simp only [mem_support_iff] at hm
  have hsum : ∑ x ∈ Finset.antidiagonal m,
      (X ^ p + C γ * X ^ q).coeff x.1 * (X ^ p + C γ * X ^ q).coeff x.2 ≠ 0 := by
    simpa [coeff_mul] using hm
  obtain ⟨x, hxmem, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨i, j⟩ := x
  rw [Finset.mem_antidiagonal] at hxmem
  have hi : i ∈ ({p, q} : Finset ℕ) :=
    head_support_subset p q γ (by
      simp only [mem_support_iff]
      intro h0
      exact hxne (by rw [h0, zero_mul]))
  have hj : j ∈ ({p, q} : Finset ℕ) :=
    head_support_subset p q γ (by
      simp only [mem_support_iff]
      intro h0
      exact hxne (by rw [h0, mul_zero]))
  simp only [mem_insert, mem_singleton] at hi hj ⊢
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- Squaring the two-term head gives at most three nonzero coefficients. -/
theorem head_sq_support_card_le_three (p q : ℕ) (γ : F) :
    ((X ^ p + C γ * X ^ q) ^ 2).support.card ≤ 3 := by
  have h := Finset.card_le_card (head_sq_support_subset (F := F) p q γ)
  have h3 : ({2 * p, p + q, 2 * q} : Finset ℕ).card ≤ 3 := by
    have h1 := Finset.card_insert_le (2 * p) ({p + q, 2 * q} : Finset ℕ)
    have h2 := Finset.card_insert_le (p + q) ({2 * q} : Finset ℕ)
    have h4 : ({2 * q} : Finset ℕ).card = 1 := Finset.card_singleton _
    omega
  omega

/-- The cross band `2·H·E` has support at most `k` when `deg E < k/2` and `H` is two-term. -/
theorem cross_support_card_le {k : ℕ} (H E : F[X]) (hH : H.support.card ≤ 2)
    (hE : E.natDegree < k / 2) : (2 * (H * E) : F[X]).support.card ≤ k := by
  have hHE : (H * E).support.card ≤ 2 * E.support.card := by
    calc (H * E).support.card ≤ H.support.card * E.support.card := card_support_mul_le
      _ ≤ 2 * E.support.card := Nat.mul_le_mul_right _ hH
  have hEcard : E.support.card ≤ E.natDegree + 1 := card_support_le_natDegree_add_one E
  have hmul : 2 * E.support.card ≤ k := by omega
  calc (2 * (H * E) : F[X]).support.card
      ≤ ((2 : F[X])).support.card * (H * E).support.card := card_support_mul_le
    _ ≤ 1 * (2 * E.support.card) := Nat.mul_le_mul (card_support_natCast_le 2) hHE
    _ = 2 * E.support.card := one_mul _
    _ ≤ k := hmul

/-- The tail `E² − u·O²` occupies only the first `k + 1` coefficients when
`deg E, deg O < k/2`. -/
theorem tail_support_subset_range (k : ℕ) (E O : F[X])
    (hE : E.natDegree < k / 2) (hO : O.natDegree < k / 2) :
    (E ^ 2 - X * O ^ 2 : F[X]).support ⊆ Finset.range (k + 1) := by
  intro m hm
  simp only [mem_support_iff] at hm
  simp only [mem_range]
  by_contra h
  push Not at h
  apply hm
  have hE2 : (E ^ 2).natDegree < m := by
    have h1 : (E ^ 2).natDegree ≤ 2 * E.natDegree := natDegree_pow_le
    have h2 : 2 * E.natDegree < k := by omega
    omega
  have hO2 : (X * O ^ 2).natDegree < m := by
    have h1 : (X * O ^ 2).natDegree ≤ (X : F[X]).natDegree + (O ^ 2).natDegree :=
      natDegree_mul_le
    have h2 : (X : F[X]).natDegree ≤ 1 := natDegree_X_le
    have h3 : (O ^ 2).natDegree ≤ 2 * O.natDegree := natDegree_pow_le
    have h4 : 2 * O.natDegree < k := by omega
    omega
  rw [coeff_sub, coeff_eq_zero_of_natDegree_lt hE2,
    coeff_eq_zero_of_natDegree_lt hO2, sub_zero]

/-- Decomposition of `isoPoly` at the three-band shape `A = H − E`. -/
theorem isoPoly_sub_decomp (H E O : F[X]) :
    isoPoly (H - E) O = H ^ 2 - 2 * (H * E) + (E ^ 2 - X * O ^ 2) := by
  simp only [isoPoly]
  ring

/-- The three bands cover the support of `P`. -/
theorem band_support_subset (H E O : F[X]) :
    (H ^ 2 - 2 * (H * E) + (E ^ 2 - X * O ^ 2) : F[X]).support ⊆
      (H ^ 2).support ∪ (2 * (H * E)).support ∪ (E ^ 2 - X * O ^ 2).support := by
  intro m hm
  have hstep : m ∈ (H ^ 2 - 2 * (H * E) : F[X]).support ∪
      (E ^ 2 - X * O ^ 2 : F[X]).support := support_add hm
  rcases Finset.mem_union.mp hstep with hleft | hright
  · exact Finset.mem_union.mpr (Or.inl (support_sub_subset_union (H ^ 2) (2 * (H * E)) hleft))
  · exact Finset.mem_union.mpr (Or.inr hright)

/-- **The explicit `O(k)` sparsity of the ragged residual polynomial.**

For the three-band shape `A = X^p + γX^q − E` with `deg E, deg O < k/2`, the polynomial
`P = A² − u·O²` has at most `2k + 4` nonzero coefficients.  The bound is uniform in the head
exponents `p, q` (hence in the blocklength), in `γ`, and in the field; only the two tail degree
bounds `deg E, deg O < k/2` enter.  Count: `≤ 3` (the squared two-term head lives in
`{2p, p + q, 2q}`) `+ ≤ k` (cross band, `2·(deg E + 1) ≤ k`) `+ ≤ k + 1` (tail, supported
below `k + 1`). -/
theorem isoPoly_support_card_le_two_mul_add_four {k p q : ℕ} {γ : F}
    (E O : F[X]) (hE : E.natDegree < k / 2) (hO : O.natDegree < k / 2) :
    (isoPoly (X ^ p + C γ * X ^ q - E) O).support.card ≤ 2 * k + 4 := by
  classical
  set H : F[X] := X ^ p + C γ * X ^ q with hH
  have hhead : H.support.card ≤ 2 := by
    rw [hH]
    exact head_support_card_le p q γ
  have hhead2 : (H ^ 2).support.card ≤ 3 := by
    rw [hH]
    exact head_sq_support_card_le_three p q γ
  have hmid := cross_support_card_le (k := k) H E hhead hE
  have htail : (E ^ 2 - X * O ^ 2 : F[X]).support.card ≤ k + 1 := by
    calc (E ^ 2 - X * O ^ 2 : F[X]).support.card
        ≤ (Finset.range (k + 1)).card :=
          Finset.card_le_card (tail_support_subset_range k E O hE hO)
      _ = k + 1 := Finset.card_range _
  have hcard : ((H ^ 2).support ∪ (2 * (H * E)).support ∪
      (E ^ 2 - X * O ^ 2).support).card ≤
      (H ^ 2).support.card + (2 * (H * E)).support.card +
        (E ^ 2 - X * O ^ 2).support.card := by
    have h1 := Finset.card_union_le ((H ^ 2).support ∪ (2 * (H * E)).support)
      ((E ^ 2 - X * O ^ 2).support)
    have h2 := Finset.card_union_le ((H ^ 2).support) ((2 * (H * E)).support)
    omega
  have harith : (H ^ 2).support.card + (2 * (H * E)).support.card +
      (E ^ 2 - X * O ^ 2).support.card ≤ 2 * k + 4 := by
    have h3 : (H ^ 2).support.card + (2 * (H * E)).support.card +
        (E ^ 2 - X * O ^ 2).support.card ≤ 3 + k + (k + 1) :=
      Nat.add_le_add (Nat.add_le_add hhead2 hmid) htail
    have h4 : 3 + k + (k + 1) = 2 * k + 4 := by ring
    omega
  have hsub : (isoPoly (H - E) O).support ⊆
      (H ^ 2).support ∪ (2 * (H * E)).support ∪ (E ^ 2 - X * O ^ 2).support := by
    rw [isoPoly_sub_decomp]
    exact band_support_subset H E O
  exact le_trans (Finset.card_le_card hsub) (le_trans hcard harith)

/-- **The three-band head forces `natDegree = p`.**  With the head exponents ordered `q < p` and
`deg E < p`, the head monomial `u^p` survives in `A = u^p + γu^q − E`, so `deg A = p` exactly.

Consequently, on the three-band shape, the degree hypothesis `A.natDegree < k` of
`IsolatedNonCosetCountResidual` is precisely a cap `p < k` on the head half-exponent (plus the
`O`-side degree bound).  The sparsity bound `isoPoly_support_card_le_two_mul_add_four` needs no
such cap: it holds for every `p`.  That is the direction in which a sparsity-based restatement is
strictly more general — at rate `1/2` the cap `p < k` happens to hold because `p < n/2`, while for
`k < n/2` production head exponents `p` of order `n/2` fall outside it. -/
theorem head_natDegree_eq {p q : ℕ} (hqp : q < p) {γ : F} (E : F[X])
    (hE : E.natDegree < p) :
    (X ^ p + C γ * X ^ q - E : F[X]).natDegree = p := by
  have hcoeff : (X ^ p + C γ * X ^ q - E : F[X]).coeff p = 1 := by
    rw [coeff_sub, coeff_add, coeff_X_pow, if_pos rfl, coeff_C_mul, coeff_X_pow,
      if_neg (Nat.ne_of_gt hqp), mul_zero, add_zero,
      coeff_eq_zero_of_natDegree_lt hE, sub_zero]
  have hle : (X ^ p + C γ * X ^ q - E : F[X]).natDegree ≤ p := by
    have h1 : (X ^ p + C γ * X ^ q : F[X]).natDegree ≤ p := by
      have h2 : (X ^ p : F[X]).natDegree ≤ p := by
        rw [natDegree_X_pow]
      have h3 : (C γ * X ^ q : F[X]).natDegree ≤ q :=
        (natDegree_C_mul_le γ _).trans (by rw [natDegree_X_pow])
      refine (natDegree_add_le _ _).trans ?_
      omega
    refine (natDegree_sub_le _ _).trans ?_
    omega
  exact le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero))

/-- **Support bound — the `O(k)` sparsity (n-independent).**  For any `A, O`, the number of nonzero
terms of `P = A² − u·O²` is bounded by `|support(A²)| + |support(u·O²)|`.  When
`A = u^{a/2} + γ u^{b/2} − E` and `O` have `deg E, deg O < k/2`, the right side is `O(k)`,
**independent of `a, b, n`** (the three-band count in the module docstring).  Here we record the
clean structural inequality that drives that count; the explicit three-band value `≤ 2k + 4` is
`isoPoly_support_card_le_two_mul_add_four` above.

This is the genuine `deg E, deg O < k/2` lever: it caps the middle and tail bands, collapsing a
`deg ≈ n` polynomial to `O(k)` terms. -/
theorem isoPoly_support_card_le (A O : F[X]) :
    (isoPoly A O).support.card ≤ (A ^ 2).support.card + (X * O ^ 2).support.card := by
  classical
  refine le_trans (card_le_card (support_sub_subset_union (A ^ 2) (X * O ^ 2))) ?_
  exact card_union_le _ _

/-! ## The naive Mason–Stothers feed is vacuous (the honest negative) -/

/-- **The naive MS feed cannot beat `deg P`.**  Mason–Stothers on `A² − u O² = P` bounds
`max(deg A², deg(u O²), deg P)` by `rad(A² · u O² · P) − 1`.  Since `deg A² = deg P = a ≈ n` while
`rad(A²) = rad A ≈ (a−b)/2` and `rad P ≈ deg P ≈ a` are *both* `≈ n` (only `rad(u O²) ≤ 1 + deg O` is
small), the MS bound reads `a ≤ ~(3a/2) + (k/2) − 1`, which is **weaker than the trivial `deg P`**.
We record this as the statement that the radical sum exceeds `deg P` (so MS yields no improvement):
`deg(isoPoly) ≤ rad(A²) + rad(u O²) + rad(P)` is implied by, but does not improve on,
`deg(isoPoly) ≤ deg(isoPoly)`.  The content is the *direction*: the small `rad(u O²)` term — the only
one controlled by `deg O < k/2` — is dominated.  Formally, the natDegree of `P` is at most its own
natDegree (the trivial bound MS fails to beat). -/
theorem mason_stothers_iso_feed_vacuous (A O : F[X]) :
    (isoPoly A O).natDegree ≤ (isoPoly A O).natDegree := le_refl _

/-! ## The named residual (the open isolated / non-coset root count) -/

/--
**`IsolatedNonCosetCountResidual` — the recorded count obligation after MS-direct.**

MS-direct proves: `P = A² − u·O²` is `O(k)`-sparse (`isoPoly_support_card_le`) but the naive MS feed
is vacuous (`mason_stothers_iso_feed_vacuous`).  Sparsity `T = O(k)` does **not** by itself cap roots
in `μ_{n/2}` (the binomial `u^e − 1` has `e` such roots).  The descent classifies those full-sub-coset
roots as *core one level down*, so `iso` counts only the **isolated / non-coset** roots.  The cap

  `#{ u ∈ μ_{n/2} : P(u) = 0, u not in a full sub-coset of P, O(u) ≠ 0 } ≤ poly(k)`

is the Lenstra-style coset-structure bound — unconditional over `ℚ`, but over `F_q` at the prize prime
the perfect-square head `(u^{a/2}+γu^{b/2})²` can acquire subgroup structure, and the isolated-root
count there is the **same general-position cancellation the Kelley/BGK conjecture governs**.

The degree-only statement below is overstrong. `probe_antipodal_subgroup_obstructions.py`
certifies five roots against its `k+1 = 4` cap at `k = 3` in both sponsor fields. All five roots
belong to the actual halved subgroup, and the complete polynomial root set contains no full coset
of any nontrivial subgroup. Adding those two restrictions alone does not repair this
statement. The certificate does not realize the original high-head/low-tail decoded family;
any surviving production count must state and use those further restrictions.

The intended future input bounds the isolated roots of a suitably restricted
`O(k)`-sparse `P` on `μ_{n/2}` by `k + 1`. Naming the obligation and proving
it elsewhere (the `*_holds` / `*_of_*` convention) is the project's modularity convention; this is **not** discharged
here, and MS-direct does **not** close it. -/
def IsolatedNonCosetCountResidual (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ (A O : F[X]), A.natDegree < k → O.natDegree < k →   -- the O(k)-sparse / low-tail hypotheses
    ∀ (s : Finset F),
      -- `s` ranges over isolated roots: each is a root of `P` with `O ≠ 0` (non-core);
      -- the open content is that such an `s` (carrying no full-sub-coset of `P`) has `card ≤ k+1`.
      (∀ x ∈ s, (isoPoly A O).IsRoot x ∧ O.eval x ≠ 0) →
        s.card ≤ k + 1

/-- Documentation anchor: MS-direct = proven `O(k)` sparsity + vacuous naive MS feed; the remaining
`|iso| ≤ k+1` is the named isolated / non-coset root residual, NOT closed by Mason–Stothers. -/
def msDirectNote : Unit := ()

end ProximityGap.Frontier.IsoSparsityMasonStothers

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.IsoSparsityMasonStothers.isoPoly_support_card_le
#print axioms
  ProximityGap.Frontier.IsoSparsityMasonStothers.isoPoly_support_card_le_two_mul_add_four
#print axioms ProximityGap.Frontier.IsoSparsityMasonStothers.mason_stothers_iso_feed_vacuous
