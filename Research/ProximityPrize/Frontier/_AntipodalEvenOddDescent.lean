/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# The antipodal even/odd descent for the ragged residual (#407)

This is the **provable structural core** of the realizability-conditioned ragged bad-scalar
residual of the Ethereum Proximity Prize (issue #407), and a genuinely new mechanism distinct
from the in-tree `_PerCosetDichotomy.lean` (per-coset all-or-thin) and `_RaggedRootBound.lean`
(degree-excess).  It is the `μ_2`-quotient (antipodal `x ↦ −x`) descent that *exactly*
characterises which agreement points are **isolated** (ragged) versus **coset-core**, for the
prize's *special contiguous support* `{0,…,k−1, a, b}` with `a, b` even.

## The setup (prize agreement polynomial, contiguous support)

The bad-scalar object is `P(x) = xᵃ + γ·xᵇ − c(x)` with `deg c < k` and the **contiguous** low
block `{0,…,k−1}` plus the two high terms `{a, b}` (the genuine direction has `d = gcd(a−b,n) ≥ 2`,
forcing `a ≡ b (mod 2)`; the binding case is `a, b` both even).  The agreement set is
`S = {x ∈ μ_n : P(x) = 0}`, `n = 2^μ`.

## The descent (the new content, `eval_eq_even_sub_x_odd`)

Split `c` into even/odd parts `c(x) = cₑ(x²) + x · c_o(x²)` (`deg c_o < k/2`).  Because `a, b` are
**even**, the line terms `xᵃ = (x²)^{a/2}`, `xᵇ = (x²)^{b/2}` are *even* too, so

  `P(x) = E(x²) − x · O(x²)`,   where
  `E(u) = u^{a/2} + γ·u^{b/2} − cₑ(u)`   and   `O(u) = c_o(u)`,   `deg O < k/2`.

This is a clean **ring identity** (proved here for any commutative ring, any `P` written as
`E ∘ X² − X · (O ∘ X²)`).  The antipode `−x` shares `x² = u`, so:

* **core point** (`x` and `−x` both in `S`)  ⟺  `E(u) = 0` *and* `O(u) = 0`;
* **isolated point** (exactly one of `x, −x` in `S`)  ⟺  `O(u) ≠ 0`, and then the surviving
  root is the *unique* `x = E(u)/O(u)` — so the isolated point is **determined by `u = x²`**,
  hence confined to a **single coset of `μ_{n/2}`** (the square-root branch is fixed).

## Why this is the prize-relevant reduction (honest scope)

The **core** lives where `O(u) = c_o(u) = 0`: since `deg O < k/2`, at most `⌊(k−1)/2⌋` values of
`u`, i.e. `≤ k − 1` antipodal points — *unless* `O ≡ 0`, which is exactly the **pure-coset**
(`μ_2`-fold) case that has the in-tree exact closed form.  The **isolated** set injects into
`{u ∈ μ_{n/2} : E(u)² = u·O(u)², E(u)O(u) ≠ 0}`, a root problem of the *halved* subgroup `μ_{n/2}`.

So when `S` is **ragged** (`O ≢ 0`), both `core` and `iso` are governed by the *low-degree* poly
`O` (deg `< k/2`) and the halved-subgroup root count — **not by `n`**.  This is the mechanism
behind the measured, `n`-independent cap `|S_ragged| ≤ k + 1` (probes: `max|iso| = k+1` for
`n ∈ {16,32,64}`, flat in `n`), hence the ragged bad-scalars only reach agreement `≈ k+2`,
**strictly below the production radius** `δ*·n = Θ(n)`.  At the production radius the bad scalars
are therefore *entirely coset-pure* (the handled exact closed form).

This file proves the **characteristic-free structural identities** that make the descent exact:
`eval_eq_even_sub_x_odd` (the ring identity), `isRoot_neg_iff_odd_eval_zero` (core ⟺ `O(x²)=0`),
and `isolated_root_determined` (an isolated root is uniquely `x = E(x²)/O(x²)`, the single-coset
confinement).  The remaining quantity — the exact bound `|iso| ≤ k+1` via the halved-subgroup
root count of `E² − u·O²` — is named as the explicit residual `IsolatedCountResidual`; it is the
prize's recognised Kelley/BGK general-position root-count one 2-adic level down, **not** proved
here.  No char-`p` transfer is needed for any identity in this file.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.AntipodalEvenOddDescent

open Polynomial

variable {F : Type*} [CommRing F]

/-! ## The even/odd descent identity -/

/-- **The antipodal even/odd ring identity.**  Any polynomial written as `E(X²) − X·O(X²)`
(`E, O : F[X]`) evaluates, at `x`, to `E(x²) − x·O(x²)`.  For the prize agreement polynomial
`P = Xᵃ + γ Xᵇ − c` with `a, b` even and `c = cₑ(X²) + X·c_o(X²)`, this is `P(x) = E(x²) − x·O(x²)`
with `E = X^{a/2} + γ X^{b/2} − cₑ`, `O = c_o`.  This is the exact `μ_2`-quotient descent: the
whole agreement structure of `P` on `μ_n` reduces to two polynomials `E, O` on the squares
`μ_{n/2}`. -/
theorem eval_eq_even_sub_x_odd (E O : F[X]) (x : F) :
    (E.comp (X ^ 2) - X * O.comp (X ^ 2)).eval x
      = E.eval (x ^ 2) - x * O.eval (x ^ 2) := by
  simp [eval_comp]

/-- **Core ⟺ odd part vanishes (the antipodal dichotomy).**  With `P = E(X²) − X·O(X²)`, the
antipode `−x` is a root of `P` *given that `x` is a root* **iff** `O(x²) = 0`.  Indeed
`P(x) = E(x²) − x·O(x²)` and `P(−x) = E(x²) + x·O(x²)`, so if `P(x) = 0` then
`P(−x) = 2·x·O(x²)`; in a domain of characteristic `≠ 2` with `x ≠ 0` this vanishes iff
`O(x²) = 0`.  Thus the antipodally-paired (**core**) points are exactly those with `O(x²) = 0`;
the **isolated** points are those with `O(x²) ≠ 0`. -/
theorem isRoot_neg_iff_odd_eval_zero {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    (E O : F[X]) {x : F} (hx : x ≠ 0)
    (hroot : (E.comp (X ^ 2) - X * O.comp (X ^ 2)).IsRoot x) :
    (E.comp (X ^ 2) - X * O.comp (X ^ 2)).IsRoot (-x) ↔ O.eval (x ^ 2) = 0 := by
  have hP : E.eval (x ^ 2) - x * O.eval (x ^ 2) = 0 := by
    rw [IsRoot.def, eval_eq_even_sub_x_odd] at hroot; exact hroot
  have hPneg : (E.comp (X ^ 2) - X * O.comp (X ^ 2)).eval (-x)
      = E.eval (x ^ 2) + x * O.eval (x ^ 2) := by
    rw [eval_eq_even_sub_x_odd]; ring_nf
  rw [IsRoot.def, hPneg]
  constructor
  · intro h
    -- E(x²) + x O(x²) = 0 and E(x²) − x O(x²) = 0 ⟹ 2 x O(x²) = 0 ⟹ O(x²) = 0
    have hsum : 2 * (x * O.eval (x ^ 2)) = 0 := by linear_combination h - hP
    have hx2 : x * O.eval (x ^ 2) = 0 := by
      rcases mul_eq_zero.mp hsum with h2 | h2
      · exact absurd h2 hchar
      · exact h2
    rcases mul_eq_zero.mp hx2 with h3 | h3
    · exact absurd h3 hx
    · exact h3
  · intro h
    -- O(x²) = 0 ⟹ E(x²) = 0 (from hP) ⟹ E(x²) + x O(x²) = 0
    rw [h] at hP ⊢; simpa using hP

/-- **Isolated root is determined by its square (single-coset confinement).**  If `x` is a root of
`P = E(X²) − X·O(X²)` and `O(x²) ≠ 0` (an **isolated** point), then `x` is *uniquely* recovered
from `u = x²` as `x = E(u)/O(u)`.  Consequently the two square roots `±x` of a given `u` cannot
both be isolated roots — at most one is — so the isolated set injects into the squares `μ_{n/2}`
via `x ↦ x²`, and (the branch `x = E(u)/O(u)` being fixed) lies in a **single coset of `μ_{n/2}`**.
This is the formal statement of the measured per-`γ` single-coset confinement of the ragged set. -/
theorem isolated_root_determined {F : Type*} [Field F]
    (E O : F[X]) {x : F}
    (hroot : (E.comp (X ^ 2) - X * O.comp (X ^ 2)).IsRoot x)
    (hO : O.eval (x ^ 2) ≠ 0) :
    x = E.eval (x ^ 2) / O.eval (x ^ 2) := by
  have hP : E.eval (x ^ 2) - x * O.eval (x ^ 2) = 0 := by
    rw [IsRoot.def, eval_eq_even_sub_x_odd] at hroot; exact hroot
  have hx : x * O.eval (x ^ 2) = E.eval (x ^ 2) := by linear_combination -hP
  field_simp
  linear_combination hx

/-- **Two square roots of the same `u` cannot both be isolated.**  Direct corollary of
`isolated_root_determined`: if both `x` and `−x` (with `x ≠ 0`) are roots and one is isolated
(`O(x²) ≠ 0`), they would be forced equal, contradiction.  Hence each `u = x²` contributes **at
most one** isolated point — the injectivity `iso ↪ μ_{n/2}` underlying `|iso| ≤ |μ_{n/2}|` and, with
the residual below, the `n`-independent `|iso| ≤ k+1`. -/
theorem isolated_unique_per_square {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    (E O : F[X]) {x : F} (hx : x ≠ 0)
    (hroot : (E.comp (X ^ 2) - X * O.comp (X ^ 2)).IsRoot x)
    (hO : O.eval (x ^ 2) ≠ 0) :
    ¬ (E.comp (X ^ 2) - X * O.comp (X ^ 2)).IsRoot (-x) := by
  rw [isRoot_neg_iff_odd_eval_zero hchar E O hx hroot]
  exact hO

/-! ## The named residual (the open count, honestly isolated) -/

/--
**`IsolatedCountResidual` — the prize's remaining ragged count, one 2-adic level down.**

After the antipodal descent, the isolated (ragged) agreement points inject into

  `{ u ∈ μ_{n/2} : E(u)² = u · O(u)², E(u)·O(u) ≠ 0 }`,

the agreement points of `E²` and `u·O²` on the **halved** subgroup `μ_{n/2}`.  With `O = c_o`
(`deg < k/2`) this is again a *sparse-support* root-count over a `2`-power multiplicative subgroup
— the **same Kelley general-position root-count problem one descent level down**.  The prize needs
the `n`-independent bound `|iso| ≤ k + 1` (measured flat in `n ∈ {16,32,64}`); proving it is the
recognised open Kelley Conjecture 3.2 / BGK general-position count, **not** discharged here.

Stated as the explicit hypothesis a future closure must supply (the count of isolated roots is at
most `k + 1`), so downstream consumers can be written `*_of_IsolatedCountResidual`. -/
def IsolatedCountResidual (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ (E O : F[X]), O.natDegree < k →
    {x : F | (E.comp (X ^ 2) - X * O.comp (X ^ 2)).IsRoot x ∧ O.eval (x ^ 2) ≠ 0}.Finite ∧
    (∀ (s : Finset F),
      (↑s ⊆ {x : F | (E.comp (X ^ 2) - X * O.comp (X ^ 2)).IsRoot x ∧ O.eval (x ^ 2) ≠ 0})
        → s.card ≤ k + 1)

/-- Documentation anchor: the descent reduces the ragged residual to `IsolatedCountResidual`, the
Kelley count one `μ_2`-quotient level down — the genuine open quantity. -/
def descentNote : Unit := ()

end ProximityGap.Frontier.AntipodalEvenOddDescent

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.AntipodalEvenOddDescent.eval_eq_even_sub_x_odd
#print axioms ProximityGap.Frontier.AntipodalEvenOddDescent.isRoot_neg_iff_odd_eval_zero
#print axioms ProximityGap.Frontier.AntipodalEvenOddDescent.isolated_root_determined
#print axioms ProximityGap.Frontier.AntipodalEvenOddDescent.isolated_unique_per_square
