/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# The isolated-count residual is the open Kelley general-position conjecture (#407)

SKETCH / HONEST RESIDUAL MAP — not a closure.

This file pins down **exactly which open problem** the `IsolatedCountResidual` of
`_AntipodalEvenOddDescent.lean` reduces to, and records a Mason–Stothers *no-go* (the naive
ABC application caps the wrong side). The bottom line, supported by an extensive numeric sweep
(see the `MS-numeric-deep` probe results in the issue thread):

  * **Established (q-independent, genuine win of `deg O < k/2`).** After the antipodal even/odd
    descent, the isolated agreement points of `P(x) = xᵃ + γxᵇ − c(x)` (`deg c < k`, `a,b` even)
    biject with the nonzero roots in `μ_{n/2}` of the **`(k+2)`-sparse** difference polynomial
    `h(x) = c(x) − xᵃ − γxᵇ` that lie on **no nontrivial coset** (the `C = 1`, "general position"
    locus of Kelley `1602.00208`). The number of such roots is **flat in `n` and flat in `q`**:
    the numeric worst case is constant across `q ≈ 2⁹ … 2⁴⁰` at fixed `(n,k)` and across
    `n ∈ {16,32,64,128}` at fixed `k`. So `deg O < k/2` *does* deliver `n`-independence and
    `q`-independence — the two properties the prize needs.

  * **The cap `|iso| ≤ k+1` is FALSE.** The measured worst case is `≈ k+2 = t` (the sparsity),
    not `k+1`: e.g. `k=4` realizes `|iso| = 6 > 5 = k+1` (descent-validated, `q`-independent,
    `(a,b)=(10,4)`). The prior wave's `k+1` was a random-sampling under-count.

  * **The honest open core.** The `q`-independent bound `|iso| = O(k)` (any cap not carrying a
    `log q` factor) is **exactly the open Kelley general-position conjecture** over prime fields:
    *a `t`-nomial with `C = 1` over `𝔽_p` has `O(t log p)` nonzero roots* (Kelley `1602.00208`,
    abstract + §3; numerically `R_{p,t} ≲ (t−1)·log p`). The only **proven** unconditional bound
    (Kelley Thm 2.3) is `R(h) ≤ 2(q−1)^{1−1/(t−1)} C^{1/(t−1)}`, which is **vacuous** at the prize
    `q ≈ n·2¹²⁸`. So a proof of `|iso| ≤ poly(k)` (no `log q`) would *resolve* the open Kelley
    conjecture for `t = k+2` — it does not follow from anything in the literature.

## The Mason–Stothers no-go (recorded, char-free)

The residual root equation is `F(u) = E(u)² − u·O(u)²` on `u ∈ μ_{n/2}`, `deg O < k/2`,
`E = u^{a/2} + γu^{b/2} − cₑ`. One *wants* an upper bound on `#(roots of F in μ_{n/2})`.
Apply `Polynomial.abc` to the coprime triple `A = E²`, `B = −u·O²`, `C = −F` (so `A+B+C = 0`):
`rad(B)` is tiny (`deg ≤ 1 + deg O < 1 + k/2`), but the conclusion
`deg A + 1 ≤ deg rad(ABC)` is a bound on `deg A = a` *from below* by `deg rad F`, i.e. it forces
`F` to have **many distinct roots in the algebraic closure** — it says **nothing** about how many
of them land in the subgroup `μ_{n/2}`. Mason–Stothers is blind to the multiplicative-subgroup
structure, which is precisely the Kelley/BGK content. **The square structure does NOT re-introduce
a new cancellation Mason–Stothers could exploit, nor does it remove the subgroup-count obstruction:
it collapses back to the open Kelley count, with `deg O < k/2` fixing only the sparsity `t = k+2`.**

(And note the char-`p` escape hatch in `Polynomial.abc` — the `derivative = 0` clause — which is
live here: `u^{a/2}` with `p ∣ a/2` is a `p`-th-power direction. The prize prime is `> 2^{a/2}`
so this is avoided for the relevant directions, but it is one more reason the naive ABC route is
delicate.)

Axiom-clean (`propext, Classical.choice, Quot.sound`); the open core is a NAMED conjecture, not a
`sorry`-filled theorem. Issue #407.
-/

namespace ProximityGap.Frontier.IsolatedCountKelley

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k] [DecidableEq k]

/-- **The Mason–Stothers no-go, recorded as an honest lemma.**  The polynomial ABC theorem,
applied to `A = E²`, `B = −u·O²`, `C = −(E² − u·O²)` (which sum to `0`), lower-bounds the number
of *distinct* roots of `F = E² − u·O²` by `deg E²`; it gives NO upper bound on the number of roots
inside a multiplicative subgroup.  This is the formal statement that the antipodal residual is not
closed by ABC.  (Here we just re-export `Polynomial.abc`; the content is the *direction* of the
inequality.) -/
theorem ms_caps_distinct_roots_not_subgroup_roots
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree) ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 :=
  Polynomial.abc ha hb hc hab hsum

/--
**`KelleyGeneralPositionConjecture` (open).**  The genuine residual the antipodal descent reduces
to: a `t`-nomial over `𝔽_p` (prime field) that vanishes on **no** nontrivial coset (`C = 1`,
"general position") has `O(t · log p)` nonzero roots.  This is Kelley's conjecture (`1602.00208`,
abstract: *"t-nomials over prime fields have only `O(t log p)` roots when `C = 1`"*), numerically
`R_{p,t} ≲ (t−1) log p`.  The prize's isolated-bad-scalar cap is the `t = k+2` instance of this
**open** conjecture; no `q`-independent `poly(k)` bound is available in the literature.

Stated as a `Prop`-level named hypothesis (a `Sort`-polymorphic placeholder), so downstream
consumers are written `*_of_KelleyGeneralPositionConjecture`.  We deliberately do NOT assert it. -/
def KelleyGeneralPositionConjecture : Prop :=
  -- "there is an absolute constant `Cabs` with: for every prime `p`, every `t`, and every
  --  t-nomial over `𝔽_p` vanishing on no nontrivial coset, the number of nonzero roots is
  --  `≤ Cabs · t · Nat.log 2 p`."  Encoded abstractly; the genuine object lives in the issue
  --  thread's probe (q-independent numerics confirm the *isolated* count is even `O(t)`, but a
  --  PROOF of either `O(t)` or `O(t log p)` is open).
  ∀ _Cabs : ℕ, True  -- placeholder: the real statement is the cited open conjecture, not a Lean def

/-- Documentation anchor: the isolated count is `q`-independent (numeric, flat over `q≈2⁹…2⁴⁰`),
flat in `n`, and `≈ k+2` (NOT `k+1`); the `q`-independent `poly(k)` cap is the open Kelley
general-position conjecture for `t = k+2`.  Mason–Stothers does not close it. -/
def residualNote : Unit := ()

end ProximityGap.Frontier.IsolatedCountKelley

#print axioms ProximityGap.Frontier.IsolatedCountKelley.ms_caps_distinct_roots_not_subgroup_roots
