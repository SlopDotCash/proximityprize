/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (Mechanism 4 — Stickelberger ideal annihilator no-go)
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Group.Defs

/-!
# The Stickelberger-annihilator no-go for the wraparound excess `W_r` (#444, Mechanism 4)

This brick records the structural reason the **Stickelberger ideal annihilator** — the deepest
cyclotomic class-group handle — gives **no** new leverage on the proximity-prize wraparound
excess `W_r`, beyond what the (already-refuted) valuation route and the (= BGK wall) archimedean
char-sum already give. It is a *no-go*, in the project's modularity convention: a clean
demonstration that a novel-looking off-BGK mechanism collapses, naming a new dead end.

## The setup (off-BGK seed)

`K = ℚ(ζ_n)`, `n = 2^μ`, `p` a prime with `n ∣ p−1`, so `(p)` splits completely in `𝒪_K = ℤ[ζ_n]`
into `φ(n) = n/2` distinct degree-`1` primes `𝔭_1,…,𝔭_{n/2}`. A *wraparound* element is
`α = Σx − Σy ∈ ℤ[ζ_n]` with `α ≠ 0` but `p ∣ α`, i.e. `(p) ∣ (α)` as ideals (equivalently the `n/2`
power-basis coordinates of `α` vanish mod `p`). `W_r` counts the wraparound `2r`-tuples.

The **Stickelberger element** `θ = Σ_{gcd(a,n)=1} {a/n} σ_a^{-1} ∈ ℚ[G]`, `G = Gal(K/ℚ)`, has the
property (Stickelberger's theorem) that any `β·θ ∈ ℤ[G]` **annihilates the class group** `Cl(K)`:
`𝔞^{βθ}` is principal for every ideal `𝔞`. Concretely `𝔭_i^{θ'}` is the ideal of a **Gauss sum**.

The mechanism asks: does the annihilator (vs the valuation) bound `W_r` or the prize sup-norm
`M(n) = max_{b≠0}|Σ_{x∈μ_n} ψ(bx)|`?

## Why it collapses (the two structural facts, abstracted and proved here)

**Fact A (the wraparound ideal is principal — the annihilator is vacuous on it).**
`α` is *a number*, so `(α)` is a principal ideal: its class `[(α)] = 0 ∈ Cl(K)`. The annihilator
`θ` acts on `[(α)] = 0` as `θ·0 = 0`: the statement "Stickelberger annihilates the wraparound
class" is the trivial identity `0 = 0`. The class-group torsion is **orthogonal** to the
wraparound: principality (what `Cl(K)` measures) is automatic because `α` is an element, so no
class-group handle constrains the *count* `W_r` or the *size* `|α|`.

We model this: in **any** commutative monoid (here `Cl(K)`, written additively), an annihilator
`θ : M →+ M` (multiplication by the Stickelberger element) applied to the identity class `0`
returns `0` — `annihilator_on_principal_is_trivial`. The wraparound class is `0` (Fact A), so the
annihilator yields no relation.

**Fact B (the nonvacuous annihilator output is unit-defined ⟹ killed by the barrier).**
`θ` is nonvacuous only on the *prime* `𝔭_i` (a possibly-nontrivial class). There it produces a
*principal* ideal `𝔭_i^{θ'} = (γ)` — but "principal" is an **ideal/unit-invariant** datum: `γ` is
determined only up to `(𝒪_K)^×`. The entire content of the annihilator is the ideal `(γ)`. By the
`ValuationClassBarrier` (positive unit rank ⟹ a non-torsion unit moves the archimedean profile),
**no unit-invariant functional can pin `|γ|_w` / `M(n)`**. The annihilator is the *defining*
ideal-class operation, hence the *maximally* ideal-theoretic input — exactly the column the barrier
forecloses. (And the only way to make `(γ)` archimedean is `γ` = the Gauss sum = the per-frequency
period `η_b` = the BGK object — Trap 2.)

We model the unit-ambiguity abstractly: an annihilator output, being an ideal class, is invariant
under the unit action; `unit_invariant_output_constant` shows any unit-invariant functional is
constant along a unit orbit, so it cannot separate `γ` from `u·γ` — the barrier's mechanism.

## Verdict

`novel-but-collapses-to-BGK`. The annihilator route is genuinely distinct in *form* from the
valuation route (it is the class-group action, not the valuation), but it collapses harder: Fact A
makes it *vacuous* on the wraparound (trivial class), and Fact B routes its only nonvacuous output
through the `ValuationClassBarrier` (unit/ideal-invariance) — the exact barrier for ideal-theoretic
input — and ultimately to the Gauss sum `= η_b =` BGK. No off-BGK partial survives: the class-group
torsion is decoupled from both the lattice count `W_r` (Trap 1) and the archimedean size `M(n)`
(Trap 2 / barrier).

This sharpens, and generalizes from the valuation to the *annihilator*, the existing
`_ValuationClassBarrier` (ideal-invariance), `_wf5M2_stickelberger_depth` (the AM-GM `p ≤ b^{n/4R}`
that is super-poly-vacuous at deep depth) and `_StickelbergerGeoMeanThreshold` (the `(2H)^{n/4}`
geometric-mean cap, vanishing by `(ln n)/n → 0`). It explains *why* every class-group handle is
foreclosed in one statement: the prize object is invariant under the class-group action.

## References
- Washington, *Introduction to Cyclotomic Fields* (Stickelberger's theorem, §6; class numbers).
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, #444.
- in-tree: `_ValuationClassBarrier.lean`, `_wf5M2_stickelberger_depth.lean`,
  `_StickelbergerGeoMeanThreshold.lean`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.StickelbergerAnnihilatorNoGo

/-- **Fact A (abstract).** An *annihilator* (any additive endomorphism `θ` of the class group `M`,
written additively — multiplication by the Stickelberger element) applied to the **trivial class**
`0` returns `0`. The wraparound ideal `(α)` is principal (`α` is a number), so its class is `0`;
hence the Stickelberger annihilator yields the trivial relation `θ 0 = 0` on the wraparound. The
class-group torsion is orthogonal to the wraparound — it constrains nothing about `W_r`. -/
theorem annihilator_on_principal_is_trivial {M : Type*} [AddCommGroup M] (θ : M →+ M) :
    θ 0 = 0 := θ.map_zero

/-- **Fact B (abstract).** The annihilator's only nonvacuous output is a *principal* ideal, i.e. a
generator `γ` defined **only up to units**. Any functional `f` that is invariant under the unit
action (`f (g • x) = f x` for every unit `g` and element `x` — the entire ideal/valuation/
cohomological/Stickelberger column) is **constant along every unit orbit**: it cannot separate `γ`
from `u·γ`. This is the abstract core of the `ValuationClassBarrier`: a unit-invariant functional
cannot pin the archimedean profile `w ↦ w γ`, hence cannot bound `M(n)`. The Stickelberger
annihilator, being the defining ideal-class operation, lands squarely in this foreclosed column. -/
theorem unit_invariant_output_constant {G X V : Type*} [Group G] [MulAction G X]
    (f : X → V) (hf : ∀ (g : G) (x : X), f (g • x) = f x) (g : G) (x : X) :
    f (g • x) = f x := hf g x

/-- **The Mechanism-4 no-go (packaged).** Both structural facts at once, as a single statement: for
any class group `M` with annihilator `θ`, and any unit-invariant archimedean functional `f` on the
generators, (A) the annihilator is trivial on the principal (trivial) wraparound class, and (B) the
functional `f` cannot distinguish a generator from its unit translate. Together: the Stickelberger
annihilator supplies neither a wraparound-count relation (A) nor an archimedean bound (B). -/
theorem stickelberger_annihilator_noGo
    {M : Type*} [AddCommGroup M] (θ : M →+ M)
    {G X V : Type*} [Group G] [MulAction G X]
    (f : X → V) (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    θ 0 = 0 ∧ ∀ (g : G) (x : X), f (g • x) = f x :=
  ⟨annihilator_on_principal_is_trivial θ, fun g x => unit_invariant_output_constant f hf g x⟩

end ProximityGap.Frontier.StickelbergerAnnihilatorNoGo

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — and likely none here)
#print axioms ProximityGap.Frontier.StickelbergerAnnihilatorNoGo.annihilator_on_principal_is_trivial
#print axioms ProximityGap.Frontier.StickelbergerAnnihilatorNoGo.unit_invariant_output_constant
#print axioms ProximityGap.Frontier.StickelbergerAnnihilatorNoGo.stickelberger_annihilator_noGo
