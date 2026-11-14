/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
into `φ(n) = n/2` distinct degree-`1` primes `𝔭_1,…,𝔭_{n/2}`. Fixing the embedding `μ_n ↪ 𝔽_p`
fixes **one** of these primes, say `𝔭 = 𝔭_1 = (p, ζ_n − g)` for the chosen root `g ∈ 𝔽_p`. A
*wraparound* element is `α = Σx − Σy ∈ ℤ[ζ_n]` with `α ≠ 0` but `α ∈ 𝔭`, i.e. `α` reduces to `0`
under the **chosen** evaluation `ζ_n ↦ g` mod `p`. `W_r` counts the wraparound `2r`-tuples.

*Correction (audit 2026-10-28, R-211).* An earlier version of this header defined a wraparound
by `p ∣ α`, i.e. `(p) ∣ (α)` (all `n/2` power-basis coordinates of `α` vanish mod `p`). That is a
different and much stronger event: since `(p) = 𝔭_1 ⋯ 𝔭_{n/2}`, it demands vanishing at **every**
prime above `p`. Three events must be kept apart:
* `α ∈ 𝔭` for the chosen `𝔭` (the actual finite-field wraparound used by `W_r`);
* `p ∣ N_{K/ℚ}(α)` (vanishing at *some* prime above `p`, an existence-over-embeddings event);
* `(p) ∣ (α)` (vanishing at *all* primes above `p`).
Example: in `ℤ[ζ_8]` with `p = 17`, `α = ζ⁴ + ζ⁵ − 1 − ζ⁶ = −2 − ζ + ζ²` is nonzero, vanishes at
the root `ζ ↦ 2` mod `17` (so `α ∈ 𝔭` for that `𝔭`), and has norm `34`; its coordinates
`−2, −1, 1, 0` are not all divisible by `17`, so `α ∉ (17)`. This is a genuine short balanced
wraparound excluded by the old definition. Nothing in this file is formalized about any of these
events: the Lean content below is two abstract one-line lemmas.

The **Stickelberger element** `θ = Σ_{gcd(a,n)=1} {a/n} σ_a^{-1} ∈ ℚ[G]`, `G = Gal(K/ℚ)`, has the
property (Stickelberger's theorem) that any `β·θ ∈ ℤ[G]` **annihilates the class group** `Cl(K)`:
`𝔞^{βθ}` is principal for every ideal `𝔞`. Concretely `𝔭_i^{θ'}` is the ideal of a **Gauss sum**.

The mechanism asks: does the annihilator (vs the valuation) bound `W_r` or the prize sup-norm
`M(n) = max_{b≠0}|Σ_{x∈μ_n} ψ(bx)|`?

## Heuristic argument (informal), and the two trivial lemmas proved here

*Scope (audit 2026-10-28, R-211).* What is proved in Lean below is only: an additive
homomorphism maps `0` to `0`, and an *assumed* invariance hypothesis is returned unchanged. These
are not an arithmetic impossibility theorem. No short-element / coefficient-height model, no
factorization model and no class group is formalized, so this file does **not** prove that
class-group or Stickelberger methods cannot contribute to counting short wraparound generators.
The discussion below is a heuristic for why the authors did not pursue this route.

**Fact A (the wraparound ideal is principal).**
`α` is *a number*, so `(α)` is a principal ideal: its class `[(α)] = 0 ∈ Cl(K)`, and the
annihilator `θ` acts on `[(α)] = 0` as `θ·0 = 0`. Caveat: principality of `(α)` is not
contentless. Writing `(α) = 𝔭 · 𝔟` (with `𝔭` the chosen prime above `p`), principality imposes the
relation `[𝔟] = −[𝔭]` among the ideal classes of the prime factors of `α`, and such factorization
constraints could in principle restrict which short `α` exist. The trivial identity `θ 0 = 0`
does not exclude that; it only says the annihilator gives nothing *on the class `[(α)]` itself*.

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

We model the unit-ambiguity abstractly: `unit_invariant_output_constant` takes as a *hypothesis*
that a functional is unit-invariant and returns it. Caveat: arbitrary unit translates `u·γ` need
not preserve the coefficient-height / short-relation domain in which wraparounds live, so this
invariance statement on its own is not a no-go for short-generator counting.

## Verdict (heuristic, not a formal no-go)

`heuristic-collapse; not formally excluded`. The annihilator route is distinct in *form* from the
valuation route. Heuristically, Fact A says the annihilator gives nothing on the trivial class
`[(α)]`, and Fact B routes its nonvacuous output through ideal/unit-invariant data, the column the
`ValuationClassBarrier` addresses. This file does **not** prove that the class-group torsion is
decoupled from the count `W_r` or the size `M(n)`: that would need an actual short-element and
factorization model (using the chosen-prime event above, not `(p) ∣ (α)`) and a theorem excluding
class-group constraints on it, neither of which is formalized.

Related in-tree files: `_ValuationClassBarrier` (ideal-invariance), `_wf5M2_stickelberger_depth`
(the conditional AM-GM `p ≤ b^t` with `M = 2Rt`) and `_StickelbergerGeoMeanThreshold` (the
`(2H)^{n/4}` geometric-mean cap).

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
hence the Stickelberger annihilator yields the trivial relation `θ 0 = 0` on that class. This is
only `AddMonoidHom.map_zero`; it does not show that class-group data constrains nothing about
`W_r` (principality of `(α)` still relates the classes of its prime factors). -/
theorem annihilator_on_principal_is_trivial {M : Type*} [AddCommGroup M] (θ : M →+ M) :
    θ 0 = 0 := θ.map_zero

/-- **Fact B (abstract).** The annihilator's only nonvacuous output is a *principal* ideal, i.e. a
generator `γ` defined **only up to units**. Any functional `f` that is invariant under the unit
action (`f (g • x) = f x` for every unit `g` and element `x`) is constant along every unit orbit.
The invariance is the *hypothesis* `hf`, returned unchanged; nothing about the Stickelberger
element, units of `ℤ[ζ_n]`, archimedean profiles or `M(n)` is formalized, and unit translates
need not preserve the short-coefficient domain of wraparounds. -/
theorem unit_invariant_output_constant {G X V : Type*} [Group G] [MulAction G X]
    (f : X → V) (hf : ∀ (g : G) (x : X), f (g • x) = f x) (g : G) (x : X) :
    f (g • x) = f x := hf g x

/-- **The Mechanism-4 lemmas (packaged).** The conjunction of the two trivial lemmas above: (A)
`θ 0 = 0`, and (B) the entered invariance hypothesis `hf`. Despite the historical name, this is
not an arithmetic impossibility theorem: it does not show that the Stickelberger annihilator
supplies no wraparound-count relation or archimedean bound (see the module docstring, R-211). -/
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
