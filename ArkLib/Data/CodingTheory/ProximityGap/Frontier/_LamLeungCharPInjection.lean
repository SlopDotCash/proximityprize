/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# The char-`p` Lam–Leung matching injection (abstract form) (#444, THREAD T2-lamleung-charp)

## The shape of the bound

The char-0 energy bound `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r` is proven (in-tree) by the **Lam–Leung
matching injection**: a solution of the energy equation `x₁+⋯+x_r = y₁+⋯+y_r` over `ℂ` (with all
`xᵢ, yⱼ ∈ μ_n`) is encoded by

  1. a **perfect matching** of the `2r` slot indices into antipodal-or-equal pairs (there are
     `(2r−1)‼` such matchings), together with
  2. an element of `[n]^r` recording one representative root per matched pair

— and this encoding is *injective*, giving `E_r^{char0} ≤ (2r−1)‼ · n^r`.

Over `F_p` the same encoding is **no longer injective on its own**: char-`p` "wraparound"
solutions (sums that vanish mod `p` without vanishing over `ℤ`) are NOT antipodally matched, so a
single `(matching, [n]^r)` pair can be hit by several genuinely distinct `F_p`-solutions. The
fix is to adjoin a **wraparound-tag** `t ∈ Tag` that disambiguates them, restoring injectivity into

  `Matching × [n]^r × Tag`.

If the tag alphabet has size `≤ 1 + τ` (one slot for the genuine char-0 image, `τ` extra slots for
the wraparound collisions it absorbs), the cardinality bound becomes

  `E_r(F_p) = |solutions| ≤ |Matching| · n^r · (1 + τ) = (2r−1)‼ · n^r · (1 + τ)`.

## What this file proves (axiom-clean) and what is the open residual

This file lands the **ABSTRACT injection lemma** unconditionally:

* `card_le_of_inject_into_triple` — given ANY injection `f : S ↪ A × B × T` (no structure assumed),
  `|S| ≤ |A| · |B| · |T|`. Pure `Fintype.card`/`Function.Injective` combinatorics.
* `card_le_of_tag_bounded` — if moreover `|T| ≤ 1 + τ`, then `|S| ≤ |A| · |B| · (1 + τ)`.
* `lamLeung_charP_card_le` — the Lam–Leung-shaped instantiation: with `A = Matching`,
  `|Matching| = oddFact r` (the `(2r−1)‼` matching count), `B = Fin n → Fin r`-style representative
  data of size `n^r` (passed as the abstract cardinality hypothesis), the energy solution set has
  `|solutions| ≤ oddFact r · n^r · (1 + τ)`.
* `lamLeung_charP_clean` — the corollary at `τ = 0` (no wraparound): the bound collapses to the
  exact char-0 Lam–Leung bound `|solutions| ≤ oddFact r · n^r`, recovering the proven char-0 face
  as the `τ = 0` slice.

**The named open residual is `τ` — the wraparound-tag multiplicity.** It is exactly the `W_r`
excess in disguise: `τ = 0` is the char-0 regime (proven), and a global bound `τ ≤ τ₀(r)` with
`τ₀(r*) = o(Wick)` at the saddle depth `r* ≈ log p` is the genuine open core of the prize
(equivalent to `p·W_r ≤ n^{2r} − E_r^{char0}`, the wraparound-collisions-bounded-by-their-mean
statement of `_OpenCoreCharPLighterReduction`). This file does NOT discharge `τ`; it isolates it as
the single combinatorial obligation the injection leaves open. The abstract lemma is genuinely
unconditional — the tag bound `|T| ≤ 1 + τ` is a HYPOTHESIS, not a hidden discharge of the prize.

Honesty: this is a `LANDED` brick — an axiom-clean abstract injection bound whose one named open
hypothesis (`τ`, the wraparound-tag count / `W_r` excess) IS the genuine open part. Issue #444.
-/

namespace ProximityGap.Frontier.LamLeungCharPInjection

open Finset

/-- The odd double factorial `(2r−1)‼` as the char-0 Lam–Leung matching count. `oddFact 0 = 1`
(the empty matching), `oddFact (r+1) = (2r+1)·oddFact r`. This is the number of perfect matchings
of `2r` points into antipodal-or-equal pairs — the `A`-alphabet of the injection. -/
def oddFact : ℕ → ℕ
  | 0 => 1
  | (r + 1) => (2 * r + 1) * oddFact r

@[simp] theorem oddFact_zero : oddFact 0 = 1 := rfl

@[simp] theorem oddFact_succ (r : ℕ) : oddFact (r + 1) = (2 * r + 1) * oddFact r := rfl

theorem oddFact_pos (r : ℕ) : 0 < oddFact r := by
  induction r with
  | zero => simp
  | succ k ih => simp only [oddFact_succ]; positivity

/-! ## The abstract injection lemma (unconditional core) -/

/-- **Abstract triple-injection cardinality bound.** If a finite type `S` injects into a product
`A × B × T` of finite types, then `|S| ≤ |A| · |B| · |T|`. No structure on the injection is
assumed — this is the pure combinatorial backbone of the Lam–Leung encoding `solutions ↪
Matching × [n]^r × Tag`. -/
theorem card_le_of_inject_into_triple
    {S A B T : Type*} [Fintype S] [Fintype A] [Fintype B] [Fintype T]
    (f : S → A × B × T) (hf : Function.Injective f) :
    Fintype.card S ≤ Fintype.card A * Fintype.card B * Fintype.card T := by
  have h1 : Fintype.card S ≤ Fintype.card (A × B × T) := Fintype.card_le_of_injective f hf
  calc Fintype.card S
      ≤ Fintype.card (A × B × T) := h1
    _ = Fintype.card A * (Fintype.card B * Fintype.card T) := by
          rw [Fintype.card_prod, Fintype.card_prod]
    _ = Fintype.card A * Fintype.card B * Fintype.card T := by ring

/-- **Tag-bounded form.** Adjoining the wraparound-tag multiplicity bound `|T| ≤ 1 + τ` to the
abstract injection turns the triple bound into `|S| ≤ |A| · |B| · (1 + τ)`. Here `1` is the slot
for the genuine char-0 image and `τ` counts the wraparound collisions absorbed per `(A,B)` cell. -/
theorem card_le_of_tag_bounded
    {S A B T : Type*} [Fintype S] [Fintype A] [Fintype B] [Fintype T]
    (f : S → A × B × T) (hf : Function.Injective f)
    (τ : ℕ) (hT : Fintype.card T ≤ 1 + τ) :
    Fintype.card S ≤ Fintype.card A * Fintype.card B * (1 + τ) := by
  have h := card_le_of_inject_into_triple f hf
  calc Fintype.card S
      ≤ Fintype.card A * Fintype.card B * Fintype.card T := h
    _ ≤ Fintype.card A * Fintype.card B * (1 + τ) := by
          exact Nat.mul_le_mul_left _ hT

/-! ## The Lam–Leung-shaped instantiation

We keep the matching alphabet `A` and the representative-data alphabet `B` abstract, pinned only by
their cardinalities (`|A| = oddFact r = (2r−1)‼`, `|B| = n^r`). This is the honest statement: the
*existence* of the injection with a tag alphabet of size `≤ 1 + τ` is the hypothesis; the
conclusion is the energy cardinality bound. The combinatorial content (that such `A, B, T, f` exist
over `F_p`) is summarized by the `τ` residual. -/

/-- **The char-`p` Lam–Leung cardinality bound.** Suppose the `F_p` energy solution set `S` (finite)
admits a Lam–Leung-style injection into `Matching × Repr × Tag`, where `Matching` is the antipodal-
matching alphabet with `|Matching| = oddFact r` (the `(2r−1)‼` char-0 matchings), `Repr` is the
representative-root data with `|Repr| = n^r`, and `Tag` is the wraparound-tag alphabet with
`|Tag| ≤ 1 + τ`. Then

  `|S| ≤ (2r−1)‼ · n^r · (1 + τ)`.

The factor `(1 + τ)` is the *only* gap between this and the proven char-0 bound; `τ` (the
wraparound-tag multiplicity, equal to the `W_r` excess) is the named open residual. -/
theorem lamLeung_charP_card_le
    {S Matching Repr Tag : Type*}
    [Fintype S] [Fintype Matching] [Fintype Repr] [Fintype Tag]
    (n r τ : ℕ)
    (hMatching : Fintype.card Matching = oddFact r)
    (hRepr : Fintype.card Repr = n ^ r)
    (f : S → Matching × Repr × Tag) (hf : Function.Injective f)
    (hTag : Fintype.card Tag ≤ 1 + τ) :
    Fintype.card S ≤ oddFact r * n ^ r * (1 + τ) := by
  have h := card_le_of_tag_bounded f hf τ hTag
  rwa [hMatching, hRepr] at h

/-- **The `τ = 0` collapse (char-0 face recovered).** When there is no wraparound (`τ = 0`, the
char-0 regime / below the `W_r` onset), the tag alphabet is trivial (`|Tag| ≤ 1`) and the bound
collapses to the exact proven Lam–Leung char-0 bound `|S| ≤ (2r−1)‼ · n^r`. This shows the abstract
lemma genuinely *contains* the char-0 result as its `τ = 0` slice (not a vacuous discharge). -/
theorem lamLeung_charP_clean
    {S Matching Repr Tag : Type*}
    [Fintype S] [Fintype Matching] [Fintype Repr] [Fintype Tag]
    (n r : ℕ)
    (hMatching : Fintype.card Matching = oddFact r)
    (hRepr : Fintype.card Repr = n ^ r)
    (f : S → Matching × Repr × Tag) (hf : Function.Injective f)
    (hTag : Fintype.card Tag ≤ 1) :
    Fintype.card S ≤ oddFact r * n ^ r := by
  have h := lamLeung_charP_card_le n r 0 hMatching hRepr f hf (by simpa using hTag)
  simpa using h

/-- **Monotonicity in the tag residual.** A smaller wraparound-tag bound gives a smaller energy
bound: the char-`p` energy ceiling is monotone in `τ`. This records that *driving `τ` down toward 0*
(the open program) monotonically tightens the bound toward the char-0 ideal `(2r−1)‼·n^r`. -/
theorem charP_bound_mono_in_tag (r n τ₁ τ₂ : ℕ) (hτ : τ₁ ≤ τ₂) :
    oddFact r * n ^ r * (1 + τ₁) ≤ oddFact r * n ^ r * (1 + τ₂) :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_left hτ 1)

/-- **Naming the residual as the `W_r` excess.** This `def` makes the open obligation a first-class
named `Prop`: *there is a global wraparound-tag bound `τ ≤ τ₀(r)` valid at the saddle depth*. The
prize is exactly the assertion `WraparoundTagBounded` with `τ₀(r*) ` small enough that
`oddFact r* · n^r* · (1 + τ₀(r*)) ≤ (2r*−1)‼ · n^{r*} · (1 + o(1))`, i.e. the wraparound collisions
do not exceed their heuristic mean (`p·W_r ≤ n^{2r} − E_r^{char0}` of
`_OpenCoreCharPLighterReduction`). Stating it does NOT prove it — it is the named open residual. -/
def WraparoundTagBounded
    (S Matching Repr Tag : Type*)
    [Fintype S] [Fintype Matching] [Fintype Repr] [Fintype Tag]
    (n r τ : ℕ) : Prop :=
  Fintype.card Matching = oddFact r ∧ Fintype.card Repr = n ^ r ∧
    Fintype.card Tag ≤ 1 + τ ∧ (∃ f : S → Matching × Repr × Tag, Function.Injective f)

/-- **The reduction `WraparoundTagBounded ⟹ energy bound`.** Unpacking the named residual yields
the char-`p` energy cardinality bound. This is the precise statement that the *only* thing standing
between the proven abstract injection and the energy ceiling is the tag bound `τ` — the open core. -/
theorem energy_bound_of_wraparoundTagBounded
    {S Matching Repr Tag : Type*}
    [Fintype S] [Fintype Matching] [Fintype Repr] [Fintype Tag]
    (n r τ : ℕ)
    (h : WraparoundTagBounded S Matching Repr Tag n r τ) :
    Fintype.card S ≤ oddFact r * n ^ r * (1 + τ) := by
  obtain ⟨hM, hR, hT, f, hf⟩ := h
  exact lamLeung_charP_card_le n r τ hM hR f hf hT

end ProximityGap.Frontier.LamLeungCharPInjection

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.LamLeungCharPInjection.oddFact_pos
#print axioms ProximityGap.Frontier.LamLeungCharPInjection.card_le_of_inject_into_triple
#print axioms ProximityGap.Frontier.LamLeungCharPInjection.card_le_of_tag_bounded
#print axioms ProximityGap.Frontier.LamLeungCharPInjection.lamLeung_charP_card_le
#print axioms ProximityGap.Frontier.LamLeungCharPInjection.lamLeung_charP_clean
#print axioms ProximityGap.Frontier.LamLeungCharPInjection.charP_bound_mono_in_tag
#print axioms ProximityGap.Frontier.LamLeungCharPInjection.energy_bound_of_wraparoundTagBounded
