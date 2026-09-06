/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Door IV coherence is multiplicative-order-blind

This file records the axiom-clean obstruction behind the probe
`scripts/probes/probe_dooriv_rho_vs_order.py`.

## Probe context (door-(iv) Lane 1)

The brief's localized object is the index-2 coset-half coherence `ρ(b)` of the period sum
`S(b) = ∑_{x∈μ_n} e_p(b·x)`.
A natural anti-concentration lever would be to target frequencies `b` of *special multiplicative
order* (a small subgroup, roots of unity) hoping for systematically smaller `ρ` (more cancellation).

The probe (proper `μ_n`, `p ≫ n³`, structured primes) shows this lever is empty:

* the mean `ρ(b)`, bucketed by `ord(b)/φ` into tiny `(≤0.05)`, small `(≤0.5)`, large `(>0.5)`, is
  **flat at `≈0.70–0.74`** across all order classes — `ρ` does not track order;
* the worst `b` (`argmax|S|`) has `ρ = 1.0000` with **generic** order (`ord(b)/φ ∈
  {0.014, 0.33, 0.5, 1.0}` across primes — no special value).

So `ρ` is **order-blind**.

## The brick (mechanism)

`ρ(b)` is built from the two coset-half period sums, which are **constant on multiplicative cosets**
`b·μ_n` (in-tree `_EtaCosetInvariance`).  Hence `ρ` is `μ_n`-coset-invariant.  But the
multiplicative order is *not* a coset invariant: two elements of the same coset `b·μ_n` can have
different orders.  Therefore a coset-invariant statistic takes the **same** value at every order
present in a coset, and no order-indexed restriction can constrain it.  We formalize the abstract
obstruction: a function constant on the cosets of a subgroup `H` is equal on any two `H`-translates
— in particular on a pair of same-coset elements with different orders.  This is a constraint lemma,
not `CORE`, and uses no moment or completion.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVCoherenceOrderBlind

variable {G : Type*} [Group G]

/-- Coset-invariance of a statistic `f` w.r.t. a subgroup `H`: `f` is unchanged by left-multiplying
by any element of `H`.  (This is the property the coset-half period sums — and hence `ρ` — satisfy
by `_EtaCosetInvariance`.) -/
def CosetInvariant (H : Subgroup G) {β : Type*} (f : G → β) : Prop :=
  ∀ (c : G), c ∈ H → ∀ b : G, f (c * b) = f b

/-- A coset-invariant statistic takes equal values on any two elements of the same left coset
(elements differing by a left `H`-translate). -/
theorem eq_of_cosetInvariant_of_sameCoset {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) {a b : G} (hab : a * b⁻¹ ∈ H) :
    f a = f b := by
  have hkey : a = (a * b⁻¹) * b := by group
  rw [hkey, hf (a * b⁻¹) hab b]

/-- **Order-blindness obstruction.**  If `f` is `H`-coset-invariant and two same-coset elements
`a, b` (with `a · b⁻¹ ∈ H`) have *different* multiplicative orders, then `f` still takes the
**same** value on them.  Thus a statistic that is `H`-coset-invariant cannot be made to depend on
multiplicative order of its argument: no order-indexed restriction constrains it.  (Here `H = μ_n`,
`f = ρ`; the probe exhibits same-coset elements of differing order, all with the same `ρ`.) -/
theorem cosetInvariant_blind_to_order {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) {a b : G} (hab : a * b⁻¹ ∈ H)
    (_hord : orderOf a ≠ orderOf b) :
    f a = f b :=
  eq_of_cosetInvariant_of_sameCoset hf hab

/-- Contrapositive packaging: if a coset-invariant statistic takes *distinct* values on `a` and `b`,
then `a` and `b` are in *different* cosets — so any genuine `ρ`-difference is a coset-level (not
order-level) phenomenon. -/
theorem distinct_value_forces_distinct_coset {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) {a b : G} (hne : f a ≠ f b) :
    a * b⁻¹ ∉ H := by
  intro hab
  exact hne (eq_of_cosetInvariant_of_sameCoset hf hab)

/-- The left-coset equivalence relation attached to `H`, written in the multiplicative form used
above: `a` and `b` are equivalent iff `a * b⁻¹ ∈ H`.  This is the exact quotient on which any
coset-invariant door-(iv) statistic (such as `ρ`) lives. -/
def LeftCosetSetoid (H : Subgroup G) : Setoid G where
  r a b := a * b⁻¹ ∈ H
  iseqv := by
    constructor
    · intro a
      simp
    · intro a b hab
      have hinv : (a * b⁻¹)⁻¹ ∈ H := H.inv_mem hab
      simpa [mul_inv_rev] using hinv
    · intro a b c hab hbc
      have hmul : (a * b⁻¹) * (b * c⁻¹) ∈ H := H.mul_mem hab hbc
      have hkey : (a * b⁻¹) * (b * c⁻¹) = a * c⁻¹ := by group
      simpa [hkey] using hmul

/-- **Exact quotient-factorization.**  Any `H`-coset-invariant statistic factors through the left
coset quotient `G / H` (represented by `LeftCosetSetoid H`).  In door-(iv) language: the localized
coherence `ρ(b)` is not a function of the raw frequency `b`, and in particular not of `orderOf b`;
it is a well-defined statistic on the multiplicative coset `b·μₙ`.  Therefore any proposed
order-level or element-level anti-concentration lever must first survive this quotient collapse. -/
noncomputable def factorThroughLeftCosets {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) : Quot (LeftCosetSetoid H) → β :=
  Quot.lift f (by
    intro a b hab
    exact eq_of_cosetInvariant_of_sameCoset hf hab)

/-- Evaluating the quotient factor on the class of `b` recovers the original statistic. -/
theorem factorThroughLeftCosets_mk {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) (b : G) :
    factorThroughLeftCosets (H := H) (f := f) hf (Quot.mk (LeftCosetSetoid H) b) = f b :=
  rfl

/-- Conversely, any statistic presented as a function of the left-coset quotient is automatically
`H`-coset-invariant.  This packages the door-(iv) mechanism as an iff-ready consumer: quotient-level
statistics are exactly blind to motion inside a coset. -/
theorem cosetInvariant_of_factorThroughLeftCosets {H : Subgroup G} {β : Type*}
    (F : Quot (LeftCosetSetoid H) → β) :
    CosetInvariant H (fun b : G => F (Quot.mk (LeftCosetSetoid H) b)) := by
  intro c hc b
  apply congrArg F
  apply Quot.sound
  change (c * b) * b⁻¹ ∈ H
  have hkey : (c * b) * b⁻¹ = c := by group
  simpa [hkey] using hc

/-- **Quotient-collapse iff.**  A statistic on frequencies is `H`-coset-invariant exactly when it is
pulled back from a function on the left-coset quotient.  For door-(iv), this is the clean reusable
form of the guardrail: any proposed coherence lever for `ρ(b)` must be a quotient-level invariant of
`b·μₙ`; if it changes inside a coset, it cannot govern `ρ`. -/
theorem cosetInvariant_iff_exists_factorThroughLeftCosets {H : Subgroup G} {β : Type*} {f : G → β} :
    CosetInvariant H f ↔
      ∃ F : Quot (LeftCosetSetoid H) → β, ∀ b : G, F (Quot.mk (LeftCosetSetoid H) b) = f b := by
  constructor
  · intro hf
    exact ⟨factorThroughLeftCosets (H := H) (f := f) hf,
      factorThroughLeftCosets_mk (H := H) (f := f) hf⟩
  · rintro ⟨F, hF⟩ c hc b
    calc
      f (c * b) = F (Quot.mk (LeftCosetSetoid H) (c * b)) := (hF (c * b)).symm
      _ = F (Quot.mk (LeftCosetSetoid H) b) := by
        apply congrArg F
        apply Quot.sound
        change (c * b) * b⁻¹ ∈ H
        have hkey : (c * b) * b⁻¹ = c := by group
        simpa [hkey] using hc
      _ = f b := hF b

/-- **Coset-hitting selectors preserve all coset-invariant values.**  If a proposed restricted
frequency class `T` intersects every left `H`-coset, then every global value of a coset-invariant
statistic already occurs on `T`.  Thus an order/selector-based door-(iv) restriction cannot lower
worst coherence unless it actually misses an entire `μₙ`-coset. -/
theorem values_on_cosetHitting_set_cover_global {H : Subgroup G} {β : Type*}
    {f : G → β} (hf : CosetInvariant H f) {T : Set G}
    (hT : ∀ b : G, ∃ t ∈ T, t * b⁻¹ ∈ H) :
    ∀ b : G, ∃ t ∈ T, f t = f b := by
  intro b
  rcases hT b with ⟨t, ht, htb⟩
  exact ⟨t, ht, eq_of_cosetInvariant_of_sameCoset hf htb⟩


/-- **Exact value-set preservation under coset-hitting selectors.**  If a restricted frequency
class `T` meets every left `H`-coset, then restricting a coset-invariant door-(iv) statistic to `T`
does not remove even a single value: the restricted image `f '' T` equals the global range.  This is
the value-set version of the selector obstruction.  An order bucket or element-level filter can
change the observed coherence spectrum only by missing whole `μₙ`-cosets; otherwise every global
coherence value is already represented inside the restricted class. -/
theorem image_cosetHitting_set_eq_range {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) {T : Set G}
    (hT : ∀ b : G, ∃ t ∈ T, t * b⁻¹ ∈ H) :
    f '' T = Set.range f := by
  ext y
  constructor
  · rintro ⟨t, _ht, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨b, rfl⟩
    rcases values_on_cosetHitting_set_cover_global (H := H) (f := f) hf hT b with ⟨t, ht, htb⟩
    exact ⟨t, ht, htb⟩

/-- **Restricted bounds are global exactly when the restriction hits every coset.**  For a
coset-invariant door-(iv) statistic, any upper bound checked on a set `T` meeting every `H`-coset is
already the global bound, and conversely the global bound trivially restricts to `T`.
This formalizes why order buckets or element-level filters cannot be a new anti-concentration lever
unless they remove whole cosets, which is quotient-level rather than multiplicative-order data. -/
theorem bound_on_cosetHitting_set_iff_global {H : Subgroup G} {β : Type*} [LE β]
    {f : G → β} {C : β} (hf : CosetInvariant H f) {T : Set G}
    (hT : ∀ b : G, ∃ t ∈ T, t * b⁻¹ ∈ H) :
    (∀ t ∈ T, f t ≤ C) ↔ ∀ b : G, f b ≤ C := by
  constructor
  · intro h b
    rcases hT b with ⟨t, ht, htb⟩
    rw [← eq_of_cosetInvariant_of_sameCoset hf htb]
    exact h t ht
  · intro h t _
    exact h t



/-- **No strict selector improvement without missing a coset.**  Direct impossibility form of
`bound_on_cosetHitting_set_iff_global`: if a restricted class `T` meets every left `H`-coset, then it
cannot satisfy a bound below any actual global value of a coset-invariant statistic.  Therefore an
order bucket, selector, or element-level filter can improve the door-(iv) worst coherence only by
omitting an entire `μₙ`-coset; otherwise the global obstruction is still present inside `T`. -/
theorem no_strict_bound_on_cosetHitting_set_below_global_value {H : Subgroup G} {β : Type*}
    [Preorder β] {f : G → β} (hf : CosetInvariant H f) {T : Set G} {C : β} {b : G}
    (hT : ∀ x : G, ∃ t ∈ T, t * x⁻¹ ∈ H) (hbound : ∀ t ∈ T, f t ≤ C)
    (hb : C < f b) : False := by
  have hglobal : ∀ x : G, f x ≤ C :=
    (bound_on_cosetHitting_set_iff_global (H := H) (f := f) (C := C) hf hT).1 hbound
  exact not_lt_of_ge (hglobal b) hb

/-- **Positive form of the selector obstruction.**  If a restricted class `T` satisfies a strict
bound below some global value of a coset-invariant statistic, then `T` must miss an entire left
`H`-coset.  Thus any genuine selector improvement is forced to be quotient-level: it cannot come from
an element-level property (such as multiplicative order) that still hits every `μₙ`-coset. -/
theorem exists_coset_missed_of_strict_selector_bound {H : Subgroup G} {β : Type*}
    [Preorder β] {f : G → β} (hf : CosetInvariant H f) {T : Set G} {C : β}
    (hbound : ∀ t ∈ T, f t ≤ C) (hstrict : ∃ b : G, C < f b) :
    ∃ x : G, ∀ t ∈ T, t * x⁻¹ ∉ H := by
  by_contra hmiss
  push Not at hmiss
  rcases hstrict with ⟨b, hb⟩
  exact no_strict_bound_on_cosetHitting_set_below_global_value
    (H := H) (f := f) (C := C) hf hmiss hbound hb

end ProximityGap.Frontier.DoorIVCoherenceOrderBlind

#print axioms ProximityGap.Frontier.DoorIVCoherenceOrderBlind.eq_of_cosetInvariant_of_sameCoset
#print axioms ProximityGap.Frontier.DoorIVCoherenceOrderBlind.cosetInvariant_blind_to_order
#print axioms ProximityGap.Frontier.DoorIVCoherenceOrderBlind.distinct_value_forces_distinct_coset
#print axioms ProximityGap.Frontier.DoorIVCoherenceOrderBlind.factorThroughLeftCosets_mk
#print axioms
  ProximityGap.Frontier.DoorIVCoherenceOrderBlind.cosetInvariant_of_factorThroughLeftCosets
#print axioms
  ProximityGap.Frontier.DoorIVCoherenceOrderBlind.cosetInvariant_iff_exists_factorThroughLeftCosets
#print axioms
  ProximityGap.Frontier.DoorIVCoherenceOrderBlind.values_on_cosetHitting_set_cover_global
#print axioms
  ProximityGap.Frontier.DoorIVCoherenceOrderBlind.image_cosetHitting_set_eq_range
#print axioms
  ProximityGap.Frontier.DoorIVCoherenceOrderBlind.bound_on_cosetHitting_set_iff_global
#print axioms
  ProximityGap.Frontier.DoorIVCoherenceOrderBlind.no_strict_bound_on_cosetHitting_set_below_global_value
#print axioms
  ProximityGap.Frontier.DoorIVCoherenceOrderBlind.exists_coset_missed_of_strict_selector_bound
