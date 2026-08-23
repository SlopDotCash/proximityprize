/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusCapForcedBelow

/-!
# A census cap FORBIDS large aligned sets — the necessity contrapositive (#444)

The census equivalence has two halves that the tree carries separately:

* **Sufficiency** (`UniversalAlignmentLaw.epsMCA_le_of_alignableSets_card_le`): a uniform census
  cap `#alignableSets ≤ L` pushes the prize-side MCA error down, `ε_mca ≤ L / |F|`.
* **Necessity FLOOR** (`CensusCapForcedBelow.choose_card_le_alignableSets`): a single `γ`-aligned
  set `A` of size `≥ a` carrying a non-degenerate `(k+1)`-tuple forces
  `C(|A| − (k+1), a − (k+1)) ≤ #alignableSets`, so the cap `K` cannot be smaller than that
  binomial.

What was MISSING is the **necessity contrapositive**: the direction that turns a census *upper*
bound back into a *list/agreement-size* upper bound.  If the census is capped at `K`, then no
aligned set can be so large that its own subset-supply alone would overflow `K`.

**The brick (`no_large_aligned_of_census_cap`).**  Assume `#alignableSets dom k a u₀ u₁ ≤ K`.
Then there is NO `γ`-aligned set `A` with `a ≤ |A|`, carrying a non-degenerate injective
`(k+1)`-tuple, whose subset supply exceeds the cap, i.e. with `K < C(|A| − (k+1), a − (k+1))`.
This is exactly the contrapositive of `choose_card_le_alignableSets`: such an `A` would force
`C(|A| − (k+1), a − (k+1)) ≤ #alignableSets ≤ K`, contradicting `K < C(…)`.

Specialised to the prize band `|A| = n`, `a ~ (1 − δ) n`: a census cap `K` caps the maximal
size of any aligned (= MCA-witnessing) set at the largest `m` with `C(m − (k+1), a − (k+1)) ≤ K`.
A *polynomial* census cap `K = poly(n)` therefore forbids aligned sets of size `n` once
`C(n − (k+1), a − (k+1))` is super-polynomial — the structural shape of "the cap controls the
list size", which is the necessity content of the equivalence the weld prose asserted.

**Honest scope.**  This is the *logical* necessity converse of the in-tree injection, stated as an
unconditional theorem.  It is NOT a CORE closure, NOT thinness-essential, and makes NO
capacity / beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched): it does not bound
`#alignableSets` itself (the open `M(μ_n) ≤ C√(n log(p/n))` CORE, equivalently the cap
`#alignableSets ≤ rm+1`, stays OPEN).  It only assembles the *if-capped-then-no-large-set*
half of the equivalence skeleton from the already-proven subset-supply injection.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

set_option linter.unusedVariables false in
open Classical in
omit [NeZero n] in
/-- **A census cap forbids large aligned sets.**  If the alignable-set census at band `a` is
capped by `K`, then there is no `γ`-aligned set `A` (with `a ≤ |A|`, `k+1 ≤ a`) carrying a
non-degenerate injective `(k+1)`-tuple whose subset supply `C(|A| − (k+1), a − (k+1))` exceeds
`K`.  Contrapositive of `choose_card_le_alignableSets`. -/
theorem no_large_aligned_of_census_cap (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {K : ℕ}
    (hcap : (alignableSets dom k a u₀ u₁).card ≤ K)
    {γ : F} {A : Finset (Fin n)}
    (hAa : a ≤ A.card) (hka : k + 1 ≤ a)
    (halign : Aligned dom k u₀ u₁ γ A)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ A)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    (A.card - (k + 1)).choose (a - (k + 1)) ≤ K :=
  le_trans
    (choose_card_le_alignableSets dom u₀ u₁ hAa hka halign htinj htmem hnd) hcap

set_option linter.unusedVariables false in
open Classical in
omit [NeZero n] in
/-- **Strict-overflow form.**  Under a census cap `K`, NO aligned set with subset supply strictly
exceeding `K` can exist: the hypotheses of `choose_card_le_alignableSets` are jointly
unsatisfiable when `K < C(|A| − (k+1), a − (k+1))`.  This is the clean "cap ⟹ no large set"
statement (a `False` from the witness), the necessity converse of the supply floor. -/
theorem not_aligned_of_census_cap_lt (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {K : ℕ}
    (hcap : (alignableSets dom k a u₀ u₁).card ≤ K)
    {γ : F} {A : Finset (Fin n)}
    (hAa : a ≤ A.card) (hka : k + 1 ≤ a)
    (hlt : K < (A.card - (k + 1)).choose (a - (k + 1)))
    (halign : Aligned dom k u₀ u₁ γ A)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ A)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    False :=
  absurd
    (no_large_aligned_of_census_cap dom u₀ u₁ hcap hAa hka halign htinj htmem hnd)
    (Nat.not_le.mpr hlt)

set_option linter.unusedVariables false in
open Classical in
omit [NeZero n] in
/-- **Size ceiling form.**  A census cap `K` forces a ceiling on `|A|` for any aligned set with
a non-degenerate tuple: its size minus `(k+1)` cannot exceed the largest `m` with
`C(m, a − (k+1)) ≤ K`.  Concretely, monotonicity of the binomial in its top argument means a
*polynomial* cap `K` confines aligned-set sizes once the supply is super-polynomial — the
necessity-side "cap controls list size" shape. -/
theorem aligned_supply_le_census_cap (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {K : ℕ}
    (hcap : (alignableSets dom k a u₀ u₁).card ≤ K)
    {γ : F} {A : Finset (Fin n)}
    (hAa : a ≤ A.card) (hka : k + 1 ≤ a)
    (halign : Aligned dom k u₀ u₁ γ A)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ A)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    ∃ m, (A.card - (k + 1)).choose (a - (k + 1)) = m ∧ m ≤ K :=
  ⟨(A.card - (k + 1)).choose (a - (k + 1)), rfl,
    no_large_aligned_of_census_cap dom u₀ u₁ hcap hAa hka halign htinj htmem hnd⟩

set_option linter.unusedVariables false in
open Classical in
/-- **Prize-band consumer form.**  At the full domain `A = univ` (`|A| = n`, the prize band where
the alignment is over ALL `n` evaluation points), a census cap `K` must dominate the genuine
supply `C(n − (k+1), a − (k+1))`.  Here the cap BITES: at `a < n` the binomial grows in `n`, so a
polynomial census cap forbids the whole domain from being aligned with a non-degenerate tuple
once `C(n − (k+1), a − (k+1))` is super-polynomial.  This is the prize-band instance of the
necessity converse — the form a CORE-side list-size bound would consume. -/
theorem census_cap_ge_full_domain_supply (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) {K : ℕ}
    (hcap : (alignableSets dom k a u₀ u₁).card ≤ K)
    (hka : k + 1 ≤ a) (han : a ≤ n)
    {γ : F} (halign : Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    (n - (k + 1)).choose (a - (k + 1)) ≤ K := by
  have hcardeq : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hAa : a ≤ (Finset.univ : Finset (Fin n)).card := by rw [hcardeq]; exact han
  have htmem : ∀ b, t b ∈ (Finset.univ : Finset (Fin n)) := fun b => Finset.mem_univ _
  have := no_large_aligned_of_census_cap dom u₀ u₁ hcap hAa hka halign htinj htmem hnd
  rwa [hcardeq] at this

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.no_large_aligned_of_census_cap
#print axioms ProximityGap.Ownership.not_aligned_of_census_cap_lt
#print axioms ProximityGap.Ownership.aligned_supply_le_census_cap
#print axioms ProximityGap.Ownership.census_cap_ge_full_domain_supply
