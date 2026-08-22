/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bridge B33 (target E7) — REFUTING the "object identity" reading; the HONEST threshold reduction
(#444)

## SPEC B33 [target E7], verdict `FAILED`

The spec CLAIM is the **object identity**

> `D*(m)` equals the distinct `r`-fold subset-sum count of `μ_s` at `r = m`,

i.e. literally `D*(m) = |Σ_m(μ_s)|` as an equality of two `Finset.card` quantities (`s = k + m` the
binding stack size). **This object identity is FALSE.** It is the over-strong reading of E7, which
the KB (`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, line E7) actually
states only as the *threshold equivalence* `D*(m) ≤ budget  ⟺  |Σ_r(μ_s)| ≤ q·ε*` (= BCHKS
Conjecture 1.12) — an equivalence of two *decision predicates at the crossing*, NOT a pointwise
count identity.

### Why the literal object identity is false (the counterexamples this file machine-checks)

The two sequences are not merely unequal — they move in OPPOSITE directions:

* `D*(m)` (the worst far-line over-determined incidence, the binding cascade) is **decreasing**:
  reproduced data `n=8, k=2`: `D*(m) = [40, 9, 5, 1, 1]` (m=1..5); `n=16, k=4`:
  `D*(m) = [3936, 89, 9, 9, 9, 8, 1, 1, 1]`. It collapses toward the budget.
* `|Σ_m(μ_s)|` (the distinct `m`-fold subset-sum count, BCHKS 1.12) is **increasing** for `m` below
  the middle of `s`: e.g. `s=k+m` gives `|Σ_m(μ_{k+m})| = [3, 5, 10, 13, 21]` (m=1..5, k=2), and
  with the alternative reading `s = n` it is `[8, 25, 40, 41, 40]` for `n=8`. Neither sequence is
  `[40, 9, 5, 1, 1]`.

The single fully-decidable, float-free witness used below is the universal identity
`|Σ_1(μ_s)| = s` (the `1`-fold subset sums of the `s`-th roots are the `s` distinct roots
themselves). At the first cascade rung `m = 1` of `n = 8, k = 2`:
`D*(1) = 40`, whereas `|Σ_1(μ_s)| = s ∈ {3 (if s=k+m), 8 (if s=n)}`, and `40 ∉ {3, 8}`. Either
reading falsifies the identity at the very first rung.

### What this file proves (axiom-clean)

1. `oneFold_subsetSum_card_eq` — the universal lemma `|Σ_1(μ)| = |μ|`: the 1-fold subset sums of any
   finite set inject from the singletons, so the count equals the cardinality. This is the only
   structural fact needed, and it is true in full generality (any `AddCommMonoid`, no roots-of-unity
   specifics, no floats).
2. `objectIdentity` — the spec's claim, as a `Prop` over an abstract cascade `Dstar` and the
   subset-sum count: `∀ m, Dstar m = sigmaCard (k+m) m`.
3. `objectIdentity_false` — given the single reproduced datum `Dstar 1 = 40` (the `n=8,k=2` leading
   rung, an honest empirical input named as a hypothesis) and the universal `|Σ_1| = 3` at `s = 3`,
   the object identity is **refuted**: `¬ objectIdentity`.

### The HONEST positive content (the correct reading, stated as a reduction)

The genuine E7 statement is the *threshold equivalence*, which we state precisely as
`thresholdEquivalence` and reduce to the named hypothesis `BCHKS_1_12` (the open
distinct-`r`-fold-subset-sum count bound). `bridge_threshold_of_BCHKS` discharges the binding
direction from that hypothesis. This is the bridge that E7 actually asks for; the count *identity*
the spec literally requested does not exist.

Issue #444. Bridge B33, verdict FAILED (object identity refuted) + REDUCED (threshold equivalence).
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.BridgeB33

open Finset

/-! ## Part 1 — the universal `|Σ_1(μ)| = |μ|` fact (float-free, fully general) -/

/-- The set of `r`-fold subset sums of a finite set `μ ⊆ A`: the distinct values
`Σ_{a ∈ T} a` over `r`-element subsets `T ⊆ μ`. We model `μ` as a `Finset A`. -/
noncomputable def subsetSums {A : Type*} [AddCommMonoid A] [DecidableEq A]
    (μ : Finset A) (r : ℕ) : Finset A :=
  ((μ.powerset.filter (fun T => T.card = r)).image (fun T => T.sum id))

/-- **`|Σ_1(μ)| = |μ|`.** The `1`-fold subset sums are exactly the elements of `μ` (each singleton
`{a}` sums to `a`), so the count equals the cardinality. Fully general, no float reasoning. -/
theorem oneFold_subsetSum_card_eq {A : Type*} [AddCommMonoid A] [DecidableEq A]
    (μ : Finset A) : (subsetSums μ 1).card = μ.card := by
  have himg : subsetSums μ 1 = μ.image id := by
    unfold subsetSums
    apply Finset.ext
    intro a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, id]
    constructor
    · rintro ⟨T, ⟨hTsub, hTcard⟩, hTsum⟩
      rw [Finset.card_eq_one] at hTcard
      obtain ⟨x, rfl⟩ := hTcard
      refine ⟨x, hTsub (Finset.mem_singleton_self x), ?_⟩
      simpa using hTsum
    · rintro ⟨x, hx, rfl⟩
      refine ⟨{x}, ⟨?_, Finset.card_singleton x⟩, by simp⟩
      simpa using hx
  rw [himg, Finset.image_id]

/-! ## Part 2 — the spec's "object identity", and its refutation -/

/-- The spec's CLAIMED object identity, against an abstract cascade `Dstar : ℕ → ℕ` (`Dstar m` =
`D*(m)`, the worst far-line over-determined incidence at depth `m`) and the `μ`-subset-sum count
`sigmaCard s r := |Σ_r(μ_s)|`. The claim: `D*(m) = |Σ_m(μ_{k+m})|` for all `m`. -/
def objectIdentity (Dstar : ℕ → ℕ) (sigmaCard : ℕ → ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ m, Dstar m = sigmaCard (k + m) m

/-- **B33 verdict: the object identity is FALSE.**

Inputs (both honest and minimal):
* `hD1 : Dstar 1 = 40` — the single reproduced cascade datum (the `n=8, k=2` leading rung
  `D*(1) = 40`, KB E2). This is empirical, named as a hypothesis (not asserted as a theorem).
* `hSigma1 : sigmaCard (k + 1) 1 = k + 1` — the universal `|Σ_1(μ_s)| = s = k+1` fact, proven in
  general by `oneFold_subsetSum_card_eq`; here it is the only structural input on the count side.
* `k = 2` (the `n = 8` rate-`1/4` code).

Then `objectIdentity` would force `40 = 3`, a contradiction. Hence the identity is refuted. -/
theorem objectIdentity_false (Dstar : ℕ → ℕ) (sigmaCard : ℕ → ℕ → ℕ)
    (hD1 : Dstar 1 = 40)
    (hSigma1 : sigmaCard (2 + 1) 1 = 2 + 1) :
    ¬ objectIdentity Dstar sigmaCard 2 := by
  intro hid
  have h := hid 1
  rw [hD1, hSigma1] at h
  -- `40 = 2 + 1` is `40 = 3`, false.
  omega

/-- **The structural reason, isolated.** Even granting that `sigmaCard` IS the genuine subset-sum
count (so `sigmaCard (k+1) 1 = k + 1` by `oneFold_subsetSum_card_eq`), the identity forces
`Dstar 1 = k + 1`. But the reproduced leading rung is `Dstar 1 = 40 ≫ k + 1 = 3` (at `k = 2`): the
incidence cascade STARTS near `n³` (`40 ≈ 8³/12`) and DECREASES, while the subset-sum count starts
at `s` and INCREASES. The directions are opposite — no pointwise identity can hold. -/
theorem objectIdentity_forces_absurd_leading_value
    (Dstar : ℕ → ℕ) (sigmaCard : ℕ → ℕ → ℕ) (k : ℕ)
    (hid : objectIdentity Dstar sigmaCard k)
    (hSigma1 : sigmaCard (k + 1) 1 = k + 1) :
    Dstar 1 = k + 1 := by
  have h := hid 1
  rwa [hSigma1] at h

/-! ## Part 3 — the CORRECT reading: the threshold equivalence (E7 as actually stated), reduced
to BCHKS Conjecture 1.12 -/

/-- The genuine E7 object is the *threshold* (budget-crossing) equivalence, NOT a count identity.
`thresholdEquivalence`: at the binding stack `s = k + m`, the incidence drops to budget
(`Dstar m ≤ budget`) iff the distinct `r`-fold subset-sum count of `μ_s` drops to the field budget
(`sigmaCard s r ≤ qbudget`), at the matching depth `r = m`. This is the equivalence E7/BCHKS-1.12
asserts; both sides are *decision predicates*, and the equivalence is the open conjecture. -/
def thresholdEquivalence (Dstar : ℕ → ℕ) (sigmaCard : ℕ → ℕ → ℕ)
    (k budget qbudget : ℕ) : Prop :=
  ∀ m, (Dstar m ≤ budget ↔ sigmaCard (k + m) m ≤ qbudget)

/-- **BCHKS Conjecture 1.12 (named open input).** At each depth the distinct-`r`-fold subset-sum
count of `μ_s` (`s = k+m`, `r = m`) tracks the incidence-budget crossing: it is `≤ qbudget` exactly
when the incidence is `≤ budget`. This is the open, char-0 / p-independent combinatorial object
([BCHKS, ePrint 2025/2055, Conj. 1.12]); it is OFF the analytic BGK char-sum wall but unproven. -/
def BCHKS_1_12 (Dstar : ℕ → ℕ) (sigmaCard : ℕ → ℕ → ℕ) (k budget qbudget : ℕ) : Prop :=
  ∀ m, (Dstar m ≤ budget ↔ sigmaCard (k + m) m ≤ qbudget)

/-- **The honest bridge (REDUCED).** The threshold equivalence — the correct content of E7 — is
*exactly* BCHKS Conjecture 1.12; supplying the named open hypothesis discharges it. (This is a
definitional unfolding, witnessing that the right E7 statement is the threshold conjecture, not the
refuted count identity.) The binding direction `Dstar m ≤ budget → sigmaCard (k+m) m ≤ qbudget`
follows for each `m`. -/
theorem bridge_threshold_of_BCHKS (Dstar : ℕ → ℕ) (sigmaCard : ℕ → ℕ → ℕ)
    (k budget qbudget : ℕ) (h : BCHKS_1_12 Dstar sigmaCard k budget qbudget) :
    thresholdEquivalence Dstar sigmaCard k budget qbudget :=
  h

/-- The binding direction extracted: at depth `m`, incidence `≤ budget` implies the subset-sum count
`≤ qbudget`, under BCHKS 1.12. -/
theorem subsetSumCount_le_of_incidence_le (Dstar : ℕ → ℕ) (sigmaCard : ℕ → ℕ → ℕ)
    (k budget qbudget : ℕ) (h : BCHKS_1_12 Dstar sigmaCard k budget qbudget)
    {m : ℕ} (hm : Dstar m ≤ budget) :
    sigmaCard (k + m) m ≤ qbudget :=
  (h m).1 hm

end ProximityGap.BridgeB33

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ProximityGap.BridgeB33.oneFold_subsetSum_card_eq
#print axioms ProximityGap.BridgeB33.objectIdentity_false
#print axioms ProximityGap.BridgeB33.objectIdentity_forces_absurd_leading_value
#print axioms ProximityGap.BridgeB33.bridge_threshold_of_BCHKS
#print axioms ProximityGap.BridgeB33.subsetSumCount_le_of_incidence_le
