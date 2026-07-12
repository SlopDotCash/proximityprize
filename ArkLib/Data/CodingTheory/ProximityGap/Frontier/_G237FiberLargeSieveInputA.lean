/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G233JacobiL2MassFloorNoGo
import Mathlib.Algebra.Order.Chebyshev

/-!
# G237: the fiber large-sieve is the phase-honest source of G233 input (A) (#466)

The quotient-Jacobi fanout no-go chain (G228→G234) culminates in G233's basis-independent
coefficient-L2 mass floor `l2_mass_floor_of_largesieve_parseval`, whose first exact analytic input
(sponsor regime `2 ∉ G`) is

* `(A)` the large-sieve operator bound  `‖V a‖² ≤ n² · ‖a‖²`  for every coefficient vector `a`.

G234 attempted to *derive* `(A)` from the structural premise "every Gram row-mass `≤ n²`" via the
elementary Schur / Gershgorin surrogate `λ_max ≤ max-abs-row-sum`.  Two independent referee probes
(G235 Result A, G236 fiber validation) then showed that premise is **false at sponsor scale**: the
absolute Gram row-mass reaches `1.2–1.7 · n²` as `m/n` grows, because the off-diagonal Gram entries
do not all align in phase and `max-abs-row-sum` over-counts the true top eigenvalue by a factor up
to `~8×`.  G234's abstract `schur_operator_bound` is correct, but its `R = n²` specialization
formalizes a lemma that is not true in exactly the cells that matter.

The honest, phase-honest source of `(A)` is the **direct fiber large-sieve**, whose sharp operator
constant is the maximal *fiber count* `maxfiber` (the largest number of subgroup elements `u ∈ G`
whose quotient class `cls u` coincides), and `maxfiber ≤ |G| = n` **trivially**, because the fibers
`{u ∈ G : cls u = d}` are pairwise-disjoint subsets of `G`.  This file formalizes that structural
core with **no character theory** — pure fiber Cauchy–Schwarz and a fiber-count bound — giving the
sharp operator inequality that replaces G234's false-at-scale row-mass premise.

The character-theory-free structural invariant is:

```text
∑_{d ∈ cls '' G} ‖∑_{u ∈ G, cls u = d} F u‖²  ≤  maxfiber · ∑_{u ∈ G} ‖F u‖²,   maxfiber ≤ |G|,
```

which is the fiber-Cauchy heart of the G236-validated chain
`∑_{χ≠1}|Va(χ)|² = (1/m)∑_D|T_D|²  ≤  (maxfiber/m)∑_{u∈G}|F_a(u)|² = (maxfiber·n/m)·(m/…)`.  Feeding
`maxfiber ≤ n` and the multiplicative-character Parseval `∑_{u∈G}|F_a(u)|² = n‖a‖²` (the one
remaining Mathlib character-theory input, quarantined here as an explicit hypothesis rather than
smuggled in as a false structural claim) into this bound yields `(A)` with the sharp constant `n²`.

Scope.  Keystone correctness upgrade of the G228→G234 chain: it installs the sharp, phase-honest
operator bound and closes G234's silent scope error (a premise valid only for small `m/n`).  It is
not a new character-sum estimate and does not consume the target.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G237FiberLargeSieveInputA

open Finset

variable {α β : Type*}

/-! ## Fiber Cauchy–Schwarz for a single quotient class -/

/-- **Single-fiber Cauchy–Schwarz.**  For any finite fiber `t : Finset α` and `F : α → ℂ`, the
squared norm of the fiber sum is bounded by the fiber cardinality times the fiber energy:

```text
‖∑_{u ∈ t} F u‖² ≤ #t · ∑_{u ∈ t} ‖F u‖².
```

Proof: triangle inequality `‖∑ F‖ ≤ ∑ ‖F‖` on the (nonnegative) reals, then the real Cauchy–Schwarz
`(∑ g)² ≤ #t · ∑ g²` (`sq_sum_le_card_mul_sum_sq`) with `g u = ‖F u‖`. -/
theorem fiber_cauchy (t : Finset α) (F : α → ℂ) :
    ‖∑ u ∈ t, F u‖ ^ 2 ≤ (t.card : ℝ) * ∑ u ∈ t, ‖F u‖ ^ 2 := by
  have htri : ‖∑ u ∈ t, F u‖ ≤ ∑ u ∈ t, ‖F u‖ := norm_sum_le _ _
  have hsq : ‖∑ u ∈ t, F u‖ ^ 2 ≤ (∑ u ∈ t, ‖F u‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖∑ u ∈ t, F u‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 htri 2
  have hcs : (∑ u ∈ t, ‖F u‖) ^ 2 ≤ (t.card : ℝ) * ∑ u ∈ t, ‖F u‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact hsq.trans hcs

/-! ## The abstract fiber large-sieve operator bound -/

/-- **Fiber large-sieve operator bound (structural core, no character theory).**

Let `G : Finset α` be a finite index set (the subgroup, `|G| = n`), `cls : α → β` a class map, and
`D : Finset β` a set of classes with `cls` mapping `G` into `D`.  For any `F : α → ℂ`, define the
class-sum `T d := ∑_{u ∈ G, cls u = d} F u`.  Then

```text
∑_{d ∈ D} ‖T d‖² ≤ R · ∑_{u ∈ G} ‖F u‖²
```

whenever every fiber has cardinality `≤ R` (`hfib : ∀ d ∈ D, #(G.filter (cls · = d)) ≤ R`).

This is exactly the fiber-Cauchy heart of the G236-validated large-sieve chain; the operator
constant is the maximal fiber count `R`, and the proof is a per-fiber Cauchy–Schwarz
(`fiber_cauchy`) recombined by `sum_fiberwise`.  No spectral decomposition, no phase alignment, no
character orthogonality. -/
theorem fiber_largesieve_operator_bound
    [DecidableEq β] (G : Finset α) (cls : α → β) (D : Finset β) (F : α → ℂ) (R : ℝ)
    (hmaps : ∀ u ∈ G, cls u ∈ D)
    (hfib : ∀ d ∈ D, ((G.filter (fun u => cls u = d)).card : ℝ) ≤ R) :
    ∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2
      ≤ R * ∑ u ∈ G, ‖F u‖ ^ 2 := by
  classical
  -- Per-fiber Cauchy–Schwarz, then bound each fiber card by `R`.
  have hEnergy_nonneg : ∀ d ∈ D,
      (0 : ℝ) ≤ ∑ u ∈ G.filter (fun u => cls u = d), ‖F u‖ ^ 2 :=
    fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hstep : ∀ d ∈ D,
      ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2
        ≤ R * ∑ u ∈ G.filter (fun u => cls u = d), ‖F u‖ ^ 2 := by
    intro d hd
    refine (fiber_cauchy (G.filter (fun u => cls u = d)) F).trans ?_
    exact mul_le_mul_of_nonneg_right (hfib d hd) (hEnergy_nonneg d hd)
  calc ∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2
      ≤ ∑ d ∈ D, R * ∑ u ∈ G.filter (fun u => cls u = d), ‖F u‖ ^ 2 :=
        Finset.sum_le_sum hstep
    _ = R * ∑ d ∈ D, ∑ u ∈ G.filter (fun u => cls u = d), ‖F u‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = R * ∑ u ∈ G, ‖F u‖ ^ 2 := by
        rw [Finset.sum_fiberwise_of_maps_to hmaps]

/-! ## The fiber-count bound `maxfiber ≤ n` (trivial, phase-honest) -/

/-- **Fiber-count ceiling.**  Every fiber `{u ∈ G : cls u = d}` is a subset of `G`, hence its
cardinality is at most `#G = n`.  This is the sharp, structurally-honest replacement for G234's
false-at-scale `Gram-row-mass ≤ n²` premise: the true operator constant is a *fiber count*, and it
is `≤ n` for the trivial reason that the fibers partition `G`. -/
theorem fiber_card_le (G : Finset α) (cls : α → β) (d : β)
    [DecidablePred (fun u => cls u = d)] :
    (G.filter (fun u => cls u = d)).card ≤ G.card :=
  Finset.card_filter_le _ _

/-! ## Input (A) from the fiber large-sieve, sharp constant `n²` -/

/-- **Large-sieve input (A) from the fiber bound and multiplicative-character Parseval.**

Chaining the structural fiber operator bound with constant `maxfiber ≤ n`
(`fiber_largesieve_operator_bound` + `fiber_card_le`) and the multiplicative-character Parseval
`∑_{u ∈ G} ‖F u‖² = n · ‖a‖²` (`hParseval`, the single remaining character-theory input, kept
explicit) yields G233's input `(A)`:

```text
∑_{d ∈ D} ‖T d‖²  ≤  n · ∑_{u ∈ G} ‖F u‖²  =  n · (n · ‖a‖²)  =  n² · ‖a‖².
```

The Parseval identity `∑_x |Va(χ)|² = (1/m)∑_D|T_D|² − k₀` of the G236 chain then upgrades this to
the operator bound on `Va` itself; here we deliver the sharp fiber-side inequality, which is the
part G234 got wrong (its `n²` came from a false absolute row-mass, this `n²` comes from the honest
`maxfiber ≤ n` fiber count times the Parseval energy `n·‖a‖²`).  Constant `n²` is sharp: equality
in `fiber_largesieve_operator_bound` is achievable when a single fiber saturates, so no smaller
constant is structurally forced. -/
theorem largesieve_inputA_of_fiber_parseval
    [DecidableEq β] (G : Finset α) (cls : α → β) (D : Finset β) (F : α → ℂ)
    (n : ℕ) (aNorm2 : ℝ)
    (hmaps : ∀ u ∈ G, cls u ∈ D)
    (hcard : G.card = n)
    (hParseval : ∑ u ∈ G, ‖F u‖ ^ 2 = (n : ℝ) * aNorm2) :
    ∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2
      ≤ (n : ℝ) ^ 2 * aNorm2 := by
  classical
  have hfib : ∀ d ∈ D, ((G.filter (fun u => cls u = d)).card : ℝ) ≤ (n : ℝ) := by
    intro d _
    have : (G.filter (fun u => cls u = d)).card ≤ G.card := fiber_card_le G cls d
    calc ((G.filter (fun u => cls u = d)).card : ℝ)
        ≤ (G.card : ℝ) := by exact_mod_cast this
      _ = (n : ℝ) := by rw [hcard]
  calc ∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2
      ≤ (n : ℝ) * ∑ u ∈ G, ‖F u‖ ^ 2 :=
        fiber_largesieve_operator_bound G cls D F (n : ℝ) hmaps hfib
    _ = (n : ℝ) * ((n : ℝ) * aNorm2) := by rw [hParseval]
    _ = (n : ℝ) ^ 2 * aNorm2 := by ring

/-! ## Wiring the honest input (A) into the G233 mass floor -/


open ArkLib.ProximityGap.Frontier.G233JacobiL2MassFloorNoGo in
/-- **G233 mass floor with input (A) supplied by the fiber large-sieve.**

Combining `largesieve_inputA_of_fiber_parseval` (the *honest, phase-correct* input `(A)` with
sharp constant `n²` from the fiber count `maxfiber ≤ n` and multiplicative Parseval) with the
sponsor Parseval `(B)` and half capture gives the division-free coefficient mass floor
`m − n ≤ 4 · n · ‖a‖²`.

Unlike G234's `l2_mass_floor_of_gram_rowmass_parseval` — whose `hrow : Gram-row-mass ≤ n²` premise
is false at sponsor scale (`m/n` large) — the input `(A)` here rests on the trivially-true fiber
count `#(fiber) ≤ #G = n` and the character-Parseval energy identity, so the whole chain is sound
in exactly the cells that matter.

The reconstruction mass consumed by `l2_mass_floor_of_largesieve_parseval` is the class-sum energy
`∑_d ‖T d‖²` and the coefficient mass is `aNorm2`; the only surviving premises are the maps-to fact,
the character Parseval energy identity `(hParseval)`, the sponsor Parseval `(hSponsor)`, and half
capture `(hHalf)`. -/
theorem l2_mass_floor_of_fiber_parseval
    [DecidableEq β] (G : Finset α) (cls : α → β) (D : Finset β) (F : α → ℂ)
    (n m : ℕ) (hn : 0 < n) (aNorm2 sNorm2 : ℝ)
    (hmaps : ∀ u ∈ G, cls u ∈ D)
    (hcard : G.card = n)
    (hParseval : ∑ u ∈ G, ‖F u‖ ^ 2 = (n : ℝ) * aNorm2)
    (hSponsor : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ ∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2) :
    (m : ℝ) - n ≤ 4 * n * aNorm2 :=
  l2_mass_floor_of_largesieve_parseval n m hn aNorm2
    (∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2)
    sNorm2
    (largesieve_inputA_of_fiber_parseval G cls D F n aNorm2 hmaps hcard hParseval)
    hSponsor hHalf

end ArkLib.ProximityGap.Frontier.G237FiberLargeSieveInputA
