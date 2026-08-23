/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DistinctPeriodMomentLaw
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The distinct-period SECOND MOMENT: `∑_{t∈T} ‖η_t‖² = q − n` (issues #407, #444)

`SubgroupGaussSumSecondMoment.subgroup_gaussSum_secondMoment` gives the field-level Parseval
identity over ALL `q` frequencies
`∑_{b∈F} ‖η_b‖² = q·|μ_n| = q·n`, and `DistinctPeriodMomentLaw` proved the coset-collapse
engine for the COMPLEX power-sum `∑_{b≠0} η_bʳ = n·∑_{t∈T} η_tʳ`.  Neither file carried the
NORM-squared (`‖·‖²`, Parseval) reindexing the prize's *average period magnitude* baseline needs.

This file supplies that step.  The modulus `‖η_b‖²` is constant on each `μ_n`-coset
(`eta_norm_const_on_coset`), so the same orbit partition `nonzeroFreqs = ⨆_{t∈T} fiber t`
collapses the nonzero-spectrum energy:

  **`∑_{b≠0} ‖η_b‖² = n · ∑_{t∈T} ‖η_t‖²`**     (`nonzero_normSq_sum_eq_card_mul`),

and subtracting the principal term `‖η_0‖² = |μ_n|² = n²` from the Parseval total `q·n` gives the
nonzero-spectrum energy `q·n − n²`, hence the headline DISTINCT-period second moment

  **`∑_{t∈T} ‖η_t‖² = q − n`**     (`distinctPeriod_secondMoment`),

an EXACT integer over the `m = (q−1)/n` distinct Gaussian periods.  The **average** distinct-period
energy is `(q−n)/m`, which `→ n` as `q → ∞` (since `m·n = q−1`, so `(q−n)/m = n·(q−n)/(q−1) → n`;
e.g. `15.94…15.99` for `n=16` in the probe).  This is the **L²/average baseline** the open BGK/Paley
sup `B = max_{b≠0} ‖η_b‖` must beat: the periods average to `≈√n` in modulus; the prize asks the
*worst-case* one to be `≤ C√(n·log(q/n))`, a `√(log m)`-factor above this exactly-pinned average
energy `∑_T‖η_t‖² = q−n`.

## Probe (`scripts/probes/probe_distinct_period_secondmoment.py`, ONE sweep, NEVER `n = q−1`)

Exact `ℂ`, PROPER thin `μ_n = ⟨g^{(q−1)/n}⟩ ⊊ Fₚ*`, `n = 2^a`, `p ≡ 1 mod n`, multi-prime
incl. `p ≫ n³` (`4129, 40961, 7681, 12289`) and Fermat `257`, NEVER `n = q−1`:
`∑_{t∈T} ‖η_t‖² = q − n` in **13/13** configs (full `= q·n`, nonzero `= q·n − n²`, distinct
`= q − n` all exact), and the average `(q−n)/m → n` (`15.94…15.99` for `n=16` as `q` grows).

## Scope (rules 1, 3, 4, 6 + ASYMPTOTIC GUARD — honesty contract)

NOT a CORE closure, NOT a refutation, NOT thinness-essential (true for every `n ∣ q−1`).  This is
the EXACT L²/average period energy — the OPPOSITE scale from the open sup `B`: it pins the
*average* `‖η_t‖²` to `n` but says NOTHING about the *max*, which is the BGK/Paley wall.  It is
EXTEND-proven (consumes the proven Parseval second moment + the proven coset-collapse engine) and
NON-MOMENT in the prize sense (no `|·|^{2r}` energy ladder, no Wick expansion — it is the `r=1`
Parseval norm, a single exact additive-character orthogonality, not a moment route).  No
capacity / beyond-Johnson / `δ*` / cliff-at-`n/2` claim; the average→max gap `√(log m)` is exactly
the wall and is UNTOUCHED.  CORE (`M(μ_n) ≤ C·√(n·log(q/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier.DistinctPeriodMomentLaw

namespace ArkLib.ProximityGap.Frontier.DistinctPeriodSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`‖η‖²` is constant `= ‖η_t‖²` on the fiber `t•μ_n`.** The modulus descends to the quotient
`Fₚ*/μ_n` (`eta_norm_const_on_coset`), so squaring it is constant on each coset fiber. The
norm-squared analogue of `eta_const_on_fiber`. -/
theorem normSq_const_on_fiber {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) {t b : F}
    (hb : b ∈ fiber n t) :
    ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2
      = ‖eta ψ (nthRootsFinset n (1 : F)) t‖ ^ 2 := by
  rw [eta_const_on_fiber hn hb]

/-- **The fiber energy collapses to `n · ‖η_t‖²`.** Summing `‖η_b‖²` over a single `μ_n`-coset
fiber `t•μ_n` gives `n · ‖η_t‖²` (modulus-constancy `normSq_const_on_fiber` + fiber size `n`
`coset_fiber_card`). The norm-squared analogue of `sum_pow_on_fiber`. -/
theorem sum_normSq_on_fiber {ψ : AddChar F ℂ} {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n)
    (hn : 0 < n) {t : F} (ht : t ≠ 0) :
    ∑ b ∈ fiber n t, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2
      = (n : ℝ) * ‖eta ψ (nthRootsFinset n (1 : F)) t‖ ^ 2 := by
  classical
  have hconst : ∀ b ∈ fiber n t,
      ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2
        = ‖eta ψ (nthRootsFinset n (1 : F)) t‖ ^ 2 := by
    intro b hb; rw [normSq_const_on_fiber hn hb]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, fiber, coset_fiber_card hζprim hn ht,
    nsmul_eq_mul]

/-- **The nonzero-spectrum energy reindexes to `n` times the distinct-period energy.** For a coset
transversal `T` of `Fₚ*/μ_n` (under a primitive `n`-th root `ζ`),
`∑_{b≠0} ‖η_b‖² = n · ∑_{t∈T} ‖η_t‖²` — the orbit partition `nonzeroFreqs = ⨆_{t∈T} fiber t`
(`nonzeroFreqs_eq_biUnion_fibers`) with each fiber-energy collapsed (`sum_normSq_on_fiber`). The
norm-squared analogue of `rawMoment_erase_zero_eq_card_mul_repSum`. -/
theorem nonzero_normSq_sum_eq_card_mul {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) :
    ∑ b ∈ nonzeroFreqs F, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2
      = (n : ℝ) * ∑ t ∈ T, ‖eta ψ (nthRootsFinset n (1 : F)) t‖ ^ 2 := by
  classical
  -- disjointness of the fibers (distinct labels ⇒ disjoint fibers).
  have hdisj : (T : Set F).PairwiseDisjoint (fiber n) := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr ?_
    intro x hxa hxb
    rw [fiber, Finset.mem_filter] at hxa hxb
    exact hab (hT.inj a ha b hb (hxa.2.symm.trans hxb.2))
  have htne : ∀ t ∈ T, t ≠ 0 := by
    intro t ht; have := hT.subset ht; rwa [mem_nonzeroFreqs] at this
  have hcover : nonzeroFreqs F = T.biUnion (fiber n) := nonzeroFreqs_eq_biUnion_fibers hT
  rw [hcover, Finset.sum_biUnion hdisj, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  exact sum_normSq_on_fiber hζprim hn (htne t ht)

/-- **The distinct-period second moment.** For a finite multiplicative subgroup `μ_n ⊆ Fₚ*`
(under a primitive `n`-th root `ζ`) with a coset transversal `T` of `Fₚ*/μ_n`,
`n · ∑_{t∈T} ‖η_t‖² = q·n − n²` — the Parseval total `∑_{b∈F}‖η_b‖² = q·n`
(`subgroup_gaussSum_secondMoment`) with the principal term `‖η_0‖² = n²` stripped, reindexed by
the coset collapse `nonzero_normSq_sum_eq_card_mul`. This is the L²/average energy of the
distinct Gaussian periods, the exact baseline the open sup `B = max_{b≠0}‖η_b‖` must beat. -/
theorem card_mul_distinctPeriod_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {n : ℕ}
    {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) :
    (n : ℝ) * ∑ t ∈ T, ‖eta ψ (nthRootsFinset n (1 : F)) t‖ ^ 2
      = (Fintype.card F : ℝ) * (n : ℝ)
          - ((nthRootsFinset n (1 : F)).card : ℝ) ^ 2 := by
  classical
  -- the subgroup card is `n` (primitive `n`-th root).
  have hcard : (nthRootsFinset n (1 : F)).card = n :=
    IsPrimitiveRoot.card_nthRootsFinset hζprim
  -- Parseval over all `b ∈ F`, splitting off `b = 0`.
  have hpars : ∑ b : F, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2
      = (Fintype.card F : ℝ) * ((nthRootsFinset n (1 : F)).card : ℝ) :=
    subgroup_gaussSum_secondMoment hψ (nthRootsFinset n (1 : F))
  -- `univ = insert 0 (nonzeroFreqs F)`, so the full sum = (b=0 term) + (nonzero sum).
  have hsplit : ∑ b : F, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2
      = ‖eta ψ (nthRootsFinset n (1 : F)) 0‖ ^ 2
        + ∑ b ∈ nonzeroFreqs F, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2 := by
    rw [nonzeroFreqs, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F)), add_comm]
  -- the principal term `‖η_0‖² = (|μ_n|)²`: `η_0 = ∑_{y∈G} ψ 0 = |G|`.
  have hzero : ‖eta ψ (nthRootsFinset n (1 : F)) 0‖ ^ 2
      = ((nthRootsFinset n (1 : F)).card : ℝ) ^ 2 := by
    have heta0 : eta ψ (nthRootsFinset n (1 : F)) 0
        = ((nthRootsFinset n (1 : F)).card : ℂ) := by
      simp only [SubgroupGaussSumSecondMoment.eta, zero_mul, AddChar.map_zero_eq_one,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [heta0, Complex.norm_natCast]
  -- combine.
  have hnz : ∑ b ∈ nonzeroFreqs F, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ 2
      = (Fintype.card F : ℝ) * ((nthRootsFinset n (1 : F)).card : ℝ)
          - ((nthRootsFinset n (1 : F)).card : ℝ) ^ 2 := by
    have := hsplit
    rw [hpars, hzero] at this
    linarith [this]
  rw [← nonzero_normSq_sum_eq_card_mul hζprim hn hT, hnz, hcard]

/-- **The headline distinct-period second moment: `∑_{t∈T} ‖η_t‖² = q − n`.** Dividing the
`card_mul_distinctPeriod_secondMoment` identity `n·∑_T‖η_t‖² = q·n − n²` by `n = |μ_n| > 0`.
EXACT integer over the `m = (q−1)/n` distinct Gaussian periods. -/
theorem distinctPeriod_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {n : ℕ}
    {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) :
    ∑ t ∈ T, ‖eta ψ (nthRootsFinset n (1 : F)) t‖ ^ 2
      = (Fintype.card F : ℝ) - (n : ℝ) := by
  have hcard : (nthRootsFinset n (1 : F)).card = n :=
    IsPrimitiveRoot.card_nthRootsFinset hζprim
  have hkey := card_mul_distinctPeriod_secondMoment hψ hζprim hn hT
  rw [hcard] at hkey
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- `n · S = q·n − n²`, divide by `n`.
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  field_simp at hkey ⊢
  nlinarith [hkey]

/-- **The distinct-period energy sits strictly below the trivial `q` ceiling.** Over a PROPER thin
subgroup (`0 < n`), `∑_{t∈T} ‖η_t‖² = q − n < q`. The L²/average total is bounded by `q` (the
naive sup-squared-times-count ceiling `m·n` would also be `q − n` since `m·n = q − 1`... ` no):
this records the exact deficit `n` below the field size. Honest exact integer fact, the L²
baseline the open sup `B` lives above. -/
theorem distinctPeriod_secondMoment_lt_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {n : ℕ}
    {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) :
    ∑ t ∈ T, ‖eta ψ (nthRootsFinset n (1 : F)) t‖ ^ 2
      < (Fintype.card F : ℝ) := by
  rw [distinctPeriod_secondMoment hψ hζprim hn hT]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith

end ArkLib.ProximityGap.Frontier.DistinctPeriodSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.DistinctPeriodSecondMoment.sum_normSq_on_fiber
#print axioms
  ArkLib.ProximityGap.Frontier.DistinctPeriodSecondMoment.nonzero_normSq_sum_eq_card_mul
#print axioms
  ArkLib.ProximityGap.Frontier.DistinctPeriodSecondMoment.card_mul_distinctPeriod_secondMoment
#print axioms ArkLib.ProximityGap.Frontier.DistinctPeriodSecondMoment.distinctPeriod_secondMoment
#print axioms
  ArkLib.ProximityGap.Frontier.DistinctPeriodSecondMoment.distinctPeriod_secondMoment_lt_card
