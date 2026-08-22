/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PeriodMomentLaw
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031SupTransversalCollapse

/-!
# The distinct-period moment law: the coset-reindexing consumer step (#407, #444)

`SubgroupGaussSumRawMoment.subgroup_gaussSum_rawMoment` gives the field-level engine
`∑_{b∈F} η_bʳ = q·N₀(G,r)`, and `PeriodMomentLaw.rawMoment_erase_zero` subtracts the `b=0`
term to give the **nonzero-spectrum** form `∑_{b≠0} η_bʳ = q·N₀ − nʳ`. Both files note (in
prose only) that, since `η_b` is constant on each of the `m = (q−1)/n` `μ_n`-cosets of the
nonzero frequencies (`eta_dilation_invariant`), the nonzero-spectrum sum is `n` copies of the
**distinct-period** sum `∑_i η_iʳ` over the `m` distinct Gaussian periods, yielding the
*period moment law*

> `∑_i η_iʳ = (q/n)·N₀(G,r) − n^{r−1}`   (issue #407).

`I031SupTransversalCollapse.eta_norm_sup'_eq_of_transversal` proved the **sup/value-level** form
of this collapse (`sup_{b≠0}‖η_b‖ = sup_{t∈T}‖η_t‖` over a coset transversal `T`), but the
**sum-power moment** form — the actual `∑_i η_iʳ` reindexing the period moment law of #407 needs —
was never stated as a theorem. This file proves that coset-reindexing consumer step, in the
division-free form

> `n · ∑_{t∈T} η_tʳ = ∑_{b≠0} η_bʳ = q·N₀(G,r) − nʳ`,

for the SAME concrete `IsCosetTransversal n T` predicate the I031 sup capstone uses (one
representative per `μ_n`-coset of `Fₚ*`). The factor `n = |μ_n|` is the coset multiplicity; under
a primitive `n`-th root `|T| = (q−1)/n` (`transversal_card`) and dividing by `n` recovers the
prose `∑_i η_iʳ = (q/n)·N₀ − n^{r−1}` form.

The proof reindexes `∑_{b≠0} η_bʳ` along the proven orbit partition
`nonzeroFreqs F = ⨆_{t∈T} fiber t` (`nonzeroFreqs_eq_biUnion_fibers`), collapses each fiber-sum to
`n · η_tʳ` (`eta_dilation_invariant` constancy + `coset_fiber_card` size `n`), and equates with the
proven field-level moment (`rawMoment_erase_zero`).

NON-MOMENT structural (pure coset-partition reindexing — no thinness, no √-cancellation; the
char-independent backbone that pins every period power-sum to the integer additive relation count
`N₀`, which is exactly *why* the conjecture-bank power-sum routes carry no extra cancellation).
EXTEND-proven (sits on the proven `rawMoment_erase_zero`, `eta_dilation_invariant`, and the I031
transversal partition). **NOT** a CORE/BGK result; no capacity/beyond-Johnson/`δ*` claim, and
**not** thinness-essential (true for every `n ∣ q−1`).

Axiom-clean. Issues #407, #444.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction
open ArkLib.ProximityGap.PeriodMomentLaw
open ArkLib.ProximityGap.I031DilationOrbitReduction

namespace ArkLib.ProximityGap.Frontier.DistinctPeriodMomentLaw

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The fiber of the coset-label map over a representative `t`: the `μ_n`-coset `t•μ_n` realised as
a subset of the nonzero frequencies. -/
noncomputable def fiber (n : ℕ) (t : F) : Finset F :=
  (nonzeroFreqs F).filter (fun x => cosetLabel n x = cosetLabel n t)

/-- **`η` is constant `= η_t` on the fiber `t•μ_n`.** Each `b` in the fiber lies in the coset
`cosetLabel n t = t•μ_n`, i.e. `b = x·t` with `x ∈ μ_n`, so `η_b = η_{x·t} = η_t`
(`eta_dilation_invariant`). -/
theorem eta_const_on_fiber {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) {t b : F}
    (hb : b ∈ fiber n t) :
    eta ψ (nthRootsFinset n (1 : F)) b = eta ψ (nthRootsFinset n (1 : F)) t := by
  classical
  rw [fiber, Finset.mem_filter] at hb
  obtain ⟨hb0, hlabel⟩ := hb
  -- `b ∈ cosetLabel n b = cosetLabel n t`, so `b = x * t` with `x ∈ μ_n`.
  have hb_in : b ∈ cosetLabel n t := by
    rw [← hlabel]; exact self_mem_cosetLabel hn b
  rw [cosetLabel, dilate, Finset.mem_image] at hb_in
  obtain ⟨x, hx, rfl⟩ := hb_in
  rw [mul_comm t x]
  exact eta_dilation_invariant hx t

/-- **The fiber-sum collapses to `n · η_tʳ`.** Summing `η_bʳ` over a single `μ_n`-coset fiber
`t•μ_n` gives `n · η_tʳ` (value-constancy `eta_const_on_fiber` + fiber size `n`
`coset_fiber_card`). -/
theorem sum_pow_on_fiber {ψ : AddChar F ℂ} {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (rexp : ℕ) {t : F} (ht : t ≠ 0) :
    ∑ b ∈ fiber n t, eta ψ (nthRootsFinset n (1 : F)) b ^ rexp
      = (n : ℂ) * eta ψ (nthRootsFinset n (1 : F)) t ^ rexp := by
  classical
  have hconst : ∀ b ∈ fiber n t,
      eta ψ (nthRootsFinset n (1 : F)) b ^ rexp
        = eta ψ (nthRootsFinset n (1 : F)) t ^ rexp := by
    intro b hb; rw [eta_const_on_fiber hn hb]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, fiber, coset_fiber_card hζprim hn ht,
    nsmul_eq_mul]

/-- **The nonzero-spectrum sum reindexes to `n` times the distinct-period sum.** For a coset
transversal `T` of `Fₚ*/μ_n` (under a primitive `n`-th root `ζ`),
`∑_{b≠0} η_bʳ = n · ∑_{t∈T} η_tʳ` — the orbit partition `nonzeroFreqs = ⨆_{t∈T} fiber t`
(`nonzeroFreqs_eq_biUnion_fibers`) with each fiber-sum collapsed (`sum_pow_on_fiber`). -/
theorem rawMoment_erase_zero_eq_card_mul_repSum {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) (rexp : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), eta ψ (nthRootsFinset n (1 : F)) b ^ rexp
      = (n : ℂ) * ∑ t ∈ T, eta ψ (nthRootsFinset n (1 : F)) t ^ rexp := by
  classical
  -- the disjointness of the fibers (distinct labels ⇒ disjoint fibers).
  have hdisj : (T : Set F).PairwiseDisjoint (fiber n) := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr ?_
    intro x hxa hxb
    rw [fiber, Finset.mem_filter] at hxa hxb
    exact hab (hT.inj a ha b hb (hxa.2.symm.trans hxb.2))
  have htne : ∀ t ∈ T, t ≠ 0 := by
    intro t ht; have := hT.subset ht; rwa [mem_nonzeroFreqs] at this
  -- `univ.erase 0 = nonzeroFreqs F = ⨆_{t∈T} fiber t`.
  have hcover : Finset.univ.erase (0 : F)
      = T.biUnion (fiber n) := nonzeroFreqs_eq_biUnion_fibers hT
  rw [hcover, Finset.sum_biUnion hdisj, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  exact sum_pow_on_fiber hζprim hn rexp (htne t ht)

/-- **The distinct-period moment law (division-free form).** For a finite multiplicative subgroup
`μ_n ⊆ Fₚ*` (under a primitive `n`-th root `ζ`) with a coset transversal `T` of `Fₚ*/μ_n`,
`n · ∑_{t∈T} η_tʳ = q·N₀(μ_n,r) − nʳ` for **every** `r` (odd included). Under a primitive root
`|T| = (q−1)/n` (`transversal_card`); dividing by `n` gives the prose period moment law
`∑_i η_iʳ = (q/n)·N₀ − n^{r−1}` of #407. This is the coset-reindexing consumer step that
`SubgroupGaussSumRawMoment` / `PeriodMomentLaw` stated only in prose — the sum-power analogue of the
I031 sup capstone `eta_norm_sup'_eq_of_transversal`. -/
theorem card_mul_repSum_eq_rawMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) (rexp : ℕ) :
    (n : ℂ) * ∑ t ∈ T, eta ψ (nthRootsFinset n (1 : F)) t ^ rexp
      = (Fintype.card F : ℂ) * N0 (nthRootsFinset n (1 : F)) rexp
          - ((nthRootsFinset n (1 : F)).card : ℂ) ^ rexp := by
  rw [← rawMoment_erase_zero_eq_card_mul_repSum hζprim hn hT rexp]
  exact rawMoment_erase_zero hψ (nthRootsFinset n (1 : F)) rexp

end ArkLib.ProximityGap.Frontier.DistinctPeriodMomentLaw

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.DistinctPeriodMomentLaw.eta_const_on_fiber
#print axioms ArkLib.ProximityGap.Frontier.DistinctPeriodMomentLaw.sum_pow_on_fiber
#print axioms
  ArkLib.ProximityGap.Frontier.DistinctPeriodMomentLaw.rawMoment_erase_zero_eq_card_mul_repSum
#print axioms ArkLib.ProximityGap.Frontier.DistinctPeriodMomentLaw.card_mul_repSum_eq_rawMoment
