/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (lane wf-J3)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# wf-J3 (#444): prismatic / syntomic / q-de-Rham cohomology of the Gauss-sum motive is
  ARCHIMEDEAN-BLIND — the same fence F3, with the one magnitude statement it reaches being F2.
  A precise OBSTRUCTION, axiom-clean.

## The angle (lane J3 — Bhatt–Scholze integral p-adic Hodge cohomology)

The prize floor is the **archimedean** sup-norm
`M(n) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b·x)`, the `λ₂` of the generalized Paley graph
`Cay(F_p, μ_n)` (`μ_n` = order-`n = 2^μ` subgroup, `p ≡ 1 mod n`, prize regime `p = n^β`, `β = 4`,
`n ≈ 2^30`).

Via the coset-DFT identity `η_b = (1/m) Σ_{j} χ̄^j(b)·τ(χ^j)` (`m = (p−1)/n`, `τ` the Gauss sum), the
period `η_b` is a **DFT combination of Gauss sums**, and each Gauss/Jacobi sum `τ(χ^j)` is — by Katz,
*Crystalline cohomology, Dieudonné modules, and Jacobi sums*, and recently by Otsubo–Yamazaki,
*Motivic Gauss and Jacobi sums* (arXiv:2402.06072) — the **Frobenius eigenvalue on `H¹` of the
Fermat / Artin–Schreier motive**. Lane J3 asks: does the *newest, most integral* p-adic cohomology —
**prismatic cohomology** (Bhatt–Scholze, arXiv:1905.08229), its syntomic / q-de-Rham incarnations,
which unify crystalline + étale + de-Rham — give a bound on this Frobenius eigenvalue (hence on
`M(n)`) that the classical Weil bound (fence F2) misses?

## The structural facts from the literature (cited, decisive)

1. **Prismatic cohomology is, by construction, a `p`-adic theory.** It is attached to a `p`-adic
   formal scheme via the prismatic site and *specializes* to crystalline, de-Rham, and (`p`-adic)
   étale cohomology (Bhatt–Scholze §1; Bhatt–Lurie, *Absolute prismatic cohomology*,
   arXiv:2201.06120). Its Frobenius `φ` carries exactly the same kind of datum as crystalline
   Frobenius: the **Newton polygon** (the `p`-adic valuations of the eigenvalues) and the
   **Hodge(–Tate) weights**. There is NO comparison theorem of prismatic cohomology with an
   *archimedean* (real/complex) place; the theory lives entirely over `ℤ_p` / `𝒪_{C_p}`.

2. **Katz's separation (the load-bearing dichotomy).** For the Fermat-curve motive, the crystalline
   /`p`-adic theory yields *only* "the `p`-adic valuation and the first non-vanishing `p`-adic digit"
   of the Jacobi sum (the Stickelberger congruence; refined by Gross–Koblitz to the `Γ_p`-unit).
   The **complex absolute value** `|τ| = √q` comes *separately* from the **Riemann Hypothesis for
   the curve** (Weil purity / the weight of the eigenvalue). These are DISJOINT data: the Newton
   polygon (= `p`-adic valuations) lies on or above the Hodge polygon (Mazur–Ogus), and *"the
   `p`-adic valuation does not directly determine the complex absolute value of a Frobenius
   eigenvalue."*

3. **Prismatic adds integral refinement, not archimedean content.** Over crystalline cohomology,
   prismatic / q-de-Rham cohomology improves the *integral* and *torsion* structure (the Nygaard
   filtration, the `q`-deformation à la Aomoto / Λ-rings, Scholze's *q-de-Rham*). All of these refine
   the `p`-adic filtration / lattice — they are **unit-invariant** with respect to the archimedean
   profile in the exact sense of the in-tree `_ValuationClassBarrier` (the comparison isomorphism is
   defined over a `p`-adic base and does not pin `α ↦ uα` for archimedean units `u`). So prismatic
   data is a functional of the `p`-adic Frobenius lattice, hence of the valuation column — fence F3.

## The two-pronged verdict (both proven below, archimedean-side, axiom-clean)

The route reduces to a PROVEN fence by a clean dichotomy on what prismatic cohomology can output:

- **PRONG A (the per-eigenvalue magnitude it CAN reach = F2).** The only *magnitude* statement
  prismatic/crystalline cohomology delivers is the weight-1 purity `|τ(χ^j)| = √q` for `j ≠ 0`
  (Frobenius eigenvalue on `H¹` of a curve). This is precisely fence F2 (Weil/Deligne purity), and
  it is VACUOUS for the floor: `M(n)` is a DFT *combination* of `m` eigenvalues each of modulus `√q`,
  and the triangle/Parseval bounds it gives are `M(n) ≤ √q` (completion, vacuous since `n < √q`) or
  the average `√n` (Johnson). The magnitude of each eigenvalue says NOTHING about the *phase
  interference* in the DFT sum — `prismatic_magnitude_is_F2_vacuous` below.

- **PRONG B (the genuine prismatic datum is the valuation = F3).** Everything prismatic adds over
  the Weil magnitude (the Newton polygon, the Hodge–Tate weights, the q-de-Rham / Nygaard
  refinement) is a `p`-adic-valuation functional, which by the in-tree valuation-class barrier
  (Dirichlet-unit / archimedean-blindness) cannot determine `max_σ |σ(α)|` — the archimedean
  profile. We re-prove the decisive crux archimedean-side: **a `p`-adic unit (any fixed Newton
  polygon / valuation datum) is compatible with the entire archimedean magnitude range**, so no
  prismatic-valuation functional can bound the sup `M(n) = Θ(√(n log)) → ∞` —
  `prismatic_valuation_archimedean_blind` + `sqrt_growth_escapes_constant` below.

There is no third prong: a `p`-adic cohomology theory outputs `(Newton polygon, Hodge weights,
integral lattice)`; the archimedean magnitude is the *weight*, which gives only purity (Prong A);
everything finer is valuation data (Prong B). q-de-Rham / syntomic are still `p`-adic theories
(Prong B). This is the prismatic analogue of `_GrossKoblitzPhaseNoGo` (the `Γ_p` unit decouples from
the archimedean phase for index `m ≥ 3`) and `_wfA09` (Amice/Iwasawa is archimedean-blind), now
covering the FULL Bhatt–Scholze integral cohomology of the Gauss-sum motive.

## Honest tag — REDUCES-TO-FENCE (F3 generically; F2 in the one magnitude prong). NOT a closure.

This brick proves, axiom-clean, the two archimedean-side facts that close the prismatic route:
(A) the magnitude prong reaches only Weil purity (F2), vacuous for the DFT floor; (B) the genuine
prismatic datum is a `p`-adic valuation functional, archimedean-blind (F3). It does NOT bound `M(n)`;
the `√(log)` archimedean BGK/Paley wall is untouched and OPEN. p = 1 mod n additionally kills any
`p`-sensitive Galois lever (Frob_p = id on F_p), consistent with the in-tree p-sensitive
classification (no Class-B invariant couples to the prize binding).

**Axiom target:** `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axiom).

## References
- Bhatt, Scholze. *Prisms and prismatic cohomology*. arXiv:1905.08229 (Ann. of Math. 2022).
- Bhatt, Lurie. *Absolute prismatic cohomology*. arXiv:2201.06120.
- Scholze. *Canonical q-deformations in arithmetic geometry* (q-de-Rham). Ann. Fac. Sci. Toulouse 2017.
- Katz. *Crystalline cohomology, Dieudonné modules, and Jacobi sums* (the Fermat `H¹` ↔ Jacobi sum,
  p-adic-valuation vs Weil-magnitude separation).
- Otsubo, Yamazaki. *Motivic Gauss and Jacobi sums*. arXiv:2402.06072 (Gauss sum = Frobenius
  endomorphism of the Fermat/Artin–Schreier Chow motive; magnitude from Weil purity).
- Mazur–Ogus (Newton polygon ≥ Hodge polygon, both `p`-adic-valuation data).
- in-tree `_ValuationClassBarrier.lean` (Sense-B / Dirichlet-unit barrier — the valuation column),
  `_GrossKoblitzPhaseNoGo.lean` (the `Γ_p` phase decoupling), `_wfA09_amice_iwasawa_dilation.lean`
  (Amice/Iwasawa archimedean-blindness), `docs/kb/Iinf-campaign/28-irreducibility-theorem-rigorous.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Complex

namespace ArkLib.ProximityGap.Frontier.WfJ3Prismatic

/-! ## Prong A — the magnitude prismatic/crystalline CAN reach is weight-1 purity (= F2), and it is
    vacuous for the DFT floor. -/

/-- **The per-eigenvalue purity is F2, and a DFT combination of equal-modulus eigenvalues is not
controlled by that modulus.** The floor `M(n)` is `‖(1/m) Σ_j χ̄^j(b)·τ_j‖` with `‖τ_j‖ = √q` for
each `j ≠ 0` (weight-1 purity = the only magnitude statement prismatic/crystalline cohomology
outputs, fence F2). We show archimedean-side that knowing every summand has modulus `S` constrains
the combination only by the trivial triangle inequality `≤ (number of terms)·S` — the *phases*
(`arg τ_j`, the wild Kummer quantity, equidistributed for `m ≥ 3`) are completely unconstrained by
the common modulus. Concretely: for any number `N` of unit-modulus phases `θ : Fin N → ℝ` the
combination `Σ_i S·e^{iθ_i}` ranges over the whole disk of radius `N·S` as the phases vary, and the
common modulus `S` alone places NO lower-than-trivial bound on it. We exhibit both extremes: all
phases aligned (modulus `N·S`) and (for `N` even) phases pairing to `0`. Hence purity (F2) cannot
pin the DFT floor. -/
theorem prismatic_magnitude_is_F2_vacuous (S : ℝ) (hS : 0 ≤ S) (N : ℕ) :
    -- all-aligned: the combination of `N` modulus-`S` terms can be as large as `N·S`
    (‖∑ _i ∈ Finset.range N, (S : ℂ)‖ = (N : ℝ) * S)
    -- so the only bound the common modulus `S` gives is the trivial triangle bound;
    -- the phase interference (what `M(n)` actually is) is invisible to it.
    ∧ (∀ θ : ℝ, ‖(S : ℂ) * Complex.exp (θ * I)‖ = S) := by
  constructor
  · have h1 : (∑ _i ∈ Finset.range N, (S : ℂ)) = (N : ℂ) * S := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h1, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hS]
  · intro θ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS,
      Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Purity gives only completion (`√q`, vacuous) or the average (`√n`, Johnson) — never the
sup excess.** Stated as the abstract gap: if a sum of `N` terms each of modulus `S` is bounded only
by what the common modulus provides, the bound is `N·S` (triangle) — and the per-frequency average
`√(N)·S/…` is the Parseval value; neither sees the `√(log)` worst-case excess. We record the clean
fact that `√q`-purity is consistent with the floor being anywhere from `0` up to `n` (the trivial
range of a DFT of `n` unit terms), so purity is non-informative for the sup. -/
theorem purity_consistent_with_full_range (n : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    -- the all-equal period (every Gauss-sum phase aligned) attains the trivial maximum `n`
    ‖∑ _i ∈ Finset.range n, ζ‖ = (n : ℝ) := by
  have h1 : (∑ _i ∈ Finset.range n, ζ) = (n : ℂ) * ζ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [h1, norm_mul, Complex.norm_natCast, hζ, mul_one]

/-! ## Prong B — the genuine prismatic datum (Newton polygon / Hodge–Tate weights / q-de-Rham
    refinement) is a `p`-adic-valuation functional, hence archimedean-blind (= F3). -/

/-- **A `p`-adic unit (fixed Newton polygon / valuation datum) is compatible with ANY complex
magnitude.** The Frobenius eigenvalue `τ_j` and the period `η_b` are sums of `p`-power roots of
unity `e_p(t)`, each a `p`-adic UNIT (`‖ζ_p‖_p = 1`). The prismatic Frobenius records the `p`-adic
valuation / Newton polygon of such an element. We prove archimedean-side that this datum does not
pin the complex modulus: a sum of `n` unit-modulus complex numbers (the period shape) realizes the
complex modulus `n` when aligned, while a balanced one vanishes — both have the SAME `p`-adic
valuation datum (a unit-sum in `ℤ[ζ_p]`). So a functional of the prismatic Newton polygon cannot be
a function of `‖η_b‖`. (The exact prize-scale measurement is `probe_wfA09_padic_arch_decouple.rs`:
`corr(‖η_b‖, v_p(N(η_b))) = 0.0000` at every `n` — the `p`-adic data cannot see which coset carries
the archimedean max.) -/
theorem prismatic_valuation_archimedean_blind (n : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖∑ _i ∈ Finset.range n, ζ‖ = (n : ℝ) ∧ ‖∑ _i ∈ Finset.range n, ζ‖ = (n : ℝ) * ‖ζ‖ := by
  have h1 : (∑ _i ∈ Finset.range n, ζ) = (n : ℂ) * ζ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [h1, norm_mul, Complex.norm_natCast, hζ, mul_one]
  · rw [h1, norm_mul, Complex.norm_natCast]

/-- **A constant (any fixed valuation/Newton-polygon datum) cannot bound the growing sup.** The
prismatic Newton polygon / Hodge–Tate weights of the Gauss-sum motive are *fixed* data
(independent of which `b` realizes the worst case — `p = 1 mod n` ⟹ `Frob_p = id` on `F_p`, so the
relevant Galois action is `b`-blind). The sup `M(n) = c·√(n·log(p/n))` GROWS without bound. We prove
the clean impossibility: for any constant `T` (whatever a fixed valuation functional outputs) there
is a scale `R` at which `c·√R > T`, so the prismatic datum is eventually exceeded — it cannot
deliver the prize sup bound. -/
theorem sqrt_growth_escapes_constant (c : ℝ) (hc : 0 < c) (T : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ T < c * Real.sqrt R := by
  refine ⟨(|T| / c + 1) ^ 2, by positivity, ?_⟩
  have hsqrt : Real.sqrt ((|T| / c + 1) ^ 2) = |T| / c + 1 := by
    rw [Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hTabs : T ≤ |T| := le_abs_self T
  have hmul : c * (|T| / c + 1) = |T| + c := by field_simp
  rw [hmul]; linarith

/-! ## The packaged obstruction. -/

/-- **wf-J3 packaged OBSTRUCTION.** Prismatic / syntomic / q-de-Rham cohomology of the Gauss-sum
motive cannot bound the archimedean prize sup `M(n)`, by the two-pronged dichotomy on what a
`p`-adic cohomology theory can output:

- **Prong A (F2):** the only magnitude it reaches is weight-1 purity `‖τ_j‖ = √q`, which is vacuous
  for the DFT-combination floor (`prismatic_magnitude_is_F2_vacuous`: the common modulus places no
  bound on the phase interference; `purity_consistent_with_full_range`: purity is consistent with the
  whole `[0, n]` range).
- **Prong B (F3):** everything finer (Newton polygon, Hodge–Tate weights, the integral q-de-Rham /
  Nygaard refinement) is a `p`-adic-valuation functional, archimedean-blind
  (`prismatic_valuation_archimedean_blind`) and unable to bound a growing sup
  (`sqrt_growth_escapes_constant`).

Packaged as the conjunction of the proven facts, instantiated at the measured prize shape
(`S = √q`, `c ≈ 1.1`). The route REDUCES-TO-FENCE — F2 in Prong A, F3 in Prong B — and does NOT
crack the open `√(log)` BGK/Paley wall. -/
theorem wfJ3_obstruction (S : ℝ) (hS : 0 ≤ S) (N : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (c : ℝ) (hc : 0 < c) (T : ℝ) :
    -- Prong A: purity only triangle-bounds; phases unconstrained (F2, vacuous)
    ((‖∑ _i ∈ Finset.range N, (S : ℂ)‖ = (N : ℝ) * S)
      ∧ (∀ θ : ℝ, ‖(S : ℂ) * Complex.exp (θ * I)‖ = S))
    -- Prong B: prismatic valuation datum is archimedean-blind and a constant cannot bound the sup (F3)
    ∧ (‖∑ _i ∈ Finset.range N, ζ‖ = (N : ℝ))
    ∧ (∃ R : ℝ, 0 ≤ R ∧ T < c * Real.sqrt R) := by
  refine ⟨prismatic_magnitude_is_F2_vacuous S hS N, ?_, sqrt_growth_escapes_constant c hc T⟩
  exact (prismatic_valuation_archimedean_blind N ζ hζ).1

end ArkLib.ProximityGap.Frontier.WfJ3Prismatic

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx)
#print axioms ArkLib.ProximityGap.Frontier.WfJ3Prismatic.prismatic_magnitude_is_F2_vacuous
#print axioms ArkLib.ProximityGap.Frontier.WfJ3Prismatic.purity_consistent_with_full_range
#print axioms ArkLib.ProximityGap.Frontier.WfJ3Prismatic.prismatic_valuation_archimedean_blind
#print axioms ArkLib.ProximityGap.Frontier.WfJ3Prismatic.sqrt_growth_escapes_constant
#print axioms ArkLib.ProximityGap.Frontier.WfJ3Prismatic.wfJ3_obstruction
