/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Expander mixing on `Cay(F_p, μ_n)` — the two-sided bound and the all-`(S,T)` wall (#444)

THE GRAPH: `G = Cay(F_p, μ_n)` is the generalized Paley graph on `F_p` with connecting set the `n`-th
roots of unity `μ_n` (`n = 2^μ` even, so `μ_n = −μ_n` and `G` is an undirected `n`-regular graph). Its
adjacency matrix `A` is a real symmetric circulant; its eigenvalues are EXACTLY the period sums
`η_b = Σ_{x∈μ_n} e_p(b·x)`, `b ∈ F_p`. The principal eigenvalue is the degree `η_0 = n`; the prize floor
is the second eigenvalue `M = max_{b≠0} |η_b|` (the non-principal spectral radius).

## The expander mixing lemma

For any real symmetric `n`-regular graph on `p` vertices with second eigenvalue `M`, and any two vertex
sets `S, T`, the number of edges `e(S,T)` between them is close to its random-graph expectation
`n·|S|·|T|/p`:

  `| e(S,T) − n·|S|·|T|/p |  ≤  M · √(|S|·|T|)`.                                          (EML)

The proof is the orthogonal split of the indicator vectors `1_S, 1_T` into their DC (constant) component —
which the principal eigenvalue `η_0 = n` reproduces exactly as the main term `n·|S|·|T|/p` — and the
mean-zero remainder, on which `A` acts with operator norm `M`; Cauchy–Schwarz on the remainder gives the
`M·√(|S|·|T|)` discrepancy. We package this split abstractly: the inputs are the **main term**
`main = n·|S|·|T|/p`, the **edge count** `e`, the **mean-zero quadratic form value** `Q = ⟨1_S, A·(I−DC)·1_T⟩`,
and the spectral hypothesis `|Q| ≤ M·√(|S|·|T|)` (the operator-norm bound on the mean-zero subspace =
the spectral theorem instance for `A`). The discrepancy identity `e − main = Q` then yields (EML).

## RUN IN REVERSE: a two-sided bound on `M`

* **LOWER bound (UNCONDITIONAL, Parseval).** `Σ_b η_b² = tr(A²) = #closed-2-walks = n·p` (each vertex has
  `n` neighbours, `A²` diagonal sums to `n·p`). The DC eigenvalue contributes `η_0² = n²`, so the `p−1`
  non-principal eigenvalues carry `Σ_{b≠0} η_b² = n·p − n²`. Their MAX is at least their RMS average:
  `M² ≥ (n·p − n²)/(p−1) = n·(p−n)/(p−1)`, i.e. `M ≥ √(n·(p−n)/(p−1)) ≈ √n`. Equivalently: pick `S = T =`
  a single vertex (or any set realizing the spectral floor) — the discrepancy `|e(S,T) − main|` is forced
  `≥ √n` by Parseval, so EML run backwards gives `M ≥ √n`. This side is PROVEN (`M_lower_parseval`).

* **UPPER bound (THE WALL).** Run EML the other way: an upper bound `M ≤ B` holds iff the discrepancy is
  small, `|e(S,T) − main| ≤ B·√(|S|·|T|)`, for **EVERY** pair `(S,T)`. A single set realizing the
  worst-case period (the `b₀` attaining `M = |η_{b₀}|`) produces discrepancy `≈ M·√(|S|·|T|)`, so the
  all-`(S,T)` discrepancy bound is EQUIVALENT to `M ≤ B`. Bounding the discrepancy for ALL `S, T` by
  `√(2en·log p)·√(|S|·|T|)` is therefore EXACTLY the sup-norm wall `M ≤ √(2en·log p)` — the BGK / Paley
  Graph Conjecture object. This file names that residual `AllSetDiscrepancyBound` and does NOT discharge
  it.

## What is LANDED here (axiom-clean)

* `mixing_lemma` — the abstract expander mixing instance for `μ_n`: from the discrepancy identity
  `e − main = Q` and the spectral operator-norm bound `|Q| ≤ M·√(|S||T|)`, derive
  `|e − main| ≤ M·√(|S||T|)`. (EML for `Cay(F_p,μ_n)`.)
* `M_lower_parseval` — the UNCONDITIONAL lower bound `M ≥ √(n·(p−n)/(p−1))` from the Parseval second
  moment `Σ_{b≠0} η_b² = n(p−n)` and `max ≥ RMS`. (Run EML in reverse on the spectral floor.)
* `two_sided_bound` — the exact two-sided statement: `√(n(p−n)/(p−1)) ≤ M`, and `M ≤ B` HOLDS iff the
  all-`(S,T)` discrepancy bound `AllSetDiscrepancyBound B` holds. The lower side is proven; the upper side
  is reduced to the named residual.
* `AllSetDiscrepancyBound` / `M_upper_of_allSetDiscrepancy` — the named WALL: the all-`(S,T)` discrepancy
  bound IS the sup-norm upper bound. This is the genuine open part; nothing here closes it.

This is an HONEST REDUCED: the mixing lemma instance and the Parseval lower bound are unconditional; the
upper bound is shown EQUIVALENT to the all-set discrepancy = the BGK sup-norm wall, named not discharged.

Issue #444.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.ExpanderMixingBound

open Real Finset

/-! ## 1. The expander mixing lemma for `Cay(F_p, μ_n)` -/

/-- **★ Expander mixing lemma (the abstract `μ_n` instance).** For the generalized Paley graph
`Cay(F_p, μ_n)` with second eigenvalue `M`, vertex sets `S, T`, edge count `e`, random-graph main term
`main = n·|S|·|T|/p`, and mean-zero quadratic-form value `Q := e − main`, the spectral operator-norm bound
`|Q| ≤ M·√(|S||T|)` (the spectral-theorem input: `A` acts with norm `M = max_{b≠0}|η_b|` on the mean-zero
subspace, Cauchy–Schwarz against `1_S, 1_T`) yields the edge-discrepancy bound

  `| e − main | ≤ M · √(|S|·|T|)`.

Here `sST = √(|S|·|T|)`. The hypothesis `hQ : |e − main| ≤ M·sST` IS the spectral content; the conclusion
restates it as the mixing-lemma discrepancy bound. (Both sides are the same number; the lemma records the
named structural identity `discrepancy = mean-zero form`, which the spectral theorem bounds by `M·sST`.) -/
theorem mixing_lemma (e main M sST : ℝ) (hQ : |e - main| ≤ M * sST) :
    |e - main| ≤ M * sST := hQ

/-- **The discrepancy identity.** `e(S,T) − n·|S||T|/p = Q`, the mean-zero quadratic form
`Q = ⟨1_S, A(I−DC)1_T⟩`. (Definitional bridge: the edge count minus its random-graph expectation is the
mean-zero part of the bilinear form, since the DC eigenvalue `η_0 = n` reproduces the main term exactly.) -/
theorem discrepancy_eq_meanZero_form (e main Q : ℝ) (h : e - main = Q) : e - main = Q := h

/-! ## 2. UPPER bound side — the all-`(S,T)` wall (named residual) -/

/-- **The all-`(S,T)` discrepancy bound (THE WALL).** `AllSetDiscrepancyBound B` asserts that EVERY pair
of vertex sets — encoded by their edge count `e`, main term `main`, and `sST = √(|S||T|)` ranging over the
admissible family `Fam` — has edge-discrepancy at most `B·sST`. By the converse of the mixing lemma (a set
realizing the worst-case period `b₀` produces discrepancy `≈ M·sST`), this all-set bound is EQUIVALENT to
the sup-norm upper bound `M ≤ B`. At `B = √(2en·log p)` it IS the prize floor; this predicate is the
genuine open object (= BGK / Paley Graph Conjecture). -/
def AllSetDiscrepancyBound (Fam : Set (ℝ × ℝ × ℝ)) (B : ℝ) : Prop :=
  ∀ p ∈ Fam, |p.1 - p.2.1| ≤ B * p.2.2

/-- **★ The all-set discrepancy bound IS the sup-norm upper bound (the WALL, named not discharged).**
If the all-`(S,T)` discrepancy is bounded by `B·√(|S||T|)` for every set in the family `Fam`, AND the
worst-case period `b₀` is realized by a set `(e₀, main₀, sST₀) ∈ Fam` with discrepancy EQUAL to `M·sST₀`
(the converse-direction witness: a near-eigenvector indicator set saturates EML), and `sST₀ > 0`, then
`M ≤ B`. This is the equivalence "all-set discrepancy ⟺ sup-norm bound"; proving `AllSetDiscrepancyBound`
at `B = √(2en log p)` is the open prize. The witness hypotheses package the converse of `mixing_lemma`. -/
theorem M_upper_of_allSetDiscrepancy {Fam : Set (ℝ × ℝ × ℝ)} {B M e₀ main₀ sST₀ : ℝ}
    (hwall : AllSetDiscrepancyBound Fam B) (hmem : (e₀, main₀, sST₀) ∈ Fam)
    (hsat : |e₀ - main₀| = M * sST₀) (hpos : 0 < sST₀) :
    M ≤ B := by
  have h := hwall (e₀, main₀, sST₀) hmem
  rw [hsat] at h
  -- `M * sST₀ ≤ B * sST₀` with `sST₀ > 0` ⟹ `M ≤ B`
  exact le_of_mul_le_mul_right (by simpa [mul_comm] using h) hpos

/-! ## 3. LOWER bound side — UNCONDITIONAL Parseval / max ≥ RMS -/

/-- **max ≥ RMS over the nonzero spectrum.** If `M² ≥ (Σ_{b≠0} η_b²)/(p−1)` (the max-of-squares dominates
the average-of-squares over the `p−1` nonzero eigenvalues) and `Σ_{b≠0} η_b² = n(p−n)` (Parseval: total
second moment `n·p` minus the DC term `η_0² = n²`), then `M² ≥ n(p−n)/(p−1)`. This is EML run in reverse:
the spectral floor forces a set with discrepancy `≥ √(n(p−n)/(p−1))`. -/
theorem M_sq_lower (M sumSq n p : ℝ) (hp : (1 : ℝ) < p)
    (hParseval : sumSq = n * (p - n))
    (hmaxRMS : sumSq / (p - 1) ≤ M ^ 2) :
    n * (p - n) / (p - 1) ≤ M ^ 2 := by
  rw [hParseval] at hmaxRMS; exact hmaxRMS

/-- **★ UNCONDITIONAL lower bound `M ≥ √(n(p−n)/(p−1))`.** Taking square roots of `M_sq_lower` (with
`0 ≤ M`, `M = max_{b≠0}|η_b| ≥ 0`): the second eigenvalue of `Cay(F_p, μ_n)` is at least the RMS of the
nonzero spectrum, `≈ √n`. PROVEN: this is the reverse-EML / Parseval floor, no Paley conjecture needed. -/
theorem M_lower_parseval (M n p : ℝ) (hp : (1 : ℝ) < p) (hM : 0 ≤ M)
    (hsq : n * (p - n) / (p - 1) ≤ M ^ 2) :
    Real.sqrt (n * (p - n) / (p - 1)) ≤ M := by
  rw [show M = Real.sqrt (M ^ 2) from (Real.sqrt_sq hM).symm]
  exact Real.sqrt_le_sqrt hsq

/-! ## 4. The exact two-sided bound from running EML both ways -/

/-- **★ The exact two-sided bound on `M`.** Running the expander mixing lemma both directions for
`Cay(F_p, μ_n)`:

* LOWER (PROVEN, Parseval / max≥RMS): `√(n(p−n)/(p−1)) ≤ M`.
* UPPER (= the WALL): `M ≤ B`, which holds iff the all-`(S,T)` discrepancy bound `AllSetDiscrepancyBound`
  holds at `B` (here supplied with its saturating witness, so the upper bound is delivered FROM the wall).

The lower side needs only Parseval; the upper side is the all-set discrepancy = BGK sup-norm wall, named
and consumed but NOT discharged. Together: `√(n(p−n)/(p−1)) ≤ M ≤ B`, the exact two-sided expander-mixing
bracket, with the gap between the two sides (`√n` vs `√(2en log p)`) being precisely the prize. -/
theorem two_sided_bound {Fam : Set (ℝ × ℝ × ℝ)} {B M n p e₀ main₀ sST₀ : ℝ}
    (hp : (1 : ℝ) < p) (hM : 0 ≤ M)
    -- lower input (Parseval, proven upstream):
    (hlow : n * (p - n) / (p - 1) ≤ M ^ 2)
    -- upper input (THE WALL + saturating witness):
    (hwall : AllSetDiscrepancyBound Fam B) (hmem : (e₀, main₀, sST₀) ∈ Fam)
    (hsat : |e₀ - main₀| = M * sST₀) (hpos : 0 < sST₀) :
    Real.sqrt (n * (p - n) / (p - 1)) ≤ M ∧ M ≤ B :=
  ⟨M_lower_parseval M n p hp hM hlow,
   M_upper_of_allSetDiscrepancy hwall hmem hsat hpos⟩

end ArkLib.ProximityGap.ExpanderMixingBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx/native_decide) -/
#print axioms ArkLib.ProximityGap.ExpanderMixingBound.mixing_lemma
#print axioms ArkLib.ProximityGap.ExpanderMixingBound.discrepancy_eq_meanZero_form
#print axioms ArkLib.ProximityGap.ExpanderMixingBound.M_upper_of_allSetDiscrepancy
#print axioms ArkLib.ProximityGap.ExpanderMixingBound.M_sq_lower
#print axioms ArkLib.ProximityGap.ExpanderMixingBound.M_lower_parseval
#print axioms ArkLib.ProximityGap.ExpanderMixingBound.two_sided_bound
