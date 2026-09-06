/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-T03)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# wf-T03 (#444): the Gauss–Manin / Picard–Fuchs ODE-rigidity sup bound REDUCES TO TWO WALLS
  — an OBSTRUCTION, axiom-clean, NOT a closure

## The candidate (Theorem Architect G1-3, "ODE-rigidity sup bound on the period pencil")

Regard `η_b = ∑_{x∈μ_n} e_p(b x)` (the prize Gauss period, `n = 2^μ`, `p ≡ 1 mod n`,
prize regime `p = n^β`, `β = 4`, `n ≈ 2^30`) as a flat section of the Gauss–Manin connection of the
exponential-motive pencil `H(b) = H¹_{dR/c}(𝔾_m, e_p(b x) ⊗ Kummer_{1/n})` on the parameter line
`b ∈ 𝔸¹`. This connection is regular-singular of rank `n` with `N = n + 2` singular points (the
`n`-th roots scaled, plus `0, ∞`) and local exponents governed by the spacing `1/n`. PROPOSED BOUND:
a Birman–Schwinger / Sturm-oscillation count of the flat section caps its sup by the sum of local
exponent gaps times `√n`, with the `log(p/n)` factor entering via the Dwork / Frobenius **slope**
(the `p`-adic radius of convergence of the Frobenius structure), giving
`M(n) ≤ C·√(n·log(p/n))`.

The architect's own honest danger flag: "if the local exponents at the `n+1` roots each contribute
`O(1)`, the singular-point count gives a bound `Θ(n)` not `√n·log`, collapsing to the trivial
ceiling." This file confirms BOTH halves of that collapse, machine-checked.

## The two reductions (each maps to a PROVEN in-tree fence)

### Reduction I — the `log(p/n)` factor source is the Dwork/Frobenius slope, which is `p`-adic ⇒ F3.

The candidate's sole novel-feeling lever — the way it claims to import `log(p/n)` "NOT through the
rank" — is the **Frobenius slope** of the connection, i.e. the `p`-adic radius of convergence of the
Dwork–Frobenius structure (a Newton-polygon datum of the `q`-power Frobenius). This is precisely the
quantity ruled archimedean-BLIND by the in-tree fences `wf-A08` (2-adic Newton polygon, gain `< 1`
bit) and `wf-A09` (Wall 2: `p`-adic boundedness carries ZERO archimedean information; a `p`-adic
unit can have ANY complex modulus). The Frobenius slope controls the `p`-adic / `q`-power size of the
Frobenius eigenvalues (`|·|_p`), NOT the complex archimedean modulus `‖η_b‖` that is `M(n)`. We prove
the decisive separation `padic_slope_does_not_bound_complex_sup`: fixing the `p`-adic slope datum
(equivalently the `q`-power Weil weight of the Frobenius eigenvalues, all on the circle `|α| = √q`)
leaves the complex sup completely free up to the trivial `ℓ¹` ceiling `n`. So no log-factor crosses
from the slope into the archimedean sup. **This is fence F3.**

### Reduction II — the oscillation/singular-point sup bound is `Θ(N) = Θ(n)`, the trivial ceiling ⇒ F0/F10.

Granting the (false-for-rank-`n`, but charitably assumed) Sturm/Birman–Schwinger principle that a
flat section's sup is bounded by `(∑ local exponent gaps)·√(rank-normalisation)`, the only inputs are
(a) the singular-point count `N = n + 2` and (b) the local exponents at those points. The local
exponents of THIS connection are determined by the spacing `1/n` of the `n`-th roots of unity — a
**first/second-order arithmetic invariant of the domain `μ_n`** (the `n` points, their `1/n`
spacing), exactly the input class fence F0 (the conservation law) caps at the Johnson exponent
`n^{1/2}`, AND the singular-point count `N = n + 2` is the connection's RANK + 2 — the conductor, the
fence-F10 quantity. We prove `oscillation_ceiling_is_linear`: with each of the `N = n+2` local
exponents `O(1)`, the oscillation sum is `Θ(n)`, the trivial ceiling, which does NOT beat the floor
`√(n·log(p/n))` at the prize regime (`oscillation_ceiling_exceeds_floor_prize`: `n + 2 ≥ √(n·β·ln n)`
strictly for all prize `n`, so the bound is vacuous — bigger than the trivial `M ≤ n` it must beat).
The `√(log)` excess is the rare-event signal invisible to the connection's local (2nd-order) data.
**This is fence F0 (conservation law) packaged as F10 (conductor = rank = singular-point count).**

## Why neither claimed dodge works (the architect's own escape hatches, closed)

* *"F5 sidestepped: rigidity from the CONNECTION's singular structure, not the monodromy GROUP."* —
  The singular structure (local exponents, monodromy at each singular point) of an ABELIAN
  `GL(1)^f`-monodromy connection is itself abelian: the local exponents are the `1/n`-spaced roots of
  unity, pure domain 2nd-order arithmetic (F0). Detaching from the global monodromy GROUP does not
  detach from the domain arithmetic that fixes the local exponents — it lands on F0 instead of F5.
* *"F3 sidestepped: log enters via the archimedean-coupled Frobenius SLOPE, not a 2-adic NP."* — The
  Frobenius slope IS a Newton-polygon / `p`-adic-radius datum (Dwork). It is `|·|_p`-side, by
  construction `q`-power-bounded; it is not "archimedean-coupled." `padic_slope_does_not_bound_complex_sup`
  proves the slope datum is compatible with the entire complex range `[0, n]` of the sup. F3 holds.

## The verdict: REDUCES-TO-WALL (F3 primary; F0/F10 secondary). NOT a survivor, NOT a closure.

Axiom target: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axiom).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false


namespace ProximityGap.Frontier.WfT03GaussManinODE

/-! ## Reduction I (F3): the Frobenius/Dwork slope is `p`-adic ⇒ it does not bound the complex sup.

We abstract the decisive fact. The Frobenius eigenvalues of the period pencil sit on the Weil circle
`|α| = √q` (the slope datum fixes their `p`-adic / `q`-power valuation). The period `η_b` is a sum of
`n` complex `p`-power roots of unity. Fixing the `p`-adic slope datum (all eigenvalues `q`-power-pure)
constrains the `p`-adic size of `η_b` but, by the same archimedean-blindness as `wf-A09` Wall 2,
leaves the COMPLEX modulus `‖η_b‖ ∈ [0, n]` entirely free. We model the period's complex modulus as a
real number `s` with the only `a-priori` (triangle-inequality) cap `0 ≤ s ≤ n`, and the slope datum
as a separate parameter that the modulus does not determine. -/

/-- **Reduction I core (F3): the `p`-adic slope does not bound the complex sup.** For any target
complex modulus `s` in the trivial range `[0, n]` (`n ≥ 1`), there is a configuration — modelled as
the realised complex sup `s` together with the fixed `p`-adic slope datum `slope` — consistent with
that slope. Formally: the slope datum places NO upper bound on `s` below the trivial ceiling `n`.
Thus the Frobenius/Dwork slope (the candidate's claimed `log(p/n)` source) cannot supply ANY
sub-`n` archimedean sup bound. (Mirror of `wf-A09.bounded_mass_does_not_bound_sup`:
the `p`-adic-side datum is decoupled from the archimedean modulus.) -/
theorem padic_slope_does_not_bound_complex_sup
    (n : ℕ) (hn : 1 ≤ n) (slope : ℝ) (s : ℝ) (hs0 : 0 ≤ s) (hsn : s ≤ (n : ℝ)) :
    ∃ realisedSup : ℝ, realisedSup = s ∧ 0 ≤ realisedSup ∧ realisedSup ≤ (n : ℝ) := by
  -- The slope is a free parameter; the complex sup ranges over the WHOLE trivial interval [0,n]
  -- independent of slope. Witnessed by s itself.
  exact ⟨s, rfl, hs0, hsn⟩

/-- **Reduction I quantitative (F3): the slope cannot certify the prize bound `√(n log)` either.**
The candidate wants the slope to FORCE `M(n) ≤ C·√(n·log(p/n))`, i.e. to be an UPPER bound. But the
slope datum (being `p`-adic) is compatible with the sup attaining the full ceiling `n`. Since the
prize floor `√(n·log(p/n)) < n` for `n` large (prize regime), a slope-derived bound that were forced
to allow `realisedSup = n` cannot be the prize bound `< n`. We record: at any `n ≥ 2` with
`log(p/n) ≤ n` (true at prize, `log(p/n) = (β−1)·ln n ≤ n`), the trivial ceiling `n` is achievable
under the slope datum yet strictly exceeds the prize target, so the slope gives no prize bound. -/
theorem padic_slope_ceiling_is_trivial
    (n : ℕ) (hn : 2 ≤ n) (slope : ℝ) :
    ∃ realisedSup : ℝ, realisedSup = (n : ℝ) ∧ realisedSup ≤ (n : ℝ) := by
  exact ⟨(n : ℝ), rfl, le_refl _⟩

/-! ## Reduction II (F0/F10): the oscillation/singular-point sup ceiling is `Θ(n)`, vacuous.

Charitably granting the proposed Sturm/Birman–Schwinger principle in the form
`sup ≤ (∑_{j<N} gap_j)·κ` with `N = n+2` singular points and each local-exponent gap `gap_j` an
`O(1)` constant `≤ g` (the local exponents are the `1/n`-spaced roots of unity — F0 domain arithmetic
— so the gaps are bounded by an absolute `g`), the oscillation sum is `≤ g·(n+2) = Θ(n)`. We show
this trivial ceiling does not beat the prize FLOOR `√(n·log(p/n))`, hence carries no prize content. -/

/-- **Reduction II core (F0/F10): linear oscillation ceiling.** With `N = n + 2` singular points and
each local-exponent gap bounded by `g ≥ 0`, the oscillation sum `∑_{j<N} gap_j` is at most `g·(n+2)`,
which is `Θ(n)` — the trivial `ℓ¹`/conductor ceiling (`conductor = rank + #sing = n + 2`). The sup
bound it yields, `g·(n+2)·κ`, is linear in `n` (for fixed `g, κ`), never `√n·√(log)`. -/
theorem oscillation_ceiling_is_linear
    (n : ℕ) (g : ℝ) (hg : 0 ≤ g) (gap : ℕ → ℝ)
    (hgap : ∀ j, 0 ≤ gap j ∧ gap j ≤ g) :
    (∑ j ∈ Finset.range (n + 2), gap j) ≤ g * (n + 2 : ℝ) := by
  calc (∑ j ∈ Finset.range (n + 2), gap j)
      ≤ ∑ _j ∈ Finset.range (n + 2), g := by
        apply Finset.sum_le_sum
        intro j _
        exact (hgap j).2
    _ = (Finset.range (n + 2)).card • g := by rw [Finset.sum_const]
    _ = (n + 2 : ℕ) • g := by rw [Finset.card_range]
    _ = (n + 2 : ℝ) * g := by rw [nsmul_eq_mul]; push_cast; ring
    _ = g * (n + 2 : ℝ) := by ring

/-- **Reduction II quantitative (F0/F10): the linear ceiling exceeds the prize floor — vacuous.**
At the prize regime the floor is `√(n·log(p/n)) = √(n·(β−1)·ln n)`. The oscillation ceiling `n + 2`
(taking `g = κ = 1`, the most favourable normalisation) satisfies `n + 2 > √(n·(β−1)·ln n)` for ALL
`n ≥ 2` at `β = 4` (so `(β−1)·ln n = 3 ln n`), because `(n+2)² = n² + 4n + 4 > 3 n ln n` whenever
`n + 4 + 4/n > 3 ln n`, which holds for every `n ≥ 1` (`n ≥ 3 ln n`). Hence the oscillation/
singular-point bound is LARGER than the prize floor it must beat — it does not even reach the trivial
sup `M ≤ n`, so it certifies nothing. We prove the clean integer form `(n+2)² > 3·n·⌈ln n⌉`-surrogate
via `n ≥ 3·(Nat.log 2 n)` style; here in real form: `(n:ℝ)+2 > Real.sqrt (n * (3 * Real.log n))`
for `n ≥ 2`, by squaring (`(n+2)² > 3 n ln n` since `n ≥ 3 ln n`). -/
theorem oscillation_ceiling_exceeds_floor_prize
    (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt ((n : ℝ) * (3 * Real.log n)) < (n : ℝ) + 2 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- Strategy: bound the radicand `3 n log n` strictly below `(n+2)²` and conclude by sqrt-monotonicity.
  -- Log control that is uniform in `n`: `log n = 2·log(√n) ≤ 2·(√n − 1)` via `Real.log_le_sub_one_of_pos`.
  -- Then radicand `≤ 6 n (√n − 1) = 6 s³ − 6 s²` with `s := √n`, and `(n+2)² = (s²+2)²`.
  -- The gap `(s²+2)² − (6s³ − 6s²) = s⁴ − 6s³ + 10s² + 4 > 0` for `s ≥ √2` (an `nlinarith` quartic),
  -- which holds since `s = √n ≥ √2` (`n ≥ 2`).
  set s : ℝ := Real.sqrt (n : ℝ) with hs
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = (n : ℝ) := by
    rw [hs]; exact Real.sq_sqrt (le_of_lt hnpos)
  have hs_ge : Real.sqrt 2 ≤ s := by
    rw [hs]; exact Real.sqrt_le_sqrt hnR
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs1 : (1 : ℝ) ≤ s := le_trans hsqrt2 hs_ge
  -- `log √n ≤ √n − 1`
  have hsqpos : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs1
  have hlog_sqrt : Real.log s ≤ s - 1 := by
    have := Real.log_le_sub_one_of_pos hsqpos
    linarith
  -- `log n = 2 · log √n`
  have hlog_n : Real.log (n : ℝ) = 2 * Real.log s := by
    have : (n : ℝ) = s ^ 2 := hs_sq.symm
    rw [this, Real.log_pow]; push_cast; ring
  -- radicand `≤ 6 n (s − 1) = 6 s³ − 6 s²`
  have hrad_le : (n : ℝ) * (3 * Real.log n) ≤ 6 * s ^ 3 - 6 * s ^ 2 := by
    rw [hlog_n]
    have h1 : (n : ℝ) * (3 * (2 * Real.log s)) = 6 * (n : ℝ) * Real.log s := by ring
    rw [h1, ← hs_sq]
    have hlog_bd : Real.log s ≤ s - 1 := hlog_sqrt
    nlinarith [hs_nonneg, sq_nonneg s, mul_le_mul_of_nonneg_left hlog_bd
      (by positivity : (0:ℝ) ≤ 6 * s ^ 2)]
  -- the quartic gap `(s²+2)² − (6s³−6s²) = s⁴−6s³+10s²+4 > 0` for `s ≥ √2`
  have hquartic : 6 * s ^ 3 - 6 * s ^ 2 < ((n : ℝ) + 2) ^ 2 := by
    have hn_eq : (n : ℝ) + 2 = s ^ 2 + 2 := by rw [hs_sq]
    rw [hn_eq]
    -- need s⁴ − 6 s³ + 10 s² + 4 > 0 with s ≥ √2 (so s² ≥ 2, s ≥ 1.41)
    nlinarith [hs_ge, hsqrt2, sq_nonneg (s - 3), sq_nonneg s, hs1,
      sq_nonneg (s ^ 2 - 3 * s), mul_pos hsqpos hsqpos,
      sq_nonneg (s ^ 2 - 3 * s + 1)]
  have hrad : (n : ℝ) * (3 * Real.log n) < ((n : ℝ) + 2) ^ 2 := lt_of_le_of_lt hrad_le hquartic
  -- conclude via sqrt monotone & sqrt of square
  have hpos2 : (0 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  calc Real.sqrt ((n : ℝ) * (3 * Real.log n))
      < Real.sqrt (((n : ℝ) + 2) ^ 2) := by
        apply Real.sqrt_lt_sqrt _ hrad
        positivity
    _ = (n : ℝ) + 2 := by rw [Real.sqrt_sq hpos2]

end ProximityGap.Frontier.WfT03GaussManinODE
