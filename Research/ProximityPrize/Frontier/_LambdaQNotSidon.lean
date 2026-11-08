/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# μ_n is not a combinatorial B₂ set — scalar bookkeeping for the antipodal `q = 4` defect (#444)

## Corrections (audit R-310) — read first

* **Two different "Sidon" notions.** In this file "Sidon" / "non-Sidon" means the COMBINATORIAL
  `B₂` property (every additive two-sum coincidence `x₁+x₂ = y₁+y₂` is trivial). Pisier
  (arXiv:1704.02969) defines Sidon *analytically*, by an inequality quantified over ALL scalar
  coefficient vectors (and its moment formulation likewise quantifies all coefficients). An excess
  of zero-sum antipodal pairs is a failure of `B₂`; it does NOT by itself disprove the analytic
  inequality or force its optimal constant to diverge. At fixed `n`, the pointwise triangle bound
  already gives, for every `q ≥ 2` and uniformly in the prime, `‖η‖_q ≤ n ≤ √(n/2)·√q·√n`, so a
  positive polynomial `B₂` defect cannot establish divergence. A growing-`n` family would need the
  corresponding quantitative argument. The actual all-coefficient obstruction is identified
  separately via modulation (rootT97), independently of the invalid `B₂ ⇒` analytic inference made
  by an earlier version of this header.
* **Exact punctured normalization.** If `E_2 = 3n² − 3n`, then the punctured moment is
  `μ_4 = (p·(3n² − 3n) − n⁴)/(p − 1)`, which differs from `E_2` by `(E_2 − n⁴)/(p − 1)`. It is NOT
  exactly `3n² − 3n` and NOT exactly `3n` below `Wick_2 = 3n²`. The reason `E_2` lies below `3n²` is
  its own `−3n` correction; DC subtraction does not "over-compensate an `n²` antipodal defect"
  (changing reference from the `B₂` floor `2n² − n` to Wick `3n²` is just a change of baseline).
  For `p > n³` the DC term `n⁴/(p − 1)` is of order less than `n`, not order `n²`.
* **`actualE2` is a char-0 polynomial, not the finite-field energy.** Actual `F_p` energy need not
  equal `3n² − 3n`: the known cell `n = 64`, `p = 17318209` (`p > n⁴`) has `E_2 = 13632`
  (vs `3n² − 3n = 12096`), and its punctured fourth moment exceeds `Wick_2 = 12288`. So the claimed
  universal "benign at `q = 4`" / "onset strictly above `q = 4`" conclusion is FALSE even in a
  genuinely thin cell. The theorems below are valid only for the DEFINED polynomial `actualE2`
  (i.e. conditional on the entered energy formula).

## The object

`η : Z_p → C`, `η(b) = Σ_{x∈μ_n} e_p(b·x)`, `μ_n` the `n`-th roots of unity, `n = 2^μ`.
The prize floor `M = max_{b≠0}|η(b)| ≤ C·√(n·log m)` is implied by the all-ones moment inequality
`‖η‖_{L^q(Z_p)} ≤ C·√q·√n` at `q ≈ 2 log m` (`m = (p−1)/n`); this all-ones inequality is not the
all-coefficient `Λ(q)` constant.

## The exact `B₂` defect of the char-0 energy formula (scalar identity, formalized here)

The `q = 4` Λ-level is the **second energy moment**
`E_2 := E_2(μ_n) = #{ x₁+x₂ = y₁+y₂ : xᵢ,yⱼ ∈ μ_n } = Σ_b |η(b)|⁴ / p`.

* **`B₂` floor** (the only solutions are the trivial `{x₁,x₂}={y₁,y₂}`): `E_2^{B₂} = 2n² − n`
  (`n` diagonal `x₁=x₂` + `2(n choose 2)·… = n²−n` swapped, giving `2n²−n` ordered).
* **Char-0 value** (exact in `ℤ[ζ_n]`; probe-checked `n = 4,8,16,32`): `E_2(μ_n) = 3n² − 3n`. Over
  `F_p` this holds only when no extra wrap-around collisions occur; it fails, e.g., at
  `n = 64`, `p = 17318209`.
* **The `B₂` defect** `Δ := E_2 − E_2^{B₂} = (3n²−3n) − (2n²−n) = n² − 2n`.
  This excess is **entirely the `σ = 0` antipodal collisions**: `μ_n` is closed under `x ↦ −x`
  (`n = 2^μ` even), so `x + (−x) = 0 = y + (−y)` has `n·n = n²` ordered solutions, of which `2n`
  are already trivial (`{x,−x}={y,−y}`), leaving the `n²−2n` *non-trivial* antipodal sumset
  coincidences. So `μ_n` is **Sidon-except-negation** (memory: `issue444-downstream-listdecode-pivot`).

`exact_nonSidon_defect` lands `E_2 − E_2^{B₂} = n² − 2n` as an exact algebraic identity of the
defined polynomials, and `nonSidon_defect_pos` shows it is strictly positive for `n > 2` — so, given
the entered energy formula, `μ_n` is **not a combinatorial `B₂` set**. This says nothing by itself
about Pisier's analytic Sidon constant (see the corrections above).

## The `q = 4` scalar comparison (conditional on the entered energy formula)

For the punctured moment `μ_{2k} := (p·E_k − n^{2k})/(p−1)` (the uncentered `b≠0` average —
`_LambdaQMeanZeroEnergy`) and `Wick_k := (2k−1)‼·n^k`: IF `E_2 = 3n² − 3n` exactly, then

  `μ_4 − Wick_2 = (p·E_2 − n⁴)/(p−1) − 3n² = (3n² − 3n·p − n⁴)/(p−1) < 0`  for `p > n³`.

`mu4_lt_Wick2_of_deep` lands this strict inequality axiom-clean for the defined polynomial
`actualE2`. The gap below Wick is `(3np + n⁴ − 3n²)/(p − 1)`, approximately `3n` for `p > n³` (not
exactly `3n`); it comes from `E_2`'s own `−3n` correction, with the DC term `n⁴/(p−1)` contributing
less than order `n`.

**Onset.** This comparison does NOT locate an onset `q` for actual `μ_n ⊂ F_p`: actual `E_2` may
exceed `3n² − 3n` through wrap-around collisions, and in the known cell `n = 64`, `p = 17318209` the
actual punctured fourth moment is ABOVE `Wick_2`. `onset_above_q4` is therefore only the
conjunction of the two scalar facts for the defined polynomial, not a theorem that the actual
`q = 4` level is benign. No onset variable, actual energy, analytic Sidon constant, or higher-moment
law is formalized here. (The per-summand DC scale `n^{2k}/p` crosses `1` at
`k₀ = ⌈log p / (2 log n)⌉`, `= 3` at prize parameters `n = 2³⁰`, `p ≈ 2¹⁵⁸`; the prize saddle is
`q ≈ 2 log m ≈ 177`. These are parameter calculations, not onset theorems.)

## Honesty

`exact_nonSidon_defect`, `nonSidon_defect_pos`, `mu4_lt_Wick2_of_deep`, `onset_above_q4` are
**axiom-clean scalar facts about the defined polynomials** `actualE2 = 3n²−3n` and
`sidonFloorE2 = 2n²−n` and an entered `μ_4` equation. The polynomial `3n²−3n` is the char-0 energy;
its identification with the actual finite-field energy is NOT proved and is false in some thin
cells (`n = 64`, `p = 17318209`). This file does **NOT** close the prize; the genuine open part is
the deep-`k` `μ_{2k} ≤ Wick_k` near the saddle (= the BGK resonance, `_OpenCoreMonotoneReduction`).

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.LambdaQNotSidon

open Real

/-- **The `B₂` floor for the `q=4` energy level.** For a combinatorial `B₂` set (no nontrivial additive
coincidences) the count `E_2 = #{x₁+x₂ = y₁+y₂}` is exactly the trivial solutions: the `n` diagonal
terms (`x₁=x₂=y₁=y₂` … here `x₁=y₁,x₂=y₂` and `x₁=y₂,x₂=y₁`), giving `2n² − n` ordered solutions. -/
def sidonFloorE2 (n : ℝ) : ℝ := 2 * n ^ 2 - n

/-- **The char-0 `q=4` energy polynomial of `μ_n`** (probe-checked `n=4,8,16,32`:
`36,168,720,2976`): `E_2(μ_n) = 3n² − 3n` in `ℤ[ζ_n]`. Despite the name, this is NOT the actual
finite-field energy in general (e.g. `n = 64`, `p = 17318209` has `E_2 = 13632 ≠ 12096`). -/
def actualE2 (n : ℝ) : ℝ := 3 * n ^ 2 - 3 * n

/-- **The Gaussian/Wick reference at `k=2` (`q=4`):** `Wick_2 = (2·2−1)‼·n² = 3·n²`. -/
def wick2 (n : ℝ) : ℝ := 3 * n ^ 2

/-- **★ The exact `B₂` defect (of the defined polynomials).**
`E_2(μ_n) − E_2^{B₂} = (3n²−3n) − (2n²−n) = n² − 2n`. The `n² − 2n` excess is the non-trivial `σ = 0`
antipodal sumset coincidences (`μ_n` closed under `x ↦ −x`): in char 0, `μ_n` is
**`B₂`-except-negation**. -/
theorem exact_nonSidon_defect (n : ℝ) :
    actualE2 n - sidonFloorE2 n = n ^ 2 - 2 * n := by
  unfold actualE2 sidonFloorE2; ring

/-- **`μ_n` is not a combinatorial `B₂` set (given the entered energy formula).** The defect
`n² − 2n` is strictly positive for `n > 2`, so `actualE2` strictly exceeds the `B₂` floor. This is
the combinatorial `B₂` property only; it does NOT imply divergence of Pisier's analytic Sidon
constant (arXiv:1704.02969), which quantifies over all coefficient vectors — at fixed `n` the
triangle bound gives `‖η‖_q ≤ √(n/2)·√q·√n` for all `q ≥ 2` (audit R-310). -/
theorem nonSidon_defect_pos {n : ℝ} (hn : 2 < n) :
    sidonFloorE2 n < actualE2 n := by
  have h : 0 < n ^ 2 - 2 * n := by nlinarith
  have := exact_nonSidon_defect n
  linarith

/-- **Scalar `q = 4` comparison for the defined polynomial.** IF `E_2 = actualE2 n = 3n²−3n`, the
punctured (uncentered `b≠0`) moment `μ_4 := (p·E_2 − n⁴)/(p−1)` sits **strictly below**
`Wick_2 = 3n²`:

  `μ_4 − Wick_2 = (3n² − 3n·p − n⁴)/(p−1) < 0`   whenever `p > n³`.

The gap comes from `E_2`'s own `−3n` correction, not from DC subtraction over-compensating an `n²`
defect. This does NOT show the actual `F_p` second moment is benign: actual `E_2` can exceed
`3n² − 3n` (e.g. `n = 64`, `p = 17318209`, where the actual `μ_4 > Wick_2`). (`μ4` is the
`_LambdaQMeanZeroEnergy` punctured object.) -/
theorem mu4_lt_Wick2_of_deep {n p μ4 : ℝ} (hn : 0 < n) (hp : 1 < p) (hpn : n ^ 3 < p)
    (hμ4 : μ4 = (p * actualE2 n - n ^ 4) / (p - 1)) :
    μ4 < wick2 n := by
  have hpne : (0 : ℝ) < p - 1 := by linarith
  rw [hμ4, div_lt_iff₀ hpne]
  unfold actualE2 wick2
  -- p*(3n²−3n) − n⁴  <  3n²·(p−1)   ⟺   3n²−3np−n⁴ < 0
  nlinarith [hpn, hn, hp, sq_nonneg n, sq_nonneg (n - 1), mul_pos hn hn]

/-- **Conjunction of the two scalar facts for the defined polynomial.** For `actualE2 = 3n²−3n`:
the `B₂` defect is positive, and the punctured `μ_4` built from it stays below `Wick_2`. Despite the
name, this is NOT a theorem that the actual onset lies above `q = 4`: no onset variable or actual
finite-field energy appears, and the conclusion fails for actual `μ_n ⊂ F_p` in the known thin cell
`n = 64`, `p = 17318209` (actual `E_2 = 13632`, actual `μ_4 > Wick_2`) (audit R-310). -/
theorem onset_above_q4 {n p μ4 : ℝ} (hn : 2 < n) (hp : 1 < p) (hpn : n ^ 3 < p)
    (hμ4 : μ4 = (p * actualE2 n - n ^ 4) / (p - 1)) :
    sidonFloorE2 n < actualE2 n ∧ μ4 < wick2 n :=
  ⟨nonSidon_defect_pos hn, mu4_lt_Wick2_of_deep (by linarith) hp hpn hμ4⟩

end ArkLib.ProximityGap.LambdaQNotSidon

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx/native_decide) -/
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.exact_nonSidon_defect
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.nonSidon_defect_pos
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.mu4_lt_Wick2_of_deep
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.onset_above_q4
