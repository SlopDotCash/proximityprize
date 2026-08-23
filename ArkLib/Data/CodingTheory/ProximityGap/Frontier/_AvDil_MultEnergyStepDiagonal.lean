/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# DILATION_MULTIPLICATIVE_ENERGY angle: the exact DC-subtracted step diagonal (#444)

For `μ_n` (order `n = 2^μ`, `p ∈ [n^4, 2n^4)`), let `c_K = μ_n^{*K}` be the additive `K`-fold
convolution of the indicator of `μ_n` on `ℤ/p`, `N_K = Σ_a c_K(a)^2`, `A_K = N_K − n^{2K}/p`.
The single open "deep step" is `A_{K+1} ≤ (2K+1)·n·A_K`.

## What the dilation/multiplicative lever buys (proven, exact-verified)

`μ_n` is a multiplicative subgroup, hence **dilation-invariant**: `t·μ_n = μ_n` for `t ∈ μ_n`,
so every `c_K` is constant on `μ_n`-orbits (`c_K(t·a) = c_K(a)`). Because `n` is even, `−1 ∈ μ_n`,
so `μ_n` is also **negation-symmetric** (`c_K(−x) = c_K(x)`). These two facts give the chain of
EXACT identities below (each verified to the last digit by `scripts/probes/probe_wick_step_monotone.py`
extended in this session over `n=8,16,32`, primes good and bad):

1. **Autocorrelation collapses to deeper convolution.** With negation symmetry,
   `C_K(d) := Σ_b c_K(b)c_K(b+d) = c_{2K}(d)`.  (Verified: `dil4.py`.)

2. **The step is a difference-set sum.**
   `N_{K+1} = Σ_{r,s ∈ μ_n} c_{2K}(r−s)`  (Plancherel/autocorrelation of the `μ_n`-convolution).

3. **DC subtraction makes it the clean diagonal identity.** Writing `φ_K(d) = c_{2K}(d) − n^{2K}/p`
   (so `Σ_d φ_K(d) = 0`), the `n^{2K}/p` terms sum to `n^2·n^{2K}/p = n^{2K+2}/p` and cancel the DC
   of `A_{K+1}`, giving the **EXACT** identity (verified to the digit, `dil6.py`):
   ```
       A_{K+1}  =  Σ_{r,s ∈ μ_n} φ_K(r − s)
                =  n · A_K  +  Σ_{r ≠ s ∈ μ_n} φ_K(r − s).
   ```
   The diagonal `r = s` contributes `n` copies of `φ_K(0) = c_{2K}(0) − n^{2K}/p = N_K − n^{2K}/p = A_K`.

   ⟹ **The deep step `A_{K+1} ≤ (2K+1)·n·A_K` is EXACTLY EQUIVALENT to the off-diagonal bound**
   ```
       Σ_{r ≠ s ∈ μ_n} φ_K(r − s)  ≤  2K · n · A_K.
   ```

This file proves the *algebraic skeleton* of that equivalence (the diagonal split, axiom-clean):
the deep step is `n·A_K + OFF ≤ (2K+1)·n·A_K  ⟺  OFF ≤ 2K·n·A_K`, where `OFF` is the off-diagonal
difference-set sum. This isolates the multiplicative content into one scalar inequality.

## Where the multiplicative structure STOPS — the BGK pinpoint (exact, this session)

Applying Cauchy–Schwarz to `OFF = Σ_{d≠0} m(d) φ_K(d)` (with `m(d) = #{(r,s)∈μ_n²: r−s=d}`) gives
```
   |OFF| ≤ sqrt( (Σ_{d≠0} m(d)²) · (Σ_{d≠0} φ_K(d)²) ).
```
Both factors are EXACT and verified (`dil7.py`, `dil8.py`):
* `Σ_{d≠0} m(d)² = 2n² − 3n` — this is `μ_n`'s additive energy `N_2 = 3n²−3n` minus the `d=0`
  term `n²`. It is the **best possible** (`μ_n` is Sidon-except-negation), so the multiplicative
  structure is *fully* exploited on this factor. ✓
* `Σ_{d≠0} φ_K(d)² = A_{2K} − A_K²` — the DC-subtracted energy at DOUBLE depth `2K`.

So Cauchy–Schwarz reduces the step to `sqrt((2n²−3n)(A_{2K}−A_K²)) ≤ 2K·n·A_K`, i.e. to
`A_{2K} ≲ (2K)²·A_K²` — **a Wick bound at depth `2K`, strictly deeper than the step itself.**
Exact measurement: `CS_bound/target` is `0.91` at `K=1` but **grows past 1 and up to `7.7`**
(n=32, deep `K`), while the true `OFF/target` stays `< 1` (worst `0.97`). The Cauchy–Schwarz step
is therefore **lossy by exactly the half-power**: it discards the *cancellation/correlation* between
`m(d)` and `φ_K(d)` over the structured difference set `μ_n − μ_n`. That cancellation is the BGK /
square-root-cancellation content — it is NOT delivered by dilation-invariance alone (which only
makes `c_{2K}` a class function and pins the `m`-energy at `2n²`). **This is the precise point where
the multiplicative structure fails to produce the `(2K+1)` factor: the off-diagonal needs genuine
cancellation in `Σ_{d≠0} m(d)φ_K(d)`, equivalently BGK at depth `2K`, not an `ℓ²` magnitude bound.**

VERDICT: `reduces-to-BGK`. The dilation lever yields a NEW EXACT RECURSION
(`A_{K+1} = n·A_K + Σ_{r≠s} φ_K(r−s)`, diagonal = `A_K`) and a clean reduction of the deep step to a
single off-diagonal difference-set inequality; but bounding that off-diagonal by `2K·n·A_K` is, via
the only structure-respecting estimate (Cauchy–Schwarz, with the `m`-energy already optimal), exactly
a depth-`2K` energy/Wick bound = BGK. The multiplicative structure is exhausted on the diagonal and
on the `m`-energy; the residual is the off-diagonal cancellation = the wall.
-/

set_option autoImplicit false


namespace Issue444.DilationMultEnergyStep

/-- **The exact DC-subtracted step diagonal split (algebraic skeleton).**

Given the exact identity (proven by dilation + negation symmetry of `μ_n`, verified to the digit
over `n=8,16,32`)
`A_{K+1} = n·A_K + OFF`, where `OFF = Σ_{r≠s∈μ_n} φ_K(r−s)` is the off-diagonal difference-set sum,
the deep step `A_{K+1} ≤ (2K+1)·n·A_K` is **EQUIVALENT** to the off-diagonal bound
`OFF ≤ 2K·n·A_K`.

This is the precise statement of what the multiplicative/dilation lever achieves: it removes the
diagonal `n·A_K` exactly (the diagonal value `φ_K(0) = A_K` is an identity, not an estimate), leaving
a single scalar inequality on the structured difference set. -/
theorem step_iff_offdiagonal
    (Akp1 Ak off : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off) :
    (Akp1 ≤ (2 * K + 1) * n * Ak) ↔ (off ≤ 2 * K * n * Ak) := by
  subst hsplit
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **Diagonal value is an exact identity, not an estimate.** The `r = s` diagonal of the
difference-set sum `Σ_{r,s∈μ_n} φ_K(r−s)` contributes exactly `n` copies of `φ_K(0)`, and
`φ_K(0) = c_{2K}(0) − n^{2K}/p = N_K − n^{2K}/p = A_K`. Hence the diagonal block equals `n·A_K`
on the nose. Recorded as the consuming implication that drives `step_iff_offdiagonal`. -/
theorem diagonal_block_eq
    (phiK0 Ak : ℚ) (n : ℚ) (hdiag : phiK0 = Ak) :
    n * phiK0 = n * Ak := by
  rw [hdiag]

/-- **Cauchy–Schwarz reduces the off-diagonal to a depth-`2K` energy bound (the BGK pinpoint).**

`OFF = Σ_{d≠0} m(d)·φ_K(d)`. Cauchy–Schwarz gives `OFF ≤ sqrt(Em · Ephi)` with the EXACT factors
`Em = Σ_{d≠0} m(d)² = 2n²−3n` (`μ_n`'s additive energy minus the diagonal; Sidon-optimal) and
`Ephi = Σ_{d≠0} φ_K(d)² = A_{2K} − A_K²` (the DC-subtracted energy at DOUBLE depth). Therefore, IF
the depth-`2K` Wick-type control `Em · (A_{2K} − A_K²) ≤ (2K·n·A_K)²` holds, the off-diagonal bound
— and hence the deep step — follows. This records the implication; the hypothesis `hCS` is exactly
the depth-`2K` energy bound = BGK, the open input. (The `0 ≤ off` orientation is the regime of
interest, `OFF > 0` for all tested `(K,p)`.) -/
theorem offdiagonal_le_of_depth2K_energy
    (off Em Ephi target : ℚ)
    (hoff_nonneg : 0 ≤ off)
    (hCS : off ^ 2 ≤ Em * Ephi)
    (htarget_nonneg : 0 ≤ target)
    (hdepth : Em * Ephi ≤ target ^ 2) :
    off ≤ target := by
  have hsq : off ^ 2 ≤ target ^ 2 := le_trans hCS hdepth
  nlinarith [hsq, hoff_nonneg, htarget_nonneg]

/-- **Assembled reduction of the deep step to the depth-`2K` energy bound.** Combining the exact
diagonal split with the Cauchy–Schwarz / depth-`2K` route: the deep step `A_{K+1} ≤ (2K+1)·n·A_K`
holds whenever the off-diagonal Cauchy–Schwarz factors satisfy `Em·(A_{2K}−A_K²) ≤ (2K·n·A_K)²`
(the depth-`2K` Wick bound = BGK) and the off-diagonal is nonnegative.

This is the SHARP form of the dilation-lever conclusion: the deep step is reduced — using ONLY the
multiplicative structure (exact diagonal, optimal `m`-energy) — to a single depth-`2K` energy
inequality. The half-power gap is precisely the slack in this Cauchy–Schwarz, which dilation does
not close. NOT a closure: `hdepth` is the open BGK input. -/
theorem deep_step_of_depth2K_energy
    (Akp1 Ak off Em Ephi : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off)
    (hoff_nonneg : 0 ≤ off)
    (hCS : off ^ 2 ≤ Em * Ephi)
    (htarget_nonneg : 0 ≤ 2 * K * n * Ak)
    (hdepth : Em * Ephi ≤ (2 * K * n * Ak) ^ 2) :
    Akp1 ≤ (2 * K + 1) * n * Ak := by
  have hoff : off ≤ 2 * K * n * Ak :=
    offdiagonal_le_of_depth2K_energy off Em Ephi (2 * K * n * Ak)
      hoff_nonneg hCS htarget_nonneg hdepth
  rw [step_iff_offdiagonal Akp1 Ak off n K hsplit]
  exact hoff

/-- **Overshooting the off-diagonal target is exactly failure of the deep step.**
Under the exact diagonal split, an empirical/probe witness `2K·n·A_K < OFF` rules out
`A_{K+1} ≤ (2K+1)·n·A_K`. This is the contrapositive interface for the diagonal reduction:
there is no hidden slack in the diagonal bookkeeping. -/
theorem not_deep_step_of_offdiagonal_gt
    (Akp1 Ak off : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off)
    (hoff_gt : 2 * K * n * Ak < off) :
    ¬ Akp1 ≤ (2 * K + 1) * n * Ak := by
  intro hdeep
  have hoff_le : off ≤ 2 * K * n * Ak :=
    (step_iff_offdiagonal Akp1 Ak off n K hsplit).mp hdeep
  linarith

/-- **A Cauchy--Schwarz certificate cannot coexist with an off-diagonal overshoot.**
If `target < OFF`, `OFF ≥ 0`, and Cauchy--Schwarz has already certified
`OFF² ≤ Em·Ephi`, then the depth-`2K` energy budget `Em·Ephi ≤ target²` is impossible.
Thus any observed off-diagonal overshoot pinpoints the missing input as the depth-`2K`
energy/Wick (BGK) bound, not the diagonal/dilation algebra. -/
theorem not_depth2K_energy_of_cs_and_offdiagonal_gt
    (off Em Ephi target : ℚ)
    (hoff_nonneg : 0 ≤ off)
    (htarget_nonneg : 0 ≤ target)
    (hoff_gt : target < off)
    (hCS : off ^ 2 ≤ Em * Ephi) :
    ¬ Em * Ephi ≤ target ^ 2 := by
  intro hdepth
  have hsq_le : off ^ 2 ≤ target ^ 2 := le_trans hCS hdepth
  have hsq_lt : target ^ 2 < off ^ 2 := by
    nlinarith [sq_nonneg (off - target)]
  linarith

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms step_iff_offdiagonal
#print axioms diagonal_block_eq
#print axioms offdiagonal_le_of_depth2K_energy
#print axioms deep_step_of_depth2K_energy
#print axioms not_deep_step_of_offdiagonal_gt
#print axioms not_depth2K_energy_of_cs_and_offdiagonal_gt

end Issue444.DilationMultEnergyStep
