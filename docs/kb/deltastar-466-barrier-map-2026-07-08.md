# δ* / Proximity Prize — the four-axis irreducibility barrier map (2026-07-08)

> **Purpose.** A precise, ground-truth-anchored map of *why* the prize's open core resists every
> tool tried — so the next agent (or model) starts from the closed routes instead of re-walking
> them. This is **not** a proof of the prize; the core stays the named open conjecture. It is an
> honest "why it's hard" artifact, verified from five tool-constructions and four theory-candidates
> against the Lean compiler and exact numerics.

## 0. The target and the reduction (settled, in-tree)

The prize funnels (machine-checked) to bounding the **worst-case incomplete Gauss period**
`M(μ_n) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`, for the explicit dyadic subgroup
`μ_n = μ_{2^μ} ⊂ F_p^×`, `n = 2^30`, at the Burgess barrier `p ≈ n^β`, uniformly to moment depth
`r ≈ ln q`. Target: `M ≤ C√(n·log(p/n))`, `C = O(1)` (conjecturally √2).

Named open predicate (both directions of the reduction are in-tree):
- `WorstCaseIncompleteSumBound` — `InteriorWorstCaseIncompleteSum.lean:59`.
- `ConstantIndexSubGaussianPeriodBound` + `worstCaseIncompleteSumBound_of_subGaussian` —
  `ConstantIndexSubGaussianPeriod.lean:97,105` (+ converse `centeredDeepMomentBound_of_subGaussian`).

`η_1` is a **Gauss period**: an algebraic integer of degree `m = (p-1)/n`, whose Galois conjugates
are exactly the `η_b` (one per multiplicative coset — this *is* the coset-invariance `η_{bt}=η_b`,
`t∈μ_n`). So `M(μ_n)` is the **house** (max conjugate modulus) of a cyclotomic period.

## 1. The four-axis barrier (the core statement)

The quantity `M(μ_n)` sits at the simultaneous intersection of four properties, and **every known
or constructible method is aligned to the wrong axis**:

| Axis of the target | Methods on that axis | Status |
|---|---|---|
| **Archimedean MAX** (a house / L∞) | heights, norms, Galois, Stickelberger, period polynomial | control **aggregate/average or p-adic**, never the max |
| **LINEAR** (correlation with `e_p(bx)`) | Fourier / `U²` / additive energy / moments | this is the *only* right-axis method — **provably capped at BGK** |
| needs **cohomological independence** of `m` Gauss sheaves | Deligne/Katz vertical Sato–Tate | **effective version proven vacuous** in-tree |
| **no Hecke multiplicativity** in the spectral variable `b` | automorphic subconvexity / amplification | amplifier is **blind → collapses to convexity `√p`** |

The single method on the correct (archimedean-linear) axis is the moment/energy method, and it is
proven to cap below the threshold (the campaign's Meta-Theorem / Tetrachotomy; the `U²` = 4th-moment
identity below). Escaping requires a method that is archimedean **and** max-sensitive **and** linear
**and** beats the moment cap — no such method exists.

## 2. Evidence: five tools built and killed (each against ground truth)

1. **`ℓ¹` operator norm of mult-by-`η`** → trivial `√p`. `‖c‖₂=√n` (Parseval) forces
   `‖c‖₁ ≤ √m·√n = √p`. Numerics: bound/house = 1.2→5.5× growing as `√m`.
2. **Gauss-sum DFT / effective Katz** → **vacuous** (`effectiveKatz_vacuous_in_thin_regime`,
   `_AssaultV2_EffectiveSatoTate.lean:135`). The reformulation `η_b=(1/m)Σ_ψ ψ̄(b)g(ψ)` is
   circular; the only non-circular leverage is effective equidistribution, proven vacuous here.
3. **House from period-polynomial coefficients** → coefficients too large (`~10¹²` at `m=27`); no
   root bound beats trivial. (Period poly confirmed integer to `4e-8`.)
4. **Non-negative structure constants** (`η² = Σ r(C_i)σ^i(η)+n`, `r(C_i)≥0`, `Σ=n−1`) → trivial
   `house ≤ n`.
5. **Autocorrelation flatness** → **= the 4th moment** (`house²−n` = sup of DFT of `(a−ā)`
   = `|η_b|²−n`, the additive-energy object), provably capped. Numerics: `house ≈ (Σ|η_b|⁴)^{1/4}`.

**General law (verified 5×):** every tool is `sup|DFT(v)|` for a sequence `v` with `ℓ²` pinned by
Parseval; beating the trivial/`√p` bound requires certifying **spectral flatness / `ℓ¹`-sparsity**
of `v`, which *is* the open conjecture. Two sinks (trivial / capped-moment); no third.

## 3. Evidence: four candidate "new theories" attacked and killed

- **Adelic / height transfer** (link p-adic Stickelberger to archimedean house via the product
  formula) → **aggregate-only**. `min|η_b| → 0` (measured 1.02, 0.11, 0.23, **0.010** as `m` grows;
  min/geomean → 0.004), so `Norm=∏|η_b|` is absorbed by tiny conjugates and cannot pin the max. The
  product formula controls the *average* log-magnitude, never the max.
- **Effective higher-order Fourier** (μ_n Gowers-uniform ⟹ small Fourier) → **category mismatch**.
  `max_b‖η_b‖` is correlation with *linear* phases = a `U²` object = additive energy = the capped
  4th moment (measured `house ≈ (Σ|η_b|⁴)^{1/4}`). Higher `U^k` address *nonlinear* phases —
  irrelevant to this linear quantity. The one genuinely-new framework does not apply.
- **Motivic / cohomological theory of incomplete sums** → **= effective Katz**. The completed sum is
  `(1/m)Σ_ψ g(ψ)`, `m` weight-1 Gauss sheaves; the needed cancellation is cohomological independence
  = effective vertical Sato–Tate = vacuous in-tree (anchor as tool #2).

- **Automorphic / subconvexity / amplification** (the axis I under-attacked at first; given a real
  fight) → **fourth sink: amplification without Hecke multiplicativity is blind = convexity.** The
  amplified certificate `max_k|v_k|² ≤ Σ_{k'}|v_{k'}|²|A(k')|² / |A(k)|²` over the quotient `ℤ/m`
  (multiplicative shifts = cyclic shifts on coset-values) reaches the house to **0.5%** — *if* the
  amplifier is allowed to peak at the true worst coset (a-posteriori, using the answer). But a
  **fixed a-priori** amplifier (blind to `k₀`): flat → exactly `√p` (measured 0.97–1.00× convexity);
  any fixed 1-mode → *worse* (1.47–12.6×, small `min_k|A(k)|²`). A provable amplifier must be large
  at the *unknown* worst coset, which requires an Euler product / Hecke eigenvalues in the spectral
  variable — and `η_b` has **no multiplicativity in `b`** (Gauss sums don't factor over the
  quotient). So subconvexity's engine is absent; the certificate collapses to convexity `√p`.

The four deaths are **complementary** — they close four different axes (archimedean-aggregate,
linear-capped, cohomological-vacuous, amplification-blind) — which is why the barrier is robust, not
an artifact of one failed method. The a-posteriori-reaches-house / a-priori-stalls-at-`√p` split is
the sharp diagnostic: the method has the *power* but not the *provable amplifier*, and the missing
amplifier is exactly the missing Hecke structure.

## 3b. The unifying identity: house = second eigenvalue (Perron / spectral-gap framing)

The multiplication-by-`η` operator is a **non-negative integer matrix** (structure constants are
additive-coincidence counts `≥0`). Its eigenvalues are the `η_b`. Perron–Frobenius gives the whole
picture in one shot: `λ₁ = n` **exactly** (all-ones eigenvector = the `b=0` direction we exclude),
and `house = λ₂` = the **second eigenvalue of the generalized Paley graph** `Cay(F_p,μ_n)`. Verified:
`λ₁ = n` to machine precision; `house/2√n` = 0.87, 1.15, 1.14, 1.34 (not Ramanujan; at the `√(n log)`
scale). Non-negativity buys `λ₁` for free and says *nothing* about `λ₂` — bounding the spectral gap of
a specific non-negative matrix below its Perron root, absent extra structure, is the
expander/Ramanujan problem, i.e. the conjecture. This is the single object every axis-1..4 method
reduces to: `λ₂(Cay(F_p,μ_n))` = house = Paley eigenvalue = `WorstCaseIncompleteSumBound`.

## 4. What a genuine solution would require

A method that is archimedean, max-sensitive, linear, and beats the moment cap — equivalently, a
*certification of spectral flatness* (sub-Gaussian tail `P(‖η_b‖>tn) ≤ e^{-ct²n}` to depth
`r≈ln q`) for the **explicit** subgroup, i.e. `ConstantIndexSubGaussianPeriodBound`. The distribution
is known correct (independent-Gaussian, FHK killed by experiment; C∈[1,1.4] over 400 primes, 0
exceed √2); the difficulty is *certification*, and it is the Paley/Burgess frontier — beyond BGK's
`n^{1-o(1)}` and beyond current mathematics. Not session-achievable; not literature-available.

## 5. Session contributions folded in (honest, axiom-clean)

- `_R25DiscreteArcsineMoment.lean` (9 theorems, real-build 2960 jobs): the discrete-arcsine-moment
  theory `∑_{k<N}(ζ^k+ζ^{-k})^{2r} = N·C(2r,r)`, the shifted/autocorrelation moment, the exact
  sub-Wick suppression `C(2r,r)·r! = 2^r·(2r-1)‼`, and the moment→sup engine. The formalized
  *model* side of axis-linear; Mathlib-upstreamable (PR-5).
- `_R25SubfamilyBoundedResidualNoGo.lean`: coarse-power subfamily bounded-residual route saves
  nothing (no-go).
- Refutations (countermodels): dyadic additive-energy anomaly (2-power subgroups marginally
  *worse*), Burgess amplification (coset-invariance `η_{bt}=η_b` kills it), log-free `√(2n)` ceiling.

**Verdict: CORE OPEN, ON-BGK. No fabricated closure.** The barrier is theorem-grade and mapped from
five tools + four theory-candidates + four axes. The missing ingredient is a new archimedean flatness
certification for explicit multiplicative subgroups — a famous open problem, honestly named, never
faked.
