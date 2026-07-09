# Mathlib upstream PR plan — #466 round 25, lane MLDRAFT (2026-07-07)

Executes the r24 UPSTREAM sequencing (DISPROOF_LOG `466-r24-dblock-d4-proven-supers2-fullrung-
gate-audit`; dossier v3 §38). PR-1 and PR-2 are now drafted **as ArkLib-side files ready to
copy verbatim into Mathlib**, with the ArkLib consumers refactored to import them (so the
in-tree code exercises exactly the statements being upstreamed). All builds axiom-clean
(`propext, Classical.choice, Quot.sound`).

**Ranking (r24 skeptic correction applied):** PR-1 → PR-2 → **PR-3 (re-ranked UP)** → PR-4.
The r24 skeptic verified that `quadraticChar_sum_mul` does **not** exist in pinned Mathlib
(nothing in `Mathlib/NumberTheory/LegendreSymbol/` evaluates the shifted product sum
`∑ₛ χ(s(s+c)))`; only `jacobiSum` machinery is adjacent). So the two-point orthogonality
evaluation is a genuine Mathlib gap and MORE upstreamable than originally ranked — it moves
ahead of the milestone PR-4.

---

## PR-1 — linearity of `divByMonic` (READY; drafted file in tree)

- **Draft file (copy source):** `ArkLib/ToMathlib/Polynomial/DivByMonicLinear.lean`
- **Mathlib targets:** `Mathlib/Algebra/Polynomial/Div.lean` (next to `add_modByMonic`) for
  `add_divByMonic` / `neg_divByMonic` / `sub_divByMonic`;
  `Mathlib/Algebra/Polynomial/RingDivision.lean` (next to `smul_modByMonic` /
  `modByMonicHom`) for `smul_divByMonic` / `divByMonicHom`.
- **Final statements** (namespace `Polynomial`; `{R : Type*} [CommRing R] {q : R[X]}` —
  full CommRing generality, **no `Monic` hypothesis**: the non-monic case is degenerate,
  `p /ₘ q = 0`):
  - `theorem add_divByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) /ₘ q = p₁ /ₘ q + p₂ /ₘ q`
  - `theorem neg_divByMonic (p : R[X]) : (-p) /ₘ q = -(p /ₘ q)`
  - `theorem sub_divByMonic (p₁ p₂ : R[X]) : (p₁ - p₂) /ₘ q = p₁ /ₘ q - p₂ /ₘ q`
  - `theorem smul_divByMonic (c : R) (p : R[X]) : (c • p) /ₘ q = c • (p /ₘ q)`
  - `noncomputable def divByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X]` (`@[simps]`)
- **Diff-of-dependencies:** none — proof uses only existing Mathlib
  (`div_modByMonic_unique`, `modByMonic_add_div`, `degree_modByMonic_lt`,
  `degree_add_le`/`degree_smul_le`, `divByMonic_eq_of_not_monic`, `zero_divByMonic`,
  `subsingleton_or_nontrivial`). Uniqueness argument, not degree induction.
- **ArkLib consumer refactored:** `Frontier/_R22StepanovS2.lean` now imports the draft file;
  its local field-case `add_divByMonic` / `smul_divByMonic` are thin wrappers (kept for
  call-site compatibility with the S2 chain and the r24 d-block generalization).
- **Expected friction:** none; naming matches the `add_modByMonic` family exactly.

## PR-2 — the Gauss-sum magnitude `‖g(χ,ψ)‖ = √q` (READY; drafted file in tree)

- **Draft file (copy source):** `ArkLib/ToMathlib/NumberTheory/GaussSumNorm.lean`
- **Mathlib target:** `Mathlib/NumberTheory/GaussSum.lean`, section `GaussSumProd`, right
  after `gaussSum_ne_zero_of_nontrivial`.
- **Final statements** (root namespace, matching `gaussSum_*` convention;
  `{F : Type*} [Field F] [Fintype F]`):
  - `theorem norm_gaussSum_sq_eq_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ)`
  - `theorem norm_gaussSum_eq_sqrt_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F)`
- **Diff-of-dependencies:** none — derives from Mathlib's own
  `gaussSum_mul_gaussSum_eq_card` + `star_gaussSum_eq` (+ `Complex.mul_conj'`,
  `Real.sqrt_sq`). Absent in pinned Mathlib in any form (r24 skeptic-confirmed; the
  quadratic special case `gaussSum_sq` exists but no magnitude statement).
- **Generality note:** ℂ-target only, because Mathlib's `star_gaussSum_eq` is stated for
  `MulChar R ℂ`. An `RCLike 𝕜` version needs `star_gaussSum_eq` generalized first (character
  values are roots of unity, so `star = ⁻¹` holds in any `RCLike`); NOT cheap enough to
  bundle — offer as follow-up in the PR description.
- **ArkLib consumers refactored:**
  `ConstantIndexGaussSumBound.lean` (`norm_gaussSum_eq_sqrt` now delegates — its 10+
  downstream frontier consumers unchanged) and `Frontier/_R19ChiDecomposition.lean`
  (`norm_gaussSum_chiFamily` consumes `norm_gaussSum_eq_sqrt_card` directly, feeding the
  proven `gaussSumSizeBound_holds`).
- **Expected friction:** reviewer may ask for `Complex.norm_gaussSum` naming or an
  `RCLike` generalization; both are cosmetic.

## PR-3 — two-point orthogonality (shifted quadratic-character product sum) — RE-RANKED UP

- **Status:** proven in-tree, not yet extracted to a ToMathlib draft file (next lane).
- **In-tree source:** `Frontier/_R19HasseAudit.lean`, `sum_quadraticChar_mul_shift`
  (root namespace, axiom-clean).
- **Final statement** (`{F : Type*} [Field F] [Fintype F] [DecidableEq F]`):
  - `theorem sum_quadraticChar_mul_shift (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∑ s : F, quadraticChar F (s * (s + c)) = -1`
- **Mathlib target:** `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean`
  (next to `quadraticChar_sum_zero`), suggested Mathlib name
  `quadraticChar_sum_mul_shift` or the reviewer's choice.
- **Diff-of-dependencies:** none — uses `quadraticChar_sq_one'`, `quadraticChar_sum_zero`,
  `Finset.sum_nbij'`; self-contained reindexing proof.
- **Skeptic correction driving the re-rank:** `quadraticChar_sum_mul` does NOT exist in
  pinned Mathlib (r24 audit); the nearest machinery is `jacobiSum` (general-χ two-point sums
  `∑ χ(x)·χ'(1−x)`), which does not specialize to the shifted-product evaluation without
  extra work. The general-χ version (`∑ₛ χ(s)·χ̄(s+c)` via `jacobiSum` + `gaussSum`) is a
  natural follow-up but should NOT gate the quadratic PR.

## PR-4 — the Stepanov milestone (unconditional Hasse-type bound) — LAST

- **In-tree source chain:** `_R21StepanovS1` → `_R22StepanovS2` → `_R22StepanovAssembly`
  (defines `LegendreCubicHasseC F K : Prop` = `∀ u v ≠ 0, u ≠ v,
  (∑ₛ quadraticChar F (s·(s−u)·(s−v)))² ≤ K·#F`) → `_R23EulerBridge` →
  `_R23ParameterChoice` / `_R23Milestone`.
- **Final statements:**
  - `theorem legendreCubicHasseC_unconditional (hF : ringChar F ≠ 2) :
    LegendreCubicHasseC F 625` (every odd finite field, gap-free, zero named hypotheses)
  - `theorem fourthMoment_quadChar_unconditional … : ∑ₛ ‖shiftedCharSum …‖⁴ ≤ 29·|G|²·q`
- **Mathlib target:** NEW file, suggested
  `Mathlib/NumberTheory/LegendreSymbol/StepanovBound.lean`; needs the whole S1/S2/Hasse-
  derivative chain inlined or split into 2–3 preparatory PRs (Hasse-derivative divisibility
  `f^{N−k} ∣ D^{(k)}(f^N·a)`, the `X^{qj}` Frobenius-binomial lemma, rank–nullity existence).
- **Diff-of-dependencies:** PR-1 (the S2 chain uses `divByMonic` linearity) and nothing
  else outside Mathlib; PR-2/PR-3 are independent of it.
- **Expected friction:** constant-tightening pushback (625 → the classical ~ 8√q shape /
  `K = 64`-ish after parameter optimization); reviewers will want `IsSquarefree`-phrased
  hypotheses and a general cubic rather than the `s(s−u)(s−v)` normal form. Estimate 2–4
  weeks of review; submit AFTER PR-1..3 establish the toolkit.

---

## Build/verification record (this round)

- `ArkLib.ToMathlib.Polynomial.DivByMonicLinear`, `ArkLib.ToMathlib.NumberTheory.GaussSumNorm`,
  `ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound`: real locked build
  (`scripts/lake-locked.sh build`).
- `Frontier/_R19ChiDecomposition.lean`, `Frontier/_R22StepanovS2.lean`: re-verified after
  refactor (`scripts/pg-iterate.sh`), axiom audit clean.

---

## PR-5 — the discrete arcsine moment / central-binomial cosine power sum (READY; drafted in tree, 2026-07-08)

- **Draft file (copy source):** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R25DiscreteArcsineMoment.lean`
  (namespace `ArkLib.…R25DiscreteArcsineMoment`; rename to `Mathlib` on copy). All axiom-clean
  (`propext, Classical.choice, Quot.sound`), real-build 2960 jobs.
- **Mathlib targets:** `Mathlib/Analysis/SpecialFunctions/Trigonometric/` or
  `Mathlib/RingTheory/RootsOfUnity/` (roots-of-unity power sums); the nat identity next to
  `Mathlib/Data/Nat/Factorial/DoubleFactorial.lean`.
- **Gap check:** Mathlib has `doubleFactorial_two_mul`, `centralBinom`, and geometric sums of
  roots of unity, but NOT the closed form of `∑_{k<N} (ζ^k + ζ^{-k})^{2r}` nor the identity
  `C(2r,r)·r! = 2^r·(2r-1)‼`. Both are genuine gaps.
- **Statements (upstreamable):**
  1. `sum_cos_pow_eq`: `IsPrimitiveRoot ζ N → 2r < N →`
     `∑_{k∈range N} (ζ^k + (ζ^k)⁻¹)^(2r) = N · (2r).choose r`.
     (The exact `2r`-th moment of the discrete cosine = central binomial; the discrete arcsine
     moment.)
  2. `centralBinom_mul_factorial_eq`: `(2r).choose r · r! = 2^r · (2r-1)‼` (pure ℕ; the exact
     ratio of central binomial to the odd-double-factorial×`2^r`).
  3. `centralBinom_le_wick`: `(2r).choose r ≤ 2^r · (2r-1)‼` (sub-Wick inequality).
  - Helper lemmas `geom_sum_root_eq_zero` (nontrivial root-of-unity geometric sum vanishes) and
    `inv_pow_eq` (`(ζ^k)⁻¹ = (ζ^{N-1})^k`) are also generally useful.
- **Provenance:** the arithmetic core of the #466 δ* moment-tower analysis — `E[(2cosθ)^{2r}]`
  over an `N`-grid equals `C(2r,r)`, which is `1/r!` of the Gaussian moment; the negative excess
  kurtosis (`κ₄ = -6` at `r=2`) is the structural reason the RS proximity-gap floor is true.
  Prize-independent, self-contained.

### PR-5 addendum (2026-07-08): module extended to 9 theorems
Added to the same draft file (all axiom-clean, real-build 2960 jobs):
- `sum_cos_pow_mul_shift_eq`: `IsPrimitiveRoot ζ N → s ≤ r → 2r+2s < N →`
  `∑_{k<N} (ζ^k+(ζ^k)⁻¹)^(2r)·(ζ^k)^(2s) = N·(2r).choose (r-s)` (shifted/autocorrelation moment).
- `norm_pow_le_sum_norm_pow`: `‖g b₀‖^n ≤ ∑_{b∈s} ‖g b‖^n` (moment→sup reduction).
- `sum_cos_sq_eq` (=2N), `sum_cos_pow_four_eq` (=6N), `centralBinom_le_wick` (sub-Wick inequality).
