# Mathlib upstream PR plan — #466 round 26, lane MLREDO (2026-07-08)

Redo of the failed r25 MLDRAFT lane (DISPROOF_LOG `466-r25-d8-proven-nonsquarefree-resolved-
suby-not-free` records the r25 lane as "placeholder, dead build — NOT PRODUCED; redo owed").
This round deliberately shrinks scope to guarantee landing: (i) verify the ONE ready draft
file (PR-1) against a **real locked build**, (ii) fix the r25 SUBY provenance debt
(`_R25SubfamilyGate.lean` now carries the full 5-declaration `#print axioms` block and
passes `pg-iterate` exit 0), and (iii) this plan doc. No Frontier consumer refactors this
round (race-wipe surface avoided).

This doc supersedes `mathlib-upstream-pr-plan-2026-07-07.md` where they differ; the 07-07
doc's PR-2 consumer-refactor claims should be treated as *working-tree state, not landed*
(those files are uncommitted on the shared tree as of 2026-07-08).

**Ranking (r24 skeptic correction applied):** PR-1 → PR-2 → **PR-3 (re-ranked UP)** → PR-4.
The skeptic correction: **`quadraticChar_sum_mul` does NOT exist in pinned Mathlib.**
Nothing under `Mathlib/NumberTheory/LegendreSymbol/` evaluates the shifted product sum
`∑ₛ χ(s(s+c))`; the nearest machinery is `jacobiSum` (two-point sums `∑ χ(x)·χ'(1−x)`),
which does not specialize without extra work. So the two-point orthogonality evaluation
(PR-3) is a genuine Mathlib gap and ranks ABOVE the milestone PR-4.

**Dependency order:** PR-1, PR-2, PR-3 are mutually independent (submit in parallel if
desired; ranked order is by review cheapness). PR-4 depends on PR-1 (the Stepanov S2 chain
consumes `divByMonic` linearity) and on the toolkit credibility established by PR-1..3;
PR-2/PR-3 are not build-dependencies of PR-4.

---

## PR-1 — linearity of `divByMonic` (READY; verified this round)

- **Draft file (copy source):** `ArkLib/ToMathlib/Polynomial/DivByMonicLinear.lean`
  (tracked in-tree; real locked build re-verified 2026-07-08, axiom-clean
  `[propext, Classical.choice, Quot.sound]`).
- **Mathlib targets:** `Mathlib/Algebra/Polynomial/Div.lean` (next to `add_modByMonic`)
  for `add_divByMonic` / `neg_divByMonic` / `sub_divByMonic`;
  `Mathlib/Algebra/Polynomial/RingDivision.lean` (next to `smul_modByMonic` /
  `modByMonicHom`) for `smul_divByMonic` / `divByMonicHom`.
- **Final statements** (namespace `Polynomial`; `{R : Type*} [CommRing R] {q : R[X]}` —
  full CommRing generality, **no `Monic` hypothesis**: the non-monic case is degenerate,
  `p /ₘ q = 0` by `divByMonic_eq_of_not_monic`):
  - `theorem add_divByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) /ₘ q = p₁ /ₘ q + p₂ /ₘ q`
  - `theorem neg_divByMonic (p : R[X]) : (-p) /ₘ q = -(p /ₘ q)`
  - `theorem sub_divByMonic (p₁ p₂ : R[X]) : (p₁ - p₂) /ₘ q = p₁ /ₘ q - p₂ /ₘ q`
  - `theorem smul_divByMonic (c : R) (p : R[X]) : (c • p) /ₘ q = c • (p /ₘ q)`
  - `noncomputable def divByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X]` (`@[simps]`)
- **Proof route:** the `div_modByMonic_unique` uniqueness argument (mirror of Mathlib's
  own `add_modByMonic` / `smul_modByMonic`), NOT degree induction; the subsingleton case
  split matches Mathlib house style. Dependencies are all existing Mathlib
  (`div_modByMonic_unique`, `modByMonic_add_div`, `degree_modByMonic_lt`,
  `degree_add_le` / `degree_smul_le`, `divByMonic_eq_of_not_monic`, `zero_divByMonic`,
  `subsingleton_or_nontrivial`).
- **Consumer note (deferred by design):** `Frontier/_R22StepanovS2.lean` has local
  field-case wrappers; the r25 doc refactored it to import this file, but that refactor is
  uncommitted working-tree state. Do NOT re-touch the Frontier consumers until the draft
  file itself is committed — the PR copy is self-contained either way.
- **Expected friction:** none; naming matches the `add_modByMonic` family exactly.

## PR-2 — Gauss-sum magnitude `‖g(χ,ψ)‖ = √q` (drafted; NOT re-verified this round)

- **Draft file (copy source):** `ArkLib/ToMathlib/NumberTheory/GaussSumNorm.lean`
  (**untracked working-tree file** as of 2026-07-08 — must be committed and given a real
  locked build before the PR copy is trusted; that is the next MLREDO increment).
- **Mathlib target:** `Mathlib/NumberTheory/GaussSum.lean`, section `GaussSumProd`, right
  after `gaussSum_ne_zero_of_nontrivial`.
- **Final statements** (root namespace; `{F : Type*} [Field F] [Fintype F]`):
  - `theorem norm_gaussSum_sq_eq_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ)`
  - `theorem norm_gaussSum_eq_sqrt_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F)`
- **Dependencies:** Mathlib's `gaussSum_mul_gaussSum_eq_card` + `star_gaussSum_eq`
  (+ `Complex.mul_conj'`, `Real.sqrt_sq`). Absent in pinned Mathlib in any form
  (r24 skeptic-confirmed; only the quadratic special case `gaussSum_sq` exists).
- **Generality note:** ℂ-target only (Mathlib's `star_gaussSum_eq` is ℂ-stated); the
  `RCLike 𝕜` version needs `star_gaussSum_eq` generalized first — offer as follow-up.

## PR-3 — two-point orthogonality (shifted quadratic-character product sum) — RE-RANKED UP

- **Status:** proven in-tree, axiom-clean; ToMathlib draft-file extraction still owed.
- **In-tree source:** `Frontier/_R19HasseAudit.lean`, `sum_quadraticChar_mul_shift`.
- **Final statement** (`{F : Type*} [Field F] [Fintype F] [DecidableEq F]`):
  - `theorem sum_quadraticChar_mul_shift (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∑ s : F, quadraticChar F (s * (s + c)) = -1`
- **Mathlib target:** `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean`
  (next to `quadraticChar_sum_zero`); suggested name `quadraticChar_sum_mul_shift`.
- **Dependencies:** `quadraticChar_sq_one'`, `quadraticChar_sum_zero`,
  `Finset.sum_nbij'`; self-contained reindexing proof.
- **Why re-ranked:** the r24 skeptic verified `quadraticChar_sum_mul` does not exist in
  pinned Mathlib (see ranking note above). The general-χ version via `jacobiSum` +
  `gaussSum` is a natural follow-up but must NOT gate the quadratic PR.

## PR-4 — the Stepanov milestone (unconditional Hasse-type bound) — LAST

- **In-tree source chain:** `_R21StepanovS1` → `_R22StepanovS2` → `_R22StepanovAssembly`
  (`LegendreCubicHasseC F K : Prop` = `∀ u v ≠ 0, u ≠ v,
  (∑ₛ quadraticChar F (s·(s−u)·(s−v)))² ≤ K·#F`) → `_R23EulerBridge` →
  `_R23ParameterChoice` / `_R23Milestone`.
- **Final statements:**
  - `theorem legendreCubicHasseC_unconditional (hF : ringChar F ≠ 2) :
    LegendreCubicHasseC F 625` (every odd finite field; gap-free, zero named hypotheses)
  - `theorem fourthMoment_quadChar_unconditional … : ∑ₛ ‖shiftedCharSum …‖⁴ ≤ 29·|G|²·q`
- **Mathlib target:** NEW file, suggested
  `Mathlib/NumberTheory/LegendreSymbol/StepanovBound.lean`; realistically split into 2–3
  preparatory PRs (Hasse-derivative divisibility `f^{N−k} ∣ D^{(k)}(f^N·a)`, the `X^{qj}`
  Frobenius-binomial lemma, rank–nullity existence).
- **Dependencies:** PR-1 (S2 chain uses `divByMonic` linearity); nothing else non-Mathlib.
- **Expected friction:** constant-tightening pushback (625 → classical ~8√q shape /
  `K ≈ 64` after parameter optimization); reviewers will want `IsSquarefree` hypotheses
  and general cubics rather than the `s(s−u)(s−v)` normal form. Submit AFTER PR-1..3.

---

## Verification record (this round, 2026-07-08)

- `ArkLib.ToMathlib.Polynomial.DivByMonicLinear`: real locked build
  (`scripts/lake-locked.sh build`), see r26 findings for the job count; axiom audit clean.
- `Frontier/_R25SubfamilyGate.lean`: the r25 SUBY provenance debt fixed — the
  `#print axioms` block now covers all **5** declarations (`chiFamily_pow_subset`,
  `chiDecompositionOff_pow`, `chiDecompositionOff_powSubfamily_iff_hyperplaneTransfer`,
  `wickForIncidenceAwayAt_two_of_hyperplaneTransfer`, `hyperplaneTransferOff_one`), each
  `[propext, Classical.choice, Quot.sound]`; `scripts/pg-iterate.sh` exits 0 (12s).
- NOT verified this round (owed next): `GaussSumNorm.lean` locked build + commit; the
  PR-3 ToMathlib extraction; any Frontier consumer refactors.
