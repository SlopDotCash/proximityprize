# δ* / #466 — SYZ17: the #138 X-degree budget, proven in the form the recursion supports

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ17XDegreeBudget.lean`
Status: LANDED, axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`.

## The object

SYZ16 pinned the sole remaining Claim 5.8 residual (`GammaGenuineTailPolynomial`, non-degenerate
regime) as "the #138 X-degree budget in disguise": the missing `degreeX P₀/P₁` bounds on the
T-loaded representative — the corrected analogue of the old `hdegX : degreeX Ppoly ≤ 1` companion
that `GenuinePpolyConverter` explicitly does not produce. SYZ17 attacks that budget from the
Hensel recursion's per-step degree growth.

## The degree-accounting argument (FOUND — and its exact reach)

For monic `H` every `αGenuine t` has the **unique** integral preimage
`βHensel t · (ξ⁻¹)^(2t−1)` (integrality: `P1MonicIntegrality`; uniqueness:
`embeddingOf𝒪Into𝕃_injective`). Both factors are Λ-weight-controlled:

* the `(A.1)` numerator obeys the graded per-step growth bound already telescoped in-tree
  (`GenuineTruncationFin.weight_βHensel_le_graded`):
  `Λ(βHensel t) ≤ (n_R(D−d+1) + D + (D−d+1))·(2t−1) + (D−d+1)` — LINEAR in `t`;
* the recursion's per-step division by `W·ξ²` (monic: `W = 1` disappears; the `ξ`-division does
  NOT) contributes `(2t−1)` factors of `ξ⁻¹`, each one fixed weight `W_ξ ≥ Λ(ξ⁻¹)` by
  submultiplicativity (`WeightLambdaCalculus`).

So the recursion **does** telescope — to the explicit `t`-graded budget

    alphaGradedBudget nR D d t Wξ :=
      ((nR·(D−d+1) + D + (D−d+1))·(2t−1) + (D−d+1)) + (2t−1)·Wξ

and NOT to any absolute bound. Both halves of that dichotomy are machine-checked (below).

## What was proven (namespace `BCIKS20.CellPencilJohnson.SYZ17`, all axiom-clean)

1. **`alpha_preimage_eq_βHensel_mul_pow`** — the forced shape: any `a` with
   `embed a = αGenuine t` equals `βHensel t · b^(2t−1)` for any ξ-inverse `b` (monic lift
   identity + injectivity).

2. **`alpha_preimage_weight_le_graded`** — the telescoped budget: under the paper grading
   (`hR : degreeX (R.coeff j) ≤ D − j` + the usual graded side conditions) and a ξ-inverse
   weight supply `hbw : Λ(b) ≤ W_ξ` (with `b·ξ = 1`),
   `Λ(a) ≤ alphaGradedBudget (natDegreeY R) D d_H t W_ξ` for every integral preimage `a` of
   `αGenuine t`.

3. **`alpha_canonicalRep_coeff_natDegree_le_graded`** — the weight → X-degree extraction:
   every `Y`-coefficient of the canonical representative of that preimage has
   `X`-degree `≤ alphaGradedBudget … t W_ξ`.

4. **`exists_budgeted_corrected_representative`** — **the #138 `degreeX P₀/P₁` bounds
   (T-dependent form, PROVEN).** Monic `d_H ≤ 2`: from the truncation identity at `k`, the
   graded data, and the ξ-inverse weight supply, a corrected representative exists with
   coefficient support in `[0, k)` AND
   `degreeX P₀, degreeX P₁ ≤ alphaGradedBudget (natDegreeY R) D d_H (k−1) W_ξ`.
   (Construction: the converter run on the canonical-representative coefficients of the forced
   preimages, so the budget of (3) transfers to `P₀, P₁` verbatim.)

5. **`branch_field_budgeted_of_graded_disc_tail`** — wiring into SYZ16: at a monic quadratic
   curve, finite geometric data + the SYZ16 tail residual `GammaGenuineTailPolynomial` + the
   ξ-inverse weight supply yield BOTH the F6 ground-field emptiness AND a **fully explicit**
   T-loaded representative (support `[0,k)` + the `degreeX` budget). The truncation identity is
   derived internally via `SYZ16.gammaGenuine_eq_trunc_of_graded_disc_tail`.

6. **`weight_one_budget_wall`** — the wall, re-exported (kernel-checked in
   `XDegreeBudgetProbe.graded_rescue_dead`): the `P1MonicWeightRefutation` witness satisfies
   EVERY graded hypothesis consumed by (2) at the pinned `D = 2`, yet the paper's absolute
   budget `deg_X c₀ ≤ 1 ∧ (D+1−d_H) + deg_X c₁ ≤ 1` FAILS at `t = 1`.

## The honest wall (twofold, both machine-checked)

* **The absolute (weight-1) #138 budget is unreachable by degree bookkeeping.** The brief's
  hoped-for "pure induction to the budget" is refuted in-tree: the graded rescue is dead
  (`graded_rescue_dead`), so the linear-in-`t` budget of (2) is optimal-in-kind for every
  recursion-accounting route. The gap to the paper's weight-1 invariant is genuinely
  GS-geometric (agreement structure of the `Z`-direction), not degree accounting.
* **The ξ-inverse weight supply** `Λ(ξ⁻¹) ≤ W_ξ` is the single fixed constant the calculus does
  not produce (the recursion divides by `ξ` even in the monic case; `W`-division disappears at
  `W = 1`). It is one element, not `t`-dependent; mathematically `W_ξ` is finite and
  norm/conjugate-computable at `d_H = 2`, but the norm calculus is not in-tree. Named residual
  shape: *XiInverseWeightSupply*.
* Unchanged: `GammaGenuineTailPolynomial` (SYZ16's residual) is NOT produced here — the budget
  consumes the truncation, it does not create it.

## Net effect / scoreboard (BCIKS20 §5 branch lane)

- SYZ8 disc-locus reduction — LANDED. SYZ11–13 interface stack — LANDED. SYZ14 single-residual
  reduction — LANDED. SYZ15 T-loaded repair — LANDED. SYZ16 Claim 5.8 root reduction — LANDED.
- **SYZ17 (this note): the #138 X-degree budget is SPLIT and settled per part.**
  (a) T-dependent `degreeX P₀/P₁` bounds: PROVEN (explicit closed form, `alphaGradedBudget`),
  modulo the single fixed ξ-inverse weight constant;
  (b) absolute weight-1 form: confirmed unreachable by bookkeeping (wall re-exported) — its
  provenance must be GS geometry.

Open list for the floor lane after SYZ17:
1. `GammaGenuineTailPolynomial` non-degenerate (= the geometric core of Claim 5.8 / the
   *absolute* #138 content) — the one real §5 residual;
2. ξ-inverse weight supply (`Λ(ξ⁻¹) ≤ W_ξ` from norm/conjugate at `d_H = 2`) — mechanical-ish,
   needs a small norm calculus;
3. place-curve production; monic `d_H ≥ 3` per-coefficient T-form (span dichotomy); the
   SYZ11–13 T-carrier rename (mechanical).
