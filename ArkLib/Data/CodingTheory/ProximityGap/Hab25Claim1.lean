/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AffineCapture

/-!
# Hab25 Claim 1, faithfully: the dichotomy proof from the paper

Source: U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
ePrint 2025/2110, §3 (paper in hand). The proof of **Claim 1** there
(`|E_{i,j}| ≤ (ℓ⁶/3)·(ρn)²`) is a *dichotomy by contradiction*:

> Suppose `|E_{i,j}|` exceeds the threshold. Then the branch-incidence set `S_{x₀,R,H}`
> (scalars whose proximate's branch passes through the chosen `x₀`-fiber component `H_{i,j}`)
> exceeds `2·D_Y²·D_X·D_{YZ}` — by [BCI⁺20, Claim 5.7] this suffices for Steps 5–7 of their
> analysis (and [BCI⁺20, Appendix C] in the inseparable case `fᵢ > 0`) to force
>
>   `Rᵢ(X, Y^{p^{fᵢ}}, Z) = (Y − (a(X) + Z·b(X)))^{p^{fᵢ}}`,
>
> so the folding proximate is the **unique affine pair** `p_z = a + z·b` for *every*
> `z ∈ E_{i,j}`. Then every such `z` "must improve agreement beyond the correlated agreement
> set `A°`", and *from the proof of Lemma 1* the number of improving scalars is at most
> `|D \ A°| ≤ n` — contradicting `(ℓ⁶/3)(ρn)² = ((m+½)⁶/3ρ)·n² > n`, which holds regardless
> of parameters. ∎

Every ingredient of that argument except the bracketed [BCI⁺20] citation is already proven
in-tree:
* the improvement step is `affineCaptured_improve` (this file's import);
* the improving-scalar count is `factorImprove_card_le_n` / `hab25_endgame_count`;
* the final numeric check is `johnson_key`-style arithmetic (`threshold_gt_n` below).

This file therefore states and proves **Claim 1 with the residual pinned to the exact
[BCI⁺20] citation**:

* `claim1_dichotomy` — if capture-above-threshold holds (the Steps-5–7 output: past the
  threshold, a single degree-`< k` affine pair captures *all* scalars of the cell), then
  `|E_{i,j}| ≤ T` for any threshold `T ≥ n`;
* `hab25_threshold_gt_n` — the paper's closing numerology: `(m+½)⁶·n² / (3ρ) > n`
  "regardless of the concrete choice of parameters" (ℕ-rounded form);
* `theorem2_of_claim1_cells` — Theorem 2 reassembled: `≤ ℓ` cells each within the
  threshold give `|E| ≤ ℓ·T` (the `(ℓ⁷/3)(ρn)²` bound after instantiation), composing with
  the proven union bound.

The single remaining mathematical input for the Johnson MCA bound is now **exactly**
[BCI⁺20, Claim 5.7 + Steps 5–7 + Appendix C] — the `S_{x₀,R,H}`-large ⇒ affine-power
identification — stated per cell as the `hsteps57` hypothesis of `claim1_dichotomy`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory Polynomial

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Hab25 Claim 1, the dichotomy proof (paper §3, verbatim logic).**

Let `Ecell` be one cell `E_{i,j}` of the factor decomposition and `T ≥ n` the Claim-1
threshold. The hypothesis `hsteps57` is the *exact* content the paper cites from
[BCI⁺20, Claim 5.7 + Steps 5–7 + Appendix C]: if the cell exceeds the threshold, the
branch-incidence is large enough to force the factor to be the affine power
`(Y − (a+Zb))^{p^f}`, so a single degree-`< k` pair `(a, b)` captures **every** scalar of
the cell. Conclusion: `|E_{i,j}| ≤ T`.

Proof (the paper's): if `|Ecell| > T`, obtain the pair; every `z ∈ Ecell` must improve
agreement beyond `A°` (`affineCaptured_improve`, = "from the proof of Lemma 1"), so
`|Ecell| ≤ n ≤ T` — contradiction. -/
theorem claim1_dichotomy (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) ι₀) (Ecell : Finset F₀) (T : ℕ)
    (hn : Fintype.card ι₀ ≤ T)
    (hsteps57 : T < Ecell.card →
      ∃ a b : F₀[X], a.natDegree < k ∧ b.natDegree < k ∧
        ∀ γ ∈ Ecell, AffineCaptured domain k δ u γ (a, b)) :
    Ecell.card ≤ T := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hdega, hdegb, hcap⟩ := hsteps57 hcon
  -- every scalar of the cell improves agreement beyond `A°` (Lemma-1 endgame shape)
  have himprove : ∀ γ ∈ Ecell,
      ∃ x ∈ disagreeSet (fun i => a.eval (domain i) - u 0 i)
          (fun i => b.eval (domain i) - u 1 i),
        affineGap (fun i => a.eval (domain i) - u 0 i)
          (fun i => b.eval (domain i) - u 1 i) γ x = 0 := fun γ hγ =>
    affineCaptured_improve (ab := (a, b)) hdega hdegb (hcap γ hγ)
  -- "from the proof of Lemma 1": at most `n` improving scalars
  have hcount : Ecell.card ≤ Fintype.card ι₀ :=
    factorImprove_card_le_n _ _ Ecell himprove
  omega

/-- **The paper's closing numerology** (ℕ-honest form): `n < T` for any threshold
`T ≥ n + 1`; instantiated by the paper at `T = ⌈(ℓ⁶/3)(ρn)²⌉ = ⌈((m+½)⁶/3ρ)·n²⌉`, which
exceeds `n` "regardless of the concrete choice of parameters" since
`(m+½)⁶ ≥ 3.5⁶ > 3 ≥ 3ρ`. We record the parameter inequality in the clean real form: for
`m ≥ 3`, `0 < ρ ≤ 1`, `1 ≤ n`,  `n < (m+½)⁶/(3ρ)·n²`. -/
theorem hab25_threshold_gt_n {m ρ n : ℝ} (hm : 3 ≤ m) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 1 ≤ n) :
    n < (m + 1/2) ^ 6 / (3 * ρ) * n ^ 2 := by
  have h35 : (3.5 : ℝ) ^ 6 ≤ (m + 1/2) ^ 6 := by
    have h : (3.5 : ℝ) ≤ m + 1/2 := by linarith
    exact pow_le_pow_left₀ (by norm_num) h 6
  have hkey : 3 * ρ < (m + 1/2) ^ 6 := by nlinarith
  have hdiv : 1 < (m + 1/2) ^ 6 / (3 * ρ) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hn2 : n ≤ n ^ 2 := by nlinarith
  calc n = 1 * n := (one_mul n).symm
    _ < (m + 1/2) ^ 6 / (3 * ρ) * n := by
        exact mul_lt_mul_of_pos_right hdiv (by linarith)
    _ ≤ (m + 1/2) ^ 6 / (3 * ρ) * n ^ 2 := by
        refine mul_le_mul_of_nonneg_left hn2 (by positivity)

/-- **Theorem 2 reassembled from Claim-1 cells** (paper §3): the bad set decomposes into
`≤ ℓ` cells `E_{i,j}` (the irreducible factors of the GS interpolant, refined by the
`x₀`-fiber components — `#(i,j) ≤ D_Y < ℓ`), each within the Claim-1 threshold by
`claim1_dichotomy`; the union bound gives `|E| ≤ ℓ·T` — the `(ℓ⁷/3)(ρn)²` bound of
Theorem 2 after instantiating `T`. -/
theorem theorem2_of_claim1_cells (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) ι₀)
    {Idx : Type} [DecidableEq Idx]
    (E : Finset F₀) (Index : Finset Idx) (Ecell : Idx → Finset F₀)
    (ℓ T : ℕ)
    (hℓ : Index.card ≤ ℓ)
    (hn : Fintype.card ι₀ ≤ T)
    (hcover : E ⊆ Index.biUnion Ecell)
    (hsteps57 : ∀ ij ∈ Index, T < (Ecell ij).card →
      ∃ a b : F₀[X], a.natDegree < k ∧ b.natDegree < k ∧
        ∀ γ ∈ Ecell ij, AffineCaptured domain k δ u γ (a, b)) :
    E.card ≤ ℓ * T := by
  refine le_trans (theorem2_union_bound E Index Ecell T hcover fun ij hij =>
    claim1_dichotomy domain k δ u (Ecell ij) T hn (hsteps57 ij hij)) ?_
  exact Nat.mul_le_mul_right _ hℓ

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.claim1_dichotomy
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25_threshold_gt_n
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.theorem2_of_claim1_cells
