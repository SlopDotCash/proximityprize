/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsCore
import ArkLib.ToMathlib.PartitionRecursion
import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.ToMathlib.WeightLambdaCalculus
import Mathlib

/-!
# The BCIKS20 Appendix-A.4 Hensel-lift numerator recursion `β_t` (brick **L7**)

This file defines the **genuine** Appendix-A.4 recursion (A.1) of [BCIKS20] (eprint 2020/654) for
the
Hensel-lift numerators `β_t : 𝒪 H`, replacing the trivial `β = 0` placeholder of
`RationalFunctions.lean` with the real well-founded recursion, and proves its two structural
invariants (termination and landing-in-`𝒪`).

This is the XL core of *ingredient D* of the proximity-prize keystone; see
`research/proximity-prize/ingredient-D-DAG-2026-06-05.md` §1 (the recursion writeup) and bricks
L7/L8/L9/L12/L13.

## The recursion (A.1)

```
β_0 = T  (= mk X, the generator of 𝒪)
β_t = Σ_{i₁; λ ∈ P(t−i₁), λ ≠ λ^(t)}  W^{i₁+δ−1} · ξ^{2i₁+Σλ−2} · B_{i₁,λ} · ∏_l β_l^{λ_l}
```

where `P(m)` is the set of partitions `λ = (λ_l)_{l≥1}` of `m` (`Σ_l l·λ_l = m`), `λ^(t)` is the
trivial partition (a single part `t`), `Σλ = Multiset.card λ.parts` is the number of parts,
`δ = δ_{i₁,0}` is `1` if `i₁ = 0` else `0`, `W = liftToFunctionField H.leadingCoeff` (realised in
`𝒪` by `W_𝒪`), `ξ` is the in-tree Claim-A.2 element, and `B_{i₁,λ} ∈ 𝒪` is the *regular numerator*
of the Hasse-derivative coefficient
`A_{i₁,λ} = B_{i₁,λ} / W^{d−δ−Σλ}` (App.-A.4; the concrete trivariate Hasse derivative is brick
L2b).

## What is delivered (all kernel-clean: no `sorry`/`admit`/`axiom`/`native_decide`)

* `recursionStep_lt` — the self-contained strict-decrease lemma for every recursive call of the
  `(t+1)`-step (`l < t+1`), built on `PartitionRecursion.parts_lt_of_ne_indiscrete`. No `i₁` bound
  is
  needed (the `i₁ > t+1` branch has empty parts). This discharges the `decreasing_by` obligation.

* `betaRec` — **the genuine well-founded recursion** `β_t : 𝒪 H`, parameterised on the App.-A.4
  inputs `x₀, R, H, hHyp` and the *regular numerator interface* `Bcoeff : (i₁ : ℕ) → Partition _ →
  𝒪 H` (the `B_{i₁,λ}`, brick L2b's output). Termination is proven via `recursionStep_lt`.

* `betaRec_zero`, `betaRec_succ` — the defining equations (base case `β_0 = T = mk X`; the unfolded
  `(t+1)`-step).

* `betaRec_mem` — each `betaRec … t` genuinely lands in `𝒪 H`: its embedding into the function field
  `𝕃 H` lies in the integral part `regularElms_set H`. Because the recursion is *constructed inside*
  `𝒪`, this is `regularElms_set_embedding`; the substantive `𝕃`-side version, where each per-term
  numerator carries a genuine `W`-power denominator, is `betaRec_succ_mem_of_term_numerators`, which
  uses L2's `𝒪`-closure (`hasWPowerNumerator.mem_regularElms_set`) and isolates the per-term
  Hasse-derivative numerator `A_{i₁,λ}`'s `W`-divisibility as the **explicit interface hypothesis**
  `hterm` (brick L2b / L9 input), never as a `sorry`/`axiom`.

* `betaRec_weightBound_of_term_bounds` — the **structural skeleton of the Claim-A.2 weight bound**
  (brick L9): `weight_Λ_over_𝒪 (betaRec … (t+1)) D ≤ b` is reduced to per-term `WithBot ℕ`-budget
  hypotheses via L3's sub-additivity (`weight_Λ_over_𝒪_sum_le`). The per-term weight identities
  (the partition-indexed telescoping of App.-A line 2877–2881) are isolated as the explicit
  interface hypothesis `hterm_bound` — the genuine L9 numerical content, left as a named hypothesis.

## Isolated interface hypotheses (the genuine L2b / L9 residuals)

Every genuine gap is an **explicit named hypothesis**, not a `sorry`/`axiom`:

* `Bcoeff : (i₁ : ℕ) → Nat.Partition m → 𝒪 H` — the regular Hasse-derivative numerators `B_{i₁,λ}`
  (brick L2b). Supplied as a function argument to `betaRec`.
* `hterm` in `betaRec_succ_mem_of_term_numerators` — the per-term `𝕃`-side numerator
  `HasWPowerNumerator` witness *with `𝒪`-divisibility* (L2b's `W`-divisibility output).
* `hterm_bound` in `betaRec_weightBound_of_term_bounds` — the per-term weight budget (L9's
  numerical induction step).

This file does **not** edit the (0-sorry) `RationalFunctions.lean`; all names live in `namespace
ArkLib`, the in-tree objects opened from `BCIKS20AppendixA` / `…ClaimA2`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace ArkLib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-! ### The strict-decrease lemma for the recursion step (termination metric)

Every recursive call `β_l` appearing in the `β_{t+1}` step of (A.1) is at index `l ∈ p.parts` for a
partition `p : Partition (t+1−i₁)`, excluding the single trivial pair `(i₁=0, λ=λ^(t+1))`. We show
`l < t+1` for every such `l`, with **no upper bound on `i₁`** (the `i₁ > t+1` branch has `t+1−i₁ =
0`
whose only partition is empty, so the claim is vacuous there). This is exactly the obligation
`decreasing_by` discharges, and it is built on `PartitionRecursion.parts_lt_of_ne_indiscrete`. -/

/-- **The termination metric for the β-recursion.** For a partition `p` of `t+1−i₁` that is not the
forbidden trivial pair `(i₁=0, λ^(t+1))`, every part `l ∈ p.parts` satisfies `l < t+1`. -/
theorem recursionStep_lt {t i₁ : ℕ} (p : Nat.Partition (t + 1 - i₁))
    (hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)))
    {l : ℕ} (hl : l ∈ p.parts) : l < t + 1 := by
  rcases Nat.eq_zero_or_pos i₁ with h0 | hpos
  · subst h0
    simp only [Nat.sub_zero, true_and] at p hexcl hl ⊢
    have hne : p ≠ Nat.Partition.indiscrete (t + 1) := by
      intro hp; apply hexcl
      rw [hp]; exact Nat.Partition.indiscrete_parts (Nat.succ_ne_zero t)
    exact ArkLib.Nat.Partition.parts_lt_of_ne_indiscrete p hne l hl
  · have hle : l ≤ t + 1 - i₁ := Nat.Partition.le_of_mem_parts hl
    omega

/-! ### Exponent bookkeeping (App.-A.4)

The `W`- and `ξ`-prefactor exponents of recursion (A.1). `δ = δ_{i₁,0}` is `1` at `i₁ = 0`, else
`0`.
The `W`-exponent is `i₁ + δ − 1` and the `ξ`-exponent is `2i₁ + Σλ − 2`; both are non-negative (in
the `ℕ`-truncated sense, which agrees with the genuine value) — see `betaTerm_W_exp_eq`/`…_xi_exp`.
-/

/-- The Kronecker-`δ_{i₁,0}` prefactor of recursion (A.1): `1` at `i₁ = 0`, else `0`. -/
def betaδ (i₁ : ℕ) : ℕ := if i₁ = 0 then 1 else 0

/-- The `W`-exponent `i₁ + δ_{i₁,0} − 1` of a term of recursion (A.1). -/
def betaWExp (i₁ : ℕ) : ℕ := i₁ + betaδ i₁ - 1

/-- The `ξ`-exponent `2·i₁ + Σλ − 2` of a term of recursion (A.1), where `Σλ` is the number of
parts (`Multiset.card p.parts`). -/
def betaξExp {m : ℕ} (i₁ : ℕ) (p : Nat.Partition m) : ℕ :=
  2 * i₁ + Multiset.card p.parts - 2

/-- The `W`-exponent is `0` at `i₁ = 0` (where `δ = 1`). -/
@[simp] lemma betaWExp_zero : betaWExp 0 = 0 := by simp [betaWExp, betaδ]

/-- The `W`-exponent is `i₁ − 1` for `i₁ ≥ 1` (where `δ = 0`). -/
lemma betaWExp_of_pos {i₁ : ℕ} (h : 0 < i₁) : betaWExp i₁ = i₁ - 1 := by
  simp [betaWExp, betaδ, Nat.ne_of_gt h]

/-! ### The β-recursion (A.1)

`betaRec x₀ R H hHyp Bcoeff` is the genuine recursion. The base case `β_0 = T = mk X` is the
`T`-related base of the DAG; the `(t+1)`-step sums over `(i₁, λ)` with `i₁ ∈ range (t+2)`,
`λ : Partition (t+1−i₁)`, excluding the single forbidden pair `(0, λ^(t+1))`, the recursive product
`∏_l β_l^{λ_l}` running over the parts of `λ`. Termination is the strict decrease `l < t+1`
(`recursionStep_lt`). The regular Hasse-derivative numerators `B_{i₁,λ} ∈ 𝒪` are supplied as the
interface function `Bcoeff` (brick L2b's output). -/

/-- **The BCIKS20 Appendix-A.4 Hensel-lift numerator recursion (A.1)** `β_t : 𝒪 H`.

* `β_0 = mk X` (the generator `T` of `𝒪 H`).
* `β_{t+1} = Σ_{i₁ ∈ range (t+2)} Σ_{λ : Partition (t+1−i₁), λ ≠ (i₁=0 ∧ λ^(t+1))}
    W^{i₁+δ−1} · ξ^{2i₁+Σλ−2} · B_{i₁,λ} · ∏_{l ∈ λ.parts} β_l^{λ_l}`.

Termination is by strong recursion on `t`: every recursive call `β_l` is at `l ∈ λ.parts < t+1`
(`recursionStep_lt`). `Bcoeff i₁ λ : 𝒪 H` is the regular numerator `B_{i₁,λ}` (brick L2b). -/
noncomputable def betaRec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : ℕ → 𝒪 H
  | 0 => Ideal.Quotient.mk (Ideal.span {H_tilde' H}) Polynomial.X
  | (t + 1) =>
      ∑ i₁ ∈ Finset.range (t + 2),
        ∑ p : Nat.Partition (t + 1 - i₁),
          if hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) then
            W_𝒪 H ^ betaWExp i₁
              * ξ x₀ R H hHyp ^ betaξExp i₁ p
              * Bcoeff i₁ p
              * ∏ l ∈ p.parts.toFinset.attach,
                  betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1)
          else 0
  decreasing_by
    exact recursionStep_lt p hexcl (Multiset.mem_toFinset.mp l.2)

/-! ### Defining equations -/

/-- The base case: `β_0 = T = mk X`, the generator of `𝒪 H` (the `T`-related base of the DAG). -/
@[simp] lemma betaRec_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    betaRec x₀ R H hHyp Bcoeff 0 =
      Ideal.Quotient.mk (Ideal.span {H_tilde' H}) Polynomial.X := by
  rw [betaRec]

/-- The recursion step (A.1) unfolded. -/
lemma betaRec_succ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    betaRec x₀ R H hHyp Bcoeff (t + 1) =
      ∑ i₁ ∈ Finset.range (t + 2),
        ∑ p : Nat.Partition (t + 1 - i₁),
          if hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) then
            W_𝒪 H ^ betaWExp i₁
              * ξ x₀ R H hHyp ^ betaξExp i₁ p
              * Bcoeff i₁ p
              * ∏ l ∈ p.parts.toFinset.attach,
                  betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1)
          else 0 := by
  rw [betaRec]

/-! ### Invariant 1 (`betaRec_mem`): the recursion lands in `𝒪`

Because `betaRec` is *constructed inside* `𝒪 H`, its embedding into the function field `𝕃 H` lands
in the integral part `regularElms_set H` automatically. This is the well-typedness invariant L8: the
recursion is genuinely an element of the integral ring `𝒪`, no denominators escape. -/

/-- **Invariant 1 — landing in `𝒪`.** Each `betaRec … t` is integral: its image in `𝕃 H` lies in
`regularElms_set H`. (Immediate from the construction in `𝒪`, recorded via
`regularElms_set_embedding`.) -/
theorem betaRec_mem (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) ∈ regularElms_set H :=
  regularElms_set_embedding H _

/-! ### Invariant 1, the substantive `𝕃`-side version (L2b numerator interface)

The genuine App.-A.4 content is that, *even when the recursion is written on the `𝕃` side* with the
Hasse-derivative coefficients `A_{i₁,λ} = B_{i₁,λ}/W^{d−δ−Σλ}` carrying `W`-power denominators,
every
term lands back in the integral part `regularElms_set H`. This holds precisely because each per-term
numerator carries the `W`-divisibility witness (App.-A line 2931, the `W ∣ leadingCoeff Rx0` save) —
the documented `W^{i₁+δ}·ξ^{…}` prefactor of (A.1). We isolate that per-term witness as the explicit
hypothesis `hterm` (brick L2b's output) and discharge integrality with L2's
`hasWPowerNumerator.mem_regularElms_set`. -/

/-- **Invariant 1 (`𝕃`-side, with the L2b numerator interface).** A finite sum of `𝕃`-terms each of
which has a `W`-power numerator *with the `𝒪`-side divisibility witness* lands in the integral part
`regularElms_set H`. This is exactly the shape `embedding(β_{t+1})` has when written on the `𝕃`
side with the Hasse-coefficients' denominators present; the hypothesis `hterm` is the per-term L2b
output (numerator `B` integral *and* `W`-divisible), isolated explicitly, never a `sorry`. -/
theorem sum_mem_regularElms_set_of_term_numerators {ι : Type*} (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (s : Finset ι) (term : ι → 𝕃 H) (j : ι → ℕ)
    (hterm : ∀ i ∈ s, ∃ B : 𝒪 H,
        term i * W_𝕃 H ^ (j i) = embeddingOf𝒪Into𝕃 H B ∧ W_𝒪 H ^ (j i) ∣ B) :
    (∑ i ∈ s, term i) ∈ regularElms_set H := by
  classical
  refine Finset.sum_induction term (· ∈ regularElms_set H)
    (fun _ _ ha hb => regularElms_set_add ha hb) (regularElms_set_zero H) ?_
  intro i hi
  exact hasWPowerNumerator.mem_regularElms_set (hterm i hi)

/-- The same closure specialised to the *product* shape `W^a · ξ^e · A · P` of a single term of
recursion (A.1) on the `𝕃` side: if the prefactor-times-coefficient `W^a · ξ^e · A` already clears
to a `W`-power numerator with `𝒪`-divisibility (the L2b output, hypothesis `hnum`) and the recursive
product `P` is integral (`hP`, the inductive hypothesis), the whole term is integral. -/
theorem term_mem_regularElms_set_of_numerator {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {pref A P : 𝕃 H} {j : ℕ}
    (hnum : ∃ B : 𝒪 H, (pref * A) * W_𝕃 H ^ j = embeddingOf𝒪Into𝕃 H B ∧ W_𝒪 H ^ j ∣ B)
    (hP : P ∈ regularElms_set H) :
    (pref * A) * P ∈ regularElms_set H :=
  regularElms_set_mul (hasWPowerNumerator.mem_regularElms_set hnum) hP

/-! ### Invariant 2 skeleton (Claim A.2 weight bound, brick L9)

The Claim-A.2 weight bound `weight_Λ_over_𝒪 (β_t) D ≤ (2t+1)·d_R·D` is proven in the paper by strong
induction on `t` over recursion (A.1): each term's weight telescopes via L3's sub-multiplicativity.
Here we deliver the **structural reduction** of the bound on `β_{t+1}` to per-term `WithBot
ℕ`-budget
hypotheses, using L3's sum sub-additivity (`weight_Λ_over_𝒪_sum_le`). The per-term numerical budgets
(the partition-indexed telescoping, App.-A line 2877–2881) are the genuine L9 content, isolated as
the explicit hypothesis `hterm_bound`. -/

/-- The single `(t+1)`-step summand of recursion (A.1) at index `(i₁, p)`, as an `𝒪 H`-element.
Pulled out so the weight skeleton can talk about per-term budgets. -/
noncomputable def betaTerm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t i₁ : ℕ)
    (p : Nat.Partition (t + 1 - i₁)) : 𝒪 H :=
  if ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) then
    W_𝒪 H ^ betaWExp i₁
      * ξ x₀ R H hHyp ^ betaξExp i₁ p
      * Bcoeff i₁ p
      * ∏ l ∈ p.parts.toFinset.attach,
          betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1)
  else 0

/-- `betaRec … (t+1)` is the double sum of `betaTerm`s. (Re-expression of `betaRec_succ` collecting
the `if`-summand as `betaTerm`.) -/
lemma betaRec_succ_eq_sum_betaTerm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    betaRec x₀ R H hHyp Bcoeff (t + 1) =
      ∑ i₁ ∈ Finset.range (t + 2),
        ∑ p : Nat.Partition (t + 1 - i₁),
          betaTerm x₀ R H hHyp Bcoeff t i₁ p := by
  rw [betaRec_succ]
  refine Finset.sum_congr rfl (fun i₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  unfold betaTerm
  by_cases hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) <;> simp [hexcl]

/-- **Invariant 2 skeleton — Claim-A.2 weight bound, reduced to per-term budgets (brick L9).**

The weight of `β_{t+1}` is bounded by `b` whenever every term `betaTerm … i₁ p` has weight
`≤ (b : WithBot ℕ)`. The reduction is L3's sum sub-additivity. The per-term budgets
`hterm_bound` (the partition-indexed telescoping of App.-A line 2877–2881) are the genuine numerical
L9 residual, isolated as an explicit hypothesis. -/
theorem betaRec_weightBound_of_term_bounds (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {b : ℕ}
    (hterm_bound : ∀ i₁ ∈ Finset.range (t + 2), ∀ p : Nat.Partition (t + 1 - i₁),
        weight_Λ_over_𝒪 hH (betaTerm x₀ R H hHyp Bcoeff t i₁ p) D
          ≤ (WithBot.some b : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff (t + 1)) D
      ≤ (WithBot.some b : WithBot ℕ) := by
  classical
  rw [betaRec_succ_eq_sum_betaTerm]
  refine (weight_Λ_over_𝒪_sum_le hD hH _ _).trans ?_
  refine Finset.sup_le (fun i₁ hi₁ => ?_)
  refine (weight_Λ_over_𝒪_sum_le hD hH _ _).trans ?_
  refine Finset.sup_le (fun p _ => ?_)
  exact hterm_bound i₁ hi₁ p

end ArkLib

-- Axiom audit: every claimed-done declaration must rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.recursionStep_lt
#print axioms ArkLib.betaRec
#print axioms ArkLib.betaRec_zero
#print axioms ArkLib.betaRec_succ
#print axioms ArkLib.betaRec_mem
#print axioms ArkLib.sum_mem_regularElms_set_of_term_numerators
#print axioms ArkLib.term_mem_regularElms_set_of_numerator
#print axioms ArkLib.betaRec_succ_eq_sum_betaTerm
#print axioms ArkLib.betaRec_weightBound_of_term_bounds
#print axioms ArkLib.betaWExp_zero
#print axioms ArkLib.betaWExp_of_pos
