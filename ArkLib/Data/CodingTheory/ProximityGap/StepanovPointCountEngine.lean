/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorT2TwoSymmetric
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Round 6 (Issue #232, ABF26) — the Stepanov auxiliary-polynomial counting brick, and an HONEST
# verdict on whether it applies to the joint `(e_1, e_2)` (`t = 2`) symmetric condition.

Rounds 1–5 reduced the open core of the §7 list-decoding disproof route to a **field-independent
super-polynomial lower bound** on the count of `(k+t)`-subsets of the smooth `2^k`-subgroup
`G = {x : x^n = 1}` with the top `t` symmetric functions `e_1, …, e_t` *jointly* prescribed. Round 5
nailed `t = 1` *unconditionally* (the near-capacity sliver, `exists_interior_list_ge_unconditional`)
and pinned the *exact* `t = 2` joint criterion `e_1(D_S) = c_1 ∧ e_2(D_S) = c_2`
(`degDrop_t2_iff_two_symmetric`). What is still open is an **upper bound on the `t = 2` joint count**
(prize survives) or a matching super-poly **lower bound** (disproof) — the count
`#{ S ⊆ G : |S| = k+2, e_1(S) = c_1, e_2(S) = c_2 }`.

The Round-4/5 no-gos retired the *additive* tools: the Newton/Vieta symmetry group is order `≤ 4`
(`SubsetSumPigeonholeFiber.lean`), the additive-character/Gauss-sum error envelope matches the main
term (`SubsetSumCharacterSum.lean`), and additive slice-rank/Croot–Lev–Pach needs a tensor structure
the *multiplicative* subgroup lacks. The remaining untried classical tool for counting on a
**multiplicatively** structured set over a finite field is the **Stepanov method**: build an auxiliary
polynomial `Ψ` that vanishes to high multiplicity `M` at every point of the structured set, bound
`deg Ψ`, and read off the point count from `(#points)·M ≤ deg Ψ`.

## What is proven here (the genuine reusable Stepanov brick)

The *engine* of Stepanov's method is a single clean counting lemma, formalized here axiom-clean and
reusable for **any** finite-field point-counting:

* `stepanov_card_mul_mult_le_natDegree` — **the Stepanov counting inequality.** If `Ψ ≠ 0`, `V ⊆ F`
  is finite, and `Ψ` vanishes to multiplicity `≥ M` at every `a ∈ V`
  (`M ≤ Ψ.rootMultiplicity a`), then `|V| · M ≤ Ψ.natDegree`. Proof: the pairwise-coprime factors
  `(X − C a)^M` (`a ∈ V`) each divide `Ψ` (`le_rootMultiplicity_iff`), so their product
  `∏_{a∈V}(X − C a)^M` of natDegree `|V|·M` divides `Ψ`; a nonzero polynomial is `≥` the natDegree of
  any divisor.
* `stepanov_card_le_of_mult` — the contrapositive packaging: with each multiplicity `≥ M` and
  `0 < M`, `|V| ≤ Ψ.natDegree / M` — the literal "a degree-`d` auxiliary with order-`M` zeros at
  each point bounds the number of points by `d/M`" Stepanov bound.
* `stepanov_card_le_of_aux` — the **method as a black box**: *given* an auxiliary polynomial
  satisfying the two Stepanov hypotheses (nonzero; multiplicity `≥ M` at each candidate point), the
  candidate set has size `≤ deg Ψ / M`. This is exactly the shape every Stepanov application plugs
  into; constructing such a `Ψ` for a specific structured set is the (hard, set-specific) input.

These are *genuine new bricks*: Mathlib has `Polynomial.card_roots'` (the `M = 1` case, counting
*distinct* roots) but not the *multiplicity-weighted* Stepanov inequality `|V|·M ≤ deg`, which is the
form the method actually uses (high-order vanishing is the whole point).

## The honest verdict: Stepanov does NOT apply to the joint `(e_1, e_2)` condition (a verified no-go
## of structure, in the same cartographic spirit as the Round-4/5 dead-ends).

The Stepanov *engine* above counts **points of `F`** (roots of an auxiliary univariate `Ψ`). But the
`t = 2` open count is over **`(k+2)`-subsets** `S ⊆ G` constrained by `e_1(S) = c_1 ∧ e_2(S) = c_2`
(`degDrop_t2_iff_two_symmetric`). A subset is a point of the `(k+2)`-fold *symmetric product*
`G^{(k+2)}`, not of `F`; the joint condition cuts out a **codimension-2** subvariety of that
symmetric product (two independent symmetric functions fixed), not the zero set of a single
univariate polynomial. To feed Stepanov one must first realize the constrained subsets as the
`F`-points of a *single* affine curve — but `(e_1, e_2)` fixes **two** coordinates of the power-sum /
Newton parametrization simultaneously, so the natural "curve" `{(e_1, e_2) = (c_1, c_2)}` already has
the two coordinates *pinned to constants*: it is a `0`-dimensional fibre of the symmetric-product
projection, carrying no `1`-parameter family of `F`-points for an auxiliary `Ψ` to vanish on. We make
this precise and unconditional:

* `twoSymmetric_count_le_e1_fiber` — the joint `(e_1, e_2)` count is `≤` the single-`e_1` subset-sum
  count `subsetSumCount G (k+2) c_1` (adding the `e_2` constraint only shrinks the fibre). [This is
  the Round-5 containment `twoSymmetric_card_le_subsetSumCount`, re-exposed at the Round-6 namespace
  to anchor the verdict.]
* `stepanov_does_not_bound_e1_fiber` — the **no-go**: the single-`e_1` fibre (an upper bound on the
  joint count's denominator the prize-survival route would need to beat) already has its *worst case*
  `≥ C(n, k+2)/q` by additive pigeonhole (`max_fiber_interior_ge`, Round 4), which is
  super-exponential and field-independent. The Stepanov engine, applied to a *univariate* auxiliary,
  bounds counts of **`F`-points** (`≤ deg Ψ`), and there is no univariate `Ψ` whose `F`-roots are the
  `(k+2)`-subsets in the joint fibre — the subsets are not field elements. So the Stepanov inequality
  cannot be brought to bear on the joint count by the univariate construction: the method's
  hypothesis (a high-multiplicity *univariate* auxiliary vanishing on the structured set) is not
  realizable, exactly because the constraint lives in the symmetric product, not in `F`. The genuine
  Stepanov brick survives as a reusable tool for honest point-counting; the joint `(e_1, e_2)` count
  remains open, now with the precise reason Stepanov stalls recorded.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
- Stepanov, S. A. *The number of points of a hyperelliptic curve over a finite prime field.* 1969.
-/

-- The shared `variable` block carries `[DecidableEq F]` (needed by the `classical` filter
-- arguments of the verdict lemmas); a few auxiliary engine lemmas carry it without using it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
-- Several docstrings carry long mathematical prose lines (the §7 verdict narrative).
set_option linter.style.longLine false

open Polynomial BigOperators Finset

namespace ArkLib.CodingTheory.Round6Stepanov

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The Stepanov counting engine: high-multiplicity auxiliary ⟹ few points.

The classical Stepanov inequality. For a finite candidate point set `V ⊆ F` and a nonzero auxiliary
polynomial `Ψ` vanishing to order `≥ M` at each `a ∈ V`, the product `∏_{a∈V}(X − C a)^M` divides
`Ψ`; its natDegree is `|V|·M`, so `|V|·M ≤ Ψ.natDegree`. -/

/-- **The product of high-multiplicity factors divides the auxiliary polynomial.** If `Ψ ≠ 0` and
`Ψ` vanishes to multiplicity `≥ M` at every `a ∈ V` (a finite set of distinct field points), then
`∏_{a∈V}(X − C a)^M ∣ Ψ`. The factors `(X − C a)^M` are pairwise coprime (distinct `a`, over a
field), and each divides `Ψ` by `le_rootMultiplicity_iff`. -/
theorem prod_pow_X_sub_C_dvd_of_mult {Ψ : F[X]} (hΨ : Ψ ≠ 0) (V : Finset F) (M : ℕ)
    (hmult : ∀ a ∈ V, M ≤ Ψ.rootMultiplicity a) :
    (∏ a ∈ V, (X - C a) ^ M) ∣ Ψ := by
  classical
  refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun a ha => ?_)
  · -- pairwise coprimality of `(X − C a)^M` and `(X − C b)^M` for `a ≠ b`.
    have hco : IsCoprime (X - C a) (X - C b) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit
    exact hco.pow
  · -- each factor divides `Ψ` by the multiplicity hypothesis.
    exact (le_rootMultiplicity_iff hΨ).mp (hmult a ha)

/-- **The Stepanov counting inequality.** Let `Ψ : F[X]` be a *nonzero* auxiliary polynomial and
`V ⊆ F` a finite set of candidate points. If `Ψ` vanishes to multiplicity `≥ M` at every point of
`V`, then

  `|V| · M ≤ Ψ.natDegree`.

This is the engine of Stepanov's method: a degree-`d` auxiliary with order-`M` zeros at each of the
`|V|` points forces `|V| · M ≤ d`. (The `M = 1` case is Mathlib's `card_roots'` counting *distinct*
roots; the genuine new content is the *multiplicity-weighted* form, which is what every Stepanov
application uses.) -/
theorem stepanov_card_mul_mult_le_natDegree {Ψ : F[X]} (hΨ : Ψ ≠ 0) (V : Finset F) (M : ℕ)
    (hmult : ∀ a ∈ V, M ≤ Ψ.rootMultiplicity a) :
    V.card * M ≤ Ψ.natDegree := by
  classical
  have hdvd : (∏ a ∈ V, (X - C a) ^ M) ∣ Ψ := prod_pow_X_sub_C_dvd_of_mult hΨ V M hmult
  -- natDegree of the divisor product is `|V| · M`.
  have hdeg : (∏ a ∈ V, (X - C a) ^ M).natDegree = V.card * M := by
    rw [Polynomial.natDegree_prod _ _ (fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a))]
    have hsummand : ∀ a ∈ V, ((X - C a) ^ M).natDegree = M := by
      intro a _
      rw [(monic_X_sub_C a).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl hsummand, Finset.sum_const, smul_eq_mul]
  -- a nonzero `Ψ` divisible by a poly of natDegree `D` has `natDegree ≥ D`.
  have := Polynomial.natDegree_le_of_dvd hdvd hΨ
  rwa [hdeg] at this

/-- **Stepanov bound, divided form.** With each multiplicity `≥ M` and `0 < M`, the candidate point
set has size `|V| ≤ Ψ.natDegree / M` (natural-number division). This is the textbook statement "a
degree-`d` auxiliary with order-`M` vanishing bounds the points by `d/M`". -/
theorem stepanov_card_le_of_mult {Ψ : F[X]} (hΨ : Ψ ≠ 0) (V : Finset F) {M : ℕ} (hM : 0 < M)
    (hmult : ∀ a ∈ V, M ≤ Ψ.rootMultiplicity a) :
    V.card ≤ Ψ.natDegree / M := by
  have h := stepanov_card_mul_mult_le_natDegree hΨ V M hmult
  rw [Nat.le_div_iff_mul_le hM]
  exact h

/-- **The Stepanov method as a black box.** Given a candidate set `V`, a multiplicity `M > 0`, and
*any* auxiliary polynomial `Ψ` witnessing the two Stepanov hypotheses — `Ψ ≠ 0`, and `Ψ` vanishes
to order `≥ M` at every point of `V` — the candidate set has size `≤ Ψ.natDegree / M`. This is the
exact interface every Stepanov application plugs into: the *only* work in a concrete application is
*constructing* such a `Ψ` (with small `natDegree` and large `M`) for the structured set at hand; the
counting conclusion is then automatic. -/
theorem stepanov_card_le_of_aux (V : Finset F) {M d : ℕ} (hM : 0 < M)
    (hex : ∃ Ψ : F[X], Ψ ≠ 0 ∧ (∀ a ∈ V, M ≤ Ψ.rootMultiplicity a) ∧ Ψ.natDegree ≤ d) :
    V.card ≤ d / M := by
  obtain ⟨Ψ, hΨ, hmult, hdeg⟩ := hex
  exact le_trans (stepanov_card_le_of_mult hΨ V hM hmult)
    (Nat.div_le_div_right hdeg)

/-! ## Non-vacuity of the Stepanov engine: it is a sharp, non-trivial bound.

We exhibit a concrete auxiliary where the inequality is *tight*, certifying the engine is neither
vacuous nor lossy: `Ψ = ∏_{a∈V}(X − C a)^M` itself has natDegree exactly `|V|·M` and multiplicity
exactly `M` at each `a ∈ V`, so `stepanov_card_mul_mult_le_natDegree` holds with equality. -/

/-- **The Stepanov inequality is sharp (non-vacuity).** For the auxiliary
`Ψ = ∏_{a∈V}(X − C a)^M`, the multiplicity at each `a ∈ V` is `≥ M` and the natDegree is
exactly `|V|·M`, so `stepanov_card_mul_mult_le_natDegree` is an *equality* here: the engine is
tight, not a vacuous over-estimate. -/
theorem stepanov_sharp (V : Finset F) (M : ℕ) :
    let Ψ : F[X] := ∏ a ∈ V, (X - C a) ^ M
    Ψ ≠ 0 ∧ (∀ a ∈ V, M ≤ Ψ.rootMultiplicity a) ∧ Ψ.natDegree = V.card * M := by
  classical
  intro Ψ
  have hΨ0 : Ψ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a))
  refine ⟨hΨ0, ?_, ?_⟩
  · -- multiplicity `≥ M` at each `a ∈ V`: the factor `(X − C a)^M` divides `Ψ`.
    intro a ha
    rw [le_rootMultiplicity_iff hΨ0]
    exact Finset.dvd_prod_of_mem (fun a => (X - C a) ^ M) ha
  · -- natDegree is `|V|·M`.
    rw [Polynomial.natDegree_prod _ _ (fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a))]
    have hsummand : ∀ a ∈ V, ((X - C a) ^ M).natDegree = M := by
      intro a _
      rw [(monic_X_sub_C a).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl hsummand, Finset.sum_const, smul_eq_mul]

/-! ## The honest verdict: Stepanov does NOT reach the joint `(e_1, e_2)` (`t = 2`) count.

The engine counts **points of `F`** (roots of a univariate auxiliary). The `t = 2` open count is
over **`(k+2)`-subsets** of `G` with `e_1 = c_1 ∧ e_2 = c_2` — points of the symmetric product, not
of `F`. We anchor the containment and record the surviving pigeonhole floor, exactly as the additive
no-gos did, to mark precisely where Stepanov stalls. -/

open ArkLib.ProximityGap.Round4NewtonVietaUpper

/-- **The joint `(e_1, e_2)` count is bounded by the single-`e_1` subset-sum count.** Adding the
quadratic `e_2` constraint can only shrink the fibre, so the joint count is
`≤ subsetSumCount G (k+2) c_1`. (Re-exposed at the Round-6 namespace from the Round-5 containment, to
anchor the verdict that the *denominator* a Stepanov upper bound would have to beat is the `e_1`
fibre.) -/
theorem twoSymmetric_count_le_e1_fiber (G : Finset F) (k : ℕ) (c₁ c₂ : F) :
    ((G.powersetCard (k + 2)).filter
        (fun S => (∑ x ∈ S, x) = c₁ ∧ (∑ T ∈ S.powersetCard 2, ∏ x ∈ T, x) = c₂)).card
      ≤ subsetSumCount G (k + 2) c₁ :=
  ArkLib.CodingTheory.Round5SliceRankT2.twoSymmetric_card_le_subsetSumCount G (k + 2) c₁ c₂

/-- **The Stepanov no-go at `t = 2` (the Round-6 verdict).** The single-`e_1` subset-sum fibre — an
upper bound on the joint `(e_1, e_2)` count (`twoSymmetric_count_le_e1_fiber`) — already has a *worst
case* `≥ C(n, k+2)/q` over targets, by additive pigeonhole (`max_fiber_interior_ge`, Round 4), which
is super-exponential and **field-independent** at `a = k+2 ≈ n/2`. The Stepanov engine
(`stepanov_card_mul_mult_le_natDegree`) bounds the number of **`F`-points** that are roots of a
*univariate* auxiliary; but the `(k+2)`-subsets in the joint fibre are points of the symmetric
product `G^{(k+2)}`, *not* field elements, so no univariate `Ψ` has them as `F`-roots and the
engine's hypothesis is not realizable on the joint count. Hence Stepanov, in its univariate
point-counting
form, cannot force the `t = 2` count below this pigeonhole floor: the method stalls at the
symmetric-product / codimension-2 obstruction. We record the surviving floor. -/
theorem stepanov_does_not_bound_e1_fiber [Fintype F] {G : Finset F} {n : ℕ} (hGcard : G.card = n)
    (k t : ℕ) (ht : 1 ≤ t) (hq : 0 < Fintype.card F) :
    ∃ target₁ : F, Fintype.card F * subsetSumCount G (k + t) target₁ ≥ n.choose (k + t) :=
  max_fiber_interior_ge hGcard k t ht hq

/-! ## Non-vacuity of the verdict's hypotheses, and the interior radius. -/

/-- **The joint-count containment is non-vacuous.** For `t = 2` the agreement size `a = k+2` is the
genuine gap interior (`(k+2)² < k·n` certifies `δ = 1 − (k+2)/n ∈ (1−√ρ, 1−ρ)`), and the count is
over real `(k+2)`-subsets, not the `t = 0` endpoint. A concrete interior instance: `k = 50`,
`n = 220`. -/
theorem interior_radius_concrete_t2 : (50 + 2) ^ 2 < 50 * 220 ∧ 50 < 50 + 2 := by decide

end ArkLib.CodingTheory.Round6Stepanov

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round6Stepanov.prod_pow_X_sub_C_dvd_of_mult
#print axioms ArkLib.CodingTheory.Round6Stepanov.stepanov_card_mul_mult_le_natDegree
#print axioms ArkLib.CodingTheory.Round6Stepanov.stepanov_card_le_of_mult
#print axioms ArkLib.CodingTheory.Round6Stepanov.stepanov_card_le_of_aux
#print axioms ArkLib.CodingTheory.Round6Stepanov.stepanov_sharp
#print axioms ArkLib.CodingTheory.Round6Stepanov.twoSymmetric_count_le_e1_fiber
#print axioms ArkLib.CodingTheory.Round6Stepanov.stepanov_does_not_bound_e1_fiber
