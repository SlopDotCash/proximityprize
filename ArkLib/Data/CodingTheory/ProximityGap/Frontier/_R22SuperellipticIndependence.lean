/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovNonVanishing
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R21StepanovS1

/-!
# LANE SUPERELL (#466 round 22): does the #232 Stepanov non-vanishing generalize to y^d?

Question: `StepanovNonVanishing.obstruction_forces_trivial` proves the TWO-block
(hyperelliptic, `d = 2`) independence `A₀ + g^((q−1)/2)·A₁ ≠ 0`.  The `d ≥ 3` faces
(`TripleLinearHasse` etc.) need the `d`-block analogue
`∑_{j<d} g^(j(q−1)/d) · A_j(X, X^q) = 0 ⟹ ∀ j, A_j = 0`.

## The lemma-by-lemma generalization map (the lane's main finding; details in the report)

* `subq` machinery and faithfulness: identical, `d`-independent.
* `pow_card_eq_subq_map_C` (`g^q = subq ĝ`): identical.
* Square-first (`d = 2`) becomes norm-first: multiply the `d` conjugate relations,
  fold the product through `w^d = g^(q−1)`, and use `g^q = subq ĝ`.
* `squarefree_not_isSquare(_ratFunc)` becomes `squarefree_not_isPow(_ratFunc)`:
  proven below for every exponent `e ≥ 2`.
* Kummer: Mathlib supplies the odd-exponent criterion; the `4 ∣ d` side condition is
  reserved for the norm-fold lane.
* `genus_squarefree_forces_trivial` becomes norm-form plus Kummer independence of
  `1,θ,…,θ^(d−1)`.

**Verdict: in-tree-Stepanov-REACHABLE, no new mathematics.**  Every `d = 2` step has a
`d`-analogue whose algebraic inputs are below or in Mathlib; the remaining cost is the
norm-form Leibniz/symmetric-function bookkeeping (est. 400–800 lines).  The ONLY
2-specific conveniences are (i) the norm being a bare square, (ii) Kummer needing no
`−4` side condition; neither is a wall.  Budget generalizes as `d·D + (d−1)·deg g < q`
(matches `2D + 3 < q` at `d=2`, cubic).

## Probe (scratchpad `probe_r22_superell.py`, d = 4, q = 13, g = X(X−1)(X−2), e = 3)

* `J = 0` blocks: `1, g³, g⁶, g⁹` independent over `deg ≤ D` coefficients for ALL
  `D ≤ 8`; first failure EXACTLY at `D = 9 = deg g^((q−1)/d)` with nullity `d − 1 = 3` —
  the kernel is the tautological collision `(g³)·g^(3j) = 1·g^(3(j+1))` once `w` itself
  fits the coefficient budget.  Structural, not a Stepanov failure.
* `J ≤ 1` (with `X^q` digit): independent for `D ≤ 4`, fails at `D = 5` (cross-digit
  collision `deg g⁶ = 18 = 13 + 5`).  Both boundaries are exactly the degree-collision
  predictions; the sufficient budget `dD + (d−1)γ < q` is safely inside.
* Point counts `y⁴ = x(x−1)(x−2)(x−3)`: `|N − q|/√q ≤ 3.05` over
  `q ∈ {13,…,197}, q ≡ 1 (4)` — consistent with Hasse–Weil `2g√q`, `C(d) ~ d²`-ish:
  the classical method's arithmetic closes at `d = 4`.

## What THIS file proves (axiom-clean) vs names

Proven: `squarefree_not_isPow`, `squarefree_not_isPow_ratFunc` (the `e ≥ 2` power
analogues of the in-tree section-1 lemmas), `squarefree_pow_irreducible_ratFunc_of_odd`
(the odd-`d` Kummer chain, generalizing `squarefree_quadratic_irreducible_ratFunc`),
`blocks_pow_le` (the `d`-fold budget), `combined_blocks_lt_general` (the `d=2` budget
for ARBITRARY squarefree `g`, freeing `_R21StepanovS1` from the cubic),
`two_block_independence_general` = `dBlockIndependence_two` (the `d = 2` INSTANCE of the
named `d`-block Prop, proven from in-tree `obstruction_forces_trivial` — consistency check).

Named (open): `DBlockIndependence` for `d ≥ 3` — the norm-fold construction above.
No closure claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence

open Polynomial ArkLib.ProximityGap.StepanovNonVanishing

set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F]

/-! ## 1. Squarefree ⟹ not a perfect `e`-th power (`e ≥ 2`), in `F[X]` and `RatFunc F` -/

/-- A squarefree polynomial of positive degree is not a perfect `e`-th power, `e ≥ 2`. -/
theorem squarefree_not_isPow (g : F[X]) (hsf : Squarefree g) (hdeg : 0 < g.natDegree)
    {e : ℕ} (he : 2 ≤ e) : ¬ ∃ h : F[X], g = h ^ e := by
  rintro ⟨h, rfl⟩
  have hdvd : h * h ∣ h ^ e := by
    rw [← sq]; exact pow_dvd_pow h he
  have hu : IsUnit h := hsf h hdvd
  have : IsUnit (h ^ e) := hu.pow e
  have hd0 : (h ^ e).natDegree = 0 := natDegree_eq_zero_of_isUnit this
  omega

/-- **Function-field form.** A squarefree `g` of positive degree has no `e`-th root
(`e ≥ 2`) in `RatFunc F`: a root would be integral over `F[X]` (root of `Xᵉ − C g`),
hence in `F[X]` by integral closedness, contradicting `squarefree_not_isPow`. -/
theorem squarefree_not_isPow_ratFunc (g : F[X]) (hsf : Squarefree g)
    (hdeg : 0 < g.natDegree) {e : ℕ} (he : 2 ≤ e) :
    ¬ ∃ r : RatFunc F, r ^ e = algebraMap F[X] (RatFunc F) g := by
  rintro ⟨r, hr⟩
  have hint : IsIntegral F[X] r := by
    refine ⟨X ^ e - C g, ?_, ?_⟩
    · apply monic_X_pow_sub
      exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_of_lt he)
    · rw [eval₂_sub, eval₂_X_pow, eval₂_C, hr, sub_self]
  obtain ⟨h, hh⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have key : algebraMap F[X] (RatFunc F) g = algebraMap F[X] (RatFunc F) (h ^ e) := by
    rw [map_pow, hh, hr]
  have hg : g = h ^ e := RatFunc.algebraMap_injective F key
  exact squarefree_not_isPow g hsf hdeg he ⟨h, hg⟩

/-! ## 2. The odd-`d` Kummer chain: `Y^d − g` irreducible over `RatFunc F` -/

/-- **Odd-`d` generalization of `squarefree_quadratic_irreducible_ratFunc`.**  For odd
`d ≥ 2`(in fact odd `d ≥ 3`) and `g` squarefree of positive degree, `Y^d − g` is
irreducible over `RatFunc F`: Mathlib's Kummer criterion for odd exponents needs only
"no `p`-th root for each prime `p ∣ d`", supplied by `squarefree_not_isPow_ratFunc`.
(The `4 ∣ d` case additionally needs the `−4·(4th power)` exclusion —
`X_pow_sub_C_irreducible_iff_of_prime_pow` etc.; left to the norm-fold lane.) -/
theorem squarefree_pow_irreducible_ratFunc_of_odd (g : F[X]) (hsf : Squarefree g)
    (hdeg : 0 < g.natDegree) {d : ℕ} (hd : Odd d) :
    Irreducible (X ^ d - C (algebraMap F[X] (RatFunc F) g)) := by
  apply X_pow_sub_C_irreducible_of_odd hd
  intro p hp hpd b hb
  exact squarefree_not_isPow_ratFunc g hsf hdeg hp.two_le ⟨b, hb⟩

/-! ## 3. Block-degree budgets for the `d`-fold norm form -/

/-- Blocks of a `k`-th power are bounded by `k·D` (the `d`-fold-product budget the
norm form needs; generalizes `_R21StepanovS1.blocks_mul_le`). -/
theorem blocks_pow_le {A : Polynomial (Polynomial F)} {D : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ D) :
    ∀ k : ℕ, ∀ j, ((A ^ k).coeff j).natDegree ≤ k * D := by
  intro k
  induction k with
  | zero =>
    intro j
    simp only [pow_zero, Nat.zero_mul]
    rw [Polynomial.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    intro j
    rw [pow_succ, Polynomial.coeff_mul]
    refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    refine natDegree_mul_le.trans (le_trans (add_le_add (ih x.1) (hA x.2)) ?_)
    rw [Nat.succ_mul]

/-- The combined-square-block budget for ARBITRARY `g` (frees `_R21StepanovS1`'s
`combined_blocks_lt` from the cubic): per-blocks `≤ D` and `2D + deg g < q` give the
`hblk` hypothesis of `obstruction_forces_trivial`. -/
theorem combined_blocks_lt_general (g : F[X]) {D q : ℕ}
    (hD : 2 * D + g.natDegree < q)
    (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree ≤ D) (h1 : ∀ j, (A1.coeff j).natDegree ≤ D) :
    ∀ j, ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree < q := by
  intro j
  have hA0sq : ∀ j, ((A0 ^ 2).coeff j).natDegree ≤ 2 * D := blocks_pow_le h0 2
  have hA1sq : ∀ j, ((A1 ^ 2).coeff j).natDegree ≤ 2 * D := blocks_pow_le h1 2
  have hterm1 : ((C g * A0 ^ 2).coeff j).natDegree ≤ g.natDegree + 2 * D := by
    rw [coeff_C_mul]
    exact natDegree_mul_le.trans (add_le_add le_rfl (hA0sq j))
  have hterm2 : (((g.map (C : F →+* F[X])) * A1 ^ 2).coeff j).natDegree ≤ 2 * D := by
    rw [Polynomial.coeff_mul]
    refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    refine natDegree_mul_le.trans ?_
    have hmap : (((g.map (C : F →+* F[X]))).coeff x.1).natDegree = 0 := by
      rw [coeff_map]; exact natDegree_C _
    have := hA1sq x.2
    omega
  calc ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree
      = ((C g * A0 ^ 2).coeff j - ((g.map C) * A1 ^ 2).coeff j).natDegree := by
        rw [coeff_sub]
    _ ≤ max ((C g * A0 ^ 2).coeff j).natDegree (((g.map C) * A1 ^ 2).coeff j).natDegree :=
        natDegree_sub_le _ _
    _ < q := max_lt (by omega) (by omega)

/-! ## 4. The `d`-block independence Prop and its proven `d = 2` instance -/

/-- **THE `d`-BLOCK STEPANOV INDEPENDENCE** (the named target of the superelliptic
face): every relation `∑_{j<d} g^(j(q−1)/d) · A_j(X, X^q) = 0` with per-block degree
`≤ D` forces all `A_j = 0`.  The `d = 2` instance is proven below from the in-tree #232
core; `d ≥ 3` is the norm-fold construction (open, mapped in the header). -/
def DBlockIndependence (F : Type*) [Field F] (d q D : ℕ) (g : F[X]) : Prop :=
  ∀ A : Fin d → Polynomial (Polynomial F),
    (∀ j, ∀ k, ((A j).coeff k).natDegree ≤ D) →
    (∑ j : Fin d, g ^ ((j : ℕ) * ((q - 1) / d)) * subq q (A j)) = 0 →
    ∀ j, A j = 0

/-- **The `d = 2` instance, proven from in-tree `obstruction_forces_trivial`** — the
consistency check that `DBlockIndependence` is the right generalization, now for
ARBITRARY squarefree `g` (not just the cubic) at budget `2D + deg g < q`. -/
theorem dBlockIndependence_two [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    {D : ℕ} (hD : 2 * D + g.natDegree < Fintype.card F) :
    DBlockIndependence F 2 (Fintype.card F) D g := by
  intro A hblk hsum j
  have hsum2 : subq (Fintype.card F) (A 0)
      + g ^ ((Fintype.card F - 1) / 2) * subq (Fintype.card F) (A 1) = 0 := by
    have := hsum
    rw [Fin.sum_univ_two] at this
    simpa using this
  obtain ⟨h0, h1⟩ := obstruction_forces_trivial g hg hdeg hq_odd (A 0) (A 1)
    (combined_blocks_lt_general g hD (A 0) (A 1) (hblk 0) (hblk 1)) hsum2
  fin_cases j
  · exact h0
  · exact h1

/-- Cubic corollary: the `_R21StepanovS1` setting is literally the `d = 2` instance of
the `d`-block Prop (wiring check with the round-21 lane). -/
theorem dBlockIndependence_two_cubic [Fintype F] [DecidableEq F]
    (hq_odd : Odd (Fintype.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {D : ℕ} (hD : 2 * D + 3 < Fintype.card F) :
    DBlockIndependence F 2 (Fintype.card F) D
      (ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic u v) := by
  apply dBlockIndependence_two
  · exact ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_squarefree hu hv huv
  · rw [ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_natDegree]; omega
  · exact hq_odd
  · rw [ArkLib.ProximityGap.Frontier.R21StepanovS1.cubic_natDegree]; omega

end ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence in
#print axioms squarefree_not_isPow
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence in
#print axioms squarefree_not_isPow_ratFunc
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence in
#print axioms squarefree_pow_irreducible_ratFunc_of_odd
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence in
#print axioms blocks_pow_le
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence in
#print axioms combined_blocks_lt_general
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence in
#print axioms dBlockIndependence_two
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence in
#print axioms dBlockIndependence_two_cubic
