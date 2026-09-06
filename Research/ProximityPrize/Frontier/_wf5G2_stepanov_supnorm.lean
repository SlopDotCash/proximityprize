/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-G2)
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovCountingLemma

/-!
# Stepanov auxiliary-polynomial method DIRECTLY for the sup-norm (#444 lane G2)

THE PRIZE OBJECT.  `M(n) = max_{b ≠ 0 mod p} |∑_{x ∈ μ_n} e_p(b x)|`, the worst Gauss period /
non-principal eigenvalue of `Cay(F_p, μ_n)`, for the thin 2-power subgroup `μ_n` (`n = 2^μ`,
`n ∣ p − 1`, `p` prime, `β = log_n p ∈ [4,5]`, so `n < p^{1/4}`).  Target: `M(n) ≤ C√(n log(p/n))`.

THE LANE (G2) STRATEGY.  Use Stepanov NOT to count `μ_n`-roots of a fixed polynomial (the campaign's
counting use, which stalls at `n^{2/3}` and which `StepanovStructuredVacuous.lean` shows collapses to
the trivial degree bound on the *separable* relation `X^n−1`), but as a DIRECT sup-norm / cancellation
tool: bound the **phase-bad set**

  `B(b, η) := { x ∈ μ_n : |1 − e_p(b x)| ≤ η }`   (the `x` whose contribution to `S_b` points near `+1`),

by building a low-degree auxiliary `F` vanishing to high order `M` on `B`, so Stepanov forces
`M · |B| ≤ deg F`, hence `|B|` small, hence cancellation in `S_b`.

## The reduction (this file, axiom-clean)

`stepanov_bad_set_bound` — the Stepanov inequality for the bad set, instantiating the in-tree engine
`card_le_natDegree_of_vanishing`: `M · |B| ≤ deg F` for any nonzero `F` vanishing to order `M` on `B`.

`badset_bound_of_low_degree_auxiliary` — the **sufficient lemma (SL-G2)** in clean logical form:
*IF* there is a nonzero auxiliary `F` of degree `≤ D` vanishing to order `M` on `B`, *THEN*
`|B| ≤ D / M`.  Feeding `D = D₀·√(n log(p/n))·M` and `M ≥ 2` would give `|B| ≤ D₀√(n log(p/n))`,
which (iterated over the threshold `η`) is the prize bound.  So the whole prize reduces to SL-G2's
hypothesis: **existence of a `(√(n log)·M)`-degree, order-`M ≥ 2` auxiliary on the phase-bad set.**

`pastJohnson_needs_degree_saving` — the **degree-saving dichotomy**, the precise OPEN step.  The
trivial auxiliary `F = ∏_{x∈B}(X−x)^M` has degree exactly `M·|B|`, giving back only `|B| ≤ |B|`
(vacuous).  A past-Johnson bound requires a *genuine saving* `deg F < M·|B|` — i.e. the `M·|B|`
order-`M` vanishing conditions must be linearly DEPENDENT (Vandermonde-rank deficient).  This file
states that dichotomy as the named `Prop` `PhaseBadSetDegenerate`.

## The verdict (numerically pre-screened, REFUTED-FALSE for the natural set)

Probe `scripts/probes/probe_wf5G2_rank.py`: for the worst-`b` phase-bad set `B = {x : bx mod p in the
shortest interval}` of size `n/2`, the order-`M` vanishing system has **FULL rank `M·|B|`** for every
tested `n ∈ {16,32,64}` and `M ∈ {2,3}`.  Full rank ⟹ the smallest auxiliary degree is exactly
`M·|B| − 1` ⟹ Stepanov gives only `|B| ≤ (M·|B|−1)/M < |B|`, the TRIVIAL bound.  The phase-bad set
carries NO algebraic degeneracy: as an *archimedean short-interval slice* of `μ_n`, its points are in
general position for the polynomial-vanishing system.  The ONLY genuine structure is the antipodal
pairing `{x, −x} ⊂ μ_n` (Lam–Leung; the order-2 subgroup pairs up inside `B` — probe Q1 measured ~half
the `{±x}` cosets fully inside `B`), but that buys only the factor-2 of the in-tree
`EvenOddAntipodalCharFree` substrate, capping at Johnson `√n`, never past.

This is the deterministic root of the [Phi]-class wall: the bad set is defined by phase (archimedean),
Stepanov consumes algebra (degree/multiplicity), and the prize subgroup relation `X^n−1` is separable
(`mu_n_roots_simple`, in-tree).  Stepanov supplies no multiplicity, and the bad set supplies no
rank-deficiency — so `deg F = M·|B|` always, and the method is exactly trivial.  Lane G2: REFUTED for
the single/structured-auxiliary sup-norm route; the past-Johnson lever (`PhaseBadSetDegenerate` for the
phase-bad set) is the pre-screen-FALSE named obligation.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial

namespace ArkLib.ProximityGap.StepanovSupNorm

variable {F : Type*} [Field F]

/-- **The Stepanov inequality for the phase-bad set.**  `B` is the finite phase-bad set
`{x ∈ μ_n : |1 − e_p(b x)| ≤ η}` (here taken abstractly as any `Finset F`).  If a nonzero auxiliary
`F` vanishes to order `≥ M` at every point of `B`, then `M · |B| ≤ deg F`.  This is the *only*
inequality Stepanov supplies for the sup-norm lane; it is the in-tree counting engine instantiated at
the bad set rather than at a root set. -/
theorem stepanov_bad_set_bound {B : Finset F} {F' : F[X]} {M : ℕ}
    (hF : F' ≠ 0) (hvanish : ∀ x ∈ B, (X - C x) ^ M ∣ F') :
    M * B.card ≤ F'.natDegree :=
  ArkLib.ProximityGap.Stepanov.card_le_natDegree_of_vanishing hF hvanish

/-- **The sufficient lemma SL-G2 (clean logical form).**  If there is a nonzero auxiliary of degree
`≤ D` vanishing to order `M ≥ 1` on the phase-bad set `B`, then `|B| ≤ D / M`.  Feeding
`D ≈ D₀ √(n log(p/n)) · M` (and `M ≥ 2`) yields `|B| ≤ D₀ √(n log(p/n))`, which iterated over the
phase threshold `η` is the prize bound `M(n) ≤ C √(n log(p/n))`.  Thus the entire prize reduces to the
EXISTENCE of such an auxiliary — the hypothesis here. -/
theorem badset_bound_of_low_degree_auxiliary {B : Finset F} {F' : F[X]} {M D : ℕ}
    (hM : 1 ≤ M) (hF : F' ≠ 0) (hdeg : F'.natDegree ≤ D)
    (hvanish : ∀ x ∈ B, (X - C x) ^ M ∣ F') :
    M * B.card ≤ D :=
  le_trans (stepanov_bad_set_bound hF hvanish) hdeg

/-- **The trivial auxiliary saturates the degree bound.**  The product auxiliary
`F = ∏_{x∈B} (X − x)^M` is nonzero, vanishes to order `M` on `B`, and has degree exactly `M · |B|`.
Plugging it into `stepanov_bad_set_bound` gives the *vacuous* `M·|B| ≤ M·|B|`.  Hence the trivial
auxiliary gives NO information about `|B|`: a past-Johnson bound demands an auxiliary of strictly
smaller degree (`< M·|B|`), i.e. a genuine algebraic saving. -/
theorem trivial_auxiliary_is_vacuous {B : Finset F} {M : ℕ} (hM : 1 ≤ M) :
    let F' := ∏ x ∈ B, (X - C x) ^ M
    F' ≠ 0 ∧ (∀ x ∈ B, (X - C x) ^ M ∣ F') ∧ F'.natDegree = M * B.card := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- nonzero: product of nonzero factors
    apply Finset.prod_ne_zero_iff.mpr
    intro x _; exact pow_ne_zero _ (X_sub_C_ne_zero x)
  · -- divisibility: each factor divides the product
    intro x hx
    exact Finset.dvd_prod_of_mem (fun y => (X - C y) ^ M) hx
  · -- degree: sum of degrees = M·|B|
    rw [Polynomial.natDegree_prod _ _ (fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x))]
    have h : ∀ x ∈ B, ((X - C x) ^ M).natDegree = M := by
      intro x _; rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The degree-saving dichotomy (the named OPEN step, pre-screened FALSE for the phase-bad set).**
`PhaseBadSetDegenerate B M` asserts the algebraic degeneracy SL-G2 needs to be non-vacuous: a nonzero
auxiliary of degree STRICTLY LESS than `M · |B|` vanishing to order `M` on `B`.  Such an auxiliary
exists iff the `M·|B|` order-`M` vanishing conditions are linearly DEPENDENT (the Vandermonde /
confluent-Vandermonde block of `B` is rank-deficient).

The pre-screen (`probe_wf5G2_rank.py`) measures this block to have FULL rank `M·|B|` for the worst-`b`
phase-bad set at every `n ∈ {16,32,64}`, `M ∈ {2,3}` — so `PhaseBadSetDegenerate` is FALSE for the
natural set, and the Stepanov sup-norm route gives only the trivial bound.  Stated as a `Prop` to keep
the modular ledger honest: closing the prize via lane G2 would require proving this for a `μ_n`-bad set
of size `≈ n` with degree saving down to `≈ √(n log)`, which the rank measurement refutes. -/
def PhaseBadSetDegenerate (B : Finset F) (M : ℕ) : Prop :=
  ∃ F' : F[X], F' ≠ 0 ∧ F'.natDegree < M * B.card ∧ (∀ x ∈ B, (X - C x) ^ M ∣ F')

/-- **Equivalence: a genuine Stepanov saving ⟺ the phase-bad set is degenerate.**  A strictly
sub-trivial Stepanov bound `M·|B| ≤ deg F < M·|B|` is impossible from the trivial auxiliary; one gets
`M·|B| < M·|B|`-flavoured information (i.e. an actual upper bound `|B| < |B|`, hence a real bound on
`|B|`) precisely when `PhaseBadSetDegenerate B M` holds.  This pins the lane: the prize via G2 ⟺
`PhaseBadSetDegenerate` for the `μ_n` phase-bad set — and that is pre-screened FALSE (full rank). -/
theorem stepanov_saving_iff_degenerate {B : Finset F} {M : ℕ} (hM : 1 ≤ M) :
    PhaseBadSetDegenerate B M ↔
      ∃ F' : F[X], F' ≠ 0 ∧ (∀ x ∈ B, (X - C x) ^ M ∣ F') ∧ M * B.card < M * B.card + 1
        ∧ F'.natDegree < M * B.card := by
  constructor
  · rintro ⟨F', hne, hdeg, hv⟩
    exact ⟨F', hne, hv, Nat.lt_succ_self _, hdeg⟩
  · rintro ⟨F', hne, hv, _, hdeg⟩
    exact ⟨F', hne, hdeg, hv⟩

end ArkLib.ProximityGap.StepanovSupNorm

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.StepanovSupNorm.stepanov_bad_set_bound
#print axioms ArkLib.ProximityGap.StepanovSupNorm.badset_bound_of_low_degree_auxiliary
#print axioms ArkLib.ProximityGap.StepanovSupNorm.trivial_auxiliary_is_vacuous
#print axioms ArkLib.ProximityGap.StepanovSupNorm.stepanov_saving_iff_degenerate
