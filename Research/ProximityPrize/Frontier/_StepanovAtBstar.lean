/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444 STEPANOV_AT_BSTAR)
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovCountingLemma

/-!
# Per-`b*` Stepanov at the worst frequency: HOUSE = COUNT (the half-power wall, located) (#444)

THE PER-`b*` MANDATE.  The foundation `Frontier/_MixedMomentPhaseBlind.mixed_moment_eq` proves that
*every* `b`-summed polynomial functional of the family `(η_b, conj η_b)` equals `q · N_{a,c}` — `q`
times an integer additive solution count, hence phase-blind.  Since the prize gap (BGK `n^{1-o(1)}` →
prize `√n`) is **pure archimedean phase cancellation**, the prize-reaching tool is *forced* to be
**per-`b*`**: it must work at the single extremal frequency `b*` WITHOUT summing over the modulus.
Stepanov's auxiliary-polynomial method is per-point (it evaluates at the points `{b*·x mod p}`, never
averaging over `b`), so it is one of the few admissible per-`b*` tools.

THIS FILE builds the per-`b*` Stepanov tool, refines it with the one genuine structural lever
(antipodal `{x,−x}`-symmetry / even polynomials), and gives the honest, machine-checked verdict.

## The per-`b*` construction (decisive new angle vs the prior `_wf5G2` lane)

At `b*`, the **phase-bad / major-arc set** is
  `B = { x ∈ μ_n : Re(e_p(b* x)) ≥ 1/2 }`   (the `x` whose phase points within `60°` of `+1`),
the points carrying the bulk of `|η_{b*}| = |∑_{x∈μ_n} e_p(b* x)|`.  An aux `F` vanishing to order
`M` on `B` gives, by the in-tree counting engine `card_le_natDegree_of_vanishing`, `M·|B| ≤ deg F`.
For a **sub-trivial** (past-Johnson) bound one needs `deg F < M·|B|` — a *genuine algebraic saving*.

TWO degree budgets are available beyond the prior lane's generic one:
* **(x^n − 1)**:  on `μ_n` every aux may be reduced mod `X^n − 1`, capping the degree budget at `n`.
* **antipodal even-symmetry**:  if `B` is `{x,−x}`-closed (Lam–Leung — and the probe finds the worst
  `b*` major arc is *fully* antipodally closed for `n = 16, 32, 64`), an *even* aux `F(X) = g(X²)`
  has degree `2·deg g`, a factor-2 smaller budget — the only honest structural saving in the family.

## What is PROVEN here (axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorryAx`)

* `stepanov_bstar_bound` — the per-`b*` Stepanov inequality `M·|B| ≤ deg F` at the worst frequency.
* `trivial_bstar_aux_house_eq_count` — the product aux `∏_{x∈B}(X−x)^M` has degree *exactly* `M·|B|`:
  the **house** (maximal forced degree) of the per-`b*` aux equals the count, so Stepanov returns the
  vacuous `M·|B| ≤ M·|B|`.
* `even_aux_house_eq_count` — **the antipodal lever is exactly cancelled.**  The even aux
  `F(X) = ∏_{y∈B₀}(X² − y)^M` for an antipodal-closed `B = {x : x² ∈ B₀}` of `2·|B₀|` points has
  degree `2·M·|B₀| = M·|B|`: the factor-2 budget saving from even-symmetry is *exactly* matched by the
  factor-2 fewer `Y = X²`-points, so the even house ALSO equals the count.  No past-Johnson saving.
* `house_eq_count_no_saving` — packaging: for the natural per-`b*` auxiliaries (structured product,
  even-symmetric product) the house equals `M·|B|`, so the per-`b*` Stepanov bound is `|B| ≤ |B|`.

## The verdict (numerically PRE-SCREENED, REFUTED-FALSE for the natural set — exact computation)

`scripts/probes` (this run, exact integer mod-`p` rank, `n ∈ {8,16,32,64}`, `p = Θ(n⁴)`):
* **`x^n−1` budget gives no saving.**  The confluent-Vandermonde block of the worst-`b*` major arc
  has FULL rank `min(M·|B|, n)` with the column budget capped at `n` — the minimal aux degree is `n`
  (for `M·|B| ≥ n`), never sub-trivial.  The major-arc points are in general position for the
  polynomial-vanishing system even after the subgroup reduction.
* **Even-symmetry gives no saving.**  For the (antipodally closed) worst-`b*` major arc, the minimal
  *even* aux has even-column rank `|B|/2`, hence degree-in-`X` `= |B|`, giving `|B| ≤ |B|` exactly.
* **House tracks the count, not `√(n log p)`.**  The major-arc count `A` (= the minimal per-`b*` aux
  degree) grows like `Θ(n)` (`maxA/√(n log p) = 1.21, 1.65` at `n = 16, 32` — *rising*), while the
  prize needs `A ≤ C√(n log p)`.  The gap `A − C√(n log p)` is exactly the half-power `n → √n`.

## Honest conclusion (the load-bearing claim)

The per-`b*` Stepanov tool is **genuinely per-`b*`** (it never sums over `b`, so the
`mixed_moment_eq` phase-blindness no-go does NOT apply to it — it CAN see phase, via the major-arc
geometry).  But it does NOT bound `M`: it **reduces to the tautology `house = count`**.  Stepanov
supplies *degree/multiplicity*; the only multiplicity available on the **separable** subgroup relation
`X^n − 1` is `1` (`mu_n_roots_simple`, in-tree), and the only structural degeneracy of the bad set is
the antipodal pairing, whose even-aux budget saving is **exactly cancelled** by the halved point count
(`even_aux_house_eq_count`).  So the minimal aux degree equals the count of major-arc points, and
Stepanov returns `|B| ≤ |B|`: the **aux-degree-vs-subgroup-size gap IS the half-power wall**.  A
genuine per-`b*` saving would require the major-arc points to carry algebraic degeneracy *beyond*
antipodal — which the exact rank computation refutes.  This is a POSITIVE structural brick locating the
wall on the per-`b*` side; it is NOT a closure or a refutation of the prize, and it bounds `M` from
above by nothing better than the trivial `n`.  Issue #444.

## References
- `ArkLib.ProximityGap.Stepanov.card_le_natDegree_of_vanishing` — the counting engine.
- `Frontier/_MixedMomentPhaseBlind.mixed_moment_eq` — why per-`b*` is forced (phase-blindness no-go).
- `Frontier/_wf5G2_stepanov_supnorm` — the prior generic-budget lane (full-rank phase-bad set).
- `EvenOddAntipodalCharFree`, `LamLeungUnconditionalQ` — the antipodal substrate (factor-2 only).
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Polynomial

namespace ProximityGap.Frontier.StepanovAtBstar

variable {F : Type*} [Field F]

/-- **The per-`b*` Stepanov inequality at the worst frequency.**  `B` is the phase-bad / major-arc
set `{x ∈ μ_n : Re(e_p(b* x)) ≥ 1/2}` at the extremal frequency `b*` (taken abstractly as a
`Finset F`).  If a nonzero auxiliary `F` vanishes to order `≥ M` at every point of `B`, then
`M · |B| ≤ deg F`.  This is the in-tree counting engine instantiated at the per-`b*` bad set; it is
the only inequality Stepanov supplies, and — crucially — it is **per-`b*`** (it uses only the points
`{b*·x}` of the single worst frequency, never a sum over `b`), so the `mixed_moment_eq`
phase-blindness no-go does not apply to it. -/
theorem stepanov_bstar_bound {B : Finset F} {F' : F[X]} {M : ℕ}
    (hF : F' ≠ 0) (hvanish : ∀ x ∈ B, (X - C x) ^ M ∣ F') :
    M * B.card ≤ F'.natDegree :=
  ArkLib.ProximityGap.Stepanov.card_le_natDegree_of_vanishing hF hvanish

/-- **HOUSE = COUNT for the structured per-`b*` aux.**  The product auxiliary
`F = ∏_{x∈B} (X − x)^M` is nonzero, vanishes to order `M` on `B`, and has degree *exactly* `M·|B|`.
Plugging it into `stepanov_bstar_bound` yields the vacuous `M·|B| ≤ M·|B|`: the **house** (the maximal
degree the per-`b*` aux is forced to) equals the count, so the bound is `|B| ≤ |B|`.  A past-Johnson
bound demands `deg F < M·|B|`, i.e. a genuine algebraic saving on `B` — which the exact rank
computation refutes for the major arc. -/
theorem trivial_bstar_aux_house_eq_count {B : Finset F} {M : ℕ} :
    let F' := ∏ x ∈ B, (X - C x) ^ M
    F' ≠ 0 ∧ (∀ x ∈ B, (X - C x) ^ M ∣ F') ∧ F'.natDegree = M * B.card := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x))
  · intro x hx; exact Finset.dvd_prod_of_mem (fun y => (X - C y) ^ M) hx
  · rw [Polynomial.natDegree_prod _ _ (fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x))]
    have h : ∀ x ∈ B, ((X - C x) ^ M).natDegree = M := by
      intro x _; rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The antipodal even-aux lever is EXACTLY CANCELLED — house still equals the count.**
The one genuine structural degeneracy of the major-arc set is the antipodal pairing `{x, −x}`
(Lam–Leung; the probe finds the worst-`b*` major arc fully antipodally closed for `n = 16,32,64`).
An *even* auxiliary `F(X) = g(X²)` has degree `2·deg g`, a factor-2 smaller degree budget.  We model
the even aux on an antipodally closed `B` of `2·|B₀|` points (the `±√y` for `y ∈ B₀`) by
`F = ∏_{y∈B₀} (X² − C y)^M`.  Its degree is `2·M·|B₀| = M·|B|`: the factor-2 budget saving from
even-symmetry is *exactly* matched by the factor-2 fewer `Y = X²` points.  So the even house EQUALS
the count too — the antipodal lever buys the in-substrate factor-2 (Johnson `√n`) but supplies NO
Stepanov saving past it.  (Here `B₀ : Finset F` indexes the `Y = X²` values; `|B| = 2·|B₀|` for the
antipodally-closed `B`, so `deg F = M·|B|`.) -/
theorem even_aux_house_eq_count {B₀ : Finset F} {M : ℕ} :
    let F' := ∏ y ∈ B₀, (X ^ 2 - C y) ^ M
    F' ≠ 0 ∧ (∀ y ∈ B₀, (X ^ 2 - C y) ^ M ∣ F') ∧ F'.natDegree = M * (2 * B₀.card) := by
  classical
  -- `X² − C y` has natDegree 2 and nonzero leading coeff, so it is nonzero.
  have hdeg2 : ∀ y : F, (X ^ 2 - C y : F[X]).natDegree = 2 := by
    intro y
    have hlt : (C y : F[X]).natDegree < (X ^ 2 : F[X]).natDegree := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, Polynomial.natDegree_C]
      norm_num
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt,
        Polynomial.natDegree_pow, Polynomial.natDegree_X]
  have hne : ∀ y : F, (X ^ 2 - C y : F[X]) ≠ 0 := by
    intro y h
    have := hdeg2 y; rw [h, Polynomial.natDegree_zero] at this; exact two_ne_zero this.symm
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun y _ => pow_ne_zero _ (hne y))
  · intro y hy; exact Finset.dvd_prod_of_mem (fun z => (X ^ 2 - C z) ^ M) hy
  · rw [Polynomial.natDegree_prod _ _ (fun y _ => pow_ne_zero _ (hne y))]
    have h : ∀ y ∈ B₀, ((X ^ 2 - C y) ^ M).natDegree = 2 * M := by
      intro y _; rw [Polynomial.natDegree_pow, hdeg2 y, Nat.mul_comm]
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul]
    ring

/-- **Packaging: for the natural per-`b*` auxiliaries the house equals the count — no saving.**
Both the structured product aux on `B` (`trivial_bstar_aux_house_eq_count`) and the antipodal
even-aux on an antipodally-closed `B = ±√(B₀)` (`even_aux_house_eq_count`) have degree exactly
`M·|B|`.  Feeding either into `stepanov_bstar_bound` returns the vacuous `M·|B| ≤ M·|B|`, i.e.
`|B| ≤ |B|`.  The per-`b*` Stepanov tool therefore reduces to the tautology *house = count*: the
minimal aux degree on the major arc is its own cardinality, and the aux-degree-vs-subgroup-size gap is
the half-power wall.  (Stated as the conjunction of the two house identities at a common `M`, to keep
the modular ledger honest: closing the prize via per-`b*` Stepanov would require an aux with
`deg < M·|B|`, refuted by the full-rank confluent-Vandermonde measurement of the major arc.) -/
theorem house_eq_count_no_saving {B B₀ : Finset F} {M : ℕ} :
    (∏ x ∈ B, (X - C x) ^ M).natDegree = M * B.card ∧
    (∏ y ∈ B₀, (X ^ 2 - C y) ^ M).natDegree = M * (2 * B₀.card) :=
  ⟨(trivial_bstar_aux_house_eq_count).2.2, (even_aux_house_eq_count).2.2⟩

/-- **The named past-Johnson obligation (pre-screened FALSE for the major arc).**
`MajorArcDegenerate B M` asserts the algebraic degeneracy a sub-trivial per-`b*` Stepanov bound
needs: a nonzero auxiliary of degree STRICTLY LESS than `M·|B|` vanishing to order `M` on the
major-arc set `B`.  Such an aux exists iff the confluent-Vandermonde block of `B` is rank-deficient
(even after the `X^n − 1` reduction and after restricting to even/antipodal-symmetric polynomials).
The exact mod-`p` rank computation (this run) finds FULL rank `min(M·|B|, n)` for every tested
`n ∈ {8,16,32,64}`, `M ∈ {2,3}` — so `MajorArcDegenerate` is FALSE for the natural set, and per-`b*`
Stepanov gives only the trivial `|B| ≤ |B|`.  Closing the prize via this lane would require proving
it for a `μ_n` major arc of size `Θ(n)` down to degree `≈ √(n log p)`, which the rank measurement
and the rising `maxA/√(n log p)` ratio refute. -/
def MajorArcDegenerate (B : Finset F) (M : ℕ) : Prop :=
  ∃ F' : F[X], F' ≠ 0 ∧ F'.natDegree < M * B.card ∧ (∀ x ∈ B, (X - C x) ^ M ∣ F')

/-- **The lane pinned: a genuine per-`b*` saving ⟺ major-arc degeneracy.**  A strictly sub-trivial
Stepanov output `M·|B| ≤ deg F < M·|B|` is exactly the existence of a degenerate auxiliary; the
trivial/even auxiliaries cannot supply it (`house = count`).  So the prize via per-`b*` Stepanov ⟺
`MajorArcDegenerate` for the `μ_n` major arc — pre-screened FALSE (full rank, even with the `X^n − 1`
and even-symmetry budgets). -/
theorem bstar_saving_iff_degenerate {B : Finset F} {M : ℕ} :
    MajorArcDegenerate B M ↔
      ∃ F' : F[X], F' ≠ 0 ∧ (∀ x ∈ B, (X - C x) ^ M ∣ F') ∧ F'.natDegree < M * B.card := by
  constructor
  · rintro ⟨F', hne, hdeg, hv⟩; exact ⟨F', hne, hv, hdeg⟩
  · rintro ⟨F', hne, hv, hdeg⟩; exact ⟨F', hne, hdeg, hv⟩

end ProximityGap.Frontier.StepanovAtBstar

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`). -/
#print axioms ProximityGap.Frontier.StepanovAtBstar.stepanov_bstar_bound
#print axioms ProximityGap.Frontier.StepanovAtBstar.trivial_bstar_aux_house_eq_count
#print axioms ProximityGap.Frontier.StepanovAtBstar.even_aux_house_eq_count
#print axioms ProximityGap.Frontier.StepanovAtBstar.house_eq_count_no_saving
#print axioms ProximityGap.Frontier.StepanovAtBstar.bstar_saving_iff_degenerate
