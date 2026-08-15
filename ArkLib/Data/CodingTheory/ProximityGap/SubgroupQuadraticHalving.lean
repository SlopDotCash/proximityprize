/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false

/-!
# Round 9 (Issue #232, ABF26) — the EXACT 2-to-1 HALVING of the quadratic subgroup Gauss sum:
# the quadratic subgroup character factor is *structurally* twice a LINEAR one at half size.

ATTACK TARGET #9 (off-diagonal sign/symmetry structural bounds). Over the smooth `2^k`-subgroup
`μ_{2m} = nthRootsFinset (2m) 1` (`m = 2^{k-1}`) the per-element character factor in the prize's
`(∑x, ∑x²)` moment-collision tower carries the value `ψ(b·x²)`, which depends on `x` *only through*
`x²`. Since `μ_{2m}` is closed under negation (`−1 ∈ μ_{2m}` because `(−1)^{2m}=1`) and squaring is
**exactly 2-to-1** onto `μ_{2m}² = μ_m` (fleet's `image_sq_eq_half`), the quadratic subgroup factor
collapses *exactly* — with **no Weil / RH-for-curves input** — onto the LINEAR subgroup factor on the
half-size subgroup `μ_m`:

  `∑_{x∈μ_{2m}} ψ(b·x²)  =  2 · ∑_{y∈μ_m} ψ(b·y)`     (`gaussSum_sq_subgroup_eq_two_mul`),

hence the per-frequency norm identity

  `‖∑_{x∈μ_{2m}} ψ(b·x²)‖  =  2 · ‖∑_{y∈μ_m} ψ(b·y)‖`     (`norm_gaussSum_sq_subgroup`)

and the structural second-moment identity over all `q` frequencies

  `∑_b ‖∑_{x∈μ_{2m}} ψ(b·x²)‖²  =  4 · ∑_b ‖∑_{y∈μ_m} ψ(b·y)‖²`     (`secondMoment_gaussSum_sq_eq`).

This is the **structural (non-Weil) off-diagonal bound** that attack target #9 calls for: the genuinely
quadratic subgroup factor `ζ_b = ∑_{x∈μ_{2m}} ψ(b·x²)`, the single-coordinate object inside the
prize-deciding mixed statistic, is *not* an independent quadratic exponential sum — it is **literally
twice** the LINEAR subgroup Gauss sum `η_b = ∑_{y∈μ_m} ψ(b·y)` of the next subgroup in the tower. The
linear subgroup Gauss sum is fully under elementary control (`SubgroupGaussSumSecondMoment.lean`:
`∑_b ‖η_b‖² = q·|μ_m|`, pure Parseval); the halving transports that control to the quadratic factor at
a fixed factor-`4` cost. In particular the quadratic factor satisfies the *same* L²-average ceiling
`‖ζ_b‖²` averages to `4|μ_m|²/q = |μ_{2m}|²/q` — no per-frequency `√q`-strength is claimed, and the
deep-interior worst case (which would need Weil) is untouched. The 2-power multiplicative structure of
`x ↦ x²` does the entire job structurally.

## What is genuinely new here vs. the fleet

`SubgroupSquaresHalvingRecursion.image_sq_eq_half` proves the **set** identity `μ_{2m}² = μ_m`;
`SubgroupQuadraticSecondMoment` proves the *unweighted square-collision* second moment. Neither
supplies the **weighted character-sum** halving `∑ ψ(b·x²) = 2∑ ψ(b·y)` that turns the quadratic
subgroup factor into a linear one term-by-term. That weighted 2-to-1 collapse — the exact fiber-sum
exploiting that each square has exactly the two preimages `{w, −w}` of equal weight — is the content
of this file and the precise structural off-diagonal reduction of attack target #9.

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Structural; does **not** pin
`δ*` and does **not** advance the open Weil core (`advancesOpenCore = false`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
- A. Weil, *On some exponential sums*, PNAS 1948 (the per-frequency `√q` bound, NOT used here).
-/

open Finset Polynomial BigOperators

namespace ArkLib.ProximityGap.Round9SubgroupQuadraticHalving

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. Squaring maps `μ_{2m}` into `μ_m` (the forward/`maps_to` direction). -/

omit [Fintype F] [DecidableEq F] in
/-- **Squaring lands in the half-order subgroup.** If `x ∈ μ_{2m}` (so `x^{2m}=1`) then
`x² ∈ μ_m`, because `(x²)^m = x^{2m} = 1`. -/
theorem sq_mem_half {m : ℕ} {x : F} (hx : x ∈ nthRootsFinset (2 * m) (1 : F)) :
    x ^ 2 ∈ nthRootsFinset m (1 : F) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp only [Nat.mul_zero, nthRootsFinset_zero, Finset.notMem_empty] at hx
  · rw [mem_nthRootsFinset (by omega : 0 < 2 * m)] at hx
    rw [mem_nthRootsFinset hm]
    calc (x ^ 2) ^ m = x ^ (2 * m) := by rw [← pow_mul, mul_comm]
      _ = 1 := hx

/-! ## 2. The keystone: the weighted 2-to-1 halving of any sum precomposed with squaring. -/

omit [Fintype F] in
/-- **Weighted 2-to-1 halving (keystone).** For *any* `AddCommMonoid`-valued `f`, over the smooth
even-order subgroup `μ_{2m}` (`m ≥ 1`, char ≠ 2, primitive `2m`-th root `ζ`),

  `∑_{x∈μ_{2m}} f(x²)  =  2 • ∑_{y∈μ_m} f(y)`.

Proof: regroup the LHS by the fibers of `x ↦ x²` (which maps `μ_{2m}` into `μ_m` by `sq_mem_half`).
For each `y ∈ μ_m`, surjectivity of squaring (`ζ²` is a primitive `m`-th root, so `y = (ζ^j)²`) gives a
representative `w = ζ^j ∈ μ_{2m}` with `w² = y`; the field factorization `(x−w)(x+w) = x²−y` forces the
fiber to be exactly `{w, −w}`, which has **two** elements since `w ≠ 0` (a root of unity) and `char ≠ 2`
give `w ≠ −w`. Both `w, −w` carry the **same** value `f(w²) = f((−w)²) = f(y)`, so each fiber
contributes `2 • f(y)`. Summing over `y ∈ μ_m` yields the claim. No Weil input. -/
theorem sum_comp_sq_eq_two_smul {M : Type*} [AddCommMonoid M] {m : ℕ} (hm : 0 < m)
    (h2 : (2 : F) ≠ 0) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 * m)) (f : F → M) :
    ∑ x ∈ nthRootsFinset (2 * m) (1 : F), f (x ^ 2)
      = 2 • ∑ y ∈ nthRootsFinset m (1 : F), f y := by
  set G := nthRootsFinset (2 * m) (1 : F) with hG
  set H := nthRootsFinset m (1 : F) with hH
  -- regroup by fibers of squaring (maps `G → H`)
  have hmaps : ∀ x ∈ G, x ^ 2 ∈ H := fun x hx => sq_mem_half hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => f (x ^ 2)), Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro y hy
  -- `ζ²` is a primitive `m`-th root; surjectivity gives a square-root representative `w ∈ G`.
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) m := hζ.pow (by omega) (by rw [mul_comm])
  haveI : NeZero m := ⟨by omega⟩
  rw [mem_nthRootsFinset hm] at hy
  obtain ⟨j, _, hj⟩ := hζ2.eq_pow_of_pow_eq_one hy
  set w := ζ ^ j with hw
  have hwG : w ∈ G := by
    rw [hG, mem_nthRootsFinset (by omega : 0 < 2 * m), hw, ← pow_mul, mul_comm j (2 * m), pow_mul,
      hζ.pow_eq_one, one_pow]
  have hwy : w ^ 2 = y := by rw [hw, ← pow_mul, mul_comm j 2, pow_mul, hj]
  have hw0 : w ≠ 0 := by
    intro h; rw [hG, mem_nthRootsFinset (by omega : 0 < 2 * m)] at hwG
    rw [h, zero_pow (by omega : 2 * m ≠ 0)] at hwG; exact zero_ne_one hwG
  have hnwG : -w ∈ G := by
    rw [hG, mem_nthRootsFinset (by omega : 0 < 2 * m)] at *
    rw [neg_pow]; have : Even (2 * m) := ⟨m, by ring⟩
    rw [this.neg_one_pow, one_mul, hwG]
  have hwnw : w ≠ -w := by
    intro h; apply hw0
    have hadd : w + w = 0 := by nth_rewrite 2 [h]; ring
    have h2w : (2 : F) * w = 0 := by linear_combination hadd
    rcases mul_eq_zero.1 h2w with h' | h'
    · exact absurd h' h2
    · exact h'
  -- the fiber is exactly `{w, −w}` (field: `x² = y ⟹ (x−w)(x+w)=0 ⟹ x = ±w`).
  have hfiber : G.filter (fun x => x ^ 2 = y) = {w, -w} := by
    ext x
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨_, hxy⟩
      have hfac : (x - w) * (x + w) = 0 := by ring_nf; linear_combination hxy - hwy
      rcases mul_eq_zero.1 hfac with h' | h'
      · left; exact sub_eq_zero.1 h'
      · right; exact eq_neg_of_add_eq_zero_left h'
    · rintro (rfl | rfl)
      · exact ⟨hwG, hwy⟩
      · refine ⟨hnwG, ?_⟩; rw [neg_pow]; simpa using hwy
  rw [hfiber, Finset.sum_insert (by simp [hwnw]), Finset.sum_singleton]
  have e1 : f (w ^ 2) = f y := by rw [hwy]
  have e2 : f ((-w) ^ 2) = f y := by
    rw [neg_pow]; simp only [even_two, Even.neg_one_pow, one_mul]; rw [hwy]
  rw [e1, e2, two_smul]

/-! ## 3. The quadratic / linear subgroup Gauss sums and the halving they satisfy. -/

/-- The **quadratic** subgroup Gauss sum on `μ_{2m}` at frequency `b`: `ζ_b = ∑_{x∈μ_{2m}} ψ(b·x²)`.
The single-coordinate quadratic factor in the prize's `(∑x, ∑x²)` statistic. -/
noncomputable def gaussSumSq (ψ : AddChar F ℂ) (m : ℕ) (b : F) : ℂ :=
  ∑ x ∈ nthRootsFinset (2 * m) (1 : F), ψ (b * x ^ 2)

/-- The **linear** subgroup Gauss sum on the half-size subgroup `μ_m` at frequency `b`:
`η_b = ∑_{y∈μ_m} ψ(b·y)`. Fully controlled elementarily (`∑_b ‖η_b‖² = q·|μ_m|`, pure Parseval). -/
noncomputable def gaussSumLin (ψ : AddChar F ℂ) (m : ℕ) (b : F) : ℂ :=
  ∑ y ∈ nthRootsFinset m (1 : F), ψ (b * y)

omit [Fintype F] in
/-- **The quadratic subgroup Gauss sum is exactly twice the linear one at half size.**

  `∑_{x∈μ_{2m}} ψ(b·x²)  =  2 · ∑_{y∈μ_m} ψ(b·y)`.

Immediate specialization of `sum_comp_sq_eq_two_smul` at `f(u) = ψ(b·u)`. This is the precise
*structural* (non-Weil) collapse of the quadratic subgroup factor onto a linear one: attack target #9. -/
theorem gaussSum_sq_subgroup_eq_two_mul (ψ : AddChar F ℂ) {m : ℕ} (hm : 0 < m) (h2 : (2 : F) ≠ 0)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 * m)) (b : F) :
    gaussSumSq ψ m b = 2 * gaussSumLin ψ m b := by
  unfold gaussSumSq gaussSumLin
  have h := sum_comp_sq_eq_two_smul hm h2 hζ (fun u => ψ (b * u))
  simpa [nsmul_eq_mul] using h

omit [Fintype F] in
/-- **Per-frequency norm halving.** `‖∑_{x∈μ_{2m}} ψ(b·x²)‖ = 2·‖∑_{y∈μ_m} ψ(b·y)‖`. The quadratic
subgroup factor has *exactly* twice the magnitude of the linear factor at half size — for *every*
frequency `b`, with no exception and no Weil bound. So any per-frequency control on the linear factor
transfers verbatim (up to the constant `2`) to the quadratic factor. -/
theorem norm_gaussSum_sq_subgroup (ψ : AddChar F ℂ) {m : ℕ} (hm : 0 < m) (h2 : (2 : F) ≠ 0)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 * m)) (b : F) :
    ‖gaussSumSq ψ m b‖ = 2 * ‖gaussSumLin ψ m b‖ := by
  rw [gaussSum_sq_subgroup_eq_two_mul ψ hm h2 hζ b, norm_mul]; simp

/-- **Structural second-moment identity (off-diagonal transport).**

  `∑_b ‖∑_{x∈μ_{2m}} ψ(b·x²)‖²  =  4 · ∑_b ‖∑_{y∈μ_m} ψ(b·y)‖²`.

The full L²-energy of the quadratic subgroup factor over all `q` frequencies is **exactly** `4×` that
of the linear subgroup factor on the half-size subgroup. Since the linear subgroup Gauss sum has the
fully elementary Parseval second moment `∑_b ‖η_b‖² = q·|μ_m|` (no Weil), the quadratic factor
inherits `∑_b ‖ζ_b‖² = 4q·|μ_m| = 2q·|μ_{2m}|` — the average `‖ζ_b‖²` is `2·|μ_{2m}|`, far below the
full-field `q`. This is the exact (non-Weil) structural off-diagonal control of attack target #9; the
per-frequency *worst case* (deep interior) remains Weil-governed and is untouched. -/
theorem secondMoment_gaussSum_sq_eq (ψ : AddChar F ℂ) {m : ℕ} (hm : 0 < m) (h2 : (2 : F) ≠ 0)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 * m)) :
    ∑ b : F, ‖gaussSumSq ψ m b‖ ^ 2 = 4 * ∑ b : F, ‖gaussSumLin ψ m b‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [norm_gaussSum_sq_subgroup ψ hm h2 hζ b]; ring

/-! ## 4. Non-vacuity: the halving is realized over a genuine smooth domain. -/

/-- `5` is prime, so `ZMod 5` is a field hosting a smooth `2²`-subgroup (`2m = 4`, `m = 2`). -/
instance primeFact_SubgroupQuadraticHalving_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Non-vacuity witness.** Over `F = ZMod 5`, `2` is a primitive `4`-th root of unity
(`2¹=2, 2²=4, 2³=3, 2⁴=1`), so `μ_4 = {1,2,3,4}` and `μ_2 = {1,4}` (`4 = −1`). The halving hypotheses
hold non-vacuously: `IsPrimitiveRoot (2:ZMod 5) (2·2)` and `(2:ZMod 5) ≠ 0`, so
`gaussSum_sq_subgroup_eq_two_mul` / `norm_gaussSum_sq_subgroup` / `secondMoment_gaussSum_sq_eq` apply
to a genuine `k = 2` smooth subgroup. -/
theorem nonvacuity_zmod5 :
    IsPrimitiveRoot (2 : ZMod 5) (2 * 2) ∧ (2 : ZMod 5) ≠ 0 := by
  refine ⟨?_, by decide⟩
  have hord : orderOf (2 : ZMod 5) = 2 * 2 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro mm hmm hmm0
    interval_cases mm <;> decide
  rw [IsPrimitiveRoot.iff_orderOf, hord]

/-- **Iterated halving.** For `char ≠ 2`, `m > 0`, and a primitive `(2^j · m)`-th root `ζ`, the
`2^j`-th power map collapses the sum `2^j`-to-1 onto `μ_m`:
`∑_{x∈μ_{2^j·m}} f(x^{2^j}) = 2^j • ∑_{y∈μ_m} f(y)`. Iterating `sum_comp_sq_eq_two_smul` via
`x^{2^{j+1}} = (x²)^{2^j}` and `ζ² ` primitive `(2^j·m)`-th. So every power-of-2 power sum over the
smooth domain reduces to a LINEAR Gauss period over a half-iterated subgroup — relevant to the
`(∑x^{2^j})` coordinates of general-`t` statistics. Axiom-clean, Weil-free. -/
theorem sum_comp_pow_two_iterate {M : Type*} [AddCommMonoid M] (h2 : (2 : F) ≠ 0)
    {m : ℕ} (hm : 0 < m) (f : F → M) :
    ∀ (j : ℕ) {ζ : F}, IsPrimitiveRoot ζ (2 ^ j * m) →
      ∑ x ∈ nthRootsFinset (2 ^ j * m) (1 : F), f (x ^ (2 ^ j))
        = (2 ^ j) • ∑ y ∈ nthRootsFinset m (1 : F), f y := by
  intro j
  induction j with
  | zero =>
    intro ζ hζ
    simp only [pow_zero, one_mul, pow_one, one_smul]
  | succ j ih =>
    intro ζ hζ
    have hsplit : 2 ^ (j + 1) * m = 2 * (2 ^ j * m) := by ring
    -- ζ is a primitive (2 * (2^j m))-th root; ζ² is a primitive (2^j m)-th root
    have hζ' : IsPrimitiveRoot ζ (2 * (2 ^ j * m)) := by rw [← hsplit]; exact hζ
    have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ j * m) :=
      hζ'.pow (by positivity) (by rw [mul_comm])
    -- apply single halving to g(u) = f(u^{2^j})
    have key := sum_comp_sq_eq_two_smul (m := 2 ^ j * m) (by positivity) h2 hζ'
      (fun u => f (u ^ (2 ^ j)))
    -- rewrite the outer index 2^{j+1}m = 2*(2^j m) and the exponent (x²)^{2^j}=x^{2^{j+1}}
    rw [hsplit]
    calc ∑ x ∈ nthRootsFinset (2 * (2 ^ j * m)) (1 : F), f (x ^ (2 ^ (j + 1)))
        = ∑ x ∈ nthRootsFinset (2 * (2 ^ j * m)) (1 : F), f ((x ^ 2) ^ (2 ^ j)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← pow_mul]; congr 1; rw [pow_succ]; ring
      _ = 2 • ∑ y ∈ nthRootsFinset (2 ^ j * m) (1 : F), f (y ^ (2 ^ j)) := key
      _ = 2 • ((2 ^ j) • ∑ y ∈ nthRootsFinset m (1 : F), f y) := by rw [ih hζ2]
      _ = (2 ^ (j + 1)) • ∑ y ∈ nthRootsFinset m (1 : F), f y := by
          rw [smul_smul]; congr 1; rw [pow_succ]; ring

end ArkLib.ProximityGap.Round9SubgroupQuadraticHalving

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.sq_mem_half
#print axioms ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.sum_comp_sq_eq_two_smul
#print axioms ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.gaussSum_sq_subgroup_eq_two_mul
#print axioms ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.norm_gaussSum_sq_subgroup
#print axioms ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.secondMoment_gaussSum_sq_eq
#print axioms ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.nonvacuity_zmod5
#print axioms ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.sum_comp_pow_two_iterate
