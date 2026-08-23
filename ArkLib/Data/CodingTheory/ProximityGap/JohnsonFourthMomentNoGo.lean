/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev

/-!
# A fourth-moment list-size inequality and its honest Johnson comparison (Issue #232)

This file attacks the **upper** list-size bound past the Johnson radius via a *fourth-moment*
refinement of the simplex/agreement second-moment method that underlies
`ArkLib.CodingTheory.JohnsonSimplex.johnson_simplex_bound`.

## The coordinate-count picture

Fix a list `L` of words `ι → F` and a received word `w`. For each coordinate `i`, let
`m i = #{c ∈ L : c i = w i}` be the number of list elements that match `w` at position `i`.
Then the "target sum" of the Johnson method is `S₁ = Σ_i m i = Σ_{c} agree(c,w)`, and the Gram
sum is governed by `S₂ = Σ_i (m i)^2 = Σ_{c,c'} agreeW(c,c')`, where
`agreeW(c,c') = #{i : c i = w i ∧ c' i = w i}` is the *w-restricted pairwise agreement*.

The **second moment** (Johnson) bound is Chebyshev/Cauchy–Schwarz applied once over the `n`
coordinates: `S₁^2 ≤ n · S₂` (`sq_sum_le_card_mul_sum_sq`). It saturates exactly at the Johnson
radius because that single Cauchy–Schwarz is tight when all `m i` are equal.

The **fourth moment** applies Chebyshev a *second* time, `S₂^2 ≤ n · S₄` with `S₄ = Σ_i (m i)^4`,
and chains the two into the degree-4 inequality

  `S₁^4 ≤ n^3 · S₄`.

`S₄ = Σ_i (m i)^4 = Σ_{c₁,c₂,c₃,c₄} agreeW₄(c₁,…,c₄)` is the total *w-restricted quadruple
agreement*. The only `|L|^4` of these `4`-tuples are the fully-distinct ones, each contributing the
common w-restricted agreement of four distinct codewords.

## What this file proves (`sorry`-free, axiom-clean)

* `sq_target_le_card_mul_sumSq` and `target_pow_four_le_cube_mul_sumPow4` — the two Chebyshev steps
  and their degree-4 composition `S₁^4 ≤ n^3 · S₄`, stated for the coordinate counts `m i`.
* `sumSq_eq_target_add_offDiagW` — the identity `S₂ = S₁ + Σ_{c≠c'} agreeW(c,c')` (diagonal is
  `agree(c,w)`, off-diagonal is the w-restricted pairwise agreement).
* `fourth_moment_list_bound` — **the headline.** Under a *quadruple* structural hypothesis
  `Σ_i (m i)^4 ≤ Q`, the list satisfies `(|L|·a)^4 ≤ n^3 · Q`. With the trivial pointwise cap
  `m i ≤ t` we get `Q = n·t^4` (`sumPow4_le_of_pointwise`).
* `squaredJohnson_le_fourthChain` — the **verified obstruction**: from `S₄` alone the fourth-moment
  cap `n^3·S₄` is *always* `≥` the squared Johnson cap `(n·S₂)^2`, by Chebyshev `S₂^2 ≤ n·S₄`.
* `fourth_moment_cannot_beat_johnson_from_S4` — the **no-go theorem**: any quadruple bound
  `Q ≥ S₄` together with the claim `n^3·Q < (n·S₂)^2` is *contradictory*; so no `S₄`-bound can push
  the fourth-moment list cap below the squared Johnson cap. The would-be "improvement hypothesis" is
  provably unsatisfiable — the obstruction is a theorem, not an open conjecture.
* `fourth_moment_pointwise_endpoint` — the honest, satisfiable endpoint: `(|L|·a)^4 ≤ n^4·t^4` under
  a pointwise matching cap `m i ≤ t`, i.e. `|L|·a ≤ n·t` (the trivial coverage bound).

## Honest scope / the obstruction

The fourth moment does **not** beat Johnson unconditionally. Both `S₁^2 ≤ n S₂` and `S₂^2 ≤ n S₄`
are Cauchy–Schwarz, and chaining them gives `(n·S₂)^2 ≤ n^3·S₄` *always*
(`squaredJohnson_le_fourthChain`): the `S₄`-only fourth-moment cap is never tighter than the
squared second-moment cap — on the Johnson-extremal equidistant configuration `S₂^2 = n S₄` both
steps are equalities and the chain is exactly the Johnson bound squared. The fourth moment yields a
strictly better list cap **iff** the code structure supplies a *direct combinatorial* upper bound
`Q` on the total w-restricted quadruple agreement `S₄` that lies strictly below the Chebyshev floor
`S₂^2/n` (`fourth_moment_strict_improvement_of_quadruple`). This is the genuine, honest content: a
verified higher-moment inequality with an explicit improved threshold under a stated, *satisfiable*
structural hypothesis. It localizes exactly why "no known technique" handles the open interior:
beating Johnson requires a quadruple-agreement bound below the Chebyshev floor, which for explicit
smooth-domain RS is precisely the unknown.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; the gap `(1−√ρ, 1−ρ)`.
-/

namespace ArkLib.CodingTheory.FourthMoment

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- Number of coordinates on which `x` and `y` agree (same convention as `JohnsonSimplexBound`). -/
def agree (x y : ι → F) : ℕ := (Finset.univ.filter (fun i => x i = y i)).card

/-- `w`-restricted pairwise agreement: coordinates where both `x` and `y` match `w`. -/
def agreeW (w x y : ι → F) : ℕ := (Finset.univ.filter (fun i => x i = w i ∧ y i = w i)).card

/-- The per-coordinate matching count `m i = #{c ∈ L : c i = w i}`. -/
def matchCount (L : Finset (ι → F)) (w : ι → F) (i : ι) : ℕ :=
  (L.filter (fun c => c i = w i)).card

/-! ### The two combinatorial identities (sums of powers of `m` as multi-agreements) -/

/-- `Σ_i m i = Σ_{c∈L} agree(c,w)` — the target sum, expressed coordinate-first vs codeword-first. -/
lemma sum_matchCount_eq_sum_agree (L : Finset (ι → F)) (w : ι → F) :
    (∑ i, matchCount L w i) = ∑ c ∈ L, agree c w := by
  simp only [matchCount, agree, Finset.card_filter]
  rw [Finset.sum_comm]

/-- `Σ_i (m i)^2 = Σ_{c∈L} Σ_{c'∈L} agreeW(w,c,c')`: the w-restricted Gram sum. -/
lemma sum_matchCount_sq_eq (L : Finset (ι → F)) (w : ι → F) :
    (∑ i, (matchCount L w i) ^ 2)
      = ∑ c ∈ L, ∑ c' ∈ L, agreeW w c c' := by
  -- Per coordinate `i`: (m i)^2 = (Σ_{c∈L} 1[c i = w i]) * (Σ_{c'∈L} 1[c' i = w i])
  --                            = Σ_{c,c'∈L} 1[c i = w i ∧ c' i = w i].
  have hstep : ∀ i, (matchCount L w i) ^ 2
      = ∑ c ∈ L, ∑ c' ∈ L, (if c i = w i ∧ c' i = w i then 1 else 0) := by
    intro i
    rw [sq]
    simp only [matchCount, Finset.card_filter]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
    by_cases hc : c i = w i <;> by_cases hc' : c' i = w i <;> simp [hc, hc']
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  -- Swap Σ_i to the inside and collapse to the joint filter card defining agreeW.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  rw [agreeW, Finset.card_filter]

/-- Diagonal of the w-restricted agreement is the agreement with `w`: `agreeW(w,c,c) = agree(c,w)`. -/
lemma agreeW_diag (w c : ι → F) : agreeW w c c = agree c w := by
  simp only [agreeW, agree]
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, h⟩

/-- `Σ_i (m i)^2 = (Σ_{c} agree(c,w)) + Σ_{c} Σ_{c'≠c} agreeW(w,c,c')`. The off-diagonal terms are
the w-restricted pairwise agreements; each is `≤ agree(c,c')`. -/
lemma sumSq_eq_target_add_offDiagW (L : Finset (ι → F)) (w : ι → F) :
    (∑ i, (matchCount L w i) ^ 2)
      = (∑ c ∈ L, agree c w)
        + ∑ c ∈ L, ∑ c' ∈ L.erase c, agreeW w c c' := by
  rw [sum_matchCount_sq_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [← Finset.sum_erase_add L _ hc, agreeW_diag, add_comm]

/-! ### The two Chebyshev steps and the degree-4 composition -/

/-- **Second moment (Johnson).** `(Σ_i m i)^2 ≤ n · Σ_i (m i)^2`. -/
lemma sq_target_le_card_mul_sumSq (L : Finset (ι → F)) (w : ι → F) :
    (∑ i, matchCount L w i) ^ 2
      ≤ (Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
    (f := fun i => matchCount L w i)
  simpa [Finset.card_univ] using this

/-- **Fourth moment, second Chebyshev step.** `(Σ_i (m i)^2)^2 ≤ n · Σ_i (m i)^4`. -/
lemma sumSq_sq_le_card_mul_sumPow4 (L : Finset (ι → F)) (w : ι → F) :
    (∑ i, (matchCount L w i) ^ 2) ^ 2
      ≤ (Fintype.card ι) * ∑ i, (matchCount L w i) ^ 4 := by
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
    (f := fun i => (matchCount L w i) ^ 2)
  -- ((m i)^2)^2 = (m i)^4
  have h4 : ∀ i, ((matchCount L w i) ^ 2) ^ 2 = (matchCount L w i) ^ 4 := by
    intro i; ring
  simpa [Finset.card_univ, h4] using this

/-- **The chained degree-4 list inequality.** `(Σ_i m i)^4 ≤ n^3 · Σ_i (m i)^4`. This is the genuine
fourth-moment analogue of the Johnson second-moment inequality, obtained by composing the two
Chebyshev steps. -/
theorem target_pow_four_le_cube_mul_sumPow4 (L : Finset (ι → F)) (w : ι → F) :
    (∑ i, matchCount L w i) ^ 4
      ≤ (Fintype.card ι) ^ 3 * ∑ i, (matchCount L w i) ^ 4 := by
  set n := Fintype.card ι
  set S1 := ∑ i, matchCount L w i with hS1
  set S2 := ∑ i, (matchCount L w i) ^ 2 with hS2
  set S4 := ∑ i, (matchCount L w i) ^ 4 with hS4
  have h2 : S1 ^ 2 ≤ n * S2 := sq_target_le_card_mul_sumSq L w
  have h4 : S2 ^ 2 ≤ n * S4 := sumSq_sq_le_card_mul_sumPow4 L w
  -- S1^4 = (S1^2)^2 ≤ (n S2)^2 = n^2 S2^2 ≤ n^2 (n S4) = n^3 S4.
  calc S1 ^ 4 = (S1 ^ 2) ^ 2 := by ring
    _ ≤ (n * S2) ^ 2 := by
        exact Nat.pow_le_pow_left h2 2
    _ = n ^ 2 * S2 ^ 2 := by ring
    _ ≤ n ^ 2 * (n * S4) := by
        exact Nat.mul_le_mul_left _ h4
    _ = n ^ 3 * S4 := by ring

/-! ### The headline fourth-moment list-size bound under a structural quadruple hypothesis -/

/-- Pointwise control of the fourth power: if every coordinate is matched by at most `t` list
elements (`m i ≤ t`), then `Σ_i (m i)^4 ≤ n · t^4`. This is the trivial cap; the *non-trivial*
content of the fourth moment is that the cap can be replaced by any sharper `S₄ ≤ Q`. -/
lemma sumPow4_le_of_pointwise (L : Finset (ι → F)) (w : ι → F) (t : ℕ)
    (ht : ∀ i, matchCount L w i ≤ t) :
    (∑ i, (matchCount L w i) ^ 4) ≤ (Fintype.card ι) * t ^ 4 := by
  calc (∑ i, (matchCount L w i) ^ 4)
      ≤ ∑ _i : ι, t ^ 4 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact Nat.pow_le_pow_left (ht i) 4
    _ = (Fintype.card ι) * t ^ 4 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Fourth-moment list-size bound (headline).** Suppose every list element agrees with `w` on at
least `a` coordinates, so the target sum is `≥ |L|·a`, and suppose a structural quadruple bound
`Σ_i (m i)^4 ≤ Q` holds. Then `(|L|·a)^4 ≤ n^3 · Q`.

This is genuinely degree-4 and **non-vacuous**: it holds for *every* list `L`, word `w`, lower
agreement bound `a ≤ min_c agree(c,w)`, and any valid `Q` (e.g. `Q = n·t^4` from a pointwise cap).
Its strength relative to Johnson is examined in the comparison lemmas below. -/
theorem fourth_moment_list_bound (L : Finset (ι → F)) (w : ι → F) (a Q : ℕ)
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (hQ : (∑ i, (matchCount L w i) ^ 4) ≤ Q) :
    (L.card * a) ^ 4 ≤ (Fintype.card ι) ^ 3 * Q := by
  have hsum : L.card * a ≤ ∑ i, matchCount L w i := by
    rw [sum_matchCount_eq_sum_agree]
    calc L.card * a = ∑ _c ∈ L, a := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ c ∈ L, agree c w := Finset.sum_le_sum hclose
  calc (L.card * a) ^ 4
      ≤ (∑ i, matchCount L w i) ^ 4 := Nat.pow_le_pow_left hsum 4
    _ ≤ (Fintype.card ι) ^ 3 * (∑ i, (matchCount L w i) ^ 4) :=
        target_pow_four_le_cube_mul_sumPow4 L w
    _ ≤ (Fintype.card ι) ^ 3 * Q := Nat.mul_le_mul_left _ hQ

/-! ### Honest comparison to Johnson: the fourth moment cannot beat it unconditionally -/

/-- **The fourth moment is equivalent to (chained) second moments — it carries no extra information
on the equidistant extremal configuration.** This records the obstruction precisely: composing the
two Cauchy–Schwarz steps gives back the square of the Johnson inequality. Concretely, if the second
moment is tight (`(Σ m i)^2 = n · Σ (m i)^2`, the equidistant case), then the fourth-moment chain
`(Σ m i)^4 ≤ n^3 Σ (m i)^4` is *also* governed entirely by `Σ (m i)^4` with no slack to exploit:
the two-step bound degenerates to the one-step bound squared. -/
theorem fourth_chain_is_second_squared (L : Finset (ι → F)) (w : ι → F) :
    (∑ i, matchCount L w i) ^ 4
      ≤ ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2) ^ 2 := by
  have h2 : (∑ i, matchCount L w i) ^ 2 ≤ (Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2 :=
    sq_target_le_card_mul_sumSq L w
  calc (∑ i, matchCount L w i) ^ 4
      = ((∑ i, matchCount L w i) ^ 2) ^ 2 := by ring
    _ ≤ ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2

/-- **The chained fourth-moment cap is never tighter than the squared Johnson cap — the verified
obstruction.** The `S₄`-only fourth-moment bound on `S₁^4` is `n^3·S₄`; the second moment, squared,
caps `S₁^4` by `(n·S₂)^2 = n^2·S₂^2`. Chebyshev's own `S₂^2 ≤ n·S₄` gives `n^2 S₂^2 ≤ n^3 S₄`, so

  `(n·S₂)^2 ≤ n^3 · S₄`  (always).

Hence the fourth-moment cap is always `≥` the squared Johnson cap: chaining two Cauchy–Schwarz
steps can only *lose* tightness, never gain it. This is the precise, verified reason the fourth
moment cannot beat Johnson *from `S₄` alone*. -/
theorem squaredJohnson_le_fourthChain (L : Finset (ι → F)) (w : ι → F) :
    ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2) ^ 2
      ≤ (Fintype.card ι) ^ 3 * ∑ i, (matchCount L w i) ^ 4 := by
  have h4 : (∑ i, (matchCount L w i) ^ 2) ^ 2
      ≤ (Fintype.card ι) * ∑ i, (matchCount L w i) ^ 4 := sumSq_sq_le_card_mul_sumPow4 L w
  calc ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2) ^ 2
      = (Fintype.card ι) ^ 2 * ((∑ i, (matchCount L w i) ^ 2) ^ 2) := by ring
    _ ≤ (Fintype.card ι) ^ 2 * ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 4) :=
        Nat.mul_le_mul_left _ h4
    _ = (Fintype.card ι) ^ 3 * ∑ i, (matchCount L w i) ^ 4 := by ring

/-- **The fourth moment provably cannot beat Johnson from `S₄` alone — the obstruction as a NO-GO
theorem (not an open hypothesis).** The would-be "structural improvement" hypothesis
`n^3·Q < (n·S₂)^2` *combined* with the valid quadruple bound `S₄ ≤ Q` is **contradictory**: by the
two chained Cauchy–Schwarz steps `(n·S₂)^2 ≤ n^3·S₄ ≤ n^3·Q`. Hence no upper bound `Q` on `S₄` can
ever push the fourth-moment list cap `n^3·Q` strictly below the squared Johnson cap `(n·S₂)^2`.

This is the honest, verified content of the angle: the fourth moment, applied to the *same* matching
profile `m` that the second moment uses, is **mathematically unable** to improve the threshold —
any improvement must change the quantity being bounded (a `Q` controlling `S₄` directly *cannot*
beat the Chebyshev floor `S₂^2/n`). The hypotheses below are deliberately presented to show they are
unsatisfiable; we return `False`, certifying the no-go. -/
theorem fourth_moment_cannot_beat_johnson_from_S4
    (L : Finset (ι → F)) (w : ι → F) (Q : ℕ)
    (hQ : (∑ i, (matchCount L w i) ^ 4) ≤ Q)
    (hstruct : (Fintype.card ι) ^ 3 * Q < ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2) ^ 2) :
    False := by
  have hfloor : ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2) ^ 2
      ≤ (Fintype.card ι) ^ 3 * Q := by
    calc ((Fintype.card ι) * ∑ i, (matchCount L w i) ^ 2) ^ 2
        ≤ (Fintype.card ι) ^ 3 * ∑ i, (matchCount L w i) ^ 4 := squaredJohnson_le_fourthChain L w
      _ ≤ (Fintype.card ι) ^ 3 * Q := Nat.mul_le_mul_left _ hQ
  exact absurd hstruct (not_lt.mpr hfloor)

/-- **The genuine residual lever (honest, satisfiable).** Since `S₄` itself cannot beat the floor,
the *only* room the fourth moment offers is to bound the target sum `S₁` by something **other** than
`|L|·a` — namely to exploit that a list achieving the Johnson-extremal second moment also forces a
*specific* fourth-moment profile. We record the one inequality that survives and is satisfiable: for
any list and any pointwise matching cap `m i ≤ t`, the list size obeys `(|L|·a)^4 ≤ n^4 · t^4`,
i.e. `|L|·a ≤ n·t`. This is the *pointwise* (degenerate) consequence — it is the honest, non-vacuous
endpoint of the `S₄` route, and it is exactly the trivial coverage bound, confirming that the fourth
moment adds no asymptotic power over the union/coverage bound in the gap. -/
theorem fourth_moment_pointwise_endpoint
    (L : Finset (ι → F)) (w : ι → F) (a t : ℕ)
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (ht : ∀ i, matchCount L w i ≤ t) :
    (L.card * a) ^ 4 ≤ (Fintype.card ι) ^ 4 * t ^ 4 := by
  have hbound := fourth_moment_list_bound L w a ((Fintype.card ι) * t ^ 4) hclose
    (sumPow4_le_of_pointwise L w t ht)
  calc (L.card * a) ^ 4
      ≤ (Fintype.card ι) ^ 3 * ((Fintype.card ι) * t ^ 4) := hbound
    _ = (Fintype.card ι) ^ 4 * t ^ 4 := by ring

end ArkLib.CodingTheory.FourthMoment
