/-
# The A+Z form of the even/odd descent identity (#444, SEAM A)

A cleaner equivalent of the per-fibre agreement trichotomy
(`Sweep_A40_EvenOddDescentIdentity.lean`). Over the fibre `{r, -r}` above `y = r²` under
the squaring map `μ_{2N} → μ_N`, the number of agreement roots collapses to a SUM of two
clean indicators:

  `#{x ∈ {r,-r} : P + x·Q = 0}  =  ⟦P = 0 ∧ Q = 0⟧ + ⟦P² = r²Q²⟧`.

Summed over the `N` fibres this gives the **A + Z form** of the descent identity:

  `agreement(f, u)  =  A  +  Z`,      `A = #{y : P = Q = 0}`,   `Z = #{y : P² = y·Q²}`,

where `P = (F − u_e)(y)`, `Q = (G − u_o)(y)`. This is *equivalent* to the `2A + B` form
(`Z = A + B`, since `Q = 0 ⟹ P² = y·Q² ⟹ P = 0`), but it is the useful one:

* `A` is the **symmetric joint-agreement** term — the interleaved/folded level-`μ−1`
  agreement of the pair `(F,G)` with `(u_e,u_o)`. This is exactly the part the campaign's
  antipodal `S = −S` tower captured.
* `Z = #{y ∈ μ_N : R(y) = 0}` is the zero-count of the **explicit quadratic form**
  `R(y) := P(y)² − y·Q(y)²`. This is the genuinely new, non-symmetric content. When the word
  is **low-weight** (`u_e, u_o` Laurent polynomials of bounded degree), `R` is a genuine
  low-degree polynomial and `Z ≤ deg R` is a Lagrange bound — this is precisely why the worst
  word's exponent governs the list (the exponent-degree dichotomy: mid-exponent `a ≈ n/4`
  maximises `deg R` inside `μ_N`, matching the empirically-observed worst word `x^{n/4}+1`).

The open list-decoding content (G1 uniform branching, G2 worst-word-is-low-weight) is *not*
resolved here; this file isolates the exact closed identity those gaps sit on top of.

Axiom-clean: depends only on field arithmetic and `Finset.card`. No `sorry`, no extra axioms.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Per-fibre agreement, A + Z form.** Over the fibre `{r, -r}` above `y = r²`, the number
of agreement roots equals the sum of the symmetric indicator `⟦P = 0 ∧ Q = 0⟧` and the
quadratic-form indicator `⟦P² = r²Q²⟧`. Summing over the `N` fibres yields
`agreement = A + Z` with `A = #{P=Q=0}`, `Z = #{P²=yQ²}`. -/
theorem fiber_agreement_AZ (r P Q : F) (hr0 : r ≠ 0) (h2 : (2 : F) ≠ 0) :
    (({r, -r} : Finset F).filter (fun x => P + x * Q = 0)).card
      = (if P = 0 ∧ Q = 0 then 1 else 0) + (if P ^ 2 = r ^ 2 * Q ^ 2 then 1 else 0) := by
  -- the two fibre roots are distinct (char ≠ 2 and r ≠ 0)
  have hr2 : r ≠ -r := by
    intro h
    have hrr : r + r = 0 := by nth_rewrite 2 [h]; ring
    have : (2 : F) * r = 0 := by rw [two_mul]; exact hrr
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hr0 h'
  rw [Finset.card_filter, Finset.sum_pair hr2]
  -- helper: `r * z = 0 → z = 0`
  have hrz : ∀ z : F, r * z = 0 → z = 0 := fun z hz => by
    rcases mul_eq_zero.mp hz with h' | h'
    · exact absurd h' hr0
    · exact h'
  by_cases ha : P + r * Q = 0 <;> by_cases hb : P + -r * Q = 0
  · -- both roots agree ⇒ P = Q = 0 ⇒ both indicators fire
    have h2rQ : (2 : F) * (r * Q) = 0 := by linear_combination ha - hb
    have hQ : Q = 0 := hrz Q (by
      rcases mul_eq_zero.mp h2rQ with h' | h'
      · exact absurd h' h2
      · exact h')
    have hP : P = 0 := by rw [hQ, mul_zero, add_zero] at ha; exact ha
    have hsq : P ^ 2 = r ^ 2 * Q ^ 2 := by rw [hP, hQ]; ring
    rw [if_pos ha, if_pos hb, if_pos ⟨hP, hQ⟩, if_pos hsq]
  · -- only root `r` agrees ⇒ Q ≠ 0, P² = r²Q² ⇒ only the quadratic indicator fires
    have hsq : P ^ 2 = r ^ 2 * Q ^ 2 := by linear_combination (P - r * Q) * ha
    have hQne : Q ≠ 0 := by
      intro hQ0
      have hP : P = 0 := by rw [hQ0, mul_zero, add_zero] at ha; exact ha
      exact hb (by rw [hP, hQ0]; ring)
    have hnPQ : ¬ (P = 0 ∧ Q = 0) := fun h => hQne h.2
    rw [if_pos ha, if_neg hb, if_neg hnPQ, if_pos hsq]
  · -- only root `-r` agrees ⇒ symmetric to the previous case
    have hsq : P ^ 2 = r ^ 2 * Q ^ 2 := by linear_combination (P + r * Q) * hb
    have hQne : Q ≠ 0 := by
      intro hQ0
      have hP : P = 0 := by rw [hQ0, mul_zero, add_zero] at hb; exact hb
      exact ha (by rw [hP, hQ0]; ring)
    have hnPQ : ¬ (P = 0 ∧ Q = 0) := fun h => hQne h.2
    rw [if_neg ha, if_pos hb, if_neg hnPQ, if_pos hsq]
  · -- neither root agrees ⇒ P² ≠ r²Q² and ¬(P=Q=0) ⇒ no indicator fires
    have hnsq : ¬ P ^ 2 = r ^ 2 * Q ^ 2 := by
      intro hsq
      have hf : (P + r * Q) * (P + -r * Q) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hf with h' | h'
      · exact ha h'
      · exact hb h'
    have hnPQ : ¬ (P = 0 ∧ Q = 0) := by
      rintro ⟨hP, hQ⟩; exact ha (by rw [hP, hQ, mul_zero, add_zero])
    rw [if_neg ha, if_neg hb, if_neg hnPQ, if_neg hnsq]

/-- **Descent spine (even word, even codeword).** When the codeword's odd part matches the
word's odd part (`Q = G − u_o = 0` — the case `G ≡ 0` against an even word `u_o ≡ 0`), the
fibre agreement count is exactly `2 · ⟦P = 0⟧`. Summed over `μ_N` this is
`agreement(f, u) = 2 · #{y : F(y) = u_e(y)}` — the even codewords agree on `μ_n` at exactly
twice their level-`μ−1` agreement with `u_e`. This is the rigorous backbone of the descent:
the even codewords form a "spine" that bijects with the level-`μ−1` window list (at half
threshold), so branching along the spine is exactly `1`. The branching of the *full* list is
`1 + (#mixed members with G ≠ u_o)`, and bounding that mixed count is the open gap G1. -/
theorem fiber_agreement_even (r P : F) (hr0 : r ≠ 0) (h2 : (2 : F) ≠ 0) :
    (({r, -r} : Finset F).filter (fun x => P + x * 0 = 0)).card
      = 2 * (if P = 0 then 1 else 0) := by
  have hr2 : r ≠ -r := by
    intro h
    have hrr : r + r = 0 := by nth_rewrite 2 [h]; ring
    have : (2 : F) * r = 0 := by rw [two_mul]; exact hrr
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hr0 h'
  simp only [mul_zero, add_zero]
  by_cases hP : P = 0
  · rw [if_pos hP, Finset.filter_true_of_mem (fun x _ => hP), Finset.card_pair hr2]
  · rw [if_neg hP, Finset.filter_false_of_mem (fun x _ => hP), Finset.card_empty, mul_zero]

/-- **Global descent identity, A + Z form.** Summed over the base `B = μ_N` (each fibre with a
chosen square root `ρ y ≠ 0`), the total agreement is `A + Z`:
the symmetric joint-agreement count `A = ∑ ⟦P = Q = 0⟧` plus the quadratic-form zero count
`Z = ∑ ⟦P² = y·Q²⟧`. -/
theorem descent_identity_AZ (B : Finset F) (ρ Pf Qf : F → F)
    (hρ0 : ∀ y ∈ B, ρ y ≠ 0) (h2 : (2 : F) ≠ 0) :
    (∑ y ∈ B, (({ρ y, -ρ y} : Finset F).filter (fun x => Pf y + x * Qf y = 0)).card)
      = (∑ y ∈ B, (if Pf y = 0 ∧ Qf y = 0 then 1 else 0))
        + (∑ y ∈ B, (if Pf y ^ 2 = ρ y ^ 2 * Qf y ^ 2 then 1 else 0)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  exact fiber_agreement_AZ (ρ y) (Pf y) (Qf y) (hρ0 y hy) h2

/-- The quadratic-form zero count `Z` as the cardinality of the agreement-root set
`{y ∈ B : R(y) = 0}` with `R(y) = P(y)² − y·Q(y)²`. This is the object a low-weight word
bounds by `deg R` (Lagrange): the exact closed handle on the non-symmetric term. -/
theorem Z_eq_card_quadform (B : Finset F) (ρ Pf Qf : F → F) :
    (∑ y ∈ B, (if Pf y ^ 2 = ρ y ^ 2 * Qf y ^ 2 then 1 else 0))
      = (B.filter (fun y => Pf y ^ 2 - ρ y ^ 2 * Qf y ^ 2 = 0)).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases h : Pf y ^ 2 = ρ y ^ 2 * Qf y ^ 2
  · rw [if_pos h, if_pos (by rw [h]; ring)]
  · rw [if_neg h, if_neg (by intro hh; exact h (by linear_combination hh))]

end ArkLib.ProximityGap.EvenOddDescent
