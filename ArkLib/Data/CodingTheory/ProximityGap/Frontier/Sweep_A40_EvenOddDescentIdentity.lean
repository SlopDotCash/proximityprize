/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Even/odd non-symmetric dyadic descent — the per-fibre agreement identity (#444, SEAM A)

The heart of the even/odd descent for explicit 2-power Reed–Solomon window list-decoding
(`docs/kb/deltastar-444-evenodd-descent.md`). Over a fibre `{r, -r}` (above `y = r²` under the
squaring map `μ_{2N} → μ_N`), a codeword `f(x) = F(x²) + x G(x²)` agrees with a word
`u(x) = u_e(x²) + x u_o(x²)` according to the *non-symmetric* trichotomy
`P = Q = 0`  (both roots) / `P² = y Q² ∧ Q ≠ 0`  (exactly one root) / else (neither),
where `P = (F − u_e)(y)`, `Q = (G − u_o)(y)`. Summed over the `N` fibres this is the exact
agreement-count identity verified `200/200` by `probe_444_monomial_descent.py`.

This is the combinatorial, `p`-independent engine that the campaign's antipodal-*symmetric*
(`S = −S`) tower missed: the single-root case `P² = y Q²` is precisely the non-symmetric part.

Axiom-clean: depends only on field arithmetic and `Finset.card`. No `sorry`, no extra axioms.
-/

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Per-fibre agreement trichotomy.** Over the fibre `{r, -r}` above `y = r²`, the number of
roots `x` with `P + x·Q = 0` is `2` iff `P = Q = 0`, `1` iff `Q ≠ 0 ∧ P² = r²Q²`, and `0`
otherwise. Here `P = (F − u_e)(y)`, `Q = (G − u_o)(y)` are the even/odd difference values.

This is the exact local content of the descent identity
`|S| = 2·#{P=Q=0} + #{Q≠0 ∧ P²=yQ²}` (sum the statement over the `N` fibres). -/
theorem fiber_agreement_count (r P Q : F) (hr0 : r ≠ 0) (h2 : (2 : F) ≠ 0) :
    (({r, -r} : Finset F).filter (fun x => P + x * Q = 0)).card
      = (if P = 0 ∧ Q = 0 then 2 else if P ^ 2 = r ^ 2 * Q ^ 2 ∧ Q ≠ 0 then 1 else 0) := by
  -- the two roots are distinct (char ≠ 2 and r ≠ 0)
  have hr2 : r ≠ -r := by
    intro h
    have hrr : r + r = 0 := by nth_rewrite 2 [h]; ring
    have : (2 : F) * r = 0 := by rw [two_mul]; exact hrr
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hr0 h'
  -- expand the filtered cardinality over the explicit pair
  rw [Finset.card_filter, Finset.sum_pair hr2]
  -- helper: `r * z = 0 → z = 0`  (since `r ≠ 0`)
  have hrz : ∀ z : F, r * z = 0 → z = 0 := fun z hz => by
    rcases mul_eq_zero.mp hz with h' | h'
    · exact absurd h' hr0
    · exact h'
  by_cases ha : P + r * Q = 0 <;> by_cases hb : P + -r * Q = 0
  · -- both roots agree ⇒ P = Q = 0
    have h2rQ : (2 : F) * (r * Q) = 0 := by linear_combination ha - hb
    have hQ : Q = 0 := hrz Q (by
      rcases mul_eq_zero.mp h2rQ with h' | h'
      · exact absurd h' h2
      · exact h')
    have hP : P = 0 := by rw [hQ, mul_zero, add_zero] at ha; exact ha
    rw [if_pos ha, if_pos hb, if_pos ⟨hP, hQ⟩]
  · -- only the root `r` agrees
    have hsq : P ^ 2 = r ^ 2 * Q ^ 2 := by linear_combination (P - r * Q) * ha
    have hQne : Q ≠ 0 := by
      intro hQ0
      have hP : P = 0 := by rw [hQ0, mul_zero, add_zero] at ha; exact ha
      exact hb (by rw [hP, hQ0]; ring)
    rw [if_pos ha, if_neg hb, if_neg (fun h => hQne h.2), if_pos ⟨hsq, hQne⟩]
  · -- only the root `-r` agrees
    have hsq : P ^ 2 = r ^ 2 * Q ^ 2 := by linear_combination (P + r * Q) * hb
    have hQne : Q ≠ 0 := by
      intro hQ0
      have hP : P = 0 := by rw [hQ0, mul_zero, add_zero] at hb; exact hb
      exact ha (by rw [hP, hQ0]; ring)
    rw [if_neg ha, if_pos hb, if_neg (fun h => hQne h.2), if_pos ⟨hsq, hQne⟩]
  · -- neither root agrees
    have hnPQ : ¬ (P = 0 ∧ Q = 0) := by
      rintro ⟨hP, hQ⟩; exact ha (by rw [hP, hQ, mul_zero, add_zero])
    have hnsq : ¬ (P ^ 2 = r ^ 2 * Q ^ 2 ∧ Q ≠ 0) := by
      rintro ⟨hsq, _⟩
      have hf : (P + r * Q) * (P + -r * Q) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hf with h' | h'
      · exact ha h'
      · exact hb h'
    rw [if_neg ha, if_neg hb, if_neg hnPQ, if_neg hnsq]

/-- **Global descent identity (sum form).** Given the squaring fibration data — a base set
`B` (`= μ_N`) and for each `y ∈ B` a square root `ρ y` (`ρ y ≠ 0`) — the total agreement of a
codeword over `μ_{2N} = ⋃_{y∈B} {ρ y, -ρ y}` is the sum of the per-fibre trichotomy counts.
Stated as a clean `Finset.sum` over the fibres; combined with `fiber_agreement_count` it gives
`|S| = 2·#{y: P=Q=0} + #{y: Q≠0 ∧ P²=yQ²}`. -/
theorem descent_identity_sum (B : Finset F) (ρ Pf Qf : F → F)
    (hρ0 : ∀ y ∈ B, ρ y ≠ 0) (h2 : (2 : F) ≠ 0) :
    (∑ y ∈ B, (({ρ y, -ρ y} : Finset F).filter (fun x => Pf y + x * Qf y = 0)).card)
      = ∑ y ∈ B, (if Pf y = 0 ∧ Qf y = 0 then 2
                  else if Pf y ^ 2 = ρ y ^ 2 * Qf y ^ 2 ∧ Qf y ≠ 0 then 1 else 0) := by
  refine Finset.sum_congr rfl (fun y hy => ?_)
  exact fiber_agreement_count (ρ y) (Pf y) (Qf y) (hρ0 y hy) h2

end ArkLib.ProximityGap.EvenOddDescent
