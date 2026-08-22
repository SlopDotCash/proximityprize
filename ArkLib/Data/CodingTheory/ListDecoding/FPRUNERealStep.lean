/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The genuine FPRUNE one-step inequality (GG25 Lemma 3.4 with the agreement indicator + eq. (2))

The simplified `fprune_one_step` (in `FPRUNEPotential.lean`) proves the one-step potential
inequality under the implicit assumption that the candidate codeword agrees on *every* eligible
coordinate. The **actual** FPRUNE recursion (Goyal–Guruswami 2025 / arXiv 2512.08017,
Def. 8) carries an agreement indicator: the potential is

  `f_{η,η'}(ℋ,c,T) = [c agrees with the lists on all of T] · (1-η')^{|T|} / (dim ℋ + η)`,

so the expectation `G(ℋ,c) = E_T[X_{c,T}(1-η')^{|T|}]` obeys the recursion

  `G(ℋ,c) = ∑_{i eligible} (wt_η(ℋ_i)/W)·(1-η')·[c_i agrees]·G(ℋ_i,c)`,

summing only over **eligible** coordinates (`wt_η(ℋ_i) ≤ (1-η')·wt_η(ℋ)`) and crediting only the
ones where `c` **agrees**. Lower-bounding `G` therefore reduces to:

* the **arithmetic one-step** (`fprune_one_step_weighted`): with eligible-weight normaliser `W`
  and the eligible-agreeing coordinate set `J`, the bound `W ≤ |J|·(1-η')(r+η)` gives
  `η/(r+η) ≤ ∑_{j∈J} (wt_η(ℋ_j)/W)·(1-η')·(η/(dim ℋ_j + η))`;
* the **design weight bound** (`fprune_eligible_weight_bound`, GG25 eq. (2)): the
  subspace-design inequality (Def. 6) bounds the eligible weight
  `W ≤ ((τ(r)+η)·n - (ineligible)·(1-η'))·(r+η)`, and the distance hypothesis
  `(τ(r)+η)·n ≤ (agree)·(1-η')` (the candidate is close) forces, with
  `|J| ≥ agree - ineligible`, exactly `W ≤ |J|·(1-η')(r+η)`.

Composing the two yields the genuine Lemma 3.4 one-step, ready for the strong-induction
`fprune_potential_bound`. All `Finset`/order arithmetic; no `sorry`.
-/

namespace CodingTheory.ListDecoding

open Finset

variable {ι : Type*}

/-- **The genuine FPRUNE one-step (arithmetic core), with abstract eligible-weight `W`.** `J` is
the set of *eligible-and-agreeing* coordinates and `W > 0` the eligible-weight normaliser. From
the design weight bound `W ≤ |J|·(1-η')(r+η)`, the design-weighted survival sum dominates the
potential `η/(r+η)`. Each summand `[(d_j+η)(1-η')/W]·[η/(d_j+η)]` cancels to `(1-η')η/W`, so the
sum is `|J|·(1-η')η/W`, and the bound is exactly `W ≤ |J|(1-η')(r+η)`. -/
theorem fprune_one_step_weighted
    (η η' : ℝ) (hη : 0 < η)
    (r : ℕ) (J : Finset ι) (d : ι → ℕ) (W : ℝ) (hWpos : 0 < W)
    (hWle : W ≤ (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η))) :
    η / ((r : ℕ) + η) ≤
      ∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / W) * (η / ((d j : ℕ) + η)) := by
  have hposTerm : ∀ j, (0 : ℝ) < (d j : ℝ) + η := fun j =>
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hrη : (0 : ℝ) < (r : ℝ) + η := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  -- Each summand collapses to `(1-η')·η / W`.
  have hterm : ∀ j ∈ J,
      ((((d j : ℝ) + η) * (1 - η')) / W) * (η / ((d j : ℕ) + η)) = (1 - η') * η / W := by
    intro j _
    have hdj : (d j : ℝ) + η ≠ 0 := ne_of_gt (hposTerm j)
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  -- `η/(r+η) ≤ |J|·(1-η')η / W`.
  have key : η / ((r : ℝ) + η) ≤ ((J.card : ℝ) * (1 - η') * η) / W := by
    rw [le_div_iff₀ hWpos, div_mul_eq_mul_div, div_le_iff₀ hrη]
    nlinarith [mul_le_mul_of_nonneg_left hWle (le_of_lt hη), hη, hWpos, hrη]
  calc η / ((r : ℕ) + η)
      = η / ((r : ℝ) + η) := by ring_nf
    _ ≤ ((J.card : ℝ) * (1 - η') * η) / W := key
    _ = (J.card : ℝ) * ((1 - η') * η / W) := by ring

/-- **GG25 eq. (2): the eligible-weight bound from the subspace design.** With block length
`n`, candidate dimension `r`, design parameter `τr`, `agree` agreeing coordinates and `inelig`
ineligible coordinates, the τ-subspace-design property (Def. 6) gives the eligible-weight bound
`W ≤ ((τr+η)·n - inelig·(1-η'))·(r+η)`, and the distance hypothesis `(τr+η)·n ≤ agree·(1-η')`
(the candidate is within the decoding radius) together with `agree - inelig ≤ |J|` (eligible
agreeing ≥ agreeing − ineligible) yields exactly the bound consumed by `fprune_one_step_weighted`:
`W ≤ |J|·(1-η')(r+η)`. -/
theorem fprune_eligible_weight_bound
    (η η' : ℝ) (hη'pos : 0 < 1 - η')
    (r n : ℕ) (τr W agree inelig : ℝ) (J : Finset ι)
    (hrη : (0 : ℝ) ≤ (r : ℝ) + η)
    (hEq2 : W ≤ ((τr + η) * (n : ℝ) - inelig * (1 - η')) * ((r : ℝ) + η))
    (hDist : (τr + η) * (n : ℝ) ≤ agree * (1 - η'))
    (hJ : agree - inelig ≤ (J.card : ℝ)) :
    W ≤ (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η)) := by
  -- `|J|(1-η')(r+η) ≥ (agree-inelig)(1-η')(r+η) = (agree(1-η') - inelig(1-η'))(r+η)`
  --   `≥ ((τr+η)n - inelig(1-η'))(r+η) ≥ W`.
  have hstep : ((τr + η) * (n : ℝ) - inelig * (1 - η')) * ((r : ℝ) + η)
      ≤ (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η)) := by
    have h1 : (τr + η) * (n : ℝ) - inelig * (1 - η')
        ≤ (J.card : ℝ) * (1 - η') := by
      nlinarith [mul_le_mul_of_nonneg_right hJ (le_of_lt hη'pos), hDist]
    nlinarith [mul_le_mul_of_nonneg_right h1 hrη]
  linarith [hEq2, hstep]

/-- **The composed real FPRUNE one-step inequality (GG25 Lemma 3.4 front door).** This packages
`fprune_eligible_weight_bound` and `fprune_one_step_weighted`: once the subspace-design
eligible-weight estimate (GG25 eq. (2)), the distance/agreement lower bound, and the
eligible-agreeing count inequality are available, the design-weighted one-step recursion
dominates the potential `η/(r+η)`.

This is the local arithmetic endpoint consumed by the subspace-indexed Lemma 3.5 induction below.
It still leaves the genuinely coding-theoretic work explicit in the hypotheses: constructing the
eligible set/normaliser and proving the GG25 eq. (2), distance, and count premises for the actual
FPRUNE process. -/
theorem fprune_one_step_real
    (η η' : ℝ) (hη : 0 < η) (hη'pos : 0 < 1 - η')
    (r n : ℕ) (τr W agree inelig : ℝ) (J : Finset ι) (d : ι → ℕ)
    (hWpos : 0 < W)
    (hEq2 : W ≤ ((τr + η) * (n : ℝ) - inelig * (1 - η')) * ((r : ℝ) + η))
    (hDist : (τr + η) * (n : ℝ) ≤ agree * (1 - η'))
    (hJ : agree - inelig ≤ (J.card : ℝ)) :
    η / ((r : ℕ) + η) ≤
      ∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / W) * (η / ((d j : ℕ) + η)) := by
  have hrη : (0 : ℝ) ≤ (r : ℝ) + η :=
    le_of_lt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη)
  exact fprune_one_step_weighted η η' hη r J d W hWpos
    (fprune_eligible_weight_bound η η' hη'pos r n τr W agree inelig J
      hrη hEq2 hDist hJ)

/-! ## Subspace-indexed potential bound (faithful Lemma 3.5)

The actual FPRUNE expectation `G(ℋ,c)` is indexed by the *subspace* `ℋ`, not merely its
dimension (two subspaces of equal dimension can have different children `ℋ_i = {a ∈ ℋ | a_i = 0}`).
The `ℕ`-indexed `fprune_potential_bound` is therefore not directly applicable; we need the
strong induction over a rank function `rank : σ → ℕ` on an arbitrary index type `σ` (here the
subspaces, `rank = dim`). This is that generalisation. -/

variable {σ : Type*}

/-- **Subspace-indexed FPRUNE potential bound (faithful Lemma 3.5).** For a rank function
`rank : σ → ℕ` and value `E : σ → ℝ`, given the base case at rank `0` and, at each positive-rank
`x`, a finite nonnegatively-weighted branching into strictly-smaller-rank children `ch j` with the
expectation recursion `∑ c_j E(ch j) ≤ E x` and the one-step potential inequality
`pot(rank x) ≤ ∑ c_j pot(rank (ch j))`, the bound `pot(rank x) ≤ E x` holds for every `x`.

Proof: strong induction on `n = rank x`; children have rank `< n`, so the inductive hypothesis
`pot(rank (ch j)) ≤ E (ch j)` transports through the nonnegative combination. -/
theorem fprune_potential_bound_gen
    (rank : σ → ℕ) (E : σ → ℝ) (pot : ℕ → ℝ)
    (base : ∀ x, rank x = 0 → pot 0 ≤ E x)
    (step : ∀ x, 0 < rank x → ∃ (J : Finset ι) (c : ι → ℝ) (ch : ι → σ),
        (∀ j ∈ J, 0 ≤ c j) ∧ (∀ j ∈ J, rank (ch j) < rank x) ∧
        (∑ j ∈ J, c j * E (ch j) ≤ E x) ∧
        (pot (rank x) ≤ ∑ j ∈ J, c j * pot (rank (ch j)))) :
    ∀ x, pot (rank x) ≤ E x := by
  suffices H : ∀ n, ∀ x, rank x = n → pot (rank x) ≤ E x from fun x => H (rank x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    rcases Nat.eq_zero_or_pos (rank x) with h0 | hpos
    · rw [h0]; exact base x h0
    · obtain ⟨J, c, ch, hc, hd, hE, hpot⟩ := step x hpos
      calc pot (rank x)
          ≤ ∑ j ∈ J, c j * pot (rank (ch j)) := hpot
        _ ≤ ∑ j ∈ J, c j * E (ch j) :=
            Finset.sum_le_sum fun j hj =>
              mul_le_mul_of_nonneg_left (ih (rank (ch j)) (hx ▸ hd j hj) (ch j) rfl) (hc j hj)
        _ ≤ E x := hE

/-- **Real FPRUNE expectation lower bound from subspace-indexed branches.** This is the
Lemma-3.5 endpoint using the *real* one-step front door `fprune_one_step_real`, rather than the
simplified all-eligible-coordinate step in `FPRUNEPotential.lean`.

For each positive-rank state `x`, the branch data supplies:

* the eligible-and-agreeing coordinate set `J`,
* child states `ch j` whose rank is the child dimension `d j` and is strictly smaller than
  `rank x`,
* the eligible-weight normaliser `W > 0`,
* the GG25 eq. (2), distance/agreement, and eligible-agreeing count premises, and
* the expectation recursion through the real FPRUNE coefficients.

The conclusion is the FPRUNE potential lower bound `η/(rank x+η) ≤ E x` for every state. -/
theorem fprune_expectation_lower_real_of_branch
    (rank : σ → ℕ) (E : σ → ℝ)
    (η η' : ℝ) (hη : 0 < η) (hη'pos : 0 < 1 - η')
    (base : ∀ x, rank x = 0 → η / ((0 : ℝ) + η) ≤ E x)
    (branch : ∀ x, 0 < rank x →
      ∃ (J : Finset ι) (d : ι → ℕ) (ch : ι → σ)
        (W τr agree inelig : ℝ) (n : ℕ),
        0 < W ∧
        (∀ j ∈ J, rank (ch j) = d j) ∧
        (∀ j ∈ J, rank (ch j) < rank x) ∧
        W ≤ ((τr + η) * (n : ℝ) - inelig * (1 - η')) * ((rank x : ℝ) + η) ∧
        (τr + η) * (n : ℝ) ≤ agree * (1 - η') ∧
        agree - inelig ≤ (J.card : ℝ) ∧
        (∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / W) * E (ch j) ≤ E x)) :
    ∀ x, η / ((rank x : ℝ) + η) ≤ E x := by
  refine fprune_potential_bound_gen (ι := ι) rank E (fun r => η / ((r : ℝ) + η)) ?_ ?_
  · intro x hx
    simpa [hx] using base x hx
  · intro x hxpos
    obtain ⟨J, d, ch, W, τr, agree, inelig, n,
      hWpos, hrank, hdrop, hEq2, hDist, hJ, hE⟩ := branch x hxpos
    refine ⟨J, (fun j => (((d j : ℝ) + η) * (1 - η')) / W), ch, ?_, hdrop, hE, ?_⟩
    · intro j _
      exact div_nonneg
        (mul_nonneg (add_nonneg (Nat.cast_nonneg _) hη.le) (le_of_lt hη'pos)) hWpos.le
    · have hstep :=
        fprune_one_step_real (ι := ι) η η' hη hη'pos (rank x) n τr W agree inelig J d
          hWpos hEq2 hDist hJ
      refine le_trans hstep ?_
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left
          (by
            have hjrank := hrank j hj
            simp [hjrank] : η / ((d j : ℝ) + η) ≤
              η / ((rank (ch j) : ℝ) + η))
          (div_nonneg
            (mul_nonneg (add_nonneg (Nat.cast_nonneg _) hη.le) (le_of_lt hη'pos)) hWpos.le)

/-- **Real-branch FPRUNE list-size endpoint.** This combines the subspace-indexed real FPRUNE
expectation lower bound with the finite first-moment shell, but keeps all coding-theoretic
construction data explicit.

For each candidate `c ∈ L`, the hypotheses provide a root state `root c`, a candidate-specific
expectation function `E c`, the real FPRUNE branch data needed by
`fprune_expectation_lower_real_of_branch`, and an identity between the root expectation and the
finite sampling average `∑ T, p T * g c T`. If all roots have common rank `r` and the pointwise
simultaneous budget `∑_{c∈L} g c T ≤ M` holds, then `|L| ≤ M * (r+η)/η`. -/
theorem fprune_real_list_card_le_of_branches
    {α Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp_nonneg : ∀ T, 0 ≤ p T) (hp_sum : ∑ T, p T = 1)
    (L : Finset α) (g : α → Ω → ℝ)
    (rank : σ → ℕ) (root : α → σ) (E : α → σ → ℝ)
    (η η' : ℝ) (hη : 0 < η) (hη'pos : 0 < 1 - η')
    (r : ℕ) (M : ℝ)
    (hroot : ∀ c, c ∈ L → rank (root c) = r)
    (base : ∀ c, c ∈ L → ∀ x, rank x = 0 → η / ((0 : ℝ) + η) ≤ E c x)
    (branch : ∀ c, c ∈ L → ∀ x, 0 < rank x →
      ∃ (J : Finset ι) (d : ι → ℕ) (ch : ι → σ)
        (W τr agree inelig : ℝ) (n : ℕ),
        0 < W ∧
        (∀ j ∈ J, rank (ch j) = d j) ∧
        (∀ j ∈ J, rank (ch j) < rank x) ∧
        W ≤ ((τr + η) * (n : ℝ) - inelig * (1 - η')) * ((rank x : ℝ) + η) ∧
        (τr + η) * (n : ℝ) ≤ agree * (1 - η') ∧
        agree - inelig ≤ (J.card : ℝ) ∧
        (∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / W) * E c (ch j) ≤ E c x))
    (hExpect : ∀ c, c ∈ L → E c (root c) = ∑ T, p T * g c T)
    (hSimul : ∀ T, (∑ c ∈ L, g c T) ≤ M) :
    (L.card : ℝ) ≤ M * (((r : ℝ) + η) / η) := by
  have hrη : (0 : ℝ) < (r : ℝ) + η :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  have hβ : 0 < η / ((r : ℝ) + η) := div_pos hη hrη
  have hLower : ∀ c ∈ L, η / ((r : ℝ) + η) ≤ ∑ T, p T * g c T := by
    intro c hc
    have hpoint :=
      fprune_expectation_lower_real_of_branch (ι := ι) rank (E c) η η' hη hη'pos
        (base c hc) (branch c hc) (root c)
    have hrank := hroot c hc
    have hrootLower : η / ((r : ℝ) + η) ≤ E c (root c) := by
      simpa [hrank] using hpoint
    simpa [hExpect c hc] using hrootLower
  have hmul : (L.card : ℝ) * (η / ((r : ℝ) + η)) ≤ M := by
    calc (L.card : ℝ) * (η / ((r : ℝ) + η))
        = ∑ _c ∈ L, η / ((r : ℝ) + η) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ L, ∑ T, p T * g c T := Finset.sum_le_sum hLower
      _ = ∑ T, p T * (∑ c ∈ L, g c T) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ T, p T * M := by
          refine Finset.sum_le_sum fun T _ => ?_
          exact mul_le_mul_of_nonneg_left (hSimul T) (hp_nonneg T)
      _ = M := by rw [← Finset.sum_mul, hp_sum, one_mul]
  have hbound : (L.card : ℝ) ≤ M / (η / ((r : ℝ) + η)) := by
    rw [le_div_iff₀ hβ]
    exact hmul
  rwa [div_div_eq_mul_div, mul_div_assoc] at hbound

end CodingTheory.ListDecoding

/-! ### `#print axioms` verification anchors -/

#print axioms CodingTheory.ListDecoding.fprune_one_step_weighted
#print axioms CodingTheory.ListDecoding.fprune_eligible_weight_bound
#print axioms CodingTheory.ListDecoding.fprune_one_step_real
#print axioms CodingTheory.ListDecoding.fprune_potential_bound_gen
#print axioms CodingTheory.ListDecoding.fprune_expectation_lower_real_of_branch
#print axioms CodingTheory.ListDecoding.fprune_real_list_card_le_of_branches
