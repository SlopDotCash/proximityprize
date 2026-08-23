/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ContiguousBandBenign

/-!
# The worst monomial word `x^{n/2}` decodes to a list of EXACTLY the two constants `±1` (#444)

This file DISCHARGES the named-open `SingleLineNotList` content of `UncertaintyTwoPowerExtremal`:
the single-line beyond-Johnson agreement excess (`s* = n/2 + O(1) ≫ √(kn)`) does NOT lift to a
large LIST.  Where `UncertaintyTwoPowerExtremal.SingleLineNotList` TAKES `listAtExtremal ≤ 2` as a
HYPOTHESIS (an honest placeholder for the machine-observed numeric input), this file PROVES it
unconditionally as a genuine root-counting fact — no `sorry`, no vacuity.

## The mechanism (probe-verified, then proven)

The worst word is `w(x) = x^{n/2}` on the THIN 2-power subgroup `μ_n` (`n = 2^a`).  Since every
`x ∈ μ_n` has `x^n = 1`, we get `(x^{n/2})² = x^n = 1`, so **`w` is `{±1}`-valued**.

Probe `scripts/probes/probe_worst_monomial_listsize.py` (exact `F_p`, PROPER `μ_n`, `n=2^a`,
`p ≫ n³`, two char-0-faithful primes per `n`, NEVER `n=q−1`) over `n=8,16,32`, `k=2,4`:
- the two constants `+1`, `−1` each agree with `w` on EXACTLY `n/2` points (the two value-cosets);
- the list at radius `s = n/2` is EXACTLY `{+1, −1}` (size **2**), and EMPTY for any `s > n/2`;
- `probe_worst_monomial_witnesses.py` confirms the witnesses ARE the constants `±1`;
- the **max agreement of any NON-constant `deg < k` codeword with `w` is `≤ 2(k−1)`** (probe:
  `= 2` at `k=2`, `≤ 4` at `k=4`) — far below `n/2` in the prize regime.

So once `2(k−1) < n/2` (true for fixed `k`, `n → ∞` — the prize regime), the ONLY codewords
within Johnson radius of the worst monomial word are the two constants.  The beyond-Johnson
single-line excess is a `O(1)`-list phenomenon; it cannot seed list explosion.  This is exactly
the brief's "the combinatorial single-line face contributes only `O(1)` to the list; the genuine
beyond-Johnson gap lives in the under-determined/agreement-sharing/BGK contribution = the wall."

## What is proven here (axiom-clean, 0 `sorry`)

* `pmOne_word_sq_eq_one` — `w(x) = x^{n/2}` satisfies `w(x)² = 1` on `μ_n`.
* `nonconstant_agreement_le_two_mul` — a `deg = d ≥ 1` codeword `c` agrees with `w` on `≤ 2d`
  points of `μ_n` (root-forcing on `c² − 1`, degree `2d`, nonzero since `c` non-constant).
* `worstMonomial_list_subset_pm_one` — under `2(k−1) < n/2`, any `deg < k` codeword agreeing with
  `w` on `≥ n/2` points is one of the two constants `C 1` or `C (−1)`.
* `worstMonomial_list_card_le_two` — the list of distinct `deg < k` codewords agreeing with `w`
  on `≥ n/2` points has cardinality `≤ 2`.

Thinness is ESSENTIAL: it is exactly `x^{n/2}` being order-`2` (`n = 2^a`) that makes `w` two-valued
and the two value-cosets equal — the whole mechanism is the `2`-power structure of `μ_n`.

Honest scope: this bounds the list at the *specific* worst monomial word `x^{n/2}` (the in-tree
single-line extremal).  It does NOT bound the list at an arbitrary worst word — the genuinely open
prize object (the under-determined BGK contribution) remains the wall.  CORE
(`M(μ_n) ≤ C√(n·log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issue #444.
-/

open Polynomial Finset

namespace ProximityGap.Frontier.WorstMonomialListTwo

open ProximityGap.Frontier.ContiguousBandBenign (card_roots_le_of_imp)

variable {F : Type*} [Field F] [DecidableEq F]

/-- The worst monomial word as a polynomial: `w = X^{n/2}`. -/
noncomputable def worstWord (n : ℕ) : F[X] := X ^ (n / 2)

omit [DecidableEq F] in
/-- **`w` is `±1`-valued on `μ_n`** (`n = 2^a`): `(x^{n/2})² = x^n = 1`. -/
theorem worstWord_sq_eq_one {n : ℕ} (hn : 2 ∣ n) {x : F} (hx : x ^ n = 1) :
    (x ^ (n / 2)) ^ 2 = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel hn, hx]

/-- **Agreement polynomial of the worst word against a codeword `c`**: its `μ_n`-roots are exactly
the points where `c` agrees with `w = X^{n/2}`. -/
noncomputable def wordAgreementPoly (n : ℕ) (c : F[X]) : F[X] := X ^ (n / 2) - c

/-- **Non-constant agreement bound.** If a codeword `c` has `1 ≤ c.natDegree` (it is non-constant)
and `c.natDegree < k`, then `c` agrees with the worst word `w = X^{n/2}` on at most `2·(k−1)` points
of `μ_n` (`2 ∣ n`).

Mechanism: at an agreement point `x` (`c(x) = x^{n/2}`), `c(x)² = (x^{n/2})² = 1`, so `x` is a root
of `g := c² − 1`, which is nonzero of degree `2·c.natDegree ≤ 2·(k−1)` (nonzero because `c²` is
non-constant of degree `2·c.natDegree ≥ 2`, so `c² − 1 ≠ 0`). Root-forcing gives the bound. -/
theorem nonconstant_agreement_le_two_mul {n k : ℕ} (hn : 2 ∣ n) {c : F[X]}
    (hc1 : 1 ≤ c.natDegree) (hck : c.natDegree < k)
    {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => (wordAgreementPoly n c).IsRoot x)).card ≤ 2 * (k - 1) := by
  -- g := c² − 1, the root-forcing polynomial
  set g : F[X] := c ^ 2 - 1 with hg_def
  -- g ≠ 0: c² has natDegree 2·c.natDegree ≥ 2 > 0 = natDegree 1, so c² − 1 ≠ 0
  have hc2deg : (c ^ 2).natDegree = 2 * c.natDegree := by
    rw [Polynomial.natDegree_pow]
  have hg : g ≠ 0 := by
    intro h0
    -- c² = 1 ⟹ natDegree c² = 0, contradicting 2·c.natDegree ≥ 2
    have : c ^ 2 = 1 := by rw [hg_def, sub_eq_zero] at h0; exact h0
    rw [this, Polynomial.natDegree_one] at hc2deg
    omega
  -- deg g ≤ 2·(k−1)
  have hdeg : g.natDegree ≤ 2 * (k - 1) := by
    have hsub : g.natDegree ≤ (c ^ 2).natDegree := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simp [Polynomial.natDegree_one]
    rw [hc2deg] at hsub
    -- 2·c.natDegree ≤ 2·(k−1) since c.natDegree ≤ k−1
    have : c.natDegree ≤ k - 1 := by omega
    omega
  -- root forcing: on μ_n, an agreement root of the word forces a root of g
  refine card_roots_le_of_imp hg hdeg ?_
  intro x hx hxr
  -- hxr : (X^{n/2} − c).IsRoot x, i.e. x^{n/2} = c.eval x
  simp only [wordAgreementPoly, Polynomial.IsRoot.def, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero] at hxr
  -- hxr : x^{n/2} = eval x c; then (eval x c)² = (x^{n/2})² = 1
  have hsq : (Polynomial.eval x c) ^ 2 = 1 := by
    rw [← hxr]; exact worstWord_sq_eq_one hn (hS x hx)
  -- hence g.eval x = (c.eval x)² − 1 = 0
  rw [hg_def, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_one, hsq, sub_self]

omit [DecidableEq F] in
/-- **The constants `±1` agree with `w` only on their value-coset.** A constant codeword `c = C v`
agreeing with `w = X^{n/2}` on a point `x ∈ μ_n` has `v² = 1`, i.e. `v ∈ {1, −1}`. -/
theorem const_agree_value {n : ℕ} (hn : 2 ∣ n) {v x : F} (hx : x ^ n = 1)
    (hagree : x ^ (n / 2) = v) : v ^ 2 = 1 := by
  rw [← hagree]; exact worstWord_sq_eq_one hn hx

/-- **List ⊆ {±1} in the prize regime.** If `2·(k−1) < n/2` (fixed `k`, `n → ∞`: the prize regime),
then any `deg < k` codeword `c` agreeing with `w = X^{n/2}` on `≥ n/2` points of a set `S ⊆ μ_n`
must be a constant `C 1` or `C (−1)`.

Proof: if `c` were non-constant (`1 ≤ c.natDegree`), `nonconstant_agreement_le_two_mul` caps its
agreement at `2(k−1) < n/2`, contradicting `≥ n/2`.  So `c` is a constant `C v`; picking any
agreement point gives `v² = 1`, hence `v = 1` or `v = −1` (a field). -/
theorem worstMonomial_list_subset_pm_one {n k : ℕ} (hn : 2 ∣ n) (hk : 2 * (k - 1) < n / 2)
    {c : F[X]} (hck : c.natDegree < k)
    {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1)
    (hagree : n / 2 ≤ (S.filter (fun x => (wordAgreementPoly n c).IsRoot x)).card) :
    c = C 1 ∨ c = C (-1) := by
  classical
  -- c must be constant
  by_cases hc1 : 1 ≤ c.natDegree
  · exfalso
    have hle := nonconstant_agreement_le_two_mul hn hc1 hck hS
    omega
  -- c.natDegree = 0 ⟹ c = C (c.coeff 0)
  simp only [not_le, Nat.lt_one_iff] at hc1
  have hc0 : c.natDegree = 0 := hc1
  obtain ⟨v, hv⟩ := Polynomial.natDegree_eq_zero.mp hc0
  -- there is an agreement point (the filtered set is nonempty since n/2 ≥ 1 when n ≥ 2)
  have hpos : 0 < (S.filter (fun x => (wordAgreementPoly n c).IsRoot x)).card := by
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n <;> simp_all
      · exact h
    have : 1 ≤ n / 2 := by omega
    omega
  obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hxmem
  obtain ⟨hxS, hxroot⟩ := hxmem
  -- agreement at x: x^{n/2} = c.eval x = v
  simp only [wordAgreementPoly, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, ← hv, Polynomial.eval_C, sub_eq_zero] at hxroot
  -- v² = 1
  have hv2 : v ^ 2 = 1 := const_agree_value hn (hS x hxS) hxroot
  -- v = 1 ∨ v = −1 : factor v² − 1 = (v−1)(v+1) in the field
  have hfac : (v - 1) * (v + 1) = 0 := by linear_combination hv2
  have hvpm : v = 1 ∨ v = -1 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rcases hvpm with h | h
  · exact Or.inl (by rw [← hv, h])
  · exact Or.inr (by rw [← hv, h])

/-- **The list at the worst monomial word has cardinality `≤ 2`** (prize regime `2(k−1) < n/2`).

The set of distinct `deg < k` codewords (drawn from any finite family `L`) agreeing with the worst
word `w = X^{n/2}` on `≥ n/2` points of `μ_n` is a subset of `{C 1, C (−1)}`, hence has at most `2`
elements.  This is the UNCONDITIONAL, NON-vacuous content behind
`UncertaintyTwoPowerExtremal.SingleLineNotList`: the beyond-Johnson single-line extremal contributes
only an `O(1)` (`= 2`) list. -/
theorem worstMonomial_list_card_le_two {n k : ℕ} (hn : 2 ∣ n) (hk : 2 * (k - 1) < n / 2)
    {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1)
    (L : Finset F[X])
    (hL : ∀ c ∈ L, c.natDegree < k ∧
      n / 2 ≤ (S.filter (fun x => (wordAgreementPoly n c).IsRoot x)).card) :
    L.card ≤ 2 := by
  classical
  have hsub : L ⊆ ({C 1, C (-1)} : Finset F[X]) := by
    intro c hc
    obtain ⟨hck, hag⟩ := hL c hc
    rcases worstMonomial_list_subset_pm_one hn hk hck hS hag with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  calc L.card ≤ ({C 1, C (-1)} : Finset F[X]).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)

end ProximityGap.Frontier.WorstMonomialListTwo
