/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.UncertaintyTwoPowerJohnsonRefuted
import Mathlib.Tactic.LinearCombination

/-!
# The `n/2` sparse-zero floor extends to GENUINE TRINOMIALS (`t = 3`) on `μ_{2^μ}` (#407)

`UncertaintyTwoPowerJohnsonRefuted` exhibits the **binomial** (`t = 2`) witness `X^{n/2} + 1`,
which has exactly `n/2` roots in `μ_n` (`n = 2^μ`), refuting any sub-Johnson upper bound on the
far-line sparse-zero count `s*`. A reasonable hope to salvage a sub-`n/2` bound would be that the
`n/2` floor is an artifact of *degenerate* `2`-term sparsity (a single subgroup coset), and that a
**genuine** `3`-term agreement polynomial (the actual `T = {0,…,k-1} ∪ {a,b}` shape at `k = 1`,
support size `3`) cannot reach `n/2`. The earlier `_FourierSparseZeros` / `_SparseCoeffZeros`
abstract bound only gives the `t = 3` *ceiling* `≤ n(1 − 1/3) = 2n/3`; it says nothing about how
LOW a genuine trinomial can push its physical support (= how HIGH `s*` can go).

**This file refutes that hope.** A genuine, all-three-coefficients-nonzero trinomial supported on
`{0, n/4, n/2}` already reaches the same `n/2` floor. The explicit witness (machine-probed
p-independent for `n = 8,16,32,64`, factoring through the order-4 element `ζ^{n/4}`) is

> `g(X) = (X^{n/4} − 1)·(X^{n/4} − i) = X^{n/2} − (1 + i)·X^{n/4} + i`,  `i := ζ^{n/4}`,

a primitive `4`-th root of unity. As a function on `μ_n`, `(ζ^j)^{n/4} = i^j` runs over the order-4
cyclic group `⟨i⟩`, so `g(ζ^j) = (i^j − 1)(i^j − i) = 0` **iff** `i^j ∈ {1, i}` **iff** `j ≡ 0 or 1
(mod 4)** — exactly `n/2` of the `j ∈ [0,n)`. Its coefficient support is `{0, n/4, n/2}` (genuinely
`3` nonzero terms, since `i ≠ 0`, `1 + i ≠ 0` — `i` has order 4 so `i ≠ −1`, and `i ≠ 1`).

## Honest verdict (rule-3 / rule-4 / rule-6)

* This is a **sharpening of the existing binomial refutation, in the same direction** (a super-Johnson
  LOWER bound on `s*`), not a CORE result. It confirms the `n/2` floor is **structural**, present
  already at the smallest genuine (`t = 3`) sparsity — so no uncertainty/sparse-polynomial route can
  give a sub-`n/2` upper bound on `s*` for `n = 2^μ`. The genuinely open object remains the LIST
  bound (many codewords), where this single-line trinomial contributes only `O(1)` codewords
  (`UncertaintyTwoPowerExtremal`); the prize `δ*` is the list, not `s*`.
* **Thinness:** the witness is `2`-power-specific (it needs the order-4 element `ζ^{n/4}`, i.e. `4 ∣
  n`); over a prime-order group Tao's principle forbids it (`s* = k+1`). So the construction is
  genuinely a `2`-power phenomenon, consistent with the `[349]` Johnson-vs-capacity dichotomy. It is
  NOT a thinness-monotone CORE method — it is a refutation of a would-be upper bound, the honest
  `DISPROOF_LOG` direction.

All `sorry`-free; intended audit `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.UncertaintyTwoPowerTrinomialFloor

open Finset Polynomial
open ProximityGap.UncertaintyTwoPowerJohnsonRefuted

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### A self-contained counting lemma: `#{ j < 4m | j % 4 ∈ {0,1} } = 2m`. -/

/-- The number of naturals `j < 4 * m` with `j % 4 ∈ {0, 1}` is exactly `2 * m`. This is the count
of the two residue classes `0, 1 (mod 4)` selected by the trinomial witness. -/
theorem card_filter_mod_four_lt_two (m : ℕ) :
    ((Finset.range (4 * m)).filter (fun j => j % 4 = 0 ∨ j % 4 = 1)).card = 2 * m := by
  induction m with
  | zero => simp
  | succ t ih =>
      have hstep : Finset.range (4 * (t + 1)) =
          insert (4 * t) (insert (4 * t + 1) (insert (4 * t + 2)
            (insert (4 * t + 3) (Finset.range (4 * t))))) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [hstep, Finset.filter_insert, Finset.filter_insert, Finset.filter_insert,
        Finset.filter_insert]
      have h0 : (4 * t) % 4 = 0 ∨ (4 * t) % 4 = 1 := by omega
      have h1 : (4 * t + 1) % 4 = 0 ∨ (4 * t + 1) % 4 = 1 := by omega
      have h2 : ¬ ((4 * t + 2) % 4 = 0 ∨ (4 * t + 2) % 4 = 1) := by omega
      have h3 : ¬ ((4 * t + 3) % 4 = 0 ∨ (4 * t + 3) % 4 = 1) := by omega
      rw [if_pos h0, if_pos h1, if_neg h2, if_neg h3]
      -- the two surviving insertions add 2 fresh elements to the (= 2t)-size base
      have hmem1 : (4 * t + 1) ∉
          ((Finset.range (4 * t)).filter (fun j => j % 4 = 0 ∨ j % 4 = 1)) := by
        simp only [Finset.mem_filter, Finset.mem_range]; omega
      have hmem0 : (4 * t) ∉ insert (4 * t + 1)
          ((Finset.range (4 * t)).filter (fun j => j % 4 = 0 ∨ j % 4 = 1)) := by
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]; omega
      rw [Finset.card_insert_of_notMem hmem0, Finset.card_insert_of_notMem hmem1, ih]
      ring

/-! ### The order-4 element `i = ζ^{n/4}` and the trinomial root set. -/

/-- For `n = 2^μ` with `μ ≥ 2` and a primitive `n`-th root `ζ`, the element `i := ζ^{n/4}` is a
**primitive 4th root of unity** (`IsPrimitiveRoot i 4`). This is the structural fact that makes the
trinomial `(X^{n/4} − 1)(X^{n/4} − i)` factor through the order-4 cyclic group `⟨i⟩`. -/
theorem primRoot_pow_quarter {μ : ℕ} (hμ : 2 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    IsPrimitiveRoot (ζ ^ (2 ^ μ / 4)) 4 := by
  -- `2^μ / 4 = 2^(μ-2)`, and `2^μ / 2^(μ-2) = 4`.
  have hpne : (2 : ℕ) ^ (μ - 2) ≠ 0 := by positivity
  have hdvd : (2 : ℕ) ^ (μ - 2) ∣ 2 ^ μ := pow_dvd_pow 2 (by omega)
  have hdiv : (2 : ℕ) ^ μ / 4 = 2 ^ (μ - 2) := by
    rcases Nat.exists_eq_add_of_le hμ with ⟨t, ht⟩
    subst ht
    rw [show 2 + t = t + 2 from by omega, pow_add, Nat.add_sub_cancel]
    norm_num
  have hquot : (2 : ℕ) ^ μ / 2 ^ (μ - 2) = 4 := by
    rcases Nat.exists_eq_add_of_le hμ with ⟨t, ht⟩
    subst ht
    have he : (2 + t) - 2 = t := by omega
    rw [he, show 2 + t = t + 2 from by omega, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
    norm_num
  rw [hdiv]
  have := hζ.pow_of_dvd hpne hdvd
  rwa [hquot] at this

/-- `i^j ∈ {1, i}` (where `i` is a primitive 4th root) **iff** `j % 4 ∈ {0, 1}`. The order-4 powers
are `i^0 = 1, i^1 = i, i^2 = -1, i^3 = -i`, all distinct, so membership in `{1, i}` is decided by
`j mod 4`. -/
theorem pow_quarter_mem_iff {i : F} (hi : IsPrimitiveRoot i 4) (j : ℕ) :
    (i ^ j = 1 ∨ i ^ j = i) ↔ (j % 4 = 0 ∨ j % 4 = 1) := by
  -- reduce the exponent mod 4
  have hper : i ^ j = i ^ (j % 4) := by
    conv_lhs => rw [← Nat.div_add_mod j 4, pow_add, pow_mul, hi.pow_eq_one, one_pow, one_mul]
  -- the four distinct powers
  have hi0 : i ^ (0 : ℕ) = 1 := by simp
  have hi1 : i ^ (1 : ℕ) = i := by simp
  have hi2 : i ^ (2 : ℕ) = -1 := by
    have : IsPrimitiveRoot (i ^ (4 / 2)) 2 := hi.pow_of_dvd (by norm_num) (by norm_num)
    simpa using this.eq_neg_one_of_two_right
  have hi3 : i ^ (3 : ℕ) = -i := by
    have h22 : i ^ (2 : ℕ) = -1 := hi2
    calc i ^ (3 : ℕ) = i ^ (2 : ℕ) * i := by ring
      _ = -1 * i := by rw [h22]
      _ = -i := by ring
  -- `-1 ≠ 1` and `-i ∉ {1, i}` from primitivity (`i` has order 4, char ≠ 2)
  have hne11 : (-1 : F) ≠ 1 := by
    intro h
    have hord : i ^ (2 : ℕ) = 1 := by rw [hi2, h]
    have hdvd : (4 : ℕ) ∣ 2 := (hi.pow_eq_one_iff_dvd 2).mp hord
    omega
  have hi_ne1 : i ≠ 1 := by
    intro h
    have : (4 : ℕ) ∣ 1 := (hi.pow_eq_one_iff_dvd 1).mp (by rw [pow_one, h])
    omega
  have hni_ne1 : (-i : F) ≠ 1 := by
    intro h; rw [← hi3] at h
    have : (4 : ℕ) ∣ 3 := (hi.pow_eq_one_iff_dvd 3).mp h
    omega
  have hi_ne0 : i ≠ 0 := by
    intro h0
    have hpow : i ^ 4 = 1 := hi.pow_eq_one
    rw [h0] at hpow
    simp at hpow
  have hni_nei : (-i : F) ≠ i := by
    intro h
    have h2i : (2 : F) * i = 0 := by linear_combination (-1 : F) * h
    rcases mul_eq_zero.mp h2i with h2 | hi0'
    · exact hne11 (by linear_combination (-1 : F) * h2)
    · exact hi_ne0 hi0'
  -- `i^2 = -1 ∉ {1, i}` and `i^3 = -i ∉ {1, i}`
  have hneg1_nei : (-1 : F) ≠ i := by
    intro h
    -- -1 = i ⇒ i^2 = 1, contradicting order 4
    have hsq : i ^ (2 : ℕ) = 1 := by rw [← h]; ring
    have : (4 : ℕ) ∣ 2 := (hi.pow_eq_one_iff_dvd 2).mp hsq
    omega
  rw [hper]
  -- case on `j % 4 < 4`
  have hlt : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (j % 4)
  · simp [hi0]
  · simp [hi1]
  · simp only [hi2]
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rcases hc with hc | hc
      · exact absurd hc hne11
      · exact absurd hc hneg1_nei
    · omega
  · simp only [hi3]
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rcases hc with hc | hc
      · exact absurd hc hni_ne1
      · exact absurd hc hni_nei
    · omega

/-- **The trinomial root-count (the load-bearing real-object fact).** For `n = 2^μ` (`μ ≥ 2`) and a
primitive `n`-th root `ζ`, with `i := ζ^{n/4}` (a primitive 4th root), the genuine TRINOMIAL
`g(X) = (X^{n/4} − 1)(X^{n/4} − i)` has EXACTLY `n/2` roots among the `n`-th roots of unity
`{ζ^j : 0 ≤ j < n}`. Concretely `#{ j < n | (ζ^j)^{n/4} ∈ {1, i} } = n/2`, because
`(ζ^j)^{n/4} = i^j ∈ {1, i} ⟺ j % 4 ∈ {0,1}`, exactly half of `[0,n)`. -/
theorem card_trinomial_roots_eq {μ : ℕ} (hμ : 2 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    (((Finset.range (2 ^ μ)).filter
        (fun j => (ζ ^ j) ^ (2 ^ μ / 4) = 1 ∨ (ζ ^ j) ^ (2 ^ μ / 4) = ζ ^ (2 ^ μ / 4))).card)
      = 2 ^ μ / 2 := by
  set i := ζ ^ (2 ^ μ / 4) with hi_def
  have hi : IsPrimitiveRoot i 4 := primRoot_pow_quarter hμ hζ
  -- rewrite predicate `(ζ^j)^{n/4} ∈ {1,i}` as `i^j ∈ {1,i}`
  have hpow : ∀ j, (ζ ^ j) ^ (2 ^ μ / 4) = i ^ j := by
    intro j; rw [hi_def, ← pow_mul, Nat.mul_comm, pow_mul]
  have hset : ((Finset.range (2 ^ μ)).filter
      (fun j => (ζ ^ j) ^ (2 ^ μ / 4) = 1 ∨ (ζ ^ j) ^ (2 ^ μ / 4) = i))
      = (Finset.range (2 ^ μ)).filter (fun j => j % 4 = 0 ∨ j % 4 = 1) := by
    apply Finset.filter_congr
    intro j _
    rw [hpow j]
    exact pow_quarter_mem_iff hi j
  rw [hset]
  -- count: n = 2^μ = 4 * (2^(μ-2)), and n/2 = 2 * 2^(μ-2)
  rcases Nat.exists_eq_add_of_le hμ with ⟨t, ht⟩
  subst ht
  have hn4 : (2 : ℕ) ^ (2 + t) = 4 * 2 ^ t := by rw [pow_add]; ring
  rw [hn4]
  rw [card_filter_mod_four_lt_two (2 ^ t)]
  -- n/2 = (4 * 2^t)/2 = 2 * 2^t
  omega

/-! ### Genuine (3-term) sparsity: all three coefficients are nonzero. -/

/-- The witness is a GENUINE trinomial: in `g(X) = X^{n/2} − (1+i)·X^{n/4} + i` the constant term
`i` and the middle coefficient `1 + i` are both nonzero (`i` is a primitive 4th root, so `i ≠ 0` and
`i ≠ −1`). Together with the leading `X^{n/2}` this gives support size exactly `3` (the three
exponents `0, n/4, n/2` are distinct for `μ ≥ 2`). -/
theorem witness_coeffs_nonzero {μ : ℕ} (hμ : 2 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    (ζ ^ (2 ^ μ / 4)) ≠ 0 ∧ (1 + ζ ^ (2 ^ μ / 4)) ≠ 0 := by
  have hi : IsPrimitiveRoot (ζ ^ (2 ^ μ / 4)) 4 := primRoot_pow_quarter hμ hζ
  refine ⟨?_, ?_⟩
  · intro h0
    have hpow : (ζ ^ (2 ^ μ / 4)) ^ 4 = 1 := hi.pow_eq_one
    rw [h0] at hpow
    simp at hpow
  · -- `1 + i = 0 ⟺ i = -1 ⟺ i^2 = 1`, contradicting order 4
    intro h
    have hineg : ζ ^ (2 ^ μ / 4) = -1 := by linear_combination h
    have hsq : (ζ ^ (2 ^ μ / 4)) ^ (2 : ℕ) = 1 := by rw [hineg]; ring
    have : (4 : ℕ) ∣ 2 := (hi.pow_eq_one_iff_dvd 2).mp hsq
    omega

/-! ### The refutation packaged: `s* ≥ n/2` already at GENUINE `t = 3` sparsity. -/

/-- **THE SHARPENED REFUTATION.** A genuine TRINOMIAL (support `{0, n/4, n/2}`, all three
coefficients nonzero) already reaches `s* ≥ n/2` on `μ_{2^μ}` (`μ ≥ 2`). So the `n/2` sparse-zero
floor is NOT an artifact of degenerate `2`-term (single-coset) sparsity; it is present at the
smallest genuine sparsity, and at rate `ρ = k/n < 1/4` it exceeds the Johnson radius (`(n/2)² >
k·n ⟺ n > 4k`). No uncertainty / sparse-polynomial route can give a sub-`n/2`, let alone
sub-Johnson, upper bound on `s*` for `n = 2^μ`. -/
theorem trinomial_sStar_ge_half {μ k : ℕ} (hμ : 2 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (hrate : 4 * k < 2 ^ μ) :
    ∃ s₀ : ℕ,
      s₀ = (((Finset.range (2 ^ μ)).filter
        (fun j => (ζ ^ j) ^ (2 ^ μ / 4) = 1 ∨
                  (ζ ^ j) ^ (2 ^ μ / 4) = ζ ^ (2 ^ μ / 4))).card) ∧
      s₀ = 2 ^ μ / 2 ∧ k * 2 ^ μ < s₀ ^ 2 := by
  refine ⟨_, rfl, card_trinomial_roots_eq hμ hζ, ?_⟩
  rw [card_trinomial_roots_eq hμ hζ]
  -- identical arithmetic to the binomial case: k·n < (n/2)² since 4k < n and n even.
  have heven : Even (2 ^ μ) := (Nat.even_pow' (by omega)).2 (by norm_num)
  obtain ⟨m, hm⟩ := heven
  have hnm : (2 : ℕ) ^ μ = 2 * m := by omega
  have hhalf : (2 : ℕ) ^ μ / 2 = m := by omega
  rw [hhalf]
  have h2km : 2 * k < m := by omega
  have hkey : k * 2 ^ μ = (2 * k) * m := by rw [hnm]; ring
  calc k * 2 ^ μ = (2 * k) * m := hkey
    _ < m * m := by nlinarith [h2km]
    _ = m ^ 2 := by ring

/-- **Summary `example`.** Over a real field `F` with a genuine primitive `2^μ`-th root `ζ`
(`μ ≥ 2`), the genuine trinomial `(X^{n/4} − 1)(X^{n/4} − ζ^{n/4})` — all three coefficients nonzero
— has exactly `n/2` roots in `μ_n`, exceeding the Johnson radius at rate `< 1/4`. The `n/2` floor is
structural at the smallest genuine (`t = 3`) sparsity. -/
example {μ k : ℕ} (hμ : 2 ≤ μ) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (hrate : 4 * k < 2 ^ μ) :
    (ζ ^ (2 ^ μ / 4)) ≠ 0 ∧ (1 + ζ ^ (2 ^ μ / 4)) ≠ 0 ∧
    ∃ s₀ : ℕ, s₀ = 2 ^ μ / 2 ∧ k * 2 ^ μ < s₀ ^ 2 :=
  ⟨(witness_coeffs_nonzero hμ hζ).1, (witness_coeffs_nonzero hμ hζ).2,
   let ⟨s₀, _, heq, h⟩ := trinomial_sStar_ge_half hμ hζ hrate; ⟨s₀, heq, h⟩⟩

-- Axiom audit: `[propext, Classical.choice, Quot.sound]` (axiom-clean, no `sorryAx`).
#print axioms card_trinomial_roots_eq
#print axioms trinomial_sStar_ge_half
#print axioms witness_coeffs_nonzero

end ProximityGap.UncertaintyTwoPowerTrinomialFloor
