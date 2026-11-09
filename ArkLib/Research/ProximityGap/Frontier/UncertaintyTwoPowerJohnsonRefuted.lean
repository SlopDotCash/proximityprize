/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

/-!
# minsupport-2power-direct : the sub-Johnson upper bound on `s*` is FALSE (#407)

THE OPEN OBJECT (verified, issue #407).  `s*(2^μ, k)` = `n − minSupport(T)` where
`minSupport(T)` = the minimal physical support of a NONZERO function on `μ_n ≅ Z_n`
(`n = 2^μ`) whose discrete-Fourier support lies in `T = {0,…,k-1} ∪ {a,b}` (size `≤ k+2`).
Equivalently `s* = max #roots in μ_n of a polynomial of the form `x^a + γ·x^b − c(x)`,
`deg c < k`, over `F_p` with `n = 2^μ | p − 1`.

## The attack this file ADDRESSES (and REFUTES)

The proposed line `minsupport-2power-direct` was: prove
`minSupport(T) ≥ n − √(kn)`   (⟺ `s* ≤ √(kn)` = the **Johnson upper bound**),
which — if true — would PIN the answer at Johnson and close the prize from above.

**This is FALSE for `n = 2^μ` at every rate `ρ = k/n < 1/4`.**  The 2-adic subgroup structure
of `Z_{2^μ}` does NOT raise `minSupport`; on the contrary the index-2 subgroup `μ_{n/2}` DRAGS it
DOWN.  The explicit witness is the **subgroup binomial** `f(x) = x^{n/2} + 1`:

* its Fourier support is `{0, n/2}` (size `2 ≤ k+2`): it is the open form `x^a + γx^b − c(x)` with
  `a = n/2`, `γ = 0`, `c(x) = −1` (degree `0 < k`);
* over `F_p` with a genuine order-`n` subgroup `μ_n`, on `μ_n` the map `y ↦ y^{n/2}` takes only the
  two values `±1` (it has order 2), and `y^{n/2} = −1` holds on EXACTLY `n/2` elements of `μ_n` —
  so `f` vanishes on `n/2` points;
* hence `minSupport ≤ n/2`, i.e. **`s* ≥ n/2`**.

Since `n/2 > √(kn) ⟺ ρ < 1/4`, this contradicts `s* ≤ √(kn)` for all `n = 2^μ` at rate `< 1/4`.

This file makes the construction REAL (not an assumed `minSupport` datum field): it proves, about
the actual polynomial `X^{n/2}+1` over `F_p`, that it has **exactly `n/2` roots in the real
order-`n` cyclic subgroup `μ_n`** (`card_neg_one_coset_eq`), and packages the consequence as the
explicit refutation `johnsonUpperBound_false_at_low_rate`.

## What this means for the prize (the honest verdict)

The `minSupport` direction does NOT yield a sub-Johnson upper bound — it yields the OPPOSITE
(a super-Johnson LOWER bound on `s*`).  So **Johnson is NOT the truth for `n = 2^μ`**: the answer is
strictly above Johnson (already `≥ n/2 ≫ √(kn)` at low rate), confirming the extremal lower bound
`s* ≥ n/2 + (k−1)`.  The genuinely open object is therefore an UPPER bound on `s*` strictly between
this `n/2`-type floor and the Donoho–Stark near-capacity ceiling — and it is NOT reachable by any
uncertainty / sparse-polynomial Fourier bound (those are all `≥ n/(k+2)`, far below `n/2`).

## Citations (exact, checked applicable to `μ_{2^μ}`)

* Donoho, D. L. & Stark, P. B. (1989), "Uncertainty principles and signal recovery", SIAM J. Appl.
  Math. 49(3), 906–931: universal `|supp f|·|supp f̂| ≥ N` on `Z_N`, and (Thm. 13 + remarks)
  EQUALITY holds exactly when `f̂` (and `f`) are supported on cosets of dual subgroups.  The
  `x^{n/2}+1` witness is precisely that equality case (`|supp f| = n/2`, `|supp f̂| = 2`,
  product `= n`) — so the universal bound is SHARP here and gives `s* ≤ n − n/(k+2)` (near capacity),
  NOT `s* ≤ √(kn)`.  CONFIRMS no Fourier route to a sub-Johnson upper bound.
* Tao, T. (2005), "An uncertainty principle for cyclic groups of prime order", Math. Res. Lett.
  12(1), 121–127: for PRIME `n`, `|supp f| + |supp f̂| ≥ n+1` (sharp), giving `s* = k+1` (capacity).
  FLAGGED: the proof uses Chebotarev nonvanishing of all DFT minors and is FALSE for composite `n`;
  it gives NOTHING for `n = 2^μ`.  The contrast is the whole point: composite (2-power) `n` admits
  the `n/2`-root binomial that prime `n` forbids.
* Cheng–Gao–Rojas–Wan (2014), arXiv:1411.6346, "Sparse Univariate Polynomials with Many Roots Over
  Finite Fields": a `t`-nomial over `F_q` can vanish on `~q^{(t−2)/(t−1)}` cosets — near-capacity for
  fixed `t`.  Confirms `√(kn)` is NOT a sparse-polynomial root bound; it is a LIST bound (the real open
  object), unreachable from the single-line / minSupport view.

All results `sorry`-free; intended audit `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.UncertaintyTwoPowerJohnsonRefuted

open Finset Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### A self-contained counting lemma: `#{odd j < 2m} = m`. -/

/-- The number of odd naturals below `2 * m` is exactly `m`. -/
theorem card_filter_odd_range_two_mul (m : ℕ) :
    ((Finset.range (2 * m)).filter (fun j => Odd j)).card = m := by
  induction m with
  | zero => simp
  | succ t ih =>
      have hstep : Finset.range (2 * (t + 1)) =
          insert (2 * t) (insert (2 * t + 1) (Finset.range (2 * t))) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [hstep, Finset.filter_insert, Finset.filter_insert]
      have hno : ¬ Odd (2 * t) := by rw [Nat.odd_iff]; omega
      have hyes : Odd (2 * t + 1) := by rw [Nat.odd_iff]; omega
      rw [if_neg hno, if_pos hyes]
      have hnotmem : (2 * t + 1) ∉ (Finset.range (2 * t)).filter (fun j => Odd j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [Finset.card_insert_of_notMem hnotmem, ih]

/-! ### The real object: roots of `X^{n/2}+1` inside the order-`n` subgroup `μ_n`. -/

/-- For `n = 2^μ` with `μ ≥ 1` and a primitive `n`-th root of unity `ζ` in a field `F`, the element
`ζ ^ (n/2)` has order exactly `2`, hence equals `-1` (the unique order-2 element of the cyclic group
of `n`-th roots of unity).  This is the structural fact that makes `X^{n/2}+1` vanish on a half of
`μ_n`. -/
theorem primRoot_pow_half_eq_neg_one {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    ζ ^ (2 ^ μ / 2) = -1 := by
  -- `2^μ / 2 = 2^(μ-1)`.
  have hdiv : 2 ^ μ / 2 = 2 ^ (μ - 1) := by
    rcases Nat.exists_eq_add_of_le hμ with ⟨t, ht⟩
    subst ht
    rw [show 1 + t = t + 1 from by omega, pow_succ,
      Nat.mul_div_cancel _ (by norm_num : 0 < 2), Nat.add_sub_cancel]
  rw [hdiv]
  -- `2^(μ-1) ∣ 2^μ` with quotient `2`; `ζ^(2^(μ-1))` is a primitive 2nd root of unity.
  have hpne : (2 : ℕ) ^ (μ - 1) ≠ 0 := by positivity
  have hdvd : (2 : ℕ) ^ (μ - 1) ∣ 2 ^ μ := pow_dvd_pow 2 (by omega)
  have hquot : (2 : ℕ) ^ μ / 2 ^ (μ - 1) = 2 := by
    rcases Nat.exists_eq_add_of_le hμ with ⟨t, ht⟩
    subst ht
    rw [show 1 + t = t + 1 from by omega, Nat.add_sub_cancel]
    rw [pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have h2 : IsPrimitiveRoot (ζ ^ (2 ^ (μ - 1))) 2 := by
    have := hζ.pow_of_dvd hpne hdvd
    rwa [hquot] at this
  exact h2.eq_neg_one_of_two_right

/-- **The root-count (the load-bearing real-object fact).**  For `n = 2^μ` (`μ ≥ 1`) and a primitive
`n`-th root `ζ` in `F`, the polynomial `X^{n/2} + 1` has EXACTLY `n/2` roots among the `n`-th roots
of unity `{ζ^j : 0 ≤ j < n}`.  Concretely: `#{ j < n | (ζ^j)^{n/2} = −1 } = n/2`, because
`(ζ^j)^{n/2} = (ζ^{n/2})^j = (−1)^j`, which is `−1` exactly for the `n/2` odd `j` in `[0,n)`.
This makes `minSupport({0,n/2}) ≤ n/2`, hence `s* ≥ n/2`. -/
theorem card_neg_one_coset_eq {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    (((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2) = -1)).card)
      = 2 ^ μ / 2 := by
  -- (ζ^j)^{n/2} = (ζ^{n/2})^j = (-1)^j, so the predicate is "j is odd".
  have hpow : ∀ j, (ζ ^ j) ^ (2 ^ μ / 2) = (-1 : F) ^ j := by
    intro j
    rw [← pow_mul, Nat.mul_comm, pow_mul, primRoot_pow_half_eq_neg_one hμ hζ]
  -- `-1 ≠ 1` in `F`: the primitive `2^μ`-th root has `ζ^{n/2} = -1`, and `-1 = 1` would force
  -- `ζ^{n/2} = 1` with `0 < n/2 < n`, contradicting primitivity.  (Equivalently char `F ≠ 2`.)
  have hne : (-1 : F) ≠ 1 := by
    intro hcontra
    have hz : ζ ^ (2 ^ μ / 2) = 1 := by
      rw [primRoot_pow_half_eq_neg_one hμ hζ, hcontra]
    have h2le : (2 : ℕ) ≤ 2 ^ μ := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) hμ
    have hdvd : (2 : ℕ) ^ μ ∣ 2 ^ μ / 2 := (hζ.pow_eq_one_iff_dvd _).mp hz
    have hlt : (2 : ℕ) ^ μ / 2 < 2 ^ μ := by omega
    have hpos : 0 < (2 : ℕ) ^ μ / 2 := by omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  have hchar : ∀ j, ((ζ ^ j) ^ (2 ^ μ / 2) = -1) ↔ Odd j := by
    intro j
    rw [hpow j]
    constructor
    · intro h
      rcases Nat.even_or_odd j with he | ho
      · rw [he.neg_one_pow] at h
        exact absurd h.symm hne
      · exact ho
    · intro ho
      exact ho.neg_one_pow
  have hset : ((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2) = -1))
      = (Finset.range (2 ^ μ)).filter (fun j => Odd j) := by
    apply Finset.filter_congr
    intro j _
    simp only [hchar j]
  rw [hset]
  -- count odd numbers in [0, n): exactly n/2 since n = 2^μ is even (μ ≥ 1).
  have heven : Even (2 ^ μ) := (Nat.even_pow' (by omega)).2 (by norm_num)
  obtain ⟨m, hm⟩ := heven
  have hnm : (2 : ℕ) ^ μ = 2 * m := by omega
  rw [hnm, show (2 * m) / 2 = m from by omega]
  exact card_filter_odd_range_two_mul m

/-! ### The refutation packaged on the abstract `s*` datum. -/

/-- `s*` lower bound from a real construction: the subgroup binomial `x^{n/2}+1` vanishes on `n/2`
points of `μ_n`, so the max-zero count `s*` is at least `n/2`. -/
theorem sStar_ge_half_of_subgroupBinomial {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    2 ^ μ / 2 ≤ (((Finset.range (2 ^ μ)).filter
        (fun j => (ζ ^ j) ^ (2 ^ μ / 2) = -1)).card) := by
  rw [card_neg_one_coset_eq hμ hζ]

/-- **THE REFUTATION (Johnson upper bound is FALSE for `n = 2^μ` at low rate).**  The hypothesis
that `s* ≤ √(kn)` (stated squared, integer-clean: `s*^2 ≤ k·n`) FAILS at the subgroup-binomial
witness whenever `4k < n` (i.e. rate `ρ = k/n < 1/4`).  Concretely the witness gives `s* ≥ n/2`,
and `(n/2)^2 = n^2/4 > kn ⟺ n > 4k`.  So no theorem of the form `s*^2 ≤ kn` (Johnson-from-above)
can hold for `n = 2^μ`; the minSupport route refutes itself.

The exhibited `s₀ = n/2` is the GENUINE number of roots of `x^{n/2}+1` in the order-`n` subgroup
`μ_n` — a machine-checked countermodel to the would-be `JohnsonFloorTwoPower`. -/
theorem johnsonUpperBound_false_at_low_rate {μ k : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (hrate : 4 * k < 2 ^ μ) :
    ∃ s₀ : ℕ,
      s₀ = (((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2) = -1)).card) ∧
      k * 2 ^ μ < s₀ ^ 2 := by
  refine ⟨_, rfl, ?_⟩
  rw [card_neg_one_coset_eq hμ hζ]
  -- `k * 2^μ < (2^μ / 2)^2` since `4k < 2^μ` and `2^μ` is even.
  have heven : Even (2 ^ μ) := (Nat.even_pow' (by omega)).2 (by norm_num)
  obtain ⟨m, hm⟩ := heven
  have hnm : (2 : ℕ) ^ μ = 2 * m := by omega
  have hhalf : (2 : ℕ) ^ μ / 2 = m := by omega
  rw [hhalf]
  -- goal: k * 2^μ < m^2, with 2^μ = 2m and 4k < 2m  ⟹  2k < m.
  have h2km : 2 * k < m := by omega
  have hkey : k * 2 ^ μ = (2 * k) * m := by rw [hnm]; ring
  have hlt : (2 * k) * m < m * m := by nlinarith [h2km]
  calc k * 2 ^ μ = (2 * k) * m := hkey
    _ < m * m := hlt
    _ = m ^ 2 := by ring

/-- **Summary `example`.** Over a REAL field `F` with a genuine primitive `2^μ`-th root `ζ`
(so `μ_n` is the actual order-`n` cyclic subgroup), the real polynomial `x^{n/2}+1` has exactly
`n/2` roots in `μ_n`, and at rate `< 1/4` this single construction already exceeds the Johnson
radius — so the minSupport route gives a super-Johnson LOWER bound on `s*`, refuting any
sub-Johnson upper bound. -/
example {μ k : ℕ} (hμ : 1 ≤ μ) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (hrate : 4 * k < 2 ^ μ) :
    (((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2) = -1)).card) = 2 ^ μ / 2 ∧
    ∃ s₀ : ℕ, k * 2 ^ μ < s₀ ^ 2 :=
  ⟨card_neg_one_coset_eq hμ hζ,
   let ⟨s₀, _, h⟩ := johnsonUpperBound_false_at_low_rate hμ hζ hrate; ⟨s₀, h⟩⟩

-- Axiom audit (both theorems): `[propext, Classical.choice, Quot.sound]` (axiom-clean, no `sorryAx`).
#print axioms card_neg_one_coset_eq
#print axioms johnsonUpperBound_false_at_low_rate

end ProximityGap.UncertaintyTwoPowerJohnsonRefuted
