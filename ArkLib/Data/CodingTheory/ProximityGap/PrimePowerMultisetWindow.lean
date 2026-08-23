/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedWindowLaw

/-!
# Corrected hypothesis A4 (O124): THE PRIME-POWER MULTISET WINDOW LAW

O124 (DISPROOF_LOG) resolved the A4 trichotomy: the ℕ-weight (multiset) window law is
FALSE at general `n` (Conway–Jones (5:6) minimal sum at `n = 30`), open-≡-K5 at two
genuine primes, and TRUE at prime powers in all probes.  This file lands the
prime-power case as theorems, in the in-tree windowed language
(`DeBruijnWeightedWindowLaw`), at BOTH window depths asked by the corrected target:

* `weightedLevelDecomposes_of_dvd_prime_pow` — every divisor level of `p^k`
  weighted-level-decomposes (the O96 periodicity brick at levels `p^(c+1)`, trivially at
  level 1).  Standalone: no auxiliary second prime is smuggled in.
* `weighted_windowed_prime_pow` — **the general-`t` prime-power multiset window law**:
  for `n = p^k`, `ζ` a primitive `n`-th root of unity in a characteristic-zero field,
  `w : ℕ → ℕ`, `t < n`: the power-sum window `1 ≤ j ≤ t` vanishes **iff** `w` is an
  ℕ-combination of `μ_d`-coset indicators with `d ∣ n`, `d > t`.  The cross-fiber
  recombination (the O124 skeleton's "stretch" step — e.g. at `n = 8`, `t = 2` two
  antipodal pairs recombining into a full `γμ₄`) is exactly what the in-tree O108
  induction (`window_step`'s resonance/merge) performs; instantiating its level
  interface at prime powers makes the whole `t`-ladder unconditional here.
* `multiset_window_law_t1` — **the `t = 1` law in μ_p-coset-indicator form**
  (the A3-relevant base case, ZMod-indexed): for `a : ZMod (p^(k+1)) → ℕ`,
  `Σ_j a_j ζ^j = 0  ↔  a` is an ℕ-combination of full μ_p-coset indicator weights
  (`IsMupCosetCombination`); equivalently (`isMupCosetCombination_iff_factors`) `a`
  factors through the coset-base reduction `ZMod (p^(k+1)) → ZMod (p^k)` — at `p = 2`
  these cosets are exactly the antipodal pairs `{j, j + 2^k}`.  Forward direction:
  the O96 weighted prime-power packet theorem
  (`WeightedPrimePowerPacket.weight_replicated_of_vanishing`) gives `p^k`-shift
  periodicity; iterating the shift collapses each μ_p-fiber to its base.  Converse:
  factored weights are shift-periodic, so the O96 converse applies.

## Honest provenance

The heavy bricks are in-tree (O96 `WeightedPrimePowerPacket`, O108
`DeBruijnWeightedWindowLaw`); what was missing and is added here is (i) the prime-power
level discharge as a standalone theorem, (ii) the standalone prime-power instantiation
of the windowed law (previously only the two-prime form `weighted_windowed_two_prime`
existed, which covers `p^a·q^0` only by supplying an artificial second prime), and
(iii) the corrected-A4 packaging of `t = 1` as a μ_p-coset-indicator ℕ-combination on
`ZMod (p^(k+1))` with both directions.  The k = 1 base subtlety flagged in O124 (the
all-ones relation IS the coset indicator, so ℕ-coefficients survive) is visible here as
`k = 0`: the base ring is `ZMod (p^0) = ZMod 1`, the factored weight is a constant, and
the constant is the (ℕ-valued) multiplicity of the single full μ_p-coset.

Setting matches the in-tree windowed machinery: `[Field L] [CharZero L]` with
`IsPrimitiveRoot ζ (p^k)`.  (Characteristic zero is load-bearing: over `𝔽_17` with
`ζ = 2`, `a = (17,0,…,0)` on `ZMod 8` has vanishing sum but is not coset-constant.)
-/

namespace PrimePowerMultisetWindow

open Finset

variable {L : Type*} [Field L]

/-! ## The weighted level interface at prime-power moduli -/

/-- **Every divisor level of a prime power weighted-level-decomposes**: O96's
periodicity theorem at levels `p^(c+1)`, trivially at level `1`.  Standalone
prime-power form of `weightedLevelDecomposes_of_dvd_two_prime` (no second prime). -/
theorem weightedLevelDecomposes_of_dvd_prime_pow [CharZero L]
    {p k : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ∣ p ^ k) :
    DeBruijnWeightedWindowLaw.WeightedLevelDecomposes L m := by
  intro ξ hξ v hsum
  obtain ⟨c, _hck, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · -- level p^0 = 1: the single weight is zero, the prime-factor sum is empty
    refine ⟨fun _ _ => 0, fun r hr => ?_⟩
    rw [pow_zero] at hr hsum
    interval_cases r
    rw [pow_zero, Nat.primeFactors_one, Finset.sum_empty]
    have h0 : (v 0 : L) = 0 := by simpa using hsum
    exact_mod_cast h0
  · -- level p^(c'+1): O96 periodicity, combination coefficients literally the weights
    obtain ⟨c', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcpos.ne'
    have hper := DeBruijnWeightedWindowLaw.weightedLevel_prime_pow hp hξ v hsum
    refine ⟨fun _ r => v r, fun r hr => ?_⟩
    have hpf : (p ^ (c' + 1)).primeFactors = {p} := by
      rw [Nat.primeFactors_pow _ (Nat.succ_ne_zero c'), hp.primeFactors]
    have hdiv : p ^ (c' + 1) / p = p ^ c' := by
      rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
    rw [hpf, Finset.sum_singleton, hdiv]
    exact hper r hr

/-! ## The general-t prime-power multiset window law (corrected A4, full ladder) -/

/-- **THE PRIME-POWER MULTISET WINDOW LAW** (corrected A4, O124; general `t`): for
`n = p^k`, `ζ` a primitive `n`-th root of unity in characteristic zero, `w : ℕ → ℕ`,
`t < n`: the power-sum window `1 ≤ j ≤ t` vanishes **iff** `w` is an ℕ-combination
of `μ_d`-coset indicators with `d ∣ p^k`, `d > t`.  The cross-fiber recombination of
the O124 proof skeleton is the in-tree O108 induction; this instantiates its level
interface at prime powers.  Probe-verified (O124: `n = 8`, `t = 1,2,3`; `n = 9`,
`t = 1,2`; zero counterexamples). -/
theorem weighted_windowed_prime_pow [CharZero L]
    {p k : ℕ} (hp : p.Prime)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ k)) (w : ℕ → ℕ)
    {t : ℕ} (htn : t < p ^ k) :
    (∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ k), (w e : L) * ζ ^ (j * e) = 0) ↔
      DeBruijnWeightedWindowLaw.IsWeightedWindowCombination (p ^ k) t w :=
  DeBruijnWeightedWindowLaw.weighted_windowed_law
    (fun _ hm => weightedLevelDecomposes_of_dvd_prime_pow hp hm) hζ w htn

/-! ## t = 1 in μ_p-coset-indicator form (ZMod-indexed, the A3-relevant base) -/

variable {p k : ℕ}

/-- The coset-base reduction `ZMod (p^(k+1)) → ZMod (p^k)`.  Its fibers are exactly
the exponent sets of rotated full μ_p-cosets `{j, j + p^k, …, j + (p−1)p^k}` (at
`p = 2`: the antipodal pairs). -/
def cosetBase (p k : ℕ) : ZMod (p ^ (k + 1)) →+* ZMod (p ^ k) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))

lemma cosetBase_apply [NeZero (p ^ (k + 1))] (j : ZMod (p ^ (k + 1))) :
    cosetBase p k j = ((j.val : ℕ) : ZMod (p ^ k)) := by
  unfold cosetBase
  rw [ZMod.castHom_apply, ZMod.natCast_val]

lemma cosetBase_val [NeZero (p ^ (k + 1))] [NeZero (p ^ k)] (j : ZMod (p ^ (k + 1))) :
    (cosetBase p k j).val = j.val % p ^ k := by
  rw [cosetBase_apply, ZMod.val_natCast]

/-- The indicator weight of the full μ_p-coset of exponents over base `c`:
`1` on the `p` exponents `{j : j ≡ c mod p^k}`, `0` elsewhere. -/
def mupCosetIndicator (p k : ℕ) (c : ZMod (p ^ k)) : ZMod (p ^ (k + 1)) → ℕ :=
  fun j => if cosetBase p k j = c then 1 else 0

/-- `a` is an **ℕ-combination of full μ_p-coset indicator weights**. -/
def IsMupCosetCombination (p k : ℕ) [NeZero (p ^ k)]
    (a : ZMod (p ^ (k + 1)) → ℕ) : Prop :=
  ∃ m : ZMod (p ^ k) → ℕ,
    ∀ j, a j = ∑ c : ZMod (p ^ k), m c * mupCosetIndicator p k c j

/-- Evaluating an indicator combination: only the coset containing `j` contributes. -/
lemma combination_apply [NeZero (p ^ k)] (m : ZMod (p ^ k) → ℕ)
    (j : ZMod (p ^ (k + 1))) :
    ∑ c : ZMod (p ^ k), m c * mupCosetIndicator p k c j = m (cosetBase p k j) := by
  simp only [mupCosetIndicator, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- The combination form is exactly factoring through the coset-base reduction. -/
lemma isMupCosetCombination_iff_factors [NeZero (p ^ k)]
    (a : ZMod (p ^ (k + 1)) → ℕ) :
    IsMupCosetCombination p k a
      ↔ ∃ m : ZMod (p ^ k) → ℕ, ∀ j, a j = m (cosetBase p k j) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, fun j => by rw [hm j]; exact combination_apply m j⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, fun j => by rw [hm j]; exact (combination_apply m j).symm⟩

/-- **THE PRIME-POWER MULTISET WINDOW LAW AT `t = 1`, μ_p-COSET FORM** (corrected A4
base case, O124): for `ζ` a primitive `p^(k+1)`-th root of unity in characteristic
zero and `a : ZMod (p^(k+1)) → ℕ`, the weighted sum `Σ_j a_j ζ^j` vanishes **iff**
`a` is an ℕ-combination of full μ_p-coset indicators.  At `p = 2` the cosets are the
antipodal pairs `{j, j + 2^k}`; at `k = 0` the unique coset is all of μ_p and the
factored weight is the constant multiplicity (the all-ones relation — ℕ-coefficients
survive, as the O124 base-case analysis requires). -/
theorem multiset_window_law_t1 [CharZero L] (hp : p.Prime)
    [NeZero (p ^ (k + 1))] [NeZero (p ^ k)]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (a : ZMod (p ^ (k + 1)) → ℕ) :
    (∑ j : ZMod (p ^ (k + 1)), (a j : L) * ζ ^ (ZMod.val j) = 0)
      ↔ IsMupCosetCombination p k a := by
  rw [isMupCosetCombination_iff_factors]
  constructor
  · -- forward: O96 periodicity, iterated to fiber collapse
    intro hsum
    have hper := WeightedPrimePowerPacket.weight_replicated_of_vanishing hp hζ hsum
    have hiter : ∀ (i : ℕ) (e : ZMod (p ^ (k + 1))),
        a (e + ((i * p ^ k : ℕ) : ZMod (p ^ (k + 1)))) = a e := by
      intro i
      induction i with
      | zero => intro e; simp
      | succ i IH =>
        intro e
        have hsplit : ((i + 1) * p ^ k : ℕ) = i * p ^ k + p ^ k := by ring
        rw [hsplit, Nat.cast_add, ← add_assoc,
          hper (e + ((i * p ^ k : ℕ) : ZMod (p ^ (k + 1))))]
        exact IH e
    refine ⟨fun c => a ((c.val : ZMod (p ^ (k + 1)))), fun j => ?_⟩
    have hj2 : j = ((j.val % p ^ k : ℕ) : ZMod (p ^ (k + 1)))
        + (((j.val / p ^ k) * p ^ k : ℕ) : ZMod (p ^ (k + 1))) := by
      rw [← Nat.cast_add, Nat.mod_add_div']
      exact (ZMod.natCast_rightInverse j).symm
    have key : a (((j.val % p ^ k : ℕ) : ZMod (p ^ (k + 1)))) = a j := by
      conv_rhs => rw [hj2]
      exact (hiter (j.val / p ^ k)
        (((j.val % p ^ k : ℕ) : ZMod (p ^ (k + 1))))).symm
    dsimp only
    rw [cosetBase_val]
    exact key.symm
  · -- converse: factored weights are p^k-shift-periodic; O96 converse
    rintro ⟨m, hm⟩
    refine WeightedPrimePowerPacket.vanishing_of_weight_replicated hp hζ ?_
    intro e
    rw [hm, hm]
    congr 1
    have hzero : cosetBase p k (((p ^ k : ℕ) : ZMod (p ^ (k + 1)))) = 0 := by
      rw [map_natCast, ZMod.natCast_self]
    rw [map_add, hzero, add_zero]

/-- The corrected-A4 `t = 1` target in its one-directional headline form: a vanishing
ℕ-weighted sum of `p^(k+1)`-th roots of unity IS an ℕ-combination of full μ_p-coset
indicators. -/
theorem mupCosetCombination_of_vanishing [CharZero L] (hp : p.Prime)
    [NeZero (p ^ (k + 1))] [NeZero (p ^ k)]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (a : ZMod (p ^ (k + 1)) → ℕ)
    (hsum : ∑ j : ZMod (p ^ (k + 1)), (a j : L) * ζ ^ (ZMod.val j) = 0) :
    ∃ m : ZMod (p ^ k) → ℕ,
      ∀ j, a j = ∑ c : ZMod (p ^ k), m c * mupCosetIndicator p k c j :=
  (multiset_window_law_t1 hp hζ a).mp hsum

end PrimePowerMultisetWindow

#print axioms PrimePowerMultisetWindow.weightedLevelDecomposes_of_dvd_prime_pow
#print axioms PrimePowerMultisetWindow.weighted_windowed_prime_pow
#print axioms PrimePowerMultisetWindow.cosetBase_val
#print axioms PrimePowerMultisetWindow.combination_apply
#print axioms PrimePowerMultisetWindow.isMupCosetCombination_iff_factors
#print axioms PrimePowerMultisetWindow.multiset_window_law_t1
#print axioms PrimePowerMultisetWindow.mupCosetCombination_of_vanishing
