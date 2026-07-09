import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

set_option autoImplicit false

/-!
# Height-gate no-go: the exact norm of the block witness (#407)

The spurious-vanishing height gate (`HeightGateNormBound.gate_2power_antipodal`) certifies
"`p ∣ N(Σ_{i∈S} ζ^i) ⟹ S` antipodal" only when, for the non-antipodal `S`,
`|N_{ℚ(ζ_n)/ℚ}(Σ_{i∈S} ζ^i)| < p`.  The current Lean proof uses the loose house bound
`(#S)^{φ(n)} = n^{n/2}`, closing only `n ≤ 32` at the prize prime `p ~ 2^128`.  c.157/c.159
flagged a "structure-aware norm bound" as the next lever to push past `n = 32`.

This file shows the lever is a **no-go for the prize**: the *explicit* non-antipodal block
`S = {0,…,n/2−1}` has an EXACT (not house-bounded) norm

> `N_{ℚ(ζ_n)/ℚ}(Σ_{i=0}^{n/2−1} ζ^i) = 2^{n/2−1}`  (`n = 2^k`).

Mechanism: `B := Σ_{i<n/2} ζ^i = (ζ^{n/2} − 1)/(ζ − 1) = −2/(ζ − 1)` since `ζ^{n/2} = −1`;
`N(ζ − 1) = Φ_{2^k}(1) = 2` (`norm_sub_one_two`) and `N(−2) = (−2)^{φ(n)} = 2^{n/2}`.

Consequence: this single explicit `S` already has `|N| = 2^{n/2−1} ≥ p` for all `n ≥ 512`,
and `2^{2^{29}−1} ≫ p ~ 2^{158}` at the prize point `n = 2^{30}`.  Since the gate needs
`|N| < p` for *every* non-antipodal `S`, NO norm bound (however structure-aware) rescues it
at the prize: the worst-case `max_S |N|` is the √-cancellation/house-maximization wall itself.
-/

open Finset Polynomial Algebra Module

namespace ArkLib.ProximityGap.BlockSumNormNoGo

/-- Telescoping geometric-sum identity (inline to avoid the `GeomSum` import). -/
private theorem geomSumMul' {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring

variable {L : Type*} [Field L] [NumberField L]

omit [NumberField L] in
/-- `ζ^{2^{k-1}} = −1` for a primitive `2^k`-th root of unity (`k ≥ 1`). -/
theorem primRoot_pow_half_eq_neg_one {k : ℕ} (hk : 1 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) : ζ ^ (2 ^ (k - 1)) = -1 := by
  set w := ζ ^ (2 ^ (k - 1)) with hw
  have hsq : w ^ 2 = 1 := by
    rw [hw, ← pow_mul]
    have : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ]; congr 1; omega
    rw [this, hζ.pow_eq_one]
  have hne : w ≠ 1 := by
    rw [hw]
    intro h
    have hdvd : (2 ^ k : ℕ) ∣ 2 ^ (k - 1) := (hζ.pow_eq_one_iff_dvd _).1 h
    have hlt : 2 ^ (k - 1) < 2 ^ k := by
      apply Nat.pow_lt_pow_right one_lt_two; omega
    exact absurd (Nat.le_of_dvd (by positivity) hdvd) (by omega)
  -- w^2 = 1, w ≠ 1  ⟹  w = -1
  have hfac : (w - 1) * (w + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact eq_neg_of_add_eq_zero_left h

/-- **The exact norm of the block witness.**  For `ζ` a primitive `2^k`-th root of unity
(`k ≥ 2`) generating the cyclotomic extension `L/ℚ`, the non-antipodal block
`S = {0,…,2^{k-1}−1}` has `N_{L/ℚ}(Σ_{i∈S} ζ^i) = 2^{2^{k-1}−1}`. -/
theorem block_sum_norm {k : ℕ} (hk : 2 ≤ k) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    [IsCyclotomicExtension {2 ^ k} ℚ L] (hirr : Irreducible (cyclotomic (2 ^ k) ℚ)) :
    Algebra.norm ℚ (∑ i ∈ range (2 ^ (k - 1)), ζ ^ i) = 2 ^ (2 ^ (k - 1) - 1) := by
  set m := 2 ^ (k - 1) with hm
  set B := ∑ i ∈ range m, ζ ^ i with hB
  -- B * (ζ - 1) = ζ^m - 1 = -2
  have hgeom : B * (ζ - 1) = ζ ^ m - 1 := geomSumMul' ζ m
  have hhalf : ζ ^ m = -1 := primRoot_pow_half_eq_neg_one (by omega) hζ
  have hBval : B * (ζ - 1) = -2 := by rw [hgeom, hhalf]; ring
  -- take norms
  have hmul : Algebra.norm ℚ B * Algebra.norm ℚ (ζ - 1) = Algebra.norm ℚ (-2 : L) := by
    rw [← map_mul]; rw [hBval]
  have hsub : Algebra.norm ℚ (ζ - 1) = 2 := IsPrimitiveRoot.norm_sub_one_two hζ hk hirr
  -- finrank ℚ L = totient (2^k) = 2^{k-1} = m
  have htot : (2 ^ k).totient = 2 ^ (k - 1) := by
    have h21 : (2 : ℕ) - 1 = 1 := rfl
    rw [Nat.totient_prime_pow Nat.prime_two (show 0 < k by omega), h21, mul_one]
  have hfr : Module.finrank ℚ L = m := by
    rw [IsCyclotomicExtension.finrank L hirr, htot, hm]
  -- N(-2) = (-2)^{finrank} = (-2)^m
  have hneg2 : Algebra.norm ℚ (-2 : L) = (-2 : ℚ) ^ m := by
    have hcast : (-2 : L) = algebraMap ℚ L (-2 : ℚ) := by rw [map_neg, map_ofNat]
    rw [hcast, Algebra.norm_algebraMap, hfr]
  -- m is even (k ≥ 2 ⟹ k-1 ≥ 1)
  have hmeven : Even m := by
    rw [hm]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hpow : (-2 : ℚ) ^ m = 2 ^ m := by
    rw [neg_pow, hmeven.neg_one_pow, one_mul]
  -- combine: N(B) * 2 = 2^m, and 2^{m-1} * 2 = 2^m
  rw [hsub, hneg2, hpow] at hmul
  have hmpos : 1 ≤ m := by rw [hm]; exact Nat.one_le_pow _ _ (by norm_num)
  have h2 : (2 : ℚ) ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [h2] at hmul
  exact mul_right_cancel₀ (by norm_num) hmul

/-- **Height-gate no-go (corollary).**  The explicit non-antipodal block witness has norm
EXCEEDING the prize prime once `p ≤ 2^{2^{k-1}-1}`.  Since the gate's contradiction needs
`|N(Σ_S)| < p` for *every* non-antipodal `S`, and this single explicit `S` already violates
it, no norm bound (however structure-aware) rescues the gate there: at the prize point
`n = 2^{30}` the block alone forces `|N| = 2^{2^{29}-1} ≫ p ~ 2^{158}`. -/
theorem block_sum_norm_ge_prize {k : ℕ} (hk : 2 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) [IsCyclotomicExtension {2 ^ k} ℚ L]
    (hirr : Irreducible (cyclotomic (2 ^ k) ℚ)) {p : ℕ}
    (hp : (p : ℚ) ≤ 2 ^ (2 ^ (k - 1) - 1)) :
    (p : ℚ) ≤ Algebra.norm ℚ (∑ i ∈ Finset.range (2 ^ (k - 1)), ζ ^ i) := by
  rw [block_sum_norm hk hζ hirr]; exact hp

end ArkLib.ProximityGap.BlockSumNormNoGo

#print axioms ArkLib.ProximityGap.BlockSumNormNoGo.block_sum_norm
#print axioms ArkLib.ProximityGap.BlockSumNormNoGo.block_sum_norm_ge_prize
