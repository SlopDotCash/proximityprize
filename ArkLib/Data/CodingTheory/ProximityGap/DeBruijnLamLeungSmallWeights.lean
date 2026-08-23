/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnLamLeungReduction

/-!
# Issue #232 — LAM–LEUNG VIA SMALL-WEIGHT CLASSIFICATION: the `6 ∣ n` and
# `10 ∣ n` families, including the first nontrivial `k ≥ 3` levels (O113)

After O112 the Lam–Leung ℕ-span theorem is open exactly at squarefree
`k ≥ 3`-prime levels.  The content at a FIXED level `n` is finite: the span
`ℕp₁ + ⋯ + ℕp_k` misses only its numerical-semigroup gaps, so the law at `n`
is equivalent to the nonexistence of vanishing ℕ-sums whose total weight is a
gap.  Gaps are small; small-weight vanishing sums are classifiable:

* weight `1` — never vanishes (a root of unity is nonzero);
* weight `2` — forces `2 ∣ n` (`two_dvd_of_pair_sum_eq_zero`: the ratio is
  `−1`);
* weight `3` — forces `3 ∣ n` (`three_dvd_of_triple_sum_eq_zero`: the ratios
  are primitive cube roots — proven by embedding `ℚ(u) ↪ ℂ` via
  `IsAlgClosed.lift` and the unit-circle identity `a + ā = −1`).

Consequences (the headline span laws):

* `lam_leung_of_six_dvd` — the span law holds at EVERY `n` with `6 ∣ n`
  (gap set `{1}`); covers `n = 30, 42, 66, 78, …` — all `k ≥ 3` levels
  divisible by 6, previously open in-tree.
* `lam_leung_of_ten_dvd` — the span law holds at EVERY `n` with `10 ∣ n`
  (gap set `⊆ {1, 3}`; the gap `3` is killed by the cube-root classification
  when `3 ∤ n` and is in the span otherwise); covers `n = 70 = 2·5·7` — **the
  first nontrivial three-prime Lam–Leung instance**, where the semigroup
  argument alone does not suffice — and `n = 110, 130, 770 = 2·5·7·11 (k=4), …`

The companion probe `probe_rep_weight_cone.py` records the DISPROOF of the
naive inductive strengthening (the "rep-weight cone" claim: all ℕ-representation
weights of a fixed `γ` lie in `μ(γ) + ℕ`-span): offset-`1` representation pairs
exist at every tested modulus.  Only the `γ = 0` instance (Lam–Leung itself)
survives — which is why the remaining squarefree levels need genuinely
different tools (Lam–Leung's group-ring induction / Mann-type theorems).
-/

namespace DeBruijnLamLeungSmallWeights

open Finset IntermediateField

variable {L : Type*} [Field L]

/-! ## The multiset of a weight function and the extraction lemmas -/

/-- The exponent multiset of a weight function: `e` with multiplicity `w e`. -/
def expMultiset (n : ℕ) (w : ℕ → ℕ) : Multiset ℕ :=
  (Finset.range n).val.bind fun e => Multiset.replicate (w e) e

lemma expMultiset_card (n : ℕ) (w : ℕ → ℕ) :
    Multiset.card (expMultiset n w) = ∑ e ∈ Finset.range n, w e := by
  simp [expMultiset, Multiset.card_bind, Finset.sum]

lemma expMultiset_sum (n : ℕ) (w : ℕ → ℕ) (ζ : L) :
    ((expMultiset n w).map fun e => ζ ^ e).sum
      = ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e := by
  simp [expMultiset, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_replicate, Multiset.sum_replicate, Finset.sum, nsmul_eq_mul]

/-! ## Weight 1 and weight 2 -/

/-- A weight-1 vanishing sum is impossible: roots of unity are nonzero. -/
lemma no_weight_one {n : ℕ} {ζ : L} (hζ : ζ ^ n = 1) (hn : 0 < n) (w : ℕ → ℕ)
    (htot : ∑ e ∈ Finset.range n, w e = 1)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) : False := by
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have hcard : Multiset.card (expMultiset n w) = 1 := by
    rw [expMultiset_card, htot]
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  have h := expMultiset_sum n w ζ
  rw [ha] at h
  simp at h
  rw [hsum] at h
  exact pow_ne_zero a hζ0 h

/-- **Weight 2 forces `2 ∣ n`**: a vanishing pair of `n`-th roots of unity has
ratio `−1`, of order `2`. -/
lemma two_dvd_of_pair_sum_eq_zero [CharZero L] {n : ℕ} (hn : 0 < n)
    {x y : L} (hx : x ^ n = 1) (hy : y ^ n = 1) (hxy : x + y = 0) : 2 ∣ n := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hy' : y = -x := by linear_combination hxy
  have hyx : y * x⁻¹ = -1 := by
    rw [hy', neg_mul, mul_inv_cancel₀ hx0]
  have hpow : (-1 : L) ^ n = 1 := by
    rw [← hyx, mul_pow, hy, inv_pow, hx, inv_one, one_mul]
  rcases Nat.even_or_odd n with he | ho
  · exact he.two_dvd
  · rw [ho.neg_one_pow] at hpow
    have : (2 : L) = 0 := by linear_combination -hpow
    exact absurd this two_ne_zero

/-! ## Weight 3: the cube-root classification via a complex embedding -/

/-- Roots of unity are integral over ℚ. -/
private lemma isIntegral_of_pow_eq_one [CharZero L] {x : L} {m : ℕ} (hm : 0 < m)
    (hx : x ^ m = 1) : IsIntegral ℚ x :=
  ⟨Polynomial.X ^ m - 1,
    by simpa using Polynomial.monic_X_pow_sub_C (1 : ℚ) hm.ne',
    by simp [hx]⟩

/-- The ℂ-side core: a unit-norm pair `a`, `−1−a` of `n`-torsion points forces
`a` to be a primitive cube root, so `3 ∣ n`. -/
private lemma three_dvd_of_complex {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ^ n = 1) (hb : (-1 - a) ^ n = 1) : 3 ∣ n := by
  have hna : ‖a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one ha hn.ne'
  have hnb : ‖-1 - a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hb hn.ne'
  -- a · conj a = 1 and (−1−a) · conj (−1−a) = 1, via conj = inv on the circle
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at hna
    simp at hna
  have hb0 : (-1 - a) ≠ 0 := by
    intro h0
    rw [h0] at hnb
    simp at hnb
  have hmc : a * (starRingEnd ℂ) a = 1 := by
    rw [← Complex.inv_eq_conj hna, mul_inv_cancel₀ ha0]
  have hmb : (-1 - a) * (starRingEnd ℂ) (-1 - a) = 1 := by
    rw [← Complex.inv_eq_conj hnb, mul_inv_cancel₀ hb0]
  -- expand: a + conj a = −1
  have hsum : a + (starRingEnd ℂ) a = -1 := by
    have hexp : (-1 - a) * (starRingEnd ℂ) (-1 - a)
        = 1 + a + (starRingEnd ℂ) a + a * (starRingEnd ℂ) a := by
      rw [map_sub, map_neg, map_one]
      ring
    rw [hexp, hmc] at hmb
    linear_combination hmb
  -- a² + a + 1 = a(a + 1 + conj a) = 0
  have hquad : a ^ 2 + a + 1 = 0 := by
    calc a ^ 2 + a + 1 = a * (a + 1 + (starRingEnd ℂ) a) := by
          rw [mul_add, mul_add, hmc]
          ring
      _ = a * 0 := by rw [show a + 1 + (starRingEnd ℂ) a = 0 by
            linear_combination hsum]
      _ = 0 := mul_zero a
  have hcube : a ^ 3 = 1 := by linear_combination (a - 1) * hquad
  have hne1 : a ≠ 1 := by
    intro h1
    rw [h1] at hquad
    norm_num at hquad
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have horder : orderOf a = 3 := orderOf_eq_prime hcube hne1
  exact horder ▸ orderOf_dvd_of_pow_eq_one ha

/-- **Weight 3 forces `3 ∣ n`** (the cube-root classification): three `n`-th
roots of unity in a characteristic-zero field summing to zero have pairwise
ratios that are primitive cube roots.  Proof: normalize to `1 + u + v = 0`,
embed `ℚ(u)` into `ℂ` (`IsAlgClosed.lift`), and run the unit-circle identity. -/
theorem three_dvd_of_triple_sum_eq_zero [CharZero L] {n : ℕ} (hn : 0 < n)
    {x y z : L} (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (hxyz : x + y + z = 0) : 3 ∣ n := by
  classical
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  set u : L := y * x⁻¹ with hu
  have hun : u ^ n = 1 := by
    rw [hu, mul_pow, hy, inv_pow, hx, inv_one, one_mul]
  have hvn : (-1 - u) ^ n = 1 := by
    have hz' : z = -x - y := by linear_combination hxyz
    have hveq : -1 - u = z * x⁻¹ := by
      rw [hz', hu, sub_mul, neg_mul, mul_inv_cancel₀ hx0]
    rw [hveq, mul_pow, hz, inv_pow, hx, inv_one, one_mul]
  -- the number field ℚ(u) and its complex embedding
  have hint : IsIntegral ℚ u := isIntegral_of_pow_eq_one hn hun
  set K := ℚ⟮u⟯ with hK
  set g : K := IntermediateField.AdjoinSimple.gen ℚ u with hg
  have hcoe : algebraMap K L g = u := IntermediateField.AdjoinSimple.algebraMap_gen ℚ u
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hgn : g ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, hcoe]
    exact hun
  have hgvn : (-1 - g) ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, map_sub, map_neg, map_one, hcoe]
    exact hvn
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  let φ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine three_dvd_of_complex hn (a := φ g) ?_ ?_
  · rw [← map_pow, hgn, map_one]
  · have h := congrArg φ hgvn
    rw [map_pow, map_sub, map_neg, map_one] at h
    exact h

/-! ## The span laws -/

/-- Splitting a sum over a finset into two distinguished members. -/
private lemma sum_eq_pair {s : Finset ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (f : ℕ → ℕ) (hf : ∀ p ∈ s, p ≠ a → p ≠ b → f p = 0) :
    ∑ p ∈ s, f p = f a + f b := by
  rw [← Finset.add_sum_erase s f ha]
  congr 1
  rw [← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)]
  have hz : ∑ p ∈ (s.erase a).erase b, f p = 0 :=
    Finset.sum_eq_zero fun p hp =>
      hf p (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hp))
        (Finset.ne_of_mem_erase hp)
  rw [hz, add_zero]

/-- Splitting a sum over a finset into three distinguished members. -/
private lemma sum_eq_triple {s : Finset ℕ} {a b c : ℕ} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : ℕ → ℕ) (hf : ∀ p ∈ s, p ≠ a → p ≠ b → p ≠ c → f p = 0) :
    ∑ p ∈ s, f p = f a + (f b + f c) := by
  rw [← Finset.add_sum_erase s f ha]
  congr 1
  exact sum_eq_pair (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
    (Finset.mem_erase.mpr ⟨hac.symm, hc⟩) hbc f
    (fun p hp hpb hpc =>
      hf p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp) hpb hpc)

/-- Weight-3 vanishing combinations force `3 ∣ n` (the ℕ-weighted corollary). -/
lemma three_dvd_of_weight_three [CharZero L] {n : ℕ} (hn : 0 < n) {ζ : L}
    (hζ : ζ ^ n = 1) (w : ℕ → ℕ)
    (htot : ∑ e ∈ Finset.range n, w e = 3)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) : 3 ∣ n := by
  have hcard : Multiset.card (expMultiset n w) = 3 := by
    rw [expMultiset_card, htot]
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.mp hcard
  have h := expMultiset_sum n w ζ
  rw [habc] at h
  simp at h
  rw [hsum] at h
  have hpow : ∀ e : ℕ, (ζ ^ e) ^ n = 1 := fun e => by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine three_dvd_of_triple_sum_eq_zero hn (hpow a) (hpow b) (hpow c) ?_
  linear_combination h

/-- **LAM–LEUNG AT `6 ∣ n`** (O113a): the ℕ-span law holds at every level
divisible by 6 — the semigroup `ℕ·2 + ℕ·3` misses only `1`, and weight-1
vanishing sums do not exist.  Covers all `k ≥ 3` levels divisible by 6
(`n = 30, 42, 66, …`), previously open in-tree. -/
theorem lam_leung_of_six_dvd [CharZero L] {n : ℕ} (h6 : 6 ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℕ)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
      = ∑ p ∈ n.primeFactors, c p * p := by
  classical
  have h2n : 2 ∣ n := dvd_trans (by norm_num) h6
  have h3n : 3 ∣ n := dvd_trans (by norm_num) h6
  have h2m : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, hn.ne'⟩
  have h3m : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn.ne'⟩
  set T := ∑ e ∈ Finset.range n, w e with hT
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · exact ⟨0, by simp [hT0]⟩
  rcases Nat.lt_or_ge T 2 with hT1 | hT2
  · -- T = 1: impossible
    have hT1' : T = 1 := by omega
    exact absurd (no_weight_one hζ.pow_eq_one hn w (hT ▸ hT1') hsum) not_false
  -- T ≥ 2: split by parity
  refine ⟨fun p => if p = 2 then (T - (if T % 2 = 0 then 0 else 3)) / 2
    else if p = 3 then (if T % 2 = 0 then 0 else 1) else 0, ?_⟩
  dsimp only
  rw [sum_eq_pair h2m h3m (by norm_num)
    (fun p => (if p = 2 then (T - (if T % 2 = 0 then 0 else 3)) / 2
      else if p = 3 then (if T % 2 = 0 then 0 else 1) else 0) * p)
    (fun p _ hp2 hp3 => by
      dsimp only
      rw [if_neg hp2, if_neg hp3]
      exact zero_mul p)]
  rw [if_pos rfl, if_neg (by norm_num : (3 : ℕ) ≠ 2), if_pos rfl]
  rcases Nat.even_or_odd T with he | ho
  · have h2 : T % 2 = 0 := Nat.even_iff.mp he
    rw [if_pos h2, if_pos h2]
    omega
  · have h2' : ¬ T % 2 = 0 := by
      have := Nat.odd_iff.mp ho
      omega
    rw [if_neg h2', if_neg h2']
    omega

/-- **LAM–LEUNG AT `10 ∣ n`** (O113b): the ℕ-span law holds at every level
divisible by 10.  The semigroup `ℕ·2 + ℕ·5` misses only `{1, 3}`; weight 1
never vanishes, and weight 3 forces `3 ∣ n` (the cube-root classification) —
in which case `3` is in the span anyway.  Covers `n = 70 = 2·5·7`, **the first
nontrivial three-prime Lam–Leung instance**, and `n = 110, 130, 770, …` -/
theorem lam_leung_of_ten_dvd [CharZero L] {n : ℕ} (h10 : 10 ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℕ)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
      = ∑ p ∈ n.primeFactors, c p * p := by
  classical
  have h2n : 2 ∣ n := dvd_trans (by norm_num) h10
  have h5n : 5 ∣ n := dvd_trans (by norm_num) h10
  have h2m : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, hn.ne'⟩
  have h5m : 5 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, h5n, hn.ne'⟩
  set T := ∑ e ∈ Finset.range n, w e with hT
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · exact ⟨0, by simp [hT0]⟩
  rcases Nat.lt_or_ge T 2 with hT1 | hT2
  · have hT1' : T = 1 := by omega
    exact absurd (no_weight_one hζ.pow_eq_one hn w (hT ▸ hT1') hsum) not_false
  by_cases hT3 : T = 3
  · -- weight 3: the cube-root classification puts 3 ∣ n, so 3 is available
    have h3n : 3 ∣ n :=
      three_dvd_of_weight_three hn hζ.pow_eq_one w (hT ▸ hT3) hsum
    have h3m : 3 ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn.ne'⟩
    refine ⟨fun p => if p = 3 then 1 else 0, ?_⟩
    dsimp only
    rw [Finset.sum_eq_single_of_mem 3 h3m
      (fun p _ hp => by rw [if_neg hp]; exact zero_mul p)]
    rw [if_pos rfl, hT3]
  · -- T = 2, or T ≥ 4: ℕ2 + ℕ5 suffices (odd T ≥ 5 here)
    have h5odd : T % 2 = 1 → 5 ≤ T := by omega
    refine ⟨fun p => if p = 2 then (T - (if T % 2 = 0 then 0 else 5)) / 2
      else if p = 5 then (if T % 2 = 0 then 0 else 1) else 0, ?_⟩
    dsimp only
    rw [sum_eq_pair h2m h5m (by norm_num)
      (fun p => (if p = 2 then (T - (if T % 2 = 0 then 0 else 5)) / 2
        else if p = 5 then (if T % 2 = 0 then 0 else 1) else 0) * p)
      (fun p _ hp2 hp5 => by
        dsimp only
        rw [if_neg hp2, if_neg hp5]
        exact zero_mul p)]
    rw [if_pos rfl, if_neg (by norm_num : (5 : ℕ) ≠ 2), if_pos rfl]
    rcases Nat.even_or_odd T with he | ho
    · have h2 : T % 2 = 0 := Nat.even_iff.mp he
      rw [if_pos h2, if_pos h2]
      omega
    · have h2 : T % 2 = 1 := Nat.odd_iff.mp ho
      have hT5 : 5 ≤ T := h5odd h2
      have h2' : ¬ T % 2 = 0 := by omega
      rw [if_neg h2', if_neg h2']
      omega

end DeBruijnLamLeungSmallWeights

#print axioms DeBruijnLamLeungSmallWeights.no_weight_one
#print axioms DeBruijnLamLeungSmallWeights.two_dvd_of_pair_sum_eq_zero
#print axioms DeBruijnLamLeungSmallWeights.three_dvd_of_triple_sum_eq_zero
#print axioms DeBruijnLamLeungSmallWeights.three_dvd_of_weight_three
#print axioms DeBruijnLamLeungSmallWeights.lam_leung_of_six_dvd
#print axioms DeBruijnLamLeungSmallWeights.lam_leung_of_ten_dvd

namespace DeBruijnLamLeungSmallWeights

open Finset IntermediateField

variable {L : Type*} [Field L]

/-! ## Weight 4: the Conway–Jones quadruple classification (appended; O114)

A vanishing sum of four roots of unity is two antipodal pairs — so weight 4
forces `2 ∣ n`.  ℂ-side mechanism: conjugating `1 + a + b + c = 0` and clearing
denominators gives `e₂ + e₃ = 0` for the elementary symmetric functions of
`a, b, c`, so their cubic factors as `(T + 1)(T² + e₂)` — every branch of the
case analysis produces `−1 ∈ μ_n`.  Consequence: `lam_leung_of_105_dvd` — the
span law at every `n` divisible by `105 = 3·5·7` (gaps `{1, 2, 4}` all killed),
including `n = 105`, the FIRST odd three-prime Lam–Leung level. -/

namespace WeightFour

open IntermediateField

variable {L : Type*} [Field L]

/-- The ℂ-side core: four unit `n`-torsion points summing to zero force
`2 ∣ n`. -/
private lemma two_dvd_of_complex {n : ℕ} (hn : 0 < n) {a b c : ℂ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hc : c ^ n = 1)
    (habc : 1 + a + b + c = 0) : 2 ∣ n := by
  have neg_one_case : ∀ x : ℂ, x ^ n = 1 → x = -1 → 2 ∣ n := by
    intro x hx hx1
    rw [hx1] at hx
    rcases Nat.even_or_odd n with he | ho
    · exact he.two_dvd
    · rw [ho.neg_one_pow] at hx
      norm_num at hx
  -- norms and conj = inv
  have hkey : ∀ x : ℂ, x ^ n = 1 → x ≠ 0 ∧ (starRingEnd ℂ) x = x⁻¹ := by
    intro x hx
    have hnx : ‖x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hx hn.ne'
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0] at hnx
      simp at hnx
    exact ⟨hx0, (Complex.inv_eq_conj hnx).symm⟩
  obtain ⟨ha0, hca⟩ := hkey a ha
  obtain ⟨hb0, hcb⟩ := hkey b hb
  obtain ⟨hc0, hcc⟩ := hkey c hc
  -- the conjugate relation, cleared: abc + (bc + ac + ab) = 0
  have hconj : 1 + a⁻¹ + b⁻¹ + c⁻¹ = 0 := by
    have h := congrArg (starRingEnd ℂ) habc
    rw [map_add, map_add, map_add, map_one, map_zero, hca, hcb, hcc] at h
    exact h
  have hcleared : a * b * c + (b * c + a * c + a * b) = 0 := by
    have h := congrArg (· * (a * b * c)) hconj
    simp only [add_mul, zero_mul, one_mul] at h
    calc a * b * c + (b * c + a * c + a * b)
        = 1 * (a * b * c) + (a⁻¹ * (a * b * c) + b⁻¹ * (a * b * c)
            + c⁻¹ * (a * b * c)) := by
          field_simp
      _ = 0 := by linear_combination h
  -- the factored cubic at T = a: (a + 1)(a² + e₂) = 0
  set e₂ : ℂ := a * b + a * c + b * c with he₂
  have hsum : a + b + c = -1 := by linear_combination habc
  have hcubic : ∀ x : ℂ, (x - a) * (x - b) * (x - c)
      = (x + 1) * (x ^ 2 + e₂) := by
    intro x
    have he₃ : a * b * c = -e₂ := by
      rw [he₂]
      linear_combination hcleared
    calc (x - a) * (x - b) * (x - c)
        = x ^ 3 - (a + b + c) * x ^ 2 + (a * b + a * c + b * c) * x
            - a * b * c := by ring
      _ = x ^ 3 + x ^ 2 + e₂ * x + e₂ := by
          rw [hsum, he₂, he₃]
          ring
      _ = (x + 1) * (x ^ 2 + e₂) := by ring
  have hfa : (a + 1) * (a ^ 2 + e₂) = 0 := by
    have h := hcubic a
    simp at h
    exact mul_eq_zero.mpr h
  have hfb : (b + 1) * (b ^ 2 + e₂) = 0 := by
    have h := hcubic b
    have h2 : (b - a) * (b - b) * (b - c) = 0 := by
      simp
    rw [h2] at h
    linear_combination -h
  have hfc : (c + 1) * (c ^ 2 + e₂) = 0 := by
    have h := hcubic c
    have h2 : (c - a) * (c - b) * (c - c) = 0 := by
      simp
    rw [h2] at h
    linear_combination -h
  -- case analysis: every branch yields some root equal to −1
  rcases mul_eq_zero.mp hfa with h1 | h1
  · exact neg_one_case a ha (by linear_combination h1)
  rcases mul_eq_zero.mp hfb with h2 | h2
  · exact neg_one_case b hb (by linear_combination h2)
  rcases mul_eq_zero.mp hfc with h3 | h3
  · exact neg_one_case c hc (by linear_combination h3)
  -- all three squares equal −e₂: pairwise ratios are ±1
  have hab : (b - a) * (b + a) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp hab with h4 | h4
  · -- b = a: compare with c
    have hba : b = a := by linear_combination h4
    have hac : (c - a) * (c + a) = 0 := by linear_combination h3 - h1
    rcases mul_eq_zero.mp hac with h5 | h5
    · -- c = a too: 1 + 3a = 0 contradicts ‖a‖ = 1
      have hcaeq : c = a := by linear_combination h5
      have h13 : 1 + 3 * a = 0 := by
        rw [hba, hcaeq] at habc
        linear_combination habc
      have hna : ‖a‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one ha hn.ne'
      have ha3 : a = -(1 / 3) := by linear_combination (1 / 3 : ℂ) * h13
      rw [ha3] at hna
      norm_num at hna
    · -- c = −a: then 1 + b = ... wait b = a: 1 + 2a + c = 0, c = −a → 1 + a = 0
      have hcnega : c = -a := by linear_combination h5
      have h1a : 1 + a = 0 := by
        rw [hba, hcnega] at habc
        linear_combination habc
      exact neg_one_case a ha (by linear_combination h1a)
  · -- b = −a: then 1 + c = 0
    have hbnega : b = -a := by linear_combination h4
    have h1c : 1 + c = 0 := by
      rw [hbnega] at habc
      linear_combination habc
    exact neg_one_case c hc (by linear_combination h1c)

end WeightFour

/-- **Weight 4 forces `2 ∣ n`** (the Conway–Jones quadruple classification):
four `n`-th roots of unity in a characteristic-zero field summing to zero split
into two antipodal pairs.  Embed `ℚ(u)(v)` into `ℂ` and factor the conjugate-
cleared cubic as `(T+1)(T² + e₂)`. -/
theorem two_dvd_of_quadruple_sum_eq_zero [CharZero L] {n : ℕ} (hn : 0 < n)
    {x y z t : L} (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (ht : t ^ n = 1) (hxyzt : x + y + z + t = 0) : 2 ∣ n := by
  classical
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  set u : L := y * x⁻¹ with hu
  set v : L := z * x⁻¹ with hv
  set w : L := t * x⁻¹ with hw
  have hun : u ^ n = 1 := by
    rw [hu, mul_pow, hy, inv_pow, hx, inv_one, one_mul]
  have hvn : v ^ n = 1 := by
    rw [hv, mul_pow, hz, inv_pow, hx, inv_one, one_mul]
  have hwn : w ^ n = 1 := by
    rw [hw, mul_pow, ht, inv_pow, hx, inv_one, one_mul]
  have hrel : 1 + u + v + w = 0 := by
    have h := congrArg (· * x⁻¹) hxyzt
    simp only [add_mul, zero_mul] at h
    rw [mul_inv_cancel₀ hx0, ← hu, ← hv, ← hw] at h
    linear_combination h
  -- the two-generator number field and its complex embedding
  have hintu : IsIntegral ℚ u := isIntegral_of_pow_eq_one hn hun
  have hintv : IsIntegral ℚ⟮u⟯ v :=
    ⟨Polynomial.X ^ n - 1,
      by simpa using Polynomial.monic_X_pow_sub_C (1 : ℚ⟮u⟯) hn.ne',
      by simp [hvn]⟩
  haveI : FiniteDimensional ℚ ℚ⟮u⟯ :=
    IntermediateField.adjoin.finiteDimensional hintu
  haveI : FiniteDimensional ℚ⟮u⟯ ℚ⟮u⟯⟮v⟯ :=
    IntermediateField.adjoin.finiteDimensional hintv
  haveI : FiniteDimensional ℚ ℚ⟮u⟯⟮v⟯ := Module.Finite.trans ℚ⟮u⟯ ℚ⟮u⟯⟮v⟯
  haveI : Algebra.IsAlgebraic ℚ ℚ⟮u⟯⟮v⟯ :=
    Algebra.IsAlgebraic.of_finite ℚ ℚ⟮u⟯⟮v⟯
  -- u and v live inside the tower field
  have huE : u ∈ ℚ⟮u⟯⟮v⟯ := by
    have h := ℚ⟮u⟯⟮v⟯.algebraMap_mem ⟨u, mem_adjoin_simple_self ℚ u⟩
    simpa using h
  have hvE : v ∈ ℚ⟮u⟯⟮v⟯ := mem_adjoin_simple_self ℚ⟮u⟯ v
  set A : ℚ⟮u⟯⟮v⟯ := ⟨u, huE⟩ with hA
  set B : ℚ⟮u⟯⟮v⟯ := ⟨v, hvE⟩ with hB
  have hinj : Function.Injective (algebraMap ℚ⟮u⟯⟮v⟯ L) :=
    (algebraMap ℚ⟮u⟯⟮v⟯ L).injective
  have hAcoe : algebraMap ℚ⟮u⟯⟮v⟯ L A = u := rfl
  have hBcoe : algebraMap ℚ⟮u⟯⟮v⟯ L B = v := rfl
  have hAn : A ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, hAcoe]
    exact hun
  have hBn : B ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, hBcoe]
    exact hvn
  have hCn : (-1 - A - B) ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, map_sub, map_sub, map_neg, map_one, hAcoe, hBcoe]
    have hweq : -1 - u - v = w := by linear_combination -hrel
    rw [hweq]
    exact hwn
  let φ : ℚ⟮u⟯⟮v⟯ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine WeightFour.two_dvd_of_complex hn (a := φ A) (b := φ B)
    (c := φ (-1 - A - B)) ?_ ?_ ?_ ?_
  · rw [← map_pow, hAn, map_one]
  · rw [← map_pow, hBn, map_one]
  · rw [← map_pow, hCn, map_one]
  · rw [map_sub, map_sub, map_neg, map_one]
    ring

/-- Weight-4 vanishing ℕ-combinations force `2 ∣ n`. -/
lemma two_dvd_of_weight_four [CharZero L] {n : ℕ} (hn : 0 < n) {ζ : L}
    (hζ : ζ ^ n = 1) (w : ℕ → ℕ)
    (htot : ∑ e ∈ Finset.range n, w e = 4)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) : 2 ∣ n := by
  have hcard : Multiset.card (expMultiset n w) = 4 := by
    rw [expMultiset_card, htot]
  obtain ⟨a, b, c, d, habcd⟩ := Multiset.card_eq_four.mp hcard
  have h := expMultiset_sum n w ζ
  rw [habcd] at h
  simp at h
  rw [hsum] at h
  have hpow : ∀ e : ℕ, (ζ ^ e) ^ n = 1 := fun e => by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine two_dvd_of_quadruple_sum_eq_zero hn (hpow a) (hpow b) (hpow c)
    (hpow d) ?_
  linear_combination h

/-- **LAM–LEUNG AT `105 ∣ n`** (O114): the span law holds at every level
divisible by `105 = 3·5·7` — the semigroup `ℕ3 + ℕ5 + ℕ7` misses only
`{1, 2, 4}`; weight 1 never vanishes, weights 2 and 4 force `2 ∣ n` (in which
case they lie in the span anyway).  Covers `n = 105`, **the first odd
three-prime Lam–Leung level**, and `n = 315, 1155 = 3·5·7·11 (k = 4), …` -/
theorem lam_leung_of_105_dvd [CharZero L] {n : ℕ} (h105 : 105 ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℕ)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
      = ∑ p ∈ n.primeFactors, c p * p := by
  classical
  have h3n : 3 ∣ n := dvd_trans (by norm_num) h105
  have h5n : 5 ∣ n := dvd_trans (by norm_num) h105
  have h7n : 7 ∣ n := dvd_trans (by norm_num) h105
  have h3m : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn.ne'⟩
  have h5m : 5 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, h5n, hn.ne'⟩
  set T := ∑ e ∈ Finset.range n, w e with hT
  -- the even-weight escape: if 2 ∣ n, pair 2 with 3 as in the 6 ∣ n law
  by_cases h2n : 2 ∣ n
  · have h2m : 2 ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, hn.ne'⟩
    rcases Nat.eq_zero_or_pos T with hT0 | hTpos
    · exact ⟨0, by simp [hT0]⟩
    rcases Nat.lt_or_ge T 2 with hT1 | hT2
    · have hT1' : T = 1 := by omega
      exact absurd (no_weight_one hζ.pow_eq_one hn w (hT ▸ hT1') hsum) not_false
    refine ⟨fun p => if p = 2 then (T - (if T % 2 = 0 then 0 else 3)) / 2
      else if p = 3 then (if T % 2 = 0 then 0 else 1) else 0, ?_⟩
    dsimp only
    rw [sum_eq_pair h2m h3m (by norm_num)
      (fun p => (if p = 2 then (T - (if T % 2 = 0 then 0 else 3)) / 2
        else if p = 3 then (if T % 2 = 0 then 0 else 1) else 0) * p)
      (fun p _ hp2 hp3 => by
        dsimp only
        rw [if_neg hp2, if_neg hp3]
        exact zero_mul p)]
    rw [if_pos rfl, if_neg (by norm_num : (3 : ℕ) ≠ 2), if_pos rfl]
    rcases Nat.even_or_odd T with he | ho
    · have h2 : T % 2 = 0 := Nat.even_iff.mp he
      rw [if_pos h2, if_pos h2]
      omega
    · have h2' : ¬ T % 2 = 0 := by
        have := Nat.odd_iff.mp ho
        omega
      rw [if_neg h2', if_neg h2']
      omega
  · -- 2 ∤ n: weights 1, 2, 4 are all impossible; ℕ3 + ℕ5 + ℕ7 covers the rest
    rcases Nat.eq_zero_or_pos T with hT0 | hTpos
    · exact ⟨0, by simp [hT0]⟩
    have hT1 : T ≠ 1 := fun h1 =>
      absurd (no_weight_one hζ.pow_eq_one hn w (hT ▸ h1) hsum) not_false
    have hT2 : T ≠ 2 := by
      intro h2
      have hcard : Multiset.card (expMultiset n w) = 2 := by
        rw [expMultiset_card, ← hT, h2]
      obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
      have h := expMultiset_sum n w ζ
      rw [hab] at h
      simp at h
      rw [hsum] at h
      have hpow : ∀ e : ℕ, (ζ ^ e) ^ n = 1 := fun e => by
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      exact h2n (two_dvd_of_pair_sum_eq_zero hn (hpow a) (hpow b)
        (by linear_combination h))
    have hT4 : T ≠ 4 := fun h4 =>
      h2n (two_dvd_of_weight_four hn hζ.pow_eq_one w (hT ▸ h4) hsum)
    have h7m : 7 ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, h7n, hn.ne'⟩
    -- T ∉ {0,1,2,4}: write T = 3x + 5y + 7z by residue mod 3
    obtain ⟨x, y, z, hxyz⟩ : ∃ x y z : ℕ, T = 3 * x + 5 * y + 7 * z := by
      rcases Nat.lt_or_ge T 3 with h | h
      · omega
      have h3cases : T % 3 = 0 ∨ T % 3 = 1 ∨ T % 3 = 2 := by omega
      rcases h3cases with h0 | h1 | h2
      · exact ⟨T / 3, 0, 0, by omega⟩
      · -- T ≡ 1 mod 3, T ≥ 3, T ≠ 4 → T ≥ 7
        exact ⟨(T - 7) / 3, 0, 1, by omega⟩
      · -- T ≡ 2 mod 3, T ≥ 3 → T ≥ 5
        exact ⟨(T - 5) / 3, 1, 0, by omega⟩
    refine ⟨fun p => if p = 3 then x else if p = 5 then y
      else if p = 7 then z else 0, ?_⟩
    dsimp only
    rw [sum_eq_triple h3m h5m h7m (by norm_num) (by norm_num) (by norm_num)
      (fun p => (if p = 3 then x else if p = 5 then y
        else if p = 7 then z else 0) * p)
      (fun p _ hp3 hp5 hp7 => by
        dsimp only
        rw [if_neg hp3, if_neg hp5, if_neg hp7]
        exact zero_mul p)]
    rw [if_pos rfl, if_neg (by norm_num : (5 : ℕ) ≠ 3), if_pos rfl,
      if_neg (by norm_num : (7 : ℕ) ≠ 3), if_neg (by norm_num : (7 : ℕ) ≠ 5),
      if_pos rfl]
    omega

end DeBruijnLamLeungSmallWeights

#print axioms DeBruijnLamLeungSmallWeights.two_dvd_of_quadruple_sum_eq_zero
#print axioms DeBruijnLamLeungSmallWeights.two_dvd_of_weight_four
#print axioms DeBruijnLamLeungSmallWeights.lam_leung_of_105_dvd
