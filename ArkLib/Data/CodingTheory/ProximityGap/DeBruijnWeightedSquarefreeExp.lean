/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedSquarefree
import ArkLib.Data.CodingTheory.ProximityGap.WeightedThreadSplit

/-!
# Issue #232 — the weighted squarefree classification on the EXPONENT surface (O102)

O100 proved de Bruijn weighted at the squarefree base on the CRT grid; the named
remaining bookkeeping's hard half is the grid ↔ exponent-surface transport.  This
file lands it: for `n = p·q` (`p ≠ q` primes), `ζ` a primitive `n`-th root
(char 0), `w : ℕ → ℕ`,

    `∑_{e<pq} w_e·ζ^e = 0   ⟺   ∃ A B : ℕ → ℕ, ∀ e < pq,
        w e = A (e % q) + B (e % p)`

— the ℕ-combination of full prime packets in exponent coordinates (`e % q` is the
base of `e`'s `μ_p`-packet, `e % p` of its `μ_q`-packet).

Mechanism:
* forward: the CRT bijection `e ↔ (e % p, e % q)` — explicit section
  `(i, j) ↦ (e₁·i + e₂·j) % pq` with `e₁, e₂` from `Nat.chineseRemainder` at
  `(1,0)` and `(0,1)` — transports the sum onto the grid
  (`ζ^e = (ζ^{e₁})^{e%p}·(ζ^{e₂})^{e%q}`; the coordinate roots are primitive by
  `pow_of_coprime`, no order computation), where O100
  `debruijn_weighted_squarefree` classifies;
* converse: NO transport needed — O101 `weighted_sum_eq_thread_sum` regroups each
  part along its own packet direction and the full geometric sums kill both.

Falsify-first cover: the statement is the exponent-surface paraphrase of the O100
grid iff (probe `probe_weighted_squarefree_grid.py`, exhaustive); the inline O101
probe's thread product law covers the regrouping.  No new analytic content.

Honest scope: the squarefree base, exponent surface.  The last remaining step to
full weighted `p^a·q^b` is the digit-descent induction (iterate O101 down to this
base through `e = r + g·e''` and reassemble the combination functions) — pure
bookkeeping, queued.
-/

namespace DeBruijnWeightedSquarefreeExp

open Polynomial Finset

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- `ζ` absorbs reduction of exponents mod `n`. -/
lemma pow_mod_eq {n : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ n) (x : ℕ) :
    ζ ^ (x % n) = ζ ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x n]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

/-- **The weighted squarefree classification, exponent surface** (O100 transported):
for `p ≠ q` primes and `ζ` a primitive `pq`-th root of unity in characteristic
zero, an ℕ-weighted power sum vanishes iff the weight function is an
ℕ-combination of full prime packets: `w e = A (e % q) + B (e % p)`. -/
theorem debruijn_weighted_squarefree_exp {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q)) (w : ℕ → ℕ) :
    (∑ e ∈ Finset.range (p * q), (w e : L) * ζ ^ e = 0) ↔
      ∃ A B : ℕ → ℕ, ∀ e < p * q, w e = A (e % q) + B (e % p) := by
  classical
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hnpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  constructor
  · -- forward: transport to the grid, classify there
    intro hsum
    obtain ⟨e₁, he₁p, he₁q⟩ := Nat.chineseRemainder hco 1 0
    obtain ⟨e₂, he₂p, he₂q⟩ := Nat.chineseRemainder hco 0 1
    -- digit identities of the section
    have hmodp : ∀ i j : ℕ, (e₁ * i + e₂ * j) % p = i % p := by
      intro i j
      have h : e₁ * i + e₂ * j ≡ 1 * i + 0 * j [MOD p] :=
        Nat.ModEq.add (he₁p.mul_right i) (he₂p.mul_right j)
      simpa only [one_mul, zero_mul, add_zero] using h
    have hmodq : ∀ i j : ℕ, (e₁ * i + e₂ * j) % q = j % q := by
      intro i j
      have h : e₁ * i + e₂ * j ≡ 0 * i + 1 * j [MOD q] :=
        Nat.ModEq.add (he₁q.mul_right i) (he₂q.mul_right j)
      simpa only [one_mul, zero_mul, zero_add] using h
    have hpdq : p ∣ p * q := ⟨q, rfl⟩
    have hqdq : q ∣ p * q := ⟨p, Nat.mul_comm p q⟩
    -- the section inverts the residue map below `pq`
    have hsection : ∀ e < p * q, (e₁ * (e % p) + e₂ * (e % q)) % (p * q) = e := by
      intro e he
      have h1 : (e₁ * (e % p) + e₂ * (e % q)) % (p * q) % p = e % p := by
        rw [Nat.mod_mod_of_dvd _ hpdq, hmodp, Nat.mod_mod_of_dvd _ (dvd_refl p)]
      have h2 : (e₁ * (e % p) + e₂ * (e % q)) % (p * q) % q = e % q := by
        rw [Nat.mod_mod_of_dvd _ hqdq, hmodq, Nat.mod_mod_of_dvd _ (dvd_refl q)]
      have h3 : (e₁ * (e % p) + e₂ * (e % q)) % (p * q) ≡ e [MOD p * q] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨h1, h2⟩
      have h4 : (e₁ * (e % p) + e₂ * (e % q)) % (p * q) % (p * q) = e % (p * q) := h3
      rwa [Nat.mod_mod_of_dvd _ (dvd_refl (p * q)), Nat.mod_eq_of_lt he] at h4
    -- the coordinate roots are primitive
    have hqdvd₁ : q ∣ e₁ := (Nat.modEq_zero_iff_dvd).mp he₁q
    have hpdvd₂ : p ∣ e₂ := (Nat.modEq_zero_iff_dvd).mp he₂p
    have hpnd₁ : ¬ p ∣ e₁ := by
      intro hdvd
      obtain ⟨k, hk⟩ := hdvd
      have h0 : e₁ % p = 0 := by rw [hk]; exact Nat.mul_mod_right p k
      have h1 : e₁ % p = 1 % p := he₁p
      have h2 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
      omega
    have hqnd₂ : ¬ q ∣ e₂ := by
      intro hdvd
      obtain ⟨k, hk⟩ := hdvd
      have h0 : e₂ % q = 0 := by rw [hk]; exact Nat.mul_mod_right q k
      have h1 : e₂ % q = 1 % q := he₂q
      have h2 : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
      omega
    obtain ⟨c₁, hc₁⟩ := hqdvd₁
    obtain ⟨c₂, hc₂⟩ := hpdvd₂
    have hpc₁ : ¬ p ∣ c₁ := fun hd => hpnd₁ (hc₁ ▸ hd.mul_left q)
    have hqc₂ : ¬ q ∣ c₂ := fun hd => hqnd₂ (hc₂ ▸ hd.mul_left p)
    have hξ : IsPrimitiveRoot (ζ ^ e₁) p := by
      have h := (hζ.pow hnpos (Nat.mul_comm p q)).pow_of_coprime c₁
        (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpc₁))
      rwa [← pow_mul, ← hc₁] at h
    have hη : IsPrimitiveRoot (ζ ^ e₂) q := by
      have h := (hζ.pow hnpos rfl).pow_of_coprime c₂
        (Nat.coprime_comm.mp (hq.coprime_iff_not_dvd.mpr hqc₂))
      rwa [← pow_mul, ← hc₂] at h
    -- the exponent identity
    have hexp : ∀ i j : ℕ,
        (ζ ^ e₁) ^ i * (ζ ^ e₂) ^ j = ζ ^ ((e₁ * i + e₂ * j) % (p * q)) := by
      intro i j
      rw [← pow_mul, ← pow_mul, ← pow_add, pow_mod_eq hζ]
    -- the transport
    have htrans : ∑ e ∈ Finset.range (p * q), (w e : L) * ζ ^ e
        = ∑ x ∈ Finset.range p ×ˢ Finset.range q,
            (w ((e₁ * x.1 + e₂ * x.2) % (p * q)) : L)
              * ((ζ ^ e₁) ^ x.1 * (ζ ^ e₂) ^ x.2) := by
      refine Finset.sum_nbij' (fun e => (e % p, e % q))
        (fun x => (e₁ * x.1 + e₂ * x.2) % (p * q)) ?_ ?_ ?_ ?_ ?_
      · intro e _
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨Nat.mod_lt _ hp.pos, Nat.mod_lt _ hq.pos⟩
      · intro x _
        rw [Finset.mem_range]
        exact Nat.mod_lt _ hnpos
      · intro e he
        exact hsection e (Finset.mem_range.mp he)
      · rintro ⟨i, j⟩ hx
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
        have h1 : (e₁ * i + e₂ * j) % (p * q) % p = i := by
          rw [Nat.mod_mod_of_dvd _ hpdq, hmodp, Nat.mod_eq_of_lt hx.1]
        have h2 : (e₁ * i + e₂ * j) % (p * q) % q = j := by
          rw [Nat.mod_mod_of_dvd _ hqdq, hmodq, Nat.mod_eq_of_lt hx.2]
        exact Prod.ext h1 h2
      · intro e he
        rw [hsection e (Finset.mem_range.mp he)]
        congr 1
        rw [hexp (e % p) (e % q), hsection e (Finset.mem_range.mp he)]
    rw [htrans, Finset.sum_product] at hsum
    obtain ⟨α, β, hαβ⟩ :=
      (DeBruijnWeightedSquarefree.debruijn_weighted_squarefree hp hq hpq hξ hη
        (fun i j => w ((e₁ * i + e₂ * j) % (p * q)))).mp (by
          refine Eq.trans ?_ hsum
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [mul_assoc])
    refine ⟨β, α, fun e he => ?_⟩
    have h := hαβ (e % p) (Nat.mod_lt _ hp.pos) (e % q) (Nat.mod_lt _ hq.pos)
    simp only [hsection e he] at h
    omega
  · -- converse: each part dies along its own packet direction (O101 regrouping)
    rintro ⟨A, B, hAB⟩
    have hsplit : ∑ e ∈ Finset.range (p * q), (w e : L) * ζ ^ e
        = (∑ e ∈ Finset.range (p * q), (A (e % q) : L) * ζ ^ e)
          + ∑ e ∈ Finset.range (p * q), (B (e % p) : L) * ζ ^ e := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hAB e (Finset.mem_range.mp he)]
      push_cast
      ring
    have hA0 : ∑ e ∈ Finset.range (p * q), (A (e % q) : L) * ζ ^ e = 0 := by
      have hrw : ∑ e ∈ Finset.range (p * q), (A (e % q) : L) * ζ ^ e
          = ∑ e ∈ Finset.range (q * p), (A (e % q) : L) * ζ ^ e := by
        rw [Nat.mul_comm]
      rw [hrw, WeightedThreadSplit.weighted_sum_eq_thread_sum hq.pos ζ
        (fun e => A (e % q))]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hconst : ∀ e' ∈ Finset.range p,
          (A ((r + q * e') % q) : L) * (ζ ^ q) ^ e' = (A r : L) * (ζ ^ q) ^ e' := by
        intro e' _
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum,
        (hζ.pow hnpos (Nat.mul_comm p q)).geom_sum_eq_zero hp.one_lt, mul_zero,
        mul_zero]
    have hB0 : ∑ e ∈ Finset.range (p * q), (B (e % p) : L) * ζ ^ e = 0 := by
      rw [WeightedThreadSplit.weighted_sum_eq_thread_sum hp.pos ζ
        (fun e => B (e % p))]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hconst : ∀ e' ∈ Finset.range q,
          (B ((r + p * e') % p) : L) * (ζ ^ p) ^ e' = (B r : L) * (ζ ^ p) ^ e' := by
        intro e' _
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum,
        (hζ.pow hnpos rfl).geom_sum_eq_zero hq.one_lt, mul_zero, mul_zero]
    rw [hsplit, hA0, hB0, add_zero]

/-! ## Teeth (fired at `ℂ`, `n = 6`) -/

/-- The converse FIRED: the all-ones weight on `[0, 6)` vanishes against `ζ₆` —
`Σ_{e<6} ζ₆^e = 0` produced from the packet split `1 = 1 + 0`. -/
example : ∑ e ∈ Finset.range (2 * 3), ((1 : ℕ) : ℂ)
    * Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)) ^ e = 0 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)))
      (2 * 3) := by
    have h := Complex.isPrimitiveRoot_exp 6 (by norm_num)
    norm_num at h ⊢
    exact h
  exact (debruijn_weighted_squarefree_exp Nat.prime_two Nat.prime_three
    (by norm_num) hζ (fun _ => 1)).mpr ⟨fun _ => 1, fun _ => 0, fun e _ => rfl⟩

end DeBruijnWeightedSquarefreeExp

#print axioms DeBruijnWeightedSquarefreeExp.debruijn_weighted_squarefree_exp
