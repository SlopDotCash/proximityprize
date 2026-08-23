/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G102: depth five is out of reach of cardinality + pair-sum concentration (no-go)

G87 discharged the depth-four cutoff of the padded collision lane from a single input: the
**pair-sum concentration** `M = max_c pairCount S c`, with the chain `J_4 ≤ (M+1)·n^6` fed by
the Stepanov-method bound `M ≤ ~4 n^{2/3}` (Garcia–Voloch / Heath-Brown–Konyagin).  The depth-5
analog `J_5 ≤ (M+1)·n^8` was reported ~`2^26` over the production Wick budget, leaving open
whether a smarter `(n, M)`-chain or better concentration constants could close depth 5.

**This file proves they cannot.**  The chain is extremally tight in both parameters: an
"interval × Sidon" hybrid witness

  `S = { 5M·x + u : x ∈ ETSidon(b), u ∈ [0, M) }`   (Erdős–Turán Sidon set of prime size `b`)

has cardinality `b·M`, pair-sum concentration `≤ 2M`, and — by Cauchy–Schwarz against its
`O(M b²)`-sized sum support — depth-5 equal-sum mass `J_5 ≥ (bM)^{10}/(50Mb² + 5M + 1)`.
At `(b, M) = (509, 2^21)` (so `n ≈ 2^30` and `2M = 2^22 = 4·n^{2/3}` = exactly the Stepanov
level) the witness exceeds the production depth-5 budget by more than `2^16`:

  `219‼ · (2^30)^5  <  J_5(S) · C(110,5)² · 105!`.

Hence **no sound envelope in `(cardinality, pair-sum concentration)` alone — valid for all
sets — can absorb the depth-5 sector**: any such envelope must exceed the budget at the very
input values the production instance supplies.  (The probe further measures that even perfect
concentration `M = 2`, i.e. Sidon-optimal, has witnesses at `n^8/10`, above budget: the `(n,M)`
window at depth 5 is empty.  Kernel margin here uses the hybrid, `2^16`-safe.)

Consequence for the tool-shape doctrine: the certificate that closes depth ≥ 5 must see
**triple-scale or genuinely multiplicative** structure of `μ_n`, not any pair statistic.
Probe: `scripts/probes/probe_466_g102_pair_concentration_tightness.py`.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo

open Finset
open scoped Nat

/-! ## Depth-`s` equal-sum mass over ℕ and the Cauchy–Schwarz floor -/

/-- Ordered `s`-tuples drawn from `S`. -/
def tuples (s : ℕ) (S : Finset ℕ) : Finset (Fin s → ℕ) :=
  Fintype.piFinset fun _ => S

/-- Number of ordered `s`-tuples from `S` with sum `a`. -/
def tupleCount (s : ℕ) (S : Finset ℕ) (a : ℕ) : ℕ :=
  ((tuples s S).filter fun f => ∑ i, f i = a).card

/-- The achievable `s`-fold sums. -/
def sumImage (s : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (tuples s S).image fun f => ∑ i, f i

/-- Ordered pairs of `s`-tuples with equal sums — the depth-`s` equal-sum core universe
`J_s`, the exact counting currency of the G87/G88 sector envelopes. -/
def equalSumTuplePairs (s : ℕ) (S : Finset ℕ) : ℕ :=
  ((tuples s S ×ˢ tuples s S).filter fun q => (∑ i, q.1 i) = ∑ i, q.2 i).card

/-- Ordered pairs from `S` with sum `c` (the ℕ shape of G87's `pairCount`). -/
def pairCount (S : Finset ℕ) (c : ℕ) : ℕ :=
  ((S ×ˢ S).filter fun q => q.1 + q.2 = c).card

theorem card_tuples (s : ℕ) (S : Finset ℕ) : (tuples s S).card = S.card ^ s := by
  simp [tuples, Fintype.card_piFinset]

theorem sum_tupleCount (s : ℕ) (S : Finset ℕ) :
    ∑ a ∈ sumImage s S, tupleCount s S a = S.card ^ s := by
  rw [← card_tuples s S]
  exact (Finset.card_eq_sum_card_fiberwise fun f hf =>
    Finset.mem_image_of_mem _ hf).symm

/-- The equal-sum fiber over a fixed common sum is a product of two tuple fibers. -/
theorem equalSum_fiber (s : ℕ) (S : Finset ℕ) (a : ℕ) :
    (((tuples s S ×ˢ tuples s S).filter fun q => (∑ i, q.1 i) = ∑ i, q.2 i).filter
        fun q => (∑ i, q.1 i) = a) =
      ((tuples s S).filter fun f => ∑ i, f i = a) ×ˢ
        ((tuples s S).filter fun f => ∑ i, f i = a) := by
  ext q
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, heq⟩, ha⟩
    exact ⟨⟨h1, ha⟩, h2, heq.symm.trans ha⟩
  · rintro ⟨⟨h1, ha1⟩, h2, ha2⟩
    exact ⟨⟨⟨h1, h2⟩, ha1.trans ha2.symm⟩, ha1⟩

set_option maxHeartbeats 1600000 in
theorem equalSumTuplePairs_eq_sum_sq (s : ℕ) (S : Finset ℕ) :
    equalSumTuplePairs s S = ∑ a ∈ sumImage s S, tupleCount s S a ^ 2 := by
  unfold equalSumTuplePairs
  have hmem : ∀ q ∈ (tuples s S ×ˢ tuples s S).filter
      (fun q : (Fin s → ℕ) × (Fin s → ℕ) => (∑ i, q.1 i) = ∑ i, q.2 i),
      (∑ i, q.1 i) ∈ sumImage s S := by
    intro q hq
    exact Finset.mem_image_of_mem (fun f => ∑ i, f i)
      (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [equalSum_fiber, Finset.card_product, tupleCount, sq]

/-- **Cauchy–Schwarz floor**: the equal-sum mass is at least `n^{2s}` over the sum-support
size. -/
theorem cs_floor (s : ℕ) (S : Finset ℕ) :
    (S.card ^ s) ^ 2 ≤ (sumImage s S).card * equalSumTuplePairs s S := by
  rw [equalSumTuplePairs_eq_sum_sq, ← sum_tupleCount s S]
  exact sq_sum_le_card_mul_sum_sq

/-- Sets inside `[0, L]` have `s`-fold sums inside `[0, sL]`. -/
theorem sumImage_card_le {s L : ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, x ≤ L) :
    (sumImage s S).card ≤ s * L + 1 := by
  have hsub : sumImage s S ⊆ Finset.range (s * L + 1) := by
    intro a ha
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc ∑ i, f i ≤ ∑ _i : Fin s, L :=
          Finset.sum_le_sum fun i _ => hS _ (Fintype.mem_piFinset.mp hf i)
      _ = s * L := by simp [mul_comm]
  simpa using Finset.card_le_card hsub

/-- The bounded-support Cauchy–Schwarz floor. -/
theorem cs_floor_of_bounded {s L : ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, x ≤ L) :
    (S.card ^ s) ^ 2 ≤ (s * L + 1) * equalSumTuplePairs s S :=
  (cs_floor s S).trans (Nat.mul_le_mul_right _ (sumImage_card_le hS))

/-! ## The Erdős–Turán Sidon set -/

section ETSidon

variable (p : ℕ)

/-- The Erdős–Turán map `i ↦ 2p·i + (i² mod p)`. -/
def etFun (i : ℕ) : ℕ := 2 * p * i + i * i % p

/-- The Erdős–Turán Sidon set of a prime `p`, inside `[0, 2p²)`. -/
def etSidon : Finset ℕ := (Finset.range p).image (etFun p)

variable {p}

theorem etFun_lt (hp : 0 < p) {i : ℕ} (hi : i < p) : etFun p i < 2 * p ^ 2 := by
  have h1 : i * i % p < p := Nat.mod_lt _ hp
  have h2 : 2 * p * (i + 1) ≤ 2 * p * p := Nat.mul_le_mul_left _ hi
  have h3 : 2 * p * (i + 1) = 2 * p * i + 2 * p := by ring
  have h4 : 2 * p * p = 2 * p ^ 2 := by ring
  unfold etFun
  omega

theorem etFun_div (hp : 0 < p) (i : ℕ) : etFun p i / (2 * p) = i := by
  unfold etFun
  rw [Nat.mul_add_div (by omega)]
  have : i * i % p < 2 * p := lt_of_lt_of_le (Nat.mod_lt _ hp) (by omega)
  simp [Nat.div_eq_of_lt this]

theorem etFun_injective (hp : 0 < p) : Function.Injective (etFun p) := by
  intro i j h
  have := congrArg (· / (2 * p)) h
  simpa [etFun_div hp] using this

theorem card_etSidon (hp : 0 < p) : (etSidon p).card = p := by
  rw [etSidon, Finset.card_image_of_injective _ (etFun_injective hp), Finset.card_range]

theorem etSidon_le (hp : 0 < p) : ∀ x ∈ etSidon p, x ≤ 2 * p ^ 2 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact le_of_lt (etFun_lt hp (Finset.mem_range.mp hi))

/-- **The Erdős–Turán four-point rigidity**: an additive coincidence of `etFun` values forces
the index pairs to agree (as unordered pairs).  This is the classical argument: the `2p`-digit
splits the coincidence into `i + j = k + l` (exactly, in ℕ) and `i² + j² ≡ k² + l² (mod p)`;
in `ZMod p` this yields `(i−k)(i−l) = 0`, and a field has no zero divisors. -/
theorem etFun_add_rigid (hp : p.Prime) (hp2 : p ≠ 2) {i j k l : ℕ}
    (hi : i < p) (hj : j < p) (hk : k < p) (hl : l < p)
    (h : etFun p i + etFun p j = etFun p k + etFun p l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hmi : i * i % p < p := Nat.mod_lt _ hp0
  have hmj : j * j % p < p := Nat.mod_lt _ hp0
  have hmk : k * k % p < p := Nat.mod_lt _ hp0
  have hml : l * l % p < p := Nat.mod_lt _ hp0
  have hEq : 2 * p * (i + j) + (i * i % p + j * j % p)
      = 2 * p * (k + l) + (k * k % p + l * l % p) := by
    have e1 : 2 * p * (i + j) = 2 * p * i + 2 * p * j := by ring
    have e2 : 2 * p * (k + l) = 2 * p * k + 2 * p * l := by ring
    unfold etFun at h
    omega
  -- digit split
  have hxlt : i * i % p + j * j % p < 2 * p := by omega
  have hylt : k * k % p + l * l % p < 2 * p := by omega
  have hdiv : i + j = k + l := by
    have h1 := congrArg (· / (2 * p)) hEq
    simp only at h1
    have hx0 : (i * i % p + j * j % p) / (2 * p) = 0 := Nat.div_eq_of_lt hxlt
    have hy0 : (k * k % p + l * l % p) / (2 * p) = 0 := Nat.div_eq_of_lt hylt
    rwa [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), hx0, hy0,
      Nat.add_zero, Nat.add_zero] at h1
  have hmod : i * i % p + j * j % p = k * k % p + l * l % p := by
    have h1 := congrArg (· % (2 * p)) hEq
    simp only at h1
    have hx0 : (i * i % p + j * j % p) % (2 * p) = i * i % p + j * j % p :=
      Nat.mod_eq_of_lt hxlt
    have hy0 : (k * k % p + l * l % p) % (2 * p) = k * k % p + l * l % p :=
      Nat.mod_eq_of_lt hylt
    rwa [Nat.mul_add_mod, Nat.mul_add_mod, hx0, hy0] at h1
  -- pass to ZMod p
  have hq : (i : ZMod p) ^ 2 + (j : ZMod p) ^ 2 = (k : ZMod p) ^ 2 + (l : ZMod p) ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hmod
    push_cast [ZMod.natCast_mod] at h1
    linear_combination h1
  have hσ : (i : ZMod p) + j = (k : ZMod p) + l := by
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hdiv
    push_cast at h1
    exact h1
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hcast : ((2 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_ofNat]
      exact h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hcast
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge := hp.two_le
    exact hp2 (by omega)
  have hkl : (k : ZMod p) * l = (i : ZMod p) * j := by
    have e1 : (2 : ZMod p) * ((i : ZMod p) * j)
        = ((i : ZMod p) + j) ^ 2 - ((i : ZMod p) ^ 2 + (j : ZMod p) ^ 2) := by ring
    have e2 : (2 : ZMod p) * ((k : ZMod p) * l)
        = ((k : ZMod p) + l) ^ 2 - ((k : ZMod p) ^ 2 + (l : ZMod p) ^ 2) := by ring
    have : (2 : ZMod p) * ((k : ZMod p) * l) = 2 * ((i : ZMod p) * j) := by
      rw [e1, e2, hσ, hq]
    exact mul_left_cancel₀ h2ne this
  have hprod : ((i : ZMod p) - k) * ((i : ZMod p) - l) = 0 := by
    have expand : ((i : ZMod p) - k) * ((i : ZMod p) - l)
        = (i : ZMod p) ^ 2 - (i : ZMod p) * ((k : ZMod p) + l) + (k : ZMod p) * l := by
      ring
    rw [expand, ← hσ, hkl]
    ring
  have valEq : ∀ {a b : ℕ}, a < p → b < p → (a : ZMod p) = b → a = b := by
    intro a b ha hb hab
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
  rcases mul_eq_zero.mp hprod with h0 | h0
  · left
    have hik : i = k := valEq hi hk (sub_eq_zero.mp h0)
    exact ⟨hik, by omega⟩
  · right
    have hil : i = l := valEq hi hl (sub_eq_zero.mp h0)
    exact ⟨hil, by omega⟩

/-- **The Erdős–Turán set is Sidon**: every pair-sum fiber has at most two ordered pairs. -/
theorem pairCount_etSidon_le (hp : p.Prime) (hp2 : p ≠ 2) (c : ℕ) :
    pairCount (etSidon p) c ≤ 2 := by
  classical
  by_cases hne : ((etSidon p ×ˢ etSidon p).filter fun q => q.1 + q.2 = c).Nonempty
  · obtain ⟨⟨x₀, y₀⟩, h₀⟩ := hne
    simp only [mem_filter, mem_product] at h₀
    obtain ⟨⟨hx₀, hy₀⟩, hc₀⟩ := h₀
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hx₀
    obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_image.mp hy₀
    have hsub : ((etSidon p ×ˢ etSidon p).filter fun q => q.1 + q.2 = c) ⊆
        {(etFun p i₀, etFun p j₀), (etFun p j₀, etFun p i₀)} := by
      intro q hq
      obtain ⟨x, y⟩ := q
      simp only [mem_filter, mem_product] at hq
      obtain ⟨⟨hx, hy⟩, hcxy⟩ := hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hcoin : etFun p i + etFun p j = etFun p i₀ + etFun p j₀ := by
        rw [hcxy, hc₀]
      rcases etFun_add_rigid hp hp2 (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
          (Finset.mem_range.mp hi₀) (Finset.mem_range.mp hj₀) hcoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2
        exact Finset.mem_insert_self _ _
      · subst h1; subst h2
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    unfold pairCount
    refine (Finset.card_le_card hsub).trans ?_
    exact (Finset.card_insert_le _ _).trans (by simp)
  · unfold pairCount
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end ETSidon

/-! ## The interval × Sidon hybrid witness -/

section Hybrid

variable (p M : ℕ)

/-- The hybrid witness: an Erdős–Turán Sidon set of prime size `p`, fattened by the interval
`[0, M)` at spacing `5M`. -/
def hybrid : Finset ℕ :=
  ((etSidon p) ×ˢ Finset.range M).image fun q => 5 * M * q.1 + q.2

variable {p M}

theorem hybrid_inj (hM : 0 < M) : Set.InjOn (fun q : ℕ × ℕ => 5 * M * q.1 + q.2)
    ((etSidon p ×ˢ Finset.range M : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro ⟨x, u⟩ hx ⟨y, v⟩ hy h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx hy
  simp only at h
  have hu : u < 5 * M := by omega
  have hv : v < 5 * M := by omega
  have hdivx := congrArg (· / (5 * M)) h
  simp only at hdivx
  rw [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hv] at hdivx
  have hx_eq : x = y := by omega
  have hmodx := congrArg (· % (5 * M)) h
  simp only at hmodx
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at hmodx
  exact Prod.ext hx_eq hmodx

theorem card_hybrid (hp : 0 < p) (hM : 0 < M) : (hybrid p M).card = p * M := by
  rw [hybrid, Finset.card_image_of_injOn (hybrid_inj hM), Finset.card_product,
    card_etSidon hp, Finset.card_range]

theorem hybrid_le (hp : 0 < p) : ∀ x ∈ hybrid p M, x ≤ 10 * M * p ^ 2 + M := by
  intro x hx
  obtain ⟨⟨y, u⟩, hy, rfl⟩ := Finset.mem_image.mp hx
  simp only [Finset.mem_product, Finset.mem_range] at hy
  have h1 : y ≤ 2 * p ^ 2 := etSidon_le hp _ hy.1
  calc 5 * M * y + u ≤ 5 * M * (2 * p ^ 2) + M :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) hy.2.le
    _ = 10 * M * p ^ 2 + M := by ring

/-- Pair-sum fibers of the hybrid inject into (Sidon pair fiber) × (interval pair fiber). -/
theorem pairCount_hybrid_le (hp : p.Prime) (hp2 : p ≠ 2) (hM : 0 < M) (c : ℕ) :
    pairCount (hybrid p M) c ≤ 2 * M := by
  classical
  have key : pairCount (hybrid p M) c ≤
      pairCount (etSidon p) (c / (5 * M)) * pairCount (Finset.range M) (c % (5 * M)) := by
    unfold pairCount
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn
      (fun q => ((q.1 / (5 * M), q.2 / (5 * M)), (q.1 % (5 * M), q.2 % (5 * M))))
    · rintro ⟨x, y⟩ hq
      have hq2 : (x, y) ∈ ((hybrid p M ×ˢ hybrid p M).filter
          fun q : ℕ × ℕ => q.1 + q.2 = c) := hq
      have hx := (Finset.mem_product.mp (Finset.mem_filter.mp hq2).1).1
      have hy := (Finset.mem_product.mp (Finset.mem_filter.mp hq2).1).2
      have hsum : x + y = c := (Finset.mem_filter.mp hq2).2
      obtain ⟨⟨a, u⟩, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨⟨b, v⟩, hb, rfl⟩ := Finset.mem_image.mp hy
      simp only [Finset.mem_product, Finset.mem_range] at ha hb
      have hu : u < 5 * M := by omega
      have hv : v < 5 * M := by omega
      have hda : (5 * M * a + u) / (5 * M) = a := by
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hu, Nat.add_zero]
      have hdb : (5 * M * b + v) / (5 * M) = b := by
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hv, Nat.add_zero]
      have hma : (5 * M * a + u) % (5 * M) = u := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
      have hmb : (5 * M * b + v) % (5 * M) = v := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
      have hsum' : 5 * M * (a + b) + (u + v) = c := by
        rw [← hsum]; ring
      have huv : u + v < 5 * M := by omega
      have hcd : c / (5 * M) = a + b := by
        rw [← hsum', Nat.mul_add_div (by omega), Nat.div_eq_of_lt huv, Nat.add_zero]
      have hcm : c % (5 * M) = u + v := by
        rw [← hsum', Nat.mul_add_mod, Nat.mod_eq_of_lt huv]
      show (((5 * M * a + u) / (5 * M), (5 * M * b + v) / (5 * M)),
        ((5 * M * a + u) % (5 * M), (5 * M * b + v) % (5 * M))) ∈ _
      rw [hda, hdb, hma, hmb]
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha.1, hb.1⟩, hcd.symm⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr ha.2, Finset.mem_range.mpr hb.2⟩,
          hcm.symm⟩⟩
    · rintro ⟨x, y⟩ - ⟨x', y'⟩ - h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨hd1, hd2⟩, hm1, hm2⟩ := h
      have e1 := Nat.div_add_mod x (5 * M)
      have e2 := Nat.div_add_mod y (5 * M)
      have e3 := Nat.div_add_mod x' (5 * M)
      have e4 := Nat.div_add_mod y' (5 * M)
      rw [hd1, hm1] at e1
      rw [hd2, hm2] at e2
      have hxx : x = x' := by omega
      have hyy : y = y' := by omega
      simp [hxx, hyy]
  have h1 : pairCount (etSidon p) (c / (5 * M)) ≤ 2 := pairCount_etSidon_le hp hp2 _
  have h2 : pairCount (Finset.range M) (c % (5 * M)) ≤ M := by
    unfold pairCount
    have hsub : ∀ q ∈ (Finset.range M ×ˢ Finset.range M).filter
        (fun q : ℕ × ℕ => q.1 + q.2 = c % (5 * M)), q.1 ∈ Finset.range M :=
      fun q hq => (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have hinj : Set.InjOn (fun q : ℕ × ℕ => q.1)
        (((Finset.range M ×ˢ Finset.range M).filter
          (fun q : ℕ × ℕ => q.1 + q.2 = c % (5 * M)) : Finset (ℕ × ℕ)) :
            Set (ℕ × ℕ)) := by
      rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb h
      have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have h1 : a1 = b1 := h
      simp only at ha' hb'
      have h2 : a2 = b2 := by omega
      simp [h1, h2]
    calc ((Finset.range M ×ˢ Finset.range M).filter
          fun q => q.1 + q.2 = c % (5 * M)).card
        ≤ (Finset.range M).card := Finset.card_le_card_of_injOn _ hsub hinj
      _ = M := Finset.card_range M
  calc pairCount (hybrid p M) c
      ≤ pairCount (etSidon p) (c / (5 * M)) * pairCount (Finset.range M) (c % (5 * M)) := key
    _ ≤ 2 * M := Nat.mul_le_mul h1 h2

end Hybrid

/-! ## The production no-go -/

/-- **Production depth-5 kernel inequality**: the witness Cauchy–Schwarz floor at
`(b, M) = (509, 2^21)` exceeds the depth-5 share of one full Wick budget at
`(n, r) = (2^30, 110)` — with a `2^16` margin. -/
theorem choose_110_5 : Nat.choose 110 5 = 122391522 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rfl

theorem production_depth5_kernel :
    (5 * (10 * 2 ^ 21 * 509 ^ 2 + 2 ^ 21) + 1) *
        (Nat.doubleFactorial 219 * (2 ^ 30) ^ 5)
      < ((509 * 2 ^ 21) ^ 5) ^ 2 * (Nat.choose 110 5 ^ 2 * (105)!) := by
  rw [choose_110_5]
  decide

/-- **Headline no-go.**  There is a set of near-production cardinality whose pair-sum
concentration is exactly the Stepanov level `4·n^{2/3} = 2^22`, yet whose depth-5 equal-sum
mass strictly exceeds the production depth-5 Wick budget.  Hence no envelope of the shape
`(cardinality, pair-sum concentration) ↦ bound`, sound for all sets, can absorb the depth-5
sector: the G87 depth-four mechanism is not extendable, and any depth-≥5 certificate must use
structure invisible to pair statistics. -/
theorem depth5_pair_concentration_no_go :
    ∃ S : Finset ℕ,
      S.card = 509 * 2 ^ 21 ∧
      (∀ c : ℕ, pairCount S c ≤ 2 ^ 22) ∧
      Nat.doubleFactorial 219 * (2 ^ 30) ^ 5 <
        equalSumTuplePairs 5 S * (Nat.choose 110 5 ^ 2 * (105)!) := by
  have hp : (509 : ℕ).Prime := by norm_num
  have hM : (0 : ℕ) < 2 ^ 21 := by positivity
  refine ⟨hybrid 509 (2 ^ 21), card_hybrid hp.pos hM, ?_, ?_⟩
  · intro c
    have := pairCount_hybrid_le (p := 509) (M := 2 ^ 21) hp (by norm_num) hM c
    calc pairCount (hybrid 509 (2 ^ 21)) c ≤ 2 * 2 ^ 21 := this
      _ = 2 ^ 22 := by norm_num
  · -- Cauchy–Schwarz floor against the kernel inequality
    have hfloor := cs_floor_of_bounded (s := 5)
      (L := 10 * 2 ^ 21 * 509 ^ 2 + 2 ^ 21) (S := hybrid 509 (2 ^ 21))
      (hybrid_le hp.pos)
    rw [card_hybrid hp.pos hM] at hfloor
    set D : ℕ := 5 * (10 * 2 ^ 21 * 509 ^ 2 + 2 ^ 21) + 1 with hD
    set J : ℕ := equalSumTuplePairs 5 (hybrid 509 (2 ^ 21)) with hJ
    -- hfloor : ((509 * 2^21) ^ 5) ^ 2 ≤ D * J
    have hkernel := production_depth5_kernel
    rw [← hD] at hkernel
    -- D * (219‼ * (2^30)^5) < ((509·2^21)^5)^2 * (C² * 105!) ≤ D * J * (C² * 105!)
    have hchain : D * (Nat.doubleFactorial 219 * (2 ^ 30) ^ 5)
        < D * (J * (Nat.choose 110 5 ^ 2 * (105)!)) := by
      calc D * (Nat.doubleFactorial 219 * (2 ^ 30) ^ 5)
          < ((509 * 2 ^ 21) ^ 5) ^ 2 * (Nat.choose 110 5 ^ 2 * (105)!) := hkernel
        _ ≤ (D * J) * (Nat.choose 110 5 ^ 2 * (105)!) :=
            Nat.mul_le_mul_right _ hfloor
        _ = D * (J * (Nat.choose 110 5 ^ 2 * (105)!)) := by ring
    exact Nat.lt_of_mul_lt_mul_left hchain

end ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo.cs_floor_of_bounded
#print axioms ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo.etFun_add_rigid
#print axioms
  ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo.pairCount_etSidon_le
#print axioms
  ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo.pairCount_hybrid_le
#print axioms
  ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo.production_depth5_kernel
#print axioms
  ArkLib.ProximityGap.Frontier.G102PairConcentrationDepthFiveNoGo.depth5_pair_concentration_no_go
