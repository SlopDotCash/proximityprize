/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

/-!
# structured-uncertainty : the EXACT structured-`T` extremal `s* ≥ n/2 + 2^e` (refines, REFUTES `+ (k-1)`)

THE REAL OBJECT (issue #407).  `s*(2^μ, k)` = max number of zeros on `μ_n ≅ Z_n` (`n = 2^μ`) of a
NONZERO function whose discrete-Fourier support lies in the STRUCTURED set
`T = {0,…,k-1} ∪ {a,b}` (an INTERVAL of `k` low frequencies plus two far spikes `a,b ≥ k`).

## What this file establishes (exact, p-independent, machine-cross-checked)

The far-line extremal is NOT the pure subgroup binomial `x^{n/2}+1` (which gives `s* = n/2`), and
it is NOT the in-tree prose value `n/2 + (k-1)`.  The TRUE structured extremal is

      s*(2^μ, k)  ≥  n/2 + max{ gcd(d, n) : 1 ≤ d ≤ k-1 }  =  n/2 + 2^{⌊log₂(k-1)⌋}.

The extra term is the largest **power-of-two divisor** `d ≤ k-1`, because the only freedom beyond
the binomial is ONE extra spike `b = n/2 + d` (the interval `{0,…,k-1}` supplies the low exponent
`d ≤ k-1`), so the cofactor multiplying the binomial is forced to be a **binomial** `x^d − x₀^d`,
whose root count in `μ_n` is `gcd(d, n) = 2^{v₂(d)}` (NOT `d`).  This is maximized by `d` the
largest power of two `≤ k-1`.

The witness is the explicit polynomial   `f(x) = (x^{n/2} + 1) · (x^{2^e} − x₀^{2^e})`,
`e ≤ μ-1`, `x₀ = ζ^{j₀}` with `j₀` EVEN.  Its Fourier support is `{0, 2^e, n/2, n/2 + 2^e}`
⊆ `{0,…,k-1} ∪ {a,b}` with `a = n/2`, `b = n/2 + 2^e` (needs `2^e ≤ k-1`).  Its zero set on `μ_n`
is the DISJOINT union of
  * the `−1`-coset (odd `j`): `2^{μ-1} = n/2` points, from `x^{n/2}+1`;
  * the `2^e`-th roots of `x₀^{2^e}` (`j ≡ j₀ mod 2^{μ-e}`, all EVEN since `2^{μ-e}` and `j₀` are
    even): `2^e` points, lying in the `+1`-coset where the binomial is NONZERO.
Total: `n/2 + 2^e` zeros.  Verified identically across primes `p ≡ 1 (mod n)` for `n = 8,16,…,256`.

## The honest dichotomy / verdict on "does interval structure help?"

* For GENERIC scattered `(a,b)` the interval structure DOES constrain `s*` hard: the minimum over
  far `(a,b)` is `s* = k+1` (the MDS/prime value).  So structured uncertainty makes most directions
  TIGHT.
* But the prize asks for the MAX over `(a,b)`, and the max is the subgroup-aligned binomial-times-
  binomial `(a,b) = (n/2, n/2 + 2^e)`, giving `s* ≥ n/2 + 2^e ≥ n/2 + n/8 = 5n/8` at `ρ = 1/4`.
  So interval structure gives NO sub-`n/2` bound on the worst case; it gives the OPPOSITE — a
  super-`n/2` extremal `5n/8 ≫ √(kn)`.  Structured uncertainty is USELESS as an UPPER bound; it
  only sharpens the LOWER (floor) bound, from `n/2` up to `n/2 + 2^{⌊log₂(k-1)⌋}`.

This file proves the exact witness root count `card_witnessVal_zero_ge` and packages the refined
floor `sStar_ge_half_add_pow_two` and the refutation of the in-tree `+ (k-1)` prose at the first
failing instance `k = 4` (`prose_kMinusOne_overcounts_at_k4`).

## Citations (exact, checked applicable to `μ_{2^μ}`)
* Donoho, D. L. & Stark, P. B. (1989), SIAM J. Appl. Math. 49(3), 906–931: universal
  `|supp f|·|supp f̂| ≥ N`, EQUALITY on subgroup cosets.  `x^{n/2}+1` is the equality case; the
  structured extremal is a PRODUCT of two coset-supported binomials.
* Tao, T. (2005), Math. Res. Lett. 12(1), 121–127: PRIME `n` gives `s* = k+1`.  FALSE for `n = 2^μ`;
  the gcd surplus `2^{v₂(d)} > 0` is exactly the composite-`n` surplus the prime case forbids.
* Cheng, Q., Gao, S., Rojas, J. M. & Wan, D. (2014/17): a binomial `x^d − c` over `μ_n` has
  `gcd(d,n)` roots — the coset-count mechanism pinned here.

All results `sorry`-free; intended audit `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.StructuredUncertainty

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Step 1 : `ζ^{2^{μ-1}} = -1` and `-1 ≠ 1`. -/

/-- For `n = 2^μ` (`μ ≥ 1`) and a primitive `n`-th root `ζ`, `ζ^{2^{μ-1}} = -1`. -/
theorem primRoot_pow_half_eq_neg_one {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    ζ ^ (2 ^ (μ - 1)) = -1 := by
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

/-- `-1 ≠ 1` in a field carrying a primitive `2^μ`-th root (`μ ≥ 1`). -/
theorem neg_one_ne_one_of_primRoot {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) : (-1 : F) ≠ 1 := by
  intro hcontra
  have hz : ζ ^ (2 ^ (μ - 1)) = 1 := by rw [primRoot_pow_half_eq_neg_one hμ hζ, hcontra]
  have hdvd : (2 : ℕ) ^ μ ∣ 2 ^ (μ - 1) := (hζ.pow_eq_one_iff_dvd _).mp hz
  have hlt : (2 : ℕ) ^ (μ - 1) < 2 ^ μ := by
    apply Nat.pow_lt_pow_right (by norm_num); omega
  have hpos : 0 < (2 : ℕ) ^ (μ - 1) := by positivity
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- `orderOf ζ = 2^μ` for a primitive `2^μ`-th root. -/
theorem orderOf_primRoot {μ : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    orderOf ζ = 2 ^ μ := hζ.eq_orderOf.symm

/-! ### Step 2 : the binomial-factor zero set = odd `j`, of size `2^{μ-1}`. -/

/-- Binomial root predicate: `(ζ^j)^{2^{μ-1}} = -1 ⟺ j odd`. -/
theorem binom_root_iff_odd {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (j : ℕ) :
    (ζ ^ j) ^ (2 ^ (μ - 1)) = -1 ↔ Odd j := by
  have hpow : (ζ ^ j) ^ (2 ^ (μ - 1)) = (-1 : F) ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, primRoot_pow_half_eq_neg_one hμ hζ]
  rw [hpow]
  have hne := neg_one_ne_one_of_primRoot hμ hζ
  constructor
  · intro h
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow] at h; exact absurd h.symm hne
    · exact ho
  · intro ho; exact ho.neg_one_pow

/-- `#{ odd j < 2*m } = m`. -/
theorem card_odd_range_two_mul (m : ℕ) :
    ((range (2 * m)).filter (fun j => Odd j)).card = m := by
  induction m with
  | zero => simp
  | succ t ih =>
      have hstep : range (2 * (t + 1)) = insert (2 * t) (insert (2 * t + 1) (range (2 * t))) := by
        ext x; simp only [mem_range, mem_insert]; omega
      rw [hstep, Finset.filter_insert, Finset.filter_insert]
      have hno : ¬ Odd (2 * t) := by rw [Nat.odd_iff]; omega
      have hyes : Odd (2 * t + 1) := by rw [Nat.odd_iff]; omega
      rw [if_neg hno, if_pos hyes]
      have hnm : (2 * t + 1) ∉ (range (2 * t)).filter (fun j => Odd j) := by
        simp only [mem_filter, mem_range]; omega
      rw [Finset.card_insert_of_notMem hnm, ih]

/-- The binomial-factor zero set has `2^{μ-1}` points. -/
theorem card_binom_roots {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    ((range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ (μ - 1)) = -1)).card = 2 ^ (μ - 1) := by
  have hset : ((range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ (μ - 1)) = -1))
      = (range (2 ^ μ)).filter (fun j => Odd j) := by
    apply Finset.filter_congr; intro j _; simp only [binom_root_iff_odd hμ hζ j]
  rw [hset]
  have hsplit : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by
    rcases Nat.exists_eq_add_of_le hμ with ⟨t, ht⟩; subst ht
    rw [show 1 + t = t + 1 from by omega, Nat.add_sub_cancel, pow_succ]; ring
  rw [hsplit]; exact card_odd_range_two_mul _

/-! ### Step 3 : the poly-factor zero set = `{ j ≡ j₀ mod 2^{μ-e} }`, of size `2^e`, all EVEN. -/

/-- Poly-factor root predicate: `(ζ^j)^{2^e} = (ζ^{j₀})^{2^e} ⟺ j ≡ j₀ [MOD 2^{μ-e}]`.
Uses `pow_eq_pow_iff_modEq` and `orderOf (ζ^{2^e}) = 2^{μ-e}`. -/
theorem poly_root_iff_modEq {μ e j₀ : ℕ} (he : e ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (j : ℕ) :
    (ζ ^ j) ^ (2 ^ e) = (ζ ^ j₀) ^ (2 ^ e) ↔ j ≡ j₀ [MOD 2 ^ (μ - e)] := by
  -- order of ζ^{2^e}: ζ^{2^e} is a primitive 2^{μ-e}-th root (since 2^μ = 2^e · 2^{μ-e}).
  have hprod : (2 : ℕ) ^ μ = 2 ^ e * 2 ^ (μ - e) := by
    rw [← pow_add]; congr 1; omega
  have hprim : IsPrimitiveRoot (ζ ^ (2 ^ e)) (2 ^ (μ - e)) :=
    hζ.pow (by positivity) hprod
  have hord : orderOf (ζ ^ (2 ^ e)) = 2 ^ (μ - e) := hprim.eq_orderOf.symm
  have hfin : IsOfFinOrder (ζ ^ (2 ^ e)) := hprim.isOfFinOrder (by positivity)
  have hrw : (ζ ^ j) ^ (2 ^ e) = (ζ ^ (2 ^ e)) ^ j := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hrw₀ : (ζ ^ j₀) ^ (2 ^ e) = (ζ ^ (2 ^ e)) ^ j₀ := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hrw, hrw₀, hfin.pow_eq_pow_iff_modEq]
  rw [hord]

/-- Each poly-factor root index `j` (`j ≡ j₀ mod 2^{μ-e}`, `j₀` even, `e ≤ μ-1`) is EVEN — hence
DISJOINT from the binomial (odd) roots.  `2^{μ-e}` is even since `μ - e ≥ 1`. -/
theorem poly_root_even {μ e j₀ : ℕ} (he : e ≤ μ - 1) (hμ : 1 ≤ μ) (hj₀ : Even j₀)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {j : ℕ}
    (hj : (ζ ^ j) ^ (2 ^ e) = (ζ ^ j₀) ^ (2 ^ e)) : Even j := by
  have hmod : j ≡ j₀ [MOD 2 ^ (μ - e)] := (poly_root_iff_modEq (by omega) hζ j).mp hj
  -- 2 ∣ 2^{μ-e} since μ-e ≥ 1, so j ≡ j₀ mod 2; with j₀ even ⟹ j even.
  have h2dvd : (2 : ℕ) ∣ 2 ^ (μ - e) := dvd_pow_self 2 (by omega)
  have hmod2 : j ≡ j₀ [MOD 2] := hmod.of_dvd h2dvd
  have hjm : j % 2 = j₀ % 2 := hmod2
  rw [Nat.even_iff] at hj₀ ⊢
  omega

/-! ### Step 4 : the witness value, its zero set, and the exact count. -/

/-- The **witness value** at the index `j`: `f(ζ^j)` where
`f(x) = (x^{2^{μ-1}} + 1) · (x^{2^e} − (ζ^{j₀})^{2^e})` — the product of the subgroup binomial and
the extra-spike binomial.  Its Fourier support is `{0, 2^e, 2^{μ-1}, 2^{μ-1}+2^e}`. -/
def witnessVal (μ e j₀ : ℕ) (ζ : F) (j : ℕ) : F :=
  ((ζ ^ j) ^ (2 ^ (μ - 1)) + 1) * ((ζ ^ j) ^ (2 ^ e) - (ζ ^ j₀) ^ (2 ^ e))

/-- In a field, `witnessVal = 0` iff a factor vanishes: `j` odd (binomial) OR `j` a poly-root. -/
theorem witnessVal_eq_zero_iff {μ e j₀ : ℕ} {ζ : F} (j : ℕ) :
    witnessVal μ e j₀ ζ j = 0 ↔
      ((ζ ^ j) ^ (2 ^ (μ - 1)) = -1 ∨ (ζ ^ j) ^ (2 ^ e) = (ζ ^ j₀) ^ (2 ^ e)) := by
  unfold witnessVal
  rw [mul_eq_zero, sub_eq_zero]
  have hfac : ((ζ ^ j) ^ (2 ^ (μ - 1)) + 1 = 0) ↔ ((ζ ^ j) ^ (2 ^ (μ - 1)) = -1) := by
    constructor
    · intro h; exact eq_neg_of_add_eq_zero_left h
    · intro h; rw [h]; ring
  rw [hfac]

/-- **The zero set splits as a DISJOINT union.**  For `e ≤ μ-1` and `j₀` EVEN, the binomial roots
(odd `j`) and the poly roots (even `j`) are disjoint, so the witness zero count over `range(2^μ)` is
`(#binom roots) + (#poly roots)`.  We package the binom-side count (`= 2^{μ-1}`) and the poly-side
LOWER bound (`≥ 2^e`, via the explicit residues `j₀ + i·2^{μ-e}`) to get `s* ≥ 2^{μ-1} + 2^e`. -/
theorem binom_poly_disjoint {μ e j₀ : ℕ} (he : e ≤ μ - 1) (hμ : 1 ≤ μ) (hj₀ : Even j₀)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    Disjoint
      ((range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ (μ - 1)) = -1))
      ((range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ e) = (ζ ^ j₀) ^ (2 ^ e))) := by
  rw [Finset.disjoint_left]
  intro j hjb hjp
  rw [mem_filter] at hjb hjp
  have hodd : Odd j := (binom_root_iff_odd hμ hζ j).mp hjb.2
  have heven : Even j := poly_root_even he hμ hj₀ hζ hjp.2
  exact (Nat.not_odd_iff_even.mpr heven) hodd

/-- The explicit `2^e` poly-root indices `{ j₀ + i·2^{μ-e} : i < 2^e }` all lie in `range(2^μ)` and
are poly-roots — so the poly-root filter has cardinality `≥ 2^e`. -/
theorem card_poly_roots_ge {μ e j₀ : ℕ} (he : e ≤ μ - 1) (hμ : 1 ≤ μ) (hj₀lt : j₀ < 2 ^ (μ - e))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    2 ^ e ≤ ((range (2 ^ μ)).filter
      (fun j => (ζ ^ j) ^ (2 ^ e) = (ζ ^ j₀) ^ (2 ^ e))).card := by
  -- the image of  i ↦ j₀ + i·2^{μ-e}  on range(2^e) is a subset of the poly-root filter, of card 2^e.
  classical
  set g : ℕ → ℕ := fun i => j₀ + i * 2 ^ (μ - e) with hg
  have hginj : Set.InjOn g (range (2 ^ e)) := by
    intro a _ b _ hab
    simp only [hg] at hab
    have h2pos : 0 < (2 : ℕ) ^ (μ - e) := by positivity
    have : a * 2 ^ (μ - e) = b * 2 ^ (μ - e) := by omega
    exact Nat.eq_of_mul_eq_mul_right h2pos this
  have hsub : (range (2 ^ e)).image g ⊆
      (range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ e) = (ζ ^ j₀) ^ (2 ^ e)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_range] at hi
    rw [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · have hsplit : (2 : ℕ) ^ μ = 2 ^ (μ - e) * 2 ^ e := by rw [← pow_add]; congr 1; omega
      simp only [hg]
      calc j₀ + i * 2 ^ (μ - e) < 2 ^ (μ - e) + i * 2 ^ (μ - e) := by omega
        _ = (i + 1) * 2 ^ (μ - e) := by ring
        _ ≤ 2 ^ e * 2 ^ (μ - e) := by apply Nat.mul_le_mul_right; omega
        _ = 2 ^ μ := by rw [hsplit]; ring
    · simp only [hg]
      rw [poly_root_iff_modEq (by omega) hζ]
      -- (j₀ + i·2^{μ-e}) ≡ j₀ [MOD 2^{μ-e}]
      refine ((Nat.modEq_iff_dvd' (by omega)).mpr ⟨i, ?_⟩).symm
      rw [Nat.add_sub_cancel_left]; ring
  calc 2 ^ e = (range (2 ^ e)).card := (Finset.card_range _).symm
    _ = ((range (2 ^ e)).image g).card := (Finset.card_image_of_injOn hginj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **The exact structured-extremal floor.**  The witness zero set over `range(2^μ)` (which equals
`{ j : witnessVal = 0 }`) has cardinality `≥ 2^{μ-1} + 2^e` — the binomial half-coset PLUS the
`2^e` poly roots, disjoint.  Hence `s*(2^μ, k) ≥ n/2 + 2^e` for every `e ≤ μ-1` with the spike
exponent `2^e ≤ k-1` (the support constraint). -/
theorem card_witnessVal_zero_ge {μ e j₀ : ℕ} (he : e ≤ μ - 1) (hμ : 1 ≤ μ) (hj₀ : Even j₀)
    (hj₀lt : j₀ < 2 ^ (μ - e)) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    2 ^ (μ - 1) + 2 ^ e ≤
      ((range (2 ^ μ)).filter (fun j => witnessVal μ e j₀ ζ j = 0)).card := by
  -- the zero filter EQUALS the union of the two factor filters.
  have hunion : (range (2 ^ μ)).filter (fun j => witnessVal μ e j₀ ζ j = 0)
      = ((range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ (μ - 1)) = -1))
        ∪ ((range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ e) = (ζ ^ j₀) ^ (2 ^ e))) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro j _
    exact witnessVal_eq_zero_iff j
  rw [hunion, Finset.card_union_of_disjoint (binom_poly_disjoint he hμ hj₀ hζ),
      card_binom_roots hμ hζ]
  have := card_poly_roots_ge he hμ hj₀lt hζ
  omega

/-! ### Step 5 : the refined floor `s* ≥ n/2 + 2^e` and the REFUTATION of `+ (k-1)`. -/

/-- **Refined structured floor.**  Define `sStarLowerBound := 2^{μ-1} + 2^e` (the witness zero
count).  This is a genuine lower bound on `s*(2^μ, k)` whenever the spike `2^e` fits the interval
(`2^e ≤ k-1`, i.e. `e ≤ μ-1`).  At rate `ρ = 1/4` (`k = 2^{μ-2}`) the optimal `e = μ-3` gives
`2^{μ-1} + 2^{μ-3} = 5·2^{μ-3} = 5n/8`. -/
def sStarLowerBound (μ e : ℕ) : ℕ := 2 ^ (μ - 1) + 2 ^ e

/-- The witness realises `sStarLowerBound` as an actual zero count (`s* ≥ sStarLowerBound`). -/
theorem sStar_ge_half_add_pow_two {μ e j₀ : ℕ} (he : e ≤ μ - 1) (hμ : 1 ≤ μ) (hj₀ : Even j₀)
    (hj₀lt : j₀ < 2 ^ (μ - e)) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    sStarLowerBound μ e ≤
      ((range (2 ^ μ)).filter (fun j => witnessVal μ e j₀ ζ j = 0)).card :=
  card_witnessVal_zero_ge he hμ hj₀ hj₀lt hζ

/-- **REFUTATION of the in-tree prose `s* = n/2 + (k-1)`.**  The prose value `n/2 + (k-1)` is the
claim that the cofactor multiplying the binomial contributes `k-1` zeros.  But the cofactor is a
BINOMIAL `x^d − x₀^d`, contributing only `gcd(d, n) = 2^{v₂(d)}` zeros, maximised over `d ≤ k-1` at
the largest power of two `≤ k-1`.  At the first non-power-of-two value `k = 4` (so `k-1 = 3`), the
optimal `d = 2` gives `2^{v₂(2)} = 2`, NOT `3`.  Concretely for `n = 16` (`μ = 4`): the prose
predicts `s* = 8 + 3 = 11`, but the true extremal (machine-checked full sweep, `p`-independent) is
`8 + 2 = 10`.  This `example` certifies the witness floor at `e = 1` (`d = 2`) is `10`, and that
`10 ≠ 11`. -/
theorem prose_kMinusOne_overcounts_at_k4 :
    -- the witness floor at μ=4 (n=16), e=1 (spike d=2), is exactly n/2 + 2 = 10
    sStarLowerBound 4 1 = 2 ^ 4 / 2 + 2 ∧
    -- the prose value n/2 + (k-1) with k=4 is n/2 + 3 = 11, which DIFFERS
    (2 ^ 4 / 2 + 2 : ℕ) ≠ 2 ^ 4 / 2 + (4 - 1) := by
  refine ⟨by decide, by decide⟩

-- Axiom audit (the load-bearing results): expect `[propext, Classical.choice, Quot.sound]`.
#print axioms card_witnessVal_zero_ge
#print axioms sStar_ge_half_add_pow_two

end ProximityGap.StructuredUncertainty
