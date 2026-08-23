/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTDoubleSlice
import ArkLib.Data.CodingTheory.ProximityGap.CoprimePacketMinpoly
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnSquarefreePQ

/-!
# Issue #232 — the THREE-prime squarefree ℤ-GRID law: the structure surviving the
O105 refutation

O105 formally refuted de Bruijn's packet conjecture at three primes: the indicator
of `S = {5,6,12,18,24,25}` vanishes at `ζ₃₀` but admits NO ℕ-combination of full
prime packets.  This file lands the structure that DOES survive — the relation
module over ℤ.  **The headline iff** (`int_grid_three_prime`): for distinct primes
`p, q, r`, primitive roots `ξ, η, θ` of orders `p, q, r` (char 0), and
`W : ℤ_p × ℤ_q × ℤ_r → ℤ`,

    `∑_{i,j,k} W i j k · ξ^i·η^j·θ^k = 0   ⟺   ∃ α β γ : ℕ → ℕ → ℤ,
        W i j k = α j k + β i k + γ i j`  (on the grid)

— the kernel is exactly the sum of the three packet-direction sublattices
(`K_p ⊗ A ⊗ A + A ⊗ K_q ⊗ A + A ⊗ A ⊗ K_r`, each `K` the all-ones line), with NO
integrality gap, and the witness for the forward direction is explicit (no choice):

    `α j k = W 0 j k`,  `γ i j = W i j 0 − W 0 j 0`,
    `β i k = W i 0 k − W 0 0 k − W i 0 0 + W 0 0 0`.

Mechanism — the two-prime grid argument ITERATED, one new engine:
* `minpoly_adjoin_coprime_prime` — `Φ_p` stays irreducible over `ℚ(ζ_m)` for ANY
  `m` coprime to `p`; the shared `CoprimePacketMinpoly` totient-tower pinch is the
  three-prime step.
* `coeffs_eq_of_vanishing` — the rank-1 relation module: `CRTDoubleSlice`'s
  weight-general slice engine at packet width `1`.
* the `i`-slices `∑_{j,k} W i j k·η^j·θ^k ∈ ℚ⟮η·θ⟯` are therefore ALL EQUAL
  (`int_slice_sums_eq`; `η, θ ∈ ℚ⟮η·θ⟯` by coprime-order CRT inside the field);
  slice differences then vanish at level `q·r` and the TWO-prime ℤ-grid law
  (`int_grid_two_prime`, proved here the same way — the ℤ analogue of O100's
  `debruijn_weighted_squarefree`, with the argmin shift replaced by the free ℤ
  shift) yields the modular equations; pure `omega` assembles the tables.
* converse: all three parts die against full geometric sums.

Corollaries (Stage-3): `int_total_three_prime` — the Schoenberg-form total identity
`Σ W = p·Σα + q·Σβ + r·Σγ`.  HONEST SCOPE: since `gcd(p·q, q·r, p·r) = 1`, the bare
membership `Σ W ∈ ℤp + ℤq + ℤr` is vacuous as a constraint — the content is the
identity with the actual table sums.  The ℕ-span theorem (Lam–Leung: `Σ W ∈
ℕp + ℕq + ℕr` for ℕ-weights) is STRICTLY finer and remains open here; the O105
witness below realizes the hard branch of its induction (its slice evaluations are
equal and NONZERO).

Teeth — the O105 witness gets constructive: `witnessW` (the indicator of `S` in CRT
grid coordinates, kernel-checked against `S` itself) decomposes over ℤ with the
explicit small tables `witnessα/β/γ` (`decide`), the `β` table is genuinely
NEGATIVE, NO ℕ-table decomposition exists (four cells + `omega` — the O105
phenomenon on the grid surface), and the converse direction fires the witness's
vanishing at `ℂ` from the tables alone.

Falsified first: `scripts/probes/probe_three_prime_grid.py` (exact arithmetic,
exit 0) — the COMPLETE lattice identity at `(p,q,r) = (2,3,5), (2,3,7), (2,3,11),
(3,5,7)`: all generators vanish, ℚ-ranks match (`pqr − (p−1)(q−1)(r−1)`), Smith
invariant factors all `1` (saturation: no integrality gap, settling the law for ALL
of `ℤ^{pqr}`, stronger than any finite weight box), the modular equations lie in
the span of the vanishing conditions, the explicit construction reconstructs 200
random kernel elements per triple, unit-bump and perturbation controls live, and
the witness tables match the ones below.
-/

namespace DeBruijnThreePrimeIntGrid

open Polynomial Finset IntermediateField

/-- **`Φ_p` is irreducible over ANY coprime cyclotomic extension** — the
`CoprimePacketMinpoly` theorem with the coprimality orientation used by this
three-prime grid file: for `ω` a primitive `m`-th root, `ξ` a primitive `p`-th
root, `p` prime, `p` coprime to `m` (char 0), the minimal polynomial of `ξ` over
`ℚ⟮ω⟯` is the full packet `1 + X + ⋯ + X^{p−1}`.  At `m = q·r` this is the
engine of the three-prime grid law. -/
theorem minpoly_adjoin_coprime_prime {L : Type*} [Field L] [CharZero L] {m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime p m)
    {ω ξ : L} (hω : IsPrimitiveRoot ω m) (hξ : IsPrimitiveRoot ξ p) :
    minpoly ℚ⟮ω⟯ ξ = ∑ t ∈ Finset.range p, (X : Polynomial ℚ⟮ω⟯) ^ t := by
  simpa using
    (CoprimePacketMinpoly.minpoly_adjoin_coprime_prime_eq_geom
      (L := L) hm hp hcop.symm hω hξ)

/-- **The rank-1 relation module**: if `minpoly K ξ` is the full packet
`1 + X + ⋯ + X^{p−1}`, every vanishing `K`-combination of `1, ξ, …, ξ^{p−1}` has
all coefficients equal — `CRTDoubleSlice.slice_of_packet_minpoly` at packet
width `1`. -/
lemma coeffs_eq_of_vanishing {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} {ξ : L}
    (hmin : minpoly K ξ = ∑ t ∈ Finset.range p, (X : K[X]) ^ t)
    {c : ℕ → K} (hsum : ∑ i ∈ Finset.range p, c i • ξ ^ i = 0)
    {i i' : ℕ} (hi : i < p) (hi' : i' < p) : c i = c i' := by
  have hmin1 : minpoly K ξ = ∑ t ∈ Finset.range p, (X : K[X]) ^ (t * 1) := by
    simpa using hmin
  have hsum1 : ∑ e ∈ Finset.range (p * 1), c e • ξ ^ e = 0 := by
    simpa using hsum
  have h := CRTDoubleSlice.slice_of_packet_minpoly hmin1 hsum1 hi hi'
    Nat.one_pos
  simpa using h

/-- The left factor of a product of roots of coprime orders lies in the simple
adjoin of the product: `η ∈ ℚ⟮η·θ⟯` (CRT inside the field). -/
lemma left_mem_adjoin_mul {L : Type*} [Field L] [CharZero L] {q r : ℕ}
    (hq : 1 < q) {η θ : L} (hηq : η ^ q = 1) (hθr : θ ^ r = 1)
    (hco : Nat.Coprime r q) : η ∈ ℚ⟮η * θ⟯ := by
  have hpow : (η * θ) ^ r = η ^ r := by
    rw [mul_pow, hθr, mul_one]
  have hr_mem : η ^ r ∈ ℚ⟮η * θ⟯ := by
    rw [← hpow]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ (η * θ)) r
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco hq
  have hηrs : η ^ (r * s) = η := by
    conv_lhs => rw [← Nat.div_add_mod (r * s) q]
    rw [pow_add, pow_mul, hηq, one_pow, one_mul, hs, pow_one]
  have hmem : (η ^ r) ^ s ∈ ℚ⟮η * θ⟯ := pow_mem hr_mem s
  rwa [← pow_mul, hηrs] at hmem

/-- The right factor of a product of roots of coprime orders lies in the simple
adjoin of the product: `θ ∈ ℚ⟮η·θ⟯`. -/
lemma right_mem_adjoin_mul {L : Type*} [Field L] [CharZero L] {q r : ℕ}
    (hr : 1 < r) {η θ : L} (hηq : η ^ q = 1) (hθr : θ ^ r = 1)
    (hco : Nat.Coprime q r) : θ ∈ ℚ⟮η * θ⟯ := by
  have h := left_mem_adjoin_mul hr hθr hηq hco
  rwa [mul_comm] at h

variable {L : Type*} [Field L] [CharZero L]

/-! ## The TWO-prime ℤ-grid law (the ℤ analogue of O100, also the recursion base) -/

/-- **Equal rows over ℤ**: a vanishing ℤ-weighted two-prime grid sum has all its
`η`-side row sums equal — the rank-1 relation module over `ℚ⟮η⟯`. -/
lemma int_row_sums_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℤ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (W i j : L) * ξ ^ i * η ^ j = 0)
    {i i' : ℕ} (hi : i < p) (hi' : i' < p) :
    ∑ j ∈ Finset.range q, (W i j : L) * η ^ j
      = ∑ j ∈ Finset.range q, (W i' j : L) * η ^ j := by
  classical
  set g : ℚ⟮η⟯ := IntermediateField.AdjoinSimple.gen ℚ η with hg
  have hcoe : algebraMap ℚ⟮η⟯ L g = η :=
    IntermediateField.AdjoinSimple.algebraMap_gen ℚ η
  set c : ℕ → ℚ⟮η⟯ := fun a => ∑ j ∈ Finset.range q, (W a j : ℚ⟮η⟯) * g ^ j with hc
  have hmap : ∀ a : ℕ, algebraMap ℚ⟮η⟯ L (c a)
      = ∑ j ∈ Finset.range q, (W a j : L) * η ^ j := by
    intro a
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_intCast, map_pow, hcoe]
  have hmin : minpoly ℚ⟮η⟯ ξ = ∑ t ∈ Finset.range p, (X : Polynomial ℚ⟮η⟯) ^ t :=
    minpoly_adjoin_coprime_prime hq.pos hp
      ((Nat.coprime_primes hp hq).mpr hpq) hη hξ
  have hrel : ∑ a ∈ Finset.range p, c a • ξ ^ a = 0 := by
    calc ∑ a ∈ Finset.range p, c a • ξ ^ a
        = ∑ a ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (W a j : L) * ξ ^ a * η ^ j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Algebra.smul_def, hmap, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := hsum
  have hceq := coeffs_eq_of_vanishing hmin hrel hi hi'
  have hfin := congrArg (algebraMap ℚ⟮η⟯ L) hceq
  rwa [hmap, hmap] at hfin

/-- **The ℤ modular equation** at two primes: a vanishing ℤ-weighted grid sum
satisfies `W i j + W 0 0 = W i 0 + W 0 j` — equal rows plus prime-level
ℚ-rigidity. -/
lemma int_modular_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℤ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (W i j : L) * ξ ^ i * η ^ j = 0) :
    ∀ i < p, ∀ j < q, W i j + W 0 0 = W i 0 + W 0 j := by
  intro i hi j hj
  have hrow := int_row_sums_eq hp hq hpq hξ hη W hsum hi hp.pos
  have hdiff : ∑ j' ∈ Finset.range q,
      algebraMap ℚ L ((W i j' : ℚ) - (W 0 j' : ℚ)) * η ^ j' = 0 := by
    have hterm : ∀ j' ∈ Finset.range q,
        algebraMap ℚ L ((W i j' : ℚ) - (W 0 j' : ℚ)) * η ^ j'
          = (W i j' : L) * η ^ j' - (W 0 j' : L) * η ^ j' := by
      intro j' _
      rw [map_sub, map_intCast, map_intCast, sub_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hrow, sub_self]
  obtain ⟨cst, hcst⟩ := DeBruijnSquarefreePQ.vanishing_combination_const hq hη
    (fun j' => (W i j' : ℚ) - (W 0 j' : ℚ)) hdiff
  have h1 := hcst j hj
  have h2 := hcst 0 hq.pos
  have h4 : (W i j : ℚ) + (W 0 0 : ℚ) = (W i 0 : ℚ) + (W 0 j : ℚ) := by
    simp only at h1 h2
    linarith
  exact_mod_cast h4

/-- **The TWO-prime ℤ-grid law**: a ℤ-weighted sum over the `p × q` root-of-unity
grid vanishes iff the weight matrix splits as a row function plus a column function
over ℤ.  The ℤ analogue of O100's `debruijn_weighted_squarefree` — over ℤ the
argmin shift is unnecessary (no positivity), so the witness is the plain base
shift. -/
theorem int_grid_two_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℤ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (W i j : L) * ξ ^ i * η ^ j = 0) ↔
      ∃ α β : ℕ → ℤ, ∀ i < p, ∀ j < q, W i j = α i + β j := by
  constructor
  · intro hsum
    have hmod := int_modular_eq hp hq hpq hξ hη W hsum
    refine ⟨fun i => W i 0 - W 0 0, fun j => W 0 j, fun i hi j hj => ?_⟩
    have h1 := hmod i hi j hj
    show W i j = W i 0 - W 0 0 + W 0 j
    omega
  · rintro ⟨α, β, hαβ⟩
    have hsplit : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (W i j : L) * ξ ^ i * η ^ j
        = (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (α i : L) * ξ ^ i * η ^ j)
          + ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
              (β j : L) * ξ ^ i * η ^ j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hαβ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
      push_cast
      ring
    have hpart1 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (α i : L) * ξ ^ i * η ^ j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, hη.geom_sum_eq_zero hq.one_lt, mul_zero]
    have hpart2 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (β j : L) * ξ ^ i * η ^ j = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hterm : ∀ i ∈ Finset.range p,
          (β j : L) * ξ ^ i * η ^ j = (β j : L) * η ^ j * ξ ^ i := by
        intro i _
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        hξ.geom_sum_eq_zero hp.one_lt, mul_zero]
    rw [hsplit, hpart1, hpart2, add_zero]

/-! ## The THREE-prime ℤ-grid law -/

/-- **Equal slices at three primes**: a vanishing ℤ-weighted triple grid sum has
all its `i`-slices (as elements of `ℚ⟮η·θ⟯`, mapped to `L`) equal — the rank-1
relation module of `1, ξ, …, ξ^{p−1}` over the coprime BI-cyclotomic extension
`ℚ(ζ_{qr})`. -/
lemma int_slice_sums_eq {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {ξ η θ : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (hθ : IsPrimitiveRoot θ r)
    (W : ℕ → ℕ → ℕ → ℤ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
      (W i j k : L) * ξ ^ i * η ^ j * θ ^ k = 0)
    {i i' : ℕ} (hi : i < p) (hi' : i' < p) :
    ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r, (W i j k : L) * η ^ j * θ ^ k
      = ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
          (W i' j k : L) * η ^ j * θ ^ k := by
  classical
  have hco_qr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  have horderη : orderOf η = q := hη.eq_orderOf.symm
  have horderθ : orderOf θ = r := hθ.eq_orderOf.symm
  have horder : orderOf (η * θ) = q * r := by
    rw [(Commute.all η θ).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [horderη, horderθ]; exact hco_qr), horderη, horderθ]
  have hω : IsPrimitiveRoot (η * θ) (q * r) :=
    horder ▸ IsPrimitiveRoot.orderOf (η * θ)
  have hηmem : η ∈ ℚ⟮η * θ⟯ :=
    left_mem_adjoin_mul hq.one_lt hη.pow_eq_one hθ.pow_eq_one hco_qr.symm
  have hθmem : θ ∈ ℚ⟮η * θ⟯ :=
    right_mem_adjoin_mul hr.one_lt hη.pow_eq_one hθ.pow_eq_one hco_qr
  set ηK : ℚ⟮η * θ⟯ := ⟨η, hηmem⟩ with hηK
  set θK : ℚ⟮η * θ⟯ := ⟨θ, hθmem⟩ with hθK
  have hcoeη : algebraMap ℚ⟮η * θ⟯ L ηK = η := rfl
  have hcoeθ : algebraMap ℚ⟮η * θ⟯ L θK = θ := rfl
  set c : ℕ → ℚ⟮η * θ⟯ := fun a => ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
    (W a j k : ℚ⟮η * θ⟯) * ηK ^ j * θK ^ k with hc
  have hmap : ∀ a : ℕ, algebraMap ℚ⟮η * θ⟯ L (c a)
      = ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
          (W a j k : L) * η ^ j * θ ^ k := by
    intro a
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_intCast, map_pow, map_pow, hcoeη, hcoeθ]
  have hmin : minpoly ℚ⟮η * θ⟯ ξ
      = ∑ t ∈ Finset.range p, (X : Polynomial ℚ⟮η * θ⟯) ^ t :=
    minpoly_adjoin_coprime_prime (Nat.mul_pos hq.pos hr.pos) hp
      (Nat.Coprime.mul_right ((Nat.coprime_primes hp hq).mpr hpq)
        ((Nat.coprime_primes hp hr).mpr hpr)) hω hξ
  have hrel : ∑ a ∈ Finset.range p, c a • ξ ^ a = 0 := by
    calc ∑ a ∈ Finset.range p, c a • ξ ^ a
        = ∑ a ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (W a j k : L) * ξ ^ a * η ^ j * θ ^ k := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Algebra.smul_def, hmap, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := hsum
  have hceq := coeffs_eq_of_vanishing hmin hrel hi hi'
  have hfin := congrArg (algebraMap ℚ⟮η * θ⟯ L) hceq
  rwa [hmap, hmap] at hfin

/-- **THE THREE-PRIME SQUAREFREE ℤ-GRID LAW** — the structure surviving the O105
refutation: a ℤ-weighted sum over the `p × q × r` root-of-unity grid vanishes
**iff** the weight tensor is a sum of three slice functions
`W i j k = α j k + β i k + γ i j` over ℤ.  The forward witness is explicit (no
choice): `α j k = W 0 j k`, `γ i j = W i j 0 − W 0 j 0`,
`β i k = W i 0 k − W 0 0 k − W i 0 0 + W 0 0 0`.  Over ℕ the analogous statement
is FALSE (O105 / `ThreePrimePacketRefutation`); the ℤ-relaxation is exact. -/
theorem int_grid_three_prime {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {ξ η θ : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (hθ : IsPrimitiveRoot θ r) (W : ℕ → ℕ → ℕ → ℤ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
        (W i j k : L) * ξ ^ i * η ^ j * θ ^ k = 0) ↔
      ∃ α β γ : ℕ → ℕ → ℤ,
        ∀ i < p, ∀ j < q, ∀ k < r, W i j k = α j k + β i k + γ i j := by
  constructor
  · intro hsum
    refine ⟨fun j k => W 0 j k,
            fun i k => W i 0 k - W 0 0 k - W i 0 0 + W 0 0 0,
            fun i j => W i j 0 - W 0 j 0,
            fun i hi j hj k hk => ?_⟩
    have hslice := int_slice_sums_eq hp hq hr hpq hpr hqr hξ hη hθ W hsum hi hp.pos
    have hdiff : ∑ j' ∈ Finset.range q, ∑ k' ∈ Finset.range r,
        ((W i j' k' - W 0 j' k' : ℤ) : L) * η ^ j' * θ ^ k' = 0 := by
      have hsub : ∑ j' ∈ Finset.range q, ∑ k' ∈ Finset.range r,
          ((W i j' k' - W 0 j' k' : ℤ) : L) * η ^ j' * θ ^ k'
          = (∑ j' ∈ Finset.range q, ∑ k' ∈ Finset.range r,
              (W i j' k' : L) * η ^ j' * θ ^ k')
            - ∑ j' ∈ Finset.range q, ∑ k' ∈ Finset.range r,
                (W 0 j' k' : L) * η ^ j' * θ ^ k' := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k' _ => ?_
        push_cast
        ring
      rw [hsub, hslice, sub_self]
    have hmod := int_modular_eq hq hr hqr hη hθ
      (fun j' k' => W i j' k' - W 0 j' k') hdiff j hj k hk
    show W i j k = W 0 j k + (W i 0 k - W 0 0 k - W i 0 0 + W 0 0 0)
      + (W i j 0 - W 0 j 0)
    simp only at hmod
    omega
  · rintro ⟨α, β, γ, hαβγ⟩
    have hsplit : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (W i j k : L) * ξ ^ i * η ^ j * θ ^ k
        = (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (α j k : L) * ξ ^ i * η ^ j * θ ^ k)
          + (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              (β i k : L) * ξ ^ i * η ^ j * θ ^ k)
          + ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              (γ i j : L) * ξ ^ i * η ^ j * θ ^ k := by
      calc ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (W i j k : L) * ξ ^ i * η ^ j * θ ^ k
          = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              ((α j k : L) * ξ ^ i * η ^ j * θ ^ k
                + (β i k : L) * ξ ^ i * η ^ j * θ ^ k
                + (γ i j : L) * ξ ^ i * η ^ j * θ ^ k) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            refine Finset.sum_congr rfl fun j hj => ?_
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [hαβγ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
              k (Finset.mem_range.mp hk)]
            push_cast
            ring
        _ = _ := by
            simp only [Finset.sum_add_distrib]
    have hpartα : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (α j k : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
      have hterm : ∀ i ∈ Finset.range p,
          ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (α j k : L) * ξ ^ i * η ^ j * θ ^ k
          = ξ ^ i * ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              (α j k : L) * η ^ j * θ ^ k := by
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
        hξ.geom_sum_eq_zero hp.one_lt, zero_mul]
    have hpartβ : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (β i k : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hterm : ∀ j ∈ Finset.range q,
          (β i k : L) * ξ ^ i * η ^ j * θ ^ k
            = (β i k : L) * ξ ^ i * θ ^ k * η ^ j := by
        intro j _
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        hη.geom_sum_eq_zero hq.one_lt, mul_zero]
    have hpartγ : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (γ i j : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum, hθ.geom_sum_eq_zero hr.one_lt, mul_zero]
    rw [hsplit, hpartα, hpartβ, hpartγ]
    norm_num

/-! ## Stage-3 corollaries: the total identity and the constructive O105 witness -/

/-- **The Schoenberg-form total identity at three squarefree primes**: a vanishing
ℤ-weighted triple grid sum has total weight `p·Σα + q·Σβ + r·Σγ` for the
decomposition tables.  Honest scope: since `gcd(p, q, r) = 1` this is vacuous as a
bare membership in `ℤp + ℤq + ℤr`; the content is the identity itself.  The
ℕ-span refinement (Lam–Leung) is strictly finer and not derivable from the ℤ-grid
alone — see the O105 witness below, which realizes the obstruction. -/
theorem int_total_three_prime {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {ξ η θ : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (hθ : IsPrimitiveRoot θ r) (W : ℕ → ℕ → ℕ → ℤ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
      (W i j k : L) * ξ ^ i * η ^ j * θ ^ k = 0) :
    ∃ A B C : ℤ, ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, W i j k = (p : ℤ) * A + (q : ℤ) * B + (r : ℤ) * C := by
  obtain ⟨α, β, γ, h⟩ :=
    (int_grid_three_prime hp hq hr hpq hpr hqr hξ hη hθ W).mp hsum
  refine ⟨∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r, α j k,
          ∑ i ∈ Finset.range p, ∑ k ∈ Finset.range r, β i k,
          ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, γ i j, ?_⟩
  have hW : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
      W i j k
      = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
          (α j k + β i k + γ i j) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun k hk => ?_
    exact h i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      k (Finset.mem_range.mp hk)
  have hA : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
      α j k = (p : ℤ) * ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r, α j k := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hB : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
      β i k = (q : ℤ) * ∑ i ∈ Finset.range p, ∑ k ∈ Finset.range r, β i k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hC : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
      γ i j = (r : ℤ) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, γ i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hW]
  simp only [Finset.sum_add_distrib]
  rw [hA, hB, hC]

/-- The O105 witness `S = {5, 6, 12, 18, 24, 25}` at `n = 30` in CRT grid
coordinates `(i, j, k) = (e % 2, e % 3, e % 5)`. -/
def witnessW : ℕ → ℕ → ℕ → ℤ := fun i j k =>
  if (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 0 ∧ j = 0 ∧ k = 1) ∨ (i = 0 ∧ j = 0 ∧ k = 2)
    ∨ (i = 0 ∧ j = 0 ∧ k = 3) ∨ (i = 0 ∧ j = 0 ∧ k = 4) ∨ (i = 1 ∧ j = 1 ∧ k = 0)
  then 1 else 0

/-- The explicit `α` table (the `i = 0` base slice). -/
def witnessα : ℕ → ℕ → ℤ := fun j k => if j = 0 ∧ 1 ≤ k ∧ k ≤ 4 then 1 else 0

/-- The explicit `β` table — genuinely NEGATIVE: the O105 phenomenon (a vanishing
0/1 weight whose three-prime decomposition cannot avoid signs). -/
def witnessβ : ℕ → ℕ → ℤ := fun i k => if i = 1 ∧ 1 ≤ k ∧ k ≤ 4 then -1 else 0

/-- The explicit `γ` table. -/
def witnessγ : ℕ → ℕ → ℤ := fun i j => if i = 1 ∧ (j = 1 ∨ j = 2) then 1 else 0

/-- `witnessW` IS the O105 witness: the CRT transport of the indicator of
`S = {5, 6, 12, 18, 24, 25} ⊆ [0, 30)`, kernel-checked cell by cell. -/
theorem witnessW_eq_indicator : ∀ e < 30,
    witnessW (e % 2) (e % 3) (e % 5)
      = (if e ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ) then 1 else 0) := by
  decide

/-- **The constructive O105 decomposition**: the witness splits over ℤ with the
explicit small tables — `decide`-checked on the full `2 × 3 × 5` grid. -/
theorem witness_decomposes : ∀ i < 2, ∀ j < 3, ∀ k < 5,
    witnessW i j k = witnessα j k + witnessβ i k + witnessγ i j := by
  decide

/-- The β table really goes negative. -/
theorem witnessβ_neg : witnessβ 1 1 = -1 := by decide

/-- **No ℕ-table decomposition exists** (the grid-surface form of O105): the same
witness admits NO decomposition with nonnegative tables — four cells and `omega`.
Together with `witness_decomposes` this is the exact ℤ/ℕ separation at three
primes. -/
theorem witness_no_nat_decomposition :
    ¬ ∃ A B C : ℕ → ℕ → ℕ, ∀ i < 2, ∀ j < 3, ∀ k < 5,
      witnessW i j k = (A j k : ℤ) + (B i k : ℤ) + (C i j : ℤ) := by
  rintro ⟨A, B, C, h⟩
  have h1 := h 1 (by norm_num) 0 (by norm_num) 1 (by norm_num)
  have h2 := h 0 (by norm_num) 0 (by norm_num) 1 (by norm_num)
  have h3 := h 0 (by norm_num) 1 (by norm_num) 1 (by norm_num)
  have h4 := h 0 (by norm_num) 0 (by norm_num) 0 (by norm_num)
  have e1 : witnessW 1 0 1 = 0 := by decide
  have e2 : witnessW 0 0 1 = 1 := by decide
  have e3 : witnessW 0 1 1 = 0 := by decide
  have e4 : witnessW 0 0 0 = 0 := by decide
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  omega

/-! ## Teeth (fired at `ℂ`: the witness's vanishing produced from the tables) -/

private lemma exp_two_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (2 : ℕ))) 2 :=
  Complex.isPrimitiveRoot_exp 2 (by norm_num)

private lemma exp_three_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))) 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

private lemma exp_five_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (5 : ℕ))) 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The converse FIRED at `ℂ`: the O105 witness's vanishing at `n = 30` (grid
coordinates) is PRODUCED from the explicit ℤ tables — the signed decomposition
proves the vanishing that the ℕ-packet machinery provably cannot reach. -/
example : ∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 5,
    (witnessW i j k : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I / (2 : ℕ)) ^ i
      * Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ^ j
      * Complex.exp (2 * Real.pi * Complex.I / (5 : ℕ)) ^ k = 0 := by
  refine (int_grid_three_prime Nat.prime_two Nat.prime_three
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exp_two_primitive exp_three_primitive exp_five_primitive witnessW).mpr ?_
  exact ⟨witnessα, witnessβ, witnessγ, witness_decomposes⟩

/-- The witness's total identity `6 = 2·4 + 3·(−4) + 5·2` — the Stage-3 identity
instantiated with the explicit tables (the probe's exact values). -/
example : ∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 5,
    witnessW i j k = 2 * 4 + 3 * (-4) + 5 * 2 := by decide

end DeBruijnThreePrimeIntGrid

#print axioms DeBruijnThreePrimeIntGrid.minpoly_adjoin_coprime_prime
#print axioms DeBruijnThreePrimeIntGrid.coeffs_eq_of_vanishing
#print axioms DeBruijnThreePrimeIntGrid.int_grid_two_prime
#print axioms DeBruijnThreePrimeIntGrid.int_slice_sums_eq
#print axioms DeBruijnThreePrimeIntGrid.int_grid_three_prime
#print axioms DeBruijnThreePrimeIntGrid.int_total_three_prime
#print axioms DeBruijnThreePrimeIntGrid.witness_decomposes
#print axioms DeBruijnThreePrimeIntGrid.witness_no_nat_decomposition
