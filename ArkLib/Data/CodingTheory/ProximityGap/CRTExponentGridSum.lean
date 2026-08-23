/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTDoubleSlice
import Mathlib.Algebra.BigOperators.Fin

/-!
# Issue #232 — the CRT exponent bijection: subset sums of `μ_n` as coprime-grid double sums

De Bruijn capstone step (2), as named in DISPROOF_LOG O73: convert a (vanishing) subset
sum `Σ_{z ∈ S} z` over `S ⊆ μ_n` (`n = N·M`, `gcd(N, M) = 1`; think `N = p^a`,
`M = q^b`) into the coprime-grid double sum `Σ_{(j,c) ∈ I} ξ^j · η^c` that
`CRTDoubleSlice.crt_fiber_slice` consumes, where `ξ = ζ^M` and `η = ζ^N` for a chosen
`n`-th root `ζ`.

This file COMPLETES (and supersedes) the rate-limit-orphaned draft
`CRTExponentBijection.lean`, whose six main theorems elaborate but whose non-vacuity
example fails (its positional `by norm_num` arguments elaborate against unassigned
metavariables for `N`, `q`, `Q'`). Here every witness elaborates: the composition
witness pins `N`, `q`, `Q'`, `i`, `i'`, `s` by name, and a genuine two-prime witness
(`N = 2`, `M = 3`, `ζ = 3 ∈ ZMod 7`, a primitive 6th root) exercises the bijection
identity away from the degenerate `N = 1` corner. The orphaned draft should be dropped
in favour of this file.

**Normalization (falsified-first, `scripts/probes/probe_crt_exponent_bijection.py`,
82 405 checks / 0 violations, exhaustive over all `2^n` subsets at `n = 12, 15`,
re-run cold this session, exit 0):** the formalized direction is the FORWARD grid map

    g(j, c) = j·M + c·N  (mod n),

which needs **no Bezout coefficients** — `ζ^{g(j,c)} = ξ^j · η^c` is trivial exponent
arithmetic, and bijectivity is CRT. The Bezout data (`u = M⁻¹ mod N`, `v = N⁻¹ mod M`,
`ζ^e = ξ^{u·e mod N} · η^{v·e mod M}`) only enters the *inverse* map and is never needed
here: surjectivity of `g` is proved by the injectivity + cardinality argument, which is
where the coprimality hypothesis bites (the probe's non-coprime control `N = 4, M = 6`
fails bijectivity, image `12 < 24`).

Contents:

* `pow_mod_eq` — `ζ^(m % n) = ζ^m` for `ζ^n = 1` (exponent-reduction helper).
* `gridMap_inj` — injectivity of `g` on the grid `[0,N) × [0,M)`, from coprimality
  (mod-`N` and mod-`M` reduction + unit cancellation).
* `gridMap_surj` — surjectivity onto `ZMod (N·M)` (injectivity + cardinality).
* `pow_gridMap` — the intertwining `ζ^{g(j,c).val} = (ζ^M)^j · (ζ^N)^c`.
* `subset_sum_eq_grid_double_sum` — **the deliverable**: for any `S : Finset (ZMod n)`,
  `Σ_{e ∈ S} ζ^{e.val} = Σ_{(j,c) ∈ gridSet S} (ζ^M)^j · (ζ^N)^c`, a `Finset.sum` over
  the 0/1-indicator grid set (no weights), over any `Monoid + AddCommMonoid` — in
  particular any commutative ring containing an `n`-th root of unity.
* `fiber_slice_of_vanishing_subset_sum` — the composition with
  `CRTDoubleSlice.crt_fiber_slice`: a vanishing subset sum of `μ_n` exponents has
  μ_q-shift invariant fiber sums `A(c) = Σ_{(j,c) ∈ gridSet S} ξ₀^j ∈ K`, under the
  packet-minpoly hypothesis at the second prime. This discharges step (2) of the O73
  "what remains" list; steps (1) (minpoly over `ℚ(ζ_{p^a})`) and (3)
  (positivity/disjointness — the genuinely de Bruijn part) stay open and are NOT
  claimed here.

Non-vacuity: (a) the bijection identity is exercised at a genuine two-prime point
`N = 2, M = 3` over `ZMod 7` with the nonempty exponent set `{0, 1, 3}` (both sides
evaluate to `3 ≠ 0`, kernel-checked); (b) the composition corollary is exercised at
`N = 1`, `q = 2`, `Q' = 1`, `ζ = −1`, `S = univ` (the full `μ₂`, a *nonempty*
vanishing sum `1 + (−1) = 0`), with every hypothesis discharged.
-/

namespace CRTExponentGridSum

open Polynomial Finset

/-- Exponent reduction: if `ζ ^ n = 1` then `ζ ^ (m % n) = ζ ^ m`. -/
lemma pow_mod_eq {L : Type*} [Monoid L] {ζ : L} {n : ℕ} (hζ : ζ ^ n = 1) (m : ℕ) :
    ζ ^ (m % n) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [pow_add, pow_mul, hζ, one_pow, mul_one]

/-- The CRT grid map `(j, c) ↦ j·M + c·N` into `ZMod (N·M)`. On the grid
`[0,N) × [0,M)` this is the inverse-direction Chinese remainder bijection; no Bezout
coefficients appear in this direction. -/
def gridMap (N M : ℕ) (x : ℕ × ℕ) : ZMod (N * M) :=
  ((x.1 * M + x.2 * N : ℕ) : ZMod (N * M))

/-- **Injectivity of the grid map** on `[0,N) × [0,M)`, from `gcd(N,M) = 1`:
reduce mod `N` (killing the `c·N` terms, cancelling the unit `M`) and mod `M`. -/
lemma gridMap_inj {N M : ℕ} (hcop : Nat.Coprime N M)
    {j c j' c' : ℕ} (hj : j < N) (hc : c < M) (hj' : j' < N) (hc' : c' < M)
    (h : gridMap N M (j, c) = gridMap N M (j', c')) : j = j' ∧ c = c' := by
  rw [gridMap, gridMap, ZMod.natCast_eq_natCast_iff] at h
  constructor
  · have hN : j * M + c * N ≡ j' * M + c' * N [MOD N] := h.of_dvd ⟨M, rfl⟩
    have h1 : j * M ≡ j' * M [MOD N] := by
      have := hN
      unfold Nat.ModEq at this ⊢
      simpa only [Nat.add_mul_mod_self_right] using this
    have h2 : j ≡ j' [MOD N] := Nat.ModEq.cancel_right_of_coprime hcop h1
    have h3 : j % N = j' % N := h2
    rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h3
  · have hM : j * M + c * N ≡ j' * M + c' * N [MOD M] := h.of_dvd ⟨N, mul_comm N M⟩
    have h1 : c * N ≡ c' * N [MOD M] := by
      have := hM
      rw [Nat.add_comm (j * M) (c * N), Nat.add_comm (j' * M) (c' * N)] at this
      unfold Nat.ModEq at this ⊢
      simpa only [Nat.add_mul_mod_self_right] using this
    have h2 : c ≡ c' [MOD M] := Nat.ModEq.cancel_right_of_coprime hcop.symm h1
    have h3 : c % M = c' % M := h2
    rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at h3

/-- **Surjectivity of the grid map** onto `ZMod (N·M)`: injectivity + cardinality
(`N·M` grid points, `N·M` residues). This is where coprimality is load-bearing —
the probe's non-coprime control (`N = 4, M = 6`) violates it. -/
lemma gridMap_surj {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hcop : Nat.Coprime N M)
    (e : ZMod (N * M)) :
    ∃ x ∈ Finset.range N ×ˢ Finset.range M, gridMap N M x = e := by
  haveI : NeZero (N * M) := ⟨(Nat.mul_pos hN hM).ne'⟩
  have hinj : Set.InjOn (gridMap N M) ↑(Finset.range N ×ˢ Finset.range M) := by
    rintro ⟨j, c⟩ hx ⟨j', c'⟩ hx' h
    rw [Finset.mem_coe, Finset.mem_product] at hx hx'
    simp only [Finset.mem_range] at hx hx'
    obtain ⟨h1, h2⟩ := gridMap_inj hcop hx.1 hx.2 hx'.1 hx'.2 h
    rw [h1, h2]
  have hcard : ((Finset.range N ×ˢ Finset.range M).image (gridMap N M)).card
      = Fintype.card (ZMod (N * M)) := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
      Finset.card_range, ZMod.card]
  have huniv := Finset.eq_univ_of_card _ hcard
  have he : e ∈ (Finset.range N ×ˢ Finset.range M).image (gridMap N M) := by
    rw [huniv]; exact Finset.mem_univ e
  obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp he
  exact ⟨x, hx, hxe⟩

/-- **The intertwining identity**: for any `ζ` with `ζ^{N·M} = 1`,
`ζ^{g(j,c).val} = (ζ^M)^j · (ζ^N)^c` — i.e. the grid map converts powers of `ζ`
into products of powers of `ξ = ζ^M` and `η = ζ^N`. -/
lemma pow_gridMap {L : Type*} [Monoid L] {N M : ℕ} {ζ : L}
    (hζ : ζ ^ (N * M) = 1) (x : ℕ × ℕ) :
    ζ ^ (gridMap N M x).val = (ζ ^ M) ^ x.1 * (ζ ^ N) ^ x.2 := by
  rw [gridMap, ZMod.val_natCast, pow_mod_eq hζ, pow_add]
  congr 1
  · rw [← pow_mul, mul_comm]
  · rw [← pow_mul, mul_comm]

/-- The grid index set of `S`: the CRT preimage of `S` inside `[0,N) × [0,M)`.
Membership is the 0/1 indicator — sums over `gridSet` are unweighted. -/
def gridSet (N M : ℕ) (S : Finset (ZMod (N * M))) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range M).filter (fun x => gridMap N M x ∈ S)

lemma gridSet_subset (N M : ℕ) (S : Finset (ZMod (N * M))) :
    gridSet N M S ⊆ Finset.range N ×ˢ Finset.range M :=
  Finset.filter_subset _ _

/-- **The CRT exponent bijection, summed (de Bruijn step 2)**: any subset sum of
`n`-th roots of unity (`n = N·M`, `gcd(N,M) = 1`, exponents `S : Finset (ZMod n)`)
equals the coprime-grid double sum over its CRT index set, with `ξ = ζ^M`,
`η = ζ^N` and 0/1 indicator weights (a bare `Finset.sum` over `gridSet`):

    Σ_{e ∈ S} ζ^e  =  Σ_{(j,c) ∈ gridSet S} ξ^j · η^c.

Stated over any `Monoid + AddCommMonoid` (in particular any commutative ring
containing an `n`-th root of unity; primitivity is NOT needed for this identity). -/
theorem subset_sum_eq_grid_double_sum {L : Type*} [Monoid L] [AddCommMonoid L]
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hcop : Nat.Coprime N M)
    {ζ : L} (hζ : ζ ^ (N * M) = 1) (S : Finset (ZMod (N * M))) :
    ∑ e ∈ S, ζ ^ e.val
      = ∑ x ∈ gridSet N M S, (ζ ^ M) ^ x.1 * (ζ ^ N) ^ x.2 := by
  refine (Finset.sum_bij (fun x _ => gridMap N M x) ?_ ?_ ?_ ?_).symm
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · rintro ⟨j, c⟩ hx₁ ⟨j', c'⟩ hx₂ h
    have h1 := (Finset.mem_filter.mp hx₁).1
    have h2 := (Finset.mem_filter.mp hx₂).1
    rw [Finset.mem_product] at h1 h2
    simp only [Finset.mem_range] at h1 h2
    obtain ⟨hj, hc⟩ := gridMap_inj hcop h1.1 h1.2 h2.1 h2.2 h
    rw [hj, hc]
  · intro e he
    obtain ⟨x, hx, hxe⟩ := gridMap_surj hN hM hcop e
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxe ▸ he⟩, hxe⟩
  · intro x hx
    exact (pow_gridMap hζ x).symm

/-- **Composition with the CRT double-slice engine** (O73 `crt_fiber_slice` fed by the
exponent bijection): a *vanishing subset sum of `μ_n` exponents* (`n = N·(q·Q')`,
`gcd = 1`) has μ_q-shift invariant `K`-valued fiber sums over its CRT grid set,
provided `ξ₀ ∈ K` maps to `ζ^{q·Q'}` and `η = ζ^N` has the geometric-packet minimal
polynomial over `K`. This is de Bruijn step (2) composed with the step-(0) engine;
steps (1) (packet minpoly over `ℚ(ζ_{p^a})`) and (3) (disjoint-packet positivity)
remain open. -/
theorem fiber_slice_of_vanishing_subset_sum {K L : Type*} [Field K] [Field L]
    [Algebra K L] {N q Q' : ℕ} (hN : 0 < N) (hq : 0 < q) (hQ' : 0 < Q')
    (hcop : Nat.Coprime N (q * Q'))
    {ζ : L} (hζ : ζ ^ (N * (q * Q')) = 1)
    {ξ₀ : K} (hξ : algebraMap K L ξ₀ = ζ ^ (q * Q'))
    (hmin : minpoly K (ζ ^ N) = ∑ t ∈ Finset.range q, (X : K[X]) ^ (t * Q'))
    (S : Finset (ZMod (N * (q * Q'))))
    (hsum : ∑ e ∈ S, ζ ^ e.val = 0)
    {i i' s : ℕ} (hi : i < q) (hi' : i' < q) (hs : s < Q') :
    (∑ j ∈ Finset.range N, if (j, i * Q' + s) ∈ gridSet N (q * Q') S then ξ₀ ^ j else 0)
      = ∑ j ∈ Finset.range N,
          if (j, i' * Q' + s) ∈ gridSet N (q * Q') S then ξ₀ ^ j else 0 := by
  refine CRTDoubleSlice.crt_fiber_slice hmin ξ₀ (gridSet N (q * Q') S)
    (gridSet_subset N (q * Q') S) ?_ hi hi' hs
  calc ∑ x ∈ gridSet N (q * Q') S, (algebraMap K L ξ₀) ^ x.1 * (ζ ^ N) ^ x.2
      = ∑ x ∈ gridSet N (q * Q') S, (ζ ^ (q * Q')) ^ x.1 * (ζ ^ N) ^ x.2 := by
        rw [hξ]
    _ = ∑ e ∈ S, ζ ^ e.val :=
        (subset_sum_eq_grid_double_sum hN (Nat.mul_pos hq hQ') hcop hζ S).symm
    _ = 0 := hsum

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity of the bijection identity at a **genuine two-prime point**:
`N = 2`, `M = 3`, `ζ = 3 ∈ ZMod 7` (a primitive 6th root of unity, `3^6 = 1`),
`S = {0, 1, 3}` nonempty. Both sides are forced equal by the theorem with every
hypothesis discharged; this is away from the degenerate `N = 1` corner. -/
example :
    ∑ e ∈ ({0, 1, 3} : Finset (ZMod (2 * 3))), (3 : ZMod 7) ^ e.val
      = ∑ x ∈ gridSet 2 3 {0, 1, 3}, ((3 : ZMod 7) ^ 3) ^ x.1 * ((3 : ZMod 7) ^ 2) ^ x.2 :=
  subset_sum_eq_grid_double_sum (N := 2) (M := 3) (ζ := (3 : ZMod 7))
    (by norm_num) (by norm_num) (by decide) (by decide) _

/-- The two-prime witness is NOT trivial: the subset sum evaluates to `3 ≠ 0` in
`ZMod 7` (`3^0 + 3^1 + 3^3 = 31 ≡ 3`), kernel-checked — so the bijection identity
above equates two genuinely nonzero double sums. -/
example : ∑ e ∈ ({0, 1, 3} : Finset (ZMod (2 * 3))), (3 : ZMod 7) ^ e.val = 3 := by
  decide

/-- Non-vacuity of the composition corollary, **nonempty vanishing sum**: `N = 1`,
`q = 2`, `Q' = 1`, `ζ = −1 ∈ ℚ`, `S = univ` (all of `μ₂` in exponent form): the subset
sum `(−1)^0 + (−1)^1 = 0` genuinely vanishes, every hypothesis is discharged, and the
fiber-sum invariance follows from the theorem. (The orphaned draft's version of this
witness fails to elaborate; pinning `N`, `q`, `Q'`, `i`, `i'`, `s` by name fixes it.) -/
example :
    (∑ j ∈ Finset.range 1, if (j, 0 * 1 + 0) ∈
        gridSet 1 (2 * 1) (Finset.univ : Finset (ZMod (1 * (2 * 1))))
      then (1 : ℚ) ^ j else 0)
      = ∑ j ∈ Finset.range 1, if (j, 1 * 1 + 0) ∈
          gridSet 1 (2 * 1) (Finset.univ : Finset (ZMod (1 * (2 * 1))))
        then (1 : ℚ) ^ j else 0 := by
  have hmin : minpoly ℚ ((-1 : ℚ) ^ (1 : ℕ))
      = ∑ t ∈ Finset.range 2, (X : ℚ[X]) ^ (t * 1) := by
    rw [pow_one, minpoly.eq_X_sub_C', Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.mul_one, pow_zero, pow_one, map_neg, map_one]
    ring
  have hsum : ∑ e ∈ (Finset.univ : Finset (ZMod (1 * (2 * 1)))), (-1 : ℚ) ^ e.val = 0 := by
    show ∑ e : Fin 2, (-1 : ℚ) ^ (e : ℕ) = 0
    rw [Fin.sum_univ_two]
    norm_num
  exact fiber_slice_of_vanishing_subset_sum (K := ℚ) (L := ℚ)
    (N := 1) (q := 2) (Q' := 1) (ζ := (-1 : ℚ)) (ξ₀ := (1 : ℚ))
    (i := 0) (i' := 1) (s := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hmin Finset.univ hsum (by norm_num) (by norm_num) (by norm_num)

end CRTExponentGridSum

#print axioms CRTExponentGridSum.pow_mod_eq
#print axioms CRTExponentGridSum.gridMap_inj
#print axioms CRTExponentGridSum.gridMap_surj
#print axioms CRTExponentGridSum.pow_gridMap
#print axioms CRTExponentGridSum.subset_sum_eq_grid_double_sum
#print axioms CRTExponentGridSum.fiber_slice_of_vanishing_subset_sum
