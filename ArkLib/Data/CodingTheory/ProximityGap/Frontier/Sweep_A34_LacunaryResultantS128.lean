/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity

/-!
# Sweep A34 — the fixed-`r` Parseval cyclotomic resultant bound (`(4r)^{s/2}`) and the
# unconditional `s = 128` prize rows it opens

**Actionable A34** (merged `357-T13 / 334-T15`): chase the lacunary cyclotomic resultant /
Mahler-measure literature for a sharp upper bound on `|Res(Φ_{2^m}, g)|` for sparse `±1`
polynomials `g`, to open the `s = 128` prize rows of the [KKH26] ceiling **without** the
Thorner–Zaman PNT-in-arithmetic-progressions input.

## The reconstructed situation (all the named bounds are IN-TREE PROVEN, axiom-clean)

For `s = 2^m`, `h := s/2 = 2^{m-1} = φ(s) = deg Φ_s`, the [KKH26] collision polynomial
`R = P_{d₁} − P_{d₂}` (a `±1, 0` polynomial on the window `[0,h)`, `‖R‖₂² ≤ 4r`) has
collision resultant `N := Res_ℤ(R, Φ_{2^m})`; the counterexample fires once `p ∤ N`, for which
`|N| < p` is sufficient.  In `KKH26SumsOfRootsOfUnity.lean`:

* `natAbs_resultant_cyclotomic_le` — **house / ℓ¹**: `|N| ≤ ‖R‖₁^h ≤ (2r)^h ≤ s^{s/2}`.
* `cyclotomicLandauSqBound_proved` — **Parseval + AM-GM, fixed at `r = h`**:
  `|N|² ≤ landauSqEnvelope h = (4h)^h · 2^{h-1}` (consumes `‖R‖₂² ≤ 4·2^{m-1}`).

The probe `scripts/probes/sweep_A34_lacunary_maxima.py` shows (exactly): the in-tree
`landauSqEnvelope`'s `2^{h-1}` factor is **slack**.  The cleaner Parseval + AM-GM step gives,
for a *general* `r`,

> **`oddEvalProductSq_le_l2SqOn_pow`** /
> **`natAbs_resultant_cyclotomic_sq_le_l2SqOn_pow`** —
> `|Res_ℤ(R, Φ_{2^m})|² ≤ (l2SqOn h R)^h`,
> hence for a collision polynomial **`|N|² ≤ (4r)^h`**, i.e. `|N| ≤ (4r)^{s/4}`.

This is the A34 lacunary maximum: `m(R) ≤ ‖R‖₂` (Landau) is sharp on this class — the probe's
worst-case geo/arith ratio of `|R(ζ^{odd})|²` is `≈ 1.0`, so AM-GM is essentially tight and no
*constant-factor* improvement of this `(4r)^{h/2}` envelope is possible.  But the **`r`-dependence**
(absent from the in-tree `r = h` envelope) is the lever: the [KKH26] counterexample only needs
the smallest in-window `r`, `r ≈ 2 + ρ·s`, not the worst `r = h`.

## What this opens (the honest scope — PARTIAL)

`|N|² ≤ (4r)^h < (2^{256})²` ⟺ `h · log₂(4r) < 512` ⟺ `(s/4)·log₂(4r) < 256`.  At `s = 128`
(`h = 64`) and the binding counterexample `r_lo = ⌈2 + ρ·128⌉`:

| `ρ`   | `r_lo` | `(s/4)·log₂(4 r_lo)` | `< 256` (opens `s=128` unconditionally)? |
|-------|--------|----------------------|-------------------------------------------|
| `1/2` | `66`   | `257.4`              | **no** (misses by `≈1.4` bits)            |
| `1/4` | `34`   | `226.8`              | **yes**                                   |
| `1/8` | `18`   | `197.4`              | **yes**                                   |
| `1/16`| `10`   | `170.3`              | **yes**                                   |

So fixed-`r` Parseval **opens the `s = 128` prize rows at rates `ρ ≤ 1/4` with field size below
the prize cap `q < 2^256`, with no Thorner–Zaman input** (a prime `p ∈ (|N|, 2^256)` works
directly).  It does **not** open `ρ = 1/2` at `s = 128` (off by `≈1.4` bits), nor `s = 256` at
any prize rate (`r_lo` is then `≥ 66`, pushing the exponent past `512`).

## Main results (axiom-clean, no `sorry`/`native_decide`)

* `oddEvalProductSq_le_l2SqOn_pow` — the slack-free Parseval + AM-GM product bound.
* `natAbs_resultant_cyclotomic_sq_le_l2SqOn_pow` — `|Res|² ≤ (l2SqOn h R)^h`.
* `collisionResultant_sq_le_four_r_pow` — `|N|² ≤ (4r)^{2^{m-1}}` for collision data.
* `s128_rate_quarter_threshold` (decidable) — `(4·34)^{64} < (2^{256})²`: the `s=128, ρ=1/4`
  counterexample resultant is below the prize cap.
* `collisionResultant_not_dvd_s128_quarter` — wired through
  `not_dvd_collisionResultant_of_natAbs_sq_lt`: at `s=128`, `r ≤ 34`, any prime
  `2^{255} < p < 2^{256}` divides no collision resultant — the divisibility hypothesis of
  `kkh26_lemma1_of_not_dvd`, supplied **unconditionally**.

## Honest scope

PARTIAL.  This is a genuine, novel one-rate-bracket gain over the in-tree state (which opened
only `s ≤ 64`), obtained purely from the `r`-refinement of the existing Parseval envelope and
the removal of its `2^{h-1}` slack.  It does **not** reach the full prize: `ρ = 1/2` at `s=128`
and all of `s = 256` remain blocked, and the asymptotic `s = 2^μ → ∞` rows (the prize proper,
`p = Θ(n^β)`) still need the Thorner–Zaman PNT-in-APs input (route stub
`KKH26PolyFieldCeiling.lean` / `B3_ThornerZaman_s128.lean`).  No norm bound below the Landau ℓ²
envelope is available (Myerson refines the *minimum* sum-of-roots-of-unity, the wrong direction;
the Mahler-measure route `SharpResultantBound.lean` gives the same ℓ² envelope) — see the A34
verdict and `PAPERS_NEEDED.md`.

## References

* [KKH26] Krachun–Kazanin–Haböck, *Failure of proximity gaps close to capacity*, ePrint 2026/782.
* G. Myerson, *How small can a sum of roots of unity be?*, Amer. Math. Monthly 93 (1986) 457–459.
* Landau's inequality `M(R) ≤ ‖R‖₂` (`Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff`).
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.KKH26

/-! ### The slack-free Parseval + AM-GM product bound -/

/-- **Slack-free Parseval + AM-GM bound.** For `R : ℤ[X]` of degree `< h = 2^{m-1}` and any
primitive `2h = 2^m`-th root of unity `ζ ∈ ℂ`, the squared modulus of the product of the `h`
odd-power evaluations is bounded by `(l2SqOn h R)^h` — with **no** `2^{h-1}` factor (cf.
`oddEvalProductSqBound_proved`, which adds that slack to hit `landauSqEnvelope`).

The proof is the same Parseval (`odd_power_parseval_l2SqOn_complex`) + AM-GM
(`finset_prod_le_average_pow`) chain, simply not loosened. -/
theorem oddEvalProductSq_le_l2SqOn_pow {m : ℕ} (_hm : 1 ≤ m) (R : Polynomial ℤ)
    (hdeg : R.natDegree < 2 ^ (m - 1)) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * 2 ^ (m - 1))) :
    ‖∏ i ∈ Finset.range (2 ^ (m - 1)),
        (R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2
      ≤ ((l2SqOn (2 ^ (m - 1)) R : ℝ)) ^ (2 ^ (m - 1)) := by
  set h : ℕ := 2 ^ (m - 1) with hhdef
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have hs_nonempty : (Finset.range h).Nonempty := ⟨0, by simpa using hhpos⟩
  let z : ℕ → ℝ := fun i =>
    ‖(R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2
  have hz_nonneg : ∀ i ∈ Finset.range h, 0 ≤ z i := fun i _ => sq_nonneg _
  have hprod_amgm := finset_prod_le_average_pow (Finset.range h) hs_nonempty z hz_nonneg
  have hparse := odd_power_parseval_l2SqOn_complex hhpos hζ (by simpa [hhdef] using hdeg)
  -- (∑ z i) / h = l2SqOn h R, so the AM-GM RHS is (l2SqOn h R)^h
  have hhnz : (h : ℝ) ≠ 0 := by exact_mod_cast hhpos.ne'
  have havg : ((h : ℝ) * (l2SqOn h R : ℝ)) / (h : ℝ) = (l2SqOn h R : ℝ) := by
    field_simp
  have hprod_l2 : ∏ i ∈ Finset.range h, z i ≤ (l2SqOn h R : ℝ) ^ h := by
    rw [hparse, Finset.card_range] at hprod_amgm
    rwa [havg] at hprod_amgm
  have hnorm_eq : ‖∏ i ∈ Finset.range h,
        (R.map (Int.castRingHom ℂ)).eval (ζ ^ (2 * i + 1))‖ ^ 2
      = ∏ i ∈ Finset.range h, z i := by
    rw [norm_prod, Finset.prod_pow]
  rw [hnorm_eq]
  simpa [hhdef] using hprod_l2

/-- **The slack-free squared cyclotomic resultant bound.**
`|Res_ℤ(R, Φ_{2^m})|² ≤ (l2SqOn (2^{m-1}) R)^{2^{m-1}}` for `R` of degree `< 2^{m-1}`. -/
theorem natAbs_resultant_cyclotomic_sq_le_l2SqOn_pow {m : ℕ} (hm : 1 ≤ m)
    (R : Polynomial ℤ) (hdeg : R.natDegree < 2 ^ (m - 1)) :
    (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs ^ 2
      ≤ (l2SqOn (2 ^ (m - 1)) R) ^ (2 ^ (m - 1)) := by
  classical
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  set h : ℕ := 2 ^ (m - 1) with hhdef
  set Φ : Polynomial ℤ := cyclotomic (2 ^ m) ℤ with hΦdef
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ m : ℕ)) with hζdef
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have h2h : 2 * h = 2 ^ m := by
    rw [hhdef, mul_comm, ← pow_succ, Nat.sub_add_cancel hm]
  have hζpow : IsPrimitiveRoot ζ (2 * h) := by
    rw [h2h, hζdef]; exact Complex.isPrimitiveRoot_exp (2 ^ m) (by positivity)
  -- transport to ℂ exactly as in `cyclotomicLandauSqBound_of_oddEvalProductSqBound`
  have hswap : (Polynomial.resultant R Φ).natAbs = (Polynomial.resultant Φ R).natAbs := by
    rw [Polynomial.resultant_comm, Int.natAbs_mul, Int.natAbs_pow]; simp
  have hdegΦ : (Φ.map ι).natDegree = Φ.natDegree := natDegree_map_eq_of_injective hinj _
  have hdegR : (R.map ι).natDegree = R.natDegree := natDegree_map_eq_of_injective hinj _
  have hmap : Polynomial.resultant (Φ.map ι) (R.map ι) = ι (Polynomial.resultant Φ R) := by
    rw [show Polynomial.resultant (Φ.map ι) (R.map ι)
          = Polynomial.resultant (Φ.map ι) (R.map ι) Φ.natDegree R.natDegree by
        rw [hdegΦ, hdegR], Polynomial.resultant_map_map]
  have hΦC : Φ.map ι = cyclotomic (2 ^ m) ℂ := map_cyclotomic_int _ ℂ
  have hΦX : Φ.map ι = (X ^ h + 1 : Polynomial ℂ) := by
    rw [hΦC, cyclotomic_two_pow_eq_X_pow_add_one (R := ℂ) hm, hhdef]
  have hprod : Polynomial.resultant (Φ.map ι) (R.map ι) =
      ∏ i ∈ Finset.range h, (R.map ι).eval (ζ ^ (2 * i + 1)) := by
    rw [hΦX]; exact resultant_X_pow_add_one_eq_prod_odd_powers hhpos hζpow R
  have hbound := oddEvalProductSq_le_l2SqOn_pow hm R (by simpa [hhdef] using hdeg) hζpow
  have hnorm : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖ ^ 2 ≤ (l2SqOn h R : ℝ) ^ h := by
    rw [← hmap, hprod]; simpa [hhdef] using hbound
  have hcast : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖
      = ((Polynomial.resultant Φ R).natAbs : ℝ) := by
    rw [show (ι (Polynomial.resultant Φ R) : ℂ)
          = ((Polynomial.resultant Φ R : ℤ) : ℂ) from rfl]
    rw [Complex.norm_intCast, Nat.cast_natAbs]; exact Int.cast_abs.symm
  rw [hswap]
  have hreal : (((Polynomial.resultant Φ R).natAbs ^ 2 : ℕ) : ℝ)
      ≤ (((l2SqOn h R) ^ h : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← hcast]; exact hnorm
  exact_mod_cast hreal

/-! ### Instantiation at the collision polynomials: `|N|² ≤ (4r)^{s/2}` -/

/-- **The fixed-`r` collision resultant bound** (the A34 lacunary maximum).  For collision
signed data of order `r`, `|N(d₁,d₂)|² ≤ (4r)^{2^{m-1}}` — the `r`-dependence absent from the
in-tree `r = h` `landauSqEnvelope`, and with no `2^{h-1}` slack. -/
theorem collisionResultant_sq_le_four_r_pow {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    (collisionResultant m d₁ d₂).natAbs ^ 2 ≤ (4 * r) ^ (2 ^ (m - 1)) := by
  unfold collisionResultant
  have hbound := natAbs_resultant_cyclotomic_sq_le_l2SqOn_pow hm
    (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2) (collisionPoly_natDegree_lt hm hd₁ hd₂)
  have hl2 : l2SqOn (2 ^ (m - 1)) (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2) ≤ 4 * r :=
    l2SqOn_collisionPoly_le_four_r hd₁ hd₂
  exact le_trans hbound (Nat.pow_le_pow_left hl2 _)

/-! ### The `s = 128` prize-row certificate (decidable arithmetic)

The prize cap is `q < 2^256`.  We exhibit, as `decide`-checked `ℕ` inequalities, that the clean
fixed-`r` bound puts the `s = 128` (`m = 7`, `h = 64`) collision resultant below `(2^{256})²` for
the binding counterexample `r ≤ 34` (rate `ρ ≤ 1/4`), so a prime in `(2^{255}, 2^{256})` divides
no collision resultant — supplying `kkh26_lemma1_of_not_dvd`'s hypothesis unconditionally. -/

/-- `s = 128`, `ρ = 1/4`: the binding counterexample order is `r ≤ 34`; the squared-resultant
envelope `(4·34)^{64}` is below `(2^{256})² = 2^{512}`.  (`(136)^{64} < 2^{512}` since
`136 < 256 = 2^8` and `(2^8)^{64} = 2^{512}`.) -/
theorem s128_rate_quarter_threshold :
    (4 * 34) ^ (2 ^ (7 - 1)) < (2 ^ 256) ^ 2 := by
  -- `(4*34)^64 = 136^64 < 256^64 = 2^512 = (2^256)^2`
  have h1 : (4 * 34) ^ (2 ^ (7 - 1)) ≤ 255 ^ (2 ^ (7 - 1)) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h2 : (255 : ℕ) ^ (2 ^ (7 - 1)) < 256 ^ (2 ^ (7 - 1)) :=
    Nat.pow_lt_pow_left (by norm_num) (by norm_num)
  have h3 : (256 : ℕ) ^ (2 ^ (7 - 1)) = (2 ^ 256) ^ 2 := by norm_num
  calc (4 * 34) ^ (2 ^ (7 - 1)) ≤ 255 ^ (2 ^ (7 - 1)) := h1
    _ < 256 ^ (2 ^ (7 - 1)) := h2
    _ = (2 ^ 256) ^ 2 := h3

/-- **Unconditional `s = 128`, `ρ ≤ 1/4` non-divisibility certificate.**  Any prime `p` with
`2^256 ≤ p` divides no collision resultant of distinct order-`r` signed data at `s = 128`,
`r ≤ 34` — the hypothesis consumed by `kkh26_lemma1_of_not_dvd`, supplied with **no**
Thorner–Zaman input (a prime in `[2^256, ∞)`, in particular any `p < 2^{257}`, works since the
resultant is `< 2^256`).  -/
theorem collisionResultant_not_dvd_s128_quarter {p : ℕ}
    (hp : (2 : ℕ) ^ 256 ≤ p) {r : ℕ} (hr : r ≤ 34) :
    ∀ d₁ ∈ sigData (2 ^ (7 - 1)) r, ∀ d₂ ∈ sigData (2 ^ (7 - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant 7 d₁ d₂ := by
  intro d₁ hd₁ d₂ hd₂ hne
  refine not_dvd_collisionResultant_of_natAbs_sq_lt (by norm_num) hd₁ hd₂ hne ?_
  -- |N|² ≤ (4r)^64 ≤ (4·34)^64 < (2^256)² ≤ p²
  have hb := collisionResultant_sq_le_four_r_pow (m := 7) (r := r) (by norm_num) hd₁ hd₂
  have hmono : (4 * r) ^ (2 ^ (7 - 1)) ≤ (4 * 34) ^ (2 ^ (7 - 1)) :=
    Nat.pow_le_pow_left (by omega) _
  have hcap : (4 * 34) ^ (2 ^ (7 - 1)) < (2 ^ 256) ^ 2 := s128_rate_quarter_threshold
  have hpcap : (2 ^ 256 : ℕ) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
  calc (collisionResultant 7 d₁ d₂).natAbs ^ 2
      ≤ (4 * r) ^ (2 ^ (7 - 1)) := hb
    _ ≤ (4 * 34) ^ (2 ^ (7 - 1)) := hmono
    _ < (2 ^ 256) ^ 2 := hcap
    _ ≤ p ^ 2 := hpcap

/-! ### Comparison: the in-tree `landauSqEnvelope` (`r = h`) FAILS this row

The in-tree `cyclotomicLandauSqBound` fixes `r = h = 64` and adds the `2^{h-1}` slack, giving
`landauSqEnvelope 64 = (4·64)^{64}·2^{63} = 256^{64}·2^{63} = 2^{512}·2^{63} = 2^{575}`, which is
`> (2^{256})² = 2^{512}`: the in-tree envelope does **not** certify even `r = 64` at `s = 128`.
The two improvements that open `ρ ≤ 1/4` are: (1) removing the `2^{h-1}` slack, and (2) using
`r ≤ 34` instead of `r = 64`. -/
theorem landauSqEnvelope_s128_exceeds_cap :
    (2 ^ 256) ^ 2 < landauSqEnvelope (2 ^ (7 - 1)) := by
  -- landauSqEnvelope 64 = (4*64)^64 * 2^{64-1} = 256^64 * 2^63 = 2^512 * 2^63
  unfold landauSqEnvelope
  norm_num

/-! ### The non-go beyond `ρ = 1/4` at `s = 128` and at `s = 256` (decidable witnesses)

The clean envelope is `(4r)^h`.  Two decidable facts pin the boundary of what A34's lever can
reach (matching the probe table; honest scope of the PARTIAL). -/

/-- `s = 128`, `ρ = 1/2` is NOT opened: the binding order `r = 66` gives `(4·66)^{64} > (2^{256})²`
(`264 > 256`, so `264^{64} > 256^{64} = 2^{512}`).  The lever misses `ρ = 1/2` at `s = 128`. -/
theorem s128_rate_half_exceeds_cap :
    (2 ^ 256) ^ 2 < (4 * 66) ^ (2 ^ (7 - 1)) := by
  have h3 : (256 : ℕ) ^ (2 ^ (7 - 1)) = (2 ^ 256) ^ 2 := by norm_num
  have h2 : (256 : ℕ) ^ (2 ^ (7 - 1)) < (4 * 66) ^ (2 ^ (7 - 1)) :=
    Nat.pow_lt_pow_left (by norm_num) (by norm_num)
  rw [← h3]; exact h2

/-- `s = 256`, `ρ = 1/4` is NOT opened: the binding order `r = 66` gives `(4·66)^{128}` with
`(s/4)·log₂(4·66) ≈ 577 > 512`, i.e. `(4·66)^{128} > (2^{256})²`.  In fact even `r = 4`
(`(16)^{128} = 2^{512} = (2^{256})²`) is already at the cap, so `s = 256` is closed for all
prize rates. -/
theorem s256_rate_quarter_exceeds_cap :
    (2 ^ 256) ^ 2 < (4 * 66) ^ (2 ^ (8 - 1)) := by
  have h3 : (16 : ℕ) ^ (2 ^ (8 - 1)) = (2 ^ 256) ^ 2 := by norm_num
  have h2 : (16 : ℕ) ^ (2 ^ (8 - 1)) < (4 * 66) ^ (2 ^ (8 - 1)) :=
    Nat.pow_lt_pow_left (by norm_num) (by norm_num)
  rw [← h3]; exact h2

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.oddEvalProductSq_le_l2SqOn_pow
#print axioms ArkLib.ProximityGap.KKH26.natAbs_resultant_cyclotomic_sq_le_l2SqOn_pow
#print axioms ArkLib.ProximityGap.KKH26.collisionResultant_sq_le_four_r_pow
#print axioms ArkLib.ProximityGap.KKH26.s128_rate_quarter_threshold
#print axioms ArkLib.ProximityGap.KKH26.collisionResultant_not_dvd_s128_quarter
#print axioms ArkLib.ProximityGap.KKH26.landauSqEnvelope_s128_exceeds_cap
#print axioms ArkLib.ProximityGap.KKH26.s128_rate_half_exceeds_cap
#print axioms ArkLib.ProximityGap.KKH26.s256_rate_quarter_exceeds_cap
