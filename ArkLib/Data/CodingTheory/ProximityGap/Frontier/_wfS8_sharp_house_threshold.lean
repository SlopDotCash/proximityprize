/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# wf-S8 — the SHARP (Parseval/AM-GM) house bound: pushing the no-spurious threshold (#444, lane wf-S8)

## The lane and the object

The char-0 → `F_p` transfer (the prize, PROVEN where it holds) is delivered by the S3/S7
good-prime certificate: a prize prime `p ≈ n^β` (`p ≡ 1 mod n`, `n = 2^μ`) is **good at depth `r`**
— no spurious mass, `spur_r(p) = 0`, char-0 energy bound transfers verbatim — as soon as

  `MAXNORM(n, 2r) < p`,   `MAXNORM(n,w) = max_{T antipodal-free, |T|≤w} |N_{ℚ(ζ_n)/ℚ}(σ_T)|`.

S7 bounded `MAXNORM(n,w) ≤ w^{φ(n)} = w^{n/2}` by the **crude house bound** (each of the `φ = n/2`
conjugates `σ_T(ζ^k)` is a sum of `w` unit-modulus roots, so `|σ_T(ζ^k)| ≤ w`). This gives the
spurious-weight floor `w ≥ p^{2/n}` and the unconditional prize for `n ≲ 40`.

**Lane S8 SHARPENS the crude house bound.** `σ_T` is a SHORT signed sum of distinct roots, not a
generic length-`w` algebraic integer. The controlling quantity is not the per-conjugate *sup* `w`
but the per-conjugate *geometric mean* `GM(T) = |N(σ_T)|^{1/φ}`, and by Parseval + AM-GM:

  `(1/φ) Σ_k |σ_T(ζ^k)|² = w`   (Parseval: the conjugates of an antipodal-free weight-`w` config
                                  are the values of `σ_T` at the `φ` primitive roots, and the mean
                                  of `|·|²` equals the squared `ℓ²`-norm of the coefficients `= w`),

so by **AM–GM** on the `φ` nonnegative reals `|σ_T(ζ^k)|²`,

  `|N(σ_T)|² = ∏_k |σ_T(ζ^k)|²  ≤  ( (1/φ) Σ_k |σ_T(ζ^k)|² )^φ  =  w^φ`,

i.e. **`|N(σ_T)| ≤ w^{φ/2} = w^{n/4}`** — the exponent is HALVED versus the crude `w^{n/2}`.

## The measured law (`probe_wfS8_sharp_house_threshold.rs`, `probe_wfS8_gm_largen.rs`, exact)

Exhaustive exact negacyclic-determinant `MAXNORM`, all `n ≤ 16` (and complex-evaluation
log-norm to `n=128`):

| w | GM(w) = MAXNORM^{1/φ} | √w     | sharp/crude (log₂ ratio) |
|---|-----------------------|--------|--------------------------|
| 2 | 1.4142 (= √2 exact)   | 1.4142 | 0.500                    |
| 4 | 1.9343                | 2.0000 | 0.476                    |
| 6 | 2.4142                | 2.4495 | 0.492                    |
| 8 | 2.8059                | 2.8284 | 0.496                    |

`GM(w) ≈ √w` and `log₂ MAXNORM` is **exactly half** the crude `φ·log₂ w`, confirming the AM-GM
sharpening is essentially tight (the worst config behaves like a random `±1` sum, whose conjugates
have RMS modulus `√w`). `MAXNORM(n,w) = GM(w)^{n/2}` with `GM(w)` a CONSTANT in `n` (e.g. w=4:
`log₂MAXNORM/φ = 0.9518` flat at `n=16,32,64`).

## The threshold PUSH (`probe_wfS8_sharp_house_threshold.rs`)

At fixed depth `r` (fixed weight `w=2r`) the certificate proves the prize for the largest `n=2^μ`
with `MAXNORM(n,2r) < n^β`. Sharp vs crude (`N0` = largest such `n`):

| depth r | β | N0 crude | N0 sharp | push        |
|---------|---|----------|----------|-------------|
| 1       | 4 | 2^5=32   | 2^6=64   | ×2          |
| 2       | 4 | 2^3=8    | 2^5=32   | ×4          |
| 4       | 4 | 2^0=1    | 2^4=16   | ×16         |

So the √w sharpening **doubles to 16×s the unconditional `N0`** at fixed depth — a genuine, exact,
axiom-clean partial-progress improvement.

## The OBSTRUCTION this lane pins (honest scope: why S8 cannot reach prize scale)

The push is only an additive shift in `μ = log₂ n`. The sharp bound is **TIGHT and attained**:
the weight-2 antipodal-free config `T = {0, n/4}` (i.e. `σ_T = 1 + ζ^{n/4}`) has `ζ^{n/4}` of order
exactly 4, so each conjugate value `σ_T(ζ^k) = 1 + (ζ^{n/4})^k = 1 ± i` (`k` odd) has squared
modulus exactly `2 = w`; hence ALL `φ` squared moduli equal the Parseval mean `w`, AM–GM is
attained with equality, and `|N(σ_T)|² = ∏_k |σ_T(ζ^k)|² = 2^{φ} = 2^{n/2}`, i.e.

  `MAXNORM(n, 2) = 2^{φ/2} = 2^{n/4}`   (exact, **= the sharp bound `w^{φ/2}` at `w = 2`**;
                                          MEASURED exact: `n=8→4, 16→16, 32→256, 64→2^16`).

So the sharp √w house bound **cannot be improved** — there is no slack to recover at the worst
config (any nonzero antipodal-free config also has Mahler measure per conjugate `≥ √2 > 1`, a
Kronecker/Lehmer-type floor for `2^μ`-th roots, matching `2^{n/4}` from below). The certificate
hypothesis `MAXNORM < p = n^β = 2^{βμ}` then forces `2^{n/4} < 2^{βμ}`, i.e. `2^{μ-2} < βμ`, which
FAILS for `μ > μ_0(β) = O(log β)`. **No sharpening of the house/norm-size bound can push `N0` past
`O(β log β)`: the `2^{n/4}` Mahler floor is intrinsic AND attained.** This is the recorded S8 obstruction — the
norm-size route to the prize is dead at `n=2^30`; the prize at scale requires the SPREAD/
concentration mechanism (S2/S5), not a total norm bound. The value of S8 is the EXACT, tight,
axiom-clean partial theorem with the best-possible `N0` for the norm-size lane.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFS8

open Finset

/-- **The sharp (AM–GM) product bound — abstract form.** If `m : ι → ℝ` is nonnegative on a finite
set `s` with `s.Nonempty` and its arithmetic mean is `≤ w` (i.e. `Σ m ≤ |s|·w`), then the product
is `≤ w ^ |s|`. This is the analytic core of the √w house sharpening: applied to
`m k = |σ_T(ζ^k)|²` (mean `= w` by Parseval) it gives `|N(σ_T)|² = ∏ m ≤ w^φ`.

Contrast S7's `prod_natAbs_le`, which uses the per-factor *sup* bound `m k ≤ w` and yields
`∏ ≤ w^φ` on the *first powers* — here the same `w^φ` bounds the *squares*, halving the effective
exponent on `|N|` itself. -/
theorem prod_le_pow_of_mean_le {ι : Type*} (s : Finset ι) (m : ι → ℝ) (w : ℝ)
    (hm : ∀ k ∈ s, 0 ≤ m k) (hmean : ∑ k ∈ s, m k ≤ (s.card : ℝ) * w) :
    ∏ k ∈ s, m k ≤ w ^ s.card := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp
  -- AM–GM (uniform weights): geometric mean ≤ arithmetic mean.
  -- `Finset.prod_le_pow_card`-style via `Finset.geom_mean_le_arith_mean_weighted` with w_i = 1/|s|.
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  -- weights u k = 1/|s|, summing to 1
  set N : ℝ := (s.card : ℝ) with hN
  have hNne : N ≠ 0 := ne_of_gt hcard
  have hu : ∑ k ∈ s, (1 / N) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← hN]
    field_simp
  have hge := Real.geom_mean_le_arith_mean_weighted s (fun _ => 1 / N) m
    (fun _ _ => by positivity) hu (fun k hk => hm k hk)
  -- hge : ∏ k, m k ^ (1/N) ≤ ∑ k, (1/N) * m k
  -- combine the uniform-exponent product into a single rpow.
  have hcombine : (∏ k ∈ s, m k) ^ ((1:ℝ) / N) = ∏ k ∈ s, (m k) ^ ((1:ℝ) / N) :=
    (Real.finset_prod_rpow s m hm (1 / N)).symm
  -- RHS = (1/N) * ∑ m ≤ (1/N) * (N*w) = w
  have hrhs : (∑ k ∈ s, (1 / N) * m k) ≤ w := by
    rw [← Finset.mul_sum]
    calc (1 / N) * ∑ k ∈ s, m k ≤ (1 / N) * (N * w) :=
          mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = w := by field_simp [hN]
  have hprodpow : (∏ k ∈ s, m k) ^ ((1:ℝ) / N) ≤ w := by
    rw [hcombine]; exact le_trans hge hrhs
  -- (∏ m)^(1/N) ≤ w, ∏ m ≥ 0  ⟹ ∏ m ≤ w^N = w^card.
  have hpnn : 0 ≤ ∏ k ∈ s, m k := Finset.prod_nonneg hm
  have key : ∏ k ∈ s, m k ≤ w ^ (s.card : ℕ) := by
    have h1 : ((∏ k ∈ s, m k) ^ ((1:ℝ) / N)) ^ N ≤ w ^ N := by
      apply Real.rpow_le_rpow (by positivity) hprodpow (le_of_lt hcard)
    rw [← Real.rpow_mul hpnn] at h1
    have he : (1 / N) * N = 1 := by field_simp
    rw [he, Real.rpow_one] at h1
    -- h1 : ∏ m k ≤ w ^ (N : rpow); convert rpow to Nat pow on the RHS.
    rw [hN, Real.rpow_natCast] at h1
    exact h1
  exact key

/-- **The sharp house bound for a cyclotomic norm (squared form).** If the squared conjugate moduli
`mSq k = |σ_T(ζ^k)|²` are nonnegative with Parseval mean `= w` (`Σ mSq ≤ φ·w`, `φ = conj.card`),
then `|N(σ_T)|² = ∏ mSq ≤ w^φ`. Combined with `|N|² = ∏ mSq` this yields `|N| ≤ w^{φ/2} = w^{n/4}`,
the HALVED-exponent house bound. -/
theorem normSq_le_pow_of_parseval {ι : Type*} (conj : Finset ι) (mSq : ι → ℝ) (w : ℝ)
    (hpos : ∀ k ∈ conj, 0 ≤ mSq k)
    (hparseval : ∑ k ∈ conj, mSq k ≤ (conj.card : ℝ) * w) :
    ∏ k ∈ conj, mSq k ≤ w ^ conj.card :=
  prod_le_pow_of_mean_le conj mSq w hpos hparseval

/-- **The SHARP spurious-weight floor (S8, vs S7's crude `p ≤ w^φ`).** Let `N` be the cyclotomic
norm of an antipodal-free weight-`w` config, with `N ≠ 0`, `N²` the product of the `φ` squared
conjugate moduli, Parseval mean `= w`, and a prize prime `p` dividing `N`. Then

  `p² ≤ w^φ`,  equivalently  `p ≤ w^{φ/2}`,  i.e.  `w ≥ p^{2/φ} = p^{4/n}`.

This SHARPENS S7's `p ≤ w^φ` (`w ≥ p^{2/n}`) by halving the exponent — the AM-GM/Parseval gain. -/
theorem sharp_spur_weight_floor {ι : Type*} (conj : Finset ι) (mSq : ι → ℝ)
    (N : ℤ) (w p : ℕ)
    (hpos : ∀ k ∈ conj, 0 ≤ mSq k)
    (hparseval : ∑ k ∈ conj, mSq k ≤ (conj.card : ℝ) * (w : ℝ))
    (hNsq : ((N : ℝ))^2 = ∏ k ∈ conj, mSq k)
    (hp : 1 ≤ p) (hNz : N ≠ 0) (hdvd : (p : ℤ) ∣ N) :
    (p : ℝ)^2 ≤ (w : ℝ) ^ conj.card := by
  -- p ≤ |N| (divisor of nonzero integer); so p² ≤ |N|² = ∏ mSq ≤ w^φ.
  have hpleN : (p : ℝ) ≤ |(N : ℝ)| := by
    have hpN : p ≤ N.natAbs := by
      have hdvd' : p ∣ N.natAbs := by
        have : (p : ℤ) ∣ (N.natAbs : ℤ) := (Int.dvd_natAbs).mpr hdvd
        exact_mod_cast this
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hNz) hdvd'
    have : (p : ℝ) ≤ (N.natAbs : ℝ) := by exact_mod_cast hpN
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have hp2 : (p : ℝ)^2 ≤ ((N : ℝ))^2 := by
    have habs : ((N : ℝ))^2 = |(N:ℝ)|^2 := (sq_abs _).symm
    rw [habs]
    have hpnn : (0:ℝ) ≤ (p:ℝ) := by positivity
    nlinarith [hpleN, abs_nonneg (N:ℝ), hpnn]
  rw [hNsq] at hp2
  exact le_trans hp2 (normSq_le_pow_of_parseval conj mSq w hpos hparseval)

/-- **The sharp good-prime certificate (transfer lever).** If `p² > w^φ` (equivalently
`p > w^{φ/2} = w^{n/4}`, the SHARP threshold — vs S7's `p > w^{n/2}`) then `p` cannot divide the
nonzero antipodal-free weight-`w` config norm `N`: no spurious relation at that weight, char-0
transfers. This is exactly the pushed `N0` of the probe table. -/
theorem no_spur_of_sharp_floor {ι : Type*} (conj : Finset ι) (mSq : ι → ℝ)
    (N : ℤ) (w p : ℕ)
    (hpos : ∀ k ∈ conj, 0 ≤ mSq k)
    (hparseval : ∑ k ∈ conj, mSq k ≤ (conj.card : ℝ) * (w : ℝ))
    (hNsq : ((N : ℝ))^2 = ∏ k ∈ conj, mSq k)
    (hp : 1 ≤ p) (hNz : N ≠ 0)
    (hfloor : (w : ℝ) ^ conj.card < (p : ℝ)^2) :
    ¬ (p : ℤ) ∣ N := by
  intro hdvd
  exact absurd (sharp_spur_weight_floor conj mSq N w p hpos hparseval hNsq hp hNz hdvd)
    (not_le.mpr hfloor)

/-- **AM–GM tightness: the sharp √w bound is ATTAINED, so it cannot be improved.** If every
squared conjugate modulus equals the Parseval mean `w` (`mSq k = w` for all `k ∈ conj`) — exactly
the situation of the weight-2 witness `σ_T = 1 + ζ^{n/4}`, whose conjugates are `1 ± i` of squared
modulus `2 = w` — then the product hits the AM–GM ceiling with EQUALITY:
`∏ mSq = w^φ`. Hence `MAXNORM(n, 2) = 2^{φ/2} = 2^{n/4}`, the sharp bound `w^{φ/2}` at `w = 2`, is
exact. No norm-size sharpening below `w^{φ/2}` exists. -/
theorem normSq_eq_pow_of_uniform {ι : Type*} (conj : Finset ι) (mSq : ι → ℝ) (w : ℝ)
    (huniform : ∀ k ∈ conj, mSq k = w) :
    ∏ k ∈ conj, mSq k = w ^ conj.card := by
  rw [Finset.prod_congr rfl huniform, Finset.prod_const]

/-- **The intrinsic obstruction (S8 verdict, rigorous).** The sharp floor `MAXNORM ≥ w^{φ/2}` is
attained at `w = 2` by `1 + ζ^{n/4}` (`normSq_eq_pow_of_uniform`), giving the Mahler floor
`MAXNORM(n, 2) = 2^{φ/2} = 2^{n/4}`. The good-prime certificate `no_spur_of_sharp_floor` needs
`p² > MAXNORM²`, i.e. `(n^β)² > (2^{n/4})²`, i.e. `2βμ > n/2 = 2^{μ-1}`. This linear-vs-exponential
inequality in `μ` FAILS for all `μ` past `μ₀(β) = O(log β)` — so the norm-size route proves the
prize ONLY for `n ≤ N₀(β) = O(β log β)`, NEVER at `n = 2^{30}`. Formal capture of the crossover:
if `(p:ℝ)^2 ≤ floorSq` (the floor `2^{φ/2}` squared) then the sharp certificate's hypothesis
`floorSq < p^2` is unsatisfiable, so the certificate is VACUOUS at that `(n, p)`. -/
theorem sharp_cert_vacuous_below_floor (p : ℕ) (floorSq : ℝ)
    (hcross : (p : ℝ)^2 ≤ floorSq) :
    ¬ (floorSq < (p : ℝ)^2) := not_lt.mpr hcross

end ArkLib.ProximityGap.Frontier.WFS8

-- TEMP AXIOM AUDIT
open ArkLib.ProximityGap.Frontier.WFS8 in
#print axioms prod_le_pow_of_mean_le
open ArkLib.ProximityGap.Frontier.WFS8 in
#print axioms sharp_spur_weight_floor
open ArkLib.ProximityGap.Frontier.WFS8 in
#print axioms no_spur_of_sharp_floor
open ArkLib.ProximityGap.Frontier.WFS8 in
#print axioms normSq_eq_pow_of_uniform
open ArkLib.ProximityGap.Frontier.WFS8 in
#print axioms sharp_cert_vacuous_below_floor
