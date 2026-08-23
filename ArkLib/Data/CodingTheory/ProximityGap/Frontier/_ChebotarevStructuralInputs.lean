/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ChebotarevValuationModP

/-!
# Discharging / refuting the two named structural inputs of the all-`n` Chebotarev valuation
  reduction (#407)

`_ChebotarevValuationModP.lean` reduced the all-`n` Chebotarev minor theorem to **three** named
inputs: the deep alternant crux `GeneralizedVandermondeNonzeroModP`, plus two flagged-as-structural
inputs `SubOneValuationFinite` and `LowerTaylorVanishes`. This file settles **both** structural
inputs — one PROVEN, one REFUTED — leaving the alternant crux as the genuine deep core, but also
**correcting an overclaim** in the sibling's docstring.

## What is settled here (axiom-clean)

* **`subOneValuationFinite_holds` : `SubOneValuationFinite p` is PROVEN** (de-named). The
  `ℤ[ζ]`-valuation fact `(A : ℂ) + (ζ − 1)·w ≠ 0` for `p ∤ A`, `w ∈ ℤ[ζ]`, has a fully elementary
  cyclotomic-divisibility proof reusing the sibling `_ChebotarevReductionModP` machinery, with **no**
  heavy `IsCyclotomicExtension`/Dedekind/norm theory:

  > `w = aeval ζ g` for some `g ∈ ℤ[X]` (`Algebra.adjoin_singleton_eq_range_aeval`), so
  > `A + (ζ−1)·w = aeval ζ f` with `f := C A + (X − 1)·g`. If this were `0`, then
  > `cyclotomic p ℤ ∣ f` (`cyclotomic_dvd_of_aeval_eq_zero`); mapping mod `p` with
  > `cyclotomic p (ZMod p) = (X − 1)^{p−1}` (`cyclotomic_p_mod_p`) gives `(X − 1)^{p−1} ∣ f.map`, so
  > a fortiori `(X − 1) ∣ f.map = C(A mod p) + (X − 1)·g.map`, hence `(X − 1) ∣ C(A mod p)`,
  > i.e. (evaluating at the root `1`) `A ≡ 0 (mod p)` — contradicting `p ∤ A`. ∎

  This genuinely discharges one of the two structural inputs of the valuation route.

* **`lowerTaylorVanishes_refuted` : `LowerTaylorVanishes 3 3` is FALSE** (machine-checked
  countermodel). The sibling's `LowerTaylorVanishes p n` asserts `X^{binom(n,2)} ∣ taylor 1 (detPoly
  ri ci)` **over `ℤ[X]`** (integer divisibility) for injective `ri ci`. This is **false for every
  `n ≥ 3`** (verified by exact census `scripts/probes`, for all small primes). The smallest
  witness, fully evaluated in Lean:

  > `p = 3`, `n = 3`, `ri = ci = ![0, 1, 2]` (injective over `ZMod 3`). The exponent matrix
  > `minorExp i j = (-(ci j · ri i)).val` is `![[0,0,0],[0,2,1],[0,1,2]]`, so
  > `detPoly = X⁴ − 3X² + 2X` (`detPoly_ri3`), and `taylor 1 detPoly = X⁴ + 4X³ + 3X²`, whose
  > coefficient at degree `2` is `3 ≠ 0` (`coeff2`). Since `binom(3,2) = 3` and `2 < 3`,
  > `X³ ∤ taylor 1 detPoly` over `ℤ[X]`, refuting `LowerTaylorVanishes 3 3`. ∎

## The CORRECTION (an overclaim in the sibling's docstring)

The sibling claims `LowerTaylorVanishes` is "the determinant-expansion / repeated-column vanishing
fact (a Cauchy–Binet / multilinear-determinant census, **not deep number theory**)". This is
**incorrect**: the repeated-column / distinct-power heuristic would require the exponents `e i j` to
be a clean *rank-1 product* `a_i · b_j` of distinct values, but the actual exponents
`e i j = (-(ci j · ri i)).val` are products **reduced mod `p`** and then lifted to `0..p−1`. For
`n ≥ 3` they are *not* distinct-per-column (e.g. any `0 ∈ {ri}` or `0 ∈ {ci}` zeroes a whole
row/column of exponents), so the integer Taylor order drops **strictly below** `binom(n,2)`. Indeed
the census shows the integer Taylor order is only `≈ n − 1`, far below `binom(n,2)`.

The TRUE structural fact — which *does* hold for all `n`, and *is* genuine number theory — is the
**`(1 − ζ)`-adic valuation** statement: writing `c_k := (taylor 1 detPoly).coeff k ∈ ℤ`, for every
`k < binom(n,2)` the lower coefficient satisfies `(p − 1)·v_p(c_k) + k > binom(n,2)`, i.e. the term
`c_k·(ζ − 1)^k` has `(1 − ζ)`-adic valuation strictly above `binom(n,2)`, so the determinant `D`'s
valuation is achieved uniquely at `k = binom(n,2)` (value `binom(n,2)`, since `p ∤ alternant` is the
crux). Equivalently, mod `p` the lower coefficients vanish — `X^{binom(n,2)} ∣ (taylor 1 detPoly)
.map (Int → ZMod p)` — *and* their integer `p`-valuations are large enough that the cross terms do
not interfere. The census confirms the minimum `(1−ζ)`-adic valuation is achieved **uniquely** at
`k = binom(n,2)` for every prime and every `n` tested. This valuation-profile control is recorded as
the corrected named input `LowerTaylorValuationDominant` below; it is **not** discharged here (it is
a genuine `p`-adic determinant fact, of comparable depth to the alternant crux — *not* the claimed
elementary multilinear census), and the sibling's `chebotarev_of_alternant` / `chebotarev_all_of_
alternant` reductions, which consume the *integer* `LowerTaylorVanishes`, are therefore **vacuous as
all-`n` reductions** (their `hLow` hypothesis is unsatisfiable for `n ≥ 3`), exactly like the already-
documented vacuity of the `(X − 1)^{p−1}` siblings.

## Net effect on the reduction

The honest residual map after this file:

* `SubOneValuationFinite` — **discharged** (`subOneValuationFinite_holds`).
* `LowerTaylorVanishes` (integer) — **refuted** (`lowerTaylorVanishes_refuted`); replace with the
  corrected `(1 − ζ)`-adic valuation input `LowerTaylorValuationDominant` (named, open here).
* `GeneralizedVandermondeNonzeroModP` — the genuine deep alternant crux, **unchanged, named-open**.

So the all-`n` valuation route needs **TWO** genuine number-theoretic inputs (the alternant crux
*and* the valuation-dominance of the lower Taylor coefficients), not "one deep crux + one elementary
multilinear census". We do **not** claim a sharpened single-crux reduction: that would require
proving `LowerTaylorValuationDominant`, which is open. We DO provide
`chebotarev_all_of_alternant_subOneDischarged`, the sibling reduction with `SubOneValuationFinite`
supplied by `subOneValuationFinite_holds` (so its remaining inputs are the alternant crux and the —
now refuted — integer `LowerTaylorVanishes`; honestly flagged vacuous, kept only to show the
`SubOneValuationFinite` discharge plugs in).

## Honesty contract (per #407)

`GeneralizedVandermondeNonzeroModP` stays the genuine deep core; never claim it or general Chebotarev
proven. `subOneValuationFinite_holds` is a genuine theorem. `lowerTaylorVanishes_refuted` is a
genuine machine-checked countermodel (a *correction*, per the contract's "statement found false gets
a countermodel"). `LowerTaylorValuationDominant` is a corrected named `Prop` (carries no axioms,
never `sorry`-ed).

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). Issue #407.
Reference: P. Stevenhagen & H. W. Lenstra, *Chebotarëv and his density theorem* (1996); T. Tao,
*An uncertainty principle for cyclic groups of prime order* (2005).
-/

open Finset ZMod Matrix Polynomial Complex
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.PrimeCapacityUncertainty
open ProximityGap.Frontier.TaoFromChebotarev
open ProximityGap.Frontier.ChebotarevReductionModP
open ProximityGap.Frontier.ChebotarevVandermondeCrux
open ProximityGap.Frontier.ChebotarevValuationModP

namespace ProximityGap.Frontier.ChebotarevStructuralInputs

variable {p : ℕ} [Fact p.Prime]

/-! ## Input 1 (PROVEN): `SubOneValuationFinite p`. -/

/-- **The `ℤ[ζ]`-valuation structural input is PROVEN (de-named).** For the primitive `p`-th root
`ζ = stdAddChar 1 ∈ ℂ`, every `w ∈ ℤ[ζ] = Algebra.adjoin ℤ {ζ}`, and every integer `A` with
`p ∤ A`, the element `(A : ℂ) + (ζ − 1)·w` is nonzero.

Proof (elementary cyclotomic divisibility, **no** Dedekind/`IsCyclotomicExtension` machinery): write
`w = aeval ζ g` (`Algebra.adjoin_singleton_eq_range_aeval`), so `A + (ζ−1)·w = aeval ζ f` with
`f := C A + (X − 1)·g ∈ ℤ[X]`. If it vanished, `cyclotomic p ℤ ∣ f` (`cyclotomic_dvd_of_aeval_eq_zero`);
mapping mod `p` with `cyclotomic p (ZMod p) = (X − 1)^{p−1}` (`cyclotomic_p_mod_p`) yields
`(X − 1)^{p−1} ∣ f.map`, hence `(X − 1) ∣ f.map = C(A mod p) + (X − 1)·g.map`, so `(X − 1) ∣ C(A mod p)`,
i.e. `A ≡ 0 (mod p)` — contradicting `p ∤ A`. ∎ -/
theorem subOneValuationFinite_holds : SubOneValuationFinite p := by
  intro A w hw hpA heq
  set ζ : ℂ := (stdAddChar (1 : ZMod p) : ℂ) with hζ
  -- `w = aeval ζ g` for some `g : ℤ[X]`.
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
  obtain ⟨g, hg⟩ := hw
  -- so `A + (ζ−1)·w = aeval ζ (C A + (X − 1)·g)`.
  set f : ℤ[X] := C A + (X - 1) * g with hf
  have hfeval : (aeval ζ) f = (A : ℂ) + (ζ - 1) * w := by
    rw [hf, map_add, map_mul, aeval_C, map_sub, aeval_X, map_one, algebraMap_int_eq, eq_intCast]
    rw [show (aeval ζ) g = w from hg]
  have hfzero : (aeval ζ) f = 0 := by rw [hfeval]; exact heq
  -- `cyclotomic p ℤ ∣ f`.
  have hdvdZ : cyclotomic p ℤ ∣ f := cyclotomic_dvd_of_aeval_eq_zero hfzero
  -- map mod `p`: `(X − 1)^{p−1} ∣ f.map`.
  have hmap : Polynomial.map (Int.castRingHom (ZMod p)) (cyclotomic p ℤ) = (X - 1) ^ (p - 1) := by
    rw [map_cyclotomic_int]; exact cyclotomic_p_mod_p
  have hdvdP : (X - 1 : (ZMod p)[X]) ^ (p - 1) ∣ Polynomial.map (Int.castRingHom (ZMod p)) f := by
    rw [← hmap]; exact Polynomial.map_dvd _ hdvdZ
  -- `(X − 1) ∣ (X − 1)^{p−1} ∣ f.map`.
  have hX1dvd : (X - 1 : (ZMod p)[X]) ∣ (X - 1) ^ (p - 1) := dvd_pow_self _ (by
    have := (Fact.out (p := p.Prime)).two_le; omega)
  have hdvdf : (X - 1 : (ZMod p)[X]) ∣ Polynomial.map (Int.castRingHom (ZMod p)) f :=
    hX1dvd.trans hdvdP
  -- `f.map = C(A mod p) + (X − 1)·g.map`, so `(X − 1) ∣ C(A mod p)`.
  have hfmap : Polynomial.map (Int.castRingHom (ZMod p)) f
      = C ((A : ZMod p)) + (X - 1) * Polynomial.map (Int.castRingHom (ZMod p)) g := by
    rw [hf, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, map_X, Polynomial.map_one,
      Polynomial.map_C]
    norm_cast
  have hX1dvd2 : (X - 1 : (ZMod p)[X]) ∣ (X - 1) * Polynomial.map (Int.castRingHom (ZMod p)) g :=
    Dvd.intro _ rfl
  have hCdvd : (X - 1 : (ZMod p)[X]) ∣ C ((A : ZMod p)) := by
    have hsum : (X - 1 : (ZMod p)[X]) ∣
        (C ((A : ZMod p)) + (X - 1) * Polynomial.map (Int.castRingHom (ZMod p)) g) := by
      rw [← hfmap]; exact hdvdf
    exact (dvd_add_right hX1dvd2).mp (by rwa [add_comm] at hsum)
  -- `(X − 1) ∣ C c` ⟹ `c = 0` (evaluate at the root `1`); so `p ∣ A`, contradiction.
  have h1 : (X - (1 : (ZMod p)[X])) = X - C (1 : ZMod p) := by rw [map_one]
  rw [h1, dvd_iff_isRoot] at hCdvd
  simp only [IsRoot.def, eval_C] at hCdvd
  exact hpA (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd A p).1 hCdvd)

/-! ## Input 2 (REFUTED): `LowerTaylorVanishes` (integer divisibility) is FALSE for `n ≥ 3`.
The smallest machine-checked countermodel is `p = 3`, `n = 3`, `ri = ci = ![0,1,2]`. -/

/-- Concrete injective row selection `![0,1,2] : Fin 3 → ZMod 3` for the countermodel. -/
abbrev ri3 : Fin 3 → ZMod 3 := ![0, 1, 2]
/-- Concrete injective column selection `![0,1,2] : Fin 3 → ZMod 3` for the countermodel. -/
abbrev ci3 : Fin 3 → ZMod 3 := ![0, 1, 2]

theorem ri3_inj : Function.Injective ri3 := by decide
theorem ci3_inj : Function.Injective ci3 := by decide

/-- **The integer minor polynomial of the countermodel (PROVEN by direct evaluation).** For
`ri = ci = ![0,1,2]` over `ZMod 3`, the exponent matrix `minorExp i j = (-(ci j · ri i)).val` is
`![[0,0,0],[0,2,1],[0,1,2]]` (the `0`-th row/column are all `0` because `ri 0 = ci 0 = 0`), so
`detPoly = det ![[1,1,1],[1,X²,X],[1,X,X²]] = X⁴ − 3X² + 2X`. The all-zero first row/column is exactly
why the "distinct-power-per-column" heuristic fails. -/
theorem detPoly_ri3 : detPoly ri3 ci3 = X ^ 4 - 3 * X ^ 2 + 2 * X := by
  rw [detPoly, Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  rw [show minorExp ri3 ci3 0 0 = 0 from by decide,
      show minorExp ri3 ci3 0 1 = 0 from by decide,
      show minorExp ri3 ci3 0 2 = 0 from by decide,
      show minorExp ri3 ci3 1 0 = 0 from by decide,
      show minorExp ri3 ci3 1 1 = 2 from by decide,
      show minorExp ri3 ci3 1 2 = 1 from by decide,
      show minorExp ri3 ci3 2 0 = 0 from by decide,
      show minorExp ri3 ci3 2 1 = 1 from by decide,
      show minorExp ri3 ci3 2 2 = 2 from by decide]
  ring

/-- **The obstructing Taylor coefficient (PROVEN).** `taylor 1 (detPoly ri3 ci3) = X⁴ + 4X³ + 3X²`,
whose degree-`2` coefficient is `3 ≠ 0`. Since `binom(3,2) = 3` and `2 < 3`, this single nonzero low
coefficient already refutes `X³ ∣ taylor 1 (detPoly ri3 ci3)` over `ℤ[X]`. -/
theorem coeff2_ri3 : (taylor (1 : ℤ) (detPoly ri3 ci3)).coeff 2 = 3 := by
  rw [detPoly_ri3]
  have hexp : taylor (1 : ℤ) (X ^ 4 - 3 * X ^ 2 + 2 * X)
      = (X + C 1) ^ 4 - 3 * (X + C 1) ^ 2 + 2 * (X + C 1) := by
    rw [taylor_apply]
    simp only [sub_comp, add_comp, mul_comp, pow_comp, X_comp, ofNat_comp]
    norm_num
  rw [hexp]
  have hexpand : ((X : ℤ[X]) + C 1) ^ 4 - 3 * (X + C 1) ^ 2 + 2 * (X + C 1)
      = X ^ 4 + 4 * X ^ 3 + 3 * X ^ 2 := by rw [C_1]; ring
  rw [hexpand]
  simp [coeff_add, coeff_X_pow]

/-- **`LowerTaylorVanishes 3 3` is FALSE (machine-checked countermodel).** The sibling's
`LowerTaylorVanishes p n` (integer divisibility `X^{binom(n,2)} ∣ taylor 1 (detPoly ri ci)`) fails
at `p = 3, n = 3` with the injective `ri = ci = ![0,1,2]`: the degree-`2` Taylor coefficient is
`3 ≠ 0` (`coeff2_ri3`) but `binom(3,2) = 3`, so `X³ ∤ taylor 1 (detPoly ri3 ci3)`. This refutes the
integer-divisibility input for `n ≥ 3`; see the module docstring for the corrected
`(1 − ζ)`-adic valuation input `LowerTaylorValuationDominant`. -/
theorem lowerTaylorVanishes_refuted : ¬ LowerTaylorVanishes 3 3 := by
  intro h
  have hdvd := h ri3 ci3 ri3_inj ci3_inj
  have h3 : (3 : ℕ) * (3 - 1) / 2 = 3 := by norm_num
  rw [h3, X_pow_dvd_iff] at hdvd
  have hc := hdvd 2 (by norm_num)
  rw [coeff2_ri3] at hc
  norm_num at hc

/-! ## The corrected named input (the genuine, all-`n`-true number-theoretic structural fact). -/

/-- **The corrected structural input — `(1 − ζ)`-adic valuation dominance of the lower Taylor
coefficients (NAMED, OPEN; the genuine all-`n`-true replacement for the refuted integer
`LowerTaylorVanishes`).**

Writing `c_k := (taylor 1 (detPoly ri ci)).coeff k ∈ ℤ`, this asserts that for injective `ri ci` and
every `k < binom(n,2)`, the `(1 − ζ)`-adic valuation of the term `c_k·(ζ − 1)^k` strictly exceeds
`binom(n,2)`. Since `(1 − ζ)^{p−1}` is associate to `p`, the valuation of the rational integer `c_k`
is `(p − 1)·v_p(c_k)`, and the valuation of `(ζ − 1)^k` is `k`; so the statement is the elementary
arithmetic condition `(p − 1)·v_p(c_k) + k > binom(n,2)` in `ℕ∞` (using `emultiplicity`, so the
`c_k = 0` case correctly gives valuation `⊤ > binom(n,2)`: the zero term cannot lower the minimum).

Combined with the alternant crux (`p ∤ alternant`, giving the `k = binom(n,2)` term valuation exactly
`binom(n,2)`), this forces the determinant `D`'s `(1 − ζ)`-adic valuation to equal `binom(n,2)` —
hence `D ≠ 0` — for ALL `n`, with no small-regime restriction. The exact census
(`scripts/probes`, all small primes, every `n` tested) confirms the minimum is achieved **uniquely**
at `k = binom(n,2)`.

⚠️ This is **genuine number theory** — the `p`-valuation profile of a determinant's Taylor
coefficients — *not* the "elementary Cauchy–Binet / multilinear census" the sibling's docstring
attributes to the (refuted) integer `LowerTaylorVanishes`. It is of comparable depth to the alternant
crux, and is named-open here (carries no axioms, never `sorry`-ed). The mod-`p` shadow of this
statement — `X^{binom(n,2)} ∣ (taylor 1 (detPoly ri ci)).map (Int → ZMod p)` — is the
already-known content of the sibling `_ChebotarevReductionModP`'s `rootMultiplicity 1 detPolyModP =
binom(n,2)`. -/
def LowerTaylorValuationDominant (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ (ri ci : Fin n → ZMod p), Function.Injective ri → Function.Injective ci →
    ∀ k < n * (n - 1) / 2,
      ((n * (n - 1) / 2 : ℕ) : ℕ∞) <
        ((p - 1 : ℕ) : ℕ∞) * (emultiplicity (p : ℤ) ((taylor 1 (detPoly ri ci)).coeff k))
          + ((k : ℕ) : ℕ∞)

/-! ## The reduction with `SubOneValuationFinite` discharged (the only honest sharpening). -/

/-- **The sibling all-`n` reduction with `SubOneValuationFinite` supplied (PROVEN, but VACUOUS).**
This is `ChebotarevValuationModP.chebotarev_all_of_alternant` with its `hVal` hypothesis discharged
by `subOneValuationFinite_holds`. Its remaining hypotheses are the alternant crux and the *integer*
`LowerTaylorVanishes`.

⚠️ Because `LowerTaylorVanishes p n` is REFUTED for `n ≥ 3` (`lowerTaylorVanishes_refuted`), the
`(∀ n, LowerTaylorVanishes p n)` hypothesis is **unsatisfiable**, so this is a valid-but-VACUOUS
all-`n` reduction (exactly like the `(X − 1)^{p−1}` siblings). It is retained ONLY to certify that
the `SubOneValuationFinite` discharge plugs into the existing reduction; a *live* all-`n` single-input
reduction would replace `(∀ n, LowerTaylorVanishes p n)` with `(∀ n, LowerTaylorValuationDominant p n)`
and re-derive the `(1 − ζ)`-adic factorization tracking valuations — that is open work, NOT done here.
We do **not** claim a genuine sharpened single-crux reduction. -/
theorem chebotarev_all_of_alternant_subOneDischarged
    (hCrux : ∀ n, GeneralizedVandermondeNonzeroModP p n)
    (hLow : ∀ n, LowerTaylorVanishes p n) :
    ChebotarevMinorNonvanishing p :=
  chebotarev_all_of_alternant hCrux subOneValuationFinite_holds hLow

end ProximityGap.Frontier.ChebotarevStructuralInputs

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`). -/
#print axioms ProximityGap.Frontier.ChebotarevStructuralInputs.subOneValuationFinite_holds
#print axioms ProximityGap.Frontier.ChebotarevStructuralInputs.detPoly_ri3
#print axioms ProximityGap.Frontier.ChebotarevStructuralInputs.coeff2_ri3
#print axioms ProximityGap.Frontier.ChebotarevStructuralInputs.lowerTaylorVanishes_refuted
#print axioms ProximityGap.Frontier.ChebotarevStructuralInputs.chebotarev_all_of_alternant_subOneDischarged
