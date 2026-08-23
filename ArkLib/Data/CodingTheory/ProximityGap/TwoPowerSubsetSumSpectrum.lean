/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity

/-!
# The subset-sum spectrum of a `2`-power multiplicative subgroup (counting core)

Let `g` be a primitive `2^μ`-th root of unity in a field, `G = ⟨g⟩` of order `s = 2^μ`, and
`h = 2^{μ−1}`.  Then `g^h = −1`, so the `2^μ` group elements split into `h` antipodal classes
`{g^i, g^{i+h}} = {g^i, −g^i}` (`i < h`), and any subset sum collapses to a *signed*
combination `∑_{i<h} ε_i g^i` with `ε ∈ {−1,0,1}^h`.  Because `Φ_{2^μ} = X^h + 1` is the
minimal polynomial of `g` (degree `h`), the map `ε ↦ ∑ ε_i g^i` is **injective** on
`{−1,0,1}^h`.  Counting the signed combinations of a fixed *signed weight* `a` (number of
non-zero `ε_i`) gives `2^a · C(h, a)`, and summing over the realizable weights yields the
**exact** subset-sum spectrum law
`N(μ, r) = ∑_{a valid} 2^a · C(h, a)`.

## Pragmatic scope (honest)

This file formalizes the **self-contained combinatorial counting core**, abstracting the
cyclotomic field theory away as a clean *injectivity hypothesis* `hinj` on the signed-sum
map.  Concretely it proves, for any commutative ring `F` and any `g : F` with `g^h = −1`:

* `antipodal_pow` — the antipodal reduction `g^{i+h} = −g^i` (fully proven, no hypotheses).
* `signedSumStratum_card` — **the stratum count**: given injectivity of the signed-sum map
  `sVal g` on the signed data of support size `a`, the number of distinct signed sums of
  weight `a` is exactly `2^a · C(h, a)`.
* `subsetSumSpectrum_card` — **the exact spectrum**: given injectivity on the union over a
  *valid* set `A` of weights, the number of distinct sums is `∑_{a ∈ A} 2^a · C(h, a)`.
* `kkh26_term_le_subsetSumSpectrum` — the spectrum count dominates the in-tree weight-`r`
  term `2^r · C(h, r)` (the spectrum law sharpens, never loosens, `kkh26_lemma1`).

It does **not** re-derive cyclotomic injectivity (already in `sVal_injOn`/`sVal_injOn_of_not_dvd`),
and it does **not** pin `δ*`.  It sharpens the in-tree lower bound `kkh26_lemma1`
(`2^r·C(h,r)`, the single weight-`r` stratum) to an exact, stratum-summed law: the `a = r`
term is exactly `kkh26_lemma1`'s `2^r·C(h,r)`, and the lower strata `a < r` make the true
count strictly larger.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782 (Lemma 1).
-/

open Finset

namespace ArkLib.ProximityGap.KKH26

/-! ### The antipodal reduction -/

/-- **The antipodal reduction.**  If `g^h = −1` then `g^{i+h} = −g^i`: the element `g^{i+h}`
is the antipode of `g^i`.  This is the only field input the counting core needs from the
`2`-power structure; everything else is combinatorics.  (For `g` a primitive `2^μ`-th root of
unity with `h = 2^{μ−1}`, the hypothesis `g^h = −1` is `pow_half_eq_neg_one`.) -/
theorem antipodal_pow {F : Type*} [CommRing F] {g : F} {h : ℕ} (hh : g ^ h = -1) (i : ℕ) :
    g ^ (i + h) = -(g ^ i) := by
  rw [pow_add, hh, mul_neg, mul_one]

/-! ### The signed-sum stratum count

We reuse the in-tree signed data `sigData h a` (= `(U, T)` with `U ⊆ range h`, `|U| = a`,
`T ⊆ U`) and signed sum `sVal g (U, T) = ∑_{i∈T} g^i − ∑_{i∈U∖T} g^i` from
`KKH26SumsOfRootsOfUnity.lean`.  An `ε ∈ {−1,0,1}^h` of signed weight `a` is exactly a datum
in `sigData h a`: `U` is the support (`ε_i ≠ 0`), `T` the positive part (`ε_i = +1`), and
`U ∖ T` the negative part (`ε_i = −1`); its value is the antipodal-reduced subset sum.  There
are `|sigData h a| = 2^a · C(h, a)` such data (`card_sigData`). -/

/-- **The stratum count.**  Given that the signed-sum map `sVal g` is injective on the signed
data of support size `a` (the linear-independence / cyclotomic input — proven in-tree as
`sVal_injOn` above the prime threshold, or `sVal_injOn_of_not_dvd` at a good prime), the number
of *distinct* signed sums of weight `a` equals `2^a · C(h, a)`.  At `a = r` this is exactly the
in-tree `kkh26_lemma1` lower-bound term; the spectrum below makes the lower strata count too. -/
theorem signedSumStratum_card {F : Type*} [CommRing F] [DecidableEq F] (g : F) (h a : ℕ)
    (hinj : Set.InjOn (sVal g) (sigData h a)) :
    ((sigData h a).image (sVal g)).card = 2 ^ a * h.choose a := by
  rw [Finset.card_image_of_injOn hinj, card_sigData]

/-! ### The exact subset-sum spectrum -/

/-- The full signed-data set over the *valid* weight set `A` (a finset of admissible signed
weights `a`).  Each weight contributes its own stratum `sigData h a`; the union is taken via a
sigma over `A`. -/
def spectrumData (h : ℕ) (A : Finset ℕ) : Finset ((_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)) :=
  A.sigma fun a => sigData h a

/-- The signed sum of a spectrum datum (forgetting the weight tag). -/
def spectrumVal {F : Type*} [CommRing F] (g : F)
    (e : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)) : F :=
  sVal g e.2

/-- **The exact subset-sum spectrum (counting core).**  Given that the signed-sum map
`spectrumVal g` is injective on the spectrum data over the valid weight set `A` (the
linear-independence / cyclotomic input — for a primitive `2^μ`-th root this is the in-tree
`sVal_injOn` extended over the realizable weights), the number of *distinct* signed sums is
exactly the stratum-summed law

  `∑_{a ∈ A} 2^a · C(h, a)`.

For `A = {r}` this is the single in-tree `kkh26_lemma1` term `2^r · C(h, r)`; for the full
realizable weight set `A` it is strictly larger, recovering the exact spectrum `N(μ, r)`. -/
theorem subsetSumSpectrum_card {F : Type*} [CommRing F] [DecidableEq F] (g : F) (h : ℕ) (A : Finset ℕ)
    (hinj : Set.InjOn (spectrumVal g) (spectrumData h A)) :
    ((spectrumData h A).image (spectrumVal g)).card = ∑ a ∈ A, 2 ^ a * h.choose a := by
  classical
  rw [Finset.card_image_of_injOn hinj]
  rw [spectrumData, Finset.card_sigma]
  exact Finset.sum_congr rfl fun a _ => by rw [card_sigData]

/-- **Spectrum mass dominates the single in-tree stratum.**  Whenever the realizable weight
set `A` contains `r`, the exact spectrum count is at least the in-tree `kkh26_lemma1` term
`2^r · C(h, r)` — the spectrum law *sharpens* the lower bound, never loosens it. -/
theorem kkh26_term_le_subsetSumSpectrum {F : Type*} [CommRing F] [DecidableEq F] (g : F) (h : ℕ)
    (A : Finset ℕ) (r : ℕ) (hr : r ∈ A)
    (hinj : Set.InjOn (spectrumVal g) (spectrumData h A)) :
    2 ^ r * h.choose r ≤ ((spectrumData h A).image (spectrumVal g)).card := by
  classical
  rw [subsetSumSpectrum_card g h A hinj]
  exact Finset.single_le_sum (f := fun a => 2 ^ a * h.choose a)
    (fun a _ => Nat.zero_le _) hr

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.antipodal_pow
#print axioms ArkLib.ProximityGap.KKH26.signedSumStratum_card
#print axioms ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card
#print axioms ArkLib.ProximityGap.KKH26.kkh26_term_le_subsetSumSpectrum
