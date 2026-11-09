/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumLowerLoop50

/-!
# Loop 51 (O16): transferring the char-0 subset-sumset bound along a reduction hom

Loop50 proved, *unconditionally*, that for an actual primitive `2^m`-th root of unity `ζ` in a
characteristic-0 field the subset-sumset over `Fin (2^{m-1})` has `≥ 2^{2^{m-1}}` elements. To turn
this into a disproof of the prize **over a finite field** (the STARK regime) one must transfer the
bound through a reduction `ℤ[ζ] → F_q`. This file machine-checks the transfer step and isolates the
inputs it needs; it does **not** construct the reduction, and it does not prove the prize false.

## Model correction (audit 2026-10-28, PG-073)
An earlier version took the reduction to be a ring hom `φ : K →+* L` out of the characteristic-0
*field* `K`. That front door is unsatisfiable whenever `L` is finite or has positive
characteristic: a unital ring hom out of a field into a nontrivial ring is injective, so it would
force `CharZero L` (`isEmpty_ringHom_of_charZero_of_charP` below records the impossibility). The
reduction is now modelled on an **integral model** `A` (e.g. `ℤ[ζ]`, `𝓞 K`, or an adjoin-root
ring): `A` carries a comparison hom `ι : A →+* K` into a characteristic-0 field with `ι ζ` a
primitive `2^m`-th root of unity, and a separate reduction hom `φ : A →+* L` into an arbitrary
commutative ring `L` (a finite field included). Such pairs exist; e.g. `redHom` in
`FpReductionHom.lean` constructs a reduction `𝓞 K →ₐ[ℤ] ZMod p` from the cyclotomic power basis.

## The transfer (`card_subsetSumset_finiteField_ge`)
A ring hom commutes with subset sums: `φ(∑_{j∈S} ζ^j) = ∑_{j∈S} (φ ζ)^j`. So the `L`-side
subset-sumset of `φ ζ` is the `φ`-image of the `A`-side subset-sumset, and the `K`-side
subset-sumset of `ι ζ` is the `ι`-image of the same `A`-side set (so the `A`-side set is at least
as large as the `K`-side one, which Loop50 bounds). If `φ` is **injective on the `A`-side sums**
(`hInj`), the `L`-side set has the same cardinality as the `A`-side one, so `L` inherits the
`≥ 2^{2^{m-1}}` bound.

## What remains explicit (O16, number-theoretic)
* `hInj` — the finite restricted injectivity: a prime `p ≡ 1 (mod 2^m)` (Dirichlet — Mathlib's
  `Nat.infinite_setOf_prime_and_eq_mod`) and a reduction `A → F_p` injective on the
  `2^{2^{m-1}}` distinct sums. The intended argument: each difference is a nonzero cyclotomic
  integer of nonzero norm (`Algebra.norm_ne_zero_iff`), divisible by only finitely many primes,
  which Dirichlet lets us avoid. This norm/prime-avoidance existence is **not** formalized here.
* `hbad` in `prize_false_finiteField_of_lifting` — the bridge from the subset-sumset size to the
  §7 bad-scalar count over `L` (the Lemma-6.1/attack lower bound) is an explicit hypothesis.
See `docs/research/proximity-gap/DISPROOF_LOG.md` (O16/Loop51).
-/

open Finset

namespace ArkLib.ProximityGap.FiniteFieldLiftLoop51

open ArkLib.ProximityGap.SubsetSumLowerLoop50

/-- **No reduction hom out of a characteristic-0 field.** A unital ring hom from a field `K` of
characteristic zero into a nontrivial ring `L` of characteristic `p ≠ 0` (for instance a finite
field) cannot exist: it would be injective, yet it sends the nonzero element `(p : K)` to
`(p : L) = 0`. This is why the transfer below starts from an integral model `A`, not from `K`. -/
theorem isEmpty_ringHom_of_charZero_of_charP (K L : Type*) [Field K] [CharZero K] [CommRing L]
    [Nontrivial L] (p : ℕ) [CharP L p] (hp : p ≠ 0) : IsEmpty (K →+* L) := by
  refine ⟨fun φ => ?_⟩
  have h1 : φ (p : K) = φ 0 := by rw [map_natCast, CharP.cast_eq_zero L p, map_zero]
  exact (Nat.cast_ne_zero (R := K)).mpr hp (φ.injective h1)

variable {A K L : Type*} [CommRing A] [Field K] [CommRing L]

/-- **A ring hom commutes with subset sums of powers.** `φ(∑_{j∈S} ζ^j) = ∑_{j∈S} (φ ζ)^j`. -/
theorem ringHom_subsetSum {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (ζ : R)
    {N : ℕ} (T : Finset (Fin N)) :
    φ (∑ j ∈ T, ζ ^ (j : ℕ)) = ∑ j ∈ T, (φ ζ) ^ (j : ℕ) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_pow])

/-- **Transfer of the lower bound through a reduction hom on an integral model.** Let `A` be a
commutative ring (e.g. `ℤ[ζ]` or `𝓞 K`) with a comparison hom `ι : A →+* K` into a
characteristic-0 field sending `ζ` to a primitive `2^m`-th root of unity, and let `φ : A →+* L` be a
hom into any commutative ring `L` (e.g. a reduction `A →+* ZMod p`). If `φ` is injective on the
`A`-side subset sums (`hInj`), then `L` realises `≥ 2^{2^{m-1}}` distinct subset sums of `φ ζ`.
`ι` need not be injective: the `K`-side sumset is the `ι`-image of the `A`-side sumset. The
nontrivial input `hInj` (norm / prime avoidance) is an explicit hypothesis, not proved here. -/
theorem card_subsetSumset_finiteField_ge [CharZero K] [DecidableEq A] [DecidableEq K]
    [DecidableEq L] {m : ℕ} (hm : 1 ≤ m) (ι : A →+* K) {ζ : A}
    (hζ : IsPrimitiveRoot (ι ζ) (2 ^ m)) (φ : A →+* L)
    (hInj : Set.InjOn φ
      (↑(Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ))))) :
    2 ^ (2 ^ (m - 1)) ≤
      (Finset.univ.image
        (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (φ ζ) ^ (j : ℕ))).card := by
  classical
  set f : Finset (Fin (2 ^ (m - 1))) → A := fun S => ∑ j ∈ S, ζ ^ (j : ℕ) with hf
  -- the `L`-side sumset is the `φ`-image of the `A`-side sumset
  have himgL :
      (Finset.univ.image (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (φ ζ) ^ (j : ℕ)))
        = (Finset.univ.image f).image φ := by
    rw [Finset.image_image]
    refine Finset.image_congr (fun S _ => ?_)
    simp only [hf, Function.comp_apply]
    exact (ringHom_subsetSum φ ζ S).symm
  -- the `K`-side sumset is the `ι`-image of the `A`-side sumset
  have himgK :
      (Finset.univ.image (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (ι ζ) ^ (j : ℕ)))
        = (Finset.univ.image f).image ι := by
    rw [Finset.image_image]
    refine Finset.image_congr (fun S _ => ?_)
    simp only [hf, Function.comp_apply]
    exact (ringHom_subsetSum ι ζ S).symm
  rw [himgL, Finset.card_image_of_injOn hInj]
  calc 2 ^ (2 ^ (m - 1))
      ≤ (Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (ι ζ) ^ (j : ℕ))).card :=
        card_subsetSumset_isPrimitiveRoot_two_pow_ge hm hζ
    _ ≤ (Finset.univ.image f).card := by
        rw [himgK]; exact Finset.card_image_le

/-- **Conditional finite-field disproof skeleton.** Packaged with the §7 numerator comparison: given
the injective reduction on the integral model (`hInj`) and that the §7 bad count `bad` over `L` is
at least the subset-sumset size (`hbad`, the Lemma-6.1/attack lower bound, an explicit hypothesis),
no fixed prize exponent `c₁` survives once the domain `2^m` is large enough that `2^{2^{m-1}}`
beats `(2^m)^{c₁}` (`hgap`, an elementary super-exponential inequality). This is conditional on
`hInj` and `hbad`; neither is constructed here. -/
theorem prize_false_finiteField_of_lifting [CharZero K] [DecidableEq A] [DecidableEq K]
    [DecidableEq L] {m : ℕ} (hm : 1 ≤ m) (ι : A →+* K) {ζ : A}
    (hζ : IsPrimitiveRoot (ι ζ) (2 ^ m)) (φ : A →+* L)
    (hInj : Set.InjOn φ
      (↑(Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ)))))
    {bad c₁ : ℕ}
    (hbad : (Finset.univ.image
        (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (φ ζ) ^ (j : ℕ))).card ≤ bad)
    (hgap : (2 ^ m) ^ c₁ < 2 ^ (2 ^ (m - 1))) :
    (2 ^ m) ^ c₁ < bad := by
  have h1 := card_subsetSumset_finiteField_ge hm ι hζ φ hInj
  omega

end ArkLib.ProximityGap.FiniteFieldLiftLoop51

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.FiniteFieldLiftLoop51.isEmpty_ringHom_of_charZero_of_charP
#print axioms ArkLib.ProximityGap.FiniteFieldLiftLoop51.ringHom_subsetSum
#print axioms ArkLib.ProximityGap.FiniteFieldLiftLoop51.card_subsetSumset_finiteField_ge
#print axioms ArkLib.ProximityGap.FiniteFieldLiftLoop51.prize_false_finiteField_of_lifting
