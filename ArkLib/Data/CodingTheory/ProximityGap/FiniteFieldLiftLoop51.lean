/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumLowerLoop50

/-!
# Loop 51 (O16) — transferring the proven char-0 subset-sumset bound to a finite field through any
# injective reduction hom; the finite-field disproof skeleton, residual = one number-theoretic input.

Loop50 proved, *unconditionally*, that for an actual primitive `2^m`-th root of unity `ζ` in a
characteristic-0 field the subset-sumset over `Fin (2^{m-1})` has `≥ 2^{2^{m-1}}` elements. To turn
this into a disproof of the prize **over a finite field** (the STARK regime) we must transfer the
bound through the reduction `ℤ[ζ] → F_q`. This loop machine-checks the transfer and isolates the one
remaining input.

## The transfer (`card_subsetSumset_finiteField_ge`)
A ring hom `φ : K →+* L` commutes with subset sums: `φ(∑_{j∈S} ζ^j) = ∑_{j∈S} (φ ζ)^j`. So the
`L`-side subset-sumset of `φ ζ` is the `φ`-image of the `K`-side subset-sumset. If `φ` is **injective
on those sums** (`hInj`), the image has the *same* cardinality, so the finite field `L` inherits the
`≥ 2^{2^{m-1}}` bound. Hence the §7 bad count over `L` is super-exponential in the domain `2^m`, and
(with `thm71_no_fixed_exponent`, Loop46) **the prize-as-stated is false over `L`.**

## The sole residual (O16, number-theoretic)
The hypothesis `hInj` is exactly the lifting: a prime `p ≡ 1 (mod 2^m)` (Dirichlet — Mathlib's
`Nat.infinite_setOf_prime_and_eq_mod`) and a reduction `ℤ[ζ] → F_p` injective on the `2^{2^{m-1}}`
distinct sums. Distinctness survives reduction because each difference is a nonzero cyclotomic integer
of nonzero norm (`Algebra.norm_ne_zero_iff`), divisible by only finitely many primes, which Dirichlet
lets us avoid. Formalizing *that existence* needs the cyclotomic ring of integers + norm + Dirichlet
assembly; it is the named residual. Everything *downstream* of it — the entire disproof skeleton — is
now machine-checked here. See `DISPROOF_LOG.md` (O16/Loop51).
-/

open Finset

namespace ArkLib.ProximityGap.FiniteFieldLiftLoop51

open ArkLib.ProximityGap.SubsetSumLowerLoop50

variable {K L : Type*} [Field K] [Field L]

/-- **A ring hom commutes with subset sums of powers.** `φ(∑_{j∈S} ζ^j) = ∑_{j∈S} (φ ζ)^j`. -/
theorem ringHom_subsetSum (φ : K →+* L) (ζ : K) {N : ℕ} (S : Finset (Fin N)) :
    φ (∑ j ∈ S, ζ ^ (j : ℕ)) = ∑ j ∈ S, (φ ζ) ^ (j : ℕ) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_pow])

/-- **Transfer of the lower bound through an injective reduction hom.** If `φ : K →+* L` is injective
on the char-0 subset sums, then the finite field `L` also realises `≥ 2^{2^{m-1}}` distinct subset
sums of `φ ζ`. This is the disproof's transfer step; the only nontrivial input is `hInj`. -/
theorem card_subsetSumset_finiteField_ge [CharZero K] [DecidableEq K] [DecidableEq L]
    {m : ℕ} (hm : 1 ≤ m) {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ m)) (φ : K →+* L)
    (hInj : Set.InjOn φ
      (↑(Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ))))) :
    2 ^ (2 ^ (m - 1)) ≤
      (Finset.univ.image
        (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (φ ζ) ^ (j : ℕ))).card := by
  classical
  -- the `L`-side sumset is the `φ`-image of the `K`-side sumset
  set f : Finset (Fin (2 ^ (m - 1))) → K := fun S => ∑ j ∈ S, ζ ^ (j : ℕ) with hf
  have himg : (Finset.univ.image (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (φ ζ) ^ (j : ℕ)))
      = (Finset.univ.image f).image φ := by
    rw [Finset.image_image]
    refine Finset.image_congr (fun S _ => ?_)
    simp only [hf, Function.comp_apply]
    exact (ringHom_subsetSum φ ζ S).symm
  rw [himg, Finset.card_image_of_injOn hInj]
  exact card_subsetSumset_isPrimitiveRoot_two_pow_ge hm hζ

/-- **End-to-end finite-field disproof skeleton.** Packaged with the §7 numerator comparison: given
the injective reduction (`hInj`) and that the §7 bad count `bad` over `L` is at least the subset-sumset
size (`hbad`, the Lemma-6.1/attack lower bound), no fixed prize exponent `c₁` survives once the domain
`2^m` is large enough that `2^{2^{m-1}}` beats `(2^m)^{c₁}` (`hgap`, an elementary super-exponential
inequality). The prize-as-stated is then false over `L`. -/
theorem prize_false_finiteField_of_lifting [CharZero K] [DecidableEq K] [DecidableEq L]
    {m : ℕ} (hm : 1 ≤ m) {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ m)) (φ : K →+* L)
    (hInj : Set.InjOn φ
      (↑(Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ)))))
    {bad c₁ : ℕ}
    (hbad : (Finset.univ.image
        (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, (φ ζ) ^ (j : ℕ))).card ≤ bad)
    (hgap : (2 ^ m) ^ c₁ < 2 ^ (2 ^ (m - 1))) :
    (2 ^ m) ^ c₁ < bad := by
  have h1 := card_subsetSumset_finiteField_ge hm hζ φ hInj
  omega

end ArkLib.ProximityGap.FiniteFieldLiftLoop51

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.FiniteFieldLiftLoop51.ringHom_subsetSum
#print axioms ArkLib.ProximityGap.FiniteFieldLiftLoop51.card_subsetSumset_finiteField_ge
#print axioms ArkLib.ProximityGap.FiniteFieldLiftLoop51.prize_false_finiteField_of_lifting
