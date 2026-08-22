/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CyclotomicResultantBound
import Mathlib.Tactic.NormNum.Prime

/-!
# The floor-successor realizability ⇔ resultant-divisibility bridge (#466, lane FS4)

**The load-bearing char-0 fact behind the whole floor-successor program, machine-checked.**

The floor-successor obstruction (`_FloorSuccessorNorm.lean`, round-7 mechanism S3) is:
for `n = 2^k`, a structured "adjacent-7th-type" pattern `A ⊆ ℤ/n` is *realizable* over `𝔽_p`
(`p ≡ 1 mod n`) — i.e. `p` is floor-bad witnessed by `A` — iff the pattern's obstruction matrix
`M_A` drops rank mod `p`.  Rounds 7 and 8 established (by exact `ℤ[ζ_n]` arithmetic + `sympy`
resultant, `probe_466_successor_norm.py`) that this rank-drop is governed by an integer
*obstruction norm* `N(A) = Res(V_A, Φ_n)`, the resultant of a `ℤ[X]` representative `V_A` of the
obstruction coefficient with the cyclotomic polynomial `Φ_n`; and that
`floor-bad ⟹ p ∣ N(A)`.  Until now that necessary condition — the "rank-drop ⟹ `p` divides the
resultant" step — was only *computed*, never Lean-verified.

This file supplies the missing Lean layer, adapting the width-four resultant machinery of
`CyclotomicResultantBound.lean` (`dvd_resultant_of_isPrimitiveRoot_isRoot`) — the SAME
cyclotomic-resultant-divisibility pattern already formalized for the width-four object
(`E2W4CyclotomicNonCollision`, `CanonicalWidthFourBadPrimeSet`) — to the floor obstruction.

## What is a "floor obstruction polynomial"?

For a fixed pattern `A`, its obstruction coefficient `r_k(A)` is an algebraic integer of
`ℤ[ζ_n]`; write it as `V_A(ζ_n)` for a representative `V_A ∈ ℤ[X]` (`ζ_n` a primitive `n`-th
root).  The pattern is realizable over `𝔽_p` exactly when this coefficient *vanishes* at a
primitive `n`-th root `ζ` of `ZMod p`, i.e. `V_A` and `Φ_n` share the root `ζ` mod `p`
(equivalently, they are non-coprime mod `p` — the Sylvester matrix, i.e. the obstruction matrix,
is singular; "the rank drops").  That is `FloorRealizableAt` below.

## Main statements (axiom-clean)

* `FloorRealizableAt` — the char-`p` realizability predicate: a primitive `n`-th root of
  `ZMod p` is a common root of `V_A` and `Φ_n`.
* `prime_dvd_resultant_iff_not_isCoprime_mod` — **the structural bridge**: `p ∣ Res(Φ_n, V)` iff
  `Φ_n` and `V` are non-coprime mod `p` (rank-drop of the obstruction/Sylvester matrix ⇔
  resultant vanishes mod `p`).
* `floorRealizable_dvd_resultant` — **the necessary condition, machine-proven**: if `A` is
  realizable at `p` then `p ∣ Res(Φ_n, V_A)`.  This is the previously only-computed step.
* `floorBad_forces_pmin_16` / `floorBad_forces_pmin_32` — the concrete decided rungs: given the
  *computed* obstruction-norm identity `Res(Φ_n, V_A) = R_n` (`R_16 = 2312`, `R_32 = 602176`),
  realizability at `p ≡ 1 mod n` forces `p = p_min(n)` (`17`, `97`).  The resultant *value* is a
  named hypothesis (computed in the probe, not evaluated in Lean — a degree-`φ(2^k)` Sylvester
  determinant); the *divisibility* step `realizable ⟹ p ∣ Res` is now fully machine-proven.
* `exists_isPrimitiveRoot_of_modEq_one` — the primitive-root supply making the regime
  `p ≡ 1 mod n` non-vacuous (reproduced locally, cf. the width-four lane).

## Honesty

`realizable ⟹ p ∣ Res(Φ_n, V_A)` and `p ∣ Res ⇔ non-coprime mod p` are **proven here**
(axiom-clean, only `propext, Classical.choice, Quot.sound`).  The numeric resultant *identities*
`Res(Φ_16, V_A) = 2312`, `Res(Φ_32, V_A) = 602176`, and the identification of `V_A` with the
concrete obstruction coefficient, remain **computed** in `probe_466_successor_norm.py`, not
Lean-evaluated; they enter as explicitly named hypotheses `hres`.  This upgrades the round-8 germ
`_FloorSuccessorNorm.floorObstructionNorm_forces_pmin_16` (bare `p ∣ 2312 ⇒ p = 17`) to the full
chain `realizable ⇒ p ∣ Res ⇒ [Res = 2312 computed] ⇒ p ∣ 2312 ⇒ p = 17`, with the
resultant-divisibility link now machine-checked rather than asserted.
-/

open Polynomial

namespace ArkLib.ProximityGap.Frontier.FloorSuccessorResultantBridge

set_option autoImplicit false
set_option linter.style.longLine false

/-- **The char-`p` floor-successor realizability predicate.**  A pattern with `ℤ[X]` obstruction
representative `V` is realizable over `𝔽_p` when some primitive `n`-th root `ζ` of `ZMod p` is a
common root of `V` and `Φ_n` mod `p` — i.e. the obstruction (Sylvester) matrix drops rank. -/
def FloorRealizableAt (n p : ℕ) (V : ℤ[X]) : Prop :=
  ∃ ζ : ZMod p, IsPrimitiveRoot ζ n ∧ (V.map (Int.castRingHom (ZMod p))).eval ζ = 0

/-- **The structural bridge: rank-drop ⇔ resultant vanishing mod `p`.**  The prime `p` divides the
integer cyclotomic resultant `Res(Φ_n, V)` iff `Φ_n` and `V`, reduced mod `p`, fail to be coprime
(the obstruction/Sylvester matrix is singular mod `p`).  This is the resultant reformulation of
"the obstruction matrix drops rank mod `p`". -/
theorem prime_dvd_resultant_iff_not_isCoprime_mod {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    (V : ℤ[X]) (hVdeg : (V.map (Int.castRingHom (ZMod p))).natDegree = V.natDegree) :
    (p : ℤ) ∣ resultant (cyclotomic n ℤ) V (cyclotomic n ℤ).natDegree V.natDegree
      ↔ ¬ IsCoprime (cyclotomic n (ZMod p)) (V.map (Int.castRingHom (ZMod p))) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  set R : ℤ := resultant (cyclotomic n ℤ) V (cyclotomic n ℤ).natDegree V.natDegree with hR
  have hdeg : (cyclotomic n ℤ).natDegree = (cyclotomic n (ZMod p)).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
  -- `R mod p` is the resultant of the reduced polynomials
  have hmap : ((R : ℤ) : ZMod p)
      = resultant (cyclotomic n (ZMod p)) (V.map (Int.castRingHom (ZMod p)))
          (cyclotomic n ℤ).natDegree V.natDegree := by
    rw [hR, ← map_cyclotomic_int n (ZMod p)]
    exact (resultant_map_map (f := cyclotomic n ℤ) (g := V)
      (m := (cyclotomic n ℤ).natDegree) (n := V.natDegree) (Int.castRingHom (ZMod p))).symm
  have hmap0 : ((R : ℤ) : ZMod p)
      = resultant (cyclotomic n (ZMod p)) (V.map (Int.castRingHom (ZMod p))) := by
    rw [hmap, hdeg, ← hVdeg]
  -- assemble: `p ∣ R ⇔ R ≡ 0 ⇔ resultant reduced = 0 ⇔ not coprime`
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd R p, hmap0, resultant_eq_zero_iff]
  have hcyc_ne : cyclotomic n (ZMod p) ≠ 0 := cyclotomic_ne_zero n (ZMod p)
  simp only [ne_eq, hcyc_ne, not_false_eq_true, true_or, true_and]

/-- **The floor-successor necessary condition, machine-proven.**  If a pattern with obstruction
representative `V` is realizable at `p` (`p ≡ 1 mod n` supplying the primitive root), then `p`
divides the integer obstruction norm `Res(Φ_n, V)`.  This is the previously only-*computed*
"floor-bad ⟹ `p ∣ N(A)`" step, now an instance of the cyclotomic-resultant bridge. -/
theorem floorRealizable_dvd_resultant {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] {V : ℤ[X]}
    (hVdeg : (V.map (Int.castRingHom (ZMod p))).natDegree = V.natDegree)
    (hreal : FloorRealizableAt n p V) :
    (p : ℤ) ∣ resultant (cyclotomic n ℤ) V (cyclotomic n ℤ).natDegree V.natDegree := by
  obtain ⟨ζ, hζ, hζ0⟩ := hreal
  exact dvd_resultant_of_isPrimitiveRoot_isRoot hn V hVdeg hζ hζ0

/-- Natural-number form of the necessary condition: realizability forces `p ∣ |Res(Φ_n, V)|`. -/
theorem floorRealizable_dvd_natAbs_resultant {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    {V : ℤ[X]} (hVdeg : (V.map (Int.castRingHom (ZMod p))).natDegree = V.natDegree)
    (hreal : FloorRealizableAt n p V) :
    p ∣ (resultant (cyclotomic n ℤ) V (cyclotomic n ℤ).natDegree V.natDegree).natAbs := by
  have h := floorRealizable_dvd_resultant hn hVdeg hreal
  simpa using Int.natAbs_dvd_natAbs.mpr h

/-! ## The concrete decided rungs `n = 16, 32`

The obstruction-norm *values* `Res(Φ_16, V_A) = 2312`, `Res(Φ_32, V_A) = 602176` are computed in
`probe_466_successor_norm.py` (exact `ℤ[ζ_n]` arithmetic) and enter as the named hypothesis
`hres`.  Everything else — the divisibility bridge and the arithmetic pin — is machine-proven. -/

/-- **`n = 16` concrete rung.**  Given the computed obstruction-norm identity
`Res(Φ_16, V_A) = 2312 = 2^3·17^2`, any pattern realizable at a prime `p ≡ 1 mod 16` has
`p = 17 = p_min(16)`.  The resultant *value* is the named computed input `hres`; the chain
`realizable ⇒ p ∣ Res ⇒ p ∣ 2312 ⇒ p = 17` is machine-proven. -/
theorem floorBad_forces_pmin_16 {p : ℕ} [Fact p.Prime] {V : ℤ[X]}
    (hmod : p % 16 = 1)
    (hVdeg : (V.map (Int.castRingHom (ZMod p))).natDegree = V.natDegree)
    (hres : resultant (cyclotomic 16 ℤ) V (cyclotomic 16 ℤ).natDegree V.natDegree = 2312)
    (hreal : FloorRealizableAt 16 p V) :
    p = 17 := by
  have hp : p.Prime := Fact.out
  have hdvdZ := floorRealizable_dvd_resultant (by norm_num) hVdeg hreal
  rw [hres] at hdvdZ
  -- `(p : ℤ) ∣ 2312` ⟹ `p ∣ 2312`
  have hdvd : p ∣ 2312 := by
    have : (p : ℤ) ∣ ((2312 : ℕ) : ℤ) := by exact_mod_cast hdvdZ
    exact_mod_cast this
  -- arithmetic pin: prime `≡ 1 mod 16` dividing `2^3·17^2` is `17`
  have hfac : (2312 : ℕ) = 2 ^ 3 * 17 ^ 2 := by norm_num
  rw [hfac] at hdvd
  rcases (hp.dvd_mul).mp hdvd with h2 | h17
  · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    omega
  · have hp17 : p ∣ 17 := hp.dvd_of_dvd_pow h17
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp17

/-- **`n = 32` concrete rung.**  Given the computed obstruction gcd-norm identity
`Res(Φ_32, V_A) = 602176 = 2^6·97^2`, any pattern realizable at a prime `p ≡ 1 mod 32` has
`p = 97 = p_min(32)`.  (The off-regime `31 ≡ −1 mod 32` factor has already been stripped by the
gcd across the three obstruction indices; see `_FloorSuccessorNorm`.) -/
theorem floorBad_forces_pmin_32 {p : ℕ} [Fact p.Prime] {V : ℤ[X]}
    (hmod : p % 32 = 1)
    (hVdeg : (V.map (Int.castRingHom (ZMod p))).natDegree = V.natDegree)
    (hres : resultant (cyclotomic 32 ℤ) V (cyclotomic 32 ℤ).natDegree V.natDegree = 602176)
    (hreal : FloorRealizableAt 32 p V) :
    p = 97 := by
  have hp : p.Prime := Fact.out
  have hdvdZ := floorRealizable_dvd_resultant (by norm_num) hVdeg hreal
  rw [hres] at hdvdZ
  have hdvd : p ∣ 602176 := by
    have : (p : ℤ) ∣ ((602176 : ℕ) : ℤ) := by exact_mod_cast hdvdZ
    exact_mod_cast this
  have hfac : (602176 : ℕ) = 2 ^ 6 * 97 ^ 2 := by norm_num
  rw [hfac] at hdvd
  rcases (hp.dvd_mul).mp hdvd with h2 | h97
  · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    omega
  · have hp97 : p ∣ 97 := hp.dvd_of_dvd_pow h97
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp97

/-! ## Non-vacuity: the primitive-root supply -/

/-- A prime `p ≡ 1 (mod n)` carries an element of multiplicative order `n` in `𝔽_p`, so the
realizability regime is non-vacuous.  (`(ZMod p)ˣ` is cyclic of order `p − 1`, and `n ∣ p − 1`.)
Reproduced locally from the width-four lane (`CanonicalWidthFourBadPrimeSet`). -/
theorem exists_isPrimitiveRoot_of_modEq_one {p : ℕ} [Fact p.Prime] {n : ℕ} (_hn : 0 < n)
    (hmod : p ≡ 1 [MOD n]) : ∃ ζ : ZMod p, IsPrimitiveRoot ζ n := by
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hdvd : n ∣ p - 1 := (Nat.modEq_iff_dvd' hp1).mp hmod.symm
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf u = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units]
  have hdvd' : n ∣ orderOf u := hord ▸ hdvd
  have hne : orderOf u ≠ 0 := (orderOf_pos u).ne'
  refine ⟨((u ^ (orderOf u / n) : (ZMod p)ˣ) : ZMod p), ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, orderOf_pow_orderOf_div hne hdvd']

end ArkLib.ProximityGap.Frontier.FloorSuccessorResultantBridge

/-! ## Axiom audit -/

namespace ArkLib.ProximityGap.Frontier.FloorSuccessorResultantBridge

#print axioms prime_dvd_resultant_iff_not_isCoprime_mod
#print axioms floorRealizable_dvd_resultant
#print axioms floorRealizable_dvd_natAbs_resultant
#print axioms floorBad_forces_pmin_16
#print axioms floorBad_forces_pmin_32
#print axioms exists_isPrimitiveRoot_of_modEq_one

end ArkLib.ProximityGap.Frontier.FloorSuccessorResultantBridge
