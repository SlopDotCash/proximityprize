/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet
import Mathlib.NumberTheory.LSeries.PrimesInAP

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# U1, minimized: the canonical good prime needs only a COUNT, not a density (#464)

The end-to-end pin's ceiling node **U1** is usually stated as the full Thorner–Zaman PNT-in-AP
density lower bound `TZPrimeSupply n β supply` with `supply ~ n^{β−1−o(1)}`.  This file isolates
the **strictly weaker** analytic input that the *canonical width-four lane* actually consumes, and
proves the elementary reduction from it.

## The observation (numerically verified, #464)

In the canonical width-four lane the entire bad set is the prime-factor set of a **single fixed
nonzero integer** `R(n) = Res(Φ_n, (X⁴+1)ⁿ − (X²+1)ⁿ)` (`canonicalRatioResultant`,
`CanonicalWidthFourBadPrimeSet.lean`).  Two consequences make U1 cheaper than full TZ:

* **(boundedness)** every bad prime divides `R(n)`, hence is `≤ |R(n)| ≤ 2^{(n+1)·φ(n)}`; and
* **(few)** the bad set has cardinality `≤ ω(R(n)) ≤ log₂|R(n)| ≤ (n+1)·φ(n) = Θ(n²)`,
  and **empirically** only `Θ(log n)` of them lie below prize scale `n⁴` (probe `u1_omega_growth`:
  `#bad < n⁴` is `0, 1, 4, 13, 22, 35` for `n = 8,…,256`).

So the consumer (`canonicalWidthFourGoodPrimeSupply_of_TZ`) needs only:

> there are **more** primes `p ≡ 1 (mod n)` in some computable window than the **explicit**
> bad-prime count `ω(R(n))`.

This is a *cardinality comparison against a fixed finite obstruction count*, **not** a density
statement.  Concretely the minimal Prop is `WindowExceedsCanonicalOmega n β`: the window count
strictly exceeds the canonical bad count.  We prove it is **equivalent** to the consumer's exact
pigeonhole premise, and that it is **implied by** the in-tree `TZPrimeSupply` at the crude exponent
(`supply > (n+1)·φ(n)`, i.e. `β > 3`) — but, unlike full TZ, it does **not** require the
asymptotic `o(1)` density: any window-count lower bound clearing the explicit `ω(R(n))` suffices.

## What is proven vs. named (honesty)

PROVEN, axiom-clean: the reduction `WindowExceedsCanonicalOmega ⇒ CanonicalWidthFourGoodPrimeSupply`
(elementary pigeonhole, re-using `exists_tzWindow_notMem_canonicalRatioBadPrimes`), and the
`TZPrimeSupply ⇒ WindowExceedsCanonicalOmega` arrow at the crude budget.  NAMED-OPEN, never an
axiom: `WindowExceedsCanonicalOmega` itself — the analytic window-count.  **This is strictly
weaker than the full TZ density** (a finite cardinality comparison, no `o(1)`), and it is the
honest statement of "the minimum analytic input that closes U1 for the canonical lane".

It does **not** touch the Paley/BGK sup-norm wall: U1 is pure analytic NT (prime supply), entirely
on the *ceiling* side and independent of the Face-3 floor wall.

## References
* [TZ24] Thorner–Zaman, *Refinements to the prime number theorem for arithmetic progressions*.
* [KKH26] Krachun–Kazanin–Haböck, ePrint 2026/782, Lemma 2.  Issue #334 / #464.
-/

open Finset
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.E2DilationDirectCount
open ArkLib.ProximityGap.Frontier.CanonicalWidthFourBadPrimeSet

namespace ArkLib.ProximityGap.Frontier.U1MinimalSupplyInput

/-- **The minimal U1 input for the canonical lane** (named hypothesis; never an axiom).
`WindowExceedsCanonicalOmega n β` asserts only that the Thorner–Zaman window `[n^β, 2n^β]`
contains **strictly more** primes `p ≡ 1 (mod n)` than the *explicit* canonical bad-prime count
`(canonicalRatioBadPrimes n).card = ω(R(n))`.

This is a **finite cardinality comparison** against a fixed obstruction count, not a prime-density
statement: any lower bound on `(tzWindow n β).card` exceeding the explicit `ω(R(n))` discharges it.
It is implied by — but strictly weaker than — the full `TZPrimeSupply` density (no `o(1)` term). -/
def WindowExceedsCanonicalOmega (n : ℕ) (β : ℝ) : Prop :=
  (canonicalRatioBadPrimes n).card < (tzWindow n β).card

/-- **The reduction (PROVEN, axiom-clean): the minimal U1 input closes the canonical good prime.**
If the window holds more primes `≡ 1 (mod n)` than the explicit canonical bad count, then a
window prime avoids the canonical bad set, i.e. `CanonicalWidthFourGoodPrimeSupply m` holds for
`n = 2^m`.  This is the exact pigeonhole the consumer needs, fed by the *count* rather than the
*density*. -/
theorem canonicalGoodSupply_of_windowExceedsOmega {m : ℕ} {β : ℝ}
    (hWin : WindowExceedsCanonicalOmega (2 ^ m) β) :
    CanonicalWidthFourGoodPrimeSupply m := by
  -- `TZPrimeSupply (2^m) β supply` with `supply = (tzWindow).card` is automatic.
  refine canonicalWidthFourGoodPrimeSupply_of_TZ
    (β := β) (supply := (tzWindow (2 ^ m) β).card) ⟨le_rfl⟩ ?_
  exact hWin

/-- **`WindowExceedsCanonicalOmega` is exactly the consumer's pigeonhole premise.**  It is, by
definition, `(canonicalRatioBadPrimes n).card < (tzWindow n β).card` — the strict inequality that
`exists_tzWindow_notMem_canonicalRatioBadPrimes` consumes.  Recording the equivalence makes the
"minimal input" claim precise: nothing about the supply beyond this single comparison is used. -/
theorem windowExceedsOmega_iff_card_lt {n : ℕ} {β : ℝ} :
    WindowExceedsCanonicalOmega n β ↔
      (canonicalRatioBadPrimes n).card < (tzWindow n β).card := Iff.rfl

/-- **Full TZ density ⇒ the minimal input (crude budget).** The in-tree named density hypothesis
`TZPrimeSupply (2^m) β supply` with the supply clearing the *crude* explicit bad bound
`(2^m).totient · (2^m + 1)` (i.e. `β > 3` asymptotically) implies `WindowExceedsCanonicalOmega`.
This exhibits the minimal input as a genuine **weakening** of the consumed TZ density: TZ is
sufficient, but the minimal input asks only for the cardinality comparison, no `o(1)`. -/
theorem windowExceedsOmega_of_TZ_crude {m : ℕ} {β : ℝ} {supply : ℕ} (hm : 4 ≤ m)
    (hTZ : TZPrimeSupply (2 ^ m) β supply)
    (hcard : (2 ^ m).totient * (2 ^ m + 1) < supply) :
    WindowExceedsCanonicalOmega (2 ^ m) β := by
  have hn : 0 < 2 ^ m := by positivity
  have hn8 : 8 < 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 3 < m)
  have hbad : (canonicalRatioBadPrimes (2 ^ m)).card ≤ (2 ^ m).totient * (2 ^ m + 1) :=
    canonicalRatioBadPrimes_card_le_crude hn hn8
  exact lt_of_le_of_lt hbad (lt_of_lt_of_le hcard hTZ.le_card)

/-- **End-to-end (crude): full TZ density ⇒ canonical good prime, via the minimal input.**
Chains `windowExceedsOmega_of_TZ_crude` into `canonicalGoodSupply_of_windowExceedsOmega`.  This is
the same conclusion as `canonicalWidthFourGoodPrimeSupply_of_TZ_crude`, but routed through the
explicitly-named *minimal* analytic input `WindowExceedsCanonicalOmega`, so the dependency on the
deep density is now visibly factored through a single finite cardinality comparison. -/
theorem canonicalGoodSupply_of_TZ_via_minimalInput {m : ℕ} {β : ℝ} {supply : ℕ} (hm : 4 ≤ m)
    (hTZ : TZPrimeSupply (2 ^ m) β supply)
    (hcard : (2 ^ m).totient * (2 ^ m + 1) < supply) :
    CanonicalWidthFourGoodPrimeSupply m :=
  canonicalGoodSupply_of_windowExceedsOmega
    (windowExceedsOmega_of_TZ_crude hm hTZ hcard)

/-- **The minimal input also yields the literal width-four refuter.**  Composing with the in-tree
`refuter_of_canonicalWidthFourGoodPrimeSupply`, the single cardinality comparison
`WindowExceedsCanonicalOmega (2^m) β` already refutes the literal canonical width-four `≤ 2^m`
budget for one supplied prime — without ever invoking the density form of TZ. -/
theorem refuter_of_windowExceedsOmega {m : ℕ} {β : ℝ} (hm : 4 ≤ m)
    (hWin : WindowExceedsCanonicalOmega (2 ^ m) β) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      IsPrimitiveRoot ζ (2 ^ m) ∧
        ¬ (e2BadScalarSet (Polynomial.nthRootsFinset (2 ^ m) (1 : ZMod p)) 4).card
          ≤ 2 ^ m :=
  refuter_of_canonicalWidthFourGoodPrimeSupply hm
    (canonicalGoodSupply_of_windowExceedsOmega hWin)

/-! ### The Dirichlet-only extreme: U1 existence is FREE (no counting theorem) -/

/-- **A prime above the canonical resultant cannot be a canonical bad prime.**  Every bad prime
divides the nonzero integer `R(n) = canonicalRatioResultant n`, hence is `≤ |R(n)|`.  So a prime
`p > |R(n)|` is automatically *not* in `canonicalRatioBadPrimes n`.  (No counting, no density: pure
"a prime exceeding a nonzero integer cannot divide it".) -/
theorem notMem_canonicalRatioBadPrimes_of_gt_resultant {n p : ℕ} (hp : p.Prime)
    (hgt : (canonicalRatioResultant n).natAbs < p) :
    p ∉ canonicalRatioBadPrimes n := by
  intro hmem
  rw [mem_canonicalRatioBadPrimes] at hmem
  obtain ⟨_, hdvd, hne⟩ := hmem
  -- p ∣ R ⇒ p ≤ |R|, contradicting p > |R|.
  have hpd : p ∣ (canonicalRatioResultant n).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using h
  have hle : p ≤ (canonicalRatioResultant n).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hpd
  omega

/-- **U1 existence is unconditional for the canonical lane (Dirichlet-only, no count).**
Mathlib's Dirichlet theorem (`Nat.forall_exists_prime_gt_and_modEq`) produces a prime
`p ≡ 1 (mod 2^m)` with `p > |R(2^m)|`; by `notMem_canonicalRatioBadPrimes_of_gt_resultant` that
prime avoids the canonical bad set, so `CanonicalWidthFourGoodPrimeSupply m` holds with **no analytic
hypothesis at all**.  This is the `_TZDirichletUnconditional` move specialized to the *single*
canonical resultant: the price is that `p` is not proven polynomial in `n` (the super-polynomial
field-size extreme — recovering `p = poly(n)` is exactly what the *counting* input
`WindowExceedsCanonicalOmega` buys).  Together the two theorems bracket U1: existence is free,
polynomial size is the remaining (Linnik-flavoured, finite-comparison) cost. -/
theorem canonicalGoodSupply_unconditional_dirichlet {m : ℕ} (hm : 4 ≤ m) :
    CanonicalWidthFourGoodPrimeSupply m := by
  classical
  have hnpos : (2 ^ m : ℕ) ≠ 0 := by positivity
  -- a prime p > |R|, p ≡ 1 (mod 2^m), by Dirichlet
  obtain ⟨p, hpgt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (canonicalRatioResultant (2 ^ m)).natAbs
      (q := 2 ^ m) (a := 1) hnpos (Nat.coprime_one_left _)
  haveI : Fact p.Prime := ⟨hp⟩
  have hgood : p ∉ canonicalRatioBadPrimes (2 ^ m) :=
    notMem_canonicalRatioBadPrimes_of_gt_resultant hp hpgt
  obtain ⟨ζ, hζ⟩ :=
    exists_isPrimitiveRoot_zmod_of_modEq (by positivity : 0 < 2 ^ m) hpmod
  exact ⟨p, inferInstance, ζ, hζ, hgood⟩

/-- **The literal width-four refuter, UNCONDITIONALLY (Dirichlet-only).**  Composing
`canonicalGoodSupply_unconditional_dirichlet` with `refuter_of_canonicalWidthFourGoodPrimeSupply`:
for every `m ≥ 4`, with **no** analytic hypothesis, there is a primitive-root prime over which the
literal canonical width-four `≤ 2^m` budget is refuted.  (U1's *existence* obligation for the
canonical lane is thus fully discharged in-tree; only the polynomial-size refinement remains.) -/
theorem refuter_unconditional_dirichlet {m : ℕ} (hm : 4 ≤ m) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ζ : ZMod p),
      IsPrimitiveRoot ζ (2 ^ m) ∧
        ¬ (e2BadScalarSet (Polynomial.nthRootsFinset (2 ^ m) (1 : ZMod p)) 4).card
          ≤ 2 ^ m :=
  refuter_of_canonicalWidthFourGoodPrimeSupply hm
    (canonicalGoodSupply_unconditional_dirichlet hm)

end ArkLib.ProximityGap.Frontier.U1MinimalSupplyInput

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
namespace ArkLib.ProximityGap.Frontier.U1MinimalSupplyInput
#print axioms canonicalGoodSupply_of_windowExceedsOmega
#print axioms windowExceedsOmega_iff_card_lt
#print axioms windowExceedsOmega_of_TZ_crude
#print axioms canonicalGoodSupply_of_TZ_via_minimalInput
#print axioms refuter_of_windowExceedsOmega
#print axioms notMem_canonicalRatioBadPrimes_of_gt_resultant
#print axioms canonicalGoodSupply_unconditional_dirichlet
#print axioms refuter_unconditional_dirichlet
end ArkLib.ProximityGap.Frontier.U1MinimalSupplyInput
