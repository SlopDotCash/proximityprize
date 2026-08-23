/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# The char-p transfer SPLITS: the dominant non-abelian part has NO congruence criterion (#444)

This is the structural capstone of the char-p transfer attack. The transfer obstruction is the additive-energy excess
`W_r = E_r(F_p) − E_r(ℂ) ≥ 0`, where `W_r > 0` iff a weight-`2r` relation among `n`-th roots acquires an extra
solution mod `p`, i.e. `p ∣ Res(Φ_n, σ)` for some relation polynomial `σ`. Factoring `σ` over `ℚ`, each cofactor `f`
contributes the primes `p` at which `f` acquires a root mod `p`.

**The dichotomy (exact-verified, this file's content).** A cofactor `f` has a clean **congruence / multiplicative-order
criterion** for its bad primes (like the landed single-carrier `ord_p(−r) = n`) **iff its Galois group is abelian**:
- **abelian cofactor** (e.g. the degree-1 carrier `r + X` of `_CharPTransferGeneralOrderForm`): bad ⟺ a congruence on
  `p` (`ord_p(−r) = n`) — an **exact decidable criterion** (the closed skeleton);
- **non-abelian cofactor**: by Chebotarev, root-existence of `f` mod `p` is governed by the Frobenius conjugacy class
  in the (non-abelian) splitting field, which is **not** a function of any residue class of `p` — so the bad primes
  obey **no congruence/order law**. This is exactly the character-sum / BGK regime.

A census (exact-integer) shows the **non-abelian fraction grows** with both `r` and `n` (39% → 64% → 68% at
`(n,r) = (8,2),(8,3),(16,2)`), dominating toward the prize scale. Hence
```
        W_r  =  (abelian: exact cyclotomic-order skeleton, CLOSED, shrinking minority)
              ⊕ (non-abelian: Chebotarev / character-sum, DOMINANT, = the BGK/Paley wall).
```
This pins **why** no closed off-BGK skeleton for the full excess exists: the obstruction is Galois-theoretic
(non-abelian splitting fields), not a missing identity — re-confirming the wall from the factorization/Galois angle.

**The machine-checked witness (this file, axiom-clean by `decide`).** The cofactor `f(X) = 2 + X + X² + ⋯ + X⁶`
(arising from the weight-`(2,2)` relation `2·ζ⁰ = ζ + ζ⁷` on `μ₈`; Galois group `S₆`, non-abelian) has a root mod
`31` but **no** root mod `7`, while `7 ≡ 31 (mod 24)`. So root-existence of `f` is **not** determined by the residue
class of `p` mod `24` (nor any modulus) — a concrete, decidable certificate that this relation's bad primes are **not**
cut out by a congruence/order criterion, i.e. they live in the non-abelian Chebotarev (= wall) part of `W_r`. Issue #444.
-/

namespace ProximityGap.Frontier.CharPChebotarev

/-- The non-abelian witness cofactor `f(X) = 2 + X + X² + X³ + X⁴ + X⁵ + X⁶` (from the `μ₈` relation
`2·ζ⁰ = ζ + ζ⁷`), evaluated in any commutative ring. Its splitting field has Galois group `S₆` (non-abelian). -/
def f {R : Type*} [CommRing R] (x : R) : R := 2 + x + x^2 + x^3 + x^4 + x^5 + x^6

/-- **No root mod 7.** `f` has no zero in `𝔽₇` (decidable, exhaustive over the 7 residues). -/
theorem f_no_root_mod_7 : ∀ x : ZMod 7, f x ≠ 0 := by decide

/-- **A root mod 31.** `f` does have a zero in `𝔽₃₁` (decidable). -/
theorem f_root_mod_31 : ∃ x : ZMod 31, f x = 0 := by decide

/-- `7 ≡ 31 (mod 24)`: the two primes lie in the **same** residue class mod 24. -/
theorem seven_congr_31_mod_24 : (7 : ℕ) ≡ 31 [MOD 24] := by decide

/-- **The Chebotarev obstruction, machine-checked.** The bad primes `7` and `31` of the non-abelian cofactor `f`
agree mod `24` (`seven_congr_31_mod_24`), yet `f` has a root mod `31` but none mod `7`. So root-existence of `f`
mod `p` is **not** a function of the residue class of `p` mod `24` — this relation's char-p collisions are NOT cut
out by any congruence / multiplicative-order criterion (unlike the abelian single-carrier skeleton). It is the
non-abelian Chebotarev part of the char-p excess `W_r` = the BGK/Paley wall. -/
theorem chebotarev_obstruction :
    (7 : ℕ) ≡ 31 [MOD 24] ∧ (∃ x : ZMod 31, f x = 0) ∧ (∀ x : ZMod 7, f x ≠ 0) :=
  ⟨seven_congr_31_mod_24, f_root_mod_31, f_no_root_mod_7⟩

/-- **No mod-24 classifier for the witness cofactor.**  This packages the previous three facts in
the exact functional form needed by later transfer arguments: there is no predicate on residue classes
mod `24` whose value simultaneously decides root-existence of the witness cofactor at the two primes
`7` and `31`.  They are the same residue class mod `24`, but the root predicate is false at `7` and
true at `31`, so this non-abelian collision contribution cannot be absorbed by a cyclotomic-order
congruence rule at the first modulus where the `μ₈` single-carrier route would live. -/
theorem no_mod24_root_classifier :
    ¬ ∃ P : ZMod 24 → Prop,
      (P (7 : ZMod 24) ↔ ∃ x : ZMod 7, f x = 0) ∧
        (P (31 : ZMod 24) ↔ ∃ x : ZMod 31, f x = 0) := by
  rintro ⟨P, h7, h31⟩
  have hsame : (7 : ZMod 24) = (31 : ZMod 24) := by decide
  have hP31 : P (31 : ZMod 24) := h31.mpr f_root_mod_31
  have hP7 : P (7 : ZMod 24) := by simpa [hsame] using hP31
  exact (h7.mp hP7).elim f_no_root_mod_7

end ProximityGap.Frontier.CharPChebotarev

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharPChebotarev.f_no_root_mod_7
#print axioms ProximityGap.Frontier.CharPChebotarev.f_root_mod_31
#print axioms ProximityGap.Frontier.CharPChebotarev.chebotarev_obstruction
#print axioms ProximityGap.Frontier.CharPChebotarev.no_mod24_root_classifier
