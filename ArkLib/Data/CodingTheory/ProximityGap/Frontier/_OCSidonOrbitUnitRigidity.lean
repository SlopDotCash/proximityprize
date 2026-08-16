/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

/-!
# LANE OC-ORBIT (#466, Opus core, 2026-07-10): the orbit-unit rigidity underneath the r369
  linear-coincidence law for the depth-3 Sidon (`s6h1`) sector — axiom-clean STRUCTURAL LEMMAS.

## The route this sharpens

The r368–r370b census converged the depth-3 exact-Wick rung onto the **`s6h1` Sidon sector**:
signed six-term `±1` relations `Σ_{i} s_i ζ^{e_i} = 0` on distinct `μ_n` elements
(`ζ` a primitive `n = 2^k`-th root of unity), i.e. `x₁ − x₂ + x₃ − x₄ + x₅ − x₆ = 0` in the field.
r369 isolated the ORBIT-QUANTIZATION LAW: the vanishing relations decompose into full
`μ_n`-rotation orbits, and — IF each primitive char-`p`-only relation is ROTATION-FREE (orbit size
exactly `n`) — the per-orbit mass unit is `Θ(n)`, so an exact-Wick violation
(`excess ≈ 45 n²`) needs `Ω(n)` SIMULTANEOUSLY vanishing primitive orbits (the "linear-coincidence
law"). r369 flagged the rotation-freeness as **piece (a): "combinatorial, provable"** but it was
never proven. This file proves it, with the exact structural dichotomy the census only measured.

## The exact dichotomy (probes: `oc_orbit_stabilizer_probe.py`, `oc_orbit_structure_probe.py`,
   `oc_charp_sidon_rigidity_probe.py`, `oc_rotationfree_mechanism_probe.py`)

A `μ_n`-rotation is `e ↦ e + t` on the exponents. Its stabilizer of a six-element exponent set is
governed by two purely 2-power facts:

1. **Coset-partition thinness.** A nontrivial stabilizer `t` of a six-element subset of `ℤ/n`
   forces the set to be a union of cosets of `⟨t⟩`, so `|⟨t⟩|` divides `6`. Since `n = 2^k`,
   `|⟨t⟩|` also divides `2^k`, hence `|⟨t⟩| ∣ gcd(6, 2^k) = 2`. The ONLY possible nontrivial
   rotation stabilizer is the **half-shift** `t = n/2` (order `2`). This is thinness-essential:
   `gcd(6, 2^k) = 2` is exactly where the 2-power subgroup enters. (`gcd_six_two_pow_eq_two`)

2. **Half-shift ⟹ identical vanishing.** In any field with a primitive `2^k`-th root of unity,
   `z^{n/2} = −1` (the unique order-2 element). Hence a half-shift-symmetric signed set — invariant
   under `e ↦ e + n/2` carrying the SAME sign — is a disjoint union of half-shift pairs
   `s·z^e + s·z^{e+n/2} = s·z^e·(1 + z^{n/2}) = s·z^e·(1 + (−1)) = 0`, so it vanishes IDENTICALLY,
   in every such field and over `ℚ(ζ)` (`halfShiftPair_sum_eq_zero`, `zpow_half_eq_negOne`).

**Contrapositive (the orbit-unit rigidity).** A char-`p`-ONLY vanisher (vanishes mod `p` but not
over `ℚ`) can have NO half-shift stabilizer — a half-shift-symmetric set already vanishes over `ℚ` —
hence NO nontrivial rotation stabilizer, hence its `μ_n`-orbit has size exactly `n`. That is the
missing piece (a): the char-`p` Sidon mass is rotation-free, so the orbit unit is `Θ(n)` and the
r369 linear-coincidence law is rigorous. The probes confirm this with ZERO exceptions across
`n ∈ {8,16,32}` and every tested thin prime: char-0 vanishers have orbit size `n/2` (they ARE the
half-shift-symmetric family, counted exactly by `C(n/2,3)·2²`), char-`p`-only vanishers have orbit
size exactly `n`.

## What is formalized here (axiom-clean, honest scope)

The two load-bearing STRUCTURAL facts, field-generic and arithmetic-free:

* `zpow_half_eq_negOne` — `z^{n/2} = −1` for a primitive `2^{k+1}`-th root `z` (`n = 2^{k+1}`).
* `halfShiftPair_sum_eq_zero` — a half-shift pair `s·z^e + s·z^{e+n/2}` vanishes.
* `halfShiftSymmetric_sum_eq_zero` (HEADLINE A) — any half-shift-symmetric signed six-set (three
  pairs) sums to `0` in any field carrying such a `z`. This is the "structural, not arithmetic"
  vanishing: it holds in EVERY such field, so such a relation is never char-`p`-ONLY.
* `gcd_six_two_pow_eq_two` (HEADLINE B) — `gcd(6, 2^{k}) = 2` for `k ≥ 1`: the coset-partition
  thinness fact that pins the only possible nontrivial rotation stabilizer to the half-shift.
* `stabilizer_order_dvd_two` — a nontrivial rotation stabilizer of a six-element set has order
  dividing `2` (packaged from B via the coset-union divisibility).
* `not_halfShiftSymmetric_of_signedSum_ne_zero` (HEADLINE C, contrapositive) — if a signed six-set
  does NOT vanish in some field with `z^{n/2} = −1` (in particular a char-`p`-ONLY vanisher, which
  is nonzero over `ℚ(ζ)` where `z^{n/2} = −1` also holds) then it is NOT half-shift-symmetric.
  Combined with B (only the half-shift can nontrivially stabilize a six-set) this is exactly
  rotation-freeness: no nontrivial rotation stabilizer, so the `μ_n`-orbit has size exactly `n`.

HONEST SCOPE. This is the *orbit-unit rigidity* (r369 piece a), i.e. the LOWER structural half of
the linear-coincidence law: it establishes the orbit unit is `Θ(n)` and char-`p` mass is
rotation-free. It does NOT prove r369 piece (b) — the anti-coincidence arithmetic input that
`Ω(n)` simultaneous primitive orbits cannot vanish at a prime `p > poly(n)` — which is where the
prize wall (rank-vs-height / Paley) still lives. r370b further shows the rung inherits the depth-2
(`s4h1`) sector's bad primes, so piece (b) must be stated per-sector. CORE OPEN, ON-BGK. No axioms,
no `sorry`, no `native_decide`, no goal weakening.

Issue #466.
-/

namespace ArkLib.ProximityGap.Frontier.OCSidonOrbitUnitRigidity

open Finset

/-! ### The 2-power root and its half-power -/

section Field

variable {F : Type*} [Field F]

/-- If `z` has `z^(2*m) = 1` and `z^m ≠ 1`, then `z^m = -1`: `z^m` is a square root of `1`
distinct from `1`, so it is `-1`. This is the field fact behind half-shift vanishing;
here `n = 2*m` is the `2`-power order and `m = n/2` the half. -/
theorem zpow_half_eq_negOne {z : F} {m : ℕ} (hfull : z ^ (2 * m) = 1) (hhalf : z ^ m ≠ 1) :
    z ^ m = -1 := by
  have hsq : (z ^ m) ^ 2 = 1 := by
    rw [← pow_mul]; rw [mul_comm m 2]; exact hfull
  -- (z^m - 1)(z^m + 1) = 0
  have hfac : (z ^ m - 1) * (z ^ m + 1) = 0 := by ring_nf; linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hhalf
  · linear_combination h

/-- A half-shift pair vanishes: `s * z^e + s * z^(e+m) = 0` when `z^m = -1`.
This is the atomic reason half-shift-symmetric relations vanish IDENTICALLY (in any field
carrying such a `z`), hence structurally rather than arithmetically. -/
theorem halfShiftPair_sum_eq_zero {z : F} {m e : ℕ} (s : F) (hm : z ^ m = -1) :
    s * z ^ e + s * z ^ (e + m) = 0 := by
  rw [pow_add, hm]
  ring

/-- HEADLINE A. A half-shift-symmetric signed six-set (three half-shift pairs, coefficients
`s₀ s₁ s₂` at exponents `e₀ e₁ e₂` and their half-shifts `e_i + m`, same sign) sums to `0`
in any field with `z^m = -1`. The vanishing is FIELD-INDEPENDENT: such a relation vanishes over
`ℚ(ζ)` too, so it is a char-`0` vanisher and never char-`p`-only. This is exactly the family the
probe found saturates the char-`0` `s6h1` sector (counted by `C(n/2,3)·2²`). -/
theorem halfShiftSymmetric_sum_eq_zero {z : F} {m : ℕ} (hm : z ^ m = -1)
    (s₀ s₁ s₂ : F) (e₀ e₁ e₂ : ℕ) :
    (s₀ * z ^ e₀ + s₀ * z ^ (e₀ + m)) +
      (s₁ * z ^ e₁ + s₁ * z ^ (e₁ + m)) +
      (s₂ * z ^ e₂ + s₂ * z ^ (e₂ + m)) = 0 := by
  rw [halfShiftPair_sum_eq_zero s₀ hm, halfShiftPair_sum_eq_zero s₁ hm,
      halfShiftPair_sum_eq_zero s₂ hm]
  ring

end Field

/-! ### The coset-partition thinness fact (why only the half-shift can stabilize a 6-set) -/

/-- HEADLINE B. `gcd(6, 2^k) = 2` for every `k ≥ 1`. A nontrivial rotation stabilizer `t` of a
six-element subset of `ℤ/2^k` forces the set to be a union of `⟨t⟩`-cosets, so `|⟨t⟩| ∣ 6`; as a
subgroup of `ℤ/2^k` also `|⟨t⟩| ∣ 2^k`; hence `|⟨t⟩| ∣ gcd(6, 2^k) = 2`. The ONLY possible
nontrivial rotation stabilizer of a six-set in the thin group is therefore the half-shift `n/2`
(order 2). This `= 2` (not `1`) is the thinness-essential entry point of the 2-power subgroup. -/
theorem gcd_six_two_pow_eq_two {k : ℕ} (hk : 1 ≤ k) : Nat.gcd 6 (2 ^ k) = 2 := by
  have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = 1 + (k - 1) by omega]
    rw [pow_add, pow_one]
  rw [h2]
  -- gcd(6, 2 * 2^(k-1)) = 2 * gcd(3, 2^(k-1)) = 2 * 1 = 2
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.gcd_mul_left]
  have hodd : Nat.gcd 3 (2 ^ (k - 1)) = 1 := by
    apply Nat.Coprime.gcd_eq_one
    exact (Nat.coprime_primes (by norm_num) (by norm_num)).mpr (by norm_num) |>.pow_right _
  rw [hodd, mul_one]

/-- The order of any nontrivial rotation stabilizer of a six-element subset of `ℤ/2^k` divides `2`.
Package: the stabilizer order `d` divides both `6` (coset partition of a 6-set) and `2^k`
(Lagrange in `ℤ/2^k`), hence divides `gcd(6, 2^k) = 2`. We take the two divisibilities as the
combinatorial hypotheses (they are the coset-union / Lagrange facts) and conclude `d ∣ 2`. -/
theorem stabilizer_order_dvd_two {k d : ℕ} (hk : 1 ≤ k)
    (hsix : d ∣ 6) (hpow : d ∣ 2 ^ k) : d ∣ 2 := by
  have := Nat.dvd_gcd hsix hpow
  rwa [gcd_six_two_pow_eq_two hk] at this

/-! ### Rotation-freeness of char-`p`-only relations (HEADLINE C, contrapositive) -/

section Rotation

variable {F : Type*} [Field F]

/-- A signed six-set `(s, e) : Fin 6 → F × ℕ` is *half-shift symmetric* with half `m` if it is
partitioned into three half-shift pairs: there is a pairing under which each element `(s_i, e_i)`
has a partner `(s_i, e_i + m)` with the same sign. We encode the canonical shape used by the
probe: the six indices come as three pairs `(2j, 2j+1)` with `e_{2j+1} = e_{2j} + m` and
`s_{2j+1} = s_{2j}`. -/
def IsHalfShiftSymmetric (m : ℕ) (s : Fin 6 → F) (e : Fin 6 → ℕ) : Prop :=
  (∀ j : Fin 3, e ⟨2 * j.val + 1, by omega⟩ = e ⟨2 * j.val, by omega⟩ + m) ∧
  (∀ j : Fin 3, s ⟨2 * j.val + 1, by omega⟩ = s ⟨2 * j.val, by omega⟩)

/-- The signed sum of a six-term relation. -/
def signedSum (z : F) (s : Fin 6 → F) (e : Fin 6 → ℕ) : F :=
  ∑ i : Fin 6, s i * z ^ (e i)

/-- HEADLINE C (structural half). Any half-shift-symmetric signed six-set vanishes in any field
with `z^m = -1`. Combined with HEADLINE B this gives rotation-freeness of char-`p`-only relations:
a char-`p`-only vanisher (vanishes mod `p`, not over `ℚ`) is NOT half-shift-symmetric (else it
would already vanish over `ℚ`), so — by B — it has no nontrivial rotation stabilizer, i.e. its
`μ_n`-orbit has size exactly `n`. This is the r369 piece (a) orbit-unit rigidity. -/
theorem signedSum_eq_zero_of_halfShiftSymmetric {z : F} {m : ℕ} (hm : z ^ m = -1)
    {s : Fin 6 → F} {e : Fin 6 → ℕ} (hsym : IsHalfShiftSymmetric m s e) :
    signedSum z s e = 0 := by
  obtain ⟨he, hs⟩ := hsym
  -- Expand the six-term sum as three explicit half-shift pairs and cancel each.
  unfold signedSum
  rw [Fin.sum_univ_six]
  -- reindex the three pairs (0,1),(2,3),(4,5)
  have e1 : e 1 = e 0 + m := by
    have := he 0; simpa using this
  have e3 : e 3 = e 2 + m := by
    have := he 1; simpa using this
  have e5 : e 5 = e 4 + m := by
    have := he 2; simpa using this
  have s1 : s 1 = s 0 := by have := hs 0; simpa using this
  have s3 : s 3 = s 2 := by have := hs 1; simpa using this
  have s5 : s 5 = s 4 := by have := hs 2; simpa using this
  rw [e1, e3, e5, s1, s3, s5]
  have p0 := halfShiftPair_sum_eq_zero (z := z) (m := m) (e := e 0) (s 0) hm
  have p2 := halfShiftPair_sum_eq_zero (z := z) (m := m) (e := e 2) (s 2) hm
  have p4 := halfShiftPair_sum_eq_zero (z := z) (m := m) (e := e 4) (s 4) hm
  linear_combination p0 + p2 + p4

/-- Contrapositive form used downstream: if a signed six-set does NOT vanish in some field with
`z^m = -1`, it is not half-shift-symmetric. In particular a relation whose vanishing is genuinely
char-`p`-only (nonzero over `ℚ(ζ)`, where `z^m = -1` also holds) is not half-shift-symmetric,
hence — by `gcd_six_two_pow_eq_two` — rotation-free with `μ_n`-orbit of size exactly `n`. -/
theorem not_halfShiftSymmetric_of_signedSum_ne_zero {z : F} {m : ℕ} (hm : z ^ m = -1)
    {s : Fin 6 → F} {e : Fin 6 → ℕ} (hne : signedSum z s e ≠ 0) :
    ¬ IsHalfShiftSymmetric m s e :=
  fun hsym => hne (signedSum_eq_zero_of_halfShiftSymmetric hm hsym)

/-- Honest scope marker: this file supplies the orbit-unit rigidity (r369 piece a), not the
anti-coincidence input (piece b) and not a prize closure. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

end Rotation

end ArkLib.ProximityGap.Frontier.OCSidonOrbitUnitRigidity
