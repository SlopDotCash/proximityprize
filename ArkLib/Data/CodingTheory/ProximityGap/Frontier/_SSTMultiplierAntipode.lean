/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The SST multiplier action fixes the antipode (#466 lane S5)

Successor probe: `scripts/probes/probe_466_sst_multiplier.py`
(output `scripts/probes/_out_466_sst_multiplier.txt`).

## Context (dossier v3 §15, survivor 4)

For the sparse-section transference (SST) picture, `L_p = ker(ℤ[x]/(xⁿ−1) → 𝔽_p, x ↦ h)`
with `h` of exact multiplicative order `n`.  For a `2r`-subset `S ⊆ ℤ/n` the *section* is the
rank-`2r` lattice `L_S(h) = { c ∈ ℤ^S : Σᵢ cᵢ hˢⁱ ≡ 0 (mod p) }`.

* The **shift** `S ↦ S+1` multiplies the defining form by the unit `h`, so `L_{S+1}(h) = L_S(h)`
  up to coordinate sorting — a genuine isometry (proven, `probe_466_sst_sections` part (d)).
* The **multiplier** `S ↦ kS` (`gcd(k,n)=1`) satisfies the EXACT identity
  `L_{kS}(h) = L_S(hᵏ)` — it replaces `h` by the *different* primitive root `hᵏ`, a Galois twist,
  NOT a unit multiple.  So it is **not** an isometry of a fixed `L_p`.

The probe's DECISION (n=16 r=2,3 full; n=32 r=2 full census; two generic primes each, Fermat
`2¹⁶+1` flagged):

* **Dual minimum `λ₁*` is BROKEN by multipliers** — within-affine-orbit `λ₁*` variance is
  nonzero, with explicit countermodel pairs `(S,k)` of equal sparse-count but different
  `p²·λ₁*²`.  So the multiplier is dead as a lattice-geometry compression lever (it does not
  refine the dual-minimum census beyond the shift orbits).  This is the empirical countermodel
  side; lattice minima are not stated in Lean here.
* **Sparse-count IS constant on affine orbits** — an extra factor `φ(n)` of compression over
  the shift census.  The mechanism, and the content of this file, is: in the `n = 2^μ` regime
  every bad section is char-0/antipodal (a `{0,±1}` vanishing sum decomposes into antipodal
  pairs `{s, s+n/2}`), and multiplication by a unit `k` *permutes antipodal pairs*, because it
  **fixes the order-two element `n/2`**.  The reversal `S ↦ −S` seen in round 2 (sparse-count
  equal on all pairs, dual-min equal on only a fraction) is exactly the `k = −1` instance of
  this dichotomy.

## What is PROVEN here (axiom-clean)

* `mul_odd_fixes_half` — for `k` odd, `k · (m) = (m)` in `ZMod (2*m)`: every odd multiplier
  fixes the unique order-two element `m = n/2`.
* `unit_odd` — a natural number coprime to `2*m` is odd (units mod an even modulus are odd),
  so every genuine multiplier `gcd(k,n)=1` (with `n = 2m` even) is odd.
* `mul_odd_comm_antipode` — multiplication by an odd `k` commutes with the antipodal involution
  `x ↦ x + n/2`: `k·(x + n/2) = k·x + n/2`.  Hence the multiplier maps the antipodal pair
  `{x, x+n/2}` to the antipodal pair `{kx, kx+n/2}` — the exact reason the char-0 sparse-count
  is a full-affine invariant while the dual minimum is not.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.SSTMultiplier

open ZMod

/-- Every odd multiplier fixes the unique order-two element `m` of `ZMod (2*m)` (which is the
antipode `n/2` when `n = 2m`).  This is the arithmetic core of the multiplier action's
sparse-count invariance: `k·(n/2) = n/2` for odd `k`. -/
theorem mul_odd_fixes_half {m k : ℕ} (hk : Odd k) :
    (k : ZMod (2 * m)) * (m : ZMod (2 * m)) = (m : ZMod (2 * m)) := by
  obtain ⟨j, rfl⟩ := hk
  have hsplit : (2 * j + 1) * m = 2 * m * j + m := by ring
  rw [← Nat.cast_mul, hsplit, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]

/-- Units modulo an even number are odd: if `gcd(k, 2*m) = 1` then `k` is odd.  With `n = 2m`
this says every genuine multiplier `gcd(k,n)=1` is odd, so `mul_odd_fixes_half` applies. -/
theorem unit_odd {m k : ℕ} (hcop : Nat.Coprime k (2 * m)) : Odd k := by
  have h2 : Nat.Coprime k 2 := Nat.Coprime.coprime_dvd_right ⟨m, rfl⟩ hcop
  exact Nat.coprime_two_right.mp h2

/-- Multiplication by an odd `k` commutes with the antipodal involution `x ↦ x + n/2` on
`ZMod (2*m)`: it sends the antipodal pair `{x, x + n/2}` to `{k·x, k·x + n/2}`.  This is the
mechanism by which the char-0 (antipodal) sparse-count of a section is invariant under the full
affine action, whereas the dual minimum `λ₁*` (a genuine lattice invariant, not preserved by
the Galois twist `h ↦ hᵏ`) is not — the residue's live/dead split. -/
theorem mul_odd_comm_antipode {m k : ℕ} (hk : Odd k) (x : ZMod (2 * m)) :
    (k : ZMod (2 * m)) * (x + (m : ZMod (2 * m)))
      = (k : ZMod (2 * m)) * x + (m : ZMod (2 * m)) := by
  rw [mul_add, mul_odd_fixes_half hk]

/-- The reversal `k = -1` case (round-2's `S ↦ −S`): `-1` fixes the antipode, so `S ↦ −S`
preserves antipodal pairs and hence the char-0 sparse-count — consistent with the probe's
`924/924` sparse-count agreement, while dual-min agreement is only partial. -/
theorem neg_one_fixes_half {m : ℕ} :
    (-1 : ZMod (2 * m)) * (m : ZMod (2 * m)) = (m : ZMod (2 * m)) := by
  have h2m : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self (2 * m)
  have : (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add]; simpa [two_mul] using h2m
  linear_combination (-(1 : ZMod (2 * m))) * this

end ArkLib.ProximityGap.SSTMultiplier

-- axiom audit
#print axioms ArkLib.ProximityGap.SSTMultiplier.mul_odd_fixes_half
#print axioms ArkLib.ProximityGap.SSTMultiplier.unit_odd
#print axioms ArkLib.ProximityGap.SSTMultiplier.mul_odd_comm_antipode
#print axioms ArkLib.ProximityGap.SSTMultiplier.neg_one_fixes_half
