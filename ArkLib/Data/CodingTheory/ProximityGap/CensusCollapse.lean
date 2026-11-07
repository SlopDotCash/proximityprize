/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetStrip

/-!
# The conditional census collapse: the `a = 8` row reduces to the `a = 4` row

Campaign #357. One application of the strip step (`strip_coset`): under the (named,
probe-true) size-8 *contains-a-coset* obligation, every qualifying exponent set of size
EXACTLY 8 strips to a qualifying set of size 4, with the same census value at every prime
simultaneously:

> **`census8_collapse_of_containsCoset`** — given `ContainsCosetHyp8 m` (and `2 ≤ m`),
> every qualifying `A ⊆ range (2^m)` with `|A| = 8` has a qualifying `A' ⊆ range (2^m)`
> with `|A'| = 4` and `∑_{i∈A} g^i = ∑_{i∈A'} g^i` for every prime `p` and primitive
> `2^m`-th root `g ∈ ZMod p`.

This is the only collapse proved here.  An earlier, larger form — every qualifying set of any
size `a ≡ 0 (mod 4)` stripping to a core of size `< 6` — is FALSE (see the counterexamples
below), and no declaration of that form exists.

The obligation is restricted to sets of size EXACTLY 8: the C sweeps refute every
larger form — coset-free balanced 9-sets exist (one orbit at n=16, eleven at n=32),
and coset-free balanced 12- and 16-sets exist at n=32 (128 and 256, ALL of whose census
values escape census(4)): the rows a ≥ 9 of the depth-1 table are genuinely growing
primitive hierarchies, and only the a = 8 row collapses. The size-8 obligation is
probe-verified exhaustively at n = 16, 32, 64 (zero exceptions, all class structures —
4.4·10⁹ configurations at n = 64), the k = 3 class-count case is proven by hand, the
k = 4, 5 architecture lists are enumerated (67 cases, one killed), and the k ≥ 6
singleton-heavy core is localized to a σ-pinning propagation question.

## References

* Probes `probe_8set_coset_structure.py`, `probe_coset_core_conjecture.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

/-- **The named obligation** (the project's residual convention): every qualifying
exponent set of size EXACTLY 8 contains a full coset of the order-4 subgroup in
reduction. The size restriction is essential and sharp: coset-free balanced sets of sizes
9, 12, 16 exist at `n = 32` (C sweeps), so no larger form is true. Probe-verified
exhaustively at `n = 16, 32, 64` with zero exceptions across all class structures. -/
def ContainsCosetHyp8 (m : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.range (2 ^ m) → A.card = 8 →
    e2Folded m A = 0 →
    ∃ x : ZMod (2 ^ m),
      x ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))

/-- **The conditional a = 8 collapse.** Under the size-8 obligation, every qualifying
8-set strips to a qualifying 4-set with the same census value at every prime
simultaneously: `census(8) ⊆ census(4)`, the downward half of the measured set-equality
`census(8) = census(4) = (n/2−1)²`. (The upward half is the free-coset augmentation;
rows `a ≥ 9` provably do NOT collapse — their censuses grow with the primitive layers.) -/
theorem census8_collapse_of_containsCoset {m : ℕ} (hm : 2 ≤ m)
    (hyp : ContainsCosetHyp8 m)
    {A : Finset ℕ} (hsub : A ⊆ Finset.range (2 ^ m)) (hcard : A.card = 8)
    (hzero : e2Folded m A = 0) :
    ∃ A' : Finset ℕ, A' ⊆ Finset.range (2 ^ m) ∧ A'.card = 4 ∧ e2Folded m A' = 0 ∧
      ∀ {p : ℕ} [Fact p.Prime] (g : ZMod p), IsPrimitiveRoot g (2 ^ m) →
        ∑ i ∈ A, g ^ i = ∑ i ∈ A', g ^ i := by
  obtain ⟨x, hx, hxq, hxh, hxqh⟩ := hyp A hsub hcard hzero
  obtain ⟨A', hsub', hcard', hzero', hsum'⟩ :=
    strip_coset hm hsub hzero hx hxq hxh hxqh
  exact ⟨A', hsub', by omega, hzero', hsum'⟩

/-! ## Source audit -/

#print axioms census8_collapse_of_containsCoset

end ArkLib.ProximityGap.WindowTwoLayer
