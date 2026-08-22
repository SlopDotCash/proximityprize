/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444 / #389)
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingLifting

/-!
# AVENUE A `hLL` discharge in char 0: every zero-sum `2r`-tuple of `2^k`-th roots is antipodally paired (#444 / #389)

This file **closes the char-0 instance** of the structural input `hLL` of
`Frontier/CharZeroEnergyThreeExact.lean` / the `RepThree` residual of
`GaussianEnergyThreeRepThree.lean` — the "Lam–Leung balance" half of the energy ladder
`E_r = B_{2r}` — by composing two already-axiom-clean in-tree pieces:

1. **Multiset Lam–Leung (forward)** — `LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`:
   a vanishing multiset sum of `2^k`-th roots of unity (char 0) has `count w = count (−w)`
   for every `w`.
2. **Count→pairing lift** — `NegationClosedWalk.exists_isPairing_of_count_balanced`:
   antipodal count-balance of an even-length tuple (with no self-antipodal coordinate)
   produces a fixed-point-free involution `σ` (an `IsPairing`) with `c (σ i) = − c i`.

Composing them gives, for **every `r`** (not just `r ≤ 3`), the exact predicate consumed by
`zeroSumCount_le_pairings` / `RepThree` / avenue A's `hLL`:

> `charZero_hLL_pairing` :  for `k ≥ 1` over a char-0 field, every `2r`-tuple
> `c : Fin (2r) → L` of `2^k`-th roots of unity with `∑ c i = 0` admits an `IsPairing σ`
> with `c (σ i) = − c i` for all `i`.

Specialized to `r = 3` (`charZero_repThree_pairing`) this is exactly the antipodal-pairing
shape of `GaussianEnergyThreeRepThree.RepThree` and the `hLL` direction
`CharZeroEnergyThreeExact` takes on faith — now a theorem in characteristic zero.

## Honest scope (what this does and does NOT do)

This discharges the `hLL`/`RepThree` input **only in characteristic zero**, where Lam–Leung
holds unconditionally.  The PRIZE core is the **char-`p` transfer** of this statement to the
deep regime (`n = 2^30`, `q = 2^158`, depth `r ≈ ln q`) — whether short `≤ 2 ln q`-term
`±1`-relations of `2^μ`-th roots vanish mod the prize prime.  That wall is the genuine open
research and is **not** touched here.  This file makes the char-0 rung hypothesis-free, which
is the strongest the char-0 Lam–Leung substrate can give.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.CharZeroHLLPairing

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- A `2^k`-th root of unity (`k ≥ 1`) over a characteristic-0 field is never equal to its own
negation: `x = −x` forces `2x = 0`, hence `x = 0`, but a root of unity is nonzero. -/
theorem rootOfUnity_ne_neg {k : ℕ} (hk : 1 ≤ k) {x : L} (hx : x ^ (2 ^ k) = 1) :
    x ≠ - x := by
  intro hcontra
  -- x = -x ⟹ 2x = 0 ⟹ x = 0 (char ≠ 2), contradicting x^(2^k) = 1.
  have h2x : (2 : L) * x = 0 := by linear_combination hcontra
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  rcases mul_eq_zero.mp h2x with h | h
  · exact absurd h h2
  · rw [h, zero_pow (by positivity)] at hx
    exact zero_ne_one hx

/-- **AVENUE A `hLL`, general `r`, characteristic 0.**  For a char-0 field and `k ≥ 1`, every
`2r`-tuple `c : Fin (2r) → L` whose entries are `2^k`-th roots of unity and whose sum vanishes
(`∑ c i = 0`) is antipodally paired by an explicit fixed-point-free involution: there is an
`IsPairing σ` with `c (σ i) = − c i` for all `i`.

Mechanism: the value multiset `(map c univ)` sums to `0`, so by multiset Lam–Leung
(`count_antipodal_of_sum_eq_zero`) it is count-balanced (`count w = count (−w)`); each entry
is nonzero (a root of unity) hence non-self-antipodal (`rootOfUnity_ne_neg`), so the
count→pairing lift (`exists_isPairing_of_count_balanced`) produces the involution.

This is the exact predicate consumed by `RepThree` / `zeroSumCount_le_pairings`'s residual
`H` / the `hLL` direction of `CharZeroEnergyThreeExact`, now a theorem in char 0. -/
theorem charZero_hLL_pairing {k r : ℕ} (hk : 1 ≤ k)
    (c : Fin (2 * r) → L) (hc : ∀ i, (c i) ^ (2 ^ k) = 1) (hsum : ∑ i, c i = 0) :
    ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i := by
  -- the value multiset sums to 0 (`(univ.val.map c).sum = ∑ i, c i` definitionally)
  have hMsum : (Finset.univ.val.map c).sum = 0 := by
    have hdef : (Finset.univ.val.map c).sum = ∑ i, c i := rfl
    rw [hdef, hsum]
  -- every element of the multiset is a 2^k-th root of unity
  have hMroot : ∀ w ∈ (Finset.univ.val.map c), w ^ (2 ^ k) = 1 := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hw
    exact hc i
  -- multiset Lam–Leung: count-balance
  have hbal : ∀ w : L, (Finset.univ.val.map c).count w = (Finset.univ.val.map c).count (-w) :=
    LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero (k := k) hMroot hMsum
  -- each coordinate is non-self-antipodal (it is a nonzero root of unity, char ≠ 2)
  have hself : ∀ i, c i ≠ - c i := fun i => rootOfUnity_ne_neg hk (hc i)
  -- count→pairing lift
  exact exists_isPairing_of_count_balanced c hbal hself

/-- **The `r = 3` specialization: char-0 `RepThree` discharge.**  Every zero-sum `6`-tuple of
`2^k`-th roots of unity (`k ≥ 1`) over a char-0 field is antipodally paired by an `IsPairing`.
This is the exact antipodal-pairing shape of `GaussianEnergyThreeRepThree.RepThree` and the
`hLL` input of `CharZeroEnergyThreeExact`, made hypothesis-free in characteristic zero. -/
theorem charZero_repThree_pairing {k : ℕ} (hk : 1 ≤ k)
    (c : Fin (2 * 3) → L) (hc : ∀ i, (c i) ^ (2 ^ k) = 1) (hsum : ∑ i, c i = 0) :
    ∃ σ : Equiv.Perm (Fin (2 * 3)), IsPairing σ ∧ ∀ i, c (σ i) = - c i :=
  charZero_hLL_pairing hk c hc hsum

end ArkLib.ProximityGap.Frontier.CharZeroHLLPairing

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroHLLPairing.rootOfUnity_ne_neg
#print axioms ArkLib.ProximityGap.Frontier.CharZeroHLLPairing.charZero_hLL_pairing
#print axioms ArkLib.ProximityGap.Frontier.CharZeroHLLPairing.charZero_repThree_pairing
