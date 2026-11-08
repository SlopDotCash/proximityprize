/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RigidityIterated2kLift

/-!
# Bounded-coefficient cyclotomic independence: a char-p premise refuted at prize scale (#407)

Tracing the moment ladder to its root: in **char-0**, `HalfBasisIndepZ ζ (2^{m-1})` (no nonzero integer
relation among the half-basis powers) is proven from `minpoly ℚ ζ = Φ_{2^m}`
(`halfBasisIndepZ_of_primitiveRoot`), and the GENERAL antipodal-structure results
(`antipodallyClosed_of_disjoint_equal_sum`) then give every `RepK` ⟹ every Wick energy bound. So the
entire ladder is char-0-proven; the prize is purely a **char-p** phenomenon.

But `HalfBasisIndepZ` is **always false in char-p** (take `g = (p,0,…)`: `p·ζ⁰ = 0`). The rigidity chain
only ever uses **bounded** coefficients (a `k`-tuple of roots gives a relation with `|g_j| ≤ k`).
Hence the char-p candidate premise:

> **`BoundedHalfBasisIndep ζ N C`** := no nonzero `g ∈ [−C,C]^N` with `∑_j g_j ζ^j = 0`.

Note that `C` bounds **each coefficient** separately (sup-norm); the predicate does **not** bound
the support or total multiplicity `∑|g_j|` — up to all `N` coefficients may be nonzero. It is a
dense-box condition, not a sparse-relation condition.

This CAN hold in char-`p` above a threshold (the r=2 instance `C=2` is the landed
`sidonModNeg_rootsOfUnity_improved` at `p > 12^{φ(n)}`). **But in the prize regime it is false,
not open.** Injectivity of `{0,…,C}^N → F`, `a ↦ ∑ a_j ζ^j`, is necessary, so it requires
`(C+1)^N ≤ |F|` (`not_boundedHalfBasisIndep_of_card_lt`). At `N ≈ n/2` and polynomial field size
`q ~ n⁴` this fails for all large `n` even at `C = 1` (`2^{n/2} > n⁴` from `n = 64` on), and much
earlier at the previously advertised `C ~ 2 ln q`. Concretely, at `n = 16`, `p = 65537`, `ω = 64`,
the premise `BoundedHalfBasisIndep ω 8 4` is refuted in Lean (`not_boundedHalfBasisIndep_zmod65537`,
explicit witness `g = (−4,−4,−4,−1,−1,−1,0,0)` in `zmod65537_halfBasis_relation`), matching the
`DISPROOF_LOG.md` entry "BoundedHalfBasisIndep (the named char-p prize core): FALSE at the prize
prime" (which also records height-1 relations at `n = 32`). The reductions from this premise
(`AntipodalBalanceBounded`, `CountAntipodalBounded`, `BridgeBounded`) are valid conditional
implications, but this exact premise cannot be the prize core in the prize regime; an honest
replacement must use weaker hypotheses (e.g. a sparse/`ℓ¹`-bounded relation predicate matching
the relations a `k`-tuple actually produces, with its connection proved separately). A fixed `C`
also does not by itself give a Wick ladder for unbounded `r` without a uniform coefficient bound.
This file names the premise, discharges the char-0 side, and records the finite-field refutation.

Issue #407.
-/

open Round29IteratedLift

namespace ArkLib.ProximityGap.BoundedCyclotomicIndep

variable {F : Type*} [Field F]

/-- **Bounded-coefficient half-basis independence (`HBIᵦ`).** No nonzero integer relation with
coefficients in `[−C, C]` among the half-basis powers `1, ζ, …, ζ^{N-1}`. Unlike the unbounded
`HalfBasisIndepZ` (always false in char-`p`), this can hold in char-`p`, but only when
`(C+1)^N ≤ |F|` (`not_boundedHalfBasisIndep_of_card_lt`); it is false in the prize regime. `C` is a
per-coefficient bound, not a support bound. -/
def BoundedHalfBasisIndep (ζ : F) (N C : ℕ) : Prop :=
  ∀ g : Fin N → ℤ, (∀ j, (g j).natAbs ≤ C) →
    (∑ j : Fin N, (g j : F) * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0

/-- The bounded version is **weaker** than unbounded integer independence: drop the coefficient bound. -/
theorem boundedHalfBasisIndep_of_halfBasisIndepZ {ζ : F} {N : ℕ} (C : ℕ)
    (h : HalfBasisIndepZ ζ N) : BoundedHalfBasisIndep ζ N C :=
  fun g _ hsum j => h g hsum j

/-- **Char-0 discharge.** For a primitive `2^m`-th root in a characteristic-0 field, bounded-coefficient
half-basis independence holds at **every** bound `C` (it is implied by the unbounded cyclotomic
independence). It does **not** survive the transfer to char-`p` at prize parameters: see
`not_boundedHalfBasisIndep_of_card_lt` and `not_boundedHalfBasisIndep_zmod65537`. -/
theorem boundedHalfBasisIndep_of_primitiveRoot [CharZero F] {m : ℕ} (hm : 1 ≤ m) (C : ℕ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) : BoundedHalfBasisIndep ζ (2 ^ (m - 1)) C :=
  boundedHalfBasisIndep_of_halfBasisIndepZ C (halfBasisIndepZ_of_primitiveRoot hm hζ)

/-! ## Refutation in finite fields: the counting obstruction -/

/-- **Counting obstruction.** In a finite field with `|F| < (C+1)^N`, `BoundedHalfBasisIndep ζ N C`
fails for every `ζ`: the map `{0,…,C}^N → F`, `a ↦ ∑ a_j ζ^j`, is not injective, and the difference
of two colliding vectors is a nonzero relation with coefficients in `[−C, C]`. -/
theorem not_boundedHalfBasisIndep_of_card_lt [Fintype F] (ζ : F) {N C : ℕ}
    (hcard : Fintype.card F < (C + 1) ^ N) : ¬ BoundedHalfBasisIndep ζ N C := by
  intro h
  let φ : (Fin N → Fin (C + 1)) → F := fun a => ∑ j : Fin N, (((a j : ℕ) : F)) * ζ ^ (j : ℕ)
  have hlt : Fintype.card F < Fintype.card (Fin N → Fin (C + 1)) := by
    simpa [Fintype.card_fun, Fintype.card_fin] using hcard
  obtain ⟨a, a', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt
  apply hne
  have hz := h (fun j => ((a j : ℕ) : ℤ) - ((a' j : ℕ) : ℤ))
    (fun j => by
      show (((a j : ℕ) : ℤ) - ((a' j : ℕ) : ℤ)).natAbs ≤ C
      have := (a j).isLt; have := (a' j).isLt; omega)
    (by
      simp only [φ] at heq
      push_cast
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      rw [heq, sub_self])
  funext j
  apply Fin.ext
  have hj : ((a j : ℕ) : ℤ) - ((a' j : ℕ) : ℤ) = 0 := hz j
  omega

private theorem prime_65537 : Nat.Prime 65537 := by norm_num

private local instance fact_prime_65537 : Fact (Nat.Prime 65537) := ⟨prime_65537⟩

/-- `ω = 64` satisfies `ω^8 = −1` in `F_65537`, so it is a primitive 16th root of unity. -/
theorem sixtyFour_pow_eight_zmod65537 : (64 : ZMod 65537) ^ 8 = -1 := by decide

/-- **`BoundedHalfBasisIndep` is false at a prize-sized prime (n = 16, p = 65537 ≈ n⁴).** For the
primitive 16th root `ω = 64` of `F_65537`, the half-basis `1, ω, …, ω^7` (`N = n/2 = 8`) admits a
nonzero relation with coefficients bounded by `4`, e.g. `g = (−4,−4,−4,−1,−1,−1,0,0)`
(`∑ g_j ω^j = −196611 = −3·65537`; recorded in `DISPROOF_LOG.md`). Here it follows from the counting
obstruction, since `5^8 = 390625 > 65537`. -/
theorem not_boundedHalfBasisIndep_zmod65537 :
    ¬ BoundedHalfBasisIndep (64 : ZMod 65537) 8 4 :=
  not_boundedHalfBasisIndep_of_card_lt (64 : ZMod 65537) (by rw [ZMod.card]; norm_num)

/-- The explicit `DISPROOF_LOG.md` witness `g = (−4,−4,−4,−1,−1,−1,0,0)` for
`not_boundedHalfBasisIndep_zmod65537`. -/
theorem zmod65537_halfBasis_relation :
    (∑ j : Fin 8, (((![-4, -4, -4, -1, -1, -1, 0, 0] : Fin 8 → ℤ) j : ℤ) : ZMod 65537)
      * (64 : ZMod 65537) ^ (j : ℕ)) = 0 := by
  decide

end ArkLib.ProximityGap.BoundedCyclotomicIndep
#print axioms ArkLib.ProximityGap.BoundedCyclotomicIndep.boundedHalfBasisIndep_of_primitiveRoot
#print axioms ArkLib.ProximityGap.BoundedCyclotomicIndep.not_boundedHalfBasisIndep_of_card_lt
#print axioms ArkLib.ProximityGap.BoundedCyclotomicIndep.not_boundedHalfBasisIndep_zmod65537
#print axioms ArkLib.ProximityGap.BoundedCyclotomicIndep.zmod65537_halfBasis_relation
