/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HaloFreeThreshold

/-!
# WF407 / L5-s256 — depth-1 census coverage: ℓ¹ row, and a CONDITIONAL s = 256 row

**Thread L5-s256** (see `docs/kb/wf407w2-L5-s256-census-coverage.md`).  The original
headline of this thread ("unconditional census coverage to s = 256 via Parseval halving") is
**not** established: its resultant bound is false (see "Correction" below).

At a *fixed* prime field `F = 𝔽_p` the depth-1 collision/halo census of a dyadic fold scale
`s = 2^m` (half-period `N = s/2 = 2^{m-1}`) is **halo-free** — i.e. the finite-field census
equals the characteristic-0 census, with no exotic mod-`p` coincidences — as soon as the
cyclotomic resultant (norm) of every nonzero antipodal differential (a `{−1,0,1}`-coefficient
polynomial of degree `< N`) is smaller than `p`.  Note this is a LOWER bound on `p`: a field
ceiling `p < 2^256` never supplies it, and primes below the threshold are not covered.

* **ℓ¹ (coarse, IN THIS TREE, proved).**  `|Res| ≤ (ℓ¹)^N ≤ N^N`, so `N^N < p` ⟹ halo-free.
  This is exactly `HaloFreeThreshold.sum_pow_eq_zero_iff_antipodalClosed`.  Below the ceiling
  `2^256` its coverage extent is `s ≤ 64` (`N^N = 2^{N·log₂N}`: `s=64 → 2^160 < 2^256`;
  `s=128 → 2^384`), i.e. s = 64 is covered for primes `2^160 < p`.

* **ℓ² (correct Parseval bound, NOT formalized here).**  For a polynomial `R = ∑_{i<N} cᵢXⁱ`,
  Parseval over the `N` primitive `2^m`-th roots plus AM–GM gives
  `|Res(R, X^N+1)|² ≤ (∑ cᵢ²)^N`, i.e. `|Res| ≤ (∑ cᵢ²)^{N/2} ≤ N^{N/2}` for ternary `R`.  The
  generic ternary threshold is therefore `N^{N/2} = 2^{(m-1)·N/2}`: `s=128 → 2^192 < 2^256`,
  `s=256 → 2^448 > 2^256` (`coverage_s128_parsevalCorrect`, `no_coverage_s256_parsevalCorrect`
  are this arithmetic).  A constant-per-coordinate bound such as `8^N` needs a bounded
  coefficient support (`∑ cᵢ² ≤ 8`), which an arbitrary differential does not have.

**Correction (2026-10-28 audit, R-323).**  Earlier text claimed `|Res|² ≤ 8^N`, i.e.
`|Res| ≤ 2^{3N/2}`, for an ARBITRARY ternary differential.  That is false:
* at `N = 16` (`m = 5`) the differential of
  `E = {1,2,4,5,7,8,9,10,14,19,22,27,28,29,31}` has norm against `X^16+1` equal to the prime
  `412876481 > 2^24`; and over `𝔽_412876481` with the primitive 32nd root `g = 7881733`,
  `∑_{e∈E} g^e = 0` although `E` is not antipodal-closed.  So the named statement
  `ParsevalCensusResultantBound 5` is **false**, and this is kernel-checked below as
  `not_parsevalCensusResultantBound_five`;
* at `N = 128` (`m = 8`) the Rudin–Shapiro differential (`c₀ = 0`,
  `c_j = (-1)^{#adjacent 11 bit pairs of j}`) has an exact norm of 425 bits `> 2^192`
  (exact determinant computation, not formalized).  This refutes the resultant BOUND at
  `m = 8`, but a large norm does not by itself produce a prime `p > 2^192` and a selected root
  at which a collision occurs, so `ParsevalCensusResultantBound 8` (a census statement) is
  neither proved nor refuted: it is an **open** named input, and the "Parseval derivation"
  formerly offered for it is invalid.

**What is unconditional here.**  The threshold arithmetic (`coverage_s64_l1`,
`no_coverage_s128_l1`, `coverage_s256_parseval`, `no_coverage_s512_parseval`,
`coverage_s128_parsevalCorrect`, `no_coverage_s256_parsevalCorrect`), the ℓ¹ row
`haloFree_l1` (through the in-tree `sum_pow_eq_zero_iff_antipodalClosed`) and the refutation
`not_parsevalCensusResultantBound_five`.

**What is conditional.**  `haloFree_of_parseval_bound` and `haloFree_s256` take the named
`Prop` `ParsevalCensusResultantBound` as a hypothesis (never an axiom), and `haloFree_s256`
also takes the lower bound `2^192 < p` explicitly.  The s = 256 row is therefore conditional
on an open census statement for which no valid proof route is currently known; the `2^192`
threshold arithmetic does not by itself cover s = 256.

## References
* [KKH26] ePrint 2026/782, Lemma 1/2.   DISPROOF_LOG O151 (Parseval halving).   Issue #334 B3 / #407.
-/

namespace ArkLib.ProximityGap.KKH26

open Finset

/-! ### The census statement at threshold `2^{3N/2}`, as a named `Prop` -/

/-- **The census statement at the `2^{3N/2}` threshold** for the depth-1 census at fold scale
`s = 2^m` (`N = 2^{m-1}`), packaged as a named `Prop` (never an axiom): for every prime
`p > 2^{3N/2}`, every primitive `2^m`-th root `g` of `𝔽_p` and EVERY `E ⊆ [0, 2^m)`, the sum
`∑_{e∈E} g^e` vanishes iff `E` is antipodal-closed.

It was introduced as the consequence of a claimed resultant bound `|Res| ≤ 2^{3N/2}` for an
arbitrary ternary antipodal differential.  That resultant bound is false (the correct
Parseval/AM–GM bound is `|Res| ≤ (∑ cᵢ²)^{N/2}`, which is `N^{N/2}` for an arbitrary ternary
differential), and the census statement itself is **false at `m = 5`**:
see `not_parsevalCensusResultantBound_five`.  At `m = 8` it is an open statement (the
resultant bound fails there too, but no selected-prime collision above `2^192` is known); it
is used only as an explicit hypothesis. -/
def ParsevalCensusResultantBound (m : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ZMod p), IsPrimitiveRoot g (2 ^ m) →
    ∀ (E : Finset ℕ), E ⊆ range (2 ^ m) →
      (2 : ℕ) ^ (3 * 2 ^ (m - 1) / 2) < p →
        ((∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ (m - 1)) E)

/-! ### Layer 1 — the in-tree ℓ¹ engine: end-to-end unconditional, covers s ≤ 64 -/

/-- **The ℓ¹ (coarse) halo-free row, fully unconditional and end-to-end** (just the in-tree
`sum_pow_eq_zero_iff_antipodalClosed` re-exposed at the coverage-arithmetic level).  Above the
ℓ¹ threshold `N^N < p` the depth-1 census equals the char-0 census. -/
theorem haloFree_l1 {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {E : Finset ℕ} (hE : E ⊆ range (2 ^ m))
    (hp : ((2 : ℕ) ^ (m - 1)) ^ 2 ^ (m - 1) < p) :
    (∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ (m - 1)) E :=
  sum_pow_eq_zero_iff_antipodalClosed hm hg hE hp

/-- **ℓ¹ coverage extent: `s = 64` (`m = 6`) is in.**  The coarse threshold `N^N` at `m = 6`
(`N = 32`) is `32^32 = 2^160 < 2^256`, so the in-tree engine covers s = 64 at every prime
field `2^160 < p < 2^256`. -/
theorem coverage_s64_l1 : ((2 : ℕ) ^ (6 - 1)) ^ 2 ^ (6 - 1) < 2 ^ 256 := by
  norm_num

/-- **ℓ¹ coverage extent: `s = 128` (`m = 7`) is OUT.**  At `m = 7` (`N = 64`) the coarse
threshold is `64^64 = 2^384 ≥ 2^256`: the in-tree ℓ¹ engine cannot reach s = 128 inside the
prize ceiling.  (This is precisely the gap the Parseval halving closes.) -/
theorem no_coverage_s128_l1 : (2 : ℕ) ^ 256 ≤ ((2 : ℕ) ^ (7 - 1)) ^ 2 ^ (7 - 1) := by
  norm_num

/-! ### Layer 2 — the `2^{3N/2}` threshold: conditional consumer and arithmetic -/

/-- **Consumer of the named census statement.**  Given `ParsevalCensusResultantBound m`, the
depth-1 census at fold scale `s = 2^m` is halo-free at every prime `p > 2^{3N/2}`.  This is a
restatement of the hypothesis; note `ParsevalCensusResultantBound 5` is false
(`not_parsevalCensusResultantBound_five`), so the hypothesis must be checked per `m`. -/
theorem haloFree_of_parseval_bound {m : ℕ} (hPB : ParsevalCensusResultantBound m)
    {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {E : Finset ℕ} (hE : E ⊆ range (2 ^ m))
    (hp : (2 : ℕ) ^ (3 * 2 ^ (m - 1) / 2) < p) :
    (∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ (m - 1)) E :=
  hPB p g hg E hE hp

/-- **`2^{3N/2}` threshold arithmetic at `s = 256` (`m = 8`).**  The exponent at `m = 8` is
`3·N/2 = 3·128/2 = 192`, and `2^192 < 2^256`: under the hypothesis
`ParsevalCensusResultantBound 8` (an open census statement), the s = 256 census would be
halo-free at every prime `p` with `2^192 < p` (in particular for `2^192 < p < 2^256`; primes
`p ≤ 2^192` are not covered).  This is arithmetic only, not unconditional coverage: the
`2^{3N/2}` resultant bound that motivated the threshold is false (module docstring). -/
theorem coverage_s256_parseval : (2 : ℕ) ^ (3 * 2 ^ (8 - 1) / 2) < 2 ^ 256 := by
  norm_num

/-- **`2^{3N/2}` threshold arithmetic at `s = 512` (`m = 9`).**  At `m = 9` the exponent is
`3·256/2 = 384`, so the threshold `2^384 ≥ 2^256` exceeds the field ceiling: even the
(conditional) `2^{3N/2}` threshold does not reach s = 512 inside `p < 2^256`.  This pins the
reach of the conditional `2^{3N/2}` row only; it is not an unconditional coverage frontier. -/
theorem no_coverage_s512_parseval : (2 : ℕ) ^ 256 ≤ (2 : ℕ) ^ (3 * 2 ^ (9 - 1) / 2) := by
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **The conditional s = 256 row.**  Under the hypothesis `ParsevalCensusResultantBound 8`
(an open census statement, not a proved resultant bound) and the explicit lower bound
`2^192 < p`, the depth-1 census of the s = 256 fold scale is halo-free: the finite-field census
equals the char-0 census.  The field ceiling `p < 2^256` plays no role and does not supply the
lower bound.  Unconditional coverage at s = 256 is NOT established. -/
theorem haloFree_s256 (hPB : ParsevalCensusResultantBound 8)
    {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ 8))
    {E : Finset ℕ} (hE : E ⊆ range (2 ^ 8))
    (hlo : (2 : ℕ) ^ 192 < p) :
    (∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ 7) E := by
  have hp : (2 : ℕ) ^ (3 * 2 ^ (8 - 1) / 2) < p := by
    have : (3 * 2 ^ (8 - 1) / 2) = 192 := by norm_num
    rwa [this]
  exact haloFree_of_parseval_bound hPB hg hE hp

/-! ### Layer 3 — refutation at `m = 5` and the correct generic Parseval threshold -/

section Refutation5

-- The kernel replay of the `norm_num` primality certificate exceeds the default recursion
-- depth on Lean 4.35, so it is raised for this one declaration.
set_option maxRecDepth 10000 in
local instance fact_prime_412876481 : Fact (Nat.Prime 412876481) := ⟨by norm_num⟩

/-- `7881733` has multiplicative order `32` in `𝔽_412876481`. -/
theorem orderOf_7881733_zmod412876481 : orderOf (7881733 : ZMod 412876481) = 32 := by
  have h16 : ¬ (7881733 : ZMod 412876481) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (7881733 : ZMod 412876481) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (7881733 : ZMod 412876481)) h16 h32
  norm_num at h
  exact h

/-- `7881733` is a primitive `2^5`-th root of unity in `𝔽_412876481`. -/
theorem isPrimitiveRoot_7881733_zmod412876481 :
    IsPrimitiveRoot (7881733 : ZMod 412876481) (2 ^ 5) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_7881733_zmod412876481

/-- **`ParsevalCensusResultantBound 5` is false** (R-323 countermodel).  Over
`𝔽_412876481` (`412876481 > 2^24 = 2^{3·16/2}`) with the primitive 32nd root `7881733`, the
set `E = {1,2,4,5,7,8,9,10,14,19,22,27,28,29,31}` has `∑_{e∈E} g^e = 0` but is not
antipodal-closed (`1 ∈ E`, `17 ∉ E`).  Equivalently the antipodal differential of `E` has norm
against `X^16 + 1` equal to the prime `412876481` (exact computation, not formalized here), so
the claimed bound `|Res| ≤ 2^{3N/2}` fails at `N = 16`. -/
theorem not_parsevalCensusResultantBound_five : ¬ ParsevalCensusResultantBound 5 := by
  intro h
  have hE : ({1, 2, 4, 5, 7, 8, 9, 10, 14, 19, 22, 27, 28, 29, 31} : Finset ℕ) ⊆
      range (2 ^ 5) := by decide
  have hthr : (2 : ℕ) ^ (3 * 2 ^ (5 - 1) / 2) < 412876481 := by norm_num
  have hsum : ∑ e ∈ ({1, 2, 4, 5, 7, 8, 9, 10, 14, 19, 22, 27, 28, 29, 31} : Finset ℕ),
      (7881733 : ZMod 412876481) ^ e = 0 := by decide
  have hac := (h 412876481 7881733 isPrimitiveRoot_7881733_zmod412876481 _ hE hthr).mp hsum
  have h17 := (hac 1 (by norm_num)).mp (by decide)
  revert h17
  decide

end Refutation5

/-- **Correct generic Parseval threshold arithmetic at `s = 128` (`m = 7`).**  The correct
ternary Parseval/AM–GM bound `|Res| ≤ N^{N/2}` (not formalized here) gives the threshold
`(2^6)^{2^6/2} = 2^192 < 2^256` at `N = 64`. -/
theorem coverage_s128_parsevalCorrect :
    ((2 : ℕ) ^ (7 - 1)) ^ (2 ^ (7 - 1) / 2) < 2 ^ 256 := by
  norm_num

/-- **Correct generic Parseval threshold arithmetic at `s = 256` (`m = 8`).**  At `N = 128`
the generic ternary threshold `N^{N/2} = 2^448` exceeds `2^256`: the correct Parseval bound
alone does not cover s = 256 below the field ceiling. -/
theorem no_coverage_s256_parsevalCorrect :
    (2 : ℕ) ^ 256 ≤ ((2 : ℕ) ^ (8 - 1)) ^ (2 ^ (8 - 1) / 2) := by
  norm_num

/-! ### Reading of the verdict (documentation) -/

/-! **The coverage status** (documentation note).  The in-tree ℓ¹ engine covers `s ≤ 64`
for primes above its threshold (`haloFree_l1`, `coverage_s64_l1`, `no_coverage_s128_l1`).
The correct generic Parseval bound `N^{N/2}` would reach `s = 128` for `p > 2^192`
(`coverage_s128_parsevalCorrect`) but not `s = 256` (`no_coverage_s256_parsevalCorrect`); it
is not formalized here.  The s = 256 row (`haloFree_s256`) is conditional on the open
`ParsevalCensusResultantBound 8`; the same named statement is false at `m = 5`
(`not_parsevalCensusResultantBound_five`). -/

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.haloFree_l1
#print axioms ArkLib.ProximityGap.KKH26.coverage_s64_l1
#print axioms ArkLib.ProximityGap.KKH26.no_coverage_s128_l1
#print axioms ArkLib.ProximityGap.KKH26.haloFree_of_parseval_bound
#print axioms ArkLib.ProximityGap.KKH26.coverage_s256_parseval
#print axioms ArkLib.ProximityGap.KKH26.no_coverage_s512_parseval
#print axioms ArkLib.ProximityGap.KKH26.haloFree_s256
#print axioms ArkLib.ProximityGap.KKH26.not_parsevalCensusResultantBound_five
#print axioms ArkLib.ProximityGap.KKH26.coverage_s128_parsevalCorrect
#print axioms ArkLib.ProximityGap.KKH26.no_coverage_s256_parsevalCorrect
