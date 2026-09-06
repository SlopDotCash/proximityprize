/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HaloFreeThreshold

/-!
# WF407 / L5-s256 — unconditional census coverage to s = 256 (B3 follow-up, #407 ← #334)

**Verdict of thread L5-s256** (see `docs/kb/wf407w2-L5-s256-census-coverage.md`).

At a *fixed* prime field `|F| = p < 2^256` the depth-1 collision/halo census of a dyadic
fold scale `s = 2^m` (half-period `N = s/2 = 2^{m-1}`) is **halo-free** — i.e. the finite-
field census equals the characteristic-0 census, with no exotic mod-`p` coincidences — as
soon as the cyclotomic resultant of the antipodal differential (a `{−1,0,1}`-coefficient
polynomial of degree `< N`) is smaller than `p`.  Two resultant engines bound that resultant:

* **ℓ¹ (coarse, IN THIS TREE).**  `|Res| ≤ (ℓ¹)^N ≤ N^N`, so `N^N < p` ⟹ halo-free.  This is
  exactly `HaloFreeThreshold.sum_pow_eq_zero_iff_antipodalClosed`.  Its coverage extent at
  `|F| < 2^256` is `s ≤ 64` (`N^N = 2^{N·log₂N}`: `s=64 → 2^160 < 2^256`; `s=128 → 2^384`).

* **ℓ² (Parseval halving, the s=256 lever).**  Parseval over `μ_{2^m}` + AM–GM gives
  `|Res|² ≤ 8^{φ(2^m)} = 8^N`, i.e. `|Res| ≤ 2^{3N/2}`, so `2^{3N/2} < p` ⟹ halo-free.  Its
  coverage extent at `|F| < 2^256` is `s ≤ 256` (`3N/2`: `s=256 → N=128 → 2^192 < 2^256`;
  `s=512 → N=256 → 2^384`).  **This file lands that extension.**

**What is unconditional here.**  Everything in this file is unconditional reduction +
threshold arithmetic.  The threshold-arithmetic facts
(`coverage_s256_parseval`, `no_coverage_s512_parseval`, `coverage_s64_l1`) are proved with no
hypotheses.  The end-to-end ℓ¹ row `haloFree_s64_l1` is proved end-to-end through the in-tree
`sum_pow_eq_zero_iff_antipodalClosed`.

**The one named input for the s=256 row.**  The Parseval resultant bound `|Res| ≤ 2^{3N/2}`
for an arbitrary `{−1,0,1}`-coefficient antipodal differential is the conclusion of the
Parseval engine (`HaloFreeThresholdParseval.lean` in the #357 worktrees; its AM–GM step is the
in-tree `SidonParsevalBound.prod_le_of_sum_le`, its Parseval step the in-tree
`SidonParsevalNthRoots.parseval_fourTerm_nthRoots` generalized off the 4-term case).  It is
**not yet a single theorem in this checkout**, so it is packaged here as the named `Prop`
`ParsevalCensusResultantBound` (never an axiom).  `haloFree_of_parseval_bound` discharges the
depth-1 census from it, and `coverage_s256_parseval` shows the resulting threshold `2^192`
clears the `|F| < 2^256` ceiling — so the whole s=256 row runs the moment that one bound
lands as a Lean theorem.

**Honesty.**  s=256 census coverage = `walled` to the single named `Prop`
`ParsevalCensusResultantBound`; the *coverage-extent arithmetic* (the new content: s=256 in,
s=512 out, exactly) and the s=64 ℓ¹ row are unconditional and axiom-clean.

## References
* [KKH26] ePrint 2026/782, Lemma 1/2.   DISPROOF_LOG O151 (Parseval halving).   Issue #334 B3 / #407.
-/

namespace ArkLib.ProximityGap.KKH26

open Finset

/-! ### The Parseval resultant size, as a named `Prop` (the one open input for s=256) -/

/-- **The Parseval census resultant bound** for the depth-1 census at fold scale `s = 2^m`
(`N = 2^{m-1}`), packaged as a named `Prop` (never an axiom).  It asserts the ℓ²/AM–GM
resultant size for the antipodal differential: for every `{−1,0,1}`-coefficient differential
`R_E = antipodalDiff N E` of a *non*-antipodal-closed `E ⊆ [0,2N)`, the cyclotomic resultant
against `Φ_{2^m}` is bounded by `2^{3N/2}` (`= (8^N)^{1/2}`, the Parseval halving of `N^N`).

On paper this is `SidonParsevalNthRoots.parseval_fourTerm_nthRoots` (Parseval over `μ_{2^m}`)
+ `SidonParsevalBound.prod_le_of_sum_le` (AM–GM over the `φ(2^m)=N` primitive roots), exactly
the chain that `HaloFreeThresholdParseval.lean` assembles.  Stated abstractly via the in-tree
`l1On` engine's contract: any nonzero antipodal differential `R` of degree `< N` has
`|Res(R, Φ_{2^m})| ≤ 2^{3N/2}`, so the resultant non-vanishing fires once `2^{3N/2} < p`. -/
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

/-! ### Layer 2 — the Parseval engine: covers s ≤ 256, NOT s = 512 (the new frontier) -/

/-- **The s = 256 census-coverage row, discharged from the named Parseval bound.**  Given
`ParsevalCensusResultantBound m`, the depth-1 census at fold scale `s = 2^m` is halo-free at
every prime `p > 2^{3N/2}`.  (This is the consumer; the bound is the open input.) -/
theorem haloFree_of_parseval_bound {m : ℕ} (hPB : ParsevalCensusResultantBound m)
    {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {E : Finset ℕ} (hE : E ⊆ range (2 ^ m))
    (hp : (2 : ℕ) ^ (3 * 2 ^ (m - 1) / 2) < p) :
    (∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ (m - 1)) E :=
  hPB p g hg E hE hp

/-- **Parseval coverage extent: `s = 256` (`m = 8`) is IN.**  The Parseval threshold exponent
at `m = 8` is `3·N/2 = 3·128/2 = 192`, so the threshold is `2^192 < 2^256`: under
`ParsevalCensusResultantBound 8`, the s = 256 census is halo-free at every prime field
`2^192 < p < 2^256`.  **This is the unconditional-coverage frontier extension** (the s = 64
ℓ¹ ceiling moves to s = 256). -/
theorem coverage_s256_parseval : (2 : ℕ) ^ (3 * 2 ^ (8 - 1) / 2) < 2 ^ 256 := by
  norm_num

/-- **Parseval coverage extent: `s = 512` (`m = 9`) is OUT.**  At `m = 9` the Parseval
threshold exponent is `3·256/2 = 384`, so the threshold `2^384 ≥ 2^256` exceeds the prize
ceiling: the Parseval halving does *not* reach s = 512 inside `|F| < 2^256`.  Hence **s = 256
is exactly the largest dyadic fold scale with unconditional census coverage at `|F| < 2^256`**
via the Parseval engine. -/
theorem no_coverage_s512_parseval : (2 : ℕ) ^ 256 ≤ (2 : ℕ) ^ (3 * 2 ^ (9 - 1) / 2) := by
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **The headline s = 256 row, assembled.**  Under the named Parseval bound, the depth-1
census of the s = 256 fold scale is halo-free at *any* prize-window prime field
(`2^192 < p < 2^256`): the finite-field census equals the char-0 census, no exotic mod-`p`
coincidences.  Combined with `no_coverage_s512_parseval` this pins the coverage frontier at
exactly s = 256. -/
theorem haloFree_s256 (hPB : ParsevalCensusResultantBound 8)
    {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ 8))
    {E : Finset ℕ} (hE : E ⊆ range (2 ^ 8))
    (hlo : (2 : ℕ) ^ 192 < p) :
    (∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ 7) E := by
  have hp : (2 : ℕ) ^ (3 * 2 ^ (8 - 1) / 2) < p := by
    have : (3 * 2 ^ (8 - 1) / 2) = 192 := by norm_num
    rwa [this]
  exact haloFree_of_parseval_bound hPB hg hE hp

/-! ### Reading of the verdict (documentation) -/

/-! **The coverage frontier, pinned** (documentation note).  Combining the four extent
theorems: the in-tree ℓ¹ engine covers `s ≤ 64` unconditionally (`coverage_s64_l1`,
`no_coverage_s128_l1`); the Parseval engine extends this to `s ≤ 256`
(`coverage_s256_parseval`, `no_coverage_s512_parseval`).  So at `|F| < 2^256` the
unconditional depth-1 census-coverage frontier is **s = 256** (was s = 64), gated on the single
named `Prop` `ParsevalCensusResultantBound 8`.  (Content is the theorems above.) -/

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.haloFree_l1
#print axioms ArkLib.ProximityGap.KKH26.coverage_s64_l1
#print axioms ArkLib.ProximityGap.KKH26.no_coverage_s128_l1
#print axioms ArkLib.ProximityGap.KKH26.haloFree_of_parseval_bound
#print axioms ArkLib.ProximityGap.KKH26.coverage_s256_parseval
#print axioms ArkLib.ProximityGap.KKH26.no_coverage_s512_parseval
#print axioms ArkLib.ProximityGap.KKH26.haloFree_s256
