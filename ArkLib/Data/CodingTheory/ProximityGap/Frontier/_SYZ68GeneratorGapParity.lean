/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ44MuBasisDegreeSum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ45ImbalanceBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ53GeneratorGapCalibration

/-!
# SYZ68 — the μ-basis generator gap has **fixed parity** `δ₂ − δ₁ ≡ S (mod 2)`, correcting the
interior target to the class-true `gap ≤ 2 ⟺ ι ≤ 1`

## Context

SYZ44 proved the μ-basis **degree-sum law** `δ₁ + δ₂ = a + b + c =: S` (`degree_sum_of_hilbert`),
and SYZ53 the **exact half-gap identity** `ι = SYZ45.imbalance a b c δ₁ = ⌊(δ₂ − δ₁)/2⌋`
(`imbalance_eq_gap_div_two`), yielding the gap-language calibration `ι ≤ 1 ↔ δ₂ − δ₁ ≤ 3`
(`imbalance_le_one_iff_gap_le_three`).

The SYZ54 consolidation then handed downstream the target **"the μ-basis of a balanced pairwise-
coprime band triple has generator gap `δ₂ − δ₁ ≤ 1`"** for the WHOLE class (with `ι = 0 ⟺ gap ≤ 1`).
A corrected exact
GF(p) μ-basis referee sweep (`fable_syz54_truegap.py`, 1500 cells: 10 balanced/near-balanced shapes
covering **both** degree-sum parities `S = 16..27`, `p ∈ {61,101,257}`, 50 pairwise-coprime distinct
-root triples each) **refuted that wording**:

* the prior instrument measured `δ₂ = min{D : kerdim(D) ≥ 2}`, which is capped at `δ₁ + 1` by the
  poly-multiples `{g₁, x·g₁}` of the *first* generator and therefore **cannot see `gap ≥ 2`**;
  the corrected free-rank-2 readout is `δ₂ = min{D : kerdim(D) > D − δ₁ + 1}`;
* under the corrected instrument the gap obeys **`gap ≡ S (mod 2)` in all 1500 cells** (odd `S`:
  `gap = 1` always; even `S`: `gap ∈ {0, 2}`), with genuine `gap = 2` witnesses at even `S`
  (e.g. `p = 61, a = b = c = 6, S = 18: (δ₁, δ₂) = (8, 10)`, so `ι = 1`).

So the SYZ54 CLASS target "`gap ≤ 1` for all balanced coprime triples" is **false** — it has exact
gap = 2 witnesses at even `S`, so a lane trying to prove `gap ≤ 1` universally would prove a false
statement — and the honest class-true target is **`gap ≤ 2`** (equivalently `ι ≤ 1` via SYZ53's exact
`ι = ⌊gap/2⌋`).  The exact-balance *phrasing* `ι = 0 ⟺ gap ≤ 1` is also misleading across parities:
at even `S` its `gap ≤ 1` collapses to the honest `gap = 0` (gap = 1 vacuous), while at odd `S`,
`gap = 1` (not `0`) is forced with `ι = 0` — so `gap ≤ 1` is not a clean exact-balance criterion.  The mechanism behind the referee's parity observation is **zero field content**: it
is forced by the SYZ44 degree-sum law alone, `gap = δ₂ − δ₁ = S − 2δ₁ ≡ S (mod 2)`.

## Result (this file)

Pure-`ℕ`, axiom-clean, consuming only SYZ44's degree-sum law and SYZ53's exact half-gap identity.

* `gap_parity` — **`δ₂ − δ₁ ≡ (a + b + c) (mod 2)`.**  The parity law forced by `δ₁ + δ₂ = S`; the
  generator gap always shares the parity of the total band degree.  Zero field content.
* `gap_ne_three_of_even` — at even `S`, `gap = 3` is impossible (parity), so the SYZ53 ceiling
  `gap ≤ 3` **collapses to `gap ≤ 2`**: this is *why* the sharp class-true target is `gap ≤ 2`, not
  the slack `gap ≤ 3`.
* `imbalance_le_one_iff_gap_le_two_of_even` — **the corrected interior calibration:** at even `S`,
  `ι ≤ 1 ↔ δ₂ − δ₁ ≤ 2`.  This is the class-true replacement for SYZ54's false `gap ≤ 1`, one unit
  tighter than SYZ53's parity-free `gap ≤ 3` and referee-confirmed across 1500 cells.
* `imbalance_eq_zero_iff_gap_eq_zero_of_even` — **canonical exact-balance form at even `S`:**
  `ι = 0 ↔ gap = 0`.  (Even-`S` parity makes `gap ≤ 1` equivalent to `gap = 0`, so `ι = 0 ↔ gap ≤ 1`
  also holds here — but only because `gap = 1` is vacuous; the honest, non-degenerate exact-balance
  statement is `gap = 0`, and `gap ≤ 1` should not be read as a meaningful exact-balance criterion.)
* `imbalance_eq_one_iff_gap_eq_two_of_even` — pins the referee's gap = 2 witnesses: at even `S`,
  `ι = 1 ↔ gap = 2`.  Confirms `ι = 1` is **attained**, so `ι = 0` is not forced on the even-`S`
  balanced class.
* `imbalance_le_one_iff_gap_le_two_of_hilbert_even` — packaged end-to-end from SYZ44's structural
  inputs (`RankNullity`, `TwoRamp`) at even total degree.

**Why this is new, not a wrapper of SYZ53.**  SYZ53 proves the *parity-free* calibration
`ι ≤ 1 ↔ gap ≤ 3` and the *odd-S-measured* `gap ≤ 1 ⟹ ι = 0`.  This file adds the **parity invariant**
`gap ≡ S (mod 2)` (a genuinely new structural fact about the μ-basis, absent from SYZ53), and uses it
to (i) sharpen the interior target to the class-true `ι ≤ 1 ↔ gap ≤ 2` at even `S`, and (ii) expose
that the SYZ54/SYZ53 exact-balance phrasing `ι = 0 ⟺ gap ≤ 1` degenerates to the honest `gap = 0` on
the even-`S` class (its `gap ≤ 1` is vacuously `gap = 0` there).  The correction is load-bearing: it
stops a downstream lane from formalizing the **false class target** `gap ≤ 1 for all triples`, which
the gap = 2 even-`S` witnesses refute.

**Scope honesty.**  Combinatorial calibration only.  Proves the parity constraint and the corrected
`gap ≤ 2` target *as an equivalence with `ι ≤ 1`*; it does **not** prove that a balanced pairwise
-coprime band triple actually satisfies `gap ≤ 2` (the remaining Hilbert–Burch column-degree
-splitting content — an even-`S` codimension count excluding `gap ≥ 4` — handed to G56/Opus-core).
`ι ≤ 1` closes SYZ44 `uniformSylvester` only at rate `1/2`; production δ* still needs SYZ18 supports,
`hrank` realizability, strip-radius transport, and the MCAThresholdLedger BGK lower bound.  CORE
remains OPEN / ON-BGK; the BGK wall is untouched.
-/

namespace ArkLib.ProximityGap.SYZ68

open ArkLib.ProximityGap

/-! ## 1. The parity law: the generator gap shares the parity of the total band degree -/

/-- **Generator-gap parity (`gap ≡ S mod 2`).**  Under the degree-sum law `δ₁ + δ₂ = a + b + c =: S`
with `δ₁ ≤ δ₂`, the μ-basis generator gap `g = δ₂ − δ₁ = S − 2δ₁` is congruent to `S` modulo `2`.
Purely arithmetic (zero field content): the gap can never have the opposite parity to the total band
degree.  This is the mechanism behind the referee's corrected-instrument observation that odd `S`
gives `gap = 1` while even `S` gives `gap ∈ {0, 2}`. -/
theorem gap_parity
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    (δ₂ - δ₁) % 2 = (a + b + c) % 2 := by
  omega

/-- **Even total degree excludes `gap = 3`.**  When `S = a + b + c` is even, the parity law forbids
`δ₂ − δ₁ = 3`.  Hence the SYZ53 ceiling `gap ≤ 3` collapses to `gap ≤ 2` on the even-`S` class — the
reason the sharp class-true interior target is `gap ≤ 2`, not the slack `gap ≤ 3`. -/
theorem gap_ne_three_of_even
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (heven : (a + b + c) % 2 = 0) :
    δ₂ - δ₁ ≠ 3 := by
  omega

/-! ## 2. The corrected interior calibration `ι ≤ 1 ⟺ gap ≤ 2` at even total degree -/

/-- **Corrected interior target (`ι ≤ 1 ↔ gap ≤ 2` at even `S`).**  Combining SYZ53's parity-free
`ι ≤ 1 ↔ gap ≤ 3` with the parity law (which kills `gap = 3` at even `S`), the balanced-interior
spread branch closes at rate `1/2` exactly when the μ-basis generator gap is at most `2`.  This is
the class-true replacement for SYZ54's **false class target** `gap ≤ 1` (refuted by even-`S`
gap = 2 witnesses): one unit tighter than SYZ53's `gap ≤ 3`,
referee-confirmed field-independently across 1500 cells at both `S`-parities. -/
theorem imbalance_le_one_iff_gap_le_two_of_even
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (heven : (a + b + c) % 2 = 0) :
    SYZ45.imbalance a b c δ₁ ≤ 1 ↔ δ₂ - δ₁ ≤ 2 := by
  unfold SYZ45.imbalance; omega

/-- **Canonical exact-balance form at even `S`: `ι = 0 ↔ gap = 0`.**  On the even-`S` class the
exact-balance statement is `ι = 0 ↔ δ₂ − δ₁ = 0`.  Note the even-`S` parity makes `gap ≤ 1`
*equivalent* to `gap = 0` (so `ι = 0 ↔ gap ≤ 1` is also true here) — but only vacuously, because
`gap = 1` cannot occur; `gap = 0` is the honest, non-degenerate exact-balance criterion, and no
downstream lane should read `gap ≤ 1` as a meaningful exact-balance condition. -/
theorem imbalance_eq_zero_iff_gap_eq_zero_of_even
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (heven : (a + b + c) % 2 = 0) :
    SYZ45.imbalance a b c δ₁ = 0 ↔ δ₂ - δ₁ = 0 := by
  unfold SYZ45.imbalance; omega

/-- **The referee's gap = 2 witness is exactly `ι = 1` at even `S`.**  On the even-`S` balanced class,
`ι = 1 ↔ δ₂ − δ₁ = 2`.  This pins the corrected-instrument witnesses (e.g. `p = 61, a = b = c = 6,
S = 18: (δ₁, δ₂) = (8, 10)`) and certifies that `ι = 1` is **attained** on the class — hence `ι = 0`
must not be assumed forced. -/
theorem imbalance_eq_one_iff_gap_eq_two_of_even
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (heven : (a + b + c) % 2 = 0) :
    SYZ45.imbalance a b c δ₁ = 1 ↔ δ₂ - δ₁ = 2 := by
  unfold SYZ45.imbalance; omega

/-! ## 3. Packaged reduction from SYZ44's structural inputs (even total degree) -/

/-- **Packaged corrected interior calibration.**  From SYZ44's two structural inputs
(`RankNullity hilb a b c D₀` and `TwoRamp hilb δ₁ δ₂`) that yield the degree-sum law, plus
`δ₁ ≤ δ₂` and even total band degree, conclude the class-true interior equivalence
`ι ≤ 1 ↔ δ₂ − δ₁ ≤ 2`.  End-to-end from the Hilbert–Burch structural hypotheses to the corrected
`gap ≤ 2` target. -/
theorem imbalance_le_one_iff_gap_le_two_of_hilbert_even
    (hilb : ℕ → ℕ) (a b c δ₁ δ₂ D₀ : ℕ)
    (hRankNull : SYZ44.RankNullity hilb a b c D₀)
    (hTwoRamp : SYZ44.TwoRamp hilb δ₁ δ₂)
    (hle : δ₁ ≤ δ₂)
    (heven : (a + b + c) % 2 = 0) :
    SYZ45.imbalance a b c δ₁ ≤ 1 ↔ δ₂ - δ₁ ≤ 2 := by
  have hsum : δ₁ + δ₂ = a + b + c :=
    SYZ44.degree_sum_of_hilbert hilb a b c δ₁ δ₂ D₀ hRankNull hTwoRamp
  exact imbalance_le_one_iff_gap_le_two_of_even a b c δ₁ δ₂ hsum hle heven

end ArkLib.ProximityGap.SYZ68

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ68.gap_parity
#print axioms ArkLib.ProximityGap.SYZ68.gap_ne_three_of_even
#print axioms ArkLib.ProximityGap.SYZ68.imbalance_le_one_iff_gap_le_two_of_even
#print axioms ArkLib.ProximityGap.SYZ68.imbalance_eq_zero_iff_gap_eq_zero_of_even
#print axioms ArkLib.ProximityGap.SYZ68.imbalance_eq_one_iff_gap_eq_two_of_even
#print axioms ArkLib.ProximityGap.SYZ68.imbalance_le_one_iff_gap_le_two_of_hilbert_even
