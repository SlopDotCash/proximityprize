/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G267: exact thinness-separation certificate for the adjacent-rank CORE covariance (#466)

G266 realised all four sign quadrants of the adjacent-rank CORE covariance

```text
W_G(x) := #{(y,z) ∈ G² : 2y − z = x},           G = order-n multiplicative subgroup of 𝔽_p^*
R_r(x) := (dp_r ⋆ dp_{r-1})(x)
        = #{(A,B) : A ⊆ G, |A| = r, B ⊆ G, |B| = r-1, (Σ A) − (Σ B) = x}
A_r(n,p) := p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))(Σ_x R_r(x))
```

and closed the cross-rank sign lock and the adjacent-rank forced-sign repairs.  It left ONE repair
OPEN and CORROBORATED, not refuted: the **thinness-positivity bias** — as the 2-power subgroup thins
(`τ := (p−1)/n² → ∞`, the adversarial prize regime) the joint covariance sign appears to collapse to
the `(+,+)` quadrant.  G266 deliberately did NOT dress this as a theorem, because an unconditional
sign law at production primes is exactly the open BGK-hard target and is not what the finite census
proves.

This file certifies the **exact, honest, finite content** of that observation on the enumerated
`n = 8` census: a hard integer **thinness threshold** with a wide verified separation gap.  It is a
*calibrated consumer* of G266's data, not a restatement of the open repair and not a bound at
production primes.

## The certificate (computation of record: `scripts/probes/g267_thinness_separation_census.py`)

Over the 90 genuine `n = 8` cells `17 ≤ p ≤ 2657`, `p ≡ 1 (mod 8)`, with `sgn A₅, sgn A₆` the exact
adjacent-rank covariance signs (float-free), the sign-negative set is **exactly**

```text
{ p = 17  (p−1 = 16,   τ = 0.25),   (−,−)
  p = 73  (p−1 = 72,   τ = 1.125),  (−,−)
  p = 89  (p−1 = 88,   τ = 1.375),  (−,+)
  p = 113 (p−1 = 112,  τ = 1.75) }, (−,−)
```

so **every** sign-negative census cell has `p − 1 ≤ 112` (equivalently `τ ≤ 1.75`), while **every**
census cell with `p − 1 ≥ 136` (`τ ≥ 2.125`) — all 84 of them, up to `p = 2657`, `τ = 41.5` — is
`(+,+)`.  There is a strict separation gap: the last negative sits at `p − 1 = 112` and the census
is uniformly `(+,+)` from `p − 1 = 136` through `p − 1 = 2656`, a thin tail more than 23× beyond the
last sign flip.

## Scope (honest, matching G266)

This is a **finite separation certificate**, NOT a proof of the thinness repair.  It does not bound
`A₅` or `A₆` at production primes and does not claim the `(+,+)` collapse is unconditional.  What it
proves, axiom-cleanly, is that on the enumerated `n = 8` family the sign-negativity is
confined below an explicit integer thinness threshold with a wide verified positive tail — a
precise, monotone, thinness-ordered invariant that sharpens G266's open bias into an exact
recorded separation.  The surviving CORE object is unchanged: the direct row-labelled sponsor
covariance at production thinness.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G267

/-- One `n = 8` census cell: the prime `p`, and the exact adjacent-rank covariance signs recorded as
booleans `A5pos`, `A6pos` (`true` ⇔ the exact integer covariance is `> 0`).  The thinness numerator
is `p − 1 = n²·τ` with `n = 8`; `τ = (p−1)/64`.  All signs are from the float-free probe. -/
structure Cell where
  p : ℕ
  A5pos : Bool
  A6pos : Bool
  deriving DecidableEq

/-- The cell is sign-negative in at least one rank (`¬(+,+)`). -/
def Cell.neg (c : Cell) : Bool := !(c.A5pos && c.A6pos)

/-- The cell is in the `(+,+)` quadrant. -/
def Cell.plusPlus (c : Cell) : Bool := c.A5pos && c.A6pos

/-- The thinness numerator `p − 1 = 64·τ`. -/
def Cell.thinNum (c : Cell) : ℕ := c.p - 1

/-- The exact `n = 8` census: 90 genuine cells `17 ≤ p ≤ 2657`, `p ≡ 1 (mod 8)`, with the exact
adjacent-rank covariance signs from `scripts/probes/g267_thinness_separation_census.py`.  Only the
four cells `p ∈ {17, 73, 89, 113}` are sign-negative; every other cell is `(+,+)`. -/
def census : List Cell :=
  [ ⟨17, false, false⟩, ⟨41, true, true⟩, ⟨73, false, false⟩, ⟨89, false, true⟩,
    ⟨97, true, true⟩, ⟨113, false, false⟩, ⟨137, true, true⟩, ⟨193, true, true⟩,
    ⟨233, true, true⟩, ⟨241, true, true⟩, ⟨257, true, true⟩, ⟨281, true, true⟩,
    ⟨313, true, true⟩, ⟨337, true, true⟩, ⟨353, true, true⟩, ⟨401, true, true⟩,
    ⟨409, true, true⟩, ⟨433, true, true⟩, ⟨449, true, true⟩, ⟨457, true, true⟩,
    ⟨521, true, true⟩, ⟨569, true, true⟩, ⟨577, true, true⟩, ⟨593, true, true⟩,
    ⟨601, true, true⟩, ⟨617, true, true⟩, ⟨641, true, true⟩, ⟨673, true, true⟩,
    ⟨761, true, true⟩, ⟨769, true, true⟩, ⟨809, true, true⟩, ⟨857, true, true⟩,
    ⟨881, true, true⟩, ⟨929, true, true⟩, ⟨937, true, true⟩, ⟨953, true, true⟩,
    ⟨977, true, true⟩, ⟨1009, true, true⟩, ⟨1033, true, true⟩, ⟨1049, true, true⟩,
    ⟨1097, true, true⟩, ⟨1129, true, true⟩, ⟨1153, true, true⟩, ⟨1193, true, true⟩,
    ⟨1201, true, true⟩, ⟨1217, true, true⟩, ⟨1249, true, true⟩, ⟨1289, true, true⟩,
    ⟨1297, true, true⟩, ⟨1321, true, true⟩, ⟨1361, true, true⟩, ⟨1409, true, true⟩,
    ⟨1433, true, true⟩, ⟨1481, true, true⟩, ⟨1489, true, true⟩, ⟨1553, true, true⟩,
    ⟨1601, true, true⟩, ⟨1609, true, true⟩, ⟨1657, true, true⟩, ⟨1697, true, true⟩,
    ⟨1721, true, true⟩, ⟨1753, true, true⟩, ⟨1777, true, true⟩, ⟨1801, true, true⟩,
    ⟨1873, true, true⟩, ⟨1889, true, true⟩, ⟨1913, true, true⟩, ⟨1993, true, true⟩,
    ⟨2017, true, true⟩, ⟨2081, true, true⟩, ⟨2089, true, true⟩, ⟨2113, true, true⟩,
    ⟨2129, true, true⟩, ⟨2137, true, true⟩, ⟨2153, true, true⟩, ⟨2161, true, true⟩,
    ⟨2273, true, true⟩, ⟨2281, true, true⟩, ⟨2297, true, true⟩, ⟨2377, true, true⟩,
    ⟨2393, true, true⟩, ⟨2417, true, true⟩, ⟨2441, true, true⟩, ⟨2473, true, true⟩,
    ⟨2521, true, true⟩, ⟨2593, true, true⟩, ⟨2609, true, true⟩, ⟨2617, true, true⟩,
    ⟨2633, true, true⟩, ⟨2657, true, true⟩ ]

/-- The census has exactly 90 cells. -/
theorem census_length : census.length = 90 := by decide

/-- The explicit integer thinness threshold: every sign-negative census cell has `p − 1 ≤ 112`
(equivalently `τ ≤ 1.75`).  This is the hard separation constant. -/
def thinThreshold : ℕ := 112

/-- **Thinness confinement of sign-negativity.**  Every sign-negative cell in the `n = 8` census has
thinness numerator `p − 1 ≤ 112` (`τ ≤ 1.75`).  So sign flips are confined below the explicit
thinness threshold; there is no negative cell in the thin tail. -/
theorem neg_cells_below_threshold :
    ∀ c ∈ census, c.neg = true → c.thinNum ≤ thinThreshold := by decide

/-- **Thin tail is uniformly `(+,+)`.**  Every census cell with thinness numerator `p − 1 ≥ 136`
(`τ ≥ 2.125`) lies in the `(+,+)` quadrant.  Combined with `neg_cells_below_threshold` this exhibits
a strict separation gap `(112, 136)` between the last sign flip and the start of the verified thin
tail. -/
theorem thin_tail_plusPlus :
    ∀ c ∈ census, 136 ≤ c.thinNum → c.plusPlus = true := by decide

/-- The sign-negative cells are exactly the four primes `{17, 73, 89, 113}`. -/
theorem neg_cells_are_exactly :
    census.filter Cell.neg = [⟨17, false, false⟩, ⟨73, false, false⟩,
      ⟨89, false, true⟩, ⟨113, false, false⟩] := by decide

/-- There are exactly four sign-negative cells in the census. -/
theorem neg_cells_count : (census.filter Cell.neg).length = 4 := by decide

/-- The verified thin `(+,+)` tail reaches `p = 2657`, i.e. `p − 1 = 2656`, `τ = 41.5`.  The
separation gap above the last negative (`p − 1 = 112`) is more than 23-fold. -/
theorem thin_tail_reaches_2656 :
    ∃ c ∈ census, c.plusPlus = true ∧ c.thinNum = 2656 := by decide

/-- **Monotone thinness separation (packaged).**  On the `n = 8` census the sign-negative set is
confined to `p − 1 ≤ 112`, the region `p − 1 ≥ 136` is uniformly `(+,+)`, and the positive tail is
verified up to `p − 1 = 2656`.  A precise, thinness-ordered separation certificate — NOT a bound at
production primes; the thinness repair remains OPEN / ON-BGK. -/
theorem thinness_separation_census :
    (∀ c ∈ census, c.neg = true → c.thinNum ≤ 112) ∧
    (∀ c ∈ census, 136 ≤ c.thinNum → c.plusPlus = true) ∧
    (∃ c ∈ census, c.plusPlus = true ∧ c.thinNum = 2656) :=
  ⟨neg_cells_below_threshold, thin_tail_plusPlus, thin_tail_reaches_2656⟩

end ArkLib.ProximityGap.Frontier.G267
