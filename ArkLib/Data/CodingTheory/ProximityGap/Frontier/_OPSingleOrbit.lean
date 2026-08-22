/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# `_OPSingleOrbit` — the `O_P = 1` single-orbit persistence is REFUTED (#444)

## Attack [OP-single-orbit] — verdict: REFUTED (O_P grows as `n/8 − 1`).

The far-line MCA binding direction `x^{n/2+1} + γ·x^{n/2-1}` on `μ_n` has incidence
`#bad γ = (n/d)·O_P + [γ = 0]`, where `O_P` is the number of distinct Schur-ratio
dilation orbits of bad scalars (`MonomialGammaFibration`). The single-orbit hope is
`O_P = 1` for all `n = 2^μ` (so `#bad = 1 + n/d ≤ n`, an off-BGK closure of the far horn).
It was machine-confirmed `O_P = 1` for `n ≤ 16` (`DeltaStarOP1BindingN16.lean`).

**This file refutes `O_P = 1` for `n ≥ 32`.** At the binding "level-set `= n/2`" rung,
the bad scalars descend (even polynomial → `y = x²` → clear → monic quartic that must split
over `μ_m`, `m = n/2`) to the `e₂ = 0` four-subsets of `ℤ/m` with `e₁ ≠ 0`, counted up to the
dilation/shift `J ↦ J + 1`. We compute that orbit count exactly (two independent ways —
cyclotomic and direct-field — `scripts/probes/_probe_444_OP_e2vanish_tower.py`,
`_probe_444_OP_field_descent.py`):

> **`O_P = m/4 − 1 = n/8 − 1`** (machine-verified, `m = 8,16,32,64,128`).

The `n = 16` result `O_P = 1` is exactly the boundary case `m = 8`: `m/4 − 1 = 1`. For
`n = 32` (`m = 16`) the count is `3`; `n = 64` gives `7`; `n = 128` gives `15`. So the
single-orbit persistence FAILS — the binding far-line has a GROWING number of dilation orbits.

The clean structural reason (verified `m = 8…64`): the nonzero `e₂ = 0` four-subsets of `ℤ/m`,
modulo shift, are EXACTLY the `m/4 − 1` orbits with representatives `{0, j, 2j, h+j}` for
`j = 1, …, m/4 − 1` (`h = m/2`) — one antipodal pair `{j, j+h}` welded to a "doubling" pair
`{0, 2j}`. Each orbit has full size `m = n/2`, giving the binding `#bad = (m/4 − 1)·m + 1 ≈ n²/8`,
which **exceeds the budget `n`** for all `n ≥ 32` (the single-orbit off-BGK closure cannot hold).

## What is `decide`-certified here (axiom-clean, NOT `native_decide`)

Exhaustive `powersetCard`/quantified `decide` over `ℤ/16` is kernel-infeasible, so we certify the
refutation by an explicit *witness triple*: three concrete binding configurations
`{0,1,2,9}`, `{0,2,4,10}`, `{0,3,6,11}` (the `{0,j,2j,h+j}` reps, `h = 8`, `j = 1,2,3`), each
satisfying `e₂ = 0`, `e₁ ≠ 0`, lying in pairwise-DISTINCT shift orbits, each of full orbit size
`16`. Three distinct full orbits ⟹ `O_P ≥ 3 > 1`. This refutes `O_P = 1` at `n = 32`.

NOTE (honest scope). The exact closed form `O_P = n/8 − 1` (all `n = 2^μ`) is verified
exhaustively for `m ≤ 128` and explained structurally; what is `decide`-proved below is the
sufficient refuting witness `O_P ≥ 3` at `n = 32`. The demand-floor reduction
`O_P ≤ C(n/2, r−1)` (`DemandFloorReduction.lean`) is NOT affected: `n/8 − 1 ≤ C(n/2, 3)` with
vast slack — only the strictly stronger `O_P = 1` single-orbit claim dies.
See `docs/kb/deltastar-444-OP-single-orbit-refuted.md`.
-/

namespace ArkLib.ProximityGap.OPSingleOrbit

open Finset

set_option maxRecDepth 10000

/-- Pairwise-sum multiplicity of a 4-subset `J ⊆ ℤ/16` at residue `r`. -/
def pairMult (J : Finset (ZMod 16)) (r : ZMod 16) : ℕ :=
  ((powersetCard 2 J).filter (fun s => s.sum id = r)).card

/-- The char-0 (cyclotomic) condition `e₂(J) = 0` on `μ_16`: pairwise-sum multiplicities are
antipodally balanced, `M_r = M_{r+8}`. Over `ℚ(ζ₁₆)` this is `∑_{pairs} ζ^{i+j} = 0` since
`ζ₁₆⁸ = -1`. -/
abbrev e2vanish (J : Finset (ZMod 16)) : Prop :=
  ∀ r : ZMod 16, pairMult J r = pairMult J (r + 8)

/-- `e₁(J) = 0`: `J` is closed under the antipodal map `x ↦ x + 8` (mult by `-1` on `μ_16`);
the cyclotomic sum `∑_{j∈J} ζ^j` then vanishes (antipodal pairs cancel). The `γ = 0` configs. -/
abbrev e1zero (J : Finset (ZMod 16)) : Prop := J.image (· + 8) = J

/-- The dilation / shift action `J ↦ J + 1` (multiplication by `ζ₁₆`). -/
def shift (J : Finset (ZMod 16)) : Finset (ZMod 16) := J.image (· + 1)

/-- The three orbit representatives of the nonzero binding configurations at `n = 32`
(`m = 16`), of the structural form `{0, j, 2j, h+j}`, `h = 8`, `j = 1, 2, 3`. -/
def base1 : Finset (ZMod 16) := {0, 1, 2, 9}
def base2 : Finset (ZMod 16) := {0, 2, 4, 10}
def base3 : Finset (ZMod 16) := {0, 3, 6, 11}

/-- Each witness is a genuine `e₂ = 0` four-subset (the cyclotomic binding condition). -/
theorem base1_e2vanish : e2vanish base1 := by decide
theorem base2_e2vanish : e2vanish base2 := by decide
theorem base3_e2vanish : e2vanish base3 := by decide

/-- Each witness has `e₁ ≠ 0` (it is NOT antipodally closed), so `γ ≠ 0`: a genuine bad scalar. -/
theorem base1_e1nz : ¬ e1zero base1 := by decide
theorem base2_e1nz : ¬ e1zero base2 := by decide
theorem base3_e1nz : ¬ e1zero base3 := by decide

/-- The three witnesses lie in PAIRWISE DISTINCT shift orbits: no shift-iterate of one equals
another. (Checked over all `16` iterates — the orbit period divides `16`.) -/
theorem bases_distinct_orbits :
    (∀ t : Fin 16, base1 ≠ shift^[t.val] base2) ∧
    (∀ t : Fin 16, base1 ≠ shift^[t.val] base3) ∧
    (∀ t : Fin 16, base2 ≠ shift^[t.val] base3) := by decide

/-- Each witness has FULL orbit size `16 = n/2`: its `16` shift-iterates are pairwise distinct.
So each base spans a full `n/2`-orbit of bad scalars. -/
theorem base1_orbit_full :
    ((Finset.univ : Finset (Fin 16)).image (fun t => shift^[t.val] base1)).card = 16 := by decide
theorem base2_orbit_full :
    ((Finset.univ : Finset (Fin 16)).image (fun t => shift^[t.val] base2)).card = 16 := by decide
theorem base3_orbit_full :
    ((Finset.univ : Finset (Fin 16)).image (fun t => shift^[t.val] base3)).card = 16 := by decide

/-- **The refutation of `O_P = 1` at `n = 32` (`m = 16`).** There are at least THREE distinct
Schur-ratio dilation orbits of bad scalars at the binding far-line: three genuine binding
configurations (`e₂ = 0`, `e₁ ≠ 0`), each of full orbit size `16`, lying in pairwise-distinct
orbits. Hence `O_P ≥ 3 > 1`: the single-orbit persistence (`O_P = 1`, which holds at `n ≤ 16`)
is FALSE at `n = 32`. -/
theorem OP_single_orbit_refuted :
    -- three genuine binding configs (e₂ = 0, e₁ ≠ 0)
    (e2vanish base1 ∧ ¬ e1zero base1) ∧
    (e2vanish base2 ∧ ¬ e1zero base2) ∧
    (e2vanish base3 ∧ ¬ e1zero base3) ∧
    -- each spans a full n/2 = 16 orbit
    ((Finset.univ : Finset (Fin 16)).image (fun t => shift^[t.val] base1)).card = 16 ∧
    ((Finset.univ : Finset (Fin 16)).image (fun t => shift^[t.val] base2)).card = 16 ∧
    ((Finset.univ : Finset (Fin 16)).image (fun t => shift^[t.val] base3)).card = 16 ∧
    -- in pairwise-distinct orbits ⟹ at least 3 orbits ⟹ O_P ≥ 3 > 1
    (∀ t : Fin 16, base1 ≠ shift^[t.val] base2) ∧
    (∀ t : Fin 16, base1 ≠ shift^[t.val] base3) ∧
    (∀ t : Fin 16, base2 ≠ shift^[t.val] base3) :=
  ⟨⟨base1_e2vanish, base1_e1nz⟩, ⟨base2_e2vanish, base2_e1nz⟩, ⟨base3_e2vanish, base3_e1nz⟩,
   base1_orbit_full, base2_orbit_full, base3_orbit_full,
   bases_distinct_orbits.1, bases_distinct_orbits.2.1, bases_distinct_orbits.2.2⟩

-- Axiom audit: must be a subset of [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms OP_single_orbit_refuted

end ArkLib.ProximityGap.OPSingleOrbit
