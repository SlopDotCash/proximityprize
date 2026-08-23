/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean

/-!
# Loop 8 (O6) — the disproof reduces to a `q`-growing GS list size below capacity

The earlier loops (O3/O4/O6-naive) attacked the *fixed-field* surface
`epsMCAgs_prizeBound_conjecture`, which is **already a theorem**
(`GrandChallenge141UniformResolved.epsMCAgs_prizeBound_conjecture_holds`): there the constants are
chosen *after* the field, so `c₃ = n` with `(15/16)^n ≤ 1/q` absorbs `q`. The concurrent Loop 7
self-refutation (`η ≲ A/d` absorbed by the permitted `η^{-c₃}` factor) is the same phenomenon.

The genuine open prize is `epsMCAgsPrizeUniversalConjecture` / `UniversalGSListMassBound`, where the
constant triple `c₁,c₂,c₃` is fixed **before the field**. Its proof chain (all proved in-tree,
`MCAGSWitness.lean`) is

    PivotCovering ∧ (∀u, |L u| ≤ ℓ)  ⟹  epsMCAgs ≤ ℓ/q  ⟹  (if ℓ/q ≤ bound) mass bound,

with `bound = epsMCAgsPrizeBound q m ρ η c₁ c₂ c₃ = (1/q)·(2^m)^{c₁}/(ρ^{c₂}η^{c₃})`. The decisive
observation: the mass clause `ℓ/q ≤ (1/q)·B` cancels the `1/q` on both sides, so it forces

    ℓ ≤ B,   where  B = (2^m)^{c₁}/(ρ^{c₂}η^{c₃})  is **independent of `q`**.

Because the universal quantifier order fixes `(c₁,c₂,c₃)` — hence `B` — before the field, **the GS
list size must be bounded by a constant independent of `q`** at every prize rate and gap. Therefore:

> **Disproof reduction (O6).** If, at some prize rate `ρ` and fixed gap `η > 0`, the minimal
> pivot-covering faithful GS list size at radius `δ = 1−ρ−η` grows without bound as `q → ∞`, then no
> universal constant triple works and `UniversalGSListMassBound` (hence the prize) is **false**.

This is exactly the dual of the open Reed–Solomon problem: *list-decodability up to capacity with
`q`-independent list size below `1−ρ`*. This file proves the `q`-independence extraction and the
refutation arithmetic, sorry-free and axiom-clean.

**Disproof of the disproof (O6).** The antecedent — a `q`-unbounded list size at a prize rate and a
*fixed* gap `η` (radius strictly below capacity) — is not established. Below the Johnson radius the
list is provably `q`-independent (Johnson/BCIKS); in the band `(1−√ρ, 1−ρ−η]` the known RS
list-size lower bounds either need radius `≥` capacity or pathological fields whose status at a
*fixed positive* gap is open. The verified `ε_mca` lower bounds in-tree are only `poly/q` (within the
permitted bound), so they do not refute. O6 sharpens the target to a list-decoding lower bound but
does not disprove. See `DISPROOF_LOG.md` (O6).
-/

namespace ArkLib.ProximityGap.DisproofLoop8

open scoped Real

/-- **`q`-independence extraction.** If a list size `ℓ` clears the prize mass bound
`ℓ/q ≤ (1/q)·B` over a field of size `q > 0`, then `ℓ ≤ B` — the bound on `ℓ` is independent of
`q`. (`1/q` cancels.) -/
theorem listsize_le_numerator_of_mass
    {ℓ q B : ℝ} (hq : 0 < q) (hmass : ℓ / q ≤ (1 / q) * B) :
    ℓ ≤ B := by
  rw [div_eq_inv_mul, one_div] at hmass
  -- `q⁻¹ · ℓ ≤ q⁻¹ · B`, cancel the positive factor `q⁻¹`
  have hinv : 0 < q⁻¹ := inv_pos.mpr hq
  exact le_of_mul_le_mul_left hmass hinv

/-- **List-size growth refutes the mass bound.** If `ℓ > B` (the list size exceeds the
`q`-independent numerator), the mass clause `ℓ/q ≤ (1/q)·B` fails, for any `q > 0`. -/
theorem listsize_gt_numerator_refutes_mass
    {ℓ q B : ℝ} (hq : 0 < q) (hgt : B < ℓ) :
    ¬ (ℓ / q ≤ (1 / q) * B) := by
  intro hmass
  exact (not_le_of_gt hgt) (listsize_le_numerator_of_mass hq hmass)

/-- **The punchline of O6.** For any fixed `q`-independent numerator `B` (i.e. any candidate
universal constant triple, which determines `B` before the field is chosen), a sufficiently large
list size exceeds it: `∃ ℓ, B < ℓ`. Combined with `listsize_gt_numerator_refutes_mass`, a list size
that grows without bound as `q → ∞` eventually breaks the mass bound for that fixed `B` — disproving
the universal conjecture. The remaining (open) content is realizing such growth at a prize rate and
fixed gap. -/
theorem listsize_can_exceed_any_numerator (B : ℝ) : ∃ ℓ : ℕ, B < (ℓ : ℝ) :=
  exists_nat_gt B

/-- **Quantitative refutation skeleton.** Suppose at every field size in a sequence `q` the minimal
faithful pivot-covering GS list size is `ℓ(q)`, and the universal conjecture supplies a fixed
numerator `B`. If for *some* `q > 0` we have `ℓ(q) > B`, the universal bound is violated at that
field. This packages the reduction in one implication: a single over-the-numerator instance kills a
candidate constant triple. -/
theorem single_instance_over_numerator_refutes
    {ℓ q B : ℝ} (hq : 0 < q) (hgt : B < ℓ)
    (hmass : ℓ / q ≤ (1 / q) * B) : False :=
  listsize_gt_numerator_refutes_mass hq hgt hmass

end ArkLib.ProximityGap.DisproofLoop8
