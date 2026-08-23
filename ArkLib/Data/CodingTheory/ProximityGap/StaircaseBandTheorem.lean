/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarLiteralEps

/-!
# The staircase BAND THEOREM: `δ* = e/n` on EVERY sub-saturation band (#357, round 3a)

Round 2 (`MCADeltaStarLiteralEps.lean`) pinned the first rung: for any RS code over a
field of size `q ∈ (2¹²⁸, 2¹²⁹)`, `mcaDeltaStar(RS, 2⁻¹²⁸) = 1/n`.  This file proves
the **general band theorem**: ONE theorem giving the exact staircase value of `δ*` at
the literal challenge error `ε* = 2⁻¹²⁸` on **every** band of `q` within the ladder's
reach.  For every rung `e ≥ 1`:

  `q ∈ [e·2¹²⁸, (e+1)·2¹²⁸)  ⟹  mcaDeltaStar(RS[F, dom, k], 2⁻¹²⁸) = e/n`

(`mcaDeltaStar_staircase_band`), valid whenever `3(e−1) + k ≤ n` and `e + 1 + k ≤ n`.

**The staircase law, normalized as proven.**  With `Λ(e) :=` the worst-case number of
bad scalars at radii strictly inside `e/n`, the in-tree ladder certifies `Λ(e) = e`
exactly (collapse `badScalars_card_le`: ≤ `e` bad scalars whenever `δ·n < e`; spike
floor: `e + 1` bad scalars materialize at `δ·n = e`).  The staircase law

  `δ*(RS, ε*) = max { e/n : Λ(n, k, e) ≤ ε*·q }`

then reads: `δ* = e/n` exactly on the budget band `ε*·q ∈ [e, e+1)`.  At the literal
`ε* = 2⁻¹²⁸` the budget band is the field-size band `q ∈ [e·2¹²⁸, (e+1)·2¹²⁸)` — the
two band-arithmetic lemmas `band_lo_general` / `band_hi_general` below are exactly
this translation, and the ladder (`mcaDeltaStar_rs_eq_granularity`,
`GranularityLadderRS.lean`) supplies both rungs `Λ(e) = e` (good side) and
`Λ(e+1) = e+1 > ε*·q` (bad side, the `(e+1)`-spike stack).  Round 2's rung-1 pin is
the `e = 1` instance (re-derived as a consistency `example` below); this theorem turns
the staircase law from per-rung verification into a THEOREM on the whole
sub-saturation region.

**Validity region (satisfiability — these hypotheses are jointly realizable).**
* `e = 1, n = 2²⁵, k = 2²⁴, q` any prime in `[2¹²⁸, 2¹²⁹)` — the round-2 pin; the
  non-strict lower edge now also admits the binary field `GF(2¹²⁸)` (`q = 2¹²⁸`
  exactly, where `ε* = 1/q` sits on the closed band edge).
* General `e`: at production shape `n = 2²⁵, k = 2²⁴` the distance conditions
  `3(e−1) + 2²⁴ ≤ 2²⁵` and `e + 1 + 2²⁴ ≤ 2²⁵` hold for ALL `1 ≤ e ≤ 5 592 406`
  (`mcaDeltaStar_production_shape_staircase`), i.e. for every field size
  `q < 5 592 407 · 2¹²⁸ ≈ 2¹⁵⁰·⁴`.  Primes exist in every band `[e·2¹²⁸, (e+1)·2¹²⁸)`
  in abundance (PNT: the band has width `2¹²⁸` at height `< 2¹⁵¹`, so contains
  `≈ 2¹²⁸/151·ln 2` primes); per repo convention the prime stays abstract with the two
  band bounds as hypotheses.
* The general validity region: every `(e, q, n, k)` with `1 ≤ e`,
  `3(e−1) + k ≤ n`, `e + 1 + k ≤ n`, `e·2¹²⁸ ≤ q < (e+1)·2¹²⁸`.

**Honest scope (the saturation boundary).**  The ladder's distance condition caps the
reach at `e ≲ (n−k)/3`, i.e. `q ≲ ((n−k)/3)·2¹²⁸`.  Beyond that band (production
parameterization has `q ≥ n²·2¹²⁸`, budget `ε*·q ≥ n²`) the staircase's certified
rungs run out and `Λ`'s growth through the Johnson window is exactly the open core —
this theorem completes the sub-saturation side and does **not** touch the prize
window `(1−√ρ, 1−ρ)`.  Note also `δ* = e/n ≤ (n−k)/(3n) < 1−ρ` throughout the region,
consistent with the half-distance ceiling.

All results are `sorry`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (round-2 synthesis: the staircase-law hypothesis; this file = round 3a).
- `GranularityLadderRS.lean` (the general-ε* ladder `mcaDeltaStar_rs_eq_granularity`),
  `UniversalStaircaseCollapse.lean` (good side `Λ(e) ≤ e`),
  `UniversalSpikeFloor.lean` (bad side, the `(e+1)`-spike),
  `MCADeltaStarLiteralEps.lean` (the `e = 1` rung; `smoothDom`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.StaircaseBandTheorem

open ProximityGap.SpikeFloor ProximityGap.MCADeltaStarLiteralEps

/-! ## Band arithmetic: `2⁻¹²⁸` sits in the `e`-th ladder window `[e/q, (e+1)/q)` iff
`e·2¹²⁸ ≤ q < (e+1)·2¹²⁸` -/

/-- Lower band edge, general rung: `e/q ≤ 2⁻¹²⁸` whenever `e·2¹²⁸ ≤ q` (and `e ≥ 1`). -/
theorem band_lo_general {e q : ℕ} (he : 1 ≤ e) (hqlo : e * 2 ^ 128 ≤ q) :
    ((e : ℕ) : ℝ≥0∞) / (q : ℝ≥0∞) ≤ 1 / 2 ^ 128 := by
  have he0 : ((e : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp he
  have heT : ((e : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top e
  calc ((e : ℕ) : ℝ≥0∞) / (q : ℝ≥0∞)
      ≤ ((e : ℕ) : ℝ≥0∞) / (((e : ℕ) : ℝ≥0∞) * 2 ^ 128) :=
        ENNReal.div_le_div le_rfl (by exact_mod_cast hqlo)
    _ = ((e : ℕ) : ℝ≥0∞) * 1 / (((e : ℕ) : ℝ≥0∞) * 2 ^ 128) := by rw [mul_one]
    _ = 1 / 2 ^ 128 := ENNReal.mul_div_mul_left 1 (2 ^ 128) he0 heT

/-- Upper band edge, general rung: `2⁻¹²⁸ < (e+1)/q` whenever `q < (e+1)·2¹²⁸`. -/
theorem band_hi_general {e q : ℕ} (hqhi : q < (e + 1) * 2 ^ 128) :
    (1 / 2 ^ 128 : ℝ≥0∞) < ((e + 1 : ℕ) : ℝ≥0∞) / (q : ℝ≥0∞) := by
  have he0 : ((e + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero e
  have heT : ((e + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have key : (1 / 2 ^ 128 : ℝ≥0∞)
      = ((e + 1 : ℕ) : ℝ≥0∞) / (((e + 1 : ℕ) : ℝ≥0∞) * 2 ^ 128) := by
    rw [show ((e + 1 : ℕ) : ℝ≥0∞) / (((e + 1 : ℕ) : ℝ≥0∞) * 2 ^ 128)
        = ((e + 1 : ℕ) : ℝ≥0∞) * 1 / (((e + 1 : ℕ) : ℝ≥0∞) * 2 ^ 128) from by
      rw [mul_one]]
    rw [ENNReal.mul_div_mul_left 1 (2 ^ 128) he0 heT]
  rw [key]
  exact ENNReal.div_lt_div_left he0 heT (by exact_mod_cast hqhi)

/-! ## The general band theorem -/

section General

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE STAIRCASE BAND THEOREM** — `δ* = e/n` exactly on every sub-saturation band,
at the literal challenge error `ε* = 2⁻¹²⁸`.  For every rung `e ≥ 1`, any field `F`
with `e·2¹²⁸ ≤ |F| < (e+1)·2¹²⁸`, any injective evaluation domain of size `n`, any
dimension `k` with `3(e−1) + k ≤ n` and `e + 1 + k ≤ n`:

  `mcaDeltaStar (RS[F, dom, k]) 2⁻¹²⁸ = e/n`.

Good side (`Λ(e) = e`): every `δ < e/n` has `ε_mca ≤ e/|F| ≤ 2⁻¹²⁸`.  Bad side
(`Λ(e+1) = e+1`): at `δ = e/n` the `(e+1)`-bad-scalar spike stack forces
`ε_mca ≥ (e+1)/|F| > 2⁻¹²⁸`.  This is the `j = e` band of the granularity ladder,
whose window `[e/|F|, (e+1)/|F|)` contains `2⁻¹²⁸` exactly because
`e·2¹²⁸ ≤ |F| < (e+1)·2¹²⁸`.  The round-2 rung-1 pin (`mcaDeltaStar_eq_inv_n`) is the
`e = 1` instance. -/
theorem mcaDeltaStar_staircase_band (dom : Fin n ↪ F) {k e : ℕ} (he : 1 ≤ e)
    (hd3 : 3 * (e - 1) + k ≤ n) (hde : e + 1 + k ≤ n)
    (hqlo : e * 2 ^ 128 ≤ Fintype.card F)
    (hqhi : Fintype.card F < (e + 1) * 2 ^ 128) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))
        (1 / 2 ^ 128 : ℝ≥0∞)
      = (e : ℝ≥0) / (n : ℝ≥0) := by
  have hjF : e + 1 ≤ Fintype.card F := by
    have h1 : e + 1 ≤ e * 2 := by omega
    have h2 : e * 2 ≤ e * 2 ^ 128 := by
      exact Nat.mul_le_mul_left e (by norm_num)
    exact le_trans h1 (le_trans h2 hqlo)
  have h := mcaDeltaStar_rs_eq_granularity dom (k := k) (j := e) he hd3 hde hjF
    (band_lo_general he hqlo) (band_hi_general hqhi)
  rwa [Fintype.card_fin] at h

/-- Consistency check: the round-2 rung-1 pin (`mcaDeltaStar_eq_inv_n`,
`MCADeltaStarLiteralEps.lean`) is the `e = 1` instance of the band theorem — with the
band edge now closed at `q = 2¹²⁸` (so `GF(2¹²⁸)` itself is covered). -/
example (dom : Fin n ↪ F) {k : ℕ} (hkn : k + 2 ≤ n)
    (hqlo : 2 ^ 128 ≤ Fintype.card F) (hqhi : Fintype.card F < 2 ^ 129) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))
        (1 / 2 ^ 128 : ℝ≥0∞)
      = 1 / (n : ℝ≥0) := by
  have h := mcaDeltaStar_staircase_band dom (k := k) (e := 1) le_rfl
    (by omega) (by omega)
    (by simpa using hqlo)
    (by rw [show (1 + 1) * 2 ^ 128 = 2 ^ 129 from by norm_num]; exact hqhi)
  rwa [Nat.cast_one] at h

end General

/-! ## Prime fields and smooth domains -/

section Prime

variable (p : ℕ) [Fact (Nat.Prime p)]

open Classical in
/-- The band theorem over a prime field: any rung `e ≥ 1`, any prime
`e·2¹²⁸ ≤ p < (e+1)·2¹²⁸` (PNT puts `≈ 2¹²⁸/ln p` primes in every such band; the
prime stays abstract with the two band bounds as hypotheses, the repo convention),
any injective domain of size `n`, any `k` with `3(e−1) + k ≤ n` and `e + 1 + k ≤ n`:

  `mcaDeltaStar (RS[F_p, dom, k]) 2⁻¹²⁸ = e/n`. -/
theorem mcaDeltaStar_staircase_band_zmod {e : ℕ} (he : 1 ≤ e)
    (hplo : e * 2 ^ 128 ≤ p) (hphi : p < (e + 1) * 2 ^ 128)
    {n : ℕ} [NeZero n] (dom : Fin n ↪ ZMod p) {k : ℕ}
    (hd3 : 3 * (e - 1) + k ≤ n) (hde : e + 1 + k ≤ n) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        ((rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)) : Set (Fin n → ZMod p))
        (1 / 2 ^ 128 : ℝ≥0∞)
      = (e : ℝ≥0) / (n : ℝ≥0) := by
  refine mcaDeltaStar_staircase_band dom he hd3 hde ?_ ?_ <;>
    rw [ZMod.card] <;> assumption

open Classical in
/-- **The band theorem for smooth-domain Reed–Solomon** — the prize's code shape on
every sub-saturation band: prime field `e·2¹²⁸ ≤ p < (e+1)·2¹²⁸`, evaluation domain
the cyclic 2-power group `⟨g⟩` of order `n = 2^μ`, any dimension `k` with the rung-`e`
slack `3(e−1) + k ≤ 2^μ` and `e + 1 + k ≤ 2^μ`:

  `mcaDeltaStar (RS[F_p, ⟨g⟩, k]) 2⁻¹²⁸ = e/2^μ`. -/
theorem mcaDeltaStar_staircase_band_smooth {e : ℕ} (he : 1 ≤ e)
    (hplo : e * 2 ^ 128 ≤ p) (hphi : p < (e + 1) * 2 ^ 128)
    {μ : ℕ} (g : (ZMod p)ˣ) (hg : orderOf g = 2 ^ μ) {k : ℕ}
    (hd3 : 3 * (e - 1) + k ≤ 2 ^ μ) (hde : e + 1 + k ≤ 2 ^ μ) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        ((rsCode (smoothDom p g hg) k :
            Submodule (ZMod p) (Fin (2 ^ μ) → ZMod p)) : Set (Fin (2 ^ μ) → ZMod p))
        (1 / 2 ^ 128 : ℝ≥0∞)
      = (e : ℝ≥0) / ((2 ^ μ : ℕ) : ℝ≥0) := by
  haveI : NeZero (2 ^ μ) := ⟨pow_ne_zero μ (by norm_num)⟩
  exact mcaDeltaStar_staircase_band_zmod p he hplo hphi (smoothDom p g hg) hd3 hde

open Classical in
/-- **Production shape, ALL bands:** `n = 2²⁵`, `k = 2²⁴` (rate `1/2`), smooth domain
`⟨g⟩` of order `2²⁵`, ANY rung `1 ≤ e ≤ 5 592 406` and any prime `p` in the `e`-th
band `[e·2¹²⁸, (e+1)·2¹²⁸)`:

  `mcaDeltaStar (RS[F_p, ⟨g⟩, 2²⁴]) 2⁻¹²⁸ = e/2²⁵`.

The complete staircase at production block length and rate: as the field grows
through the bands `q ≈ e·2¹²⁸`, `δ*` climbs the staircase `e/2²⁵` rung by rung, up to
the saturation rung `e = 5 592 406` (where `3(e−1)` exhausts the distance budget
`n − k = 2²⁴`; field sizes up to `≈ 2¹⁵⁰·⁴`).  Beyond saturation the certified rungs
run out — that regime (production has `q ≥ n²·2¹²⁸`) is the open core. -/
theorem mcaDeltaStar_production_shape_staircase {e : ℕ}
    (he : 1 ≤ e) (hemax : e ≤ 5592406)
    (hplo : e * 2 ^ 128 ≤ p) (hphi : p < (e + 1) * 2 ^ 128)
    (g : (ZMod p)ˣ) (hg : orderOf g = 2 ^ 25) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        ((rsCode (smoothDom p g hg) (2 ^ 24) :
            Submodule (ZMod p) (Fin (2 ^ 25) → ZMod p)) : Set (Fin (2 ^ 25) → ZMod p))
        (1 / 2 ^ 128 : ℝ≥0∞)
      = (e : ℝ≥0) / ((2 ^ 25 : ℕ) : ℝ≥0) :=
  mcaDeltaStar_staircase_band_smooth p he hplo hphi g hg
    (by norm_num; omega) (by norm_num; omega)

end Prime

end ProximityGap.StaircaseBandTheorem

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.StaircaseBandTheorem.band_lo_general
#print axioms ProximityGap.StaircaseBandTheorem.band_hi_general
#print axioms ProximityGap.StaircaseBandTheorem.mcaDeltaStar_staircase_band
#print axioms ProximityGap.StaircaseBandTheorem.mcaDeltaStar_staircase_band_zmod
#print axioms ProximityGap.StaircaseBandTheorem.mcaDeltaStar_staircase_band_smooth
#print axioms ProximityGap.StaircaseBandTheorem.mcaDeltaStar_production_shape_staircase
