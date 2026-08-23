/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R348: Period-square recursion — the self-similar-hierarchy skeleton, machine-checked

Session 2026-07-09 (#466), route `self-similar-hierarchy` (Route 3), companion to
`_R341CAZACCosetEquivalence` (the Mellin ⟺ coset dictionary) and to the WallHolds /
DCEnergyBound moment tower (`_WallCapstone`, `GaussPeriodMomentBound`).

## Route verdict this brick records (see kb note + probe scripts)

Route 3 ("contract the max-period bound through a self-similar hierarchy of period-square
recursions") is **DEAD past the quartic ceiling** at the level of its full decoupling family:
* the complete-group van der Corput step is an **identity with zero loss** (no Fejér loss —
  the √-loss is in the return decoupling, not the differencing);
* the whole hierarchy resums exactly to the cyclotomic period-square recursion, which is
  **scale-preserving** (a closed 2-cycle `S ↔ T` at the same `(p, m)`; `H − 1` is not a
  subgroup, so there is no descent to smaller scales — `subgroupSum_mul_mem` below);
* one full loop with the only unconditional inputs (Weil–Jacobi) is **non-contractive**:
  the `√p` terms cancel identically and Weil is the unique fixed point
  (`weil_roundtrip_ge_weil`, `weil_roundtrip_eq_degenerate`);
* the exponent map of a full cycle destroys `β/2` of exponent (`m = p^β`):
  gain `δ ↦ min (β/2) (max 0 (δ − β/2))`, so the dream gain `β/2` dies in ONE cycle
  (`exponent_map_gain`);
* the salvage is a **conditional quartic ceiling** `σ = 1/2 − β/4`
  (`max_sq_le_of_kurtosis`, `papr_le_quartic_of_kurtosis`), equal to plain L⁴-Chebyshev
  up to the constant — the self-similar structure adds identification, not strength.

## Dictionary (paper ↔ this file)

`p` prime, `m ∣ p−1`, `n = (p−1)/m`, `H = (F_p^*)^m` (`|H| = n`), `S_b = ∑_{x∈bH} e_p(x)`
the Gaussian period.  Here `subgroupSum ψ H b = ∑_{w∈H} ψ(b·w)` over ANY finite
multiplicative subgroup `H` of ANY commutative ring, for ANY additive character `ψ` into any
commutative ring (`= eta ψ (torsion F d) b` of the substrate at `H = torsion F d`; restated
locally per lane hygiene).  `Sig = ∑_{i≠0}|T_i|²` (flatness mass of the shifted-subgroup sums
`T_i = ∑_{v∈H,v≠1} χ^i(v−1)`), `E(d) = A(d) − n/m` the centered cyclotomic counts,
`Ms² = max_b |S_b|²`, PAPR majorant `= (m·Ms + 1)/√p` (r341: `‖M_b‖ ≤ m·‖S_b‖ + 1` exactly,
`mellinSum_eq_coset` / `norm_mellinSum_le_coset`).

## PROVEN here (machine-checked, axiom-clean; no Weil input anywhere)

* `period_sq_recursion` — **[ID-SQ] the exact recursion** `S_b·S_{−b} = n + ∑_{v∈H,v≠1}
  S_{b(v−1)}` for any finite multiplicative subgroup of any `CommRing` and any `AddChar` into
  any `CommRing`.  Over `ℂ` the left side is `|S_b|²` (`conj_mul_subgroupSum`,
  `subgroupSum_neg_eq_conj`).  Numerically verified ≤ 4.6e−8 abs at six instances
  `(p,m) ∈ {(17,8),(2017,32),(54121,5),(246241,456),(200201,100),(20011,690)}`
  (scratchpad `route3_hierarchy.py`, session 2026-07-09).
* `subgroupSum_mul_mem` — **scale preservation / no-descent**: `S_{b·h} = S_b` for `h ∈ H`;
  the recursion never leaves the coset scale `(p, m)`.
* `period_sq_recursion_f17` — the recursion **fully closed at `(p,m) = (17,8)`**
  (the `DeltaStarPinsF17N8` instance): `H = {1,16}`, and for EVERY additive character into
  every commutative ring, `S_b·S_{−b} = 2 + S_{15·b}` — a one-term RHS, `decide`-checked
  subgroup data (`H17_isMulSubgroup`, `H17_eq_eighth_powers`, `H17_cyclotomic_shift`:
  `A(6) = 1` and all other cyclotomic classes empty, coset label `15 = 3⁶`).
* `parseval_centered` — the centering identity `∑_d (A(d) − n/m)² = (1 + Sig_A)/m` with
  `Sig_A := m·∑A² − (n−1)²` given only `∑_d A(d) = n − 1` (the real-algebra shadow of
  DFT-Parseval `[ID-L2E]`; no `ω`, no characters needed).
* `max_sq_le_of_parseval` — **the unconditional Cauchy–Schwarz chain** `[ID-SQ2]`:
  from the grouped-recursion-at-argmax hypothesis `Ms² ≤ n(1−1/m) + |∑_d E(d)·S(d)|` and the
  two Parseval identities (named-input hypotheses `hE`, `hS`; both are classical exact
  identities, verified ≤ 1e−13 rel. at the six instances) conclude
  `Ms² ≤ n + √((1+Sig)(p−n)/m)`.
* `max_sq_le_of_kurtosis` — the **conditional quartic ceiling, exact form**: under
  `PeriodKurtosisBound` the chain bound becomes `Ms² ≤ n + √((1+K·m·n)(p−n)/m)` —
  exactly the `σ = 1/2 − β/4` ceiling, and exactly L⁴-Chebyshev strength (the loop only
  improves the constant `κ ↦ κ − 1`): identification, not strength.
* `papr_le_quartic_of_kurtosis` — the headline cosmetic form
  `(m·√Ms² + 1)/√p ≤ 2^{3/4}·K^{1/4}·m^{3/4} + 1`, WITH the verifier-mandated domain fix
  `K ≥ 1/(2m)` (the bare form is FALSE in the corner `K ≲ 0.4/m`; all measured `K` = 0.44–8.77
  sit far above the fix, and an unconditional RMS floor `PAPR ≥ √(m−1)` makes the corner
  likely unrealizable by actual primes).  The LHS is exactly the r341 PAPR majorant:
  `‖mellinSum‖/√q ≤ (t·‖η_b‖+1)/√q` (`norm_mellinSum_le_coset`), so this wires
  `MellinCAZACBound` (r341) to the depth-2 rung of the WallHolds tower — the quartic
  ceiling `m^{3/4}` is what the depth-2 rung buys, strictly weaker than the open
  `√(m log p)` target.
* `quartic_discriminant_factor` — `m⁴ − 6m³ + 13m² − 12m + 4 = ((m−1)(m−2))²`, the identity
  that makes the roundtrip radical algebra exact.
* `weil_roundtrip_ge_weil` — **NON-CONTRACTION** (uncentered return form): for all real
  `m ≥ 3`, `s = √p ≥ 1`, `WeilS² ≤ n + √((1 + (m−1)·WeilT²)(p−n)/m)` where
  `WeilT = ((m−2)s+2)/m`, `WeilS = ((m−1)s+1)/m`, `n = (s²−1)/m`, `p = s²`: plugging the
  only unconditional input (Weil–Jacobi on `T`) back through the loop returns a bound NO
  BETTER than Weil on `S`.  Proof: the exact factorization
  `X − (WeilS²−n)² = (s−1)·Q(s,m)/m⁴` with `Q = (2m²−6m+3)(s³−1) + (2m²−2m−1)(s²−1)
  + (10m−7)(s−1) + 4m²` termwise nonnegative (sympy-verified, then `field_simp; ring`).
  Per the verifier correction: the `p/m²` gap of this UNCENTERED form is an artifact of the
  lossier bound; the sharp centered form `n(1−1/m) + √(…)` has gap `2/((m−2)m²) + o(1)` and
  is also non-contractive (0/1100 grid violations) — either way Weil is the fixed point and
  the route cannot contract.
* `weil_roundtrip_eq_degenerate` — at the degenerate point `s = 1` the loop is EXACT
  (both sides `= 1`): Weil is literally a fixed point, not merely a lower bound.
* `exponent_map_gain` — **the no-bootstrap exponent map**: with `m = p^β`, forward transfer
  `σ' = max ((1−β)/2) (τ/2 + 1/4)` and return transfer `τ' = min (1/2) (β + 2σ − 1/2)`
  compose to gain `δ = 1/2 − σ ↦ min (β/2) (max 0 (δ − β/2))` — every full cycle destroys
  exactly `β/2` of exponent; even granting pointwise square-root cancellation at level 2 the
  output is only `σ = 1/2 − β/4`.

## NAMED OPEN (do not discharge)

* `PeriodKurtosisBound m n Sig K` (≡ ShiftedSubgroupL2Flatness): `Sig ≤ K·m·n`, the depth-2
  rung of the WallHolds / DCEnergyBound moment tower (`r = 2` shape).  OPEN in the window
  `(log p)^{1+ε} ≤ m ≤ p/(log p)^{1+ε}`; measured `K = 0.44–2.14` generic, `8.77` at the
  record instance `(246241, 456)`; the CAZAC dream forces `K ≤ C·log p` (proved necessity,
  session derivation `Sig ≤ (m/p)·Ms²·(p−n)`), so it is strictly weaker than the dream yet
  still unproved.  Deeper rungs (2k-th moments, k ≥ 2) improve only the constant
  `K^{1/4} ↦ m^{o(1)}`, never the exponent `1/2 − β/4`.
* The two named-input hypotheses of `max_sq_le_of_parseval` (`hrec`: grouped recursion at the
  argmax coset — follows from `period_sq_recursion` + coset grouping + `∑_cosets S = −1`;
  `hE`/`hS`: `∑E² = (1+Sig)/m` and `∑|S|² ≤ p−n` — DFT-Parseval and additive-character
  orthogonality).  All are exact classical identities (six-instance verified); they are
  consumed as named inputs per the residual convention, not re-derived here.
* NOT formalized here (classical, six-instance verified, needs `|g(χ)|² = p`): the exact
  closure `[ID-SIG']` `p·Sig = m·∑_b|S_b|⁴ − (p−n)²` identifying `Sig` with the period
  fourth moment, whence `K = (κ−1)(1−1/m)²(1+O(1/p))`.
* The residual prize content of Route 3 (`SignedBilinearCancellation`, prose): beating
  Cauchy–Schwarz by `√m/polylog` in the signed sum `∑_d E(d)·S_{b*+d}` at the argmax coset —
  by `[ID-SQ2]` elementarily equivalent (both directions) to closing `m^{3/4} → √(m log p)`;
  CS is measured SATURATED (loss 1.0011) on the known alignment extreme `(54121, 5)`, so any
  proof must exploit non-alignment structure in the window.  Not stated as a formal `Prop`
  here: an honest statement needs the argmax-coset apparatus this brick deliberately avoids.

Known-dead routes respected (do NOT retread): aggregate fixed-depth Wick moments (r304),
resonance-method refutation, two-generator refuters, metaplectic at growing `m`.

Issue #466, round 348, route `self-similar-hierarchy`.
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion

open Finset

/-! ## §1 The exact period-square recursion [ID-SQ] -/

/-- `subgroupSum ψ H b = ∑_{w ∈ H} ψ(b·w)` — the Gaussian-period-shaped subgroup character
sum (`= eta ψ (torsion F d) b` of the substrate at `H = torsion F d`; local restatement per
lane hygiene). -/
def subgroupSum {F R : Type*} [CommRing F] [CommRing R]
    (ψ : AddChar F R) (H : Finset F) (b : F) : R :=
  ∑ w ∈ H, ψ (b * w)

/-- `H` is a finite subgroup of the multiplicative monoid: contains `1`, closed under
multiplication, and every element has an inverse inside `H`.  (Over a field this is exactly
"finite subgroup of `Fˣ`"; phrased with `∃`-inverses so it makes sense over any `CommRing`
and is `decide`-checkable at concrete instances.) -/
structure IsMulSubgroup {F : Type*} [CommRing F] (H : Finset F) : Prop where
  one_mem : (1 : F) ∈ H
  mul_mem : ∀ u ∈ H, ∀ v ∈ H, u * v ∈ H
  exists_inv : ∀ u ∈ H, ∃ v ∈ H, u * v = 1

/-- Left multiplication by a fixed `w ∈ H` permutes `H` (reindexing workhorse). -/
theorem sum_reindex_mulLeft {F R : Type*} [CommRing F] [AddCommMonoid R]
    {H : Finset F} (hH : IsMulSubgroup H) {w : F} (hw : w ∈ H) (f : F → R) :
    ∑ v ∈ H, f (w * v) = ∑ u ∈ H, f u := by
  obtain ⟨wi, hwi, hwwi⟩ := hH.exists_inv w hw
  exact Finset.sum_bij' (fun v _ => w * v) (fun u _ => wi * u)
    (fun v hv => hH.mul_mem w hw v hv)
    (fun u hu => hH.mul_mem wi hwi u hu)
    (fun v hv => by show wi * (w * v) = v; rw [← mul_assoc, mul_comm wi w, hwwi, one_mul])
    (fun u hu => by show w * (wi * u) = u; rw [← mul_assoc, hwwi, one_mul])
    (fun v hv => rfl)

/-- **[ID-SQ] The exact period-square recursion** (complete-group van der Corput with ZERO
loss, resummed): for any finite multiplicative subgroup `H` (`|H| = n`) of a commutative
ring, any additive character `ψ` into any commutative ring, and every `b`,

  `S_b · S_{−b} = n + ∑_{v ∈ H, v ≠ 1} S_{b(v−1)}`.

Over `ℂ` the left side is `|S_b|²` (`conj_mul_subgroupSum`).  The RHS lives at the SAME
scale `(p, m)` (`subgroupSum_mul_mem`): the hierarchy is a fixed-point loop, not a descent. -/
theorem period_sq_recursion {F R : Type*} [CommRing F] [DecidableEq F] [CommRing R]
    (ψ : AddChar F R) {H : Finset F} (hH : IsMulSubgroup H) (b : F) :
    subgroupSum ψ H b * subgroupSum ψ H (-b)
      = (H.card : R) + ∑ v ∈ H.erase 1, subgroupSum ψ H (b * (v - 1)) := by
  have expand : subgroupSum ψ H b * subgroupSum ψ H (-b)
      = ∑ w ∈ H, ∑ u ∈ H, ψ (b * (u - w)) := by
    unfold subgroupSum
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have reindex : ∀ w ∈ H, ∑ u ∈ H, ψ (b * (u - w)) = ∑ v ∈ H, ψ (b * w * (v - 1)) := by
    intro w hw
    rw [← sum_reindex_mulLeft hH hw (fun u => ψ (b * (u - w)))]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    ring
  have hone : subgroupSum ψ H (b * ((1 : F) - 1)) = (H.card : R) := by
    rw [sub_self, mul_zero]
    unfold subgroupSum
    have hz : ∀ w ∈ H, ψ ((0 : F) * w) = 1 := fun w _ => by
      rw [zero_mul, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl hz, Finset.sum_const, nsmul_eq_mul, mul_one]
  calc subgroupSum ψ H b * subgroupSum ψ H (-b)
      = ∑ w ∈ H, ∑ u ∈ H, ψ (b * (u - w)) := expand
    _ = ∑ w ∈ H, ∑ v ∈ H, ψ (b * w * (v - 1)) := Finset.sum_congr rfl reindex
    _ = ∑ v ∈ H, ∑ w ∈ H, ψ (b * w * (v - 1)) := Finset.sum_comm
    _ = ∑ v ∈ H, subgroupSum ψ H (b * (v - 1)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        unfold subgroupSum
        refine Finset.sum_congr rfl fun w _ => ?_
        congr 1
        ring
    _ = subgroupSum ψ H (b * ((1 : F) - 1))
          + ∑ v ∈ H.erase 1, subgroupSum ψ H (b * (v - 1)) :=
        (Finset.add_sum_erase H (fun v => subgroupSum ψ H (b * (v - 1))) hH.one_mem).symm
    _ = (H.card : R) + ∑ v ∈ H.erase 1, subgroupSum ψ H (b * (v - 1)) := by rw [hone]

/-- **Scale preservation / no-descent**: `S` is constant on cosets — `S_{b·h} = S_b` for
`h ∈ H`.  The recursion is a closed 2-cycle at the same `(p, m)`: `H − 1` is not a subgroup
and no smaller scale ever appears; Route 3's "self-similarity" is a fixed point, not a
descent. -/
theorem subgroupSum_mul_mem {F R : Type*} [CommRing F] [CommRing R]
    (ψ : AddChar F R) {H : Finset F} (hH : IsMulSubgroup H) (b : F) {h : F} (hh : h ∈ H) :
    subgroupSum ψ H (b * h) = subgroupSum ψ H b := by
  unfold subgroupSum
  rw [← sum_reindex_mulLeft hH hh (fun u => ψ (b * u))]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  ring

/-- Over `ℂ` and `F = ZMod q` (`q ≠ 0`), `S_{−b} = conj S_b` — so `period_sq_recursion`
computes `|S_b|²` on the nose. -/
theorem subgroupSum_neg_eq_conj {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    (H : Finset (ZMod q)) (b : ZMod q) :
    subgroupSum ψ H (-b) = (starRingEnd ℂ) (subgroupSum ψ H b) := by
  unfold subgroupSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hR : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne q)
  rw [AddChar.starComp_apply hR, AddChar.inv_apply, neg_mul]

/-- `[ID-SQ]` in modulus form over `ℂ`: `S_b · conj S_b = n + ∑_{v∈H, v≠1} S_{b(v−1)}`
(the LHS is `|S_b|²` as a complex number). -/
theorem conj_mul_subgroupSum {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    {H : Finset (ZMod q)} (hH : IsMulSubgroup H) (b : ZMod q) :
    subgroupSum ψ H b * (starRingEnd ℂ) (subgroupSum ψ H b)
      = (H.card : ℂ) + ∑ v ∈ H.erase 1, subgroupSum ψ H (b * (v - 1)) := by
  rw [← subgroupSum_neg_eq_conj]
  exact period_sq_recursion ψ hH b

/-! ## §2 The `(p, m) = (17, 8)` instance (`DeltaStarPinsF17N8` family), `decide`-checked -/

/-- The 8th-power subgroup `H = {1, 16} ⊂ F₁₇` (`m = 8`, `n = 2`). -/
def H17 : Finset (ZMod 17) := {1, 16}

/-- `H17` is a multiplicative subgroup (kernel-checked). -/
theorem H17_isMulSubgroup : IsMulSubgroup H17 :=
  ⟨by decide, by decide, by decide⟩

/-- `H17` really is the full set of nonzero 8th powers in `F₁₇` (kernel-checked). -/
theorem H17_eq_eighth_powers :
    H17 = (Finset.univ.filter fun x : ZMod 17 => x ≠ 0).image (· ^ 8) := by decide

/-- Cyclotomic-count pin at `(p, m) = (17, 8)`: the unique `v ∈ H \ {1}` has `v − 1 = 15`;
`15 = 3⁶` lies in the coset `3⁶·H` of the primitive root `g = 3` (`3⁸ = 16 ≠ 1` certifies
full order `16`), so `A(6) = 1` and every other cyclotomic class is empty — the grouped
recursion at this instance is the one-term map `|S_b|² = 2 + S_{b+6}` in coset labels. -/
theorem H17_cyclotomic_shift :
    (H17.erase 1).image (fun v => v - 1) = {15} ∧
      (15 : ZMod 17) ∈ H17.image (fun h => 3 ^ 6 * h) ∧
      (3 : ZMod 17) ^ 8 ≠ 1 := by decide

/-- **The recursion fully closed at `(17, 8)`** (one-term RHS): for EVERY additive character
`ψ` of `F₁₇` into every commutative ring and every `b`, `S_b · S_{−b} = 2 + S_{15·b}`.
Instance of `period_sq_recursion`; matches the six-instance numerics at `(17, 8)`. -/
theorem period_sq_recursion_f17 {R : Type*} [CommRing R] (ψ : AddChar (ZMod 17) R)
    (b : ZMod 17) :
    subgroupSum ψ H17 b * subgroupSum ψ H17 (-b) = 2 + subgroupSum ψ H17 (15 * b) := by
  have h := period_sq_recursion ψ H17_isMulSubgroup b
  have herase : H17.erase 1 = {16} := by decide
  rw [herase, Finset.sum_singleton] at h
  have hcard : ((H17.card : ℕ) : R) = 2 := by
    rw [show H17.card = 2 by decide]
    norm_num
  have harg : b * ((16 : ZMod 17) - 1) = 15 * b := by
    rw [show (16 : ZMod 17) - 1 = 15 by decide, mul_comm]
  rw [hcard, harg] at h
  exact h

/-! ## §3 The quartic ceiling: Parseval chain, kurtosis rung, conditional PAPR bound -/

/-- Centering identity (real-algebra shadow of DFT-Parseval `[ID-L2E]`): if
`∑_d A(d) = n − 1` then `∑_d (A(d) − n/m)² = (1 + Sig_A)/m` with
`Sig_A := m·∑_d A(d)² − (n−1)²` (the Parseval value of `∑_{i≠0}|T_i|²`).
No characters, no `ω` — pure finite algebra. -/
theorem parseval_centered {m : ℕ} (hm : 0 < m) (A : Fin m → ℝ) (n : ℝ)
    (hA : ∑ d, A d = n - 1) :
    ∑ d, (A d - n / m) ^ 2 = (1 + ((m : ℝ) * ∑ d, A d ^ 2 - (n - 1) ^ 2)) / m := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h1 : ∀ d : Fin m, (A d - n / m) ^ 2
      = A d ^ 2 - 2 * (n / m) * A d + (n / m) ^ 2 := fun d => by ring
  rw [Finset.sum_congr rfl fun d _ => h1 d, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hA, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **NAMED OPEN — the depth-2 rung of the moment tower** (≡ ShiftedSubgroupL2Flatness;
WallHolds / DCEnergyBound `r = 2` shape): `Sig ≤ K·m·n` where `Sig = ∑_{i≠0}|T_i|²`,
equivalently (`[ID-SIG']`, not formalized here) `κ − 1 ≤ K(1+o(1))` for the period kurtosis
`κ = m·∑_b|S_b|⁴/(p−n)²`.  OPEN in the window `(log p)^{1+ε} ≤ m ≤ p/(log p)^{1+ε}`;
measured `K = 0.44–2.14` generic, `8.77` at the record instance; the CAZAC dream forces
`K ≤ C log p` (proved necessity, session), so this is strictly weaker than the dream yet
still unproved.  Do not discharge. -/
def PeriodKurtosisBound (m n Sig K : ℝ) : Prop := Sig ≤ K * (m * n)

/-- **[ID-SQ2 + Cauchy–Schwarz] The unconditional chain bound.**  Inputs (named-input
hypotheses, classical exact identities — see module docstring):
`hrec` = the grouped recursion at the argmax coset (`|S_{b*}|² ≤ n(1−1/m) + |∑_d E(d)·S(d)|`,
from `period_sq_recursion` + coset grouping + `∑_cosets S = −1`), `hE` = DFT-Parseval
`∑_d E(d)² = (1+Sig)/m`, `hS` = character orthogonality `∑_d S(d)² ≤ p − n`.
Output: `Ms² ≤ n + √((1+Sig)(p−n)/m)`.  Cauchy–Schwarz is measured SATURATED (loss 1.0011)
on the alignment extreme `(54121, 5)` — the chain is tight on the known extremal family. -/
theorem max_sq_le_of_parseval {m : ℕ} (E S : Fin m → ℝ) (MS2 n p Sig : ℝ)
    (hrec : MS2 ≤ n * (1 - 1 / m) + |∑ d, E d * S d|)
    (hE : ∑ d, E d ^ 2 = (1 + Sig) / m)
    (hS : ∑ d, S d ^ 2 ≤ p - n)
    (hn : 0 ≤ n) :
    MS2 ≤ n + Real.sqrt ((1 + Sig) * (p - n) / m) := by
  have hSnn : (0 : ℝ) ≤ ∑ d, S d ^ 2 := Finset.sum_nonneg fun d _ => sq_nonneg _
  have hEnn : (0 : ℝ) ≤ (1 + Sig) / m := by
    rw [← hE]
    exact Finset.sum_nonneg fun d _ => sq_nonneg _
  have hpn : (0 : ℝ) ≤ p - n := le_trans hSnn hS
  have hcs : (∑ d, E d * S d) ^ 2 ≤ (1 + Sig) / m * (p - n) := by
    calc (∑ d, E d * S d) ^ 2
        ≤ (∑ d, E d ^ 2) * ∑ d, S d ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ E S
      _ ≤ (1 + Sig) / m * (p - n) := by
          rw [hE]
          exact mul_le_mul_of_nonneg_left hS hEnn
  have habs : |∑ d, E d * S d| ≤ Real.sqrt ((1 + Sig) * (p - n) / m) := by
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    calc (∑ d, E d * S d) ^ 2 ≤ (1 + Sig) / m * (p - n) := hcs
      _ = (1 + Sig) * (p - n) / m := by ring
  have h1m : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hfrac : n * (1 - 1 / m) ≤ n := by nlinarith [mul_nonneg hn h1m]
  linarith

/-- **Conditional quartic ceiling, exact form**: under the depth-2 kurtosis rung the chain
bound becomes `Ms² ≤ n + √((1 + K·m·n)(p−n)/m)` — exactly the `σ = 1/2 − β/4` quartic
ceiling, and exactly plain L⁴-Chebyshev strength up to the constant (`κ` vs `κ − 1`):
the self-similar structure adds identification, not strength. -/
theorem max_sq_le_of_kurtosis (m n p Sig K MS2 : ℝ)
    (hkur : PeriodKurtosisBound m n Sig K)
    (hchain : MS2 ≤ n + Real.sqrt ((1 + Sig) * (p - n) / m))
    (hpn : 0 ≤ p - n) (hm : 0 ≤ m) :
    MS2 ≤ n + Real.sqrt ((1 + K * (m * n)) * (p - n) / m) := by
  have h1 : 1 + Sig ≤ 1 + K * (m * n) := by
    have h := hkur
    unfold PeriodKurtosisBound at h
    linarith
  have h2 : (1 + Sig) * (p - n) ≤ (1 + K * (m * n)) * (p - n) :=
    mul_le_mul_of_nonneg_right h1 hpn
  have harg : (1 + Sig) * (p - n) / m ≤ (1 + K * (m * n)) * (p - n) / m := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hm)
  linarith [hchain, Real.sqrt_le_sqrt harg]

/-- **Conditional PAPR quartic ceiling (headline form, domain-fixed).**  With the
verifier-mandated side condition `K ≥ 1/(2m)` (the bare bound is FALSE in the corner
`K ≲ 0.4/m`; all measured `K = 0.44–8.77` are far above), normalization `K·m·n ≥ 1`,
and `m·n ≤ p` (true: `mn = p − 1`):

  `(m·√Ms² + 1)/√p ≤ 2^{3/4}·K^{1/4}·m^{3/4} + 1`.

The LHS is the exact r341 PAPR majorant (`‖mellinSum‖ ≤ m·‖S_b‖ + 1`,
`norm_mellinSum_le_coset`): this is the quartic weakening of `MellinCAZACBound`
that the depth-2 rung `PeriodKurtosisBound` buys — `σ = 1/2 − β/4`, strictly weaker than
the open `√(m log p)` target throughout the prize window. -/
theorem papr_le_quartic_of_kurtosis {m n p Sig K MS2 : ℝ}
    (hm : 1 ≤ m) (hp : 1 ≤ p)
    (hnm : m * n ≤ p) (hpn : 0 ≤ p - n)
    (hkur : PeriodKurtosisBound m n Sig K)
    (hKmn : 1 ≤ K * (m * n))
    (hKm : 1 / (2 * m) ≤ K)
    (hchain : MS2 ≤ n + Real.sqrt ((1 + Sig) * (p - n) / m)) :
    (m * Real.sqrt MS2 + 1) / Real.sqrt p
      ≤ 2 ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 4) * m ^ ((3 : ℝ) / 4) + 1 := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hKm
  have hkur' : Sig ≤ K * (m * n) := hkur
  have hsig2 : 1 + Sig ≤ 2 * (K * (m * n)) := by linarith
  have hnpm : n ≤ p / m := by
    rw [le_div_iff₀ hm0]
    nlinarith [hnm]
  -- Step 1: the sqrt argument is ≤ (2K/m)·p².
  have hstep1 : (1 + Sig) * (p - n) / m ≤ 2 * K / m * p ^ 2 := by
    have e1 : 2 * (K * (m * n)) * (p - n) / m = 2 * K * (n * (p - n)) := by
      field_simp
    have i1 : (1 + Sig) * (p - n) / m ≤ 2 * (K * (m * n)) * (p - n) / m := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsig2 hpn)
        (by positivity)
    have i2 : 2 * K * (n * (p - n)) ≤ 2 * K * (n * p) := by
      have hx : n * (p - n) ≤ n * p := by nlinarith [sq_nonneg n]
      exact mul_le_mul_of_nonneg_left hx (by positivity)
    have i3 : 2 * K * (n * p) ≤ 2 * K / m * p ^ 2 := by
      have hx : n * p ≤ p / m * p := mul_le_mul_of_nonneg_right hnpm hp0.le
      calc 2 * K * (n * p) ≤ 2 * K * (p / m * p) :=
            mul_le_mul_of_nonneg_left hx (by positivity)
        _ = 2 * K / m * p ^ 2 := by
            field_simp
    calc (1 + Sig) * (p - n) / m
        ≤ 2 * (K * (m * n)) * (p - n) / m := i1
      _ = 2 * K * (n * (p - n)) := e1
      _ ≤ 2 * K * (n * p) := i2
      _ ≤ 2 * K / m * p ^ 2 := i3
  -- Step 2: MS2 ≤ p/m + √(2K/m)·p.
  have hMS2p : MS2 ≤ p / m + Real.sqrt (2 * K / m) * p := by
    calc MS2 ≤ n + Real.sqrt ((1 + Sig) * (p - n) / m) := hchain
      _ ≤ p / m + Real.sqrt (2 * K / m * p ^ 2) :=
          add_le_add hnpm (Real.sqrt_le_sqrt hstep1)
      _ = p / m + Real.sqrt (2 * K / m) * p := by
          rw [Real.sqrt_mul (by positivity) (p ^ 2), Real.sqrt_sq hp0.le]
  -- Step 3: rpow bookkeeping — c² = √(8·K·m³) for c = 2^{3/4}·K^{1/4}·m^{3/4}.
  have hc2 : (2 ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 4) * m ^ ((3 : ℝ) / 4)) ^ 2
      = Real.sqrt (8 * K * m ^ 3) := by
    rw [Real.sqrt_eq_rpow, mul_pow, mul_pow,
      ← Real.rpow_natCast (2 ^ ((3 : ℝ) / 4)) 2,
      ← Real.rpow_natCast (K ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_natCast (m ^ ((3 : ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul hK0.le, ← Real.rpow_mul hm0.le,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hK0.le,
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast (2 : ℝ) 3, ← Real.rpow_natCast m 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hm0.le]
    norm_num
  -- Step 4: m² · √(2K/m) = √(2K·m³), and m ≤ √(2K·m³) from the domain fix K ≥ 1/(2m).
  have hm2sqrt : m ^ 2 * Real.sqrt (2 * K / m) = Real.sqrt (2 * K * m ^ 3) := by
    rw [show (m : ℝ) ^ 2 = Real.sqrt ((m ^ 2) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm,
      ← Real.sqrt_mul (by positivity) (2 * K / m)]
    congr 1
    field_simp
  have hmle : m ≤ Real.sqrt (2 * K * m ^ 3) := by
    apply Real.le_sqrt_of_sq_le
    have h2Km : 1 ≤ 2 * K * m := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)] at hKm
      nlinarith [hKm]
    nlinarith [mul_le_mul_of_nonneg_right h2Km (by positivity : (0 : ℝ) ≤ m ^ 2)]
  have h8 : Real.sqrt (8 * K * m ^ 3) = 2 * Real.sqrt (2 * K * m ^ 3) := by
    rw [show (8 : ℝ) * K * m ^ 3 = 4 * (2 * K * m ^ 3) by ring,
      Real.sqrt_mul (by norm_num) (2 * K * m ^ 3),
      show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  -- Step 5: squared master bound m²·MS2 ≤ c²·p, then take square roots.
  have hsq : m ^ 2 * MS2
      ≤ (2 ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 4) * m ^ ((3 : ℝ) / 4)) ^ 2 * p := by
    rw [hc2]
    have step := mul_le_mul_of_nonneg_left hMS2p (by positivity : (0 : ℝ) ≤ m ^ 2)
    have e : m ^ 2 * (p / m + Real.sqrt (2 * K / m) * p)
        = m * p + Real.sqrt (2 * K * m ^ 3) * p := by
      rw [← hm2sqrt]
      field_simp
    rw [e] at step
    have hmp := mul_le_mul_of_nonneg_right hmle hp0.le
    rw [h8]
    linarith
  have hc0 : (0 : ℝ) ≤ 2 ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 4) * m ^ ((3 : ℝ) / 4) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hK0.le _)) (Real.rpow_nonneg hm0.le _)
  have hfin1 : m * Real.sqrt MS2
      ≤ 2 ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 4) * m ^ ((3 : ℝ) / 4) * Real.sqrt p := by
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ m ^ 2) MS2, Real.sqrt_sq hm0.le,
      Real.sqrt_mul (by positivity) p, Real.sqrt_sq hc0] at h1
  have hsp : (1 : ℝ) ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hp
  have hsp0 : (0 : ℝ) < Real.sqrt p := by linarith
  rw [div_le_iff₀ hsp0]
  have hexpand : (2 ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 4) * m ^ ((3 : ℝ) / 4) + 1)
        * Real.sqrt p
      = 2 ^ ((3 : ℝ) / 4) * K ^ ((1 : ℝ) / 4) * m ^ ((3 : ℝ) / 4) * Real.sqrt p
        + Real.sqrt p := by ring
  rw [hexpand]
  linarith

/-! ## §4 Non-contraction: Weil is the fixed point of the full loop -/

/-- The exact discriminant factorization that makes the roundtrip radical algebra exact:
`m⁴ − 6m³ + 13m² − 12m + 4 = ((m−1)(m−2))²`. -/
theorem quartic_discriminant_factor (m : ℝ) :
    m ^ 4 - 6 * m ^ 3 + 13 * m ^ 2 - 12 * m + 4 = ((m - 1) * (m - 2)) ^ 2 := by ring

/-- **NON-CONTRACTION of the full self-similar loop** (uncentered return form): for all real
`m ≥ 3` and `s = √p ≥ 1`, with `n = (s²−1)/m`, `p = s²`, Weil–Jacobi input
`WeilT = ((m−2)s+2)/m` and Weil target `WeilS = ((m−1)s+1)/m`:

  `WeilS² ≤ n + √((1 + (m−1)·WeilT²)·(p−n)/m)`.

One full loop with the only unconditional input returns a bound NO BETTER than Weil: the
`√p` terms cancel identically (`quartic_discriminant_factor` is the underlying identity) and
the exact certificate is `X − (WeilS²−n)² = (s−1)·Q(s,m)/m⁴` with `Q` termwise nonnegative.
Verifier correction honored: the `p/m²` gap wording belongs to THIS uncentered form; the
sharp centered form has gap `2/((m−2)m²)+o(1)` and is also non-contractive — either way the
route cannot contract below Weil. -/
theorem weil_roundtrip_ge_weil {m s : ℝ} (hm : 3 ≤ m) (hs : 1 ≤ s) :
    (((m - 1) * s + 1) / m) ^ 2
      ≤ (s ^ 2 - 1) / m
        + Real.sqrt ((1 + (m - 1) * (((m - 2) * s + 2) / m) ^ 2)
            * (s ^ 2 - (s ^ 2 - 1) / m) / m) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hm' : m ≠ 0 := ne_of_gt hm0
  have hmm : (0 : ℝ) ≤ m * (m - 3) := mul_nonneg (by linarith) (by linarith)
  have hs3 : (1 : ℝ) ≤ s ^ 3 := one_le_pow₀ hs
  have hs2 : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ hs
  have hq1 : (0 : ℝ) ≤ 2 * m ^ 2 - 6 * m + 3 := by nlinarith [hmm]
  have hq2 : (0 : ℝ) ≤ 2 * m ^ 2 - 2 * m - 1 := by nlinarith [hmm]
  have hq3 : (0 : ℝ) ≤ 10 * m - 7 := by linarith
  have hQ : (0 : ℝ) ≤ (2 * m ^ 2 - 6 * m + 3) * (s ^ 3 - 1)
      + (2 * m ^ 2 - 2 * m - 1) * (s ^ 2 - 1) + (10 * m - 7) * (s - 1) + 4 * m ^ 2 := by
    have t1 : (0 : ℝ) ≤ (2 * m ^ 2 - 6 * m + 3) * (s ^ 3 - 1) :=
      mul_nonneg hq1 (by linarith)
    have t2 : (0 : ℝ) ≤ (2 * m ^ 2 - 2 * m - 1) * (s ^ 2 - 1) :=
      mul_nonneg hq2 (by linarith)
    have t3 : (0 : ℝ) ≤ (10 * m - 7) * (s - 1) := mul_nonneg hq3 (by linarith)
    nlinarith [sq_nonneg m]
  have hfactor : (1 + (m - 1) * (((m - 2) * s + 2) / m) ^ 2)
        * (s ^ 2 - (s ^ 2 - 1) / m) / m
        - ((((m - 1) * s + 1) / m) ^ 2 - (s ^ 2 - 1) / m) ^ 2
      = (s - 1) * ((2 * m ^ 2 - 6 * m + 3) * (s ^ 3 - 1)
          + (2 * m ^ 2 - 2 * m - 1) * (s ^ 2 - 1) + (10 * m - 7) * (s - 1) + 4 * m ^ 2)
        / m ^ 4 := by
    field_simp
    ring
  have hrhs : (0 : ℝ) ≤ (s - 1) * ((2 * m ^ 2 - 6 * m + 3) * (s ^ 3 - 1)
      + (2 * m ^ 2 - 2 * m - 1) * (s ^ 2 - 1) + (10 * m - 7) * (s - 1) + 4 * m ^ 2)
      / m ^ 4 := by
    apply div_nonneg (mul_nonneg (by linarith) hQ)
    positivity
  have hkey : ((((m - 1) * s + 1) / m) ^ 2 - (s ^ 2 - 1) / m) ^ 2
      ≤ (1 + (m - 1) * (((m - 2) * s + 2) / m) ^ 2)
        * (s ^ 2 - (s ^ 2 - 1) / m) / m := by
    linarith [hfactor, hrhs]
  have hAX := Real.le_sqrt_of_sq_le hkey
  linarith [hAX]

/-- **Weil is a fixed point, exactly**: at the degenerate point `s = 1` (`p = 1`, `n = 0`)
the roundtrip and the Weil target coincide — both sides equal `1`.  The loop is weakly
repelled upward from the fixed point, never contracted below it. -/
theorem weil_roundtrip_eq_degenerate {m : ℝ} (hm : 3 ≤ m) :
    (((m - 1) * 1 + 1) / m) ^ 2
      = ((1 : ℝ) ^ 2 - 1) / m
        + Real.sqrt ((1 + (m - 1) * (((m - 2) * 1 + 2) / m) ^ 2)
            * ((1 : ℝ) ^ 2 - ((1 : ℝ) ^ 2 - 1) / m) / m) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hm' : m ≠ 0 := ne_of_gt hm0
  have harg : (1 + (m - 1) * (((m - 2) * 1 + 2) / m) ^ 2)
      * ((1 : ℝ) ^ 2 - ((1 : ℝ) ^ 2 - 1) / m) / m = 1 := by
    rw [show (m - 2) * 1 + 2 = m by ring, div_self hm']
    field_simp
    ring
  rw [harg, Real.sqrt_one, show (m - 1) * 1 + 1 = m by ring, div_self hm']
  norm_num

/-- **The no-bootstrap exponent map.**  Write `m = p^β` and track the saving exponent `σ`
in `Ms ≤ p^σ` (gain `δ = 1/2 − σ`).  The session-proved forward transfer is
`σ' = max ((1−β)/2) (τ/2 + 1/4)` and the return transfer is
`τ' = min (1/2) (β + 2σ − 1/2)`; this theorem is the exact composition law: one full loop
sends the gain `δ` to `min (β/2) (max 0 (δ − β/2))`.  Every full cycle destroys `β/2` of
exponent; the "dream" gain `β/2` dies to `0` in ONE cycle, and even granting pointwise
square-root cancellation at level 2 the output is only `σ = 1/2 − β/4`. -/
theorem exponent_map_gain (β δ : ℝ) (hβ : 0 ≤ β) :
    1 / 2 - max ((1 - β) / 2) ((min (1 / 2) (β + 2 * (1 / 2 - δ) - 1 / 2)) / 2 + 1 / 4)
      = min (β / 2) (max 0 (δ - β / 2)) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

end ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.sum_reindex_mulLeft
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.period_sq_recursion
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.subgroupSum_mul_mem
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.subgroupSum_neg_eq_conj
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.conj_mul_subgroupSum
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.H17_isMulSubgroup
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.H17_eq_eighth_powers
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.H17_cyclotomic_shift
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.period_sq_recursion_f17
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.parseval_centered
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.max_sq_le_of_parseval
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.max_sq_le_of_kurtosis
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.papr_le_quartic_of_kurtosis
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.quartic_discriminant_factor
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.weil_roundtrip_ge_weil
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.weil_roundtrip_eq_degenerate
#print axioms ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion.exponent_map_gain
