/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80QSmallDifferencePairForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G99ErdosTuranLadderCertificate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80NDivisorFourthPowerBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80OProductDivisorInterval

/-!
# LANE G100F (#466, 2026-07-10): the G99 integer-lift mechanism at COUNTING scale — an
  unconditional divisor-structure bound on the G80Q terminal small-difference pair count,
  `smallDiffPairs(b·H, W)⁸ ≤ 314880·W²·n¹²` for every window `2W² < p` (axiom-clean).

## From containment to counting

G99 (`dilated_orbit_short_interval_rigidity`) used the integer lift of consecutive orbit
differences to refute CONTAINMENT of a dilated orbit in a short interval at scale `√(p/2)`
(a Littlewood–Offord statement at total-mass scale). This lane pushes the same ℤ-lift
mechanism to the COUNTING scale on the G80Q terminal object
`smallDiffPairs(C, W) = #{(u,z) ∈ C² : u ≠ z, u − z ∈ Strip(W)}`, `C = b·H`:

1. **General-pair ℤ-lift relation** (`valMinAbs_mul_of_natAbs_le`,
   `lift_cross_relation`): products of two lifted strip values lift FAITHFULLY to ℤ when
   `2W² < p`, so every modular multiplicative relation among four strip values holds as an
   INTEGER relation among the lifts — the general form of G99's consecutive-difference
   congruence `m_j·m_k ≡ m_0·m_{j+k}`, now valid for arbitrary (non-consecutive) pairs.
2. **Coset confinement**: by G80Q/G80S the pair count decomposes exactly over ratios
   `d ∈ H∖{1}`, and the per-ratio small differences `(d−1)·b·y` fill the SINGLE coset
   `(d−1)b·H`. Same-ratio lifts have modular ratio in `H` (`same_ratio_lift_ratio_mem`;
   probe-verified 100% at every measured cell), and the product of two of them lies in the
   single coset `((d−1)b)²·H`, which carries exactly `n = |H|` residues.
3. **Divisor counting** (`coset_strip_pairs_le`): the product map on lifted per-ratio pairs
   therefore has image of size `≤ n` (faithful lift + one-coset confinement) and fibers of
   size `≤ 2·d(|y|)` (ordered divisor pairs with a sign) — the CG product trick EXTENDED
   FROM THE SUBGROUP (G80O/G80M) TO EVERY COSET: `N_d(W)² ≤ 2·D·n` under
   `DivisorBound(W², D)`.
4. **Unconditional instantiation** (`ratio_strip_count_pow_eight_le`, via G80N's
   `d(y)⁴ ≤ 19680·y`): `N_d(W)⁸ ≤ 314880·W²·n⁴` with zero named hypotheses.
5. **CAPSTONE** (`smallDiffPairs_pow_eight_le`): summing over the `≤ n` ratio classes,
   `smallDiffPairs(b·H, W)⁸ ≤ 314880·W²·n¹²`, i.e.
   `smallDiffPairs ≤ 314880^{1/8}·n^{3/2}·W^{1/4} ≈ 4.88·n^{3/2}·W^{1/4}`,
   for EVERY multiplicative `H`, EVERY dilation `b ≠ 0`, EVERY window `2W² < p`.

Against the trivial caps `min(n², 2W·n)` the capstone is NONTRIVIAL throughout
`n^{2/3} ≪ W ≪ n²` (inside `W < √(p/2)`) — to our knowledge the first machine-checked
non-Fourier COUNTING bound on the terminal G80Q object in the intermediate window between
the G99 containment scale and the prize saddle.

## Probe findings (`scripts/probes/probe_466_g100f_smalldiff_counting.py`, 2026-07-10)

Cells `n ∈ {16,32,64,...}`, `β ∈ [2,4]`, up to 400 cosets each: (i) the count leaves `0` at
the birthday scale `W ≈ p/(2n²)` (median first gap tracks `p/(2n²)`, NOT `√p`); (ii) in the
window `[√p, p/K]` the worst-coset/uniform ratio DECAYS monotonically (≈ 1.3–2.5 at the
prize `W = p/K`, spikes only at small `W` where the uniform count is `< 1` pair) — the
intermediate window is uniform-like and thin, no spike; (iii) same-ratio lift pairs satisfy
`m/m' ∈ H (mod p)` in 100% of measured pairs, lifted values are few and heavily
gcd-correlated (distinct `|lifts|` ≈ 25–35% of count, max pairwise gcd up to 722) — the
multiplicative quasi-closure that powers the theorem is exact in evidence; (iv) the
capstone bound holds with large margin (measured `sdp/bound ≤ 0.13`).

## Honest scope

The window `2W² < p` is the integer-lift rigidity regime; by G80P regime disjointness the
prize saddle sits at `W = p/K ≫ √p`, OUTSIDE this window — no prize claim. The bound's
shape `n^{3/2}·W^{1/4}` is far above the uniform main term `n²·2W/p` at these `W` (the
probe shows truth is essentially uniform); its value is structural: the G99 ℤ-lift
mechanism DOES count (not merely refute containment), the CG interval technology extends
from the subgroup to every coset and hence to the full terminal pair object, and the
remaining gap to the certificate is exactly the `W > √p` half of the window plus the
uniform-main-term strength. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean; no `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting

open ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction
open ArkLib.ProximityGap.Frontier.G80QSmallDifferencePairForm
open ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate
open ArkLib.ProximityGap.Frontier.G80NDivisorFourthPowerBound
open ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-! ## Part 1 — the ℤ-lift bricks: strip values lift to `[−W, W]`, products lift faithfully -/

/-- Members of the centered strip of half-width `W` lift to integers of absolute value
`≤ W`: `w ∈ Strip(W) ⟹ |valMinAbs(w)| ≤ W` (needs `2W < p` so the two strip arms do not
overlap the far side). -/
theorem valMinAbs_natAbs_le_of_mem_strip {W : ℕ} (hW : 2 * W < p) {w : ZMod p}
    (hw : w ∈ strip p W) : w.valMinAbs.natAbs ≤ W := by
  rw [strip, Finset.mem_filter] at hw
  have hvlt : w.val < p := ZMod.val_lt w
  rcases hw.2 with hlo | hhi
  · -- low arm: val ≤ W, the lift is val itself
    have hz : (((w.val : ℤ)) : ZMod p) = w := by
      exact_mod_cast ZMod.natCast_rightInverse w
    have h2 : 2 * ((w.val : ℤ)).natAbs < p := by omega
    have hlift := valMinAbs_intCast_of_two_mul_abs_lt h2
    rw [hz] at hlift
    rw [hlift]
    omega
  · -- high arm: val ≥ p − W, the lift is val − p ∈ [−W, 0)
    set z : ℤ := (w.val : ℤ) - (p : ℤ) with hzdef
    have hz : ((z : ZMod p)) = w := by
      rw [hzdef]
      push_cast
      rw [ZMod.natCast_self, sub_zero]
      exact_mod_cast ZMod.natCast_rightInverse w
    have h2 : 2 * z.natAbs < p := by omega
    have hlift := valMinAbs_intCast_of_two_mul_abs_lt h2
    rw [hz] at hlift
    rw [hlift]
    omega

/-- **The general-pair integer-lift multiplicative relation.** If two residues have lifts
of absolute value `≤ W` and `2W² < p`, the lift of their product IS the product of their
lifts: `valMinAbs(w₁·w₂) = valMinAbs(w₁)·valMinAbs(w₂)` in ℤ. This is G99's congruence
mechanism (`m_j·m_k ≡ m_0·m_{j+k}`, both sides `< p`, hence ℤ-equal) freed from the
consecutive-difference special case: the ℤ-lift of the strip is multiplicatively faithful
below `√(p/2)`. -/
theorem valMinAbs_mul_of_natAbs_le {W : ℕ} (hW : 2 * (W * W) < p) {w₁ w₂ : ZMod p}
    (h₁ : w₁.valMinAbs.natAbs ≤ W) (h₂ : w₂.valMinAbs.natAbs ≤ W) :
    (w₁ * w₂).valMinAbs = w₁.valMinAbs * w₂.valMinAbs := by
  have hcast : ((Int.cast (w₁.valMinAbs * w₂.valMinAbs) : ZMod p)) = w₁ * w₂ := by
    rw [Int.cast_mul, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  have h2 : 2 * (w₁.valMinAbs * w₂.valMinAbs).natAbs < p := by
    rw [Int.natAbs_mul]
    have := Nat.mul_le_mul h₁ h₂
    omega
  rw [← hcast]
  exact valMinAbs_intCast_of_two_mul_abs_lt h2

/-- **Cross-pair ℤ-relations.** ANY modular multiplicative relation `w₁·w₂ = w₃·w₄` among
four strip values holds as an INTEGER relation among their lifts once `2W² < p` — the
lifted small-difference set is multiplicatively quasi-closed as a bounded set of integers.
-/
theorem lift_cross_relation {W : ℕ} (hW : 2 * (W * W) < p) {w₁ w₂ w₃ w₄ : ZMod p}
    (h₁ : w₁.valMinAbs.natAbs ≤ W) (h₂ : w₂.valMinAbs.natAbs ≤ W)
    (h₃ : w₃.valMinAbs.natAbs ≤ W) (h₄ : w₄.valMinAbs.natAbs ≤ W)
    (hrel : w₁ * w₂ = w₃ * w₄) :
    w₁.valMinAbs * w₂.valMinAbs = w₃.valMinAbs * w₄.valMinAbs := by
  rw [← valMinAbs_mul_of_natAbs_le hW h₁ h₂, ← valMinAbs_mul_of_natAbs_le hW h₃ h₄, hrel]

/-- **Same-ratio lifts have modular ratio in `H`.** For a division-closed `H` and any two
base points `y₁, y₂ ∈ H`, the lifted small differences at the same ratio (`c = d − 1`),
`m_i = valMinAbs(c·b·y_i)`, satisfy `m₁/m₂ ∈ H (mod p)` — the structure the G100F probe
verified in 100% of measured pairs. -/
theorem same_ratio_lift_ratio_mem (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H)
    {b c y₁ y₂ : ZMod p} (hb : b ≠ 0) (hc : c ≠ 0) (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H) :
    (((c * (b * y₁)).valMinAbs : ZMod p)) * (((c * (b * y₂)).valMinAbs : ZMod p))⁻¹
      ∈ H := by
  have hy₂0 : y₂ ≠ 0 := fun h => h0 (h ▸ hy₂)
  rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  have hkey : (c * (b * y₁)) * (c * (b * y₂))⁻¹ = y₁ * y₂⁻¹ := by
    rw [mul_inv, mul_inv]
    field_simp
  rw [hkey]
  exact hdiv y₁ hy₁ y₂ hy₂

/-! ## Part 2 — the coset product–divisor bound: the CG trick beyond the subgroup -/

/-- **The COSET strip-pair bound.** For multiplicatively closed `H` avoiding `0`, any
dilation `b ≠ 0` and any ratio direction `c ≠ 0`, the per-ratio strip count
`N = #{z ∈ b·H : c·z ∈ Strip(W)}` satisfies `N² ≤ 2·D·|H|` whenever `2W² < p` and
`DivisorBound(W², D)`. Mechanism: the counted values fill the single coset `cb·H`; their
ℤ-lifts lie in `[−W, W] ∖ {0}`; the product of two lifts lifts faithfully (Part 1) into
the single coset `(cb)²·H` carrying `n` residues, so the product map has image `≤ n` and
fibers `≤ 2·d(|y|) ≤ 2D` (divisor pairs with a sign). This extends G80O's subgroup product
trick to EVERY coset — the step the small-difference pair object needs. -/
theorem coset_strip_pairs_le (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W D : ℕ} (hW : 2 * (W * W) < p) (hD : DivisorBound (W * W) D)
    {b c : ZMod p} (hb : b ≠ 0) (hc : c ≠ 0) :
    ((H.image (fun y => b * y)).filter (fun z => c * z ∈ strip p W)).card ^ 2
      ≤ 2 * D * H.card := by
  classical
  have hW1 : 2 * W < p := by
    rcases Nat.eq_zero_or_pos W with rfl | hWpos
    · have := (Fact.out : p.Prime).pos
      omega
    · have h1 : W ≤ W * W := Nat.le_mul_of_pos_left W hWpos
      omega
  set A : Finset (ZMod p) :=
    (H.image (fun y => b * y)).filter (fun z => c * z ∈ strip p W) with hA
  set B : Finset (ZMod p) := A.image (fun z => c * z) with hB
  have hcardB : B.card = A.card :=
    Finset.card_image_of_injective _ (mul_right_injective₀ hc)
  -- structure of the members of B: in the strip, nonzero, in the coset (c·b)·H
  have hBmem : ∀ w ∈ B, w ∈ strip p W ∧ w ≠ 0 ∧ ∃ y ∈ H, w = c * b * y := by
    intro w hw
    rw [hB, Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hA, Finset.mem_filter, Finset.mem_image] at hz
    obtain ⟨⟨y, hy, rfl⟩, hstrip⟩ := hz
    have hy0 : y ≠ 0 := fun h => h0 (h ▸ hy)
    show c * (b * y) ∈ strip p W ∧ c * (b * y) ≠ 0 ∧ ∃ y' ∈ H, c * (b * y) = c * b * y'
    exact ⟨hstrip, mul_ne_zero hc (mul_ne_zero hb hy0), y, hy, by ring⟩
  have hlift : ∀ w ∈ B, w.valMinAbs.natAbs ≤ W := fun w hw =>
    valMinAbs_natAbs_le_of_mem_strip hW1 (hBmem w hw).1
  have hlift0 : ∀ w ∈ B, w.valMinAbs ≠ 0 := by
    intro w hw h
    exact (hBmem w hw).2.1 (by rw [← ZMod.coe_valMinAbs w, h, Int.cast_zero])
  -- the lifted product map on pairs
  have hbnd : ∀ y ∈ (B ×ˢ B).image (fun q => q.1.valMinAbs * q.2.valMinAbs),
      y.natAbs ≤ W * W ∧ y ≠ 0 := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨⟨w₁, w₂⟩, hw, rfl⟩ := hy
    rw [Finset.mem_product] at hw
    constructor
    · show (w₁.valMinAbs * w₂.valMinAbs).natAbs ≤ W * W
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hlift _ hw.1) (hlift _ hw.2)
    · show w₁.valMinAbs * w₂.valMinAbs ≠ 0
      exact mul_ne_zero (hlift0 _ hw.1) (hlift0 _ hw.2)
  -- fibers of the product map are at most 2·D (divisor with sign)
  have key : (B ×ˢ B).card
      ≤ (2 * D) * ((B ×ˢ B).image (fun q => q.1.valMinAbs * q.2.valMinAbs)).card := by
    refine Finset.card_le_mul_card_image _ (2 * D) ?_
    intro y hy
    obtain ⟨habs, hy0⟩ := hbnd y hy
    have h1abs : 1 ≤ y.natAbs := Int.natAbs_pos.mpr hy0
    calc ((B ×ˢ B).filter (fun q => q.1.valMinAbs * q.2.valMinAbs = y)).card
        ≤ (y.natAbs.divisors ×ˢ (Finset.univ : Finset Bool)).card := by
          refine Finset.card_le_card_of_injOn
            (fun q => (q.1.valMinAbs.natAbs, decide (0 ≤ q.1.valMinAbs))) ?_ ?_
          · rintro ⟨u₁, u₂⟩ hq
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
            obtain ⟨⟨hu₁, hu₂⟩, hprod⟩ := hq
            simp only [Finset.mem_coe]
            show (u₁.valMinAbs.natAbs, decide (0 ≤ u₁.valMinAbs))
              ∈ y.natAbs.divisors ×ˢ (Finset.univ : Finset Bool)
            rw [Finset.mem_product]
            refine ⟨?_, Finset.mem_univ _⟩
            rw [Nat.mem_divisors]
            exact ⟨Int.natAbs_dvd_natAbs.mpr ⟨u₂.valMinAbs, hprod.symm⟩,
              Int.natAbs_ne_zero.mpr hy0⟩
          · rintro ⟨u₁, u₂⟩ hq ⟨v₁, v₂⟩ hq' heq
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq hq'
            obtain ⟨⟨hu₁, hu₂⟩, hp1⟩ := hq
            obtain ⟨⟨hv₁, hv₂⟩, hp2⟩ := hq'
            simp only [Prod.mk.injEq] at heq
            obtain ⟨h1, h2⟩ := heq
            rw [decide_eq_decide] at h2
            have hval : u₁.valMinAbs = v₁.valMinAbs := by omega
            have hu : u₁ = v₁ := by
              calc u₁ = ((u₁.valMinAbs : ℤ) : ZMod p) := (ZMod.coe_valMinAbs u₁).symm
                _ = ((v₁.valMinAbs : ℤ) : ZMod p) := by rw [hval]
                _ = v₁ := ZMod.coe_valMinAbs v₁
            have hm2 : u₂.valMinAbs = v₂.valMinAbs := by
              have h := hp1.trans hp2.symm
              rw [hval] at h
              exact mul_left_cancel₀ (hlift0 v₁ hv₁) h
            have hu2 : u₂ = v₂ := by
              calc u₂ = ((u₂.valMinAbs : ℤ) : ZMod p) := (ZMod.coe_valMinAbs u₂).symm
                _ = ((v₂.valMinAbs : ℤ) : ZMod p) := by rw [hm2]
                _ = v₂ := ZMod.coe_valMinAbs v₂
            rw [Prod.mk.injEq]
            exact ⟨hu, hu2⟩
      _ = y.natAbs.divisors.card * 2 := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
      _ ≤ D * 2 := Nat.mul_le_mul_right 2
          (hD y.natAbs (Finset.mem_Icc.mpr ⟨h1abs, habs⟩))
      _ = 2 * D := Nat.mul_comm D 2
  -- the image injects into the single coset (cb)²·H, hence has ≤ |H| elements
  have hcb : c * b ≠ 0 := mul_ne_zero hc hb
  have he : (c * b) * (c * b) ≠ 0 := mul_ne_zero hcb hcb
  have himg : ((B ×ˢ B).image (fun q => q.1.valMinAbs * q.2.valMinAbs)).card
      ≤ H.card := by
    refine Finset.card_le_card_of_injOn
      (fun y => ((y : ℤ) : ZMod p) * (((c * b) * (c * b))⁻¹)) ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe] at hy ⊢
      rw [Finset.mem_image] at hy
      obtain ⟨⟨w₁, w₂⟩, hw, rfl⟩ := hy
      rw [Finset.mem_product] at hw
      obtain ⟨hs₁, hn₁, y₁, hy₁, hw₁⟩ := hBmem w₁ hw.1
      obtain ⟨hs₂, hn₂, y₂, hy₂, hw₂⟩ := hBmem w₂ hw.2
      show ((Int.cast (w₁.valMinAbs * w₂.valMinAbs) : ZMod p))
        * (((c * b) * (c * b))⁻¹) ∈ H
      rw [Int.cast_mul, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, hw₁, hw₂,
        show (c * b * y₁) * (c * b * y₂) = ((c * b) * (c * b)) * (y₁ * y₂) by ring,
        mul_comm ((c * b) * (c * b)) (y₁ * y₂), mul_assoc, mul_inv_cancel₀ he, mul_one]
      exact hmul y₁ hy₁ y₂ hy₂
    · intro y hy y' hy' heq
      rw [Finset.mem_coe] at hy hy'
      obtain ⟨habs, hy0⟩ := hbnd y hy
      obtain ⟨habs', hy0'⟩ := hbnd y' hy'
      have heq' : ((y : ℤ) : ZMod p) * (((c * b) * (c * b))⁻¹)
          = ((y' : ℤ) : ZMod p) * (((c * b) * (c * b))⁻¹) := heq
      have h1 : ((y : ℤ) : ZMod p) = ((y' : ℤ) : ZMod p) :=
        mul_right_cancel₀ (inv_ne_zero he) heq'
      have h2 : 2 * (y : ℤ).natAbs < p := by omega
      have h2' : 2 * (y' : ℤ).natAbs < p := by omega
      calc y = ((y : ℤ) : ZMod p).valMinAbs :=
            (valMinAbs_intCast_of_two_mul_abs_lt h2).symm
        _ = ((y' : ℤ) : ZMod p).valMinAbs := by rw [h1]
        _ = y' := valMinAbs_intCast_of_two_mul_abs_lt h2'
  calc A.card ^ 2 = (B ×ˢ B).card := by
        rw [Finset.card_product, hcardB]
        ring
    _ ≤ (2 * D) * ((B ×ˢ B).image (fun q => q.1.valMinAbs * q.2.valMinAbs)).card := key
    _ ≤ (2 * D) * H.card := Nat.mul_le_mul_left _ himg

/-- **The unconditional per-ratio bound** (G80N instantiation): for every ratio direction
`c ≠ 0` and window `2W² < p`, `N_c(W)⁸ ≤ 314880·W²·|H|⁴` with ZERO named hypotheses —
the coset analogue of G80M's `T(W)⁸ ≤ 19680·W²·n⁴` (the extra `2⁴ = 16` pays for the
sign of the lift). -/
theorem ratio_strip_count_pow_eight_le (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : 2 * (W * W) < p) {b c : ZMod p} (hb : b ≠ 0) (hc : c ≠ 0) :
    ((H.image (fun y => b * y)).filter (fun z => c * z ∈ strip p W)).card ^ 8
      ≤ 314880 * (W * W) * H.card ^ 4 := by
  classical
  rcases Nat.eq_zero_or_pos W with rfl | hWpos
  · -- W = 0: the strip is {0}, which the coset avoids
    have hzero :
        ((H.image (fun y => b * y)).filter (fun z => c * z ∈ strip p 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hy0 : y ≠ 0 := fun h => h0 (h ▸ hy)
      intro hmem
      simp only [strip, Finset.mem_filter] at hmem
      obtain ⟨-, hstrip0⟩ := hmem
      have hvlt : (c * (b * y)).val < p := ZMod.val_lt _
      have hval : (c * (b * y)).val = 0 := by omega
      exact (mul_ne_zero hc (mul_ne_zero hb hy0)) ((ZMod.val_eq_zero _).mp hval)
    rw [hzero]
    simp
  -- W ≥ 1: realize D as the attained divisor maximum on [1, W²] (G80M pattern)
  have hIcc : (Finset.Icc 1 (W * W)).Nonempty := by
    rw [Finset.nonempty_Icc]
    nlinarith
  have hne : ((Finset.Icc 1 (W * W)).image (fun y => y.divisors.card)).Nonempty :=
    hIcc.image _
  set D : ℕ := ((Finset.Icc 1 (W * W)).image (fun y => y.divisors.card)).max' hne with hD
  have hDB : DivisorBound (W * W) D := by
    intro y hy
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem (fun y => y.divisors.card) hy)
  have hD4 : D ^ 4 ≤ 19680 * (W * W) := by
    have hmem := Finset.max'_mem _ hne
    rw [Finset.mem_image] at hmem
    obtain ⟨y₀, hy₀, hDy⟩ := hmem
    rw [Finset.mem_Icc] at hy₀
    have hy0ne : y₀ ≠ 0 := by omega
    have hDy' : y₀.divisors.card = D := by
      rw [hD]
      exact hDy
    calc D ^ 4 = y₀.divisors.card ^ 4 := by rw [hDy']
      _ ≤ 19680 * y₀ := card_divisors_pow_four_le hy0ne
      _ ≤ 19680 * (W * W) := Nat.mul_le_mul_left _ hy₀.2
  have hsq := coset_strip_pairs_le H h0 hmul hW hDB hb hc
  calc ((H.image (fun y => b * y)).filter (fun z => c * z ∈ strip p W)).card ^ 8
      = (((H.image (fun y => b * y)).filter
          (fun z => c * z ∈ strip p W)).card ^ 2) ^ 4 := by ring
    _ ≤ (2 * D * H.card) ^ 4 := Nat.pow_le_pow_left hsq 4
    _ = 16 * (D ^ 4 * H.card ^ 4) := by ring
    _ ≤ 16 * ((19680 * (W * W)) * H.card ^ 4) := by
        exact Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right _ hD4)
    _ = 314880 * (W * W) * H.card ^ 4 := by ring

/-! ## Part 3 — CAPSTONE: the counting bound on the G80Q terminal object -/

/-- **CAPSTONE — the integer-lift COUNTING bound on the terminal small-difference pair
object.** For every prime `p`, multiplicative `H` (`0 ∉ H`, closed under `·` and `/`),
every dilation `b ≠ 0` and every window `W` with `2W² < p`:

`smallDiffPairs(b·H, W)⁸ ≤ 314880 · W² · |H|¹²`,

i.e. `smallDiffPairs ≤ 4.88·n^{3/2}·W^{1/4}` — nontrivial against the trivial caps
`min(n², 2W·n)` throughout `n^{2/3} ≪ W ≪ n²`. Proof: the exact G80Q ratio decomposition
`smallDiffPairs = Σ_{d ∈ H∖1} N_{d−1}(W)`, the per-ratio coset product–divisor bound
(`ratio_strip_count_pow_eight_le`), and the `≤ n` count of ratio classes. -/
theorem smallDiffPairs_pow_eight_le (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : 2 * (W * W) < p) (b : ZMod p) (hb : b ≠ 0) :
    (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 8
      ≤ 314880 * (W * W) * H.card ^ 12 := by
  classical
  rw [← strip_sum_eq_smallDiffPairs H h0 hdiv hmul W b hb]
  rcases Finset.eq_empty_or_nonempty (H.erase 1) with he | hne
  · rw [he]
    simp
  -- bound the ratio sum by (#ratio classes) · (worst per-ratio count)
  obtain ⟨d₀, hd₀, hmax⟩ := Finset.exists_max_image (H.erase 1) (fun d =>
    ((H.image (fun y => b * y)).filter
      (fun z => (d - 1) * z ∈ strip p W)).card) hne
  have hc₀ : d₀ - 1 ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hd₀).1
  have hB8 : ((H.image (fun y => b * y)).filter
      (fun z => (d₀ - 1) * z ∈ strip p W)).card ^ 8
      ≤ 314880 * (W * W) * H.card ^ 4 :=
    ratio_strip_count_pow_eight_le H h0 hmul hW hb hc₀
  have hsum : ∑ d ∈ H.erase 1,
      ((H.image (fun y => b * y)).filter
        (fun z => (d - 1) * z ∈ strip p W)).card
      ≤ H.card * ((H.image (fun y => b * y)).filter
        (fun z => (d₀ - 1) * z ∈ strip p W)).card := by
    have h1 : ∑ d ∈ H.erase 1,
        ((H.image (fun y => b * y)).filter
          (fun z => (d - 1) * z ∈ strip p W)).card
        ≤ (H.erase 1).card • ((H.image (fun y => b * y)).filter
          (fun z => (d₀ - 1) * z ∈ strip p W)).card :=
      Finset.sum_le_card_nsmul _ _ _ (fun d hd => hmax d hd)
    rw [nsmul_eq_mul] at h1
    exact h1.trans (Nat.mul_le_mul_right _ Finset.card_erase_le)
  calc (∑ d ∈ H.erase 1,
      ((H.image (fun y => b * y)).filter
        (fun z => (d - 1) * z ∈ strip p W)).card) ^ 8
      ≤ (H.card * ((H.image (fun y => b * y)).filter
          (fun z => (d₀ - 1) * z ∈ strip p W)).card) ^ 8 :=
        Nat.pow_le_pow_left hsum 8
    _ = H.card ^ 8 * ((H.image (fun y => b * y)).filter
          (fun z => (d₀ - 1) * z ∈ strip p W)).card ^ 8 := by ring
    _ ≤ H.card ^ 8 * (314880 * (W * W) * H.card ^ 4) := Nat.mul_le_mul_left _ hB8
    _ = 314880 * (W * W) * H.card ^ 12 := by ring

end ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting.valMinAbs_natAbs_le_of_mem_strip
#print axioms
  ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting.valMinAbs_mul_of_natAbs_le
#print axioms
  ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting.lift_cross_relation
#print axioms
  ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting.same_ratio_lift_ratio_mem
#print axioms
  ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting.coset_strip_pairs_le
#print axioms
  ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting.ratio_strip_count_pow_eight_le
#print axioms
  ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting.smallDiffPairs_pow_eight_le
