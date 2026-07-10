/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80VArcDilationCoincidenceReduction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80S (#466, 2026-07-10): the DIRECTIONAL STRIP reduction — same-arc coincidence
  forces `(d−1)·v` into a centered strip of width `p/K`, so the arc certificate reduces to
  SHORT-INTERVAL CONCENTRATION of shifted-subgroup dilates (axiom-clean).

## Motivation: the G80T directional finding

The G80T probe refuted the unsigned lattice-height weld: `R(d)` anomalies are DIRECTIONAL
(proximity of `d` to positive small ratios near the diagonal), invisible to unsigned `λ₁`.
This lane lands the correct signed object. Same-arc membership `arcIndex(x) = arcIndex(y)`
pins the vals to one interval of length `< p/K + 1`, hence the DIFFERENCE `x − y` lies in the
CENTERED strip `Strip(W) = {w : val(w) ≤ W ∨ val(w) ≥ p − W}` at `W = ⌈p/K⌉` — the signed
window. Consequences, all machine-checked:

* `sub_mem_strip_of_same_arc` : `arcIndex K x = arcIndex K y ⟹ (x − y) ∈ Strip(p/K + 1)`.
* `dilCoincidence_le_stripCount` : `R(d) ≤ #{v ≠ 0 : (d−1)·v ∈ Strip}` — the
  dilation-coincidence count (G80V's Fourier-free floor object) is bounded by the strip
  concentration of the `(d−1)`-dilate.
* `stripCount_avg` : `Σ_{c≠0} StripCount(c) = (p−1)·(|Strip| − 1)` — exact all-`c` mean
  `≈ 2p/K`; the strip bound is tight on average.
* `pairCount_le_strip_sum` (CAPSTONE) : for a multiplicatively closed `H ∋ 1`, EVERY dilation
  `b`: `pairCount(b·H) ≤ |H| + Σ_{d ∈ H, d ≠ 1} #{z ∈ b·H : (d−1)·z ∈ Strip}` — the
  pair-form certificate (G80W) reduces to short-interval concentration of the COSET `b·H`
  under dilation by the SHIFTED-subgroup elements `d − 1 ∈ H − 1`.

## What this identifies

`#{z ∈ b·H : (d−1)z ∈ Strip}` is the classical object "concentration of a multiplicative
coset in a short centered interval after dilation" — with the dilations ranging over the
SHIFTED subgroup `H − 1`. This is exactly the Heath-Brown–Konyagin / Cilleruelo–Garaev /
Bourgain short-interval-concentration frontier (and `H − 1` is the shifted-subgroup object of
the G73/Shkredov context). The chain δ* ⟸ arc certificate ⟸ pair certificate ⟸ strip
concentration is now machine-checked end-to-end; the open input is the strip-concentration
bound `≤ |H|·|Strip|/p + O(polylog)` for coset dilates — the sharpest known formulation of
the wall, now with zero formal slack around it.

## Honest scope

Reduction + exact mean only; the strip-concentration bound for subgroup dilates (the wall) is
NOT proven. The strip bound loses a factor ≤ 2-ish vs exact `R` (boundary/straddle effects),
harmless at the certificate's `polylog` tolerance. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction

open ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation
open ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- The centered strip of half-width `W`: residues whose canonical val is `≤ W` or
`≥ p − W` (i.e. the signed representative lies in `[−W, W]`). -/
def strip (p W : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter (fun w => (w : ZMod p).val ≤ W ∨ p - W ≤ (w : ZMod p).val)

/-- Strip concentration count of the `c`-dilate: how many nonzero `v` have `c·v` in the
centered strip. -/
def stripCount (p : ℕ) [NeZero p] (W : ℕ) (c : ZMod p) : ℕ :=
  ((Finset.univ.erase (0 : ZMod p)).filter (fun v => c * v ∈ strip p W)).card

/-- **Same arc ⟹ difference in the centered strip.** If `x` and `y` share an arc
(`arcIndex K x = arcIndex K y`), their vals lie in one interval of length `< p/K + 1`, so
`x − y` has signed representative in `[−(p/K), p/K]`. -/
theorem sub_mem_strip_of_same_arc {K : ℕ} (hK : 0 < K) {x y : ZMod p}
    (h : arcIndex K x = arcIndex K y) :
    x - y ∈ strip p (p / K) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hx1 : (K * x.val / p) * p ≤ K * x.val := Nat.div_mul_le_self _ _
  have hx2 : K * x.val < (K * x.val / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  have hy1 : (K * y.val / p) * p ≤ K * y.val := Nat.div_mul_le_self _ _
  have hy2 : K * y.val < (K * y.val / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  have hjj : K * x.val / p = K * y.val / p := h
  rw [hjj] at hx1 hx2
  have hx2' : K * x.val < K * y.val / p * p + p := by
    rw [Nat.succ_mul] at hx2; exact hx2
  have hy2' : K * y.val < K * y.val / p * p + p := by
    rw [Nat.succ_mul] at hy2; exact hy2
  -- K * |vx − vy| < p hence |vx − vy| ≤ p / K
  have hKd1 : x.val ≤ y.val + p / K := by
    rcases Nat.lt_or_ge x.val (y.val + 1) with hlt | hge
    · exact (Nat.lt_succ_iff.mp hlt).trans (Nat.le_add_right _ _)
    · have hmul : K * (x.val - y.val) = K * x.val - K * y.val :=
        Nat.mul_sub_left_distrib K x.val y.val
      have hKyKx : K * y.val ≤ K * x.val :=
        Nat.mul_le_mul_left K (by omega)
      have hupper : K * x.val < p + K * y.val := by
        calc
          K * x.val < (K * y.val / p + 1) * p := hx2
          _ = (K * y.val / p) * p + p := by ring
          _ ≤ K * y.val + p := Nat.add_le_add_right hy1 p
          _ = p + K * y.val := Nat.add_comm _ _
      have hK1 : K * (x.val - y.val) < p := by
        rw [hmul]
        exact (Nat.sub_lt_iff_lt_add hKyKx).mpr hupper
      have : x.val - y.val ≤ p / K := by
        refine Nat.le_div_iff_mul_le hK |>.mpr ?_
        calc (x.val - y.val) * K = K * (x.val - y.val) := Nat.mul_comm _ _
          _ ≤ p := Nat.le_of_lt hK1
      omega
  have hKd2 : y.val ≤ x.val + p / K := by
    rcases Nat.lt_or_ge y.val (x.val + 1) with hlt | hge
    · exact (Nat.lt_succ_iff.mp hlt).trans (Nat.le_add_right _ _)
    · have hmul : K * (y.val - x.val) = K * y.val - K * x.val :=
        Nat.mul_sub_left_distrib K y.val x.val
      have hKxKy : K * x.val ≤ K * y.val :=
        Nat.mul_le_mul_left K (by omega)
      have hupper : K * y.val < p + K * x.val := by
        calc
          K * y.val < (K * y.val / p + 1) * p := hy2
          _ = (K * y.val / p) * p + p := by ring
          _ ≤ K * x.val + p := Nat.add_le_add_right hx1 p
          _ = p + K * x.val := Nat.add_comm _ _
      have hK1 : K * (y.val - x.val) < p := by
        rw [hmul]
        exact (Nat.sub_lt_iff_lt_add hKxKy).mpr hupper
      have : y.val - x.val ≤ p / K := by
        refine Nat.le_div_iff_mul_le hK |>.mpr ?_
        calc (y.val - x.val) * K = K * (y.val - x.val) := Nat.mul_comm _ _
          _ ≤ p := Nat.le_of_lt hK1
      omega
  rw [strip, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hvlt : x.val < p := ZMod.val_lt x
  have hylt : y.val < p := ZMod.val_lt y
  rcases Nat.lt_or_ge x.val y.val with hlt | hge
  · -- x.val < y.val : (x − y).val = p − (y.val − x.val) ≥ p − p/K
    right
    have hyx : (y - x).val = y.val - x.val := ZMod.val_sub (Nat.le_of_lt hlt)
    have hyx0 : y - x ≠ 0 := by
      intro hzero
      have : (y - x).val = 0 := by rw [hzero, ZMod.val_zero]
      omega
    have hneg : (x - y).val = p - (y - x).val := by
      have : NeZero (y - x) := ⟨hyx0⟩
      rw [show x - y = -(y - x) by ring, ZMod.val_neg_of_ne_zero (y - x)]
    omega
  · -- y.val ≤ x.val : (x − y).val = x.val − y.val ≤ p/K
    left
    have hsub : (x - y).val = x.val - y.val := ZMod.val_sub hge
    omega

/-- **The strip bound on the dilation-coincidence count**: `R(d) ≤ StripCount(d − 1)`. -/
theorem dilCoincidence_le_stripCount (K : ℕ) (hK : 0 < K) (d : ZMod p) :
    dilCoincidence p K d ≤ stripCount p (p / K) (d - 1) := by
  rw [dilCoincidence, stripCount]
  refine Finset.card_le_card fun v hv => ?_
  rw [Finset.mem_filter] at hv ⊢
  obtain ⟨hv0, harc⟩ := hv
  refine ⟨hv0, ?_⟩
  have := sub_mem_strip_of_same_arc hK harc
  rwa [show d * v - v = (d - 1) * v by ring] at this

/-- **Exact all-`c` strip average**: summing the strip count over every nonzero dilation `c`
gives exactly `(p − 1) · (|Strip| − 1)` — for each `v ≠ 0`, the map `c ↦ c·v` sweeps the
nonzero residues bijectively, hitting `Strip \ {0}` exactly `|Strip| − 1` times. -/
theorem stripCount_avg (W : ℕ) (hW : W < p) :
    ∑ c ∈ Finset.univ.erase (0 : ZMod p), stripCount p W c
      = (p - 1) * ((strip p W).card - 1) := by
  have hswap : ∑ c ∈ Finset.univ.erase (0 : ZMod p), stripCount p W c
      = ∑ v ∈ Finset.univ.erase (0 : ZMod p),
          ((Finset.univ.erase (0 : ZMod p)).filter (fun c => c * v ∈ strip p W)).card := by
    simp only [stripCount, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hzero_strip : (0 : ZMod p) ∈ strip p W := by
    rw [strip, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Or.inl (by rw [ZMod.val_zero]; omega)⟩
  have hinner : ∀ v ∈ Finset.univ.erase (0 : ZMod p),
      ((Finset.univ.erase (0 : ZMod p)).filter (fun c => c * v ∈ strip p W)).card
        = (strip p W).card - 1 := by
    intro v hv
    have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
    have himg : (Finset.univ.erase (0 : ZMod p)).filter (fun c => c * v ∈ strip p W)
        = ((strip p W).erase 0).image (fun w => w * v⁻¹) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
        Finset.mem_image, and_true]
      constructor
      · rintro ⟨hc0, hcs⟩
        exact ⟨c * v, ⟨mul_ne_zero hc0 hv0, hcs⟩, by field_simp⟩
      · rintro ⟨w, ⟨hw0, hws⟩, rfl⟩
        constructor
        · exact mul_ne_zero hw0 (inv_ne_zero hv0)
        · rwa [show w * v⁻¹ * v = w by field_simp]
    rw [himg, Finset.card_image_of_injective _ (fun a b hab => by
      have : a * v⁻¹ * v = b * v⁻¹ * v := by rw [hab]
      rwa [mul_assoc, mul_assoc, inv_mul_cancel₀ hv0, mul_one, mul_one] at this),
      Finset.card_erase_of_mem hzero_strip]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

variable (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
  (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H)
  (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)

include h0 hdiv hmul in
/-- **CAPSTONE — the pair certificate reduces to shifted-subgroup strip concentration.** For
every dilation `b`, the same-arc pair count of the coset `b·H` is at most
`|H| + Σ_{d ∈ H, d ≠ 1} #{z ∈ b·H : (d−1)·z ∈ Strip(p/K)}`: bounding short-interval
concentration of coset dilates by the SHIFTED subgroup `H − 1` bounds the pair certificate
(hence, through G80W → G80Y, the character sum). -/
theorem pairCount_le_strip_sum (K : ℕ) (hK : 0 < K) (h1 : (1 : ZMod p) ∈ H) (b : ZMod p)
    (hb : b ≠ 0) :
    ((H ×ˢ H).filter
        (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))).card
      ≤ H.card + ∑ d ∈ H.erase 1,
          ((H.image (fun y => b * y)).filter
            (fun z => (d - 1) * z ∈ strip p (p / K))).card := by
  rw [pair_decomposition H h0 hdiv hmul K b, ← Finset.add_sum_erase _ _ h1]
  have hd1 : (H.filter (fun y => arcIndex K (b * (1 * y)) = arcIndex K (b * y))).card
      ≤ H.card := by
    refine Finset.card_le_card (Finset.filter_subset _ _)
  refine Nat.add_le_add hd1 (Finset.sum_le_sum fun d _ => ?_)
  -- per-ratio: coincidence at y forces (d−1)·(b·y) in the strip
  have hinj : Set.InjOn (fun y => b * y) H := fun a _ c _ hac =>
    mul_left_cancel₀ hb hac
  calc (H.filter (fun y => arcIndex K (b * (d * y)) = arcIndex K (b * y))).card
      = ((H.filter (fun y => arcIndex K (b * (d * y)) = arcIndex K (b * y))).image
          (fun y => b * y)).card := by
        rw [Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    _ ≤ ((H.image (fun y => b * y)).filter
          (fun z => (d - 1) * z ∈ strip p (p / K))).card := by
        refine Finset.card_le_card fun z hz => ?_
        rw [Finset.mem_image] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        rw [Finset.mem_filter] at hy ⊢
        obtain ⟨hyH, harc⟩ := hy
        refine ⟨Finset.mem_image_of_mem _ hyH, ?_⟩
        have := sub_mem_strip_of_same_arc hK harc
        rwa [show b * (d * y) - b * y = (d - 1) * (b * y) by ring] at this

end ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction.sub_mem_strip_of_same_arc
#print axioms
  ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction.dilCoincidence_le_stripCount
#print axioms
  ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction.stripCount_avg
#print axioms
  ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction.pairCount_le_strip_sum
