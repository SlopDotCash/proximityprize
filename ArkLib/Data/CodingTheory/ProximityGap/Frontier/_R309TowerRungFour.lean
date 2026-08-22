/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R308FourthMomentWeilWeld

/-!
# LANE B2 (#466, r=3 rung, R309): the r=4 extension — the curve-Weil lag
  route BREAKS at depth 2 (measured q-exponent 2.0, no free variable), the
  uniform two-character input is CONTRADICTED already at depth 1 (degenerate
  members, measured q-exponent 1.0), and yet the diagonal-separated lag
  ENDGAME still lands: two off-zero lag-sup inputs at their MEASURED scales
  give the absolute-C DIST rung

## What the probe found (probe_466_r3_tower_rung_four.py; q-ladders to
   ~36000 at m = 9, 12; identities L1/L2 machine-precision)

* **Depth-1 off-zero lags** `lag₁(t) = ∑_j J_{j+t}·conj(J_j)`: measured
  q-exponent **1.016/1.046** — Θ(q), NOT the curve-Weil √q.  Since
  `|J_j|² = q`, `lag₁(t) = q·∑_j e^{i(θ_{j+t}−θ_j)}` and the measured sup
  `≈ (1–3)·q ≈ √m·q` is the pure random-phase scale.  The per-(u,t)
  two-character sums of the R30/R31 expansion contain DEGENERATE members
  (the rational function `(1−uy)/(1−y)·y^{…}` becomes an m-th power), each
  contributing Θ(q): a UNIFORM `TwoCharacterWeilInput` with absolute `C` is
  therefore FALSE for this dual family (implied `C` grows like `√q`); the
  honest classical content is Weil on the nondegenerate members plus exact
  counting of the degenerate ones, i.e. `L ≈ c·√m·q` with `c = O(1)`.
  (The R144-style budgets remain formally correct; their hypotheses simply
  cannot be met at absolute constants — the caps must be fed the corrected
  `L`.)  The H-coset shifts `t ∈ {u', 2u'}` are the SMALLEST lags (0.1–0.3·q)
  — no HD coherence spike.
* **Depth-2 off-zero lags** `lag₂(t) = ∑_c W_{c+t}·conj(W_c)`, `W = S⋆S`:
  measured q-exponent **1.997/2.105** — Gaussian-random `~m^{3/2}q²`, no
  Weil OR Deligne rigidity (would be exponent 1/2 or 1).  Mechanism: the
  depth-2 lag is quartic in `J`; linearizing needs two free `F_q`-variables
  and the family degenerates — **the r=4 extension of the curve-Weil lag
  machinery BREAKS here**.  This is the precise "where r enters": each depth
  doubles the character degree; only depth 1 collapses to one-variable sums.
* **Rigidity of the averages** (bonus): at fixed m and `q ≫ m³`, `K₄`
  descends toward `(1−2/m)²` and `K₈` toward ~1 — the Gaussian values 2, 24
  are small-q artifacts; at prize scale the moment constants are SMALLER
  than Gaussian (the Jacobi angles are Weil-rigid for these statistics),
  with rare heavy-tailed spikes per character.

## Why the endgame still lands (the consumer slack)

The diagonal-separated lag consumers have enormous room: the depth-1 target
`m³q²` sits a factor `m` above `m·(√m·q)²·m = m³q²`… precisely: with
`L² ≤ K·m·q²` (satisfied by the MEASURED `L ≈ c√m·q` at `K = c²`) the fourth
moment is `K₄ = 1 + K` — absolute; with `L₂² ≤ K'·m³·q⁴` (satisfied by the
measured `L₂ ≈ c'·m^{3/2}·q²` at `K' = c'²`) the eighth moment is
`K₈ = (1+K)² + K'` — absolute.  Composed through the R307 sandwich:

  **`distStratum_absoluteC_of_offZeroLags`:
   OffZeroLagBound L (L² ≤ K·m·q²) ∧ OffZeroQuadLagBound L₂ (L₂² ≤ K'·m³·q⁴)
   ⟹ E_DIST ≤ (3·√((1+K)·((1+K)² + K')) + 1215)·m³·q³.**

## FINAL DEPENDENCY GRAPH of the absolute-C r=3 rung (labels honest)

Three equivalent-strength routes, each = two named average/sup inputs:
* lag route (this file): `OffZeroLagBound` (open; trivial `mq`, needs `√m·q`
  — a `√m`-saving; measured `c ≈ 1–3`) ∧ `OffZeroQuadLagBound` (open;
  trivial `2m²q²`, needs `m^{3/2}q²` — a `√m`-saving; measured `c' = O(1)`);
* moment route (R307): `FourthMomentBound` ∧ `EighthMomentBound`;
* tower route (R308): `IterConvEnergyWick@2 ∧ @4`.
REFUTED as sources: absolute pointwise flatness (R305 Gumbel); per-variety
Weil–Deligne at any order (R304); uniform `TwoCharacterWeilInput` at O(1)
(this file, degenerate members); curve/surface rigidity of depth-2 lags
(this file, exponent 2).  Downstream: `DistStratumEnergyBound C ⟹
TripleConvEnergyBound (2C + 288)` (R300 accounting) — the full r=3 core.

CORE OPEN, ON-BGK.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R309TowerRungFour

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount
open ArkLib.ProximityGap.Frontier.R303FourthMomentInterpolation
open ArkLib.ProximityGap.Frontier.R306SixthMomentInterpolation
open ArkLib.ProximityGap.Frontier.R307MomentSandwich

/-! ### Autocorrelation and the lag-Parseval identities -/

section Lag

variable {N : ℕ} [NeZero N]

/-- Cyclic autocorrelation. -/
noncomputable def autocorr (f : ZMod N → ℂ) (t : ZMod N) : ℂ :=
  ∑ j : ZMod N, f (j + t) * (starRingEnd ℂ) (f j)

/-- The DFT of the autocorrelation is the mode power spectrum. -/
theorem hatF_autocorr (ψ : AddChar (ZMod N) ℂ) (f : ZMod N → ℂ) (a : ZMod N) :
    hatF ψ (autocorr f) a = hatF ψ f a * (starRingEnd ℂ) (hatF ψ f a) := by
  unfold hatF autocorr
  calc ∑ t : ZMod N, ψ (a * t) * ∑ j : ZMod N, f (j + t) * (starRingEnd ℂ) (f j)
      = ∑ t : ZMod N, ∑ j : ZMod N,
          ψ (a * t) * (f (j + t) * (starRingEnd ℂ) (f j)) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ j : ZMod N, ∑ t : ZMod N,
          ψ (a * t) * (f (j + t) * (starRingEnd ℂ) (f j)) := Finset.sum_comm
    _ = ∑ j : ZMod N, ∑ s : ZMod N,
          ((starRingEnd ℂ) (ψ (a * j)) * (starRingEnd ℂ) (f j))
            * (ψ (a * s) * f s) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine (Fintype.sum_bijective (fun s : ZMod N => s - j)
          (Equiv.subRight j).bijective
          (fun s => ((starRingEnd ℂ) (ψ (a * j)) * (starRingEnd ℂ) (f j))
            * (ψ (a * s) * f s))
          (fun t => ψ (a * t) * (f (j + t) * (starRingEnd ℂ) (f j)))
          (fun s => ?_)).symm
        show ((starRingEnd ℂ) (ψ (a * j)) * (starRingEnd ℂ) (f j))
            * (ψ (a * s) * f s)
          = ψ (a * (s - j)) * (f (j + (s - j)) * (starRingEnd ℂ) (f j))
        have hjs : j + (s - j) = s := by ring
        have hsplit : a * (s - j) = a * s + -(a * j) := by ring
        rw [hjs, hsplit, map_add_eq_mul, conj_psi ψ (a * j)]
        ring
    _ = (∑ x : ZMod N, ψ (a * x) * f x)
          * (starRingEnd ℂ) (∑ x : ZMod N, ψ (a * x) * f x) := by
        rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun s _ => ?_))
        rw [map_mul (starRingEnd ℂ) (ψ (a * s)) (f s)]
        ring

/-- **Lag Parseval**: the fourth moment of the DFT is `N` times the
autocorrelation energy. -/
theorem fourthMoment_eq_lag_energy {ψ : AddChar (ZMod N) ℂ}
    (hψ : ψ.IsPrimitive) (f : ZMod N → ℂ) :
    ∑ a : ZMod N, ‖hatF ψ f a‖ ^ 4 = (N : ℝ) * ∑ t : ZMod N, ‖autocorr f t‖ ^ 2 := by
  have hpt : ∀ a : ZMod N, ‖hatF ψ f a‖ ^ 4 = ‖hatF ψ (autocorr f) a‖ ^ 2 := by
    intro a
    rw [hatF_autocorr ψ f a, norm_mul, RCLike.norm_conj]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a)]
  exact hatF_parseval hψ (autocorr f)

/-- The zero lag is the sequence energy. -/
theorem norm_autocorr_zero_le (f : ZMod N → ℂ) :
    ‖autocorr f 0‖ ≤ ∑ j : ZMod N, ‖f j‖ ^ 2 := by
  unfold autocorr
  calc ‖∑ j : ZMod N, f (j + 0) * (starRingEnd ℂ) (f j)‖
      ≤ ∑ j : ZMod N, ‖f (j + 0) * (starRingEnd ℂ) (f j)‖ := norm_sum_le _ _
    _ = ∑ j : ZMod N, ‖f j‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [add_zero, norm_mul, RCLike.norm_conj]
        ring

end Lag

/-! ### The named lag inputs and the endgame -/

section Endgame

variable {u' : ℕ} [NeZero u']

/-- **Depth-1 named input**: off-zero lag sup of the zero-removed ladder.
Trivial bound `mq`; the needed scale is `√m·q` (a `√m` saving); measured
`sup ≈ (1–3)·q` at m = 9, 12 with q-exponent 1.0 — the uniform curve-Weil
`√q`-shape is REFUTED (degenerate two-character members), and the honest
classical target is Weil-on-nondegenerate + counted degenerates. -/
def OffZeroLagBound (J : ZMod (3 * u') → ℂ) (L : ℝ) : Prop :=
  ∀ t : ZMod (3 * u'), t ≠ 0 → ‖autocorr (Sfun J) t‖ ≤ L

/-- **Depth-2 named input**: off-zero lag sup of the self-convolution.
Trivial bound `≈ 2m²q²`; needed scale `m^{3/2}·q²` (a `√m` saving); measured
q-exponent 2.0 (Gaussian-random — NO Weil/Deligne rigidity survives at
depth 2; this is where the r=4 curve-Weil extension breaks). -/
def OffZeroQuadLagBound (J : ZMod (3 * u') → ℂ) (L₂ : ℝ) : Prop :=
  ∀ t : ZMod (3 * u'), t ≠ 0 →
    ‖autocorr (conv2 (Sfun J) (Sfun J)) t‖ ≤ L₂

/-- **Depth-1 consumer**: the off-zero lag sup at `L² ≤ K·m·q²` gives the
quartic moment at the absolute constant `1 + K`. -/
theorem fourthMomentBound_of_offZeroLag {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {L K : ℝ}
    (hL0 : 0 ≤ L)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hlag : OffZeroLagBound J L)
    (hreg : L ^ 2 ≤ K * ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 2) :
    FourthMomentBound ψ J q (1 + K) := by
  unfold FourthMomentBound
  have hm0 : (0 : ℝ) < ((3 * u' : ℕ) : ℝ) := by
    have := NeZero.ne u'
    positivity
  have hzero : ‖autocorr (Sfun J) 0‖ ≤ ((3 * u' : ℕ) : ℝ) * q := by
    calc ‖autocorr (Sfun J) 0‖
        ≤ ∑ j : ZMod (3 * u'), ‖Sfun J j‖ ^ 2 := norm_autocorr_zero_le _
      _ ≤ ∑ _j : ZMod (3 * u'), (q : ℝ) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          unfold Sfun
          split_ifs with h
          · exact hJ j
          · have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
            simpa using hq0
      _ = ((3 * u' : ℕ) : ℝ) * q := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
  have hsplit : ∑ t : ZMod (3 * u'), ‖autocorr (Sfun J) t‖ ^ 2
      ≤ (((3 * u' : ℕ) : ℝ) * q) ^ 2 + ((3 * u' : ℕ) : ℝ) * L ^ 2 := by
    have hpt : ∀ t : ZMod (3 * u'), ‖autocorr (Sfun J) t‖ ^ 2
        ≤ if t = 0 then (((3 * u' : ℕ) : ℝ) * q) ^ 2 else L ^ 2 := by
      intro t
      by_cases ht : t = 0
      · rw [if_pos ht, ht]
        exact pow_le_pow_left₀ (norm_nonneg _) hzero 2
      · rw [if_neg ht]
        exact pow_le_pow_left₀ (norm_nonneg _) (hlag t ht) 2
    calc ∑ t : ZMod (3 * u'), ‖autocorr (Sfun J) t‖ ^ 2
        ≤ ∑ t : ZMod (3 * u'),
            (if t = 0 then (((3 * u' : ℕ) : ℝ) * q) ^ 2 else L ^ 2) :=
          Finset.sum_le_sum (fun t _ => hpt t)
      _ = (((3 * u' : ℕ) : ℝ) * q) ^ 2
            + ∑ t ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, L ^ 2 := by
          rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr
            (Finset.mem_univ (0 : ZMod (3 * u'))))]
          rw [Finset.sum_singleton, if_pos rfl]
          rw [Finset.sum_congr rfl (fun t ht => by
            rcases Finset.mem_sdiff.mp ht with ⟨_, ht0⟩
            rw [if_neg (by simpa using ht0)])]
          ring
      _ ≤ (((3 * u' : ℕ) : ℝ) * q) ^ 2 + ((3 * u' : ℕ) : ℝ) * L ^ 2 := by
          have hcard : (((Finset.univ \ {(0 : ZMod (3 * u'))}).card : ℕ) : ℝ)
              ≤ ((3 * u' : ℕ) : ℝ) := by
            have hle : (Finset.univ \ {(0 : ZMod (3 * u'))}).card
                ≤ (Finset.univ : Finset (ZMod (3 * u'))).card :=
              Finset.card_le_card (fun j _ => Finset.mem_univ j)
            have := Finset.card_univ (α := ZMod (3 * u')) ▸ hle
            calc (((Finset.univ \ {(0 : ZMod (3 * u'))}).card : ℕ) : ℝ)
                ≤ ((Finset.univ : Finset (ZMod (3 * u'))).card : ℝ) := by
                  exact_mod_cast hle
              _ = ((3 * u' : ℕ) : ℝ) := by
                  rw [Finset.card_univ, ZMod.card]
          rw [Finset.sum_const, nsmul_eq_mul]
          have hL2 : (0 : ℝ) ≤ L ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcard hL2]
  have hlagP := fourthMoment_eq_lag_energy hψ (Sfun J)
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
      = ((3 * u' : ℕ) : ℝ) * ∑ t : ZMod (3 * u'), ‖autocorr (Sfun J) t‖ ^ 2 :=
        hlagP
    _ ≤ ((3 * u' : ℕ) : ℝ)
          * ((((3 * u' : ℕ) : ℝ) * q) ^ 2 + ((3 * u' : ℕ) : ℝ) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hsplit hm0.le
    _ ≤ ((3 * u' : ℕ) : ℝ)
          * ((((3 * u' : ℕ) : ℝ) * q) ^ 2
            + ((3 * u' : ℕ) : ℝ) * (K * ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hm0.le
        have := mul_le_mul_of_nonneg_left hreg hm0.le
        linarith [this]
    _ = (1 + K) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := by ring

/-- **Depth-2 consumer**: the depth-1 result plus the off-zero quad-lag sup
at `L₂² ≤ K'·m³·q⁴` gives the octic moment at `(1+K)² + K'`. -/
theorem eighthMomentBound_of_offZeroLags {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {L L₂ K K' : ℝ}
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hlag : OffZeroLagBound J L)
    (hreg : L ^ 2 ≤ K * ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 2)
    (hlag2 : OffZeroQuadLagBound J L₂)
    (hreg2 : L₂ ^ 2 ≤ K' * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 4) :
    EighthMomentBound ψ J q ((1 + K) ^ 2 + K') := by
  unfold EighthMomentBound
  have hm0 : (0 : ℝ) < ((3 * u' : ℕ) : ℝ) := by
    have := NeZero.ne u'
    positivity
  set W : ZMod (3 * u') → ℂ := conv2 (Sfun J) (Sfun J) with hW
  -- zero lag of W = self-convolution energy ≤ (1+K)·m²·q² via the depth-1 result
  have h4 := fourthMomentBound_of_offZeroLag hψ hL0 hJ hlag hreg
  unfold FourthMomentBound at h4
  have hE2 : ∑ c : ZMod (3 * u'), ‖W c‖ ^ 2
      ≤ (1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
    have hid := fourthMoment_eq_selfConv_energy hψ (Sfun J)
    have hmul : ((3 * u' : ℕ) : ℝ) * ∑ c : ZMod (3 * u'), ‖W c‖ ^ 2
        ≤ ((3 * u' : ℕ) : ℝ)
          * ((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
      rw [hW, ← hid]
      calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 4
          ≤ (1 + K) * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 2 := h4
        _ = ((3 * u' : ℕ) : ℝ)
              * ((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) := by ring
    exact le_of_mul_le_mul_left hmul hm0
  have hzero : ‖autocorr W 0‖ ≤ (1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2 :=
    le_trans (norm_autocorr_zero_le W) hE2
  -- eighth moment = m · lag energy of W
  have hlagP : ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 8
      = ((3 * u' : ℕ) : ℝ) * ∑ t : ZMod (3 * u'), ‖autocorr W t‖ ^ 2 := by
    have h1 := fourthMoment_eq_lag_energy hψ W
    have h2 : ∀ a : ZMod (3 * u'), ‖hatF ψ W a‖ ^ 4 = ‖hatF ψ (Sfun J) a‖ ^ 8 := by
      intro a
      rw [hW, hatF_conv2, norm_mul]
      ring
    rw [← Finset.sum_congr rfl (fun a _ => h2 a)]
    exact h1
  have hsplit : ∑ t : ZMod (3 * u'), ‖autocorr W t‖ ^ 2
      ≤ ((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ 2
        + ((3 * u' : ℕ) : ℝ) * L₂ ^ 2 := by
    have hpt : ∀ t : ZMod (3 * u'), ‖autocorr W t‖ ^ 2
        ≤ if t = 0 then ((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ 2
          else L₂ ^ 2 := by
      intro t
      by_cases ht : t = 0
      · rw [if_pos ht, ht]
        exact pow_le_pow_left₀ (norm_nonneg _) hzero 2
      · rw [if_neg ht]
        exact pow_le_pow_left₀ (norm_nonneg _) (hlag2 t ht) 2
    calc ∑ t : ZMod (3 * u'), ‖autocorr W t‖ ^ 2
        ≤ ∑ t : ZMod (3 * u'),
            (if t = 0 then ((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ 2
              else L₂ ^ 2) := Finset.sum_le_sum (fun t _ => hpt t)
      _ = ((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ 2
            + ∑ t ∈ Finset.univ \ {(0 : ZMod (3 * u'))}, L₂ ^ 2 := by
          rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr
            (Finset.mem_univ (0 : ZMod (3 * u'))))]
          rw [Finset.sum_singleton, if_pos rfl]
          rw [Finset.sum_congr rfl (fun t ht => by
            rcases Finset.mem_sdiff.mp ht with ⟨_, ht0⟩
            rw [if_neg (by simpa using ht0)])]
          ring
      _ ≤ ((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ 2
            + ((3 * u' : ℕ) : ℝ) * L₂ ^ 2 := by
          have hcard : (((Finset.univ \ {(0 : ZMod (3 * u'))}).card : ℕ) : ℝ)
              ≤ ((3 * u' : ℕ) : ℝ) := by
            have hle : (Finset.univ \ {(0 : ZMod (3 * u'))}).card
                ≤ (Finset.univ : Finset (ZMod (3 * u'))).card :=
              Finset.card_le_card (fun j _ => Finset.mem_univ j)
            calc (((Finset.univ \ {(0 : ZMod (3 * u'))}).card : ℕ) : ℝ)
                ≤ ((Finset.univ : Finset (ZMod (3 * u'))).card : ℝ) := by
                  exact_mod_cast hle
              _ = ((3 * u' : ℕ) : ℝ) := by rw [Finset.card_univ, ZMod.card]
          rw [Finset.sum_const, nsmul_eq_mul]
          have hL2 : (0 : ℝ) ≤ L₂ ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcard hL2]
  calc ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 8
      = ((3 * u' : ℕ) : ℝ) * ∑ t : ZMod (3 * u'), ‖autocorr W t‖ ^ 2 := hlagP
    _ ≤ ((3 * u' : ℕ) : ℝ)
          * (((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ 2
            + ((3 * u' : ℕ) : ℝ) * L₂ ^ 2) :=
        mul_le_mul_of_nonneg_left hsplit hm0.le
    _ ≤ ((3 * u' : ℕ) : ℝ)
          * (((1 + K) * ((3 * u' : ℕ) : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ 2
            + ((3 * u' : ℕ) : ℝ)
              * (K' * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ hm0.le
        have := mul_le_mul_of_nonneg_left hreg2 hm0.le
        linarith [this]
    _ = ((1 + K) ^ 2 + K') * ((3 * u' : ℕ) : ℝ) ^ 5 * (q : ℝ) ^ 4 := by ring

/-- **THE ENDGAME (headline)**: two off-zero lag-sup inputs at their MEASURED
scales give the absolute-C r=3 DIST rung.  Chained with the R300 accounting
this bounds the full r=3 core `TripleConvEnergyBound (2C + 288)`. -/
theorem distStratum_absoluteC_of_offZeroLags {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {L L₂ K K' : ℝ}
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K) (hK'0 : 0 ≤ K')
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hlag : OffZeroLagBound J L)
    (hreg : L ^ 2 ≤ K * ((3 * u' : ℕ) : ℝ) * (q : ℝ) ^ 2)
    (hlag2 : OffZeroQuadLagBound J L₂)
    (hreg2 : L₂ ^ 2 ≤ K' * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 4) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q
      (3 * Real.sqrt ((1 + K) * ((1 + K) ^ 2 + K')) + 1215) :=
  distStratum_absoluteC_of_fourth_and_eighth hψ
    (by positivity) (by positivity) hJ
    (fourthMomentBound_of_offZeroLag hψ hL0 hJ hlag hreg)
    (eighthMomentBound_of_offZeroLags hψ hL0 hK0 hJ hlag hreg hlag2 hreg2)

end Endgame

end ArkLib.ProximityGap.Frontier.R309TowerRungFour

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R309TowerRungFour in
#print axioms hatF_autocorr
open ArkLib.ProximityGap.Frontier.R309TowerRungFour in
#print axioms fourthMoment_eq_lag_energy
open ArkLib.ProximityGap.Frontier.R309TowerRungFour in
#print axioms norm_autocorr_zero_le
open ArkLib.ProximityGap.Frontier.R309TowerRungFour in
#print axioms fourthMomentBound_of_offZeroLag
open ArkLib.ProximityGap.Frontier.R309TowerRungFour in
#print axioms eighthMomentBound_of_offZeroLags
open ArkLib.ProximityGap.Frontier.R309TowerRungFour in
#print axioms distStratum_absoluteC_of_offZeroLags
