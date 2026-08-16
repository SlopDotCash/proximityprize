/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G100FIntegerLiftSmallDiffCounting
import Mathlib.Algebra.Order.Chebyshev

/-!
# LANE G102F (#466, 2026-07-10): the ADDITIVE lift across `√p` — per-`z` amplification of the
  G80Q terminal object into the difference set `H − H`, with exact multiplicity bookkeeping,
  valid on the window `4W < p` (axiom-clean).

## From multiplicative to additive lift

G100F's counting bound rides the MULTIPLICATIVE ℤ-lift: products of two lifted strip values
stay below `p` only when `2W² < p`, fencing the whole mechanism below `√p` (and G80P proves
that window is regime-disjoint from the prize saddle `W = p/K`). This lane develops the
ADDITIVE relation instead: for two ratios `d, d'` incident to the SAME coset point `z`
(`(d−1)z, (d'−1)z ∈ Strip(W)`), the difference of the lifts is `(d−d')z (mod p)` and has
absolute value `≤ 2W` — so it IS the lift of `(d−d')z` as soon as `4W < p`. The additive
lift is faithful on a window that crosses `√p` and reaches `p/4`.

1. **Additive-lift faithfulness** (`valMinAbs_sub_of_natAbs_le`, `sub_mem_strip_double`,
   `pair_diff_mem_strip_double`): at `4W < p` the difference of two window-`W` strip values
   lies in the window-`2W` strip, with lift exactly the difference of lifts.
2. **Per-`z` amplification with exact multiplicity bookkeeping**
   (`incidentPairs_card_le_mul_ampCount`): if `r_z` ratios are incident to `z`, the
   `r_z(r_z−1)` ordered distinct pairs push forward to directions `c = d − d' ∈ (H−H)∖{0}`
   with `cz ∈ Strip(2W)`; the fiber over a fixed `c` injects into `H ∩ (H+c)`, so
   `r_z(r_z−1) ≤ ρ · #{c ≠ 0 : cz ∈ Strip(2W)}` under the additive-collision bound
   `AddCollisionBound H ρ` (`ρ = max_c #(H∩(H+c))`). Heavy incidence at ONE `z` forces strip
   incidence of the `n²`-sized difference set at the SAME `z`.
3. **CAPSTONE A** (`smallDiffPairs_sq_le_of_addCollisionBound`): summing over `z ∈ b·H` with
   the exact full-sweep cap `#{c ≠ 0 : cz ∈ Strip(2W)} ≤ 4W` (`ampCount_le`) and
   Cauchy–Schwarz over the `n` coset points:
   `sdp(W)² ≤ n·sdp(W) + 4ρ·n²·W` for EVERY window `4W < p` —
   i.e. `sdp ≲ n + 2n√(ρW)`, nontrivial against both trivial caps `min(n², 2Wn)` exactly on
   `ρ < W < n²/(4ρ)`, a window that CROSSES `√p` whenever `ρ < n²/(4√p)` (measured
   `ρ ∈ {4,6}` at every probe cell, so at `β = 2` the window reaches `≈ 4√p` at `n = 128`).
4. **CAPSTONE B** (`smallDiffPairs_sq_le_double_window`): keeping the difference-set
   structure instead of the full sweep, the triple count injects into window-doubled
   incidences: `sdp(W)² ≤ n·sdp(W) + n²·sdp(2W)` for every `4W < p` — the self-referential
   window-doubling relation.
5. **Fence verdicts** (`double_window_bootstrap_non_amplifying`,
   `collision_free_shape_absorbed_by_trivial_caps`): the Capstone-B bootstrap is provably
   NON-AMPLIFYING (any profile `≤ n²` satisfies the relation, so iterating `W → 2W` cannot
   manufacture a contradiction: the quadratic gain is exactly repaid by the `n²` multiplier),
   and the `ρ = n` (collision-free-information) instantiation of Capstone A is absorbed by
   the trivial caps — ALL content of the amplification lives in `ρ ≪ n`.

## Probe findings (`scripts/probes/probe_466_g102f_additive_lift_amplification.py`, 2026-07-10)

Cells `n ∈ {16,32,64,128}`, `β ∈ [2, 3]`, 6 cosets each: (i) the additive-collision maximum
is TINY — `ρ_max ∈ {2,4,6}` with mean `≈ 2.2–2.5` at every cell: `μ_n` is near-difference-
Sidon in evidence, so the parametric capstone has real content; (ii) the per-`z`
amplification inequality holds at every measured `z` and is nearly TIGHT at heavy `z`
(`r(r−1)/(ρ_max·A_z)` up to `1.00`); (iii) Capstone A holds with margin (worst `lhs/rhs`
`0.056`), Capstone B is tighter (worst `0.25`); (iv) with measured `ρ_max` the Capstone-A
bound beats both trivial caps from `W ≈ ρ` through `W ≈ n²/(4ρ) ≈ 4√p` at `n=128, β=2` —
strictly beyond the G100F fence `√(p/2)`; (v) at `β ≥ 2.5` the full-sweep step is the leak:
`A_z/(4W) ≈ 0.05–0.08` (the difference set occupies only `≈ n²/p` of the sweep), while at
`β = 2` it is `0.33–0.6`.

## Honest scope and circularity verdict

No prize claim. The amplification is PARAMETRIC in the additive-collision bound `ρ`: no
in-tree unconditional bound below the trivial `ρ ≤ n` exists (the Stepanov lanes are
refutation verdicts, not collision bounds), and at `ρ = n` Capstone A is provably absorbed
by the trivial caps (`collision_free_shape_absorbed_by_trivial_caps`). The classical
`ρ ≪ n^{2/3}` (Mit'kin / Heath-Brown–Konyagin shifted-subgroup technology) is NOT
formalized; with it, Capstone A would be the first counting bound on the terminal object
crossing `√p` — the probe measures `ρ ≤ 6` at every cell. Even granting small `ρ`, at the
prize saddle `W = p/K`, `β = 2` the bound sits a factor `≈ n^{1/4}√ρ` above the uniform
main term: Capstone A crosses `√p` but does not reach certificate strength. The
self-referential Capstone B closes neither: upward it is non-amplifying
(`double_window_bootstrap_non_amplifying` — the precise circularity verdict, echoing G99's
Esseen non-contraction), and downward the Cauchy–Schwarz step costs exactly the `√K` loss
already fatal in the G80W consumer. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean; no `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification

open ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction
open ArkLib.ProximityGap.Frontier.G80QSmallDifferencePairForm
open ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate
open ArkLib.ProximityGap.Frontier.G100FIntegerLiftSmallDiffCounting

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-! ## Part 1 — the additive ℤ-lift bricks: differences lift faithfully at `4W < p` -/

/-- Converse strip membership: a residue whose minimal-absolute lift is `≤ W` in absolute
value lies in the centered strip of half-width `W` (no side condition). -/
theorem mem_strip_of_valMinAbs_natAbs_le {W : ℕ} {w : ZMod p}
    (h : w.valMinAbs.natAbs ≤ W) : w ∈ strip p W := by
  rw [strip, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hd := ZMod.valMinAbs_def_pos w
  have hvlt : w.val < p := ZMod.val_lt w
  split_ifs at hd with hle
  · left
    rw [hd] at h
    omega
  · right
    rw [hd] at h
    omega

/-- **The additive-lift faithfulness relation.** If two residues have lifts of absolute
value `≤ W` and `4W < p`, the lift of their DIFFERENCE is the difference of their lifts:
`valMinAbs(w₁ − w₂) = valMinAbs(w₁) − valMinAbs(w₂)` in ℤ. This is the additive counterpart
of G100F's multiplicative `valMinAbs_mul_of_natAbs_le`: the multiplicative relation needs
`2W² < p` (below `√p`), the additive one survives all the way to `W < p/4`. -/
theorem valMinAbs_sub_of_natAbs_le {W : ℕ} (hW : 4 * W < p) {w₁ w₂ : ZMod p}
    (h₁ : w₁.valMinAbs.natAbs ≤ W) (h₂ : w₂.valMinAbs.natAbs ≤ W) :
    (w₁ - w₂).valMinAbs = w₁.valMinAbs - w₂.valMinAbs := by
  have hcast : ((Int.cast (w₁.valMinAbs - w₂.valMinAbs) : ZMod p)) = w₁ - w₂ := by
    rw [Int.cast_sub, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  have h2 : 2 * (w₁.valMinAbs - w₂.valMinAbs).natAbs < p := by omega
  rw [← hcast]
  exact valMinAbs_intCast_of_two_mul_abs_lt h2

/-- Differences of window-`W` strip values land in the window-`2W` strip once `4W < p`. -/
theorem sub_mem_strip_double {W : ℕ} (hW : 4 * W < p) {w₁ w₂ : ZMod p}
    (h₁ : w₁ ∈ strip p W) (h₂ : w₂ ∈ strip p W) : w₁ - w₂ ∈ strip p (2 * W) := by
  have hW1 : 2 * W < p := by omega
  have m₁ := valMinAbs_natAbs_le_of_mem_strip hW1 h₁
  have m₂ := valMinAbs_natAbs_le_of_mem_strip hW1 h₂
  apply mem_strip_of_valMinAbs_natAbs_le
  rw [valMinAbs_sub_of_natAbs_le hW m₁ m₂]
  omega

/-- **The key structural observation.** Two ratios `d, d'` incident to the same point `z`
(`(d−1)z` and `(d'−1)z` both in `Strip(W)`) force the DIFFERENCE direction `d − d'` to be
strip-incident at the same `z` at doubled window: `(d−d')z ∈ Strip(2W)`, for `4W < p`. -/
theorem pair_diff_mem_strip_double {W : ℕ} (hW : 4 * W < p) {d d' z : ZMod p}
    (h₁ : (d - 1) * z ∈ strip p W) (h₂ : (d' - 1) * z ∈ strip p W) :
    (d - d') * z ∈ strip p (2 * W) := by
  have h := sub_mem_strip_double hW h₁ h₂
  rwa [show (d - 1) * z - (d' - 1) * z = (d - d') * z by ring] at h

/-- The strip of half-width `V` has at most `2V + 1` elements when `2V < p` (inject the
strip into `[−V, V] ⊂ ℤ` via the minimal-absolute lift). -/
theorem strip_card_le {V : ℕ} (hV : 2 * V < p) : (strip p V).card ≤ 2 * V + 1 := by
  have hle : (strip p V).card ≤ (Finset.Icc (-(V : ℤ)) (V : ℤ)).card := by
    refine Finset.card_le_card_of_injOn (fun w => w.valMinAbs) ?_ ?_
    · intro w hw
      rw [Finset.mem_coe] at hw
      have h := valMinAbs_natAbs_le_of_mem_strip hV hw
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    · intro w _ w' _ h
      calc w = ((w.valMinAbs : ℤ) : ZMod p) := (ZMod.coe_valMinAbs w).symm
        _ = ((w'.valMinAbs : ℤ) : ZMod p) := by
            simp only at h
            rw [h]
        _ = w' := ZMod.coe_valMinAbs w'
  rw [Int.card_Icc] at hle
  omega

/-! ## Part 2 — per-`z` amplification with exact multiplicity bookkeeping -/

/-- The additive-collision bound: every nonzero shift `c` has at most `ρ` additive
collisions `#(H ∩ (H + c)) ≤ ρ`. The trivial value is `ρ = |H|`
(`addCollisionBound_card`); the probe measures `ρ ∈ {2,4,6}` for `μ_n` at every cell —
near-difference-Sidon. No sub-trivial unconditional bound is in-tree; the classical
shifted-subgroup technology (`ρ ≪ n^{2/3}`) is NOT formalized. -/
def AddCollisionBound (H : Finset (ZMod p)) (ρ : ℕ) : Prop :=
  ∀ c : ZMod p, c ≠ 0 → (H.filter (fun x => x - c ∈ H)).card ≤ ρ

/-- The trivial additive-collision bound `ρ = |H|` always holds. -/
theorem addCollisionBound_card (H : Finset (ZMod p)) : AddCollisionBound H H.card :=
  fun _ _ => Finset.card_filter_le _ _

/-- The per-`z` incident-pair set: ordered pairs of DISTINCT ratios `d ≠ d'` (both `≠ 1`)
whose small differences at `z` both land in the window-`W` strip. Its cardinality is
`r_z(r_z − 1)` for `r_z` the incident-ratio count at `z`. -/
def incidentPairs (H : Finset (ZMod p)) (W : ℕ) (z : ZMod p) :
    Finset (ZMod p × ZMod p) :=
  ((H.erase 1) ×ˢ (H.erase 1)).filter
    (fun q => q.1 ≠ q.2 ∧ (q.1 - 1) * z ∈ strip p W ∧ (q.2 - 1) * z ∈ strip p W)

/-- **Per-`z` amplification with exact multiplicity bookkeeping.** The incident pairs at `z`
push forward along `(d, d') ↦ d − d'` into the nonzero directions `c` with `cz ∈ Strip(2W)`
(additive-lift faithfulness), and the fiber over each `c` injects into `H ∩ (H + c)`:
`#incidentPairs ≤ ρ · #{c ≠ 0 : cz ∈ Strip(2W)}` under `AddCollisionBound H ρ`, `4W < p`.
Probe: nearly tight at heavy `z` (ratio up to `1.00`). -/
theorem incidentPairs_card_le_mul_ampCount (H : Finset (ZMod p)) {W ρ : ℕ}
    (hW : 4 * W < p) (hρ : AddCollisionBound H ρ) (z : ZMod p) :
    (incidentPairs H W z).card
      ≤ ρ * ((Finset.univ.erase (0 : ZMod p)).filter
          (fun c => c * z ∈ strip p (2 * W))).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun q => q.1 - q.2) ?_ ρ ?_
  · rintro ⟨d, d'⟩ hq
    rw [incidentPairs, Finset.mem_filter] at hq
    obtain ⟨-, hne, h₁, h₂⟩ := hq
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hne, Finset.mem_univ _⟩, ?_⟩
    exact pair_diff_mem_strip_double hW h₁ h₂
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_erase] at hc
    refine le_trans (Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_) (hρ c hc.1.1)
    · rintro ⟨d, d'⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter, incidentPairs,
        Finset.mem_product] at hq
      obtain ⟨⟨⟨hd, hd'⟩, -, -, -⟩, hdc⟩ := hq
      have hdc' : d - d' = c := hdc
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_of_mem_erase hd, ?_⟩
      have hd2 : d - c = d' := by rw [← hdc']; ring
      rw [hd2]
      exact Finset.mem_of_mem_erase hd'
    · rintro ⟨d₁, d₁'⟩ hq₁ ⟨d₂, d₂'⟩ hq₂ h
      simp only [Finset.mem_coe, Finset.mem_filter] at hq₁ hq₂
      have h1 : d₁ = d₂ := h
      have h2 : d₁' = d₂' := by
        have e : d₁ - d₁' = d₂ - d₂' := hq₁.2.trans hq₂.2.symm
        rw [h1] at e
        exact sub_right_injective e
      rw [Prod.mk.injEq]
      exact ⟨h1, h2⟩

/-- **The full-sweep amplification cap.** For `z ≠ 0` the number of nonzero directions `c`
with `cz ∈ Strip(2W)` is at most `4W` (exact sweep: `c ↦ cz` injects into the strip minus
`0`). This cap ignores the `c ∈ H − H` restriction — the honest leak of Capstone A at
`β > 2`, where the difference set occupies only `≈ n²/p` of the sweep. -/
theorem ampCount_le {W : ℕ} (hW : 4 * W < p) {z : ZMod p} (hz : z ≠ 0) :
    ((Finset.univ.erase (0 : ZMod p)).filter
        (fun c => c * z ∈ strip p (2 * W))).card ≤ 4 * W := by
  have h0strip : (0 : ZMod p) ∈ strip p (2 * W) := by
    rw [strip, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Or.inl ?_⟩
    rw [ZMod.val_zero]
    exact Nat.zero_le _
  have hle : ((Finset.univ.erase (0 : ZMod p)).filter
      (fun c => c * z ∈ strip p (2 * W))).card ≤ ((strip p (2 * W)).erase 0).card := by
    refine Finset.card_le_card_of_injOn (fun c => c * z) ?_ ?_
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_erase] at hc
      simp only [Finset.mem_coe, Finset.mem_erase]
      exact ⟨mul_ne_zero hc.1.1 hz, hc.2⟩
    · intro c _ c' _ h
      have h' : c * z = c' * z := h
      exact mul_right_cancel₀ hz h'
  rw [Finset.card_erase_of_mem h0strip] at hle
  have hcard := strip_card_le (p := p) (V := 2 * W) (by omega)
  omega

/-- Per-`z` square split: `r_z² ≤ #incidentPairs(z) + r_z` (diagonal extraction; in fact
equality, stated as the inequality the capstones consume). -/
theorem sq_incident_le (H : Finset (ZMod p)) (W : ℕ) (z : ZMod p) :
    ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card ^ 2
      ≤ (incidentPairs H W z).card
        + ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card := by
  classical
  set I := (H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W) with hI
  have hQ : incidentPairs H W z = (I ×ˢ I).filter (fun q => q.1 ≠ q.2) := by
    ext ⟨u, v⟩
    simp only [incidentPairs, hI, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsplit := Finset.card_filter_add_card_filter_not (s := I ×ˢ I)
    (fun q => q.1 ≠ q.2)
  have hdiag : ((I ×ˢ I).filter (fun q => ¬ q.1 ≠ q.2)).card ≤ I.card := by
    refine Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_
    · rintro ⟨u, v⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
      simp only [Finset.mem_coe]
      exact hq.1.1
    · rintro ⟨u, v⟩ hq ⟨u', v'⟩ hq' h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        not_ne_iff] at hq hq'
      have h1 : u = u' := h
      rw [Prod.mk.injEq]
      exact ⟨h1, by rw [← hq.2, ← hq'.2, h1]⟩
  have hprod : (I ×ˢ I).card = I.card ^ 2 := by
    rw [Finset.card_product]
    ring
  rw [hQ, ← hprod, ← hsplit]
  omega

/-! ## Part 3 — global sums: Cauchy–Schwarz over the coset and the two amplification caps -/

/-- **Master Cauchy–Schwarz inequality.** For every window `W` (no size condition):
`sdp(W)² ≤ n·(Σ_{z ∈ b·H} #incidentPairs(z)) + n·sdp(W)` — the square of the terminal pair
count is controlled by the total per-`z` amplification mass. The Cauchy–Schwarz step over
the `n` coset points is where the downward use of Capstone B loses exactly `√K`. -/
theorem smallDiffPairs_sq_le_card_mul_sum (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (W : ℕ) (b : ZMod p) (hb : b ≠ 0) :
    (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card)
        + H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
            (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card := by
  classical
  have hL0 : (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
      (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
      = ∑ z ∈ H.image (fun y => b * y),
          ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card := by
    rw [← strip_sum_eq_smallDiffPairs H h0 hdiv hmul W b hb]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hCcard : (H.image (fun y => b * y)).card = H.card :=
    Finset.card_image_of_injective _ (mul_right_injective₀ hb)
  have hCS : (∑ z ∈ H.image (fun y => b * y),
        ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card) ^ 2
      ≤ (H.image (fun y => b * y)).card * ∑ z ∈ H.image (fun y => b * y),
          ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq
      (s := H.image (fun y => b * y))
      (f := fun z => ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card)
  have hsplit : ∑ z ∈ H.image (fun y => b * y),
        ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card ^ 2
      ≤ (∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card)
        + ∑ z ∈ H.image (fun y => b * y),
            ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => sq_incident_le H W z
  rw [hL0]
  calc (∑ z ∈ H.image (fun y => b * y),
        ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card) ^ 2
      ≤ (H.image (fun y => b * y)).card * ∑ z ∈ H.image (fun y => b * y),
          ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card ^ 2 := hCS
    _ ≤ (H.image (fun y => b * y)).card
          * ((∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card)
            + ∑ z ∈ H.image (fun y => b * y),
                ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card) :=
        Nat.mul_le_mul_left _ hsplit
    _ = H.card * (∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card)
          + H.card * ∑ z ∈ H.image (fun y => b * y),
              ((H.erase 1).filter (fun d => (d - 1) * z ∈ strip p W)).card := by
        rw [hCcard, Nat.mul_add]

/-- **Form-A global amplification mass**: under the additive-collision bound, the total
per-`z` incident-pair mass is at most `n·ρ·4W` (per-`z` amplification + full-sweep cap). -/
theorem sum_incidentPairs_le_of_addCollisionBound (H : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ H) {W ρ : ℕ} (hW : 4 * W < p)
    (hρ : AddCollisionBound H ρ) (b : ZMod p) (hb : b ≠ 0) :
    ∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card
      ≤ H.card * (ρ * (4 * W)) := by
  have hbound : ∀ z ∈ H.image (fun y => b * y),
      (incidentPairs H W z).card ≤ ρ * (4 * W) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact mul_ne_zero hb (fun h => h0 (h ▸ hy))
    calc (incidentPairs H W z).card
        ≤ ρ * ((Finset.univ.erase (0 : ZMod p)).filter
            (fun c => c * z ∈ strip p (2 * W))).card :=
          incidentPairs_card_le_mul_ampCount H hW hρ z
      _ ≤ ρ * (4 * W) := Nat.mul_le_mul_left _ (ampCount_le hW hz0)
  calc ∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card
      ≤ (H.image (fun y => b * y)).card * (ρ * (4 * W)) := by
        have h := Finset.sum_le_card_nsmul _ _ _ hbound
        simpa [nsmul_eq_mul] using h
    _ ≤ H.card * (ρ * (4 * W)) :=
        Nat.mul_le_mul_right _ Finset.card_image_le

/-- **Form-B global amplification mass**: KEEPING the difference-set structure, the triple
count `(z, d, d')` injects into `H × (window-2W incidences)` via
`(z, d, d') ↦ (d', (d/d', d'z))`, so the total incident-pair mass is at most
`n · sdp(2W)` — the window-doubling relation. -/
theorem sum_incidentPairs_le_double_window (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : 4 * W < p) (b : ZMod p) (hb : b ≠ 0) :
    ∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card
      ≤ H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p (2 * W))).card := by
  classical
  set T : Finset ((ZMod p) × ((ZMod p) × (ZMod p))) :=
    ((H.image (fun y => b * y)) ×ˢ ((H.erase 1) ×ˢ (H.erase 1))).filter
      (fun q => q.2.1 ≠ q.2.2 ∧ (q.2.1 - 1) * q.1 ∈ strip p W
        ∧ (q.2.2 - 1) * q.1 ∈ strip p W) with hT
  set Inc2 : Finset ((ZMod p) × (ZMod p)) :=
    ((H.erase 1) ×ˢ (H.image (fun y => b * y))).filter
      (fun q => (q.1 - 1) * q.2 ∈ strip p (2 * W)) with hInc2
  have hTcard : T.card = ∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card := by
    rw [hT, Finset.card_filter, Finset.sum_product]
    simp only [incidentPairs, Finset.card_filter]
  have hmap : T.card ≤ ((H.erase 1) ×ˢ Inc2).card := by
    refine Finset.card_le_card_of_injOn
      (fun q => (q.2.2, (q.2.1 * q.2.2⁻¹, q.2.2 * q.1))) ?_ ?_
    · rintro ⟨z, d, d'⟩ hq
      simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hzC, hd, hd'⟩, hne, h₁, h₂⟩ := hq
      have hdH : d ∈ H := Finset.mem_of_mem_erase hd
      have hd'H : d' ∈ H := Finset.mem_of_mem_erase hd'
      have hd'0 : d' ≠ 0 := fun h => h0 (h ▸ hd'H)
      simp only [Finset.mem_coe, Finset.mem_product]
      refine ⟨hd', ?_⟩
      rw [hInc2, Finset.mem_filter, Finset.mem_product]
      have hratio1 : d * d'⁻¹ ≠ 1 := by
        intro h
        apply hne
        have h' := congrArg (· * d') h
        simpa [mul_assoc, inv_mul_cancel₀ hd'0] using h'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzC
      refine ⟨⟨Finset.mem_erase.mpr ⟨hratio1, hdiv d hdH d' hd'H⟩, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨d' * y, hmul d' hd'H y hy, by ring⟩
      · have hkey : (d * d'⁻¹ - 1) * (d' * (b * y)) = (d - d') * (b * y) := by
          field_simp
        show (d * d'⁻¹ - 1) * (d' * (b * y)) ∈ strip p (2 * W)
        rw [hkey]
        exact pair_diff_mem_strip_double hW h₁ h₂
    · rintro ⟨z₁, d₁, d₁'⟩ hq₁ ⟨z₂, d₂, d₂'⟩ hq₂ heq
      simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product] at hq₁ hq₂
      obtain ⟨⟨-, -, hd₁'⟩, -, -, -⟩ := hq₁
      have h₁0 : d₁' ≠ 0 := fun h => h0 (h ▸ Finset.mem_of_mem_erase hd₁')
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2, h3⟩ := heq
      subst h1
      have hd : d₁ = d₂ := by
        have h' := congrArg (· * d₁') h2
        simpa [mul_assoc, inv_mul_cancel₀ h₁0] using h'
      have hz : z₁ = z₂ := mul_left_cancel₀ h₁0 h3
      simp only [Prod.mk.injEq]
      exact ⟨hz, hd, trivial⟩
  have hInc2card : Inc2.card
      = (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p (2 * W))).card := by
    rw [← strip_sum_eq_smallDiffPairs H h0 hdiv hmul (2 * W) b hb]
    rw [hInc2, Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  calc ∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card
      = T.card := hTcard.symm
    _ ≤ ((H.erase 1) ×ˢ Inc2).card := hmap
    _ = (H.erase 1).card * Inc2.card := Finset.card_product _ _
    _ ≤ H.card * Inc2.card := Nat.mul_le_mul_right _ Finset.card_erase_le
    _ = H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p (2 * W))).card := by
        rw [hInc2card]

/-! ## Part 4 — CAPSTONES: the two amplification inequalities on the terminal object -/

/-- **CAPSTONE A — the additive-lift amplification bound, valid across `√p`.** For every
prime `p`, multiplicative `H` (`0 ∉ H`, closed under `·` and `/`), every dilation `b ≠ 0`,
every window `4W < p`, and every additive-collision bound `ρ`:

`smallDiffPairs(b·H, W)² ≤ n·smallDiffPairs(b·H, W) + 4ρ·W·n²`,

i.e. `sdp ≲ n + 2n√(ρW)` — nontrivial against BOTH trivial caps `min(n², 2Wn)` exactly on
the window `ρ < W < n²/(4ρ)`, which crosses `√p` whenever `ρ < n²/(4√p)` (probe: `ρ ≤ 6`
at every measured cell). This is the first in-tree counting statement on the G80Q terminal
object whose validity window extends beyond the G100F/G80P integer-lift fence `√(p/2)`,
reaching `W < p/4`. -/
theorem smallDiffPairs_sq_le_of_addCollisionBound (H : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W ρ : ℕ} (hW : 4 * W < p) (hρ : AddCollisionBound H ρ) (b : ZMod p) (hb : b ≠ 0) :
    (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + 4 * ρ * W * H.card ^ 2 := by
  have hmaster := smallDiffPairs_sq_le_card_mul_sum H h0 hdiv hmul W b hb
  have hsum := sum_incidentPairs_le_of_addCollisionBound H h0 hW hρ b hb
  calc (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card)
          + H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
              (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card := hmaster
    _ ≤ H.card * (H.card * (ρ * (4 * W)))
          + H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
              (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hsum) _
    _ = H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + 4 * ρ * W * H.card ^ 2 := by ring

/-- **CAPSTONE B — the window-doubling relation (the self-referential form).** For every
window `4W < p`:

`smallDiffPairs(b·H, W)² ≤ n·smallDiffPairs(b·H, W) + n²·smallDiffPairs(b·H, 2W)`.

Heavy pair mass at window `W` forces pair mass at window `2W` — with NO collision
hypothesis. The fence: this relation is provably non-amplifying upward
(`double_window_bootstrap_non_amplifying`) and loses `√K` downward (the Cauchy–Schwarz
step), so it cannot close the certificate by itself; it is the exact circularity content
of the amplification loop. -/
theorem smallDiffPairs_sq_le_double_window (H : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : 4 * W < p) (b : ZMod p) (hb : b ≠ 0) :
    (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + H.card ^ 2 * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
            (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p (2 * W))).card := by
  have hmaster := smallDiffPairs_sq_le_card_mul_sum H h0 hdiv hmul W b hb
  have hsum := sum_incidentPairs_le_double_window H h0 hdiv hmul hW b hb
  calc (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (∑ z ∈ H.image (fun y => b * y), (incidentPairs H W z).card)
          + H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
              (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card := hmaster
    _ ≤ H.card * (H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
            (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p (2 * W))).card)
          + H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
              (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hsum) _
    _ = H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + H.card ^ 2 * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
            (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p (2 * W))).card := by ring

/-- **Unconditional instantiation** at the trivial collision bound `ρ = n`:
`sdp(W)² ≤ n·sdp(W) + 4W·n³` for every `4W < p`, zero named hypotheses. Provably absorbed
by the trivial caps (`collision_free_shape_absorbed_by_trivial_caps`) — recorded to make
the honest content explicit: everything lives in `ρ ≪ n`. -/
theorem smallDiffPairs_sq_le_unconditional (H : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : 4 * W < p) (b : ZMod p) (hb : b ≠ 0) :
    (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + 4 * W * H.card ^ 3 := by
  have h := smallDiffPairs_sq_le_of_addCollisionBound H h0 hdiv hmul hW
    (addCollisionBound_card H) b hb
  calc (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + 4 * H.card * W * H.card ^ 2 := h
    _ = H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + 4 * W * H.card ^ 3 := by ring

/-! ## Part 5 — FENCE verdicts: the precise circularity content -/

/-- **The Capstone-B bootstrap is non-amplifying.** Any constant pair-count profile
`Λ ≤ n²` satisfies the window-doubling relation `Λ² ≤ nΛ + n²Λ`, so iterating
`W → 2W → 4W → …` from any sub-maximal assumed mass can never force a contradiction: the
quadratic gain of Cauchy–Schwarz is exactly repaid by the `n²` triple-injection
multiplier. The fixed point of the map `x ↦ (x² − nx)/n²` sits at `x = n² + n`, ABOVE the
absolute cap `n²`. This is the precise circularity verdict for the additive-lift
amplification loop (the analogue of G99's Esseen non-contraction). -/
theorem double_window_bootstrap_non_amplifying {n Λ : ℕ} (h : Λ ≤ n ^ 2) :
    Λ ^ 2 ≤ n * Λ + n ^ 2 * Λ := by nlinarith

/-- **The `ρ = n` shape is absorbed by the trivial caps.** The trivial pair-count caps
`min(n², 2Wn)` already satisfy the unconditional (`ρ = n`) Capstone-A inequality, so the
collision-free instantiation carries no information beyond triviality: ALL content of the
amplification is the gap `ρ ≪ n` (probe: `ρ ≤ 6` everywhere measured; classical
shifted-subgroup bounds give `ρ ≪ n^{2/3}`, not in-tree). -/
theorem collision_free_shape_absorbed_by_trivial_caps (n W : ℕ) :
    min (n ^ 2) (2 * W * n) ^ 2
      ≤ n * min (n ^ 2) (2 * W * n) + 4 * W * n ^ 3 := by
  rcases le_total (n ^ 2) (2 * W * n) with h | h
  · rw [min_eq_left h]
    nlinarith [Nat.mul_le_mul_right (n ^ 2) h]
  · rw [min_eq_right h]
    nlinarith [Nat.mul_le_mul_right (2 * W * n) h]

end ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.mem_strip_of_valMinAbs_natAbs_le
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.valMinAbs_sub_of_natAbs_le
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.sub_mem_strip_double
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.pair_diff_mem_strip_double
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.strip_card_le
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.addCollisionBound_card
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.incidentPairs_card_le_mul_ampCount
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.ampCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.sq_incident_le
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.smallDiffPairs_sq_le_card_mul_sum
open ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification in
#print axioms sum_incidentPairs_le_of_addCollisionBound
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.sum_incidentPairs_le_double_window
open ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification in
#print axioms smallDiffPairs_sq_le_of_addCollisionBound
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.smallDiffPairs_sq_le_double_window
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.smallDiffPairs_sq_le_unconditional
#print axioms
  ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification.double_window_bootstrap_non_amplifying
open ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification in
#print axioms collision_free_shape_absorbed_by_trivial_caps
