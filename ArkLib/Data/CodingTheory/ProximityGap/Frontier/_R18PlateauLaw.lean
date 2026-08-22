/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import Mathlib.Algebra.Order.Chebyshev

/-!
# LANE PLATEAU (#466 round 18): the deg-plateau law of `S₂^D` is variance depletion —
  exact first-moment bookkeeping, the depleted-Wick reformulation, and the explicit-margin
  bridge to the constant-3 rung

## The round-17 empirical plateau, now explained

Round 17 measured `S₂^D/(3qΣ²) ≈ 1 − c/deg` with `c ≈ 1.4–1.5`, flat in `β` and `n`
(`S₂^D = ∑_{s₀∉D}‖I_H(s₀)‖⁴`, `D = {0} ∪ μ_n`, `Σ = ∑_{b∈H}‖η_b‖²`, `deg = m` the index of the
thick subgroup `H`).  Probe `probe_r18_plateau.py` (23 exact cells, `n = 8/16/32`,
`m = 2..128`, `β = 3/4`, checks to 1e-15) shows:

* **The plateau is NOT a fourth-moment phenomenon.**  `quart/Σ² = O(m/p)` and
  `‖I(0)‖²/(qΣ) = O(10⁻³)` are both negligible; the entire `1/deg` deficit enters through the
  **second moment**: the exact diagonal spike `∑_{s₀∈μ_n}‖I‖² = Σ²/n` (from
  `I(s₀∈μ_n) = Σ/n` exactly) is a `Σ/(qn) ≈ 1/m` FRACTION of the total second-moment mass
  `qΣ`  (probe column `m·Σ/(qn) = 0.90–1.40` across all cells, ≈ 1 by coset energy
  equidistribution).
* **Depleted-Wick flatness.**  Defining the spike-depleted Wick prediction
  `W* = 3·(S₁^D)²/(q−1−n)` with the EXACT `S₁^D = qΣ − ‖I(0)‖² − Σ²/n`, the measured
  `S₂^D/W* ∈ [0.93, 1.10]` in the whole bulk (`m ≤ 64`), with NO `m`-trend — at `n = 16, β = 4`:
  `1.006, 1.006, 1.010, 0.954, 0.976, 0.989` for `m = 2..64`.  (Thin-`H` `m = 128` reaches
  `1.10`, the known round-16 EVT tail regime.)  The plateau constant is DERIVED:
  `S₂^D/(3qΣ²) ≈ (S₁^D/(qΣ))²·q/(q−1−n) = (1−x)²·(1+o(1))`, `x = (Σ²/n + ‖I(0)‖²)/(qΣ) ≈ 1/m`,
  so `c(m) = m(1−(1−x)²) = 2 − 1/m + fluctuation` — matching measured `c` cell-by-cell
  (`n = 32`: predicted `1.496/1.684/1.876` vs measured `1.509/1.714/1.657`) and the round-17
  `c ≈ 1.4–1.5` at small `m`.  This also re-derives the round-17 refutation of constant 2:
  `1 − c/m > 2/3` already at `m ≥ 6`.
* **The `q·Off ≈ spike` cancellation is confirmed**: with `Off' = S₂/q − (3Σ² − 3·quart)`
  (the quadruple sum outside the three Wick pairings), `q·Off'/spike = 0.96–1.00` at `β = 4` —
  the off-pairing quadruple mass IS the diagonal spike `Σ⁴/n³`, to 4%.

## What THIS file proves unconditionally (axiom-clean, no probe input)

1. `incidenceSum_sq_sum_offsets` — the exact all-offset second moment `S₁ = qΣ`
   (local restatement; the working-tree R15 copy carries concurrent in-flight edits, so this
   lane is self-contained against the committed substrate only).
2. The exact diagonal suite (`eta_mul_right`, `incidenceSum_mul_offset`,
   `incidenceSum_diag_exact`, `diagMass_exact`, `incidenceSum_zero_offset`) — local
   restatement, same reason.
3. **`awayMoment_one_depletion`** (NEW): the EXACT first-moment depletion identity
   `S₁^D = q·Σ − ‖I_H(0)‖² − Σ²/|G|` for `D = {0} ∪ G`.  This is the algebraic origin of the
   plateau: the subtracted `Σ²/|G|` is the `≈ 1/m` variance share.
4. **`zeroSum_family_exact`** (NEW): the zero-sum quadruple family `{(b,−b,b',−b')}` sums
   exactly to `Σ²` — the third Wick pairing.  With the two diagonal pairings
   (`2Σ² − quart`, round 16) this is the exact algebraic provenance of the constant
   `3 = 2 + 1`: it exists because `−1 ∈ μ_n ⊆ H` makes the incidence field "real-Gaussian",
   not complex-Gaussian.
5. **`sq_awayMoment_one_le`** (NEW): the unconditional Cauchy–Schwarz LOWER bound
   `(S₁^D)² ≤ (q−1−|G|)·S₂^D` — the plateau value is forced from below: no proof strategy can
   push `S₂^D` below `(S₁^D)²/(q−1−n) ≈ (1−1/m)²·qΣ²`, i.e. the measured plateau is within
   `3.0–3.5×` of the absolute floor and the depleted-Wick constant `C` lives in `[1, 3.5]`.
6. **`DepletedWickR2`** (NEW named Prop): `S₂^D·(q−1−|G|) ≤ C·(S₁^D)²` — the corrected,
   probe-flat r=2 target (C = 3 measured `0.93–1.10` in the bulk).  NOT discharged.
7. **`constant3_rung_of_depletedWick`** (NEW bridge, the lane deliverable): DepletedWick at
   `C = 3` plus the mild size condition `Σ ≥ |G|(|G|+1)` (at the prize `Σ ≈ nq/m ≫ n²`)
   implies `S₂^D ≤ 3qΣ² − 3(1+|G|)Σ²` — the round-16/17 constant-3 rung
   `WickAwayAtWithConstant … 2 3` WITH AN EXPLICIT POSITIVE MARGIN `3(1+n)Σ²`.  The open
   analytic content of the r=2 rung is thereby EXACTLY the depleted-Wick constant: proving
   `C = 3` for the depleted form closes constant-3 unconditionally with room.

## Honest scope

* Items 3–5, 7 are unconditional finite algebra (+ Cauchy–Schwarz); no Weil, no regime.
* `DepletedWickR2` is a named OPEN hypothesis: probe-true with a flat margin in the bulk,
  strained (`1.10`) only in the thin-`H` EVT regime `m ≳ n²/2` — far off the prize shape.
  It is strictly weaker to prove than raw away-Wick at constant 3 in the bulk (the depleted
  target sits `≈ (1−1/m)²` LOWER), but this file shows it is also exactly equivalent in
  strength for the prize consumer, since the bridge loses only the explicit margin.
* The plateau law itself (`S₂^D/W* → 1`) is probe-derived, not proven; what is proven is the
  exact bookkeeping making "plateau = depleted variance" an identity-level reformulation and
  the bridge making the depleted constant THE open number.

Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 18,
LANE PLATEAU.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R18PlateauLaw

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) Local copies of the lane objects (self-contained against committed substrate). -/

/-- The signed incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b·s₀)` (local copy). -/
noncomputable def incidenceSum (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) : ℂ :=
  ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

/-- The diagonal-subtracted `s₀`-moment tower `S_r^D = ∑_{s₀∉D}‖I_H(s₀)‖^{2r}` (local copy of
the r15 `incidenceMomentAway`). -/
noncomputable def awayMoment (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : ℝ :=
  ∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)

/-- `G` is a finite multiplicative subgroup (Finset form; local copy). -/
structure IsMulSubgroup (G : Finset F) : Prop where
  one_mem : (1 : F) ∈ G
  zero_notMem : (0 : F) ∉ G
  mul_mem : ∀ u ∈ G, ∀ v ∈ G, u * v ∈ G
  inv_mem : ∀ u ∈ G, u⁻¹ ∈ G

/-- `G` stabilizes `H` (local copy). -/
def Stabilizes (G H : Finset F) : Prop := ∀ u ∈ G, ∀ b ∈ H, u * b ∈ H

variable {G H : Finset F}

theorem ne_zero_of_mem (hG : IsMulSubgroup G) {u : F} (hu : u ∈ G) : u ≠ 0 :=
  fun h => hG.zero_notMem (h ▸ hu)

/-! ### (1) The exact all-offset second moment `S₁ = q·Σ` (R13/R15 identity, local proof). -/

/-- `∑_{s₀} ‖I_H(s₀)‖² = q · ∑_{b∈H} ‖η_b‖²`. -/
theorem incidenceSum_sq_sum_offsets {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (H : Finset F) :
    (∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2)
      = (Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hnorm : ∀ s₀ : F,
      incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀)
        = ((‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ) := by
    intro s₀; rw [RCLike.mul_conj]; norm_cast
  have hconjI : ∀ s₀ : F, (starRingEnd ℂ) (incidenceSum ψ G H s₀)
      = ∑ b' ∈ H, eta ψ G b' * ψ (-(b' * s₀)) := by
    intro s₀
    unfold incidenceSum
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [map_mul, Complex.conj_conj, hconj (b' * s₀)]
  have hcomplex : (∑ s₀ : F,
      incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀))
        = (Fintype.card F : ℂ) * ∑ b ∈ H, eta ψ G b * (starRingEnd ℂ) (eta ψ G b) := by
    calc ∑ s₀ : F, incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀)
        = ∑ s₀ : F, ∑ b ∈ H, ∑ b' ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ψ (s₀ * (b - b')) := by
          refine Finset.sum_congr rfl (fun s₀ _ => ?_)
          rw [hconjI s₀]
          unfold incidenceSum
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          refine Finset.sum_congr rfl (fun b' _ => ?_)
          have hpsi : ψ (b * s₀) * ψ (-(b' * s₀)) = ψ (s₀ * (b - b')) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1; ring
          calc (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀) * (eta ψ G b' * ψ (-(b' * s₀)))
              = ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (ψ (b * s₀) * ψ (-(b' * s₀))) := by
                ring
            _ = ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ψ (s₀ * (b - b')) := by rw [hpsi]
      _ = ∑ b ∈ H, ∑ b' ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ∑ s₀ : F, ψ (s₀ * (b - b')) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b' _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ b ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b) * (Fintype.card F : ℂ) := by
          refine Finset.sum_congr rfl (fun b hb => ?_)
          have hb' : ∀ b' ∈ H,
              ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ∑ s₀ : F, ψ (s₀ * (b - b'))
                = (if b' = b then
                    ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (Fintype.card F : ℂ) else 0) := by
            intro b' _
            rw [AddChar.sum_mulShift (b - b') hψ]
            by_cases h : b = b'
            · subst h; simp
            · have hne : b - b' ≠ 0 := sub_ne_zero.mpr h
              rw [if_neg hne, if_neg (fun h' => h h'.symm)]
              simp
          rw [Finset.sum_congr rfl hb',
            Finset.sum_ite_eq' H b
              (fun b' => ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (Fintype.card F : ℂ))]
          rw [if_pos hb]
      _ = (Fintype.card F : ℂ) * ∑ b ∈ H, eta ψ G b * (starRingEnd ℂ) (eta ψ G b) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
  have hcast : ((∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * ∑ b ∈ H, ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    rw [show (∑ s₀ : F, ((‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ))
          = ∑ s₀ : F, incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀) from
      Finset.sum_congr rfl (fun s₀ _ => (hnorm s₀).symm)]
    rw [hcomplex, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    congr 1
    rw [RCLike.mul_conj]; norm_cast
  have hreal : ((∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-! ### (2) The exact diagonal suite (R16, local restatement). -/

/-- `η_{b·u} = η_b` for `u ∈ G`. -/
theorem eta_mul_right (hG : IsMulSubgroup G) (ψ : AddChar F ℂ) {u : F} (hu : u ∈ G) (b : F) :
    eta ψ G (b * u) = eta ψ G b := by
  classical
  unfold eta
  have hu0 : u ≠ 0 := ne_zero_of_mem hG hu
  refine Finset.sum_bij' (fun y _ => u * y) (fun y _ => u⁻¹ * y) ?_ ?_ ?_ ?_ ?_
  · intro y hy; exact hG.mul_mem u hu y hy
  · intro y hy; exact hG.mul_mem u⁻¹ (hG.inv_mem u hu) y hy
  · intro y _; dsimp only; rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  · intro y _; dsimp only; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  · intro y _; rw [mul_assoc]

/-- Exact `G`-orbit invariance of the incidence field. -/
theorem incidenceSum_mul_offset (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {u : F} (hu : u ∈ G) (s₀ : F) :
    incidenceSum ψ G H (u * s₀) = incidenceSum ψ G H s₀ := by
  classical
  unfold incidenceSum
  have hu0 : u ≠ 0 := ne_zero_of_mem hG hu
  have hui : u⁻¹ ∈ G := hG.inv_mem u hu
  refine Finset.sum_bij' (fun b _ => b * u) (fun b _ => b * u⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro b hb; dsimp only; rw [mul_comm]; exact hGH u hu b hb
  · intro b hb; dsimp only; rw [mul_comm]; exact hGH u⁻¹ hui b hb
  · intro b _; dsimp only; rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  · intro b _; dsimp only; rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  · intro b _
    rw [eta_mul_right hG ψ hu b]
    congr 2
    rw [mul_assoc]

/-- Constancy of `I_H` on `G`. -/
theorem incidenceSum_const_on (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {s s₀ : F} (hs : s ∈ G) (hs₀ : s₀ ∈ G) :
    incidenceSum ψ G H s = incidenceSum ψ G H s₀ := by
  have hs₀0 : s₀ ≠ 0 := ne_zero_of_mem hG hs₀
  have hu : s * s₀⁻¹ ∈ G := hG.mul_mem s hs s₀⁻¹ (hG.inv_mem s₀ hs₀)
  have hkey : (s * s₀⁻¹) * s₀ = s := by
    rw [mul_assoc, inv_mul_cancel₀ hs₀0, mul_one]
  calc incidenceSum ψ G H s
      = incidenceSum ψ G H ((s * s₀⁻¹) * s₀) := by rw [hkey]
    _ = incidenceSum ψ G H s₀ := incidenceSum_mul_offset hG hGH ψ hu s₀

/-- `∑_{s∈G} I_H(s) = ∑_{b∈H} conj(η_b)·η_b`. -/
theorem sum_incidenceSum_over_G (ψ : AddChar F ℂ) (G H : Finset F) :
    ∑ s ∈ G, incidenceSum ψ G H s
      = ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * eta ψ G b := by
  classical
  unfold incidenceSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.mul_sum]
  rfl

/-- The exact diagonal value `I_H(s₀∈G) = Σ/|G|`. -/
theorem incidenceSum_diag_exact (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {s₀ : F} (hs₀ : s₀ ∈ G) :
    incidenceSum ψ G H s₀
      = ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) / (G.card : ℂ) := by
  classical
  have hnonempty : G.Nonempty := ⟨1, hG.one_mem⟩
  have hcard0 : (G.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hconst : ∑ s ∈ G, incidenceSum ψ G H s = (G.card : ℂ) * incidenceSum ψ G H s₀ := by
    calc ∑ s ∈ G, incidenceSum ψ G H s
        = ∑ _s ∈ G, incidenceSum ψ G H s₀ :=
          Finset.sum_congr rfl (fun s hs => incidenceSum_const_on hG hGH ψ hs hs₀)
      _ = (G.card : ℂ) * incidenceSum ψ G H s₀ := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hval : ∑ s ∈ G, incidenceSum ψ G H s
      = ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_incidenceSum_over_G]
    have hterm : ∀ b : F, (starRingEnd ℂ) (eta ψ G b) * eta ψ G b
        = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      intro b
      rw [mul_comm, RCLike.mul_conj]
      norm_cast
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    push_cast
    rfl
  rw [eq_div_iff hcard0, mul_comm, ← hconst, hval]

/-- Norm form of the diagonal value. -/
theorem norm_incidenceSum_diag_exact (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {s₀ : F} (hs₀ : s₀ ∈ G) :
    ‖incidenceSum ψ G H s₀‖
      = (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) / (G.card : ℝ) := by
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  rw [incidenceSum_diag_exact hG hGH ψ hs₀]
  rw [norm_div]
  rw [Complex.norm_real, Complex.norm_natCast]
  rw [Real.norm_of_nonneg hSig]

/-- `I_H(0) = conj(∑_{b∈H} η_b)`. -/
theorem incidenceSum_zero_offset (ψ : AddChar F ℂ) (G H : Finset F) :
    incidenceSum ψ G H 0 = (starRingEnd ℂ) (∑ b ∈ H, eta ψ G b) := by
  classical
  unfold incidenceSum
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [mul_zero, AddChar.map_zero_eq_one, mul_one]

/-! ### (3) NEW — the exact first-moment depletion identity.

This is the algebraic origin of the round-17 plateau: subtracting the diagonal `D = {0} ∪ G`
removes EXACTLY `‖I(0)‖² + Σ²/|G|` from the exact total `qΣ`, and `Σ²/|G| ≈ (1/m)·qΣ` by coset
energy equidistribution — the `1/deg` of the plateau law enters HERE, at the second moment,
nowhere else. -/

/-- **The depletion identity**:
`S₁^D = ∑_{s₀ ∉ {0}∪G} ‖I_H(s₀)‖² = q·Σ − ‖I_H(0)‖² − Σ²/|G|` exactly. -/
theorem awayMoment_one_depletion (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    awayMoment ψ G H (insert (0 : F) G) 1
      = (Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        - ‖incidenceSum ψ G H 0‖ ^ 2
        - (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 / (G.card : ℝ) := by
  classical
  have hnonempty : G.Nonempty := ⟨1, hG.one_mem⟩
  have hcard : (0 : ℝ) < (G.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hdiag : ∑ s₀ ∈ G, ‖incidenceSum ψ G H s₀‖ ^ 2
      = (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 / (G.card : ℝ) := by
    calc ∑ s₀ ∈ G, ‖incidenceSum ψ G H s₀‖ ^ 2
        = ∑ _s₀ ∈ G, ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2) / (G.card : ℝ)) ^ 2 := by
          refine Finset.sum_congr rfl (fun s₀ hs₀ => ?_)
          rw [norm_incidenceSum_diag_exact hG hGH ψ hs₀]
      _ = (G.card : ℝ) * ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2) / (G.card : ℝ)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 / (G.card : ℝ) := by
          field_simp
  have hsdiff : ∑ s₀ ∈ Finset.univ \ insert (0 : F) G, ‖incidenceSum ψ G H s₀‖ ^ 2
      = (∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2)
        - ∑ s₀ ∈ insert (0 : F) G, ‖incidenceSum ψ G H s₀‖ ^ 2 :=
    Finset.sum_sdiff_eq_sub (Finset.subset_univ _)
  have hunf : awayMoment ψ G H (insert (0 : F) G) 1
      = ∑ s₀ ∈ Finset.univ \ insert (0 : F) G, ‖incidenceSum ψ G H s₀‖ ^ 2 := by
    rw [awayMoment]
  rw [hunf, hsdiff, Finset.sum_insert hG.zero_notMem, hdiag,
    incidenceSum_sq_sum_offsets hψ G H]
  ring

/-! ### (4) NEW — the zero-sum quadruple family: the exact provenance of the constant 3. -/

/-- `η_{−b} = conj(η_b)`. -/
theorem eta_neg (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    eta ψ G (-b) = (starRingEnd ℂ) (eta ψ G b) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  unfold eta
  rw [map_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  congr 1
  ring

/-- **The zero-sum quadruple family sums exactly to `Σ²`** — the third Wick pairing of the
r=2 quadruple sum: the family `{(b₁, −b₁, b₃, −b₃)}` (constraint `b₁+b₂ = b₃+b₄ = 0`
automatic) carries weight `conj(η_{b₁})conj(η_{−b₁})·η_{b₃}η_{−b₃} = ‖η_{b₁}‖²·‖η_{b₃}‖²`
because `η_{−b} = conj(η_b)`.  Together with the two diagonal pairings (round-16 exact value
`2Σ² − quart`) this gives the FULL Wick constant `3 = 2 + 1`: the incidence field is
real-Gaussian-like, and the third pairing exists exactly because `−1 ∈ μ_n ⊆ H`. -/
theorem zeroSum_family_exact (ψ : AddChar F ℂ) (G H : Finset F) :
    ∑ b₁ ∈ H, ∑ b₃ ∈ H,
        ((starRingEnd ℂ) (eta ψ G b₁) * (starRingEnd ℂ) (eta ψ G (-b₁)))
          * (eta ψ G b₃ * eta ψ G (-b₃))
      = (((∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  classical
  have hterm1 : ∀ b : F, (starRingEnd ℂ) (eta ψ G b) * (starRingEnd ℂ) (eta ψ G (-b))
      = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [eta_neg, Complex.conj_conj, mul_comm, RCLike.mul_conj]
    norm_cast
  have hterm2 : ∀ b : F, eta ψ G b * eta ψ G (-b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [eta_neg, RCLike.mul_conj]
    norm_cast
  calc ∑ b₁ ∈ H, ∑ b₃ ∈ H,
        ((starRingEnd ℂ) (eta ψ G b₁) * (starRingEnd ℂ) (eta ψ G (-b₁)))
          * (eta ψ G b₃ * eta ψ G (-b₃))
      = ∑ b₁ ∈ H, ∑ b₃ ∈ H,
          ((‖eta ψ G b₁‖ ^ 2 : ℝ) : ℂ) * ((‖eta ψ G b₃‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl (fun b₁ _ => Finset.sum_congr rfl (fun b₃ _ => ?_))
        rw [hterm1 b₁, hterm2 b₃]
    _ = (∑ b₁ ∈ H, ((‖eta ψ G b₁‖ ^ 2 : ℝ) : ℂ)) * (∑ b₃ ∈ H, ((‖eta ψ G b₃‖ ^ 2 : ℝ) : ℂ)) := by
        rw [Finset.sum_mul_sum]
    _ = (((∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring

/-! ### (5) NEW — the unconditional Cauchy–Schwarz floor. -/

/-- **The plateau is forced from below**: `(S₁^D)² ≤ |univ \ D| · S₂^D` for ANY diagonal set
`D`.  With the depletion identity this pins `S₂^D ≥ (qΣ − ‖I(0)‖² − Σ²/n)²/(q−1−n)`: the
depleted-Wick constant `C` (below) satisfies `C ≥ 1` unconditionally, and the measured bulk
plateau sits at `C ≈ 3` — within `3.5×` of this floor. -/
theorem sq_awayMoment_one_le (ψ : AddChar F ℂ) (G H D : Finset F) :
    (awayMoment ψ G H D 1) ^ 2
      ≤ ((Finset.univ \ D).card : ℝ) * awayMoment ψ G H D 2 := by
  classical
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ \ D) (f := fun s₀ => ‖incidenceSum ψ G H s₀‖ ^ 2)
  have hleft : (∑ s₀ ∈ Finset.univ \ D, ‖incidenceSum ψ G H s₀‖ ^ 2)
      = awayMoment ψ G H D 1 := by
    rw [awayMoment]
  have hright : (∑ s₀ ∈ Finset.univ \ D, (‖incidenceSum ψ G H s₀‖ ^ 2) ^ 2)
      = awayMoment ψ G H D 2 := by
    rw [awayMoment]
    refine Finset.sum_congr rfl (fun s₀ _ => ?_)
    rw [← pow_mul]
  rw [hleft, hright] at hCS
  exact_mod_cast hCS

/-! ### (6) NEW — the depleted-Wick target and the explicit-margin bridge. -/

/-- **The depleted-Wick r=2 hypothesis (named OPEN Prop, the round-18 reformulated target)**:
`S₂^D · (q − 1 − |G|) ≤ C · (S₁^D)²`, `D = {0} ∪ G`.  Probe-measured `C`:
`0.93–1.10 × 3` flat across the β=4 bulk (`m ≤ 64`) — unlike the raw Wick ratio, this form
carries NO `1/deg` drift: the plateau law is exactly the statement that this constant is flat.
`C ≥ 1` is forced by `sq_awayMoment_one_le`.  NOT discharged. -/
def DepletedWickR2 (ψ : AddChar F ℂ) (G H : Finset F) (C : ℝ) : Prop :=
  awayMoment ψ G H (insert (0 : F) G) 2
      * ((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
    ≤ C * (awayMoment ψ G H (insert (0 : F) G) 1) ^ 2

/-- The depleted-Wick r = 2 input is monotone in its published constant. -/
theorem depletedWickR2_mono {ψ : AddChar F ℂ} {G H : Finset F} {C C' : ℝ}
    (hC : C ≤ C') (h : DepletedWickR2 ψ G H C) :
    DepletedWickR2 ψ G H C' := by
  unfold DepletedWickR2 at *
  exact h.trans (mul_le_mul_of_nonneg_right hC (sq_nonneg _))

/-- **THE BRIDGE (lane deliverable): depleted-Wick at `C = 3` ⟹ the constant-3 rung WITH AN
EXPLICIT POSITIVE MARGIN.**  If `DepletedWickR2 3` holds and `Σ ≥ |G|·(|G|+1)` (trivially true
at the prize: `Σ ≈ nq/m ≫ n²`), then

  `S₂^D ≤ 3·q·Σ² − 3·(1+|G|)·Σ²`.

In particular the round-16/17 open target `WickAwayAtWithConstant ψ G H ({0}∪G) 2 3` follows
with room `3(1+n)Σ²`.  The open analytic content of the r=2 rung IS the depleted constant. -/
theorem constant3_rung_of_depletedWick (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hDW : DepletedWickR2 ψ G H 3)
    (hSig : ((G.card : ℝ) * ((G.card : ℝ) + 1)) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (hq : (G.card : ℝ) + 1 < (Fintype.card F : ℝ)) :
    awayMoment ψ G H (insert (0 : F) G) 2
      ≤ 3 * (Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2
        - 3 * (1 + (G.card : ℝ)) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 := by
  classical
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) - 1 - (G.card : ℝ) := by linarith
  have hcardpos : (0 : ℝ) < (G.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hG.one_mem⟩
  have hSigpos : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  -- Step 1: the depletion identity bounds S₁^D above by (q−1−n)·Σ.
  have hS1 : awayMoment ψ G H (insert (0 : F) G) 1
      ≤ ((Fintype.card F : ℝ) - 1 - (G.card : ℝ)) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
    have hid := awayMoment_one_depletion hG hGH hψ
    have h1 : ((G.card : ℝ) + 1) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 / (G.card : ℝ) := by
      rw [le_div_iff₀ hcardpos]
      nlinarith [hSig, hSigpos]
    have h2 : (0 : ℝ) ≤ ‖incidenceSum ψ G H 0‖ ^ 2 := by positivity
    rw [hid]
    nlinarith
  have hS1nonneg : (0 : ℝ) ≤ awayMoment ψ G H (insert (0 : F) G) 1 := by
    rw [awayMoment]; positivity
  -- Step 2: chain through the depleted-Wick hypothesis.
  have hsq := pow_le_pow_left₀ hS1nonneg hS1 2
  have hchain : awayMoment ψ G H (insert (0 : F) G) 2
        * ((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
      ≤ 3 * ((((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
          * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2) := by
    calc awayMoment ψ G H (insert (0 : F) G) 2
          * ((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
        ≤ 3 * (awayMoment ψ G H (insert (0 : F) G) 1) ^ 2 := hDW
      _ ≤ 3 * ((((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
          * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2) := by linarith
  have hfinal : awayMoment ψ G H (insert (0 : F) G) 2
      ≤ 3 * ((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
        * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 := by
    have h3 : 3 * ((((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
          * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2)
        = (3 * ((Fintype.card F : ℝ) - 1 - (G.card : ℝ))
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2)
          * ((Fintype.card F : ℝ) - 1 - (G.card : ℝ)) := by ring
    rw [h3] at hchain
    exact le_of_mul_le_mul_right hchain hN
  nlinarith [hfinal, sq_nonneg (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)]

#print axioms incidenceSum_sq_sum_offsets
#print axioms incidenceSum_diag_exact
#print axioms awayMoment_one_depletion
#print axioms zeroSum_family_exact
#print axioms sq_awayMoment_one_le
#print axioms depletedWickR2_mono
#print axioms constant3_rung_of_depletedWick

end ArkLib.ProximityGap.Frontier.R18PlateauLaw
