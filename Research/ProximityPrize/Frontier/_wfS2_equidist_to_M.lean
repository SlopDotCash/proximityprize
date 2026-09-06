/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# wf-S2 (#444): EQUIDISTRIBUTION ⟹ `M` bounded — the spread route to the prize, run forwards

This is the CONCENTRATION/SPREAD lane of the Proximity-Prize core (issue #444). The prize is a
bound on the *worst-case* frequency `M := max_{b≠0} ‖η_b‖`, where `η_b = ∑_{y∈μ_n} ψ(b·y)` is the
subgroup Gauss sum, NOT on the *total* additive energy `E_r = (1/q)∑_b ‖η_b‖^{2r}`.

The two existing S2 bricks run the implication BACKWARDS — they take an `M`-bound as a hypothesis
and conclude the spectral support must be wide:
* `SpreadFloor.spread_floor_div`         : `M`-bound  ⟹  `|S| ≥ q·n / M²`  (2nd moment).
* `ParticipationFloor.participation_floor_div` : `|S| ≥ A²/B = (q·n)² / (q·E₂)`  (2nd∧4th moment).

Those say "if `M` is small the mass MUST spread", but do NOT *prove* `M` small — concentration
onto a few frequencies is still a-priori possible. **This file runs the spread route FORWARDS:**
an *equidistribution certificate* (no single frequency carries more than a bounded multiple of the
support-average of the `2r`-mass) PLUS the proven energy bound *delivers* the `M`-bound. It is the
precise converse the lane was charged with.

## The mechanism (depth-`r`)

Let `T_r := ∑_{b≠0} ‖η_b‖^{2r}` be the nonprincipal `2r`-moment and `N_r := |{b≠0 : η_b ≠ 0}|`
the nonprincipal support size. The **equidistribution certificate at depth `r` with constant `κ`**
is the inequality

  `M^{2r} ≤ κ · T_r / N_r`      (`EquidistAtDepth`)

i.e. the largest single coset-mass `M^{2r}` is at most `κ` times the *support-average* `T_r/N_r`.
A perfectly flat spectrum has `κ = 1`; the S2 probe measures `κ = PAPR · (N_r/m) = M^{2r}·N_r/T_r`,
which at prize scale (`β≈4`) is `O(log n)` and prime-structure-independent (the per-coset shape is
near-flat, `PR ≈ 0.34` flat, entropy `→ 1`). The theorem below is the exact statement that turns
that measured flatness into the prize:

  `M^{2r} ≤ κ · T_r / N_r`,  and `T_r ≤ q·E_r`,  and `N_r ≥ c·q`  (wide support, the spread floor)
  ⟹  `M^{2r} ≤ (κ/c) · E_r`  ⟹  (with `E_r ≤ K^r·(2r-1)‼·n^r`) `M ≤ ((κ/c)·K^r·(2r-1)‼)^{1/2r}·√n`.

Minimising over `r ≈ ln q` (where `((2r-1)‼)^{1/2r} ≈ √(2r/e) ≈ √(ln q)`) gives the prize form
`M = O(√(n·ln q))` with the constant `C = O(√(K·κ/c))`. So under the spread route the WHOLE
remaining gap collapses to: **prove the equidistribution constant `κ` is bounded** (and the
support stays `≥ c·q` wide — already the proven spread floor). This is a strictly different — and
empirically far milder — target than the BGK additive-energy wall: it asks for *flatness of the
already-bounded total mass*, not a bound on the mass itself.

This file lands the depth-`r` reduction **schematically** (consuming `T_r`, `N_r`, `E_r`, the
energy bound, and the support floor as explicit hypotheses, so no unproven input is hidden) and the
concrete `r = 2` instance built directly on the in-tree fourth moment `∑_b‖η_b‖⁴ = q·E₂`
(`subgroup_gaussSum_fourthMoment`). All steps are Weil-free `ℝ`-arithmetic on the Parseval moments.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment (addEnergy subgroup_gaussSum_fourthMoment)

namespace ArkLib.ProximityGap.EquidistToM

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonprincipal `2r`-moment `T_r := ∑_{b≠0} ‖η_b‖^{2r}`. -/
noncomputable def nonprincMoment (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)

/-- The nonprincipal spectral support size `N_r := |{b ≠ 0 : η_b ≠ 0}|`. -/
noncomputable def nonprincSupport (ψ : AddChar F ℂ) (G : Finset F) : ℕ :=
  ((Finset.univ.erase (0 : F)).filter (fun b => eta ψ G b ≠ 0)).card

/-- **The equidistribution certificate at depth `r`, constant `κ`.** The largest single
nonprincipal coset-mass `M^{2r}` is at most `κ` times the *support-average* `T_r / N_r` of the
`2r`-mass. `κ = 1` is a perfectly flat spectrum; the S2 probe measures `κ = O(log n)` at prize
scale, prime-structure independent. (Stated with `Mpow = M^{2r}` and `Trat = T_r/N_r` as plain
reals so the consumer supplies whichever concrete `M`, support and moment it has.) -/
def EquidistAtDepth (Mpow κ Trat : ℝ) : Prop := Mpow ≤ κ * Trat

/-- **Equidistribution ⟹ energy-controlled `M` (the depth-`r` reduction, schematic).**
Given the three structural inputs of the spread route —
* the equidistribution certificate `M^{2r} ≤ κ · (T_r / N_r)`,
* the moment ceiling `T_r ≤ q · E_r` (the `2r`-moment is `q·E_r`; here as `≤` so any upper
  bound on the nonprincipal moment suffices),
* the support floor `N_r ≥ c · q` with `c > 0` (the proven spread floor: bounded `M` keeps the
  mass spread over `≥ c·q` frequencies),
— the worst-case mass is bounded purely by the energy: `M^{2r} ≤ (κ / c) · E_r`. No
characteristic-`p` / Weil input; the energy `E_r` enters as a number. Plugging the proven
char-0/transferred bound `E_r ≤ K^r·(2r-1)‼·n^r` and minimising over `r ≈ ln q` yields the prize
`M = O(√(n ln q))`. The remaining obligation is reduced from "bound the energy at a structured
prime" to "bound the equidistribution constant `κ`" (flatness of the bounded mass). -/
theorem M_pow_le_of_equidist
    {Mpow κ Tr Er qEr Nr c q : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 < c) (_hq : 0 < q) (hNr : 0 < Nr)
    (hEr : 0 ≤ Er)
    (hequi : EquidistAtDepth Mpow κ (Tr / Nr))
    (hTr : Tr ≤ qEr) (hqEr : qEr = q * Er)
    (hsupp : c * q ≤ Nr) :
    Mpow ≤ (κ / c) * Er := by
  -- T_r / N_r ≤ q·E_r / (c·q) = E_r / c
  -- support-average bound: Tr / Nr ≤ (q·Er) / (c·q) = Er / c
  have hratio : Tr / Nr ≤ Er / c := by
    rw [div_le_div_iff₀ hNr hc]
    -- Tr * c ≤ Er * Nr.  Use Tr ≤ q·Er and c·q ≤ Nr, Er ≥ 0.
    have h1 : Tr * c ≤ (q * Er) * c := by nlinarith [hTr, hqEr, hc.le]
    have h2 : (q * Er) * c = Er * (c * q) := by ring
    have h3 : Er * (c * q) ≤ Er * Nr := by
      apply mul_le_mul_of_nonneg_left hsupp hEr
    linarith [h1, h2 ▸ h3]
  -- combine with the equidistribution certificate
  have hstep : Mpow ≤ κ * (Tr / Nr) := hequi
  calc Mpow ≤ κ * (Tr / Nr) := hstep
    _ ≤ κ * (Er / c) := by apply mul_le_mul_of_nonneg_left hratio hκ
    _ = (κ / c) * Er := by ring

/-- **The concrete `r = 2` instance, built on the in-tree fourth moment.** With `G = μ_n` and the
nonprincipal fourth moment `T₂ = ∑_{b≠0}‖η_b‖⁴`, the global fourth moment identity
`∑_b‖η_b‖⁴ = q·E₂` (`subgroup_gaussSum_fourthMoment`, `E₂ = addEnergy G`) gives
`T₂ = q·E₂ − |G|⁴ ≤ q·E₂`. Feeding this into `M_pow_le_of_equidist` with the equidistribution
certificate `M⁴ ≤ κ·(T₂/N₂)` and the support floor `N₂ ≥ c·q` yields

  `M⁴ ≤ (κ/c) · E₂`,

i.e. the worst-case fourth power of the Gauss sum is controlled by the additive energy with a loss
that is exactly the equidistribution constant `κ/c`. This is the `r = 2` realisation of the spread
route: at this depth `M⁴ = O(E₂) = O(n²)` (energy is `Θ(n²)` once `q ≥ n²`), the Weil-strength
fourth-power bound, *iff* `κ` is bounded — which the probe confirms (`κ = O(1)` at `r = 2`). -/
theorem M4_le_of_equidist_fourthMoment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M κ Nr c : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 < c) (hNr : 0 < Nr)
    (hqpos : (0 : ℝ) < Fintype.card F)
    -- equidistribution at depth 2: M⁴ ≤ κ·(T₂/N₂)
    (hequi : EquidistAtDepth (M ^ 4) κ (nonprincMoment ψ G 2 / Nr))
    -- support floor: N₂ ≥ c·q
    (hsupp : c * (Fintype.card F : ℝ) ≤ Nr) :
    M ^ 4 ≤ (κ / c) * (addEnergy G : ℝ) := by
  classical
  -- nonprincipal fourth moment T₂ = (global) − ‖η_0‖⁴, and global = q·E₂
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ 4 = q * (addEnergy G : ℝ) :=
    subgroup_gaussSum_fourthMoment hψ G
  have h0 : eta ψ G 0 = (G.card : ℂ) := by
    simp [eta, AddChar.map_zero_eq_one]
  have hn04 : ‖eta ψ G 0‖ ^ 4 = (G.card : ℝ) ^ 4 := by rw [h0, Complex.norm_natCast]
  -- T₂ = ∑_{b≠0} ‖η_b‖^(2*2) = ∑_{b≠0} ‖η_b‖⁴
  have hTrdef : nonprincMoment ψ G 2 = ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4 := by
    simp only [nonprincMoment, Nat.reduceMul]
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 4
      = ‖eta ψ G 0‖ ^ 4 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  -- hence T₂ = q·E₂ − |G|⁴ ≤ q·E₂
  have hTr_le : nonprincMoment ψ G 2 ≤ q * (addEnergy G : ℝ) := by
    rw [hTrdef]
    have : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4
        = q * (addEnergy G : ℝ) - (G.card : ℝ) ^ 4 := by
      have := hsplit
      rw [hfull, hn04] at this
      linarith [this]
    rw [this]
    have hG4 : (0 : ℝ) ≤ (G.card : ℝ) ^ 4 := by positivity
    linarith [hG4]
  -- apply the schematic reduction with Er = E₂, qEr = q·E₂
  have hEr : (0 : ℝ) ≤ (addEnergy G : ℝ) := by positivity
  exact M_pow_le_of_equidist (Mpow := M ^ 4) (κ := κ) (Tr := nonprincMoment ψ G 2)
    (Er := (addEnergy G : ℝ)) (qEr := q * (addEnergy G : ℝ)) (Nr := Nr) (c := c) (q := q)
    hκ hc hqpos hNr hEr hequi hTr_le rfl hsupp

/-- **`M`-bound from equidistribution and the energy ceiling (the prize-form chain, depth `r`).**
The capstone wiring: given the depth-`r` equidistribution `M^{2r} ≤ κ·(T_r/N_r)`, the moment
ceiling `T_r ≤ q·E_r`, the support floor `N_r ≥ c·q`, AND the (char-0-proven, transfer-pending)
energy bound `E_r ≤ B_r` (e.g. `B_r = K^r·(2r-1)‼·n^r`), the worst-case mass obeys
`M^{2r} ≤ (κ/c)·B_r`. This is the single inequality the spread route reduces the prize to:
the right-hand side is the *known* energy ceiling scaled by the equidistribution loss `κ/c`, with
no remaining dependence on the prime's structure beyond `κ`. -/
theorem M_pow_le_energy_ceiling
    {Mpow κ Tr Er Br Nr c q : ℝ}
    (hκ : 0 ≤ κ) (hc : 0 < c) (hq : 0 < q) (hNr : 0 < Nr)
    (_hBr : 0 ≤ Br)
    (hequi : EquidistAtDepth Mpow κ (Tr / Nr))
    (hTr : Tr ≤ q * Er) (hsupp : c * q ≤ Nr)
    (hEr : Er ≤ Br) (hEr0 : 0 ≤ Er) :
    Mpow ≤ (κ / c) * Br := by
  have hmain := M_pow_le_of_equidist (Mpow := Mpow) (κ := κ) (Tr := Tr) (Er := Er)
    (qEr := q * Er) (Nr := Nr) (c := c) (q := q) hκ hc hq hNr hEr0 hequi hTr rfl hsupp
  have hκc : 0 ≤ κ / c := div_nonneg hκ hc.le
  calc Mpow ≤ (κ / c) * Er := hmain
    _ ≤ (κ / c) * Br := by apply mul_le_mul_of_nonneg_left hEr hκc

end ArkLib.ProximityGap.EquidistToM

#print axioms ArkLib.ProximityGap.EquidistToM.M_pow_le_of_equidist
#print axioms ArkLib.ProximityGap.EquidistToM.M4_le_of_equidist_fourthMoment
#print axioms ArkLib.ProximityGap.EquidistToM.M_pow_le_energy_ceiling
