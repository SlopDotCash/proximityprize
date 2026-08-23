/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.REnergyMaxFiberBound
import ArkLib.Data.CodingTheory.ProximityGap.GeneralMomentPeriodBound

/-!
# The SHARP max-fiber energy bound: `E_r(G) ≤ R_r · |G|^r` (#444 / #407)

`REnergyMaxFiberBound` proves the TRIVIAL ceiling `E_r(G) ≤ |G|^{2r-1}`, which deflates the energy
using the *uniform* per-fiber bound `N_r(t) ≤ |G|^{r-1}` (`card_fiber_le`).  But the convolution
identity `E_r = Σ_t N_r(t)²` (with `N_r(t) = #{v ∈ G^r : Σv = t}`) factors more sharply through the
*actual* max-fiber count `R_r = max_t N_r(t)`:

  `E_r(G) = Σ_t N_r(t)² ≤ (max_t N_r(t)) · Σ_t N_r(t) = R_r · |G|^r`.

This file supplies that **sharp** ceiling in the usable consumer form: given ANY uniform per-fiber
cap `B` (i.e. `N_r(t) ≤ B` for every target `t`), the energy is at most `B · |G|^r`.

  **`rEnergy_le_maxFiber_mul`** : `(∀ t, N_r(t) ≤ B) → E_r(G) ≤ B · |G|^r`.

It STRICTLY tightens the trivial bound: substituting the uniform witness `B = |G|^{r-1}`
(`card_fiber_le`) recovers `rEnergy_le_card_pow` exactly (`rEnergy_le_card_pow_via_maxFiber`), but a
genuine `R_r < |G|^{r-1}` cap improves it.  Probe (`probe_depthr_energy_ceiling.py`, PROPER thin
`μ_n`, `p ≫ n³`, `p ≡ 1 (mod n)`): the sharp bound `R_r · |G|^r` holds at every tested `(n,r)`
(0 violations) and the gap `R_r / |G|^{r-1}` grows with `r` (e.g. `n=8, r=4`: `R_r = 168` vs
`|G|^{r-1} = 512`, the sharp bound is 3× tighter; `r=5`: `640` vs `4096`, 6.4× tighter).

Composed with `GeneralMomentPeriodBound.period_pow_le_moment` (`‖η_b‖^{2r} ≤ q·E_r(G)`), this yields
`‖η_b‖^{2r} ≤ q · R_r · |G|^r`, i.e. it isolates the entire open dependence of the worst period on the
single quantity `R_r` = the **depth-`r` representation count** — exactly the dyadic-Sidon-to-depth-`r`
input the `GeneralMomentPeriodBound` NOTE names as the slot a genuine `E_r(G) ≤ C_r·|G|^r` plugs into.
The `r = 2` case of that target is the proven `worst_period_sidon_le` (`R_2 ≤ 3|G|/|G|`... i.e.
`E_2 ≤ 3|G|²`); this file gives the general-`r` reduction `E_r ≤ R_r·|G|^r` that the `r=2` ceiling
instantiates.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential: this is a field-universal, unconditional convolution
inequality (`Σ aᵢ² ≤ max·Σ aᵢ`).  It does NOT supply a bound on `R_r` (the max depth-`r` fiber /
representation count) — THAT is the genuine open deep-moment quantity; in the prize regime the open
question is whether `R_r = O(C_r)` (a depth-`r` Sidon bound) at depth `r ≍ log m`, and the moment
route is known (issue §6) to be non-proving at structured primes.  What it adds: it replaces the
trivial uniform fiber bound `|G|^{r-1}` by the SHARP max-fiber factor `R_r`, isolating the open
content to exactly `R_r` and strictly tightening the in-tree `rEnergy_le_card_pow`.  CORE
(`M(μ_n) ≤ C√(n·log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.REnergyMaxFiberBound

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The sharp max-fiber energy bound (consumer form).**  If every fixed-sum fiber has at most `B`
tuples (`N_r(t) ≤ B` for all targets `t`), then the `r`-fold additive energy is at most `B · |G|^r`.

This is the sharp convolution deflation `E_r = Σ_t N_r(t)² ≤ (max N_r) · Σ_t N_r = R_r · |G|^r`,
in the form where `B` is any uniform fiber cap.  STRICTLY sharper than `rEnergy_le_card_pow`
(`B = |G|^{r-1}`): a genuine `R_r < |G|^{r-1}` improves the bound. -/
theorem rEnergy_le_maxFiber_mul (G : Finset F) (s : ℕ) {B : ℕ}
    (hB : ∀ t : F, ((Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter
        (fun v => ∑ i, v i = t)).card ≤ B) :
    rEnergy G (s + 1) ≤ B * G.card ^ (s + 1) := by
  classical
  unfold rEnergy
  -- Inner sum over `w` = card of the fiber `{w : Σw = Σv}`, capped by `B`.
  have hinner : ∀ v : Fin (s + 1) → F,
      (∑ w ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0)) ≤ B := by
    intro v
    have hcf : (∑ w ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
        (if ∑ i, v i = ∑ i, w i then 1 else 0))
        = ((Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter
            (fun w => ∑ i, w i = ∑ i, v i)).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases h : ∑ i, v i = ∑ i, w i
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    rw [hcf]
    exact hB (∑ i, v i)
  have hpi : (Fintype.piFinset (fun _ : Fin (s + 1) => G)).card = G.card ^ (s + 1) := by
    rw [Fintype.card_piFinset]; simp
  calc (∑ v ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
            ∑ w ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
              (if ∑ i, v i = ∑ i, w i then 1 else 0))
        ≤ ∑ _v ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G), B :=
        Finset.sum_le_sum (fun v _ => hinner v)
    _ = G.card ^ (s + 1) * B := by rw [Finset.sum_const, hpi, smul_eq_mul]
    _ = B * G.card ^ (s + 1) := by rw [Nat.mul_comm]

/-- **Trivial bound recovered.**  Instantiating the sharp consumer at the uniform witness
`B = |G|^s` (`card_fiber_le`) gives back `E_r(G) ≤ |G|^{2r-1}` (`rEnergy_le_card_pow`), confirming the
sharp bound is a strict generalization. -/
theorem rEnergy_le_card_pow_via_maxFiber (G : Finset F) (s : ℕ) :
    rEnergy G (s + 1) ≤ G.card ^ (2 * s + 1) := by
  have h := rEnergy_le_maxFiber_mul G s (B := G.card ^ s) (fun t => card_fiber_le G s t)
  calc rEnergy G (s + 1) ≤ G.card ^ s * G.card ^ (s + 1) := h
    _ = G.card ^ (2 * s + 1) := by rw [← pow_add]; ring_nf

/-- **The sharp period bound via the max-fiber cap.**  Combining the sharp energy ceiling with the
in-tree general-moment single-period bound `‖η_b‖^{2r} ≤ q·E_r(G)`: under a uniform depth-`r` fiber
cap `B`, every Gauss period satisfies `‖η_b‖^{2r} ≤ q · B · |G|^r`.  This isolates the worst-period's
open dependence to the single max-fiber quantity `B = R_r`. -/
theorem period_pow_le_maxFiber {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s : ℕ)
    {B : ℕ} (b : F)
    (hB : ∀ t : F, ((Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter
        (fun v => ∑ i, v i = t)).card ≤ B) :
    ‖eta ψ G b‖ ^ (2 * (s + 1)) ≤ (Fintype.card F : ℝ) * (B : ℝ) * (G.card : ℝ) ^ (s + 1) := by
  have h1 := _root_.ArkLib.ProximityGap.GeneralMomentPeriodBound.period_pow_le_moment hψ G (s + 1) b
  have h2 : (rEnergy G (s + 1) : ℝ) ≤ (B : ℝ) * (G.card : ℝ) ^ (s + 1) := by
    have := rEnergy_le_maxFiber_mul G s hB
    have hcast : ((B * G.card ^ (s + 1) : ℕ) : ℝ) = (B : ℝ) * (G.card : ℝ) ^ (s + 1) := by
      push_cast; ring
    calc (rEnergy G (s + 1) : ℝ) ≤ ((B * G.card ^ (s + 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (B : ℝ) * (G.card : ℝ) ^ (s + 1) := hcast
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ (2 * (s + 1))
      ≤ (Fintype.card F : ℝ) * (rEnergy G (s + 1) : ℝ) := h1
    _ ≤ (Fintype.card F : ℝ) * ((B : ℝ) * (G.card : ℝ) ^ (s + 1)) :=
        mul_le_mul_of_nonneg_left h2 hq
    _ = (Fintype.card F : ℝ) * (B : ℝ) * (G.card : ℝ) ^ (s + 1) := by ring

end ArkLib.ProximityGap.REnergyMaxFiberBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.REnergyMaxFiberBound.rEnergy_le_maxFiber_mul
#print axioms ArkLib.ProximityGap.REnergyMaxFiberBound.rEnergy_le_card_pow_via_maxFiber
#print axioms ArkLib.ProximityGap.REnergyMaxFiberBound.period_pow_le_maxFiber
