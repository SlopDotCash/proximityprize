/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.Tactic.Positivity

set_option linter.style.longLine false

/-!
# General-`r` single-period moment bound and its trivial `r`-energy ceiling (#444)

This file extends the **proven** `r = 2` sub-`√q` worst-period bound
(`WorstPeriodSidon.worst_period_sidon_le`, which uses `∑_b ‖η_b‖⁴ = q·E(G)` plus a Sidon energy
ceiling) to **every** moment `r`, using the in-tree general moment identity
`subgroup_gaussSum_moment : ∑_b ‖η_b‖^{2r} = q · E_r(G)`.

Two unconditional, field-general bricks:

* `period_pow_le_moment` — the **single-period general-`r` bound**
  `‖η_b‖^{2r} ≤ q · E_r(G)`  for every `b` and every `r`.
  (A single term of a nonneg sum is `≤` the total, and the total is `q·E_r(G)`.)
  This is the universal *consumer* into which any `r`-energy ceiling plugs: an `E_r(G) ≤ B_r`
  bound immediately yields `‖η_b‖ ≤ (q·B_r)^{1/2r}`, whose `q`-exponent `1/2r → 0`.

* `rEnergy_le_card_pow` — the **trivial unconditional `r`-energy ceiling**
  `E_r(G) ≤ |G|^{2r-1}`  for `r ≥ 1`.
  (The solution set `{(v,w) : ∑v = ∑w}` injects into `G^r × G^{r-1}` by dropping the last `w`-coord,
  which is recovered as `∑v − ∑(first r-1 of w)`.)

Composed, `period_pow_le_card_pow` gives the explicit (Sidon-free) general-`r` period bound
`‖η_b‖^{2r} ≤ q · |G|^{2r-1}`, i.e. `‖η_b‖ ≤ q^{1/2r}·|G|·|G|^{-1/2r}`.

Probe-validated (`scripts/probes/probe_renergy_ceiling.py`, `probe_period_rbound.py`,
`probe_fiber_ceiling.py`): on PROPER `μ_n` at primes `p ≫ n³`, `p ≡ 1 (mod n)`, the energy bound
`(q·E_r)^{1/2r}` is monotone DECREASING in `r` toward the true worst period and far below `√q`
(n=8,p=8009: r=1→253, r=2→34, r=5→12 vs true ≈7.7, √q≈89), the ceiling `E_r ≤ |G|^{2r-1}` holds
(with slack for `r ≥ 3`), and the fiber count `#{w : ∑w = t} ≤ |G|^{r-1}` holds.

NOTE (scope, rule 3/6 honesty): these bricks are **field-universal and unconditional**, hence NOT
thinness-essential and NOT a CORE closure. The trivial ceiling `|G|^{2r-1}` ignores Sidon
cancellation, so the *explicit* bound it yields is weak (it does NOT beat `√q` on its own at large `G`).
The value added is the general-`r` *consumer* (`period_pow_le_moment`): it is the exact in-tree slot a
future genuine `E_r(G) ≤ C_r·|G|^r` (dyadic Sidon-to-depth-`r`) input plugs into to drive the
`q`-exponent to `0`. CORE (`M(μ_n) ≤ C√(n·log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.GeneralMomentPeriodBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The single-period general-`r` moment bound.** A single Gauss period to the `2r`-th power is at
most the full `2r`-th moment `q·E_r(G)`. The `r = 2` case is the inequality used by
`worst_period_sidon_le`; this is its general-`r` form. -/
theorem period_pow_le_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := by
  classical
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' => ‖eta ψ G b'‖ ^ (2 * r))
      (fun _ _ => by positivity) (Finset.mem_univ b)
  rwa [subgroup_gaussSum_moment hψ G r] at hterm

/-- The `r`-energy solution finset `{(v,w) ∈ G^r × G^r : ∑ v = ∑ w}`, as a `Finset` of pairs. -/
noncomputable def rEnergySol (G : Finset F) (r : ℕ) : Finset ((Fin r → F) × (Fin r → F)) :=
  ((Fintype.piFinset (fun _ : Fin r => G)) ×ˢ (Fintype.piFinset (fun _ : Fin r => G))).filter
    (fun vw => ∑ i, vw.1 i = ∑ i, vw.2 i)

/-- Membership in `rEnergySol`. -/
theorem mem_rEnergySol {G : Finset F} {r : ℕ} {vw : (Fin r → F) × (Fin r → F)} :
    vw ∈ rEnergySol G r ↔
      ((∀ i, vw.1 i ∈ G) ∧ (∀ i, vw.2 i ∈ G)) ∧ ∑ i, vw.1 i = ∑ i, vw.2 i := by
  unfold rEnergySol
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]

/-- `rEnergy` equals the cardinality of its solution finset. -/
theorem rEnergy_eq_card (G : Finset F) (r : ℕ) :
    (rEnergy G r : ℕ) = (rEnergySol G r).card := by
  classical
  unfold rEnergy rEnergySol
  rw [Finset.card_filter, Finset.sum_product]

/-- **Trivial unconditional `r`-energy ceiling: `E_r(G) ≤ |G|^{2r-1}` for `r ≥ 1`.**
The solution set injects into `G^r × G^{r-1}` by dropping the last `w`-coordinate, which is recovered
from `∑v = ∑w`. -/
theorem rEnergy_le_card_pow (G : Finset F) {r : ℕ} (hr : 1 ≤ r) :
    rEnergy G r ≤ G.card ^ (2 * r - 1) := by
  classical
  rw [rEnergy_eq_card]
  -- target codomain: G^r × G^{r-1}
  -- inject (v, w) ↦ (v, w ∘ Fin.castSucc)  using r = (r-1)+1
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  -- The injection target finset.
  let T : Finset ((Fin (m+1) → F) × (Fin m → F)) :=
    (Fintype.piFinset (fun _ : Fin (m+1) => G)) ×ˢ (Fintype.piFinset (fun _ : Fin m => G))
  -- The injection.
  have hcard : (rEnergySol G (m+1)).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn
      (fun vw => (vw.1, fun i : Fin m => vw.2 i.castSucc)) ?_ ?_
    · -- maps into T
      intro vw hvw
      simp only [Finset.mem_coe, mem_rEnergySol] at hvw
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Fintype.mem_piFinset.mpr (fun i => hvw.1.1 i)
      · exact Fintype.mem_piFinset.mpr (fun i => hvw.1.2 _)
    · -- injective on rEnergySol
      intro a ha b hb hab
      simp only [Finset.mem_coe, mem_rEnergySol] at ha hb
      simp only [Prod.mk.injEq] at hab
      obtain ⟨hv, hw⟩ := hab
      obtain ⟨_, hsumA⟩ := ha
      obtain ⟨_, hsumB⟩ := hb
      -- a.1 = b.1, and a.2, b.2 agree on castSucc; last coord from ∑-constraint
      have hlast : a.2 (Fin.last m) = b.2 (Fin.last m) := by
        have hfA : ∑ i, a.2 i = (∑ i : Fin m, a.2 i.castSucc) + a.2 (Fin.last m) :=
          Fin.sum_univ_castSucc _
        have hfB : ∑ i, b.2 i = (∑ i : Fin m, b.2 i.castSucc) + b.2 (Fin.last m) :=
          Fin.sum_univ_castSucc _
        have hcs : (∑ i : Fin m, a.2 i.castSucc) = ∑ i : Fin m, b.2 i.castSucc := by
          apply Finset.sum_congr rfl; intro i _; rw [congrFun hw i]
        have e1 : ∑ i, a.1 i = ∑ i, b.1 i := by rw [hv]
        rw [hsumA, hsumB, hfA, hfB, hcs] at e1
        exact add_left_cancel e1
      -- assemble a = b
      ext1
      · exact hv
      · -- a.2 = b.2
        funext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact congrFun hw j
        · exact hlast
  have hTcard : T.card = G.card ^ (m+1) * G.card ^ m := by
    show ((Fintype.piFinset (fun _ : Fin (m+1) => G)) ×ˢ
      (Fintype.piFinset (fun _ : Fin m => G))).card = _
    rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
    simp [Finset.prod_const, Finset.card_univ]
  have hexp : G.card ^ (m+1) * G.card ^ m = G.card ^ (2 * (m+1) - 1) := by
    rw [← pow_add]; congr 1; omega
  calc (rEnergySol G (m+1)).card ≤ T.card := hcard
    _ = G.card ^ (m+1) * G.card ^ m := hTcard
    _ = G.card ^ (2 * (m+1) - 1) := hexp

/-- **Explicit (Sidon-free) general-`r` single-period bound: `‖η_b‖^{2r} ≤ q·|G|^{2r-1}`.**
Compose `period_pow_le_moment` with the trivial ceiling. -/
theorem period_pow_le_card_pow {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ}
    (hr : 1 ≤ r) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1) := by
  have h1 := period_pow_le_moment hψ G r b
  have h2 : (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ (2 * r - 1) := by
    have := rEnergy_le_card_pow G hr
    exact_mod_cast this
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := h1
    _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1) :=
        mul_le_mul_of_nonneg_left h2 hq

end ArkLib.ProximityGap.GeneralMomentPeriodBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.GeneralMomentPeriodBound.period_pow_le_moment
#print axioms ArkLib.ProximityGap.GeneralMomentPeriodBound.rEnergy_le_card_pow
#print axioms ArkLib.ProximityGap.GeneralMomentPeriodBound.period_pow_le_card_pow
