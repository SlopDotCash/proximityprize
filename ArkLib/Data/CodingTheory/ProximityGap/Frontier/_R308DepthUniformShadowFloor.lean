/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R306Depth3CharZeroFloor

/-!
# LANE B2 (#466 round 308): THE DEPTH-UNIFORM SHADOW DICHOTOMY — r306/r307 at every
  moment depth `r`

The prize wall lives at depth `r ≈ ln q`, not depth 3.  This brick generalizes the r306
shadow factorization and floor, and the r307 injectivity equality, from triples to
`r`-tuples, uniformly in `r`:

* **`gsumR_eq_evalVec_tupleVec`** :  the field-level `r`-sum `Σ_i g^{t i}` factors through
  the exact integer shadow `tupleVec t ∈ ℤ^m` (coordinates bounded by `r`);
* **`repRF_eq_sum_NR`** :  the depth-`r` fiber count is the pushforward of the char-0
  `r`-histogram `NR`;
* **`shadowR_energy_le_depthR_energy`** :  the **depth-`r` char-0 floor**
  `Σ_v NR(v)² ≤ Σ_{c : F} rep_r(c)²`, for every field, every `g` with `g^m = −1`,
  every `r`;
* **`depthR_energy_eq_of_shadow_injective`** :  shadow injectivity at depth `r` ⟹ the
  depth-`r` energy equals the char-0 shadow energy EXACTLY.

This is the sharpest formal framing of the open core so far: for every depth
simultaneously, `E_r = (char-0 shadow energy at depth r) + (collision mass ≥ 0)`, and the
prize wall is EXACTLY the statement that the collision mass stays sub-Wick to `r ≈ ln q`
at `n = 2³⁰` — i.e. that the number-theoretic collisions of bounded-height `ℤ[ζ]` vectors
mod the prize prime stay controlled.  The char-0 part is combinatorics (Wick-bounded by the
#464 char-0 chain); ALL the arithmetic difficulty is isolated in the collision term.
Issue #466, round 308, LANE B2.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor

variable {F : Type*} [Field F]

/-- The exact char-0 shadow of an `r`-tuple of root indices. -/
def tupleVec (n m r : ℕ) (t : Fin r → Fin n) : Fin m → ℤ :=
  fun j => ∑ i : Fin r, vecOf n m (t i) j

/-- The field-level `r`-sum of a tuple of root indices. -/
def gsumR (g : F) (n r : ℕ) (t : Fin r → Fin n) : F :=
  ∑ i : Fin r, g ^ ((t i : ℕ))

/-- **The depth-`r` factorization**: the field-level `r`-sum equals the evaluation of the
shadow. -/
theorem gsumR_eq_evalVec_tupleVec (g : F) (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) (t : Fin r → Fin n) :
    gsumR g n r t = evalVec g m (tupleVec n m r t) := by
  unfold gsumR tupleVec evalVec
  -- swap the two finite sums and use the single-root factorization per coordinate
  have hswap : ∑ j : Fin m, ((∑ i : Fin r, vecOf n m (t i) j : ℤ)) • g ^ (j : ℕ)
      = ∑ i : Fin r, ∑ j : Fin m, (vecOf n m (t i) j : ℤ) • g ^ (j : ℕ) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_smul]
  rw [hswap]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (evalVec_vecOf g n m hm hn hg (t i)).symm

/-- The depth-`r` shadow key set. -/
def keysR (n m r : ℕ) : Finset (Fin m → ℤ) :=
  (Finset.univ : Finset (Fin r → Fin n)).image (tupleVec n m r)

/-- The char-0 depth-`r` histogram. -/
def NR (n m r : ℕ) (v : Fin m → ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin n)).filter (fun t => tupleVec n m r t = v)).card

section Floor

variable [Fintype F] [DecidableEq F]

/-- The field-level depth-`r` representation count at `c`. -/
def repRF (g : F) (n r : ℕ) (c : F) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin n)).filter (fun t => gsumR g n r t = c)).card

/-- The depth-`r` fiber decomposes as the pushforward of `NR`. -/
theorem repRF_eq_sum_NR (g : F) (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) (c : F) :
    repRF g n r c = ∑ v ∈ (keysR n m r).filter (fun v => evalVec g m v = c), NR n m r v := by
  classical
  unfold repRF
  rw [Finset.card_eq_sum_card_fiberwise
    (f := tupleVec n m r) (t := (keysR n m r).filter (fun v => evalVec g m v = c))
    (fun t ht => ?_)]
  · refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [Finset.mem_filter] at hv
    unfold NR
    congr 1
    rw [Finset.filter_filter]
    refine Finset.filter_congr (fun t _ => ?_)
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨by rw [gsumR_eq_evalVec_tupleVec g n m r hm hn hg, h, hv.2], h⟩
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ t), ?_⟩
    rw [← gsumR_eq_evalVec_tupleVec g n m r hm hn hg, ht]

/-- **THE DEPTH-`r` CHAR-0 FLOOR**: at every moment depth, over every field, the depth-`r`
energy dominates the char-0 shadow energy. -/
theorem shadowR_energy_le_depthR_energy (g : F) (n m r : ℕ) (hm : 0 < m)
    (hn : n = 2 * m) (hg : g ^ m = -1) :
    ∑ v ∈ keysR n m r, (NR n m r v) ^ 2 ≤ ∑ c : F, (repRF g n r c) ^ 2 := by
  classical
  have hpart : ∑ v ∈ keysR n m r, (NR n m r v) ^ 2
      = ∑ c : F, ∑ v ∈ (keysR n m r).filter (fun v => evalVec g m v = c),
          (NR n m r v) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => evalVec g m v)
      (f := fun v => (NR n m r v) ^ 2)
      (fun v _ => Finset.mem_univ (evalVec g m v))]
  rw [hpart]
  refine Finset.sum_le_sum (fun c _ => ?_)
  rw [repRF_eq_sum_NR g n m r hm hn hg c]
  exact sum_sq_le_sq_sum _ _

/-- **Depth-`r` shadow injectivity ⟹ exact char-0 energy** — the equality half, uniform
in `r`: on shadow-injective instances the depth-`r` collision mass vanishes. -/
theorem depthR_energy_eq_of_shadow_injective (g : F) (n m r : ℕ) (hm : 0 < m)
    (hn : n = 2 * m) (hg : g ^ m = -1)
    (hinj : ∀ v ∈ keysR n m r, ∀ w ∈ keysR n m r, evalVec g m v = evalVec g m w → v = w) :
    ∑ c : F, (repRF g n r c) ^ 2 = ∑ v ∈ keysR n m r, (NR n m r v) ^ 2 := by
  classical
  have hfib : ∀ c : F, ((keysR n m r).filter (fun v => evalVec g m v = c)).card ≤ 1 := by
    intro c
    rw [Finset.card_le_one]
    intro v hv w hw
    rw [Finset.mem_filter] at hv hw
    exact hinj v hv.1 w hw.1 (by rw [hv.2, hw.2])
  have hstep : ∀ c : F, (repRF g n r c) ^ 2
      = ∑ v ∈ (keysR n m r).filter (fun v => evalVec g m v = c), (NR n m r v) ^ 2 := by
    intro c
    rw [repRF_eq_sum_NR g n m r hm hn hg c]
    rcases ((keysR n m r).filter (fun v => evalVec g m v = c)).eq_empty_or_nonempty
      with h | h
    · simp [h]
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (le_antisymm (hfib c)
        (Finset.card_pos.mpr h))
      simp [hv]
  rw [Finset.sum_congr rfl (fun c _ => hstep c)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => evalVec g m v)
    (f := fun v => (NR n m r v) ^ 2)
    (fun v _ => Finset.mem_univ (evalVec g m v))]

end Floor

end ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor.gsumR_eq_evalVec_tupleVec
#print axioms ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor.repRF_eq_sum_NR
#print axioms
  ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor.shadowR_energy_le_depthR_energy
#print axioms
  ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor.depthR_energy_eq_of_shadow_injective
