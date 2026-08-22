/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# Parseval floor: `M ≥ √n` UNCONDITIONALLY (axiom-clean).

`M := max_{b≠0} ‖η_b‖`, `η_b = ∑_{y∈G} ψ(b·y)`, `G` a finite subset of `F`, `|G| = n`,
`q = |F|`. This file proves, with NO Weil / NO Paley input, the *easy* (floor) direction of
BGK at the trivial scale: the worst-case nontrivial Gauss period is at least `√n` (up to the
exact `(q-n)/(q-1)` deficit), by the second moment + max ≥ average.

## Chain
1. `rEnergy G 1 = |G|` (the 1-fold additive energy is `#{(v,w)∈G² : v=w} = |G|`).
2. `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²` (`DCSubtractedMoment.sum_nonzero_moment` at `r=1`, with (1)).
3. There are `q−1` nonzero frequencies; max ≥ average:
   `∃ b≠0, (q·|G| − |G|²)/(q−1) ≤ ‖η_b‖²`, i.e. `M² ≥ |G|·(q−|G|)/(q−1)`.
4. Hence `M ≥ √(|G|·(q−|G|)/(q−1))`, which is `√(|G|·(1−o(1)))` since `(q−|G|)/(q−1) → 1`.

The cleaner consumer form `M² ≥ |G|·(q−|G|)/(q−1)` is the headline. We also give the existence
form (some explicit nonzero `b` attains the floor), so the result is constructive.

This is the lower-bound brick the `M ≥ √n` task asks for. The `log m` factor in the full BGK
floor `c√(n log m)` needs the resonance method (a separate, harder construction) and is NOT
claimed here.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ArkLib.ProximityGap.ParsevalFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The 1-fold additive energy is `|G|`.** `E_1(G) = #{(v,w) ∈ (Fin 1 → G)² : ∑v = ∑w}`. For
`r = 1` the condition `∑ᵢ vᵢ = ∑ᵢ wᵢ` is just `v 0 = w 0`, and the pairs `(v,w)` with `v = w`
number exactly `|G|`. -/
theorem rEnergy_one (G : Finset F) : rEnergy G 1 = G.card := by
  classical
  -- For `Fin 1`, `Fintype.piFinset (fun _ => G)` is in bijection with `G` via `v ↦ v 0`, and
  -- `∑ i, v i = v 0`. The double indicator sum counts pairs `(v,w)` with `v 0 = w 0`.
  unfold rEnergy
  -- The inner sum over `w` collapses: only `w = v` survives (i.e. `w 0 = v 0`).
  have hone : ∀ v : (Fin 1 → F), (∑ i, v i) = v 0 := by
    intro v; simp [Fin.sum_univ_one]
  -- Rewrite each `∑ i, v i` as `v 0` and `∑ i, w i` as `w 0`.
  have hstep : (∑ v ∈ Fintype.piFinset (fun _ : Fin 1 => G),
      ∑ w ∈ Fintype.piFinset (fun _ : Fin 1 => G), (if ∑ i, v i = ∑ i, w i then (1:ℕ) else 0))
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin 1 => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin 1 => G), (if v 0 = w 0 then (1:ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [hone v, hone w]
  rw [hstep]
  -- Now count: for each `v`, exactly the unique `w` with `w 0 = v 0` contributes 1.
  -- The map `w ↦ w 0` is a bijection `piFinset (fun _ : Fin 1 => G) → G`.
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin 1 => G),
      (∑ w ∈ Fintype.piFinset (fun _ : Fin 1 => G), (if v 0 = w 0 then (1:ℕ) else 0)) = 1 := by
    intro v hv
    -- exactly one `w` (namely `w = v`) has `w 0 = v 0` (since membership forces `w = fun _ => w 0`)
    rw [Finset.sum_eq_single v]
    · simp
    · intro w hw hwv
      rw [if_neg]
      intro hcontra
      apply hwv
      -- `w` and `v` are both functions `Fin 1 → F`; equal at `0` ⟹ equal
      funext i
      fin_cases i
      exact hcontra.symm
    · intro hvnot; exact absurd hv hvnot
  rw [Finset.sum_congr rfl hinner]
  simp [Fintype.card_piFinset, Finset.prod_const, Fintype.card_fin]

/-- **DC-subtracted second moment, evaluated:** `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`. -/
theorem sum_nonzero_sq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have h := sum_nonzero_moment hψ G 1
  rw [rEnergy_one] at h
  simpa using h

/-- **max ≥ average (existence form).** Some nonzero frequency attains the average energy:
`∃ b ≠ 0, |G|·(q−|G|)/(q−1) ≤ ‖η_b‖²`. Proof: the `q−1` nonzero terms sum to `q|G|−|G|²`, so
not all can be strictly below the average, by `Finset.exists_le_of_sum_le`. -/
theorem exists_nonzero_eta_sq_ge_avg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq1 : 1 < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  -- The erased universe has `q − 1` elements (as a real).
  have hcard : ((univ.erase (0 : F)).card : ℝ) = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ Fintype.card F)]
    simp [hq]
  -- `q − 1 > 0`.
  have hqpos : (0 : ℝ) < q - 1 := by
    have : (1 : ℝ) < q := by rw [hq]; exact_mod_cast hq1
    linarith
  -- The set is nonempty.
  have hne : (univ.erase (0 : F)).Nonempty := by
    rw [← Finset.card_pos]
    have : 0 < ((univ.erase (0 : F)).card : ℝ) := by rw [hcard]; linarith
    exact_mod_cast this
  -- abbreviate the average value.
  set A : ℝ := n * (q - n) / (q - 1) with hA
  -- the constant sum over the erased universe is `(q−1)·A = q·n − n²`.
  have hq1ne : q - 1 ≠ 0 := ne_of_gt hqpos
  have hconst : ∑ _b ∈ univ.erase (0 : F), A = q * n - n ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hA]
    -- `(q-1) * (n*(q-n)/(q-1)) = n*(q-n) = q*n - n²`
    rw [mul_div_assoc', mul_comm (q - 1), mul_div_assoc, div_self hq1ne, mul_one]
    ring
  -- compare: `∑ const A ≤ ∑ ‖η_b‖²` (in fact equal).
  have hsum := sum_nonzero_sq hψ G
  rw [← hq, ← hn] at hsum
  have hle : ∑ _b ∈ univ.erase (0 : F), A ≤ ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 := by
    rw [hconst, hsum]
  obtain ⟨b, hb, hbge⟩ := Finset.exists_le_of_sum_le hne hle
  refine ⟨b, ?_, ?_⟩
  · exact Finset.ne_of_mem_erase hb
  · rw [hA] at hbge; exact hbge

/-- **THE FLOOR (squared form): `M² ≥ |G|·(q−|G|)/(q−1)`.** Concretely, the worst-case nonzero
Gauss period squared is at least `|G|·(q−|G|)/(q−1)`, which equals `|G|·(1 − (|G|−1)/(q−1))`,
i.e. `|G|` up to an `O(|G|/q)` deficit. Stated as: some nonzero `b` realizes it (so any upper
bound on `max` must be `≥` this). -/
theorem worstCase_eta_sq_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq1 : 1 < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 :=
  exists_nonzero_eta_sq_ge_avg hψ G hq1

/-- **THE FLOOR (norm form): `M ≥ √(|G|·(q−|G|)/(q−1))`.** Taking square roots of the squared
floor: some nonzero frequency `b` has `‖η_b‖ ≥ √(|G|·(q−|G|)/(q−1))`. As `q → ∞` this is
`√|G|·(1−o(1))`, the unconditional `M ≳ √n` lower bound. -/
theorem worstCase_eta_ge_sqrt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq1 : 1 < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) / ((Fintype.card F : ℝ) - 1))
        ≤ ‖eta ψ G b‖ := by
  obtain ⟨b, hb, hbge⟩ := worstCase_eta_sq_ge hψ G hq1
  refine ⟨b, hb, ?_⟩
  rw [show ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hbge

/-- **Clean `M² ≥ |G|/2` in the prize regime `2|G| ≤ q`.** When the field is at least twice the
subgroup (always true in the prize regime `q ≈ n⁴`, `|G| = n`), the deficit factor
`(q−|G|)/(q−1) ≥ 1/2`, so the squared floor simplifies to `M² ≥ |G|/2`. A fully unconditional,
constant-free `M ≳ √|G|`. -/
theorem worstCase_eta_sq_ge_half {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hsize : 2 * G.card ≤ Fintype.card F) (hG : 0 < G.card) :
    ∃ b : F, b ≠ 0 ∧ (G.card : ℝ) / 2 ≤ ‖eta ψ G b‖ ^ 2 := by
  have hq1 : 1 < Fintype.card F := by
    have : 2 ≤ Fintype.card F := le_trans (by omega) hsize
    omega
  obtain ⟨b, hb, hbge⟩ := worstCase_eta_sq_ge hψ G hq1
  refine ⟨b, hb, le_trans ?_ hbge⟩
  -- show `|G|/2 ≤ |G|·(q−|G|)/(q−1)`, i.e. `(q−1) ≤ 2(q−|G|)` ⟺ `2|G| ≤ q + 1` (from `2|G| ≤ q`)
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hG
  have hqgt1 : (1 : ℝ) < q := by rw [hq]; exact_mod_cast hq1
  have hsize' : 2 * n ≤ q := by rw [hq, hn]; exact_mod_cast hsize
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hnpos, hsize', hqgt1]

/-- **Clean `M ≥ √(|G|/2)` in the prize regime `2|G| ≤ q`.** Square-root of the previous bound:
some nonzero frequency has `‖η_b‖ ≥ √(|G|/2)`. This is the headline unconditional `M ≳ √n` floor
(the worst-case nontrivial Gauss period is `Ω(√n)`), with NO Weil / NO Paley input. -/
theorem worstCase_eta_ge_sqrt_half {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hsize : 2 * G.card ≤ Fintype.card F) (hG : 0 < G.card) :
    ∃ b : F, b ≠ 0 ∧ Real.sqrt ((G.card : ℝ) / 2) ≤ ‖eta ψ G b‖ := by
  obtain ⟨b, hb, hbge⟩ := worstCase_eta_sq_ge_half hψ G hsize hG
  refine ⟨b, hb, ?_⟩
  rw [show ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hbge

end ArkLib.ProximityGap.ParsevalFloor

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ParsevalFloor.rEnergy_one
#print axioms ArkLib.ProximityGap.ParsevalFloor.sum_nonzero_sq
#print axioms ArkLib.ProximityGap.ParsevalFloor.exists_nonzero_eta_sq_ge_avg
#print axioms ArkLib.ProximityGap.ParsevalFloor.worstCase_eta_sq_ge
#print axioms ArkLib.ProximityGap.ParsevalFloor.worstCase_eta_ge_sqrt
#print axioms ArkLib.ProximityGap.ParsevalFloor.worstCase_eta_sq_ge_half
#print axioms ArkLib.ProximityGap.ParsevalFloor.worstCase_eta_ge_sqrt_half
