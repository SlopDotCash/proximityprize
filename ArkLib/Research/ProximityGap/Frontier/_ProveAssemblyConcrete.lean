/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# The CONCRETE assembly: the prize floor for the actual periods from ONE energy inequality (#444)

`_ProveAssembly` chained the prize floor abstractly. This file wires it to the **concrete in-tree period**
`eta ψ G b = Σ_{y∈G} ψ(b·y)` (the Gauss period) via the **proven** moment identity
`DCSubtractedMoment.sum_nonzero_moment`:
```
Σ_{b≠0} ‖eta ψ G b‖^{2r} = q·E_r(G) − |G|^{2r},   q = |F|,  E_r = rEnergy G r.
```

The result (`period_le_prizeFloor`): for EVERY nonzero frequency `b₀`, the period obeys the prize floor
```
‖eta ψ G b₀‖ ≤ √e · √(2r·|G|)   (= the prize floor √(2e·|G|·log q) at r ≈ log q)
```
**assuming exactly ONE inequality**: the char-`p` energy bound at the saddle depth,
```
hEnergy :  (E_r(G) : ℝ) ≤ (2r·|G|)^r .
```
EVERYTHING ELSE IS PROVEN HERE, machine-checked:
* the worst term `≤` the full nonzero moment (`Finset.single_le_sum`);
* the moment identity `= q·E_r − |G|^{2r}` (in-tree `sum_nonzero_moment`);
* dropping the nonneg DC term `−|G|^{2r}`;
* the saddle `M^{2r} ≤ q·(2r|G|)^r ∧ q ≤ exp r ⟹ M ≤ √e·√(2r|G|)` (inlined, axiom-clean).

## Honest status — this is the FRONTIER, not a closure

`hEnergy` at the saddle depth `r ≈ log q` is **the open core** — equivalently `E_r(μ_n;F_p) ≤ (2r−1)‼·n^r`
at `r ≈ log p` (the `(2r−1)‼ ≤ (2r)^r` envelope is folded into `(2r·|G|)^r`). This single inequality is
**BGK at the prize exponent**: proven for `n < 2log q/loglog q ≈ 40` (norm bound), OPEN for the prize
`n = 2^30` — whether short `≤2r`-term `±1` relations of `2^μ`-th roots vanish mod the prize prime. The
literature sweep (`docs/kb/deltastar-444-literature-sweep-2026-06-18.md`) found **no** route to it; SOTA is
exponent `1−o(1)`. So this file does the MAXIMAL honest thing: it proves the prize floor for the actual
periods **modulo the single genuinely-open energy inequality**, fully machine-checked otherwise. It does NOT
prove `hEnergy`, and `hEnergy` is NOT dischargeable with present mathematics. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ProveAssemblyConcrete

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

/-! ## The saddle (self-contained, axiom-clean copies of the in-tree lemmas) -/

/-- `M^{2r} ≤ p·B^r` (`B ≥ 0`) ⟹ `M ≤ p^{1/2r}·√B`. -/
theorem moment_saddle_value {M p B : ℝ} {r : ℕ} (hr : 0 < r)
    (hM : 0 ≤ M) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hbound : M ^ (2 * r) ≤ p * B ^ r) :
    M ≤ p ^ (((2 * r : ℕ) : ℝ)⁻¹) * Real.sqrt B := by
  have hr2 : (2 * r : ℕ) ≠ 0 := by positivity
  have hMpow : (0 : ℝ) ≤ M ^ (2 * r) := by positivity
  have step1 : M ≤ (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) := by
    calc M = (M ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hM hr2).symm
      _ ≤ (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) := Real.rpow_le_rpow hMpow hbound (by positivity)
  have hsqrt : (B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) = Real.sqrt B := by
    rw [← Real.rpow_natCast B r, ← Real.rpow_mul hB, Real.sqrt_eq_rpow]
    congr 1
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ (by positivity)]
    ring
  have step2 : (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) = p ^ (((2 * r : ℕ) : ℝ)⁻¹) * Real.sqrt B := by
    rw [Real.mul_rpow hp (by positivity), hsqrt]
  rw [step2] at step1; exact step1

/-- `M^{2r} ≤ q·(2r·n)^r` with `q ≤ exp r` ⟹ `M ≤ √e·√(2r·n)` (the prize floor at `r ≈ log q`). -/
theorem saddle_floor {M q n : ℝ} {r : ℕ} (hr : 0 < r) (hM : 0 ≤ M) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hWick : M ^ (2 * r) ≤ q * (2 * r * n) ^ r) (hdepth : q ≤ Real.exp r) :
    M ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * n) := by
  have hsaddle := moment_saddle_value hr hM hq (by positivity : (0:ℝ) ≤ 2 * r * n) hWick
  refine le_trans hsaddle ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hrinv : (0 : ℝ) ≤ (((2 * r : ℕ) : ℝ))⁻¹ := by positivity
  calc q ^ (((2 * r : ℕ) : ℝ))⁻¹
      ≤ (Real.exp (r : ℝ)) ^ (((2 * r : ℕ) : ℝ))⁻¹ := Real.rpow_le_rpow hq hdepth hrinv
    _ = Real.sqrt (Real.exp 1) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.sqrt_eq_rpow,
            Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp]
        congr 1
        have hrne : (r : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp

/-! ## The concrete prize floor for the actual Gauss period -/

/-- **★ The prize floor for the actual period, from one energy inequality.** For the concrete Gauss period
`eta ψ G b = Σ_{y∈G} ψ(b·y)` (ψ primitive), EVERY nonzero frequency `b₀` obeys the prize floor
`‖eta ψ G b₀‖ ≤ √e·√(2r·|G|)` — assuming ONLY the char-`p` energy bound `E_r(G) ≤ (2r·|G|)^r` at the saddle
depth `r` (with `q = |F| ≤ exp r`, i.e. `r ≈ log q`). The worst-term bound, the proven moment identity
`sum_nonzero_moment`, the DC drop, and the saddle are all discharged here; `hEnergy` is the single open
input (= BGK at the prize exponent). -/
theorem period_le_prizeFloor {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ} (hr : 0 < r)
    {b₀ : F} (hb₀ : b₀ ≠ 0)
    (hEnergy : (rEnergy G r : ℝ) ≤ (2 * r * (G.card : ℝ)) ^ r)
    (hdepth : (Fintype.card F : ℝ) ≤ Real.exp r) :
    ‖eta ψ G b₀‖ ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * (G.card : ℝ)) := by
  have hb₀mem : b₀ ∈ univ.erase (0 : F) := mem_erase.mpr ⟨hb₀, mem_univ _⟩
  -- worst term ≤ full nonzero moment
  have hsingle : ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) (fun b _ => by positivity) hb₀mem
  -- substitute the proven moment identity
  rw [sum_nonzero_moment hψ G r] at hsingle
  -- drop the DC term and apply the energy bound
  have hWick : ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (2 * r * (G.card : ℝ)) ^ r := by
    have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
    have hE : (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
        ≤ (Fintype.card F : ℝ) * (2 * r * (G.card : ℝ)) ^ r := mul_le_mul_of_nonneg_left hEnergy hq
    have hdc : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
    linarith [hsingle, hE, hdc]
  exact saddle_floor hr (norm_nonneg _) (by positivity) (by positivity) hWick hdepth

end ArkLib.ProximityGap.Frontier.ProveAssemblyConcrete

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.ProveAssemblyConcrete.saddle_floor
#print axioms ArkLib.ProximityGap.Frontier.ProveAssemblyConcrete.period_le_prizeFloor
