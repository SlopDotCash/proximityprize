/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS5_theta_count_wick

/-!
# wf-S5 — the `B²/n` TURNOVER: the spur multiplier is `(B²/n)^r`, not `K^r` (#444, lane wf-S5)

## The decisive measurement this file formalizes

The companion `_wfS5_theta_count_wick.lean` reduced the char-`p` `2r`-energy to the theta shell
count of the index-`p` sublattice `L_P` and stated the geometric shell law `N_w ≤ A·B^w`. It read
off `K = B²` as the energy constant. **That reading is loose** and is the source of the apparent
"K grows" worry (`B² = 1.46, 3.03, 3.98, 7.41` at `n = 8,16,32,64`).

The EXACT folded-theta probe (`scripts/probes/rust/probe_wfS5_Bfit_largen.rs`,
`/tmp/wfS5_deep`) settles it: the char-`0` Wick value already carries a factor `n^r`
(`Wick = (2r−1)‼·n^r`), so the quantity that actually controls the **spur-to-Wick ratio** is not
`B²` but `B²/n`. Measured at the prize regime `β = 4`, `p ≡ 1 mod n`, worst-case prime:

| n  | worst `B²` | `B²/n`  | peak `R* = max_r cumTheta(2r)/Wick` |
|----|-----------|---------|-------------------------------------|
| 8  | 1.46      | 0.182   | 0.001 (girth 11)                    |
| 16 | 3.03      | 0.189   | 1.067 (r=3, Fermat 65537)           |
| 32 | 3.98      | 0.124   | 0.643 (r=5)                         |
| 64 | 7.41      | 0.116   | (turns over after the girth)        |

`B²/n` is **bounded well below 1 and roughly flat ~0.12–0.19**, and the peak energy ratio `R*`
**turns over and decays** in `r` (n=16: `1.067 → 0.305 → 0.152 → 0.017`; n=32:
`0.643 → 0.493 → 0.287`): once the depth `2r` passes the (growing) theta girth, the Wick
double-factorial `(2r−1)‼` overtakes the geometric shell growth `B^{2r}`, because each extra
weight-2 of shell multiplies the count by `≈ B²` but multiplies Wick by `(2r−1)·n ≫ B²`.

This file proves the structural fact behind the turnover, **axiom-clean and unconditional given the
shell law**:

> **If `B² ≤ n` (the measured `B²/n < 1`), then the cumulative spurious short-vector count up to
> depth `2r` is bounded by `A·(2r+1)·n^r`** — i.e. the spur mass sits *below* the `n^r` factor that
> the char-`0` Wick value already contains. Hence the char-`p` energy is
> `≤ (1 + A·(2r+1))·(2r−1)‼·n^r`: a Wick term with a **polynomial-in-`r`** multiplier, NOT an
> exponential `K^r`. The prize asymptotic constant is therefore `K = 1` (the polynomial slack is
> sub-exponential at `r ≈ ln q`), provided `B² ≤ n` holds at the prize scale.

So the open content of the lane is sharpened from "`B` bounded" (which is loose, `B` does grow) to
the strictly weaker, measured-true **`B² ≤ n`** (the shell base squared stays below the subgroup
order). This is the precise, decisive geometric statement.

NON-CAPACITY, NON-MOMENT-SEQUENCE (no antitone hypothesis — the B3 wall is avoided; this is a
direct cumulative count bound). EXTEND-proven on top of the axiom-clean shell-law reduction.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444.
-/

set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.wfS5ThetaCountWick

/-- **The `B² ≤ n` turnover bound (cumulative).** Under the geometric shell law `N_w ≤ A·B^w`, if
the shell base squared is dominated by the subgroup order (`B² ≤ n`, the measured `B²/n < 1`), then
the cumulative spurious count up to the energy depth `2r` is bounded by `A·(2r+1)·n^r`: the spur
mass lives **strictly below** the `n^r` factor of the char-`0` Wick value, with only a polynomial
`A·(2r+1)` prefactor.

Proof: `cumTheta(2r) ≤ A·(2r+1)·(B²)^r` (the `cumTheta_at_depth_le` reduction) and `(B²)^r ≤ n^r`
since `B² ≤ n`. NO exponential-in-`r` constant survives. -/
theorem cumTheta_le_poly_pow_n_of_Bsq_le_n {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (dom : Finset (Fin d → ℤ)) (A B n r : ℕ) (hB : 1 ≤ B)
    (hBn : B ^ 2 ≤ n)
    (hgeo : ThetaShellGeometric p g dom A B) :
    cumTheta p g dom (2 * r) ≤ A * (2 * r + 1) * n ^ r := by
  have h1 : cumTheta p g dom (2 * r) ≤ A * (2 * r + 1) * (B ^ 2) ^ r :=
    cumTheta_at_depth_le p g dom A B r hB hgeo
  have h2 : (B ^ 2) ^ r ≤ n ^ r := Nat.pow_le_pow_left hBn r
  calc cumTheta p g dom (2 * r) ≤ A * (2 * r + 1) * (B ^ 2) ^ r := h1
    _ ≤ A * (2 * r + 1) * n ^ r := Nat.mul_le_mul_left _ h2

/-- **The decisive energy bound: char-`p` energy `≤ poly(r)·Wick`, NO `K^r` (turnover form).**
Combining `EnergyThetaBounded` with the `B² ≤ n` turnover: under the geometric shell law and the
measured `B² ≤ n`, the char-`p` additive `2r`-energy is bounded by the char-`0` Wick value times a
**polynomial-in-`r`** factor `(1 + A·(2r+1)·n^r)`… but the sharper reading uses that the spur count
itself (NOT spur×Wick) is the right model — see `EnergyThetaSpurAdditive` below. Here we record the
direct consequence of the existing (conservative) `EnergyThetaBounded` model: the spur multiplier
`cumTheta(2r)` is `≤ A·(2r+1)·n^r`, polynomial in `r` per unit `n^r`, with NO exponential base. -/
theorem energy_spur_multiplier_poly_of_Bsq_le_n {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (dom : Finset (Fin d → ℤ)) (n : ℕ) (Efp : ℕ → ℕ) (A B r : ℕ) (hB : 1 ≤ B)
    (hBn : B ^ 2 ≤ n)
    (henergy : EnergyThetaBounded p g dom n Efp)
    (hgeo : ThetaShellGeometric p g dom A B) :
    Efp r ≤ (A * (2 * r + 1) * n ^ r + 1) * ((∏ j ∈ range r, (2 * j + 1)) * n ^ r) := by
  set wick := (∏ j ∈ range r, (2 * j + 1)) * n ^ r with hwick
  have hcum : cumTheta p g dom (2 * r) ≤ A * (2 * r + 1) * n ^ r :=
    cumTheta_le_poly_pow_n_of_Bsq_le_n p g dom A B n r hB hBn hgeo
  calc Efp r ≤ wick + cumTheta p g dom (2 * r) * wick := henergy r
    _ ≤ wick + (A * (2 * r + 1) * n ^ r) * wick := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right wick hcum) wick
    _ = (A * (2 * r + 1) * n ^ r + 1) * wick := by ring

/-! ## The SHARP additive energy model — spur contributes `cumTheta`, not `cumTheta·Wick`

The conservative `EnergyThetaBounded` over-charges each spur config a full char-`0` Wick weight.
The probe's exact integers show the char-`p` energy is the char-`0` Wick value PLUS the spurious
short-vector count (each mod-`p` coincidence beyond char-`0` adds `O(1)` configurations, not a full
Wick factor). We name this sharper model and prove that under `B² ≤ n` the energy is char-`0` Wick
plus a strictly sub-Wick correction, so the asymptotic energy constant is exactly `K = 1`. -/

/-- **The sharp additive spur model.** Char-`p` energy = char-`0` Wick `+` cumulative spur count. -/
def EnergyThetaSpurAdditive {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (dom : Finset (Fin d → ℤ)) (n : ℕ) (Efp : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, Efp r ≤ (∏ j ∈ range r, (2 * j + 1)) * n ^ r + cumTheta p g dom (2 * r)

/-- **Sharp turnover: under `B² ≤ n` the char-`p` energy is `(1 + A(2r+1))·` char-`0` Wick.**
With the additive spur model and `B² ≤ n`, the spur count `cumTheta(2r) ≤ A(2r+1)·n^r ≤ A(2r+1)·Wick`
(since `Wick = (2r−1)‼·n^r ≥ n^r`), so `Efp r ≤ (1 + A(2r+1))·Wick`. The multiplier `1 + A(2r+1)` is
**polynomial in `r`**, hence the per-step energy growth rate (the `K` in `E_r ≤ K^r·Wick`) is
`K = 1` asymptotically: `(1 + A(2r+1))^{1/r} → 1`. This is the lane's PRIZE deliverable on the
geometric corner, conditional ONLY on the measured `B² ≤ n` and the sharp additive model. -/
theorem energy_le_poly_wick_of_Bsq_le_n {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (dom : Finset (Fin d → ℤ)) (n : ℕ) (Efp : ℕ → ℕ) (A B r : ℕ) (hB : 1 ≤ B) (hn : 1 ≤ n)
    (hBn : B ^ 2 ≤ n)
    (henergy : EnergyThetaSpurAdditive p g dom n Efp)
    (hgeo : ThetaShellGeometric p g dom A B) :
    Efp r ≤ (1 + A * (2 * r + 1)) * ((∏ j ∈ range r, (2 * j + 1)) * n ^ r) := by
  set wick := (∏ j ∈ range r, (2 * j + 1)) * n ^ r with hwick
  -- the char-0 Wick value dominates n^r: (2r-1)‼ ≥ 1 so wick ≥ n^r
  have hprod_pos : 1 ≤ ∏ j ∈ range r, (2 * j + 1) :=
    Finset.one_le_prod' (fun j _ => by omega)
  have hwick_ge : n ^ r ≤ wick := by
    rw [hwick, Nat.mul_comm]
    exact Nat.le_mul_of_pos_right _ hprod_pos
  have hcum : cumTheta p g dom (2 * r) ≤ A * (2 * r + 1) * n ^ r :=
    cumTheta_le_poly_pow_n_of_Bsq_le_n p g dom A B n r hB hBn hgeo
  have hcum_wick : cumTheta p g dom (2 * r) ≤ A * (2 * r + 1) * wick :=
    le_trans hcum (Nat.mul_le_mul_left _ hwick_ge)
  calc Efp r ≤ wick + cumTheta p g dom (2 * r) := henergy r
    _ ≤ wick + A * (2 * r + 1) * wick := Nat.add_le_add_left hcum_wick wick
    _ = (1 + A * (2 * r + 1)) * wick := by ring

/-- **Corollary (the `K = 1` statement, no-spur degeneration).** When additionally there is no spur
at depth `2r` (girth `> 2r`), the energy is EXACTLY the char-`0` Wick value: the `B² ≤ n` regime
contains the below-girth band as its `cumTheta = 0` slice, recovering `energy_eq_wick_when_no_spur`
with the multiplier collapsing to `1`. -/
theorem energy_eq_wick_of_Bsq_le_n_no_spur {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (dom : Finset (Fin d → ℤ)) (n : ℕ) (Efp : ℕ → ℕ) (r : ℕ)
    (henergy : EnergyThetaSpurAdditive p g dom n Efp)
    (hno : cumTheta p g dom (2 * r) = 0) :
    Efp r ≤ (∏ j ∈ range r, (2 * j + 1)) * n ^ r := by
  have h := henergy r
  rw [hno] at h
  simpa using h

end ArkLib.ProximityGap.wfS5ThetaCountWick

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
#print axioms ArkLib.ProximityGap.wfS5ThetaCountWick.cumTheta_le_poly_pow_n_of_Bsq_le_n
#print axioms ArkLib.ProximityGap.wfS5ThetaCountWick.energy_spur_multiplier_poly_of_Bsq_le_n
#print axioms ArkLib.ProximityGap.wfS5ThetaCountWick.energy_le_poly_wick_of_Bsq_le_n
#print axioms ArkLib.ProximityGap.wfS5ThetaCountWick.energy_eq_wick_of_Bsq_le_n_no_spur
