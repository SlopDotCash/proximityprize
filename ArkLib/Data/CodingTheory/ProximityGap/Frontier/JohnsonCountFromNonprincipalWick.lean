/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumLadderMarkov
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.NonprincipalWickIsDCWick

/-!
# The Johnson-scale frequency COUNT bound, re-grounded on the SATISFIABLE nonprincipal Wick input (#444)

`SubgroupGaussSumLadderMarkovWick.card_johnson_scale_frequencies_mul_le_wick` proves the
anti-concentration count bound

> `#{b : ‖η_b‖² ≥ q} · q^{r-1} ≤ (2r−1)‼·n^r`

but it consumes the **full-spectrum** `GaussianEnergyBound G r` (`E_r ≤ (2r−1)‼·n^r`), which is
**FALSE at the prize** (`DCEnergyEssential`: the `b=0` / DC term `n^{2r}/q` exceeds the Wick ceiling
once `r > β`). So the deployed count bound rests on an unsatisfiable hypothesis, exactly like the
deployed direct moment→sup route did before `OptimizedSupFromNonprincipalWick` re-grounded it.

This file re-grounds the SAME count bound on the **satisfiable** `NonprincipalWickBound ψ G r`
(`∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`, the live-measured DC-Wick crux), via one extra structural fact:

> **DC is sub-Johnson in the prize regime.** When `n² < q` (i.e. `q = |F| > |G|²`, automatic at the
> prize where `q = n^β`, `β > 2`), the principal frequency `b = 0` has `‖η_0‖² = n² < q`, so it is
> **NOT** Johnson-scale. Hence the Johnson-scale set `{b : q ≤ ‖η_b‖²}` is entirely **nonprincipal**
> (`⊆ univ.erase 0`), and the count's even-moment mass is bounded by the *nonprincipal* sum alone —
> which `NonprincipalWickBound` caps at `q·(2r−1)‼·n^r`.

So the count bound transfers verbatim onto the prize-satisfiable hypothesis, at the cost of the mild,
prize-automatic side condition `n² < q`.

## What this file proves (axiom-clean, all real)

* `johnsonScale_subset_erase_zero` — the structural fact: `n² < q ⟹ {b : q ≤ ‖η_b‖²} ⊆ univ.erase 0`.
* `card_johnson_scale_frequencies_mul_le_nonprincipalWick` — the re-grounded count bound:
  under `NonprincipalWickBound ψ G r` and `n² < q` (`r ≥ 1`),
  `#{b : q ≤ ‖η_b‖²} · q^{r-1} ≤ q·(2r−1)‼·n^r`.

Probe: `scripts/probes/probe_johnson_count_nonprincipal.py` (exact eta over thin `μ_n` in
prize-shaped primes `β ∈ 2.85…4.85`, `n = 8…64`, `r = 1…4`): `n² < q` holds, the DC term is never
Johnson-scale (`0 ∉ S` always), and `#S·q^{r-1} ≤ q·Wick` holds throughout.

## Honesty (the wall is untouched)

This is a **re-grounding**, not a closure. It does NOT prove `NonprincipalWickBound` at the prize
depth `r ≈ log q` — that is the open BGK/Paley crux (`DCWickWraparoundTransfer`). It buys: the
average/count-side anti-concentration now consumes a **prize-satisfiable** input instead of the
DC-contaminated, prize-FALSE full Wick bound. The worst-case single-frequency cancellation
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ProximityGap.Frontier.NonprincipalWickIsDCWick

namespace ProximityGap.Frontier.JohnsonCountFromNonprincipalWick

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **DC is sub-Johnson in the prize regime.** When `|G|² < |F|`, the principal frequency `b = 0`
(`‖η_0‖² = |G|²`) is below the Johnson scale `q = |F|`, so the Johnson-scale set is nonprincipal. -/
theorem johnsonScale_subset_erase_zero {ψ : AddChar F ℂ} (G : Finset F)
    (hq : (G.card : ℝ) ^ 2 < (Fintype.card F : ℝ)) :
    (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2))
      ⊆ Finset.univ.erase (0 : F) := by
  intro b hb
  rw [Finset.mem_filter] at hb
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ b⟩
  rintro rfl
  -- at b = 0: ‖η_0‖² = |G|² < q ≤ ‖η_0‖², contradiction
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hn0 : ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    rw [h0, Complex.norm_natCast]
  rw [hn0] at hb
  -- hb.2 : q ≤ |G|²  and  hq : |G|² < q  ⟹  q < q
  exact absurd (lt_of_le_of_lt hb.2 hq) (lt_irrefl _)

/-- **The re-grounded Johnson-scale count bound (satisfiable hypothesis).** Under the *nonprincipal*
Wick bound `NonprincipalWickBound ψ G r` (`∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`, satisfiable at the
prize) and the prize-automatic side condition `n² < q`, the Johnson-scale frequency count satisfies

> `#{b : q ≤ ‖η_b‖²} · q^{r-1} ≤ q · (2r−1)‼ · n^r`.

Mechanism: by `johnsonScale_subset_erase_zero` the count set `S ⊆ univ.erase 0`, so
`#S · q^r ≤ ∑_{b∈S} ‖η_b‖^{2r} ≤ ∑_{b≠0} ‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` (the hypothesis); cancel one `q`.
Re-grounds `card_johnson_scale_frequencies_mul_le_wick` (which uses the prize-FALSE full
`GaussianEnergyBound`) onto the satisfiable nonprincipal input. -/
theorem card_johnson_scale_frequencies_mul_le_nonprincipalWick {ψ : AddChar F ℂ}
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (hq : 0 < Fintype.card F)
    (hn2 : (G.card : ℝ) ^ 2 < (Fintype.card F : ℝ))
    (hW : NonprincipalWickBound ψ G r) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ (r - 1)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hqpos : (0 : ℝ) < q := by rw [hqdef]; exact_mod_cast hq
  set S := Finset.univ.filter (fun b : F => q ≤ ‖eta ψ G b‖ ^ 2) with hS
  -- S is nonprincipal (prize regime DC sub-Johnson)
  have hsub : S ⊆ Finset.univ.erase (0 : F) := johnsonScale_subset_erase_zero G hn2
  -- #S · q^r ≤ ∑_{b∈S} ‖η_b‖^{2r} ≤ ∑_{b≠0} ‖η_b‖^{2r} ≤ q·Wick  (RHS of the goal)
  set W : ℝ := (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) with hWdef
  have hstep : (S.card : ℝ) * q ^ r ≤ W := by
    calc (S.card : ℝ) * q ^ r
        = ∑ _b ∈ S, q ^ r := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) := by
            refine Finset.sum_le_sum (fun b hb => ?_)
            have hb2 : q ≤ ‖eta ψ G b‖ ^ 2 := (Finset.mem_filter.mp hb).2
            have h2r : ‖eta ψ G b‖ ^ (2 * r) = (‖eta ψ G b‖ ^ 2) ^ r := by
              rw [← pow_mul, Nat.mul_comm]
            rw [h2r]
            gcongr
      _ ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by positivity)
      _ ≤ W := hW
  -- `q^r = q^{r-1}·q` (uses `r ≥ 1`); cancel one `q`
  have hqr : q ^ r = q ^ (r - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [hqr] at hstep
  -- q ≥ 1 (a field has ≥ 1 element), so #S·q^{r-1} ≤ #S·q^{r-1}·q ≤ W.
  have hq1 : (1 : ℝ) ≤ q := by
    rw [hqdef]; exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq.ne')
  have hnn : 0 ≤ (S.card : ℝ) * q ^ (r - 1) := by positivity
  calc (S.card : ℝ) * q ^ (r - 1)
      = (S.card : ℝ) * q ^ (r - 1) * 1 := by ring
    _ ≤ (S.card : ℝ) * q ^ (r - 1) * q := by gcongr
    _ = (S.card : ℝ) * (q ^ (r - 1) * q) := by ring
    _ ≤ W := hstep

end ProximityGap.Frontier.JohnsonCountFromNonprincipalWick

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.JohnsonCountFromNonprincipalWick.johnsonScale_subset_erase_zero
#print axioms ProximityGap.Frontier.JohnsonCountFromNonprincipalWick.card_johnson_scale_frequencies_mul_le_nonprincipalWick
