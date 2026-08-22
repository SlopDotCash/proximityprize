/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteMomentAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition

/-!
# The CONCRETE unconditional Parseval lower bound on the worst period (#444)

`_ExpanderMixingBound.M_lower_parseval` proves the unconditional spectral floor
`√(n(p−n)/(p−1)) ≤ M` (`M ≈ √n`, the reverse-EML / Parseval floor), but it carries BOTH the
second-moment Parseval value `Σ_{b≠0}‖η_b‖² = n(p−n)` AND the max≥RMS step `sumSq/(p−1) ≤ M²` as
ABSTRACT real hypotheses — never discharged on the actual periods `η_b = ∑_{y∈G} ψ(by)`.

This file discharges both on the concrete `M(μ_n) = max_{b≠0}‖η_b‖` (= `worstPeriod`, the same
`sup'` object used by `ConcreteMomentAssembly`):

> `worstPeriod_sq_ge_parseval` : `n(q−n)/(q−1) ≤ M(μ_n)²`,
> `worstPeriod_ge_sqrt_parseval` : `√(n(q−n)/(q−1)) ≤ M(μ_n)`.

Mechanism (all in-tree): the nonprincipal second moment `Σ_{b≠0}‖η_b‖² = q·n − n² = n(q−n)` (full
`subgroup_gaussSum_secondMoment` minus the DC term `‖η_0‖²=n²`), and `max≥RMS`:
`Σ_{b≠0}‖η_b‖² ≤ (q−1)·M²` (every nonzero term `≤ M²`, summed over the `q−1` nonzero frequencies). So
`n(q−n) ≤ (q−1)·M²`, i.e. `M² ≥ n(q−n)/(q−1)`; take the root.

This is the CONCRETE LOWER side of the expander-mixing bracket, the unconditional companion to the
concrete UPPER side `ConcreteMomentAssembly.worstPeriod_pow_le_qEnergy_sub_dc`. Together they pin the
worst period two-sided over the real `eta`: `√(n(q−n)/(q−1)) ≤ M(μ_n)` (PROVEN) and (under the
no-wraparound residual) `M(μ_n) ≤ √e·√(2rn)`.

## Honesty (scope)

This is the LOWER bound (`≈ √n`, unconditional, Parseval-only — no Paley/BGK conjecture). It is NOT
the prize: CORE asks for the UPPER bound `M(μ_n) ≤ C·√(n·log(p/n))`, whose gap to this floor
(`√n` vs `√(n·log p)`) is exactly the prize. Pure consolidation: turns the abstract Parseval-floor
hypotheses into in-tree theorems over the real periods. CORE stays OPEN.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ProximityGap.Frontier.ConcreteMomentAssembly

namespace ProximityGap.Frontier.ConcreteParsevalLower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Concrete nonprincipal second moment.** `∑_{b≠0} ‖η_b‖² = q·n − n²`. The full Parseval second
moment `subgroup_gaussSum_secondMoment` minus the DC term `‖η_0‖² = n²`. -/
theorem sum_nonzero_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2 := by
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * (G.card : ℝ) :=
    subgroup_gaussSum_secondMoment hψ G
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hdc : ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 := by rw [h0, Complex.norm_natCast]
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ 0)).symm
  rw [hfull, hdc] at hsplit
  linarith [hsplit]

/-- **Concrete Parseval floor (squared form).** `n(q−n)/(q−1) ≤ M(μ_n)²`, where
`M(μ_n) = max_{b≠0}‖η_b‖ = worstPeriod`. Discharges the abstract `M_sq_lower` on the real periods:
the nonprincipal second moment `n(q−n)` is `≤ (q−1)·M²` (each of the `q−1` nonzero terms `≤ M²`). -/
theorem worstPeriod_sq_ge_parseval {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) :
    (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1)
      ≤ (worstPeriod ψ G hne) ^ 2 := by
  set M := worstPeriod ψ G hne with hM
  -- each nonzero term ‖η_b‖² ≤ M²
  have hterm : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 ≤ M ^ 2 := by
    intro b hb
    have hbnz : b ∈ nonzeroFreqs F := by
      rw [mem_nonzeroFreqs]; exact (Finset.mem_erase.mp hb).1
    have hle : ‖eta ψ G b‖ ≤ M := by
      rw [hM]; unfold worstPeriod; exact Finset.le_sup' (fun b => ‖eta ψ G b‖) hbnz
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    nlinarith [hnn, hle, norm_nonneg (eta ψ G b)]
  -- sum over q-1 nonzero freqs ≤ (q-1)·M²
  have hcard : (univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  have hsumle : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ 2 := by
    calc ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
        ≤ ∑ _b ∈ univ.erase (0 : F), M ^ 2 := Finset.sum_le_sum hterm
      _ = ((univ.erase (0 : F)).card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((Fintype.card F : ℝ) - 1) * M ^ 2 := by
            rw [hcard]
            congr 1
            have hqpos : 1 ≤ Fintype.card F := Nat.one_le_iff_ne_zero.mpr (by
              have : 0 < Fintype.card F := Fintype.card_pos; omega)
            push_cast [Nat.cast_sub hqpos]; ring
  -- n(q-n) = Σ_{b≠0} ‖η_b‖² ≤ (q-1)M²
  rw [sum_nonzero_secondMoment hψ G] at hsumle
  have hqm1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  -- q·n − n² = n(q−n); divide
  have hnq : (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2
      = (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by ring
  rw [hnq] at hsumle
  rw [div_le_iff₀ hqm1]
  linarith [hsumle]

/-- **★ CONCRETE unconditional Parseval lower bound on the worst period.**
`√(n(q−n)/(q−1)) ≤ M(μ_n)`, the reverse-EML / max≥RMS floor (`≈ √n`), on the real periods
`η_b = ∑_{y∈G} ψ(by)`. Take the root of `worstPeriod_sq_ge_parseval` (`0 ≤ M`). Discharges
`_ExpanderMixingBound.M_lower_parseval` concretely. Unconditional: only Parseval, NO Paley/BGK. -/
theorem worstPeriod_ge_sqrt_parseval {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
      ≤ worstPeriod ψ G hne := by
  have hsq := worstPeriod_sq_ge_parseval hψ G hne hq1
  have hMnn : 0 ≤ worstPeriod ψ G hne := worstPeriod_nonneg ψ G hne
  rw [show worstPeriod ψ G hne = Real.sqrt ((worstPeriod ψ G hne) ^ 2) from (Real.sqrt_sq hMnn).symm]
  exact Real.sqrt_le_sqrt hsq

/-- **Prize-regime numeric floor (squared).** In the prize regime `q ≥ 2n` (i.e. `2·card G ≤ card F`,
which `q = n^β` with `β ≥ 4` satisfies with huge room), the Parseval ratio floor simplifies to the
clean numeric bound `M(μ_n)² ≥ n/2`. Mechanism: `q ≥ 2n ⇒ (q−n)/(q−1) ≥ 1/2` (since
`2(q−n) ≥ q ≥ q−1`), so `n(q−n)/(q−1) ≥ n/2`, chained with `worstPeriod_sq_ge_parseval`.
(Probe `probe_parseval_half_floor.py`: 0 fails, holds even at the threshold `q = 2n−1`.) -/
theorem worstPeriod_sq_ge_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hreg : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    (G.card : ℝ) / 2 ≤ (worstPeriod ψ G hne) ^ 2 := by
  have hsq := worstPeriod_sq_ge_parseval hψ G hne hq1
  -- n(q−n)/(q−1) ≥ n/2 in the regime q ≥ 2n
  have hqm1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hnn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hfloor : (G.card : ℝ) / 2
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
    rw [le_div_iff₀ hqm1]
    -- (n/2)·(q−1) ≤ n·(q−n)  ⇔  n·(q−1) ≤ 2n·(q−n);  from q ≤ 2(q−n) i.e. 2n ≤ q
    nlinarith [hnn, hreg, hqm1]
  linarith [hfloor, hsq]

/-- **Prize-regime numeric floor (root form).** `√(n/2) ≤ M(μ_n)` whenever `q ≥ 2n`. The clean
usable `≥ √(n/2)` floor on the worst period in the prize regime, rooted from
`worstPeriod_sq_ge_half_card`. Still the EASY/unconditional Parseval direction (no BGK); the prize
gap to `√(n·log(p/n))` is untouched. -/
theorem worstPeriod_ge_sqrt_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hreg : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) / 2) ≤ worstPeriod ψ G hne := by
  have hsq := worstPeriod_sq_ge_half_card hψ G hne hq1 hreg
  have hMnn : 0 ≤ worstPeriod ψ G hne := worstPeriod_nonneg ψ G hne
  rw [show worstPeriod ψ G hne = Real.sqrt ((worstPeriod ψ G hne) ^ 2) from (Real.sqrt_sq hMnn).symm]
  exact Real.sqrt_le_sqrt hsq

/-- **Deeper prize-regime numeric floor (squared).** If `q ≥ 4n`, the same Parseval ratio gives
`M(μ_n)² ≥ 3n/4`. This is the next clean constant rung after `worstPeriod_sq_ge_half_card`:
`q ≥ 4n ⇒ 4(q−n) ≥ 3(q−1)`, so `(q−n)/(q−1) ≥ 3/4`. Still only the unconditional LOWER side. -/
theorem worstPeriod_sq_ge_three_quarters_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hreg : 4 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    (3 * (G.card : ℝ)) / 4 ≤ (worstPeriod ψ G hne) ^ 2 := by
  have hsq := worstPeriod_sq_ge_parseval hψ G hne hq1
  have hqm1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hnn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hfloor : (3 * (G.card : ℝ)) / 4
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
    rw [le_div_iff₀ hqm1]
    nlinarith [hnn, hreg, hqm1]
  linarith [hfloor, hsq]

/-- **General Parseval constant floor (squared form).** If the field is `C` times larger than the
subgroup (`C·n ≤ q`) with `C > 1`, then the exact Parseval ratio gives
`M(μ_n)² ≥ (1 - 1/C)·n`. This packages the `1/2` and `3/4` rungs into the closed form that the
mean-square floor approaches `n` from below as `q/n → ∞`. It is only the lower/Johnson side, not the
BGK upper-bound core. -/
theorem worstPeriod_sq_ge_const_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    {C : ℝ} (hC : 1 < C) (hreg : C * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    ((C - 1) / C) * (G.card : ℝ) ≤ (worstPeriod ψ G hne) ^ 2 := by
  have hsq := worstPeriod_sq_ge_parseval hψ G hne hq1
  have hqm1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hCpos : (0 : ℝ) < C := by linarith
  have hnn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hratio : (C - 1) / C
      ≤ ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
    rw [div_le_div_iff₀ hCpos hqm1]
    nlinarith [hreg, hC]
  have hfloor : ((C - 1) / C) * (G.card : ℝ)
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
    calc ((C - 1) / C) * (G.card : ℝ)
        ≤ (((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
            * (G.card : ℝ) := mul_le_mul_of_nonneg_right hratio hnn
      _ = (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) /
            ((Fintype.card F : ℝ) - 1) := by ring
  linarith [hfloor, hsq]

/-- **General Parseval constant floor (root form).** Under `C·n ≤ q` with `C > 1`,
`√(((C−1)/C) n) ≤ M(μ_n)`. This is the closed-form lower-side saturation statement: in the
thin prize regime the unconditional mean-square floor tends to `√n`, and no lower-bracket argument
from Parseval alone can produce the missing upper cancellation. -/
theorem worstPeriod_ge_sqrt_const_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    {C : ℝ} (hC : 1 < C) (hreg : C * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    Real.sqrt (((C - 1) / C) * (G.card : ℝ)) ≤ worstPeriod ψ G hne := by
  have hsq := worstPeriod_sq_ge_const_card hψ G hne hq1 hC hreg
  have hMnn : 0 ≤ worstPeriod ψ G hne := worstPeriod_nonneg ψ G hne
  rw [show worstPeriod ψ G hne = Real.sqrt ((worstPeriod ψ G hne) ^ 2) from (Real.sqrt_sq hMnn).symm]
  exact Real.sqrt_le_sqrt hsq

/-- **Deeper prize-regime numeric floor (root form).** `√(3n/4) ≤ M(μ_n)` whenever `q ≥ 4n`.
This sharpens the clean Parseval lower constant deeper in the thin prize regime, but remains a lower
bound only and does not touch the BGK/Paley upper-bound core. -/
theorem worstPeriod_ge_sqrt_three_quarters_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hreg : 4 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((3 * (G.card : ℝ)) / 4) ≤ worstPeriod ψ G hne := by
  have hsq := worstPeriod_sq_ge_three_quarters_card hψ G hne hq1 hreg
  have hMnn : 0 ≤ worstPeriod ψ G hne := worstPeriod_nonneg ψ G hne
  rw [show worstPeriod ψ G hne = Real.sqrt ((worstPeriod ψ G hne) ^ 2) from (Real.sqrt_sq hMnn).symm]
  exact Real.sqrt_le_sqrt hsq

/-- **Quadratic thin-regime sharp floor (squared form).** Deep in the prize regime, where the field
is QUADRATICALLY larger than the subgroup (`q ≥ n² − n + 1`, e.g. `q = n^β` with `β ≥ 2`), the exact
Parseval ratio gives the essentially-FULL mean-square floor `M(μ_n)² ≥ n − 1`.

This is sharper than every fixed-`C` rung above (`worstPeriod_sq_ge_const_card` only ever pays a
constant fraction `(1−1/C)·n` because it assumes the LINEAR thinness `q ≥ C·n`). The quadratic
hypothesis `q ≥ n²−n+1` lands the Plancherel floor at its true value `n−1` (i.e. `M ≳ √n` with the
optimal constant `1`), so in the prize regime `q = n^β, β ≥ 2` the unconditional lower endpoint of
the Shaw-value bracket is already the full `√n` up to an additive `1`.

Thinness-essential: the hypothesis is FALSE in the thick window (`q` comparable to `n²`), so this is
not a thickness-monotone statement. It is still only the LOWER/Johnson side — the gap to the BGK
upper `C·√(n·log(q/n))` is exactly the open prize. -/
theorem worstPeriod_sq_ge_card_pred {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hreg : (G.card : ℝ) ^ 2 - (G.card : ℝ) + 1 ≤ (Fintype.card F : ℝ)) :
    ((G.card : ℝ) - 1) ≤ (worstPeriod ψ G hne) ^ 2 := by
  have hsq := worstPeriod_sq_ge_parseval hψ G hne hq1
  have hqm1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < (G.card : ℝ) := by linarith
  -- ratio step: (q − n)/(q − 1) ≥ (n − 1)/n  ⟺  n(q − n) ≥ (n − 1)(q − 1)  ⟺  q ≥ n² − n + 1
  have hratio : ((G.card : ℝ) - 1) / (G.card : ℝ)
      ≤ ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
    rw [div_le_div_iff₀ hnpos hqm1]
    nlinarith [hreg]
  have hfloor : ((G.card : ℝ) - 1)
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
    have hmul : ((G.card : ℝ) - 1) / (G.card : ℝ) * (G.card : ℝ)
        ≤ ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) * (G.card : ℝ) :=
      mul_le_mul_of_nonneg_right hratio (le_of_lt hnpos)
    calc ((G.card : ℝ) - 1)
        = ((G.card : ℝ) - 1) / (G.card : ℝ) * (G.card : ℝ) := by
          field_simp
      _ ≤ ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) * (G.card : ℝ) := hmul
      _ = (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
          ring
  linarith [hfloor, hsq]

/-- **Quadratic thin-regime sharp floor (root form).** `√(n − 1) ≤ M(μ_n)` whenever
`q ≥ n² − n + 1` and `n > 1`. In the prize regime `q = n^β` (`β ≥ 2`) the unconditional Parseval
floor is the essentially-FULL `√n`, pinning the lower endpoint of the Shaw-value bracket at its true
value. This sharpens every fixed-`C` constant floor (which only reach `√((1−1/C)·n)`) and is
thinness-essential. Still the LOWER side only: the missing `√(log(q/n))` upper cancellation is the
prize. -/
theorem worstPeriod_ge_sqrt_card_pred {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hreg : (G.card : ℝ) ^ 2 - (G.card : ℝ) + 1 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) - 1) ≤ worstPeriod ψ G hne := by
  have hsq := worstPeriod_sq_ge_card_pred hψ G hne hq1 hG1 hreg
  have hMnn : 0 ≤ worstPeriod ψ G hne := worstPeriod_nonneg ψ G hne
  rw [show worstPeriod ψ G hne = Real.sqrt ((worstPeriod ψ G hne) ^ 2) from (Real.sqrt_sq hMnn).symm]
  exact Real.sqrt_le_sqrt hsq

/-- **Clean `β ≥ 2` prize-regime floor.** Under the textbook thinness `n² ≤ q` (i.e. `q = n^β` with
`β ≥ 2`), the Parseval floor reaches `√(n − 1) ≤ M(μ_n)`. The quadratic hypothesis `n² ≤ q` implies
the sharper `n² − n + 1 ≤ q` used by `worstPeriod_ge_sqrt_card_pred` (since `n ≥ 1`), so this is the
clean restatement directly in terms of `n² ≤ q`. Still the LOWER/Johnson side only. -/
theorem worstPeriod_ge_sqrt_card_pred_of_sq_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) - 1) ≤ worstPeriod ψ G hne := by
  have hreg : (G.card : ℝ) ^ 2 - (G.card : ℝ) + 1 ≤ (Fintype.card F : ℝ) := by
    have hge1 : (1 : ℝ) ≤ (G.card : ℝ) := le_of_lt hG1
    nlinarith [hsq, hge1]
  exact worstPeriod_ge_sqrt_card_pred hψ G hne hq1 hG1 hreg

/-- **Floor-to-ideal ratio (`√n · √(1−1/n)` form).** Rewriting `√(n−1) = √n · √(1−1/n)`, the
quadratic-regime floor says `M(μ_n) ≥ √n · √(1 − 1/n)` whenever `n² ≤ q`. The deficit factor
`√(1 − 1/n) → 1`, so the unconditional Parseval floor reaches the ideal Plancherel value `√n` with
multiplicative loss tending to `1`: in the prize regime the lower bracket endpoint is the FULL `√n`
asymptotically, with optimal constant. (Probe: ratio `√(1−1/n)` = .866,.935,.968,.984,.992,.996,.998 at
`n=4..256`.) Still the LOWER side only — the missing `√(log(q/n))` upper cancellation is the prize. -/
theorem worstPeriod_ge_sqrt_mul_one_sub {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt (G.card : ℝ) * Real.sqrt (1 - 1 / (G.card : ℝ)) ≤ worstPeriod ψ G hne := by
  have hbase := worstPeriod_ge_sqrt_card_pred_of_sq_le hψ G hne hq1 hG1 hsq
  have hnpos : (0 : ℝ) < (G.card : ℝ) := by linarith
  -- √n · √(1−1/n) = √(n·(1−1/n)) = √(n−1)
  have hfac : Real.sqrt (G.card : ℝ) * Real.sqrt (1 - 1 / (G.card : ℝ))
      = Real.sqrt ((G.card : ℝ) - 1) := by
    rw [← Real.sqrt_mul (le_of_lt hnpos)]
    congr 1
    field_simp
  rw [hfac]
  exact hbase

end ProximityGap.Frontier.ConcreteParsevalLower

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.sum_nonzero_secondMoment
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_sq_ge_parseval
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_parseval
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_sq_ge_half_card
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_half_card
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_sq_ge_three_quarters_card
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_sq_ge_const_card
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_sq_ge_card_pred
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_card_pred
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_card_pred_of_sq_le
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_mul_one_sub
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_const_card
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_three_quarters_card
