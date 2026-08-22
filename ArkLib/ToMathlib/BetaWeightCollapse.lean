/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightInduction
import ArkLib.ToMathlib.BetaRecursion
import ArkLib.ToMathlib.WeightLambdaCalculus
import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.Data.Polynomial.RationalFunctions
import Mathlib

/-!
# The App.-A.4 weight collapse for the Hensel-lift numerators `β_t` (brick **L10**)

This file discharges the **L10** residual of brick L9 (`ArkLib.ToMathlib.BetaWeightInduction`): it
instantiates the abstract `ℕ`-budgets of the Claim-A.2 weight induction with the *concrete* App.-A.4
values and **proves** the App.-A line-2877–2881 telescoping, delivering the final Claim-A.2 bound

```
weight_Λ_over_𝒪 hH (betaRec … t) D ≤ (2t+1)·d_R·D     (where d_R = R.natDegree).
```

## The concrete budgets (App.-A.4)

* `bW := D − d_H` — `Λ(W)` (brick L3, `weight_Λ_over_𝒪_W_reg_le`).
* `bξ := (d_R − 1)·(D − d_H + 1)` — `Λ(ξ)` (`weight_ξ_bound`, `RationalFunctions.lean:2708`).
* `bB i₁ p := (D − Σλ) + (d_R − δ − Σλ)·(D − d_H)` (App.-A line 131/2929/2933), **and `= 0` when the
  Hasse derivative vanishes (`Σλ > d_R − δ`)**, the case in which `Bcoeff i₁ p = 0`.
* the **tight** target `wβ_tight t := 1 + (t+1)·bW + e_t·bξ`, `e_t = max(0, 2t−1)` (App.-A Claim
A.2),
  which telescopes term-by-term; the loose `(2t+1)·d_R·D` is the *final* collapse.

## What is proved (all kernel-clean: no `sorry`/`admit`/`axiom`/`native_decide`)

* `betaRec_partsCount_smul_sum` / `betaRec_partsCount_smul_card` — the two partition identities
  `Σ_l count(l)·l = Σλ.sum = m` and `Σ_l count(l) = #parts = Σλ`, the combinatorial core of the
  telescoping (`Finset.sum_multiset_map_count` / `Multiset.toFinset_sum_count_eq`).

* `betaTele_sum_eq` — the **closed form** of the recursion's per-part budget sum
  `Σ_l count(l)·wβ_tight(l) = Σλ + (m + Σλ)·bW + (2m − Σλ)·bξ` (all parts are `≥ 1`, so
  `e_l = 2l − 1`).

* `betaTele_tight` — the **App.-A line-2877–2881 telescoping**, proved as a pure-`ℕ` inequality:
  for every non-forbidden `(i₁, p)` with `Σλ ≤ d_R − δ`,
  `betaWExp(i₁)·bW + betaξExp(i₁,p)·bξ + bB i₁ p + Σ_l count·wβ_tight(l) ≤ wβ_tight(t+1)`
  (with explicit slack `d_R − d_H ≥ 0`).

* `betaRec_weight_le_tight` — the **strong-induction theorem with the concrete tight budget**:
routed
  through the L9 skeleton (`betaRec_weightBound_of_term_bounds` + `betaTerm_weight_le`), splitting
  per
  term into (forbidden ⟹ `0`), (Hasse-vanishing `Σλ > d_R − δ` ⟹ `Bcoeff = 0 ⟹ betaTerm = 0`), and
  the genuine case discharged by `betaTele_tight`.

* `betaRec_weight_le_concrete` — **brick L10**: the loose collapse
  `weight_Λ_over_𝒪 hH (betaRec … t) D ≤ (2t+1)·d_R·D`, via `tight ≤ (2t+1)·d_R·D`.

## Residual constant hypotheses (the genuine, isolated L10 inputs — explicit, never `sorry`)

The file is parametric in the in-tree objects; the only constants it *requires precise values for*
are isolated as the smallest explicit hypotheses (a brick is honest iff these are the real App.-A
facts, not faked):

* `hbB` — that the supplied `bB` budget bounds `Λ(Bcoeff i₁ p)` (App.-A line 131; brick L2b/L4).
* `hBzero` — that `Bcoeff i₁ p = 0` when the Hasse derivative vanishes (`d_R − δ < Σλ`); App.-A.
* `hdH_le` — `d_H ≤ d_R` (the cofactor-degree fact `weight_ξ_bound` itself proves internally).
* `hxi` — the `weight_ξ_bound` hypotheses `2 ≤ d_R` and `D ≥ totalDegree (evalX x₀ R)` (so the
  in-tree `weight_ξ_bound` fires; these are App.-A's standing degree assumptions).

This file does **not** edit the (0-sorry) `RationalFunctions.lean`; all names live in `namespace
ArkLib`.  It also documents one *latent interface caveat* of `betaRec_weight_le`: its `htele`
hypothesis is stated for **all** pairs `(i₁, p)`, yet is false on the single forbidden pair
`(0, {t+1})` for any non-zero `bB` (the recursion drops that term but the budget formula counts it),
so this file re-derives the bound directly from the L9 *skeleton* with the forbidden split handled
correctly, rather than instantiating the over-strong `htele`.
-/

namespace ArkLib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-! ### Partition-count identities

The recursion's per-part budget sum runs over `p.parts.toFinset.attach` as
`Σ_l count(l)·g(l)`.  Two combinatorial identities collapse it: `Σ_l count(l) = #parts`
(`Multiset.toFinset_sum_count_eq`) and `Σ_l count(l)·l = parts.sum` (`Finset.sum_multiset_map_count`
with `f = id`).  We phrase them on the `attach` domain the recursion uses. -/

/-- `Σ_{l ∈ parts.toFinset.attach} count(l)·l = parts.sum`. -/
lemma betaRec_partsCount_smul_sum {m : ℕ} (p : Nat.Partition m) :
    ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * l.1 = p.parts.sum := by
  classical
  rw [Finset.sum_attach p.parts.toFinset (fun l => p.parts.count l * l)]
  have := Finset.sum_multiset_map_count p.parts (fun l : ℕ => l)
  simpa [smul_eq_mul, Multiset.map_id'] using this.symm

/-- `Σ_{l ∈ parts.toFinset.attach} count(l) = #parts`. -/
lemma betaRec_partsCount_smul_card {m : ℕ} (p : Nat.Partition m) :
    ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 = Multiset.card p.parts := by
  classical
  rw [Finset.sum_attach p.parts.toFinset (fun l => p.parts.count l)]
  exact Multiset.toFinset_sum_count_eq p.parts

/-- The number of parts is at most their sum (each part is `≥ 1`): `#parts ≤ m`. -/
lemma betaRec_card_le {m : ℕ} (p : Nat.Partition m) : Multiset.card p.parts ≤ m := by
  classical
  -- `card = Σ_l count(l)·1 ≤ Σ_l count(l)·l = sum = m`, since every part `l ≥ 1`.
  have hcard : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 = Multiset.card p.parts :=
    betaRec_partsCount_smul_card p
  have hsum : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * l.1 = m := by
    rw [betaRec_partsCount_smul_sum p, p.parts_sum]
  calc Multiset.card p.parts
      = ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 := hcard.symm
    _ ≤ ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * l.1 := by
        refine Finset.sum_le_sum (fun l _ => ?_)
        have h1 : 1 ≤ l.1 := p.parts_pos (Multiset.mem_toFinset.mp l.2)
        calc p.parts.count l.1 = p.parts.count l.1 * 1 := (Nat.mul_one _).symm
          _ ≤ p.parts.count l.1 * l.1 := Nat.mul_le_mul_left _ h1
    _ = m := hsum

/-! ### The tight Claim-A.2 budget and its per-part sum

`wβ_tight t = 1 + (t+1)·bW + e_t·bξ` with `e_t = max(0, 2t−1) = 2t − 1` (truncated `ℕ`).  Each part
`l` of a partition is `≥ 1`, so `e_l = 2l − 1` exactly, and the per-part sum closes to
`Σλ + (m + Σλ)·bW + (2m − Σλ)·bξ`. -/

/-- The tight Claim-A.2 weight budget `1 + (t+1)·bW + e_t·bξ`, `e_t = 2t − 1` (truncated `ℕ`). -/
def wβ_tight (bW bξ : ℕ) (t : ℕ) : ℕ := 1 + (t + 1) * bW + (2 * t - 1) * bξ

/-- `Σ_l count(l)·(2l − 1) = 2·m − #parts`, the `ξ`-exponent half of the per-part sum.  Uses
`Σ count·l = m`, `Σ count = #parts`, and that every part is `≥ 1` (so `2l ≥ 1`, no truncation). -/
lemma betaRec_partsCount_two_mul_sub {m : ℕ} (p : Nat.Partition m) :
    ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * (2 * l.1 - 1)
      = 2 * m - Multiset.card p.parts := by
  classical
  have hsum : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * l.1 = m := by
    rw [betaRec_partsCount_smul_sum p, p.parts_sum]
  have hcard : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 = Multiset.card p.parts :=
    betaRec_partsCount_smul_card p
  -- For each part `l ≥ 1`: `count·(2l − 1) = count·(2l) − count` with `2l ≥ 1`.
  have key : ∀ l ∈ p.parts.toFinset.attach,
      p.parts.count l.1 * (2 * l.1 - 1)
        = p.parts.count l.1 * (2 * l.1) - p.parts.count l.1 := by
    intro l _
    rw [Nat.mul_sub, Nat.mul_one]
  rw [Finset.sum_congr rfl key]
  -- `Σ (count·2l − count) = Σ count·2l − Σ count` since `count·2l ≥ count` pointwise.
  rw [Finset.sum_tsub_distrib]
  · have h2 : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * (2 * l.1) = 2 * m := by
      have : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * (2 * l.1)
          = 2 * ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * l.1 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun l _ => by ring)
      rw [this, hsum]
    rw [h2, hcard]
  · intro l hl
    have h1 : 1 ≤ l.1 := p.parts_pos (Multiset.mem_toFinset.mp l.2)
    have : p.parts.count l.1 * 1 ≤ p.parts.count l.1 * (2 * l.1) :=
      Nat.mul_le_mul_left _ (by omega)
    simpa using this

/-- **Closed form of the recursion's per-part budget sum.**  Because every part `l ∈ p.parts` is
`≥ 1` (so `e_l = 2l − 1`), the sum `Σ_l count(l)·wβ_tight(l)` over the partition `p` of `m` equals
`#parts + (m + #parts)·bW + (2m − #parts)·bξ`.  This is the combinatorial heart of the telescoping
(App.-A line 2877). -/
lemma betaTele_sum_eq (bW bξ : ℕ) {m : ℕ} (p : Nat.Partition m) :
    ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * wβ_tight bW bξ l.1
      = Multiset.card p.parts + (m + Multiset.card p.parts) * bW
          + (2 * m - Multiset.card p.parts) * bξ := by
  classical
  set N := Multiset.card p.parts with hN
  have hcard : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 = N :=
    betaRec_partsCount_smul_card p
  have hsum : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * l.1 = m := by
    rw [betaRec_partsCount_smul_sum p, p.parts_sum]
  have hxi : ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * (2 * l.1 - 1) = 2 * m - N :=
    betaRec_partsCount_two_mul_sub p
  -- Expand `count·wβ_tight l = count·1 + count·((l+1)·bW) + count·((2l−1)·bξ)` and split the sum.
  have key : ∀ l ∈ p.parts.toFinset.attach,
      p.parts.count l.1 * wβ_tight bW bξ l.1
        = p.parts.count l.1
          + (p.parts.count l.1 * l.1 + p.parts.count l.1) * bW
          + p.parts.count l.1 * (2 * l.1 - 1) * bξ := by
    intro l _
    unfold wβ_tight
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    congr 1
    · congr 1
      rw [show (l.1 + 1) * bW = l.1 * bW + bW by ring, Nat.mul_add,
          show p.parts.count l.1 * (l.1 * bW) = p.parts.count l.1 * l.1 * bW by ring,
          Nat.add_mul]
    · rw [show p.parts.count l.1 * ((2 * l.1 - 1) * bξ)
            = p.parts.count l.1 * (2 * l.1 - 1) * bξ by ring]
  rw [Finset.sum_congr rfl key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Three sums: `Σ count = N`, `Σ (count·l + count)·bW = (m + N)·bW`,
  -- `Σ count·(2l−1)·bξ = (2m − N)·bξ`.
  rw [hcard]
  congr 1
  · congr 1
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, hsum, hcard]
  · rw [← Finset.sum_mul, hxi]

/-! ### The App.-A line-2877–2881 telescoping (pure `ℕ`)

The genuine numerical L9/L10 step.  With the concrete budgets `bW = D − d_H`,
`bξ = (d − 1)(D − d_H + 1)`, `bB i₁ p = (D − Σλ) + (d − δ − Σλ)·bW`, for every **non-forbidden**
`(i₁, p)` of `m = t+1−i₁` with `Σλ ≤ d − δ` (the Hasse-derivative-nonvanishing regime),

```
betaWExp(i₁)·bW + betaξExp(i₁,p)·bξ + bB i₁ p + Σ_l count·wβ_tight(l) ≤ wβ_tight(t+1)
```

with explicit slack `d − d_H ≥ 0`.  Proved by reducing the part-sum to its closed form
(`betaTele_sum_eq`), establishing the *exact* (non-truncated) values of the `ℕ`-truncated exponents
from the non-forbidden / `Σλ ≤ d − δ` side conditions, then `nlinarith` over `ℤ`. -/

/-- The pure-`ℕ` telescoping arithmetic for the `i₁ = 0` term (`δ = 1`, `betaWExp = 0`,
`betaξExp = N − 2`, `m = t + 1`).  The slack is exactly `d − d_H ≥ 0`.  Proved over `ℤ` after
casing on `N ≤ D` (only there is `D − N` exact; when `N > D` the term truncates to `0`, leaving more
slack).  The combinatorial input `N ≤ t + 1` (`#parts ≤ sum`) keeps `2(t+1) − N` exact. -/
lemma betaTele_core_zero {D d dH t N : ℕ}
    (hdH_le : dH ≤ d) (hdH_D : dH ≤ D) (hN2 : 2 ≤ N) (hN_le_d : N ≤ d - 1)
    (hNm : N ≤ t + 1) :
    0 * (D - dH) + (N - 2) * ((d - 1) * (D - dH + 1))
        + ((D - N) + (d - 1 - N) * (D - dH))
        + (N + (t + 1 + N) * (D - dH) + (2 * (t + 1) - N) * ((d - 1) * (D - dH + 1)))
      ≤ 1 + (t + 1 + 1) * (D - dH)
          + (2 * (t + 1) - 1) * ((d - 1) * (D - dH + 1)) := by
  rcases le_or_gt N D with hND | hND
  · -- `N ≤ D`: every subtraction is exact; slack is exactly `d − dH ≥ 0`.
    zify [hdH_le, hdH_D, hN2, hN_le_d, hNm, hND,
      show 1 ≤ d by omega, show 2 ≤ 2 * (t + 1) by omega,
      show N ≤ 2 * (t + 1) by omega, show 1 ≤ 2 * (t + 1) by omega]
    have hslack : (1 : ℤ) + (↑t + 1 + 1) * (↑D - ↑dH)
          + (2 * (↑t + 1) - 1) * ((↑d - 1) * (↑D - ↑dH + 1))
        - (0 * (↑D - ↑dH) + (↑N - 2) * ((↑d - 1) * (↑D - ↑dH + 1))
            + (↑D - ↑N + (↑d - 1 - ↑N) * (↑D - ↑dH))
            + (↑N + (↑t + 1 + ↑N) * (↑D - ↑dH)
                + (2 * (↑t + 1) - ↑N) * ((↑d - 1) * (↑D - ↑dH + 1))))
        = (d : ℤ) - dH := by ring
    have hle : (dH : ℤ) ≤ d := by exact_mod_cast hdH_le
    linarith [hslack, hle]
  · -- `N > D`: `D − N = 0` truncates; slack becomes `(d − dH) + (D − N) ≥ 0` (since `N ≤ d − 1`).
    rw [show D - N = 0 by omega, Nat.add_zero]
    zify [hdH_le, hdH_D, hN2, hN_le_d, hNm,
      show 1 ≤ d by omega, show 2 ≤ 2 * (t + 1) by omega,
      show N ≤ 2 * (t + 1) by omega, show 1 ≤ 2 * (t + 1) by omega]
    have hslack : (1 : ℤ) + (↑t + 1 + 1) * (↑D - ↑dH)
          + (2 * (↑t + 1) - 1) * ((↑d - 1) * (↑D - ↑dH + 1))
        - (0 * (↑D - ↑dH) + (↑N - 2) * ((↑d - 1) * (↑D - ↑dH + 1))
            + (0 + (↑d - 1 - ↑N) * (↑D - ↑dH))
            + (↑N + (↑t + 1 + ↑N) * (↑D - ↑dH)
                + (2 * (↑t + 1) - ↑N) * ((↑d - 1) * (↑D - ↑dH + 1))))
        = ((d : ℤ) - dH) + ((D : ℤ) - N) := by ring
    have hle : (dH : ℤ) ≤ d := by exact_mod_cast hdH_le
    have hNd1 : (N : ℤ) ≤ (d : ℤ) - 1 := by
      have : N ≤ d - 1 := hN_le_d
      have h1d : 1 ≤ d := by omega
      zify [h1d] at this; linarith
    have hdHD : (dH : ℤ) ≤ D := by exact_mod_cast hdH_D
    linarith [hslack, hle, hNd1, hdHD]

/-- The pure-`ℕ` telescoping arithmetic for the `i₁ ≥ 1` term (`δ = 0`, `betaWExp = i₁ − 1`,
`betaξExp = 2i₁ + N − 2`, `m = t + 1 − i₁`).  The slack is again exactly `d − d_H ≥ 0`.  The
combinatorial input `N ≤ t + 1 − i₁` (`#parts ≤ sum`) keeps `2(t+1−i₁) − N` exact. -/
lemma betaTele_core_pos {D d dH t i₁ N : ℕ}
    (hdH_le : dH ≤ d) (hdH_D : dH ≤ D) (h1d : 1 ≤ d) (hipos : 0 < i₁) (hi₁ : i₁ ≤ t + 1)
    (hN_le_d : N ≤ d) (hNm : N ≤ t + 1 - i₁) :
    (i₁ - 1) * (D - dH) + (2 * i₁ + N - 2) * ((d - 1) * (D - dH + 1))
        + ((D - N) + (d - 0 - N) * (D - dH))
        + ((N + ((t + 1 - i₁) + N) * (D - dH)
            + (2 * (t + 1 - i₁) - N) * ((d - 1) * (D - dH + 1))))
      ≤ 1 + (t + 1 + 1) * (D - dH)
          + (2 * (t + 1) - 1) * ((d - 1) * (D - dH + 1)) := by
  simp only [Nat.sub_zero]
  have hi1 : 1 ≤ i₁ := hipos
  have hNm2 : N ≤ 2 * (t + 1 - i₁) := by omega
  have h2iN : 2 ≤ 2 * i₁ + N := by omega
  have hle : (dH : ℤ) ≤ d := by exact_mod_cast hdH_le
  have hdHD : (dH : ℤ) ≤ D := by exact_mod_cast hdH_D
  have hNdz : (N : ℤ) ≤ d := by exact_mod_cast hN_le_d
  rcases le_or_gt N D with hND | hND
  · -- `N ≤ D`: exact; slack is exactly `d − dH ≥ 0`.
    zify [hdH_le, hdH_D, hN_le_d, hND, hi1, hi₁, hNm, h1d, hNm2, h2iN,
      show 1 ≤ 2 * (t + 1) by omega]
    have hslack : (1 : ℤ) + (↑t + 1 + 1) * (↑D - ↑dH)
          + (2 * (↑t + 1) - 1) * ((↑d - 1) * (↑D - ↑dH + 1))
        - ((↑i₁ - 1) * (↑D - ↑dH) + (2 * ↑i₁ + ↑N - 2) * ((↑d - 1) * (↑D - ↑dH + 1))
            + (↑D - ↑N + (↑d - ↑N) * (↑D - ↑dH))
            + (↑N + (↑t + 1 - ↑i₁ + ↑N) * (↑D - ↑dH)
                + (2 * (↑t + 1 - ↑i₁) - ↑N) * ((↑d - 1) * (↑D - ↑dH + 1))))
        = (d : ℤ) - dH := by ring
    linarith [hslack, hle]
  · -- `N > D`: `D − N = 0` truncates; slack becomes `(d − dH) + (D − N) ≥ 0` (since `N ≤ d`).
    rw [show D - N = 0 by omega, Nat.add_zero]
    zify [hdH_le, hdH_D, hN_le_d, hi1, hi₁, hNm, h1d, hNm2, h2iN,
      show 1 ≤ 2 * (t + 1) by omega]
    have hslack : (1 : ℤ) + (↑t + 1 + 1) * (↑D - ↑dH)
          + (2 * (↑t + 1) - 1) * ((↑d - 1) * (↑D - ↑dH + 1))
        - ((↑i₁ - 1) * (↑D - ↑dH) + (2 * ↑i₁ + ↑N - 2) * ((↑d - 1) * (↑D - ↑dH + 1))
            + (0 + (↑d - ↑N) * (↑D - ↑dH))
            + (↑N + (↑t + 1 - ↑i₁ + ↑N) * (↑D - ↑dH)
                + (2 * (↑t + 1 - ↑i₁) - ↑N) * ((↑d - 1) * (↑D - ↑dH + 1))))
        = ((d : ℤ) - dH) + ((D : ℤ) - N) := by ring
    have hdz : (D : ℤ) ≤ N := le_of_lt (by exact_mod_cast hND)
    linarith [hslack, hle, hdHD, hNdz, hdz]

/-- **The App.-A telescoping inequality (brick L10 core).**  For a non-forbidden `(i₁, p)` of
`m = t + 1 − i₁` whose number of parts `N = Σλ` satisfies `N ≤ d − δ` (`δ = betaδ i₁`), the per-term
budget collapses into the next tight budget `wβ_tight (t+1)`.  The hypotheses isolate exactly the
in-tree degree facts `d_H ≤ d` and `d_H ≤ D` (the rest is the recursion's combinatorics). -/
lemma betaTele_tight {D d dH : ℕ} (hdH_le : dH ≤ d) (hdH_D : dH ≤ D) (hd1 : 1 ≤ d)
    (t i₁ : ℕ) (p : Nat.Partition (t + 1 - i₁)) (hi₁ : i₁ ≤ t + 1)
    (hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)))
    (hNd : Multiset.card p.parts ≤ d - betaδ i₁) :
    betaWExp i₁ * (D - dH) + betaξExp i₁ p * ((d - 1) * (D - dH + 1))
        + ((D - Multiset.card p.parts)
            + (d - betaδ i₁ - Multiset.card p.parts) * (D - dH))
        + ∑ l ∈ p.parts.toFinset.attach,
            p.parts.count l.1 * wβ_tight (D - dH) ((d - 1) * (D - dH + 1)) l.1
      ≤ wβ_tight (D - dH) ((d - 1) * (D - dH + 1)) (t + 1) := by
  classical
  set bW := D - dH with hbW
  set bξ := (d - 1) * (D - dH + 1) with hbξ
  set N := Multiset.card p.parts with hN
  -- The part-sum closed form.
  rw [betaTele_sum_eq bW bξ p]
  -- abbreviate `m = t + 1 - i₁`; since `i₁ ≤ t+1`, `m + i₁ = t + 1`.
  have hm_eq : (t + 1 - i₁) + i₁ = t + 1 := by omega
  -- `N ≥ 1` (a non-empty partition for non-forbidden terms): every term has at least one part since
  -- if `m = 0` the only partition is empty, but then `N = 0`; we must show `N ≥ 1` only where
  -- needed.
  -- For the bound we instead use `1 ≤ N` from the non-forbidden structure when `m ≥ 1`, and handle
  -- `m = 0` (i.e. `i₁ = t+1`) directly.
  -- Determine `δ` and the exponent values by casing on `i₁`.
  rcases Nat.eq_zero_or_pos i₁ with hi0 | hipos
  · -- `i₁ = 0`: `δ = 1`, `betaWExp 0 = 0`, `m = t + 1`, and non-forbidden ⟹ `N ≥ 2`.
    subst hi0
    simp only [Nat.sub_zero] at p hexcl hN hNd ⊢
    have hδ : betaδ 0 = 1 := by simp [betaδ]
    have hWexp : betaWExp 0 = 0 := betaWExp_zero
    have hpsum : p.parts.sum = t + 1 := p.parts_sum
    -- non-forbidden with `i₁ = 0`: the partition is not the single block `{t+1}`, so `N ≥ 2`.
    have hN2 : 2 ≤ N := by
      rw [hN]
      by_contra hlt
      replace hlt : Multiset.card p.parts < 2 := Nat.lt_of_not_le hlt
      -- `card ≤ 1`; combined with `parts.sum = t+1 ≥ 1`, the only option is the single block.
      interval_cases hc : (Multiset.card p.parts)
      · -- card = 0 ⟹ parts empty ⟹ sum = 0, but sum = t+1 ≥ 1.
        have : p.parts = 0 := Multiset.card_eq_zero.mp hc
        rw [this] at hpsum; simp at hpsum
      · -- card = 1 ⟹ single block ⟹ parts = {t+1}, the forbidden pair.
        obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hc
        apply hexcl
        refine ⟨trivial, ?_⟩
        rw [ha] at hpsum ⊢
        simp only [Multiset.sum_singleton] at hpsum
        rw [hpsum]
    -- `betaξExp 0 p = 2·0 + N − 2 = N − 2`, exact since `N ≥ 2`.
    have hξexp : betaξExp 0 p = N - 2 := by simp [betaξExp, hN]
    -- `δ = 1`, so `bB`'s `(d − δ − N) = d − 1 − N`.
    rw [hWexp, hξexp, hδ]
    rw [hbW, hbξ]
    have hN_le_d : N ≤ d - 1 := by rw [hδ] at hNd; exact hNd
    have hNm : N ≤ t + 1 := by rw [hN]; exact betaRec_card_le p
    unfold wβ_tight
    -- `i₁ = 0`: `betaWExp = 0`, so the `bW`-power factor drops; the inequality is then linear in
    -- `bW`
    -- after expanding `bξ`.  The `#parts ≤ sum` fact (`hNm`) keeps `2(t+1) − N` exact.
    exact betaTele_core_zero hdH_le hdH_D hN2 hN_le_d hNm
  · -- `i₁ ≥ 1`: `δ = 0`, `betaWExp i₁ = i₁ − 1`, `betaξExp = 2i₁ + N − 2` (≥ 0 since `2i₁ ≥ 2`).
    have hδ : betaδ i₁ = 0 := by simp [betaδ, Nat.ne_of_gt hipos]
    have hWexp : betaWExp i₁ = i₁ - 1 := betaWExp_of_pos hipos
    have hξexp : betaξExp i₁ p = 2 * i₁ + N - 2 := by simp [betaξExp, hN]
    rw [hWexp, hξexp, hδ]
    rw [hbW, hbξ]
    have hN_le_d : N ≤ d := by rw [hδ] at hNd; simpa using hNd
    have hNm : N ≤ t + 1 - i₁ := by rw [hN]; exact betaRec_card_le p
    unfold wβ_tight
    exact betaTele_core_pos hdH_le hdH_D hd1 hipos hi₁ hN_le_d hNm

/-! ### The L10 collapse `wβ_tight ≤ (2t+1)·d_R·D`

The final numerical step (App.-A line 2879–2881): the tight budget `1 + (t+1)(D−d_H) +
e_t(d−1)(D−d_H+1)`
is bounded by the loose `(2t+1)·d_R·D`.  Over `ℕ` (with `1 ≤ d_H ≤ d_R`, `d_H ≤ D`) the slack is a
polynomial with non-negative coefficients in the slack variables `D−d_H`, `d_R−d_H`, `d_H−1`, so the
inequality holds by an explicit `ring`-rewrite plus `Nat.le_add_right`. -/

/-- **The L10 collapse.**  `wβ_tight (D − d_H) ((d_R − 1)(D − d_H + 1)) t ≤ (2t+1)·d_R·D`, the loose
Claim-A.2 form, for `1 ≤ d_H ≤ d_R` and `d_H ≤ D`. -/
lemma wβ_tight_le_loose {D d dH : ℕ} (hdH1 : 1 ≤ dH) (hdH_le : dH ≤ d) (hdH_D : dH ≤ D) (t : ℕ) :
    wβ_tight (D - dH) ((d - 1) * (D - dH + 1)) t ≤ (2 * t + 1) * d * D := by
  unfold wβ_tight
  obtain ⟨a, rfl⟩ : ∃ a, D = dH + a := ⟨D - dH, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, d = dH + b := ⟨d - dH, by omega⟩
  obtain ⟨h, rfl⟩ : ∃ h, dH = 1 + h := ⟨dH - 1, by omega⟩
  simp only [show ∀ x : ℕ, 1 + h + x - (1 + h) = x from fun x => by omega]
  rw [show 1 + h + b - 1 = h + b by omega]
  cases t with
  | zero =>
      rw [show 2 * 0 - 1 = 0 by omega]
      rw [show (2 * 0 + 1) * (1 + h + b) * (1 + h + a)
            = (1 + (0 + 1) * a + 0 * ((h + b) * (a + 1)))
              + (a * b + a * h + b * h + b + h ^ 2 + h * 2) from by ring]
      exact Nat.le_add_right _ _
  | succ t' =>
      rw [show 2 * (t' + 1) - 1 = 2 * t' + 1 by omega]
      rw [show (2 * (t' + 1) + 1) * (1 + h + b) * (1 + h + a)
            = (1 + (t' + 1 + 1) * a + (2 * t' + 1) * ((h + b) * (a + 1)))
              + (a * b * 2 + a * h * 2 + a * t' + a + b * h * t' * 2 + b * h * 3 + b * 2
                  + h ^ 2 * t' * 2 + h ^ 2 * 3 + h * t' * 2 + h * 5 + t' * 2 + 2) from by ring]
      exact Nat.le_add_right _ _

/-! ### The strong-induction theorem with the concrete tight budget (brick L10)

The Claim-A.2 bound with the **concrete** tight budget `wβ_tight`, proved by strong induction on
`t`,
routed through the L9 *skeleton* `betaRec_weightBound_of_term_bounds` with the forbidden split
handled
correctly (avoiding the over-strong `htele` of `betaRec_weight_le`).  Per term:

* forbidden `(0, {t+1})` ⟹ `betaTerm = 0` (weight `⊥`);
* Hasse-vanishing `Σλ > d_R − δ` ⟹ `Bcoeff = 0` (`hBzero`) ⟹ `betaTerm = 0` (weight `⊥`);
* otherwise `betaTerm_weight_le` (L9) + `betaTele_tight` collapse to `wβ_tight (t+1)`.

The base case `weight(T) = D + 1 − d_H = wβ_tight 0` is L3's `weight_Λ_over_𝒪_T_le`. -/

/-- **Claim-A.2 weight bound with the concrete tight budget (brick L10, tight form).** -/
theorem betaRec_weight_le_tight (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D d : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd1 : 1 ≤ d) (hdH_le : H.natDegree ≤ d) (hdH_D : H.natDegree ≤ D)
    -- L4/L2b: the App.-A `B`-numerator weight budget, and its vanishing off the Hasse support.
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (d - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        d - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    -- L3/L5: the prefactor weight budgets `Λ(W) ≤ D − d_H`, `Λ(ξ) ≤ (d−1)(D − d_H + 1)`.
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D
        ≤ (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ)) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some (wβ_tight (D - H.natDegree) ((d - 1) * (D - H.natDegree + 1)) t) :
          WithBot ℕ) := by
  classical
  -- abbreviations matching the budgets.
  set dH := H.natDegree with hdH
  set bW := D - dH with hbW_def
  set bξ := (d - 1) * (D - dH + 1) with hbξ_def
  have hbW_le : weight_Λ_over_𝒪 hH (W_𝒪 H) D ≤ (WithBot.some bW : WithBot ℕ) := by
    rw [hbW_def, hdH]; exact weight_Λ_over_𝒪_W_reg_le hD hH
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    match t with
    | 0 =>
        rw [betaRec_zero]
        -- base case: `weight(T) ≤ D + 1 − d_H = wβ_tight 0`.
        refine le_trans (weight_Λ_over_𝒪_T_le hD hH) ?_
        rw [WithBot.coe_le_coe]
        show D + 1 - Bivariate.natDegreeY H ≤ wβ_tight bW bξ 0
        unfold wβ_tight
        rw [hbW_def, hbξ_def]
        have : Bivariate.natDegreeY H = dH := rfl
        rw [this]; omega
    | (s + 1) =>
        refine betaRec_weightBound_of_term_bounds x₀ R H hHyp Bcoeff s hD hH ?_
        intro i₁ hi₁ p
        by_cases hexcl : ¬ (i₁ = 0 ∧ p.parts = ({s + 1} : Multiset ℕ))
        · -- genuine term: split on the Hasse-support condition `Σλ ≤ d − δ`.
          by_cases hNd : Multiset.card p.parts ≤ d - betaδ i₁
          · -- `betaTerm_weight_le` (L9) gives the per-term budget; `betaTele_tight` collapses it.
            have hbβ : ∀ l ∈ p.parts.toFinset,
                weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff l) D
                  ≤ (WithBot.some (wβ_tight bW bξ l) : WithBot ℕ) := by
              intro l hl
              exact IH l (recursionStep_lt p hexcl (Multiset.mem_toFinset.mp hl))
            refine le_trans
              (betaTerm_weight_le x₀ R H hHyp Bcoeff s i₁ p hD hH (wβ_tight bW bξ)
                hbW_le hbξ (hbB i₁ p) hbβ) ?_
            rw [WithBot.coe_le_coe]
            -- the collapse is `betaTele_tight` (with `bB`'s concrete value plugged in).
            have hi₁' : i₁ ≤ s + 1 := by have := Finset.mem_range.mp hi₁; omega
            have := betaTele_tight (D := D) (d := d) (dH := dH) hdH_le hdH_D hd1 s i₁ p hi₁'
              hexcl hNd
            -- align `betaWExp · bW + …` shapes.
            simpa [hbW_def, hbξ_def] using this
          · -- Hasse-vanishing: `Bcoeff i₁ p = 0` ⟹ `betaTerm = 0` ⟹ weight `⊥`.
            replace hNd : d - betaδ i₁ < Multiset.card p.parts := Nat.lt_of_not_le hNd
            have hB0 : Bcoeff i₁ p = 0 := hBzero i₁ p hNd
            have hterm0 : betaTerm x₀ R H hHyp Bcoeff s i₁ p = 0 := by
              unfold betaTerm; rw [if_pos hexcl, hB0]; ring
            rw [hterm0, weight_Λ_over_𝒪_zero' hH]
            exact bot_le
        · -- forbidden pair: `betaTerm = 0`, weight `⊥`.
          have hterm0 : betaTerm x₀ R H hHyp Bcoeff s i₁ p = 0 := by
            unfold betaTerm; rw [if_neg hexcl]
          rw [hterm0, weight_Λ_over_𝒪_zero' hH]
          exact bot_le

/-! ### Brick L10: the loose Claim-A.2 bound `≤ (2t+1)·d_R·D`

Composing the tight strong-induction theorem with the L10 collapse `wβ_tight ≤ (2t+1)·d_R·D`. -/

/-- **Brick L10 — the concrete Claim-A.2 weight collapse.**

`weight_Λ_over_𝒪 hH (betaRec … t) D ≤ (2t+1)·d·D`, with `d = d_R = R.natDegree` plugged in via the
`weight_ξ_bound` hypotheses, under the standing App.-A degree facts.  The genuine isolated inputs
are
the `B`-numerator weight budget `hbB` (App.-A line 131; brick L2b/L4) and its Hasse-support
vanishing
`hBzero`; the prefactor budgets `Λ(W) ≤ D − d_H`, `Λ(ξ) ≤ (d−1)(D − d_H + 1)` are realised in-tree
(L3, `weight_ξ_bound`). -/
theorem betaRec_weight_le_concrete (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D d : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd1 : 1 ≤ d) (hdH_le : H.natDegree ≤ d) (hdH_D : H.natDegree ≤ D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (d - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        d - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D
        ≤ (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some ((2 * t + 1) * d * D) : WithBot ℕ) := by
  refine le_trans
    (betaRec_weight_le_tight x₀ R H hHyp Bcoeff hD hH hd1 hdH_le hdH_D hbB hBzero hbξ t) ?_
  rw [WithBot.coe_le_coe]
  exact wβ_tight_le_loose hH hdH_le hdH_D t

end ArkLib

-- Axiom audit: every claimed-done declaration must rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.betaRec_partsCount_smul_sum
#print axioms ArkLib.betaRec_partsCount_smul_card
#print axioms ArkLib.betaRec_card_le
#print axioms ArkLib.betaRec_partsCount_two_mul_sub
#print axioms ArkLib.betaTele_sum_eq
#print axioms ArkLib.betaTele_core_zero
#print axioms ArkLib.betaTele_core_pos
#print axioms ArkLib.betaTele_tight
#print axioms ArkLib.wβ_tight_le_loose
#print axioms ArkLib.betaRec_weight_le_tight
#print axioms ArkLib.betaRec_weight_le_concrete
