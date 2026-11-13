/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The unconditional Chebyshev tail floor (#444)

The conditional chain (`_AvW5`–`_AvW8`) needs a **sub-Gaussian** tail
`#{b : ‖η_b‖ > T} ≤ q·e^{-cT²/n}` — the open Paley/BGK input. This file proves, *unconditionally*,
the strongest tail that follows from Parseval alone (`Σ_{b≠0}‖η_b‖² = qn − n²`, the in-tree
`nonzero_spectral_mass`): the **Markov/Chebyshev tail** `#{b : ‖η_b‖² > T²} ≤ (qn − n²)/T²` — a
*polynomial* `T^{-2}` tail, with no conjecture.

Recorded to **delineate proven from open**: the unconditional floor gives only `M ≤ √(qn)`
(`≈ n^{2.5}` at `β=4`, above even the trivial `M ≤ n` — Parseval alone says nothing useful about the
max), whereas the prize needs the sub-Gaussian tail (`M ≤ √(n log q)`). The entire content of the
Paley conjecture is upgrading this **polynomial** `T^{-2}` decay to **Gaussian** `e^{-cT²/n}` decay —
exactly the gap `_AvW5`–`_AvW8` reduce the prize to. No fixed-order moment closes it (each gives a
fixed polynomial tail; only `r ≈ log q` reaches Gaussian, and there the energy diverges,
`K_max~n^{0.77}`).

## Honest scope
PROVEN: the abstract Markov tail and its Parseval specialization (axiom-clean). The unconditional
baseline, NOT the prize — it makes explicit that the open core is precisely the polynomial→Gaussian
tail upgrade. NOT closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW9

open Finset

/-- **Markov's inequality, counting form (proven).** For nonnegative `a : ι → ℝ` over a finite set
`s` with total mass `Σ a ≤ S`, and any `T2 > 0`, the number of indices with `a i > T2` is at most
`S / T2`. -/
theorem count_large_le_of_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (S T2 : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hsum : ∑ i ∈ s, a i ≤ S) (hT2 : 0 < T2) :
    ((s.filter (fun i => T2 < a i)).card : ℝ) ≤ S / T2 := by
  set B := s.filter (fun i => T2 < a i) with hB
  have hBsub : B ⊆ s := filter_subset _ _
  -- mass on B alone is ≥ |B|·T2 (each entry exceeds T2)
  have hmassB : (B.card : ℝ) * T2 ≤ ∑ i ∈ B, a i := by
    have hconst : ∑ _i ∈ B, T2 ≤ ∑ i ∈ B, a i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (Finset.mem_filter.mp hi).2
    rwa [Finset.sum_const, nsmul_eq_mul] at hconst
  -- mass on B ≤ total mass ≤ S
  have hBs : ∑ i ∈ B, a i ≤ ∑ i ∈ s, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun i hi _ => ha i hi)
  have hkey : (B.card : ℝ) * T2 ≤ S := le_trans hmassB (le_trans hBs hsum)
  rw [le_div_iff₀ hT2]
  linarith [hkey]

/-- **The Parseval/Chebyshev tail floor (proven specialization).** With `a b = ‖η_b‖²`, total
spectral mass `Σ_{b≠0}‖η_b‖² = q·n − n²` (Parseval, DC-subtracted), the number of nonzero
frequencies whose squared period exceeds `T²` is `≤ (q·n − n²)/T²`. Stated abstractly via the mass
identity as hypothesis (the in-tree `nonzero_spectral_mass` supplies it). This is the **polynomial**
unconditional tail — the floor the Paley conjecture must improve to `e^{-cT²/n}`. -/
theorem parseval_chebyshev_floor {ι : Type*} (s : Finset ι) (etaSq : ι → ℝ) (q n T2 : ℝ)
    (hnn : ∀ b ∈ s, 0 ≤ etaSq b)
    (hmass : ∑ b ∈ s, etaSq b = q * n - n ^ 2)
    (hT2 : 0 < T2) :
    ((s.filter (fun b => T2 < etaSq b)).card : ℝ) ≤ (q * n - n ^ 2) / T2 :=
  count_large_le_of_sum s etaSq (q * n - n ^ 2) T2 hnn (le_of_eq hmass) hT2

/-- **The gap, made explicit (proven inequality between the two tails).** At any threshold
`T2 = K·n` (a constant multiple of the average `≈ n`), the proven Chebyshev floor bounds the
exceedance fraction by `(q·n)/(K·n)/q = 1/K` of all `q` frequencies — only an inverse-linear
suppression. The Paley conjecture asserts the far stronger `e^{-cK}` suppression at the same
threshold. This lemma proves the floor side: `#{b : ‖η_b‖² > K·n} ≤ q/K` (taking `n ≤ q`). -/
theorem chebyshev_fraction_bound {ι : Type*} (s : Finset ι) (etaSq : ι → ℝ) (q n K : ℝ)
    (hnn : ∀ b ∈ s, 0 ≤ etaSq b)
    (hmass : ∑ b ∈ s, etaSq b = q * n - n ^ 2)
    (hn : 0 < n) (hK : 0 < K) :
    ((s.filter (fun b => K * n < etaSq b)).card : ℝ) ≤ q / K := by
  have hT2 : 0 < K * n := mul_pos hK hn
  have h := parseval_chebyshev_floor s etaSq q n (K * n) hnn hmass hT2
  have hnum : q * n - n ^ 2 ≤ q * n := by nlinarith [sq_nonneg n]
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hK0 : K ≠ 0 := ne_of_gt hK
  calc ((s.filter (fun b => K * n < etaSq b)).card : ℝ)
      ≤ (q * n - n ^ 2) / (K * n) := h
    _ ≤ (q * n) / (K * n) := by gcongr
    _ = q / K := by field_simp

end ArkLib.ProximityGap.Frontier.AvW9

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW9.count_large_le_of_sum
#print axioms ArkLib.ProximityGap.Frontier.AvW9.parseval_chebyshev_floor
#print axioms ArkLib.ProximityGap.Frontier.AvW9.chebyshev_fraction_bound
