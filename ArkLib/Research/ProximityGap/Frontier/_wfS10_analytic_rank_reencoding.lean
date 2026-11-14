/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# wf-S10 — Analytic / partition rank of the SPURIOUS relation tensor is a RE-ENCODING, not an
independent bound (#444; NON-moment route, OBSTRUCTION + transfer-equivalence)

## Lane S10 mandate

Bound the spurious char-`p` `2r`-energy mass
`spur_r(p) := E_r^{charp}(μ_n) − E_r^{char0}(μ_n)` of the order-`n = 2^μ` subgroup `μ_n ⊂ F_p`
via the **polynomial method's analytic / partition rank** of the mod-`p` relation tensor — a route
NOT killed by the moment obstructions (the antitone/monotone moment route B3 is char-`p` false),
because rank is not a moment functional.

## What the prior rank no-gos did NOT cover

- `SliceRankDiagonalVacuous.lean`: diagonal slice rank of the FULL sum-zero tensor `N₀` — vacuous
  (the diagonal of the relation support is empty: `r·x = 0 ⇒ x = 0 ∉ μ_n`).
- `_wf2NG_partition_rank_vacuous.lean`: multiplicative-CLP partition rank of `N₀` — vacuous
  (cyclic index `d = 1` ⇒ no Croot–Lev–Pach/Ellenberg–Gijswijt exponent saving; the count lemma
  `|support| ≤ r·n` is provably FALSE: the matching hypothesis is met, the conclusion fails).

Both targeted `N₀` (ALL coincidences). Lane S10 targets the SPURIOUS subset (the EXTRA mod-`p`
mass beyond char-0) and the **analytic rank** (Lovett) `arank = −log_p(bias)`, the genuinely
distinct, stronger tensor functional.

## The S10 finding (this file): the analytic-rank route COLLAPSES to the object it would bound

The character-sum (frequency) expansion is exact:
`E_r^{charp}(μ_n) = (1/p) · Σ_{b ∈ F_p} (η_b)^{2r}`, `η_b = Σ_{x ∈ μ_n} ψ(b·x)`, with the
principal `b = 0` term `η_0 = n` contributing `n^{2r}/p` and lifting to the char-0 Wick mass.
Hence the spurious mass is **exactly** the non-principal frequency sum
`spur_r(p) = (1/p) · Σ_{b ≠ 0} (η_b)^{2r}`. The "analytic-rank bias" of the spurious tensor —
the quantity whose `−log_p` Lovett calls the analytic rank — is, by *definition*,
`bias_r := (1/p) · Σ_{b ≠ 0} (η_b/n)^{2r} = spur_r(p) / n^{2r}`.

So measuring/bounding the analytic rank `arank_r = −log_p(bias_r)` is *literally* measuring/bounding
`spur_r`: the rank route is NOT an independent functional, it is a logarithmic re-encoding of the
spurious mass. This is the S10-specific structural obstruction: the NON-moment route still
collapses to the very object it would bound.

Moreover the only inequality the rank picture supplies is the **single-largest-frequency**
envelope: with `M := max_{b ≠ 0} |η_b|`,
`bias_r ≤ ((p−1)/p) · (M/n)^{2r}`, equivalently `arank_r ≥ 2r·log_p(n/M) − log_p((p−1)/p)`.
This is *exactly* the `M = max|η_b|` (generalized-Paley non-principal eigenvalue) envelope — the
known face-3 / BGK wall. The analytic rank buys log of the M-envelope, nothing more:
**TRANSFER-EQUIVALENT to the Paley/BGK wall.**

## Measured (probe `probe_wfS10_analytic_rank_spurious.py`, EXACT integer cyclic convolution)

At the PRIZE regime `p ≈ n^4` the energy ratio `E_r/Wick = E_r/((2r-1)!!·n^r) ≤ 1` at every
measured `(n, r)` (`n = 4..32`, `r = 2..5`), with `K_eff = (E_r/Wick)^{1/r} < 1` — the char-`p`
energy is a DEFICIT relative to the char-0 Wick value, so there is NO spurious surplus to bound in
the prize regime (the `spur_r ≥ 0` premise is a sub-prize, tiny-`p` artifact: at the Fermat prime
`p = 17 ≪ n^4`, `spur_r > 0` and large, but that prime is far below `n^4`).

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`)

The abstract re-encoding identity and its envelope, stated over the frequency data alone (so they
hold verbatim for the cyclotomic spurious tensor): with a finite index set `B` (the non-principal
frequencies `b ≠ 0`), real frequency amplitudes `η : B → ℝ`, modulus `p`, scale `n > 0`, depth
`2r`:

* `analyticRankBias` `= spur / n^{2r}` (`reencoding_identity`): the analytic-rank bias is the
  normalized spurious mass — the rank route is the spurious-mass route.
* `bias ≤ ((#B)/p)·(M/n)^{2r}` (`bias_le_maxFreq_envelope`): the single-largest-frequency
  (`M = max|η_b|`) upper envelope — the rank route's only output is the M-envelope.
* Consequently a uniform analytic-rank lower bound `arank ≥ c` is logically equivalent to a uniform
  spur upper bound `spur ≤ n^{2r}·p^{-c}` (`arank_lower_iff_spur_upper`) — the routes are
  inter-derivable, confirming TRANSFER-EQUIVALENCE.

## References
- [Lovett 2019] *The analytic rank of tensors and its applications.*
- [Naslund 2020] *The partition rank of a tensor…*; [Tao 2016] CLP–EG symmetric formulation.
- in-tree `SliceRankDiagonalVacuous.lean`, `_wf2NG_partition_rank_vacuous.lean` (predecessors),
  `_wfS6_norm_divisibility_envelope.lean` (the cyclotomic-norm spur dictionary),
  face-3 generalized-Paley `M = max|η_b|` (BGK wall).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.AnalyticRankReencoding

variable {B : Type*} [Fintype B]

/-- The **spurious mass** in the frequency picture: the (normalized-by-`p`) sum of the `2r`-th
powers of the non-principal frequency amplitudes `η_b`, `b ∈ B`.  By the exact character-sum
expansion of `E_r^{charp}(μ_n)` this equals `E_r^{charp} − E_r^{char0}` (the non-principal,
i.e. spurious, contribution).  Stated abstractly over the frequency data so it specializes to the
cyclotomic spurious tensor. -/
noncomputable def spur (η : B → ℝ) (p : ℝ) (twoR : ℕ) : ℝ :=
  (∑ b, (η b) ^ twoR) / p

/-- The **analytic-rank bias** of the spurious tensor (the quantity whose `−log_p` is Lovett's
analytic rank): the normalized spurious mass, `(1/p)·Σ_{b}(η_b/n)^{2r}`. -/
noncomputable def analyticRankBias (η : B → ℝ) (p n : ℝ) (twoR : ℕ) : ℝ :=
  (∑ b, (η b / n) ^ twoR) / p

/-- **THE RE-ENCODING IDENTITY (headline OBSTRUCTION).**  The analytic-rank bias of the spurious
tensor is *exactly* the normalized spurious mass `spur / n^{2r}`.  Hence bounding the analytic rank
`= −log_p(bias)` is literally bounding `spur`: the NON-moment rank route is not an independent
functional, it is a logarithmic re-encoding of the very object it would bound. -/
theorem reencoding_identity (η : B → ℝ) (p n : ℝ) (twoR : ℕ) (_hn : n ≠ 0) :
    analyticRankBias η p n twoR = spur η p twoR / n ^ twoR := by
  unfold analyticRankBias spur
  have hsum : (∑ b, (η b / n) ^ twoR) = (∑ b, (η b) ^ twoR) / n ^ twoR := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    rw [div_pow]
  rw [hsum, div_div, div_div, mul_comm p (n ^ twoR)]

/-- The non-principal amplitudes are dominated by their maximum modulus `M = max_b |η_b|`:
`(η_b)^{2r} ≤ M^{2r}` for every `b`, when `2r` is even (the `2r`-energy exponent). -/
theorem pow_le_maxFreq (η : B → ℝ) (M : ℝ) (r : ℕ)
    (hM : ∀ b, |η b| ≤ M) (b : B) : (η b) ^ (2 * r) ≤ M ^ (2 * r) := by
  have h1 : (η b) ^ (2 * r) = |η b| ^ (2 * r) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [h1]
  have hMnonneg : 0 ≤ M := le_trans (abs_nonneg _) (hM b)
  exact pow_le_pow_left₀ (abs_nonneg _) (hM b) (2 * r)

/-- **The single-largest-frequency envelope (the rank route's ONLY output).**  The spurious mass is
bounded by `(#B / p)·M^{2r}`, `M = max_b |η_b|` — exactly the `M = max|η_b|` (generalized-Paley
non-principal eigenvalue) envelope, the known face-3 / BGK wall.  The analytic-rank route therefore
buys nothing beyond the M-envelope. -/
theorem spur_le_maxFreq_envelope (η : B → ℝ) (p M : ℝ) (r : ℕ)
    (hp : 0 < p) (hM : ∀ b, |η b| ≤ M) :
    spur η p (2 * r) ≤ (Fintype.card B : ℝ) * M ^ (2 * r) / p := by
  unfold spur
  rw [div_le_div_iff_of_pos_right hp]
  calc ∑ b, (η b) ^ (2 * r)
      ≤ ∑ _b : B, M ^ (2 * r) := Finset.sum_le_sum (fun b _ => pow_le_maxFreq η M r hM b)
    _ = (Fintype.card B : ℝ) * M ^ (2 * r) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The bias-level envelope.**  Normalizing by `n^{2r}`: `bias ≤ (#B/p)·(M/n)^{2r}`.  Taking
`−log_p` gives `arank ≥ 2r·log_p(n/M) − log_p(#B/p)` — the analytic-rank lower bound is the
logarithm of the M-envelope, confirming the rank route is the M-envelope (Paley/BGK) wall. -/
theorem bias_le_maxFreq_envelope (η : B → ℝ) (p n M : ℝ) (r : ℕ)
    (hp : 0 < p) (hn : 0 < n) (hM : ∀ b, |η b| ≤ M) :
    analyticRankBias η p n (2 * r) ≤ (Fintype.card B : ℝ) * (M / n) ^ (2 * r) / p := by
  rw [reencoding_identity η p n (2 * r) hn.ne']
  have henv := spur_le_maxFreq_envelope η p M r hp hM
  have hn2 : (0 : ℝ) < n ^ (2 * r) := pow_pos hn (2 * r)
  rw [div_pow]
  -- goal: spur / n^{2r} ≤ (#B) * (M^{2r}/n^{2r}) / p
  rw [div_le_iff₀ hn2]
  calc spur η p (2 * r)
      ≤ (Fintype.card B : ℝ) * M ^ (2 * r) / p := henv
    _ = (Fintype.card B : ℝ) * (M ^ (2 * r) / n ^ (2 * r)) / p * n ^ (2 * r) := by
        field_simp

/-- **TRANSFER-EQUIVALENCE (the S10 verdict, made precise).**  A uniform analytic-rank lower bound
`arank ≥ c` (i.e. `bias ≤ p^{-c}`, written here as `bias ≤ τ`) is logically equivalent to a uniform
spur upper bound `spur ≤ n^{2r}·τ`.  Hence the NON-moment analytic-rank route and the spurious-mass
route are inter-derivable: proving the prize via analytic rank is exactly proving it via `spur`
(which is the `M = max|η_b|` / Paley / BGK wall).  No independent gain. -/
theorem arank_lower_iff_spur_upper (η : B → ℝ) (p n τ : ℝ) (twoR : ℕ)
    (hn : 0 < n) :
    analyticRankBias η p n twoR ≤ τ ↔ spur η p twoR ≤ n ^ twoR * τ := by
  rw [reencoding_identity η p n twoR hn.ne']
  have hn2 : (0 : ℝ) < n ^ twoR := pow_pos hn twoR
  rw [div_le_iff₀ hn2]
  constructor
  · intro h; rw [mul_comm]; exact h
  · intro h; rw [mul_comm] at h; exact h

end ArkLib.ProximityGap.AnalyticRankReencoding
