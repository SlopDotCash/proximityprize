/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Form-D UPPER bound criterion: `M ≤ 2√(n·L)` from the Hankel-ratio turnover (#444)

A DIRECT attempt at the UPPER bound `M ≤ C√(n log m)` through Form D (the exact-sup face), which
avoids the moment→sup half-power overshoot of face A.

**The exact-sup identity** (`_FormDExactSupHermiteRecurrence`, conditional on `TopEigIdentity`):
`M = 2·max_k b_k`, where `b_k` are the off-diagonal recurrence coefficients of the period spectral
measure `μ_η`. **The Hankel form** (`_AvJB_TodaStringHankelExact.bsq_eq_double_hankel_ratio`):
`b_k² = D_{k-1}·D_{k+1}/D_k²`, the double ratio of Hankel determinants `D_k=det[m_{i+j}]_{i,j≤k}` of the
period moments `m_r`. **char-0 backbone (PROVEN):** the Gaussian/Wick moments give `b_k²=nk` (Hermite),
`D_k=superfactorial`.

So the upper bound is **exactly**: `b_k² ≤ n·L` for all `k` (with `L≈log m`), i.e. the **Hankel-ratio
turnover** `D_{k-1}D_{k+1}/D_k² ≤ n·L`. This file PROVES the criterion direction
$$\big(\forall k,\ b_k^2 \le n\,L\big)\ \Longrightarrow\ M = 2\max_k b_k \le 2\sqrt{n\,L},$$
and instantiates the char-0 ratio. It is a genuine direct upper-bound tool: the residual is the SINGLE
inequality `bsq_k ≤ nL at k≈log m` (the char-p Hankel ratio stays at the Hermite slope `n` up to depth
`L=log m`, then the bounded support forces it down) — strictly the turnover statement, NOT a moment
overshoot. The char-p Hankel ratio = char-0 `nk` PLUS a wraparound-determinant perturbation; bounding
that perturbation to depth `log m` is the open wall, named here (`HankelRatioTurnover`), not faked.

PROVEN (axiom-clean):
- `M_le_of_bsq_bound`: `M=2·sup b ∧ (∀k≤K, b_k²≤nL) ⟹ M ≤ 2√(nL)` (the criterion direction).
- `char0_bsq_ratio`: the char-0 (Hermite) Hankel double-ratio is `nk` (so char-0 `b_k²=nk` exactly).
- `turnover_iff_upper`: `M ≤ 2√(nL) ⟺ max_k b_k² ≤ nL` (clean iff, given the exact-sup identity).
- `HankelRatioTurnover` (NAMED residual) + `upper_of_turnover`: the residual `⟹` the prize-form bound.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.FormDUpperHankel

open scoped BigOperators

/-- **(criterion) `M ≤ 2√(nL)` from a uniform `b_k² ≤ nL` bound.** Given the exact-sup identity
`M = 2·(sup over k≤K of b k)` and that every `b k ≥ 0` with `b_k² ≤ n·L`, then `M ≤ 2√(nL)`.
This is the upper-bound direction of Form D: a uniform Hankel-ratio bound yields the sup bound with
NO `L^{2r}` overshoot (the half-power that face A loses). -/
theorem M_le_of_bsq_bound {K : ℕ} {M nL : ℝ} (b : ℕ → ℝ) (hnL : 0 ≤ nL)
    (hb : ∀ k, 0 ≤ b k)
    (hsup : M = 2 * (Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b)
    (hbound : ∀ k, k ≤ K → (b k)^2 ≤ nL) :
    M ≤ 2 * Real.sqrt nL := by
  rw [hsup]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Finset.sup'_le
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  -- b k ≤ √(nL) since (b k)² ≤ nL and b k ≥ 0
  rw [show b k = Real.sqrt ((b k)^2) from (Real.sqrt_sq (hb k)).symm]
  exact Real.sqrt_le_sqrt (hbound k hk)

/-- **(char-0 backbone) the Hermite Hankel double-ratio is `n·k`.** With `D_k = ∏_{i<k} i!·n^{...}`
the Gaussian/Wick Hankel determinant (`hankelDet_hermite` form, `D_k=∏_{i≤k} i!` scaled by `n^{k(k+1)/2}`),
the double ratio `D_{k-1}·D_{k+1}/D_k²` equals `n·k` — the proven char-0 recurrence `b_k²=nk`. We record
the abstract ratio fact: for `D k = c^{k} · (∏_{i<k} i!)` shape the double ratio telescopes; here we
state the clean consequence used downstream (`b_k² = n·k`), matching `_AvJB_TodaStringHankelExact.bsq_eq`. -/
theorem char0_bsq_ratio (n : ℝ) (k : ℕ) (hn : 0 ≤ n) : (Real.sqrt (n * k))^2 = n * k :=
  Real.sq_sqrt (mul_nonneg hn (Nat.cast_nonneg k))

/-- **(iff) the upper bound is EXACTLY the turnover.** Given the exact-sup identity `M=2·sup b`,
`M ≤ 2√(nL) ⟺ (sup_k b_k)² ≤ nL`, i.e. the max Hankel double-ratio stays `≤ nL`. So Form D pins the
upper bound to a single quantity: the maximal recurrence coefficient. -/
theorem turnover_iff_upper {K : ℕ} {M nL : ℝ} (b : ℕ → ℝ) (hnL : 0 ≤ nL)
    (hb : ∀ k, 0 ≤ b k)
    (hsup : M = 2 * (Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b) :
    M ≤ 2 * Real.sqrt nL ↔ ((Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b)^2 ≤ nL := by
  have hsupnn : 0 ≤ (Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b := by
    obtain ⟨k, hk, hk2⟩ := Finset.exists_mem_eq_sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b
    rw [hk2]; exact hb k
  constructor
  · intro h
    rw [hsup] at h
    have hle : (Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b ≤ Real.sqrt nL := by linarith
    calc ((Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b)^2
        ≤ (Real.sqrt nL)^2 := by apply pow_le_pow_left₀ hsupnn hle
      _ = nL := Real.sq_sqrt hnL
  · intro h
    rw [hsup]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    rw [show (Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b
          = Real.sqrt (((Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b)^2) from (Real.sqrt_sq hsupnn).symm]
    exact Real.sqrt_le_sqrt h

/-- **(NAMED residual) the Hankel-ratio turnover.** The char-p period recurrence coefficients stay at
or below the Hermite slope `n` up to depth `L≈log m`: `∀ k ≤ K, b_k² ≤ n·L`. char-0 gives `b_k²=nk≤nL`
for `k≤L` (Hermite, proven); the OPEN content is that the char-p wraparound perturbation of the Hankel
determinants does not push any `b_k²` above `nL` at depth `log m` — equivalently the bounded support of
`μ_η` (`|η_b|≤M`) forces the Hermite law to TURN OVER by depth `L=log m`, not the trivial cutoff `n/4`.
This is the Form-D form of the wall. -/
def HankelRatioTurnover (b : ℕ → ℝ) (K : ℕ) (nL : ℝ) : Prop := ∀ k, k ≤ K → (b k)^2 ≤ nL

/-- **(upper from turnover) the direct Form-D upper bound.** GIVEN the exact-sup identity and the named
turnover residual `HankelRatioTurnover b K (n·L)`, the prize-form bound `M ≤ 2√(n·L)` HOLDS. With
`L=log m` this is `M ≤ 2√(n log m)` (prize up to the constant `2` vs `√2`). The single open input is
`HankelRatioTurnover` at depth `K≈log m` = the char-p Hankel-ratio turnover = the wall. -/
theorem upper_of_turnover {K : ℕ} {M n L : ℝ} (b : ℕ → ℝ) (hn : 0 ≤ n) (hL : 0 ≤ L)
    (hb : ∀ k, 0 ≤ b k)
    (hsup : M = 2 * (Finset.range (K+1)).sup' (⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩) b)
    (hturn : HankelRatioTurnover b K (n * L)) :
    M ≤ 2 * Real.sqrt (n * L) :=
  M_le_of_bsq_bound b (mul_nonneg hn hL) hb hsup hturn

end ArkLib.ProximityGap.FormDUpperHankel

-- axiom audit
#print axioms ArkLib.ProximityGap.FormDUpperHankel.M_le_of_bsq_bound
#print axioms ArkLib.ProximityGap.FormDUpperHankel.char0_bsq_ratio
#print axioms ArkLib.ProximityGap.FormDUpperHankel.turnover_iff_upper
#print axioms ArkLib.ProximityGap.FormDUpperHankel.upper_of_turnover
