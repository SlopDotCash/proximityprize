/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors

/-! # Sharp Kopparty–Sha Appendix A / core-weighted ordinary mixed-Hasse obstruction at both
second-prime Johnson pivots

`SecondPrimeJohnsonPivot` reduces the side of Johnson for the second-prime MCA supremum at
rate `1/2` and rate `1/4` to the single closed error counts `314,491,699` and `536,870,913`
at length `n = 2^30`, with agreement counts `t = 759,250,125` (`t² - n d = 1,082,833,961`) and
`t = 536,870,911` (`t² - n d = 1`).

A natural strategy to recover ordinary mixed-Hasse interpolation room near Johnson is
Kopparty–Sha's Appendix A factored-surface / core-weighted interpolation (`P = (Y - h)^K Q`),
which lowers the site jet multiplicity from `r` to `r - K` on a heavy head's joint core `U`
while reducing the weighted-degree cap from `r t` to `r t - d K`.

This module proves **exact, sharp obstruction theorems** for that strategy at both pivots:

1. **MCA fresh-agreement head cap (`mcaEvent_fresh_site_of_head`, `mcaEvent_head_budget_le`):**
   Every MCA-bad scalar `γ` witnessed by an affine head `v₀ + γ • v₁` with joint core `U`
   (`|U| = H`) requires at least one fresh agreement site outside `U`, capping that head's
   MCA bad-scalar contribution by `n - H`. In particular, super-threshold heads (`H > t`)
   shrink their own MCA budget below `e = n - t`, while the canonical no-CA regime satisfies
   `H ≤ t - 1`.
2. **Universal multi-core continuous obstruction (`kopparty_sha_multicore_continuous_obstruction`):**
   For any `n, d, t, r, K, H` with `0 < d`, `t² ≥ n d`, `0 ≤ H ≤ t`, and `d K ≤ r t`,
   the exact sum-of-squares identity
   ```
   t * (2 d n r (t - H) - d K (n d - H²)) ≥ r * ((t H - n d)² + n d (t² - n d)) ≥ 0
   ```
   proves `n (r t - d K)² - d (n r - K H)² ≤ n r² (t² - n d)`, with strict loss whenever
   `K > 0` and `(t² > n d ∨ H < t)`. No multi-core drop on cores of size `≤ t` improves the
   asymptotic quadratic room.
3. **Exact discrete single-core factored-surface obstruction (`factored_pivot_no_room`):**
   For any baseline multiplicity `r`, any Kopparty–Sha drop `0 ≤ K ≤ r` on a core `U ⊆ I`
   of size `|U| ≤ t`, and ANY cutoffs `s, v : ℕ`, whenever `4 r² δ + d² ≤ 4 r d (n - t)`
   and `d² ≤ t (n + 3 d - 3 t)`, the exact `HalfSuccessorJetInterpolation.exists_order_surface`
   dimension test fails:
   ```
   columnCount s v d (r * t - d * K) ≤ ∑ x : I, rowCount s (if x ∈ U then r - K else r).
   ```
   Moreover, completing the square directly in `l` sharpens the uniform (`K = 0`) no-room
   radius by `√2×` at half rate and `2×` at quarter rate:
   * **Half-rate pivot (`314,491,699`):** `half_pivot_factored_no_room` eliminates EVERY
     `r ≤ 155,925,516` and every `0 ≤ K ≤ r` (exact sharp endpoint: `155,925,517` crosses).
   * **Quarter-rate pivot (`536,870,913`):** `quarter_pivot_factored_no_room` eliminates EVERY
     `r ≤ 144,115,187,807,420,414` and every `0 ≤ K ≤ r` (exact sharp endpoint: `+1` crosses).
4. **Budget-overflow corollaries (`quarter_factored_scalar_overflow`,
   `half_factored_two_surface_overflow`):** At both pivots, any constructible single-core
   factored ordinary mixed-Hasse surface with `|U| ≤ t` overflows the `2^31` second-prime
   budget (scalar degree `> 2^31` at quarter rate; two-surface resultant `s₁ v₂ > 2^31` at
   half rate). Breaking either pivot therefore genuinely requires higher-order (differential /
   hidden-derivative) interpolation beyond ordinary mixed-Hasse surfaces.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.PivotFactoredObstruction

open Finset HalfSuccessorJetInterpolation SecondPrimeQuarticInterpolation

/-! ## Part 1: MCA fresh-agreement head cap -/

section HeadCap

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- Joint core of an affine head `(v₀, v₁)` against a received pair `(u₀, u₁)`. -/
def jointCore (u₀ u₁ v₀ v₁ : ι → F) : Finset ι :=
  Finset.univ.filter fun i => v₀ i = u₀ i ∧ v₁ i = u₁ i

omit [DecidableEq ι] in
/-- An MCA-bad witness `S` carried by the affine head `v₀ + γ • v₁` must contain at least
one fresh agreement site `i ∈ S \ U` outside the joint core `U`. -/
theorem mcaEvent_fresh_site_of_head (C : Set (ι → F)) (u₀ u₁ v₀ v₁ : ι → F)
    (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C) (S : Finset ι) (γ : F)
    (hag : ∀ i ∈ S, (v₀ + γ • v₁) i = u₀ i + γ • u₁ i)
    (hno : ¬ ProximityGap.pairJointAgreesOn C S u₀ u₁) :
    ∃ i ∈ S, i ∉ jointCore u₀ u₁ v₀ v₁ ∧
      v₁ i ≠ u₁ i ∧ γ = -(v₀ i - u₀ i) / (v₁ i - u₁ i) := by
  have hnot_sub : ¬ S ⊆ jointCore u₀ u₁ v₀ v₁ := by
    intro hsub
    apply hno
    refine ⟨v₀, hv₀, v₁, hv₁, fun i hi => ?_⟩
    have hm := Finset.mem_filter.mp (hsub hi)
    exact hm.2
  obtain ⟨i, hiS, hiU⟩ := Finset.not_subset.mp hnot_sub
  have heq : v₀ i + γ * v₁ i = u₀ i + γ * u₁ i := by
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hag i hiS
  have hlin : (v₀ i - u₀ i) + γ * (v₁ i - u₁ i) = 0 := by linear_combination heq
  have hv1_ne : v₁ i ≠ u₁ i := by
    intro h1
    have h0 : v₀ i = u₀ i := by
      have : v₀ i - u₀ i = 0 := by
        rw [h1, sub_self, mul_zero, add_zero] at hlin
        exact hlin
      exact sub_eq_zero.mp this
    exact hiU (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h0, h1⟩)
  have hsub_ne : v₁ i - u₁ i ≠ 0 := sub_ne_zero.mpr hv1_ne
  refine ⟨i, hiS, hiU, hv1_ne, ?_⟩
  rw [eq_div_iff hsub_ne]
  linear_combination hlin

/-- The set of MCA-bad scalars witnessed by a single affine head `(v₀, v₁)` has cardinality
at most `|ι| - |jointCore u₀ u₁ v₀ v₁|`: each site outside the joint core pins at most one
fresh scalar. In particular, any super-threshold head (`|U| ≥ t`) contributes at most `n - |U| ≤ e`
bad scalars, and strictly shrinks as `|U|` grows past `t`. -/
theorem mcaEvent_head_budget_le (C : Set (ι → F)) (u₀ u₁ v₀ v₁ : ι → F)
    (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C) (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ S : Finset ι,
      (∀ i ∈ S, (v₀ + γ • v₁) i = u₀ i + γ • u₁ i) ∧
      ¬ ProximityGap.pairJointAgreesOn C S u₀ u₁) :
    G.card ≤ Fintype.card ι - (jointCore u₀ u₁ v₀ v₁).card := by
  let U := jointCore u₀ u₁ v₀ v₁
  let phi : ι → F := fun i => -(v₀ i - u₀ i) / (v₁ i - u₁ i)
  have hsub : G ⊆ (Finset.univ \ U).image phi := by
    intro γ hγ
    obtain ⟨S, hag, hno⟩ := hG γ hγ
    obtain ⟨i, _, hiU, _, hγeq⟩ := mcaEvent_fresh_site_of_head C u₀ u₁ v₀ v₁ hv₀ hv₁ S γ hag hno
    exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiU⟩, hγeq.symm⟩
  calc G.card ≤ ((Finset.univ \ U).image phi).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ \ U).card := Finset.card_image_le
    _ = Fintype.card ι - U.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]

end HeadCap

/-! ## Part 2: Universal multi-core continuous Kopparty–Sha Appendix A obstruction -/

/-- Exact universal algebraic identity comparing factored/core-weighted quadratic room against
uniform quadratic room:
`n (r t - d K)² - d (n r - K H)² = n r² (t² - n d) + 2 d n r K (H - t) - d K² (H² - n d)`. -/
theorem kopparty_sha_quadratic_identity (n d t r K H : ℤ) :
    n * (r * t - d * K) ^ 2 - d * (n * r - K * H) ^ 2 =
      n * r ^ 2 * (t ^ 2 - n * d) + 2 * d * n * r * K * (H - t) - d * K ^ 2 * (H ^ 2 - n * d) := by
  ring

/-- Universal multi-core continuous Kopparty–Sha Appendix A obstruction: for ANY positive
parameters with `t² ≥ n d`, any cap `0 ≤ H ≤ t` on the joint core sizes, and any total
multiplicity drop `K ≥ 0` with `d K ≤ r t`, lowering site multiplicities on cores of size `≤ H`
cannot increase the quadratic interpolation room above the uniform (`K = 0`) room `n r² (t² - n d)`.
Moreover, the loss is strict whenever `K > 0` and `(t² > n d ∨ H < t)`. -/
theorem kopparty_sha_multicore_continuous_obstruction {n d t r K H : ℤ}
    (hn : 0 ≤ n) (hd : 0 < d) (ht : 0 < t) (hr : 0 < r) (hK : 0 ≤ K) (hHt : H ≤ t)
    (hJ : n * d ≤ t ^ 2) (hW : d * K ≤ r * t) :
    n * (r * t - d * K) ^ 2 - d * (n * r - K * H) ^ 2 ≤ n * r ^ 2 * (t ^ 2 - n * d) := by
  rw [kopparty_sha_quadratic_identity]
  suffices h : 0 ≤ d * K * (2 * n * r * (t - H) + K * (H ^ 2 - n * d)) by linarith
  apply mul_nonneg (mul_nonneg hd.le hK)
  by_cases hHsq : n * d ≤ H ^ 2
  · have h1 : 0 ≤ 2 * n * r * (t - H) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn) hr.le) (sub_nonneg.mpr hHt)
    have h2 : 0 ≤ K * (H ^ 2 - n * d) := mul_nonneg hK (sub_nonneg.mpr hHsq)
    linarith
  · push Not at hHsq
    have hpos : 0 < n * d - H ^ 2 := sub_pos.mpr hHsq
    have hmul : d * K * (n * d - H ^ 2) ≤ r * t * (n * d - H ^ 2) :=
      mul_le_mul_of_nonneg_right hW hpos.le
    have hsos : t * (t * H ^ 2 - 2 * n * d * H + n * d * t) =
        (t * H - n * d) ^ 2 + n * d * (t ^ 2 - n * d) := by ring
    have hnd : 0 ≤ n * d := mul_nonneg hn hd.le
    have hcore_t : 0 ≤ t * (t * H ^ 2 - 2 * n * d * H + n * d * t) := by
      rw [hsos]
      exact add_nonneg (sq_nonneg _) (mul_nonneg hnd (sub_nonneg.mpr hJ))
    have hcore : 0 ≤ t * H ^ 2 - 2 * n * d * H + n * d * t :=
      nonneg_of_mul_nonneg_right hcore_t ht
    have hd_mul : 0 ≤ d * (2 * n * r * (t - H) + K * (H ^ 2 - n * d)) := by
      have hre : d * (2 * n * r * (t - H) + K * (H ^ 2 - n * d)) =
          2 * d * n * r * (t - H) - d * K * (n * d - H ^ 2) := by ring
      rw [hre]
      have hge : r * (t * H ^ 2 - 2 * n * d * H + n * d * t) ≤
          2 * d * n * r * (t - H) - d * K * (n * d - H ^ 2) := by nlinarith
      exact (mul_nonneg hr.le hcore).trans hge
    exact nonneg_of_mul_nonneg_right hd_mul hd

/-- Strict multi-core continuous loss whenever `K > 0` and either `t² > n d` or `H < t`
(with `n > 0`). -/
theorem kopparty_sha_multicore_strict_loss {n d t r K H : ℤ}
    (hn : 0 < n) (hd : 0 < d) (ht : 0 < t) (hr : 0 < r) (hK : 0 < K)
    (hHt : H ≤ t) (hJ : n * d ≤ t ^ 2) (hW : d * K ≤ r * t)
    (hstrict : n * d < t ^ 2 ∨ H < t) :
    n * (r * t - d * K) ^ 2 - d * (n * r - K * H) ^ 2 < n * r ^ 2 * (t ^ 2 - n * d) := by
  rw [kopparty_sha_quadratic_identity]
  suffices h : 0 < d * K * (2 * n * r * (t - H) + K * (H ^ 2 - n * d)) by linarith
  apply mul_pos (mul_pos hd hK)
  by_cases hHsq : n * d ≤ H ^ 2
  · rcases hstrict with hJlt | hHlt
    · by_cases hEq : H = t
      · subst hEq
        have : 0 < K * (H ^ 2 - n * d) := mul_pos hK (sub_pos.mpr hJlt)
        linarith
      · have hHlt' : H < t := lt_of_le_of_ne hHt hEq
        have h1 : 0 < 2 * n * r * (t - H) := by positivity
        have h2 : 0 ≤ K * (H ^ 2 - n * d) := mul_nonneg hK.le (sub_nonneg.mpr hHsq)
        linarith
    · have h1 : 0 < 2 * n * r * (t - H) := by positivity
      have h2 : 0 ≤ K * (H ^ 2 - n * d) := mul_nonneg hK.le (sub_nonneg.mpr hHsq)
      linarith
  · push Not at hHsq
    have hpos : 0 < n * d - H ^ 2 := sub_pos.mpr hHsq
    have hmul : d * K * (n * d - H ^ 2) ≤ r * t * (n * d - H ^ 2) :=
      mul_le_mul_of_nonneg_right hW hpos.le
    have hsos : t * (t * H ^ 2 - 2 * n * d * H + n * d * t) =
        (t * H - n * d) ^ 2 + n * d * (t ^ 2 - n * d) := by ring
    have hnd : 0 < n * d := mul_pos hn hd
    have hcore_t : 0 < t * (t * H ^ 2 - 2 * n * d * H + n * d * t) := by
      rw [hsos]
      rcases hstrict with hJlt | hHlt
      · have : 0 < n * d * (t ^ 2 - n * d) := mul_pos hnd (sub_pos.mpr hJlt)
        nlinarith [sq_nonneg (t * H - n * d)]
      · by_cases hJeq : n * d < t ^ 2
        · have : 0 < n * d * (t ^ 2 - n * d) := mul_pos hnd (sub_pos.mpr hJeq)
          nlinarith [sq_nonneg (t * H - n * d)]
        · have hJt : t ^ 2 = n * d := le_antisymm (not_lt.mp hJeq) hJ
          have hne : t * H - n * d ≠ 0 := by nlinarith
          have : 0 < (t * H - n * d) ^ 2 := sq_pos_of_ne_zero hne
          nlinarith [mul_nonneg hnd.le (sub_nonneg.mpr hJ)]
    have hcore : 0 < t * H ^ 2 - 2 * n * d * H + n * d * t :=
      pos_of_mul_pos_right hcore_t ht.le
    have hd_mul : 0 < d * (2 * n * r * (t - H) + K * (H ^ 2 - n * d)) := by
      have hre : d * (2 * n * r * (t - H) + K * (H ^ 2 - n * d)) =
          2 * d * n * r * (t - H) - d * K * (n * d - H ^ 2) := by ring
      rw [hre]
      have hge : r * (t * H ^ 2 - 2 * n * d * H + n * d * t) ≤
          2 * d * n * r * (t - H) - d * K * (n * d - H ^ 2) := by nlinarith
      exact lt_of_lt_of_le (mul_pos hr hcore) hge
    exact pos_of_mul_pos_right hd_mul hd.le

/-! ## Part 3: Exact discrete Kopparty–Sha Appendix A single-core mixed-Hasse obstruction -/

/-- Exact number of scalar coefficient constraints at a site of multiplicity `r`. -/
def rowCount (s r : ℕ) : ℕ := ∑ j ∈ range r, (r - j) * (s + 1 - j)

theorem card_rows (s r : ℕ) : Fintype.card (JetRows s r) = rowCount s r := by
  simp only [JetRows, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, rowCount]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (r - j) * (s + 1 - j)) r

/-- Exact number of monomials below the strict weighted-degree cap `W`. -/
def columnCount (s b D W : ℕ) : ℕ := ∑ j ∈ range (b + 1), (s + 1 - j) * (W - j * D)

theorem card_columns (s b D W : ℕ) :
    Fintype.card (Monomials s b D W) = columnCount s b D W := by
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, columnCount]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (s + 1 - j) * (W - j * D)) (b + 1)

/-- Single-core Kopparty–Sha site order: multiplicity `r - K` on core `U`, `r` outside `U`. -/
def singleCoreOrder {I : Type*} [DecidableEq I] (U : Finset I) (r K : ℕ) (x : I) : ℕ :=
  if x ∈ U then r - K else r

private theorem linear_sum (k a h : ℕ) (hpos : ∀ j < k, j * h ≤ a) :
    2 * (∑ j ∈ range k, (a - j * h) : ℕ) =
      (k : ℤ) * (2 * (a : ℤ) - (h : ℤ) * ((k : ℤ) - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have prev := ih (fun j hj => hpos j (by omega))
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sub (hpos k (by omega)), Nat.cast_mul,
      Nat.cast_succ]
    linarith

private theorem layer (g : ℕ → ℕ) (s M : ℕ) :
    (∑ j ∈ range M, (s + 1 - j) * g j) = (∑ j ∈ range M, (s - j) * g j) +
      ∑ j ∈ range (min M (s + 1)), g j := by
  have hsplit (j : ℕ) : (s + 1 - j) * g j =
      (s - j) * g j + (if j < s + 1 then g j else 0) := by
    split_ifs with hj
    · rw [show s + 1 - j = (s - j) + 1 by omega, add_mul, one_mul]
    · simp [Nat.sub_eq_zero_of_le (by omega : s + 1 ≤ j),
        Nat.sub_eq_zero_of_le (by omega : s ≤ j)]
  simp_rw [hsplit]
  rw [sum_add_distrib, ← sum_filter]
  have hf : (range M).filter (fun j => j < s + 1) = range (min M (s + 1)) := by
    ext j
    simp [lt_min_iff]
  rw [hf]

/-- Case 1 (full-row prefix `k ≥ r` or arbitrary integer `l`): exact square-completion identity
showing that for `0 ≤ K ≤ r`, `0 ≤ H ≤ t`, and `4 r² δ + d² ≤ 4 r d (n - t)`, the full row
budget `(n - H) r (r + 1) + H (r - K) (r - K + 1)` dominates `2 l (r t - d K) - d l (l - 1)`
for EVERY integer `l`. Note the exact nonpositive `K`-correction `-4 d (t - d) K (K - 1)`. -/
private theorem full_row_core {n d t δ H r K l : ℤ}
    (hd : 0 < d) (htd : d ≤ t) (hK0 : 0 ≤ K) (hKr : K ≤ r) (hHt : H ≤ t)
    (hj : t ^ 2 ≤ n * d + δ) (hcond : 4 * r ^ 2 * δ + d ^ 2 ≤ 4 * r * d * (n - t)) :
    l * (2 * (r * t - d * K) - d * (l - 1)) ≤
      (n - H) * (r * (r + 1)) + H * ((r - K) * (r - K + 1)) := by
  have hmono_H : (n - t) * (r * (r + 1)) + t * ((r - K) * (r - K + 1)) ≤
      (n - H) * (r * (r + 1)) + H * ((r - K) * (r - K + 1)) := by
    have hdiff : ((n - H) * (r * (r + 1)) + H * ((r - K) * (r - K + 1))) -
        ((n - t) * (r * (r + 1)) + t * ((r - K) * (r - K + 1))) =
        (t - H) * (K * (2 * r - K + 1)) := by ring
    have hnn : 0 ≤ (t - H) * (K * (2 * r - K + 1)) :=
      mul_nonneg (by linarith) (mul_nonneg hK0 (by linarith))
    linarith
  suffices h : 0 ≤ 4 * d * ((n - t) * (r * (r + 1)) + t * ((r - K) * (r - K + 1)) -
      l * (2 * (r * t - d * K) - d * (l - 1))) by
    have hle : 0 ≤ (n - t) * (r * (r + 1)) + t * ((r - K) * (r - K + 1)) -
        l * (2 * (r * t - d * K) - d * (l - 1)) :=
      nonneg_of_mul_nonneg_right h (by linarith)
    linarith
  have hid : 4 * d * ((n - t) * (r * (r + 1)) + t * ((r - K) * (r - K + 1)) -
      l * (2 * (r * t - d * K) - d * (l - 1))) =
      (2 * d * l - 2 * (r * t - d * K) - d) ^ 2 +
      (4 * r ^ 2 * (n * d - t ^ 2) + 4 * r * d * (n - t) - d ^ 2) +
      4 * d * (t - d) * (K * (K - 1)) := by ring
  rw [hid]
  have h1 : 0 ≤ (2 * d * l - 2 * (r * t - d * K) - d) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 4 * r ^ 2 * (n * d - t ^ 2) + 4 * r * d * (n - t) - d ^ 2 := by
    have hr2 : 0 ≤ 4 * r ^ 2 := by positivity
    have hdj : -δ ≤ n * d - t ^ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hdj hr2
    linarith
  have h3 : 0 ≤ 4 * d * (t - d) * (K * (K - 1)) := by
    have hKint : 0 ≤ K * (K - 1) := by
      rcases eq_or_lt_of_le hK0 with rfl | hKpos
      · norm_num
      · exact mul_nonneg hK0 (by omega)
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hKint
  linarith

/-- Case 2 (middle prefix `r - K < l ≤ r`): exact positive-definite quadratic identity in
`(u, v', w) = (r - l, l - (r - K) - 1, r - K) ≥ 0`, requiring only `2 t ≤ n + d`,
`d ≤ t ≤ n`, and `d² ≤ t (n + 3 d - 3 t)`. -/
private theorem mid_row_core {n d t H r K l : ℤ}
    (hd : 0 < d) (htd : d ≤ t) (hmean : 2 * t ≤ n + d)
    (hpd : d ^ 2 ≤ t * (n + 3 * d - 3 * t))
    (hKr : K ≤ r) (hHt : H ≤ t) (hlo : r - K < l) (hhi : l ≤ r) :
    l * (2 * (r * t - d * K) - d * (l - 1)) ≤
      (n - H) * (l * (2 * r - l + 1)) + H * ((r - K) * (r - K + 1)) := by
  let u : ℤ := r - l
  let vp : ℤ := l - (r - K) - 1
  let w : ℤ := r - K
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hvp : 0 ≤ vp := by dsimp [vp]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hr_eq : r = u + vp + 1 + w := by dsimp [u, vp, w]; ring
  have hl_eq : l = vp + 1 + w := by dsimp [vp, w]; ring
  have hK_eq : K = u + vp + 1 := by dsimp [u, vp]; ring
  have hmono_H : (n - t) * (l * (2 * r - l + 1)) + t * ((r - K) * (r - K + 1)) ≤
      (n - H) * (l * (2 * r - l + 1)) + H * ((r - K) * (r - K + 1)) := by
    have hdiff : ((n - H) * (l * (2 * r - l + 1)) + H * ((r - K) * (r - K + 1))) -
        ((n - t) * (l * (2 * r - l + 1)) + t * ((r - K) * (r - K + 1))) =
        (t - H) * ((vp + 1) * (2 * u + vp + 1 + 2 * w + 1) + 2 * u * w) := by
      rw [hr_eq, hl_eq, hK_eq]; ring
    have hnn : 0 ≤ (t - H) * ((vp + 1) * (2 * u + vp + 1 + 2 * w + 1) + 2 * u * w) :=
      mul_nonneg (by linarith) (add_nonneg (mul_nonneg (by linarith) (by linarith))
        (mul_nonneg (mul_nonneg (by norm_num) hu) hw))
    linarith
  set A : ℤ := n + 3 * d - 3 * t
  set B : ℤ := n + 2 * d - 3 * t
  set C : ℤ := n + d - 2 * t
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hA : 0 < A := by
    have : 0 < d ^ 2 := sq_pos_of_pos hd
    have : 0 < t * A := lt_of_lt_of_le this hpd
    exact pos_of_mul_pos_right this (by linarith)
  have hdet : 0 ≤ A * C - B ^ 2 := by
    have : A * C - B ^ 2 = t * A - d ^ 2 := by dsimp [A, B, C]; ring
    linarith
  have hquad_pos : 0 ≤ A * vp ^ 2 + 2 * B * vp * w + C * w ^ 2 := by
    have hmul : A * (A * vp ^ 2 + 2 * B * vp * w + C * w ^ 2) =
        (A * vp + B * w) ^ 2 + (A * C - B ^ 2) * w ^ 2 := by ring
    have hnn : 0 ≤ A * (A * vp ^ 2 + 2 * B * vp * w + C * w ^ 2) := by
      rw [hmul]
      exact add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg _))
    exact nonneg_of_mul_nonneg_right hnn hA
  have hgap : (n - t) * (l * (2 * r - l + 1)) + t * ((r - K) * (r - K + 1)) -
      l * (2 * (r * t - d * K) - d * (l - 1)) =
      (A * vp ^ 2 + 2 * B * vp * w + C * w ^ 2) +
      (2 * C + A) * vp + 3 * C * w + 2 * C +
      2 * C * u * (vp + 1 + w) := by
    rw [hr_eq, hl_eq, hK_eq]
    dsimp [A, B, C]
    ring
  have hnonneg : 0 ≤ (n - t) * (l * (2 * r - l + 1)) + t * ((r - K) * (r - K + 1)) -
      l * (2 * (r * t - d * K) - d * (l - 1)) := by
    rw [hgap]
    have t1 : 0 ≤ (2 * C + A) * vp := mul_nonneg (by linarith) hvp
    have t2 : 0 ≤ 3 * C * w := mul_nonneg (by linarith) hw
    have t3 : 0 ≤ 2 * C * u * (vp + 1 + w) :=
      mul_nonneg (mul_nonneg (by linarith) hu) (by linarith)
    linarith
  linarith

/-- Single-layer prefix comparison for a Kopparty–Sha single-core order function `r - K` on
`U` (`|U| = H ≤ t`) and `r` outside `U`. Valid for EVERY prefix length `k : ℕ`. -/
private theorem single_core_prefix_bound {n d t δ H r K : ℕ}
    (hd : 0 < d) (htd : d ≤ t) (htn : t ≤ n) (hmean : 2 * t ≤ n + d)
    (hj : t * t ≤ n * d + δ)
    (hpd : d * d ≤ t * (n + 3 * d - 3 * t))
    (hr : 0 < r) (hKr : K ≤ r) (hHt : H ≤ t)
    (hcond : 4 * r * r * δ + d * d ≤ 4 * r * d * (n - t))
    (k : ℕ) :
    (∑ j ∈ range k, (r * t - d * K - j * d)) ≤
      (n - H) * (∑ j ∈ range k, (r - j)) + H * (∑ j ∈ range k, (r - K - j)) := by
  by_cases hW0 : r * t ≤ d * K
  · have hz : ∑ j ∈ range k, (r * t - d * K - j * d) = 0 :=
      sum_eq_zero fun j _ => by omega
    rw [hz]
    exact Nat.zero_le _
  push Not at hW0
  set W : ℕ := r * t - d * K
  let l : ℕ := min k (W / d + 1)
  have hlk : l ≤ k := min_le_left _ _
  have hlW : ∀ j < l, j * d ≤ W := fun j hj => by
    have : j ≤ W / d := by omega
    exact (Nat.le_div_iff_mul_le hd).1 this
  have hcol_eq : (∑ j ∈ range l, (W - j * d)) = ∑ j ∈ range k, (W - j * d) := by
    apply sum_subset (range_mono hlk)
    intro j hj hm
    simp only [mem_range] at hj hm
    have hdiv : W / d < j := by omega
    exact Nat.sub_eq_zero_of_le ((Nat.div_lt_iff_lt_mul hd).1 hdiv).le
  rw [← hcol_eq]
  have hcol := linear_sum l W d hlW
  have hW_int : (W : ℤ) = (r : ℤ) * t - d * K := by
    dsimp [W]
    rw [Nat.cast_sub hW0.le, Nat.cast_mul, Nat.cast_mul]
  have h3t : 3 * t ≤ n + 3 * d := by
    by_contra! hgt
    have hzero : n + 3 * d - 3 * t = 0 := Nat.sub_eq_zero_of_le hgt.le
    rw [hzero, mul_zero] at hpd
    have : 0 < d * d := Nat.mul_pos hd hd
    omega
  have hpd_int : (d : ℤ) ^ 2 ≤ (t : ℤ) * ((n : ℤ) + 3 * d - 3 * t) := by
    have hnat : ((d * d : ℕ) : ℤ) ≤ ((t * (n + 3 * d - 3 * t) : ℕ) : ℤ) := by exact_mod_cast hpd
    push_cast [Nat.cast_sub h3t] at hnat
    linarith [show (d : ℤ) ^ 2 = (d : ℤ) * d by ring]
  have hcond_int : 4 * (r : ℤ) ^ 2 * δ + (d : ℤ) ^ 2 ≤ 4 * (r : ℤ) * d * ((n : ℤ) - t) := by
    have hnat : ((4 * r * r * δ + d * d : ℕ) : ℤ) ≤ ((4 * r * d * (n - t) : ℕ) : ℤ) := by
      exact_mod_cast hcond
    push_cast [Nat.cast_sub htn] at hnat
    linarith [show 4 * (r : ℤ) ^ 2 * δ + (d : ℤ) ^ 2 = 4 * r * r * δ + d * d by ring]
  have hHn : H ≤ n := hHt.trans htn
  by_cases hlr : r ≤ l
  · have hkr : r ≤ k := hlr.trans hlk
    have hr1 : (∑ j ∈ range r, (r - j)) = ∑ j ∈ range k, (r - j) := by
      apply sum_subset (range_mono hkr)
      intro j _ hm; simp only [mem_range] at hm; omega
    have hr2 : (∑ j ∈ range (r - K), (r - K - j)) = ∑ j ∈ range k, (r - K - j) := by
      apply sum_subset (range_mono (by omega : r - K ≤ k))
      intro j _ hm; simp only [mem_range] at hm; omega
    rw [← hr1, ← hr2]
    have hs1 := linear_sum r r 1 (fun j hj => by simpa using hj.le)
    have hs2 := linear_sum (r - K) (r - K) 1 (fun j hj => by simpa using hj.le)
    simp only [mul_one, Nat.cast_one, one_mul] at hs1 hs2
    have hcore := full_row_core (n := (n : ℤ)) (d := (d : ℤ)) (t := (t : ℤ)) (δ := (δ : ℤ))
      (H := (H : ℤ)) (r := (r : ℤ)) (K := (K : ℤ)) (l := (l : ℤ))
      (by exact_mod_cast hd) (by exact_mod_cast htd) (by positivity) (by exact_mod_cast hKr)
      (by exact_mod_cast hHt) (by
        have : (t : ℤ) * t ≤ n * d + δ := by exact_mod_cast hj
        linarith [show (t : ℤ) ^ 2 = (t : ℤ) * t by ring])
      hcond_int
    have hs1' : 2 * ((∑ j ∈ range r, (r - j) : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) + 1) := by
      linarith only [hs1]
    have hs2' : 2 * ((∑ j ∈ range (r - K), (r - K - j) : ℕ) : ℤ) =
        ((r : ℤ) - K) * ((r : ℤ) - K + 1) := by
      rw [Nat.cast_sub hKr] at hs2
      linarith only [hs2]
    have hcol' : 2 * ((∑ j ∈ range l, (W - j * d) : ℕ) : ℤ) =
        (l : ℤ) * (2 * ((r : ℤ) * t - d * K) - d * ((l : ℤ) - 1)) := by
      rw [hW_int] at hcol
      exact hcol
    zify [hHn]
    simp only [Nat.cast_sum] at hs1' hs2' hcol'
    linarith only [congrArg (fun x : ℤ => ((n : ℤ) - H) * x) hs1',
      congrArg (fun x : ℤ => (H : ℤ) * x) hs2', hcol', hcore]
  · push Not at hlr
    have hmono1 : (∑ j ∈ range l, (r - j)) ≤ ∑ j ∈ range k, (r - j) :=
      sum_le_sum_of_subset_of_nonneg (range_mono hlk) (fun _ _ _ => Nat.zero_le _)
    have hmono2 : (∑ j ∈ range l, (r - K - j)) ≤ ∑ j ∈ range k, (r - K - j) :=
      sum_le_sum_of_subset_of_nonneg (range_mono hlk) (fun _ _ _ => Nat.zero_le _)
    suffices h : (∑ j ∈ range l, (W - j * d)) ≤
        (n - H) * (∑ j ∈ range l, (r - j)) + H * (∑ j ∈ range l, (r - K - j)) by
      exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hmono1) (Nat.mul_le_mul_left _ hmono2))
    by_cases hlo : l ≤ r - K
    · have hs1 := linear_sum l r 1 (fun j hj => by simpa using (by omega : j ≤ r))
      have hs2 := linear_sum l (r - K) 1 (fun j hj => by simpa using (by omega : j ≤ r - K))
      simp only [mul_one, Nat.cast_one, one_mul] at hs1 hs2
      have hcol' : 2 * ((∑ j ∈ range l, (W - j * d) : ℕ) : ℤ) =
          (l : ℤ) * (2 * ((r : ℤ) * t - d * K) - d * ((l : ℤ) - 1)) := by
        rw [hW_int] at hcol; exact hcol
      rw [Nat.cast_sub hKr] at hs2
      rcases eq_or_lt_of_le (Nat.zero_le l) with hl0 | hlpos
      · rw [← hl0]; simp
      · have hlin : 0 ≤ (l : ℤ) * ((n : ℤ) * (2 * r - l + 1) - 2 * H * K -
            (2 * (r * t - d * K) - d * (l - 1))) := by
          apply mul_nonneg (by positivity)
          have h1 : 2 * ((H : ℤ) - d) * K ≤ ((n : ℤ) - d) * K := by
            have : 2 * ((H : ℤ) - d) ≤ (n : ℤ) - d := by omega
            exact mul_le_mul_of_nonneg_right this (by positivity)
          have h2 : ((n : ℤ) - d) * (l + K - 1) ≤ ((n : ℤ) - d) * (r - 1) := by
            have : (l : ℤ) + K - 1 ≤ r - 1 := by omega
            exact mul_le_mul_of_nonneg_left this (by omega)
          have h3 : 0 ≤ (r : ℤ) * ((n : ℤ) + d - 2 * t) + ((n : ℤ) - d) := by
            have : (0 : ℤ) ≤ (r : ℤ) * ((n : ℤ) + d - 2 * t) :=
              mul_nonneg (by positivity) (by omega)
            omega
          linarith only [h1, h2, h3, show ((n : ℤ) - d) * (l + K - 1) =
              ((n : ℤ) - d) * (l - 1) + ((n : ℤ) - d) * K by ring,
            show (n : ℤ) * (2 * r - l + 1) - 2 * H * K - (2 * (r * t - d * K) - d * (l - 1)) =
              (r : ℤ) * (n + d - 2 * t) + (n - d) + ((n - d) * (r - 1) - (n - d) * (l - 1) -
                2 * (H - d) * K) by ring]
        have hcomb : ((n : ℤ) - H) * ((l : ℤ) * (2 * r - (l - 1))) +
            (H : ℤ) * ((l : ℤ) * (2 * (r - K) - (l - 1))) -
            (l : ℤ) * (2 * (r * t - d * K) - d * (l - 1)) =
            (l : ℤ) * ((n : ℤ) * (2 * r - l + 1) - 2 * H * K -
              (2 * (r * t - d * K) - d * (l - 1))) := by ring
        zify [hHn]
        simp only [Nat.cast_sum] at hs1 hs2 hcol'
        linarith only [congrArg (fun x : ℤ => ((n : ℤ) - H) * x) hs1,
          congrArg (fun x : ℤ => (H : ℤ) * x) hs2, hcol', hlin, hcomb]
    · push Not at hlo
      have hr2 : (∑ j ∈ range (r - K), (r - K - j)) = ∑ j ∈ range l, (r - K - j) := by
        apply sum_subset (range_mono hlo.le)
        intro j _ hm; simp only [mem_range] at hm; omega
      rw [← hr2]
      have hs1 := linear_sum l r 1 (fun j hj => by simpa using (by omega : j ≤ r))
      have hs2 := linear_sum (r - K) (r - K) 1 (fun j hj => by simpa using hj.le)
      simp only [mul_one, Nat.cast_one, one_mul] at hs1 hs2
      have hcol' : 2 * ((∑ j ∈ range l, (W - j * d) : ℕ) : ℤ) =
          (l : ℤ) * (2 * ((r : ℤ) * t - d * K) - d * ((l : ℤ) - 1)) := by
        rw [hW_int] at hcol; exact hcol
      have hs1' : 2 * ((∑ j ∈ range l, (r - j) : ℕ) : ℤ) = (l : ℤ) * (2 * r - l + 1) := by
        linarith only [hs1]
      have hs2' : 2 * ((∑ j ∈ range (r - K), (r - K - j) : ℕ) : ℤ) =
          ((r : ℤ) - K) * ((r : ℤ) - K + 1) := by
        rw [Nat.cast_sub hKr] at hs2
        linarith only [hs2]
      have hmid := mid_row_core (n := (n : ℤ)) (d := (d : ℤ)) (t := (t : ℤ)) (H := (H : ℤ))
        (r := (r : ℤ)) (K := (K : ℤ)) (l := (l : ℤ))
        (by exact_mod_cast hd) (by exact_mod_cast htd)
        (by exact_mod_cast hmean) hpd_int (by exact_mod_cast hKr) (by exact_mod_cast hHt)
        (by omega) (by omega)
      zify [hHn]
      simp only [Nat.cast_sum] at hs1' hs2' hcol'
      linarith only [congrArg (fun x : ℤ => ((n : ℤ) - H) * x) hs1',
        congrArg (fun x : ℤ => (H : ℤ) * x) hs2', hcol', hmid]

/-- **Exact discrete Kopparty–Sha Appendix A single-core obstruction.**
For any baseline multiplicity `r > 0`, any Kopparty–Sha drop `K ≤ r` on a core of size `H ≤ t`,
and ANY cutoffs `s, v : ℕ`, whenever `4 r² δ + d² ≤ 4 r d (n - t)` and
`d² ≤ t (n + 3 d - 3 t)`, the factored ordinary mixed-Hasse monomial space has no surplus over
the site-dependent jet-row constraints. -/
theorem factored_pivot_no_room {n d t δ H : ℕ}
    (hd : 0 < d) (htd : d ≤ t) (htn : t ≤ n) (hmean : 2 * t ≤ n + d)
    (hj : t * t ≤ n * d + δ) (hpd : d * d ≤ t * (n + 3 * d - 3 * t))
    (hHt : H ≤ t) (s v r K : ℕ) (hKr : K ≤ r)
    (hcond : 0 < r → 4 * r * r * δ + d * d ≤ 4 * r * d * (n - t)) :
    columnCount s v d (r * t - d * K) ≤ (n - H) * rowCount s r + H * rowCount s (r - K) := by
  have weighted (k : ℕ) :
      (∑ j ∈ range (v + 1), (k - j) * (r * t - d * K - j * d)) ≤
        (n - H) * (∑ j ∈ range r, (k - j) * (r - j)) +
        H * (∑ j ∈ range (r - K), (k - j) * (r - K - j)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [layer, layer, layer, mul_add, mul_add]
      have hre : (n - H) * (∑ j ∈ range r, (k - j) * (r - j)) +
          (n - H) * (∑ j ∈ range (min r (k + 1)), (r - j)) +
          (H * (∑ j ∈ range (r - K), (k - j) * (r - K - j)) +
          H * (∑ j ∈ range (min (r - K) (k + 1)), (r - K - j))) =
          ((n - H) * (∑ j ∈ range r, (k - j) * (r - j)) +
          H * (∑ j ∈ range (r - K), (k - j) * (r - K - j))) +
          ((n - H) * (∑ j ∈ range (min r (k + 1)), (r - j)) +
          H * (∑ j ∈ range (min (r - K) (k + 1)), (r - K - j))) := by ring
      rw [hre]
      apply Nat.add_le_add ih
      by_cases hzero : r = 0
      · simp [hzero]
      have same1 : (∑ j ∈ range (min r (k + 1)), (r - j)) = ∑ j ∈ range (k + 1), (r - j) := by
        apply sum_subset (range_mono (min_le_right _ _))
        intro j hj hm; simp only [mem_range] at hj hm; omega
      have same2 : (∑ j ∈ range (min (r - K) (k + 1)), (r - K - j)) =
          ∑ j ∈ range (k + 1), (r - K - j) := by
        apply sum_subset (range_mono (min_le_right _ _))
        intro j hj hm; simp only [mem_range] at hj hm; omega
      rw [same1, same2]
      have hsub : (∑ j ∈ range (min (v + 1) (k + 1)), (r * t - d * K - j * d)) ≤
          ∑ j ∈ range (k + 1), (r * t - d * K - j * d) :=
        sum_le_sum_of_subset_of_nonneg (range_mono (min_le_right _ _)) (fun _ _ _ => Nat.zero_le _)
      exact hsub.trans (single_core_prefix_bound hd htd htn hmean hj hpd
        (Nat.pos_of_ne_zero hzero) hKr hHt (hcond (Nat.pos_of_ne_zero hzero)) (k + 1))
  have hrc1 : rowCount s r = ∑ j ∈ range r, (s + 1 - j) * (r - j) := by
    unfold rowCount; apply sum_congr rfl; intro j _; ring
  have hrc2 : rowCount s (r - K) = ∑ j ∈ range (r - K), (s + 1 - j) * (r - K - j) := by
    unfold rowCount; apply sum_congr rfl; intro j _; ring
  rw [hrc1, hrc2]
  exact weighted (s + 1)

/-- Convexity of the sharp room condition `4 r² δ + d² ≤ 4 r d (n - t)` over `[1, R]`. -/
private theorem interval_cond_sharp {n d t δ R : ℕ} (r : ℕ)
    (h1 : 1 ≤ r) (hR : r ≤ R)
    (e1 : 4 * 1 * 1 * δ + d * d ≤ 4 * 1 * d * (n - t))
    (eR : 4 * R * R * δ + d * d ≤ 4 * R * d * (n - t)) :
    4 * r * r * δ + d * d ≤ 4 * r * d * (n - t) := by
  set E : ℕ := n - t
  have h1' : (1 : ℤ) ≤ r := by exact_mod_cast h1
  have hR' : (r : ℤ) ≤ R := by exact_mod_cast hR
  have e1' : 4 * (1 : ℤ) * 1 * δ + d * d ≤ 4 * 1 * d * E := by exact_mod_cast e1
  have eR' : 4 * (R : ℤ) * R * δ + d * d ≤ 4 * R * d * E := by exact_mod_cast eR
  suffices h : 4 * (r : ℤ) * r * δ + d * d ≤ 4 * r * d * E by exact_mod_cast h
  rcases eq_or_lt_of_le (h1'.trans hR') with hR1 | hR1
  · have hr1 : (r : ℤ) = 1 := by linarith
    rw [hr1]; exact e1'
  · have key : ((R : ℤ) - 1) * (4 * r * r * δ + d * d - 4 * r * d * E) =
        ((R : ℤ) - r) * (4 * 1 * 1 * δ + d * d - 4 * 1 * d * E) +
        ((r : ℤ) - 1) * (4 * R * R * δ + d * d - 4 * R * d * E) +
        (4 * (δ : ℤ) * (R - 1) * (r - 1)) * (r - R) := by ring
    have a1 : ((R : ℤ) - r) * (4 * 1 * 1 * δ + d * d - 4 * 1 * d * E) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have a2 : ((r : ℤ) - 1) * (4 * R * R * δ + d * d - 4 * R * d * E) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have a3 : (4 * (δ : ℤ) * (R - 1) * (r - 1)) * (r - R) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    by_contra! hc
    have hpos : 0 < ((R : ℤ) - 1) * (4 * r * r * δ + d * d - 4 * r * d * E) :=
      mul_pos (by linarith) (by linarith)
    linarith

/-- Card identity converting `Fintype.card ((x : I) × JetRows s (singleCoreOrder U r K x))`
into `(n - |U|) * rowCount s r + |U| * rowCount s (r - K)`. -/
theorem card_singleCore_rows {I : Type*} [Fintype I] [DecidableEq I]
    (U : Finset I) (s r K : ℕ) :
    Fintype.card ((x : I) × JetRows s (singleCoreOrder U r K x)) =
      (Fintype.card I - U.card) * rowCount s r + U.card * rowCount s (r - K) := by
  rw [Fintype.card_sigma]
  simp_rw [card_rows, singleCoreOrder, apply_ite (rowCount s)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have h1 : (Finset.univ.filter fun x => x ∈ U) = U := by
    ext x; simp
  have h2 : (Finset.univ.filter fun x => x ∉ U) = Finset.univ \ U := by
    ext x; simp
  rw [h1, h2, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, add_comm]

/-! ## Part 4: Exact sharp instantiation at BOTH second-prime Johnson pivots -/

/-- Exact sharp factored no-room radius at the half-rate pivot `314,491,699`
(`√2×` sharper than `110,255,990`). -/
abbrev halfSharpRadius : ℕ := 155925516

/-- Exact sharp factored no-room radius at the quarter-rate pivot `536,870,913`
(`2×` sharper than `72,057,593,769,492,479`). -/
abbrev quarterSharpRadius : ℕ := 144115187807420414

/-- Exact arithmetic certification of both pivot identities, positive-definiteness guards,
and both sharp radius endpoints. -/
theorem pivot_sharp_data :
    1073741824 - 314491699 = 759250125 ∧
    759250125 * 759250125 = 1073741824 * 536870911 + 1082833961 ∧
    536870911 * 536870911 ≤ 759250125 * (1073741824 + 3 * 536870911 - 3 * 759250125) ∧
    1073741824 - 536870913 = 536870911 ∧
    536870911 * 536870911 = 1073741824 * 268435455 + 1 ∧
    268435455 * 268435455 ≤ 536870911 * (1073741824 + 3 * 268435455 - 3 * 536870911) ∧
    4 * halfSharpRadius * halfSharpRadius * 1082833961 + 536870911 * 536870911
      ≤ 4 * halfSharpRadius * 536870911 * 314491699 ∧
    4 * (halfSharpRadius + 1) * (halfSharpRadius + 1) * 1082833961 + 536870911 * 536870911
      > 4 * (halfSharpRadius + 1) * 536870911 * 314491699 ∧
    4 * quarterSharpRadius * quarterSharpRadius * 1 + 268435455 * 268435455
      ≤ 4 * quarterSharpRadius * 268435455 * 536870913 ∧
    4 * (quarterSharpRadius + 1) * (quarterSharpRadius + 1) * 1 + 268435455 * 268435455
      > 4 * (quarterSharpRadius + 1) * 268435455 * 536870913 := by
  norm_num [halfSharpRadius, quarterSharpRadius]

/-- At the half-rate pivot `314,491,699`, NO single-core Kopparty–Sha Appendix A factored
ordinary mixed-Hasse surface with `|U| ≤ 759,250,125` and baseline multiplicity
`r ≤ 155,925,516` has positive dimension surplus (for ANY drop `K ≤ r` and ANY `s, v`). -/
theorem half_pivot_factored_no_room (H s v r K : ℕ)
    (hH : H ≤ 759250125) (hKr : K ≤ r) (hr : r ≤ halfSharpRadius) :
    columnCount s v 536870911 (r * 759250125 - 536870911 * K) ≤
      (1073741824 - H) * rowCount s r + H * rowCount s (r - K) := by
  apply factored_pivot_no_room (δ := 1082833961) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hH s v r K hKr
  intro hpos
  exact interval_cond_sharp r hpos hr (by norm_num)
    (by norm_num [halfSharpRadius])

/-- At the quarter-rate pivot `536,870,913`, NO single-core Kopparty–Sha Appendix A factored
ordinary mixed-Hasse surface with `|U| ≤ 536,870,911` and baseline multiplicity
`r ≤ 144,115,187,807,420,414` has positive dimension surplus (for ANY `K ≤ r`, `s, v`). -/
theorem quarter_pivot_factored_no_room (H s v r K : ℕ)
    (hH : H ≤ 536870911) (hKr : K ≤ r) (hr : r ≤ quarterSharpRadius) :
    columnCount s v 268435455 (r * 536870911 - 268435455 * K) ≤
      (1073741824 - H) * rowCount s r + H * rowCount s (r - K) := by
  apply factored_pivot_no_room (δ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hH s v r K hKr
  intro hpos
  exact interval_cond_sharp r hpos hr (by norm_num)
    (by norm_num [quarterSharpRadius])

/-- Any `HalfSuccessorJetInterpolation.exists_order_surface` single-core factored interpolant
with `|U| ≤ 759,250,125` at the half-rate pivot forces baseline multiplicity
`r > 155,925,516`. -/
theorem half_pivot_factored_surface_requires {I : Type*} [Fintype I] [DecidableEq I]
    (hn : Fintype.card I = 1073741824) (U : Finset I) (hU : U.card ≤ 759250125)
    (s v r K : ℕ) (hKr : K ≤ r)
    (hcount : Fintype.card ((x : I) × JetRows s (singleCoreOrder U r K x)) <
      Fintype.card (Monomials s v 536870911 (r * 759250125 - 536870911 * K))) :
    halfSharpRadius < r := by
  rw [card_singleCore_rows, hn, card_columns] at hcount
  by_contra! hr
  exact (not_le.mpr hcount) (half_pivot_factored_no_room U.card s v r K hU hKr hr)

/-- Any `HalfSuccessorJetInterpolation.exists_order_surface` single-core factored interpolant
with `|U| ≤ 536,870,911` at the quarter-rate pivot forces baseline multiplicity
`r > 144,115,187,807,420,414`. -/
theorem quarter_pivot_factored_surface_requires {I : Type*} [Fintype I] [DecidableEq I]
    (hn : Fintype.card I = 1073741824) (U : Finset I) (hU : U.card ≤ 536870911)
    (s v r K : ℕ) (hKr : K ≤ r)
    (hcount : Fintype.card ((x : I) × JetRows s (singleCoreOrder U r K x)) <
      Fintype.card (Monomials s v 268435455 (r * 536870911 - 268435455 * K))) :
    quarterSharpRadius < r := by
  rw [card_singleCore_rows, hn, card_columns] at hcount
  by_contra! hr
  exact (not_le.mpr hcount) (quarter_pivot_factored_no_room U.card s v r K hU hKr hr)

/-- At the quarter pivot, any constructible (`r ≤ s + 1`) Kopparty–Sha Appendix A single-core
factored surface (`|U| ≤ 536,870,911`) already has scalar degree `s > 2^31`, overflowing the
second-prime budget on scalar-only factors alone. -/
theorem quarter_factored_scalar_overflow (H s v r K : ℕ) (hH : H ≤ 536870911)
    (hKr : K ≤ r) (hs : r ≤ s + 1)
    (hpos : (1073741824 - H) * rowCount s r + H * rowCount s (r - K) <
      columnCount s v 268435455 (r * 536870911 - 268435455 * K)) :
    2147483648 < s := by
  have hr : quarterSharpRadius < r := by
    by_contra! hle
    exact (not_le.mpr hpos) (quarter_pivot_factored_no_room H s v r K hH hKr hle)
  have hbig : 2147483648 < quarterSharpRadius := by norm_num [quarterSharpRadius]
  omega

/-- At the half pivot, any two constructible (`rᵢ ≤ sᵢ + 1`) Kopparty–Sha Appendix A single-core
factored surfaces (`|Uᵢ| ≤ 759,250,125`) satisfy `s₁ * s₂ > 2^31` (in fact `s₁ * s₂ > 2.4 × 10^16`,
exceeding the `2^31` budget by over 7 orders of magnitude). -/
theorem half_factored_two_surface_overflow (H₁ s₁ v₁ r₁ K₁ H₂ s₂ v₂ r₂ K₂ : ℕ)
    (hH₁ : H₁ ≤ 759250125) (hKr₁ : K₁ ≤ r₁) (hs₁ : r₁ ≤ s₁ + 1)
    (hpos₁ : (1073741824 - H₁) * rowCount s₁ r₁ + H₁ * rowCount s₁ (r₁ - K₁) <
      columnCount s₁ v₁ 536870911 (r₁ * 759250125 - 536870911 * K₁))
    (hH₂ : H₂ ≤ 759250125) (hKr₂ : K₂ ≤ r₂) (hs₂ : r₂ ≤ s₂ + 1)
    (hpos₂ : (1073741824 - H₂) * rowCount s₂ r₂ + H₂ * rowCount s₂ (r₂ - K₂) <
      columnCount s₂ v₂ 536870911 (r₂ * 759250125 - 536870911 * K₂)) :
    2147483648 < s₁ * s₂ := by
  have hr₁ : halfSharpRadius < r₁ := by
    by_contra! hle
    exact (not_le.mpr hpos₁) (half_pivot_factored_no_room H₁ s₁ v₁ r₁ K₁ hH₁ hKr₁ hle)
  have hr₂ : halfSharpRadius < r₂ := by
    by_contra! hle
    exact (not_le.mpr hpos₂) (half_pivot_factored_no_room H₂ s₂ v₂ r₂ K₂ hH₂ hKr₂ hle)
  have h1 : halfSharpRadius ≤ s₁ := by omega
  have h2 : halfSharpRadius ≤ s₂ := by omega
  have hbig : 2147483648 < halfSharpRadius * halfSharpRadius := by norm_num [halfSharpRadius]
  exact hbig.trans_le (Nat.mul_le_mul h1 h2)

#print axioms mcaEvent_fresh_site_of_head
#print axioms mcaEvent_head_budget_le
#print axioms kopparty_sha_quadratic_identity
#print axioms kopparty_sha_multicore_continuous_obstruction
#print axioms kopparty_sha_multicore_strict_loss
#print axioms factored_pivot_no_room
#print axioms pivot_sharp_data
#print axioms half_pivot_factored_no_room
#print axioms quarter_pivot_factored_no_room
#print axioms half_pivot_factored_surface_requires
#print axioms quarter_pivot_factored_surface_requires
#print axioms quarter_factored_scalar_overflow
#print axioms half_factored_two_surface_overflow

end ArkLib.ProximityGap.Frontier.PivotFactoredObstruction
