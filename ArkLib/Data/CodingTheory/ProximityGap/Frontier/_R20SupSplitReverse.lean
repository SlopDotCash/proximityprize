/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19RungRecursion

/-!
# LANE RHO (#466 round 20): the sup-split REVERSE inequality — provable shape,
  Paley–Zygmund reverse, and the magnitude-only NO-GO

Goal of the lane: prove `ρ ≤ 3` for the sup-split loss, i.e. the reverse inequality
`S_{r+1}^D ≥ (1/3)·M²_away·S_r^D`, which would make the R19 fixed-point collapse
(`tower ⟺ AwaySupBound`) a two-sided THEOREM (measured ρ ∈ [1.03, 2.70] on true
Gauss-period cells).

## PROBE VERDICT (`probe_r20_supsplit_reverse.py`, `probe_r20_longclimb.py` — scratchpad;
   exact FFT, same `|η|` multiset on `H`, adversarial phases, hill-climbed on ρ₃)

* **ρ ≤ 3 is NOT a magnitude-only fact.** Keeping the TRUE `|η_b|` multiset and replacing
  the Gauss-period phases by adversarial ones drives ρ₃ to **5.00** (p=1009), **7.37**
  (p=4073), **9.02** (p=12289) — growing with `p` and not converged (random-restart
  hill-climb, 3×25k proposals). Any proof of a constant reverse MUST use phase/arithmetic
  input (the μ_n-invariance / Gauss-period structure of the weight), not just `|I|`-moment
  data. This is a clean no-go for the "two-sided theorem from the exact identities" hope.
* **The two-atom mechanism is exactly the adversary's shape**: one lone near-sup value over
  a fat bulk `c` times lower gives ρ₃ ≈ (1+t)/2 with `t = (M/bulk)²` — unbounded. The
  hill-climb converges toward this profile. Formalized below as
  `magnitudeOnly_reverse_unbounded` (an explicit nonneg vector for EVERY target bound `B`).
* **The honest provable reverse is Paley–Zygmund-shaped** and is formalized here:
  `S_{r+2}^D ≥ t·(S_{r+1}^D − t^r·S_1^D)` for every threshold `t ≥ 0` (`pz_reverse` +
  `rungMoment_pz_reverse`). On true cells, optimizing `t` gives `S_4 ≥ S_4^{true}/c` with
  `c = 3.3–5.2` (measured) — an UNCONDITIONAL quantitative reverse whose constant is
  distribution-dependent (through `S_1`), not absolute.
* **What IS absolute**: ρ_r is monotone DECREASING in `r` (moment log-convexity,
  `rungMoment_sq_le_mul` below) and ρ_r ≥ 1 always; so the true-cell measurement ρ₃ ≤ 2.7
  bounds all deeper rungs of the same cell. The missing piece is exactly a bound on the
  FIRST nontrivial ρ, which the no-go shows needs phase input.

## What THIS file proves (all axiom-clean; no Weil, no analysis beyond `Real.sqrt`)

* `reverse_witness` — the trivial reverse: the sup is witnessed at least once,
  `S_{r+1}^D ≥ ‖I(s*)‖²·‖I(s*)‖^{2r}` for every away `s*` (in particular at the argmax:
  `S_{r+1} ≥ M^{2r+2}`).
* `pz_reverse` / `rungMoment_pz_reverse` — the Paley–Zygmund reverse (threshold form),
  abstract and instantiated at the rung moments.
* `sum_pow_sq_le_mul` / `rungMoment_sq_le_mul` — moment log-convexity
  `(S_{r+1})² ≤ S_r·S_{r+2}` (Cauchy–Schwarz), hence the sup-split loss ρ_r is
  monotone non-increasing in `r` (`rho_antitone_product` in product form).
* `SupSplitReverse` — the named Prop `∀ s away, ∀ r, ‖I s‖²·S_r ≤ ρ·S_{r+1}`; and
  `awaySup_of_reverse` — the payoff direction: `SupSplitReverse ρ` converts ANY rung
  bound into an away-sup bound (`‖I s‖²·S_r ≤ ρ·K` whenever `S_{r+1} ≤ K`), i.e. the
  reverse is precisely what upgrades the R19 collapse to an equivalence.
* `magnitudeOnly_reverse_unbounded` — the NO-GO: for every `B` there is an explicit
  nonnegative vector (spike `t` over a bulk of `⌈2B⌉+1`-scaled size) whose sup-split
  reverse constant exceeds `B`; so no magnitude-only argument can prove `ρ ≤ 3`.

## Honest scope

`ρ ≤ 3` on true Gauss-period cells remains a MEASUREMENT (documented conjecture), now with
a proof-shaped obstruction: it is equivalent to a lower-tail/anti-concentration statement
about the `‖I‖` distribution near its max, FALSE for generic phases with the same
magnitudes, hence at least as phase-deep as the wall itself. Issue #466, round 20,
LANE RHO.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R19RungRecursion

namespace ArkLib.ProximityGap.Frontier.R20SupSplitReverse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (1) The trivial reverse: the sup is witnessed. -/

/-- **Witness reverse.** Every away point contributes its full power to the next rung:
`S_{r+1}^D ≥ ‖I(s*)‖²·‖I(s*)‖^{2r}`. At the argmax this is `S_{r+1} ≥ M^{2(r+1)}` — the
vacuous end of the reverse spectrum (loses `S_r/M^{2r}` = the near-max effective count). -/
theorem reverse_witness (ψ : AddChar F ℂ) (G H D : Finset F) {s : F}
    (hs : s ∈ Finset.univ \ D) (r : ℕ) :
    ‖incidenceSum ψ G H s‖ ^ 2 * ‖incidenceSum ψ G H s‖ ^ (2 * r)
      ≤ rungMoment ψ G H D (r + 1) := by
  have h : ‖incidenceSum ψ G H s‖ ^ (2 * (r + 1)) ≤ rungMoment ψ G H D (r + 1) :=
    Finset.single_le_sum (f := fun s => ‖incidenceSum ψ G H s‖ ^ (2 * (r + 1)))
      (fun i _ => pow_nonneg (norm_nonneg _) _) hs
  calc ‖incidenceSum ψ G H s‖ ^ 2 * ‖incidenceSum ψ G H s‖ ^ (2 * r)
      = ‖incidenceSum ψ G H s‖ ^ (2 * (r + 1)) := by rw [← pow_add]; congr 1; ring
    _ ≤ rungMoment ψ G H D (r + 1) := h

/-! ### (2) The Paley–Zygmund reverse (threshold form) — abstract, then at the rungs. -/

/-- **Abstract Paley–Zygmund reverse.** For nonnegative `x` on a finset and any threshold
`t ≥ 0`: `∑ x^{r+2} ≥ t·(∑ x^{r+1} − t^r·∑ x)`. The level set `{x ≥ t}` carries the
`(r+2)`-mass; the sub-threshold mass at depth `r+1` is crushed by `t^r·∑x`. -/
theorem pz_reverse {α : Type*} [DecidableEq α] (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    t * ((∑ i ∈ s, x i ^ (r + 1)) - t ^ r * ∑ i ∈ s, x i)
      ≤ ∑ i ∈ s, x i ^ (r + 2) := by
  classical
  set s₁ := s.filter (fun i => t ≤ x i) with hs₁
  set s₂ := s.filter (fun i => ¬ t ≤ x i) with hs₂
  have hsplit : ∀ k : ℕ, (∑ i ∈ s, x i ^ k)
      = (∑ i ∈ s₁, x i ^ k) + ∑ i ∈ s₂, x i ^ k := fun k =>
    (Finset.sum_filter_add_sum_filter_not s _ _).symm
  -- sub-threshold depth-(r+1) mass ≤ t^r · (total first moment)
  have hlow : (∑ i ∈ s₂, x i ^ (r + 1)) ≤ t ^ r * ∑ i ∈ s, x i := by
    have h1 : (∑ i ∈ s₂, x i ^ (r + 1)) ≤ ∑ i ∈ s₂, t ^ r * x i := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hi0 : 0 ≤ x i := hx i (Finset.mem_filter.mp hi).1
      have hit : x i ≤ t := le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      calc x i ^ (r + 1) = x i ^ r * x i := by rw [pow_succ]
        _ ≤ t ^ r * x i :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hi0 hit r) hi0
    have h2 : (∑ i ∈ s₂, t ^ r * x i) = t ^ r * ∑ i ∈ s₂, x i := by
      rw [Finset.mul_sum]
    have h3 : (∑ i ∈ s₂, x i) ≤ ∑ i ∈ s, x i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi _ => hx i hi)
    calc (∑ i ∈ s₂, x i ^ (r + 1)) ≤ t ^ r * ∑ i ∈ s₂, x i := h1.trans h2.le
      _ ≤ t ^ r * ∑ i ∈ s, x i :=
          mul_le_mul_of_nonneg_left h3 (pow_nonneg ht r)
  -- level-set depth-(r+2) mass ≥ t · (level-set depth-(r+1) mass)
  have hhigh : t * (∑ i ∈ s₁, x i ^ (r + 1)) ≤ ∑ i ∈ s₁, x i ^ (r + 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi0 : 0 ≤ x i := hx i (Finset.mem_filter.mp hi).1
    have hit : t ≤ x i := (Finset.mem_filter.mp hi).2
    calc t * x i ^ (r + 1) ≤ x i * x i ^ (r + 1) :=
          mul_le_mul_of_nonneg_right hit (pow_nonneg hi0 _)
      _ = x i ^ (r + 2) := by rw [← pow_succ']
  have hnn : (0 : ℝ) ≤ ∑ i ∈ s₂, x i ^ (r + 2) :=
    Finset.sum_nonneg (fun i hi => pow_nonneg (hx i (Finset.mem_filter.mp hi).1) _)
  calc t * ((∑ i ∈ s, x i ^ (r + 1)) - t ^ r * ∑ i ∈ s, x i)
      ≤ t * ((∑ i ∈ s, x i ^ (r + 1)) - ∑ i ∈ s₂, x i ^ (r + 1)) := by
        apply mul_le_mul_of_nonneg_left _ ht
        exact sub_le_sub_left hlow _
    _ = t * ∑ i ∈ s₁, x i ^ (r + 1) := by rw [hsplit (r + 1)]; ring
    _ ≤ ∑ i ∈ s₁, x i ^ (r + 2) := hhigh
    _ ≤ ∑ i ∈ s, x i ^ (r + 2) := by
        rw [hsplit (r + 2)]; exact le_add_of_nonneg_right hnn

/-- **PZ reverse at the rung moments**: for every threshold `t ≥ 0`,
`S_{r+2}^D ≥ t·(S_{r+1}^D − t^r·S_1^D)`. Measured (probe): optimizing `t` recovers `S_4`
within a factor 3.3–5.2 on true cells — the honest unconditional reverse. -/
theorem rungMoment_pz_reverse (ψ : AddChar F ℂ) (G H D : Finset F)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    t * (rungMoment ψ G H D (r + 1) - t ^ r * rungMoment ψ G H D 1)
      ≤ rungMoment ψ G H D (r + 2) := by
  classical
  have key := pz_reverse (Finset.univ \ D)
    (fun s => ‖incidenceSum ψ G H s‖ ^ 2)
    (fun i _ => pow_nonneg (norm_nonneg _) _) t ht r
  have hcast : ∀ k : ℕ, (∑ s ∈ Finset.univ \ D, (‖incidenceSum ψ G H s‖ ^ 2) ^ k)
      = rungMoment ψ G H D k := by
    intro k
    unfold rungMoment
    exact Finset.sum_congr rfl (fun s _ => by rw [← pow_mul])
  rw [hcast (r + 1), hcast (r + 2)] at key
  have h1 : (∑ s ∈ Finset.univ \ D, (‖incidenceSum ψ G H s‖ ^ 2) ^ 1)
      = rungMoment ψ G H D 1 := hcast 1
  simp only [pow_one] at h1
  rw [h1] at key
  exact key

/-! ### (3) Log-convexity: the sup-split loss ρ_r is monotone non-increasing in r. -/

/-- **Abstract moment log-convexity** (Cauchy–Schwarz): for nonnegative `x`,
`(∑ x^{r+1})² ≤ (∑ x^r)·(∑ x^{r+2})`. -/
theorem sum_pow_sq_le_mul {α : Type*} (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (r : ℕ) :
    (∑ i ∈ s, x i ^ (r + 1)) ^ 2
      ≤ (∑ i ∈ s, x i ^ r) * ∑ i ∈ s, x i ^ (r + 2) := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (x i ^ r)) (fun i => Real.sqrt (x i ^ (r + 2)))
  have hfg : (∑ i ∈ s, Real.sqrt (x i ^ r) * Real.sqrt (x i ^ (r + 2)))
      = ∑ i ∈ s, x i ^ (r + 1) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi0 := hx i hi
    rw [← Real.sqrt_mul (pow_nonneg hi0 r)]
    have : x i ^ r * x i ^ (r + 2) = (x i ^ (r + 1)) ^ 2 := by ring
    rw [this, Real.sqrt_sq (pow_nonneg hi0 _)]
  have hf2 : (∑ i ∈ s, Real.sqrt (x i ^ r) ^ 2) = ∑ i ∈ s, x i ^ r :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (pow_nonneg (hx i hi) r))
  have hg2 : (∑ i ∈ s, Real.sqrt (x i ^ (r + 2)) ^ 2) = ∑ i ∈ s, x i ^ (r + 2) :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (pow_nonneg (hx i hi) _))
  rw [hfg, hf2, hg2] at cs
  exact cs

/-- **Rung-moment log-convexity**: `(S_{r+1}^D)² ≤ S_r^D·S_{r+2}^D`. Consequence: the
ratios `S_{r+1}/S_r` are non-decreasing, so ρ_r = M²·S_{r-1}/S_r is non-increasing in `r` —
the true-cell measurement ρ₃ ≤ 2.7 dominates every deeper rung of the same cell. -/
theorem rungMoment_sq_le_mul (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) :
    rungMoment ψ G H D (r + 1) ^ 2
      ≤ rungMoment ψ G H D r * rungMoment ψ G H D (r + 2) := by
  classical
  have key := sum_pow_sq_le_mul (Finset.univ \ D)
    (fun s => ‖incidenceSum ψ G H s‖ ^ 2)
    (fun i _ => pow_nonneg (norm_nonneg _) _) r
  have hcast : ∀ k : ℕ, (∑ s ∈ Finset.univ \ D, (‖incidenceSum ψ G H s‖ ^ 2) ^ k)
      = rungMoment ψ G H D k := fun k =>
    Finset.sum_congr rfl (fun s _ => by rw [← pow_mul])
  rwa [hcast r, hcast (r + 1), hcast (r + 2)] at key

/-- ρ-antitonicity in product form (division-free): for any away-sup proxy `B ≥ 0`,
`(B·S_{r+1})·S_{r+1} ≤ (B·S_r)·S_{r+2}` — i.e. `B·S_r/S_{r+1}` is non-increasing in `r`
wherever the rungs are positive. -/
theorem rho_antitone_product (ψ : AddChar F ℂ) (G H D : Finset F) (B : ℝ)
    (hB : 0 ≤ B) (r : ℕ) :
    (B * rungMoment ψ G H D (r + 1)) * rungMoment ψ G H D (r + 1)
      ≤ (B * rungMoment ψ G H D r) * rungMoment ψ G H D (r + 2) := by
  have h := rungMoment_sq_le_mul ψ G H D r
  calc (B * rungMoment ψ G H D (r + 1)) * rungMoment ψ G H D (r + 1)
      = B * rungMoment ψ G H D (r + 1) ^ 2 := by ring
    _ ≤ B * (rungMoment ψ G H D r * rungMoment ψ G H D (r + 2)) :=
        mul_le_mul_of_nonneg_left h hB
    _ = (B * rungMoment ψ G H D r) * rungMoment ψ G H D (r + 2) := by ring

/-! ### (4) The named reverse Prop and its payoff. -/

/-- **The sup-split reverse at loss ρ** (the lane target at ρ = 3, measured ≤ 2.7 on true
cells, REFUTED for generic phases by the probe): every away value satisfies
`‖I s‖²·S_r ≤ ρ·S_{r+1}`. Quantified over away `s`, this is exactly
`M²_away·S_r ≤ ρ·S_{r+1}`. -/
def SupSplitReverse (ψ : AddChar F ℂ) (G H D : Finset F) (ρ : ℝ) : Prop :=
  ∀ s ∈ Finset.univ \ D, ∀ r : ℕ,
    ‖incidenceSum ψ G H s‖ ^ 2 * rungMoment ψ G H D r
      ≤ ρ * rungMoment ψ G H D (r + 1)

/-- **The payoff (two-sidedness direction)**: `SupSplitReverse ρ` converts ANY rung bound
`S_{r+1}^D ≤ K` into an away-sup bound `‖I s‖²·S_r^D ≤ ρ·K`. With the R19
`tower_of_awaySupBound` this closes the loop: given the reverse, tower ⟺ AwaySupBound.
The probe shows `SupSplitReverse 3` is a genuinely phase-dependent statement. -/
theorem awaySup_of_reverse (ψ : AddChar F ℂ) (G H D : Finset F) {ρ K : ℝ}
    (hρ : 0 ≤ ρ) (hrev : SupSplitReverse ψ G H D ρ) {r : ℕ}
    (hK : rungMoment ψ G H D (r + 1) ≤ K) :
    ∀ s ∈ Finset.univ \ D,
      ‖incidenceSum ψ G H s‖ ^ 2 * rungMoment ψ G H D r ≤ ρ * K :=
  fun s hs => (hrev s hs r).trans (mul_le_mul_of_nonneg_left hK hρ)

/-! ### (5) The NO-GO: magnitude data alone cannot bound the reverse loss. -/

/-- **Magnitude-only no-go.** For EVERY target bound `B` there is an explicit nonnegative
vector `x` on a finite index set (one spike of height `t = 2·max(B,1) + 1` over a bulk of
`N = ⌈t³⌉` ones) whose sup-split reverse loss at rung 3 exceeds `B`:
`(sup x)·(∑ x²) > B·(∑ x³)`. Since the rung values `x_s = ‖I s‖²` of an adversarial-phase
weight realize exactly such profiles (probe: ρ₃ = 5.0/7.4/9.0 at p = 1009/4073/12289 with
the TRUE `|η|` multiset), no argument seeing only the `|I|`-moment data can prove
`SupSplitReverse 3`. The reverse, if true for Gauss periods, is phase-deep. -/
theorem magnitudeOnly_reverse_unbounded (B : ℝ) :
    ∃ (N : ℕ) (x : ℕ → ℝ),
      (∀ i, 0 ≤ x i) ∧
      (∀ i ∈ Finset.range (N + 1), x i ≤ x 0) ∧
      B * (∑ i ∈ Finset.range (N + 1), x i ^ 3)
        < x 0 * ∑ i ∈ Finset.range (N + 1), x i ^ 2 := by
  classical
  -- spike height t ≥ max (2B+1) 1, bulk = t³ ones (t a natural number)
  obtain ⟨tn, htn⟩ := exists_nat_gt (max (2 * B) 1)
  set t : ℝ := (tn : ℝ) with ht_def
  have ht1 : (1 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) htn
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
  have htB : 2 * B < t := lt_of_le_of_lt (le_max_left _ _) htn
  refine ⟨tn ^ 3, fun i => if i = 0 then t else 1, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0 <;> simp [hi, le_of_lt ht0, zero_le_one]
  · intro i _
    by_cases hi : i = 0 <;> simp [hi, le_of_lt ht1]
  · -- compute the sums: ∑ x^k = t^k + N over range (N+1)
    have hsum : ∀ k : ℕ, k ≠ 0 →
        (∑ i ∈ Finset.range (tn ^ 3 + 1), (if i = 0 then t else 1) ^ k)
          = t ^ k + (tn ^ 3 : ℝ) := by
      intro k hk
      have h0mem : (0 : ℕ) ∈ Finset.range (tn ^ 3 + 1) :=
        Finset.mem_range.mpr (Nat.succ_pos _)
      rw [← Finset.sum_erase_add _ _ h0mem]
      have herase : (∑ i ∈ (Finset.range (tn ^ 3 + 1)).erase 0,
          (if i = 0 then t else 1) ^ k) = ((tn ^ 3 : ℕ) : ℝ) := by
        calc
          (∑ i ∈ (Finset.range (tn ^ 3 + 1)).erase 0,
              (if i = 0 then t else 1) ^ k)
              = ∑ _i ∈ (Finset.range (tn ^ 3 + 1)).erase 0, (1 : ℝ) := by
                refine Finset.sum_congr rfl (fun i hi => ?_)
                have : i ≠ 0 := Finset.ne_of_mem_erase hi
                simp [this]
          _ = ((tn ^ 3 : ℕ) : ℝ) := by
              rw [Finset.sum_const, Finset.card_erase_of_mem h0mem, Finset.card_range]
              simp
      rw [herase]
      simp [add_comm]
    have h2 := hsum 2 (by norm_num)
    have h3 := hsum 3 (by norm_num)
    rw [h2, h3]
    have hx0 : (if (0 : ℕ) = 0 then t else 1) = t := by simp
    simp only [if_true]
    -- goal: B·(t³ + t³) < t·(t² + t³), i.e. 2B·t³ < t³ + t⁴, follows from 2B < t ≤ 1 + t
    have htn3 : (tn : ℝ) ^ 3 = t ^ 3 := by rw [ht_def]
    rw [htn3]
    have ht3 : (0 : ℝ) < t ^ 3 := pow_pos ht0 3
    nlinarith [mul_pos ht3 ht0]

/-! ### (6) The UNCONDITIONAL reverse: `ρ_r ≤ N^{1/r}` in natural powers, and the exact
depth at which `ρ ≤ 3` becomes a THEOREM.

The no-go (§5) shows a fixed constant at fixed small `r` needs phase input. But the probe
also shows the Hölder ceiling `ρ_r ≤ N^{1/r}` (`N` = away count) holds with room in every
cell — and it is PROVABLE with no phase input at all, from log-convexity alone, entirely in
natural powers (no `rpow`). Consequence: at depth `r + 1 ≥ log₃ N` the lane target `ρ ≤ 3`
is an unconditional theorem — and the prize depth `r ≈ ln q ≈ 0.91·log₃ q` is exactly
there. So the two-sided window is: PHASE-DEEP below depth `log₃ q`, FREE at/above it. -/

/-- `S_0 = N`, the away count — the normalizer of the Hölder chain. -/
theorem rungMoment_zero_eq_card (ψ : AddChar F ℂ) (G H D : Finset F) :
    rungMoment ψ G H D 0 = ((Finset.univ \ D).card : ℝ) := by
  unfold rungMoment
  simp

/-- **The power-mean chain** `S_r^{r+1} ≤ S_0·S_{r+1}^r`, by induction from log-convexity
alone. With `S_0 = N` this is Hölder `ρ_r ≤ N^{1/r}` in polynomial form. -/
theorem rungMoment_pow_le (ψ : AddChar F ℂ) (G H D : Finset F) :
    ∀ r : ℕ, rungMoment ψ G H D r ^ (r + 1)
      ≤ rungMoment ψ G H D 0 * rungMoment ψ G H D (r + 1) ^ r := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      by_cases h0 : rungMoment ψ G H D (r + 1) = 0
      · rw [h0, zero_pow (by omega)]
        exact mul_nonneg (rungMoment_nonneg ψ G H D 0)
          (pow_nonneg (rungMoment_nonneg ψ G H D (r + 2)) _)
      · have hpos : 0 < rungMoment ψ G H D (r + 1) :=
          lt_of_le_of_ne (rungMoment_nonneg ψ G H D (r + 1)) (Ne.symm h0)
        have hlc := rungMoment_sq_le_mul ψ G H D r
        have hlcpow : (rungMoment ψ G H D (r + 1) ^ 2) ^ (r + 1)
            ≤ (rungMoment ψ G H D r * rungMoment ψ G H D (r + 2)) ^ (r + 1) :=
          pow_le_pow_left₀ (sq_nonneg _) hlc (r + 1)
        -- feed the induction hypothesis and cancel S_{r+1}^r
        have hfactor : rungMoment ψ G H D (r + 1) ^ r
              * rungMoment ψ G H D (r + 1) ^ (r + 2)
            ≤ rungMoment ψ G H D (r + 1) ^ r
              * (rungMoment ψ G H D 0 * rungMoment ψ G H D (r + 2) ^ (r + 1)) := by
          have hIH : rungMoment ψ G H D r ^ (r + 1) * rungMoment ψ G H D (r + 2) ^ (r + 1)
              ≤ (rungMoment ψ G H D 0 * rungMoment ψ G H D (r + 1) ^ r)
                  * rungMoment ψ G H D (r + 2) ^ (r + 1) :=
            mul_le_mul_of_nonneg_right ih
              (pow_nonneg (rungMoment_nonneg ψ G H D (r + 2)) _)
          calc rungMoment ψ G H D (r + 1) ^ r * rungMoment ψ G H D (r + 1) ^ (r + 2)
              = (rungMoment ψ G H D (r + 1) ^ 2) ^ (r + 1) := by
                rw [← pow_add, ← pow_mul]; congr 1; ring
            _ ≤ (rungMoment ψ G H D r * rungMoment ψ G H D (r + 2)) ^ (r + 1) := hlcpow
            _ = rungMoment ψ G H D r ^ (r + 1) * rungMoment ψ G H D (r + 2) ^ (r + 1) := by
                rw [mul_pow]
            _ ≤ (rungMoment ψ G H D 0 * rungMoment ψ G H D (r + 1) ^ r)
                  * rungMoment ψ G H D (r + 2) ^ (r + 1) := hIH
            _ = rungMoment ψ G H D (r + 1) ^ r
                  * (rungMoment ψ G H D 0 * rungMoment ψ G H D (r + 2) ^ (r + 1)) := by
                ring
        exact le_of_mul_le_mul_left hfactor (pow_pos hpos r)

/-- **The unconditional reverse sup-split (power form)**: for every away `s*`,
`(‖I s*‖²·S_r)^{r+1} ≤ N·S_{r+1}^{r+1}` — i.e. `ρ_r ≤ N^{1/r}`, with NO hypothesis and no
phase input. Probe: the free magnitude adversary reaches `ρ_r ≈ N^{1/(r+1)}·const`, so this
ceiling is within one power of tight — magnitude-only arguments cannot beat polynomial-in-N
(consistent with the §5 no-go). -/
theorem supSplit_reverse_pow (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) {s : F}
    (hs : s ∈ Finset.univ \ D) :
    (‖incidenceSum ψ G H s‖ ^ 2 * rungMoment ψ G H D r) ^ (r + 1)
      ≤ ((Finset.univ \ D).card : ℝ) * rungMoment ψ G H D (r + 1) ^ (r + 1) := by
  have hmax : (‖incidenceSum ψ G H s‖ ^ 2) ^ (r + 1) ≤ rungMoment ψ G H D (r + 1) := by
    have h := reverse_witness ψ G H D hs r
    calc (‖incidenceSum ψ G H s‖ ^ 2) ^ (r + 1)
        = ‖incidenceSum ψ G H s‖ ^ 2 * ‖incidenceSum ψ G H s‖ ^ (2 * r) := by
          rw [← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ rungMoment ψ G H D (r + 1) := h
  calc (‖incidenceSum ψ G H s‖ ^ 2 * rungMoment ψ G H D r) ^ (r + 1)
      = (‖incidenceSum ψ G H s‖ ^ 2) ^ (r + 1) * rungMoment ψ G H D r ^ (r + 1) := by
        rw [mul_pow]
    _ ≤ rungMoment ψ G H D (r + 1)
          * (rungMoment ψ G H D 0 * rungMoment ψ G H D (r + 1) ^ r) :=
        mul_le_mul hmax (rungMoment_pow_le ψ G H D r)
          (pow_nonneg (rungMoment_nonneg ψ G H D r) _)
          (rungMoment_nonneg ψ G H D (r + 1))
    _ = rungMoment ψ G H D 0 * rungMoment ψ G H D (r + 1) ^ (r + 1) := by
        rw [pow_succ]; ring
    _ = ((Finset.univ \ D).card : ℝ) * rungMoment ψ G H D (r + 1) ^ (r + 1) := by
        rw [rungMoment_zero_eq_card]

/-- **`ρ ≤ 3` IS a theorem at depth.** If the away count satisfies `N ≤ 3^{r+1}` — true for
every rung `r + 1 ≥ log₃ q`, in particular at the prize depth `r ≈ ln q ≈ 0.91·log₃ q` —
then the reverse sup-split holds with constant 3: `‖I s*‖²·S_r ≤ 3·S_{r+1}` for every away
`s*`. With R19's forward `sup_split_recursion`, the tower ⟺ `AwaySupBound` fixed point is
TWO-SIDED with constant 3 at all rungs `r ≥ log₃ q`, unconditionally; below that depth the
§5 no-go says any constant is phase-deep. -/
theorem supSplit_reverse_three_at_depth (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ)
    (hN : ((Finset.univ \ D).card : ℝ) ≤ 3 ^ (r + 1)) {s : F}
    (hs : s ∈ Finset.univ \ D) :
    ‖incidenceSum ψ G H s‖ ^ 2 * rungMoment ψ G H D r
      ≤ 3 * rungMoment ψ G H D (r + 1) := by
  have hpow : (‖incidenceSum ψ G H s‖ ^ 2 * rungMoment ψ G H D r) ^ (r + 1)
      ≤ (3 * rungMoment ψ G H D (r + 1)) ^ (r + 1) := by
    calc (‖incidenceSum ψ G H s‖ ^ 2 * rungMoment ψ G H D r) ^ (r + 1)
        ≤ ((Finset.univ \ D).card : ℝ) * rungMoment ψ G H D (r + 1) ^ (r + 1) :=
          supSplit_reverse_pow ψ G H D r hs
      _ ≤ 3 ^ (r + 1) * rungMoment ψ G H D (r + 1) ^ (r + 1) :=
          mul_le_mul_of_nonneg_right hN
            (pow_nonneg (rungMoment_nonneg ψ G H D (r + 1)) _)
      _ = (3 * rungMoment ψ G H D (r + 1)) ^ (r + 1) := by rw [mul_pow]
  exact le_of_pow_le_pow_left₀ (by omega)
    (mul_nonneg (by norm_num) (rungMoment_nonneg ψ G H D (r + 1))) hpow

end ArkLib.ProximityGap.Frontier.R20SupSplitReverse

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.reverse_witness
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.pz_reverse
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.rungMoment_pz_reverse
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.sum_pow_sq_le_mul
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.rungMoment_sq_le_mul
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.rho_antitone_product
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.awaySup_of_reverse
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.magnitudeOnly_reverse_unbounded
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.rungMoment_zero_eq_card
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.rungMoment_pow_le
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.supSplit_reverse_pow
#print axioms ArkLib.ProximityGap.Frontier.R20SupSplitReverse.supSplit_reverse_three_at_depth
