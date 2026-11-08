/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import Mathlib.Tactic

/-!
# The sharpened unconditional LOWER bound on the worst Gauss period (#407)

The prize per-frequency object is `B = max_{b≠0} ‖η_b‖`, `η_b = ∑_{y∈μ_n} ψ(b·y)` the incomplete
subgroup Gauss sum.  Two unconditional lower bounds are in-tree:

* **Parseval** (`exists_period_sq_ge`, the `r=1` second moment): `B ≥ √(n(q−n)/(q−1)) ≈ √n`;
* the **consecutive-moment-ratio** companion (`exists_period_sq_ge_moment_ratio`).

This file supplies the **moment-AVERAGE** lower companion — the cleanest `r`-parametric strengthening
of Parseval — and uses it to push the lower bound to its genuine constant ceiling.

The DC-subtracted moment identity `∑_{b≠0} ‖η_b‖^{2r} = q·E_r − |G|^{2r}`
(`DCSubtractedMoment.sum_nonzero_moment`, pure orthogonality, **no Weil, no open input**) has `q−1`
nonzero terms, so `max ≥ average` gives, with **no hypothesis whatsoever** beyond the moment identity,

> **`worstPeriod_pow_ge_avg`** : `∃ b ≠ 0,  (q·E_r − |G|^{2r})/(q−1) ≤ ‖η_b‖^{2r}`.

This is the `r`-parametric moment-average floor: at `r=1` it reproduces Parseval exactly; for
`r ≥ 2` its strength depends on how large `E_r` is relative to `|G|^{2r}/q`.  (By Hölder the true normalized
moments are monotone in `r`, so with the *exact* `E_r` the floor never falls below Parseval; a
*weakened* energy input can, see below.)

Feeding **any** provable lower bound `E_r ≥ L` into the core (`worstPeriod_pow_ge_of_energy_lb`)
yields `max^{2r} ≥ (q·L − |G|^{2r})/(q−1)`.  Two clean energy lower bounds are proven here with no
open input:

* **`rEnergy_ge_diag`** : `E_r(G) ≥ |G|^r` (the diagonal `v=w`).  At `r = 1` this is exact and
  recovers Parseval.  For `r ≥ 2` the diagonal-only substitute can be *weaker* than Parseval: at
  `n = 4`, `q = 17`, `r = 2` it gives `max ≥ 1`, versus Parseval's `max ≥ √(13/4)`;
* **`rEnergy_mono`** : `H ⊆ G ⟹ E_r(H) ≤ E_r(G)` (sub-sum of nonnegative indicators), hence a
  *subgroup* energy lower-bounds the ambient one (e.g. `E_r(μ_n) ≥ E_r(μ_2) = C(2r,r)`).

**The exact-Wick input is false; use the falling-factorial form.**  The predicate
`WickEnergyLowerBound G r` (`E_r(G) ≥ (2r−1)‼·|G|^r`) drops a *negative* finite-size correction and
fails already at `r = 2`: for an antipodal root group in characteristic `0` (or a thin finite-field
copy), `E₂ = 3n² − 3n < 3n²`; e.g. `G = {1, −1}` has `E₂ = 6 < 12`
(`not_wickEnergyLowerBound_pm_one`).  More generally `E_r({±1}) = C(2r, r) < (2r)!/r!` for `r ≥ 2`.
The theorems `not_ramanujan_of_wickLB` / `worstPeriod_gt_two_sqrt_of_wickLB` remain correct
conditional implications but their hypothesis does not hold for such `G`.

The corrected input is the antipodal-matching count with distinct antipodal classes,
`WickFallingEnergyLowerBound G r` : `E_r(G) ≥ (2r−1)‼·∏_{i<r}(|G| − 2i)` (truncated subtraction).
It is true whenever `G = −G`, `0 ∉ G` and `char F ≠ 2` (each perfect matching of the `2r` positions,
each injective choice of `r` antipodal classes and each choice of signs gives a distinct zero-sum
tuple), but that combinatorial proof is **not formalized** here: it remains an explicit hypothesis.
With it:

> **`not_ramanujan_of_fallingWickLB`** / **`worstPeriod_gt_two_sqrt_of_fallingWickLB`** :  if
> `E_r(G) ≥ L := (2r−1)‼·∏_{i<r}(n − 2i)` and `n^{2r} ≤ q·(L − 4^r·n^r)`, then
> `max_{b≠0} ‖η_b‖ > 2√n`.

The recomputed trigger `n^{2r} ≤ q·(L − 4^r n^r)` needs `L > 4^r n^r`; since `L/n^r → (2r−1)‼` as
`n → ∞` with `r` fixed, this first becomes possible at `r = 6` (`11‼ = 10395 > 4096 = 4^6`) for `n`
large enough, where it reads approximately `q·6299 ≳ n^6` (`β = log_n q ≳ 5.6`), now with the
explicit finite-size factor `∏_{i<6}(1 − 2i/n)`.  Above that threshold the generalized Paley / Cayley graph
`Cay(F_q, μ_n)` is not Ramanujan, **conditional** on the named (true but unformalized) falling
lower bound.  Axiom-clean; no `sorry`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #407.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ArkLib.ProximityGap.WorstPeriodMomentAvgLower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The moment-average core (no open input) -/

/-- **The sharpened unconditional lower bound (moment AVERAGE).**  There is a nontrivial frequency
`b ≠ 0` whose `2r`-th Gauss-period power is at least the average of the nonzero moments,
`(q·E_r − |G|^{2r})/(q−1) ≤ ‖η_b‖^{2r}`.

Pure `max ≥ average`: the `q−1` nonzero terms of the DC-subtracted moment identity
`∑_{b≠0} ‖η_b‖^{2r} = q·E_r − |G|^{2r}` (`sum_nonzero_moment`, no Weil) sum to that value, so their
maximum is at least their average.  No hypothesis beyond the moment identity; **this is the genuine
`r`-parametric strengthening of the Parseval floor** (`r=1` reproduces Parseval). -/
theorem worstPeriod_pow_ge_avg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
          / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ (2 * r) := by
  classical
  set S : Finset F := Finset.univ.erase (0 : F) with hS
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : F)
    exact ⟨x, by rw [hS, Finset.mem_erase]; exact ⟨hx, Finset.mem_univ x⟩⟩
  -- card of the nonzero frequencies is q − 1
  have hcard : (S.card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Nat.cast_sub hq1]; simp
  have hcardpos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.mpr hSne
    exact_mod_cast this
  -- the restricted moment sum
  have hmom : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) :=
    sum_nonzero_moment hψ G r
  -- pick the maximizer
  obtain ⟨b₀, hb₀S, hb₀max⟩ := S.exists_max_image (fun b => ‖eta ψ G b‖ ^ (2 * r)) hSne
  refine ⟨b₀, ?_, ?_⟩
  · have := hb₀S; rw [hS, Finset.mem_erase] at this; exact this.1
  -- average ≤ max
  have hsum_le : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) ≤ S.card • ‖eta ψ G b₀‖ ^ (2 * r) := by
    refine Finset.sum_le_card_nsmul S _ _ (fun b hb => hb₀max b hb)
  rw [hmom] at hsum_le
  rw [nsmul_eq_mul] at hsum_le
  rw [div_le_iff₀ (by rw [← hcard]; exact hcardpos)]
  calc ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
      ≤ (S.card : ℝ) * ‖eta ψ G b₀‖ ^ (2 * r) := hsum_le
    _ = ‖eta ψ G b₀‖ ^ (2 * r) * ((Fintype.card F : ℝ) - 1) := by rw [hcard]; ring

/-- **Energy lower bound ⟹ sharpened period lower bound.**  Feeding any provable lower bound
`E_r(G) ≥ L` into the moment-average core: there is `b ≠ 0` with
`(q·L − |G|^{2r})/(q−1) ≤ ‖η_b‖^{2r}`.  The transfer map from energy lower bounds to the prize
per-frequency object.  Requires `q > 1`. -/
theorem worstPeriod_pow_ge_of_energy_lb {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (L : ℝ) (hq : (1 : ℝ) < Fintype.card F) (hL : L ≤ (rEnergy G r : ℝ)) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * L - (G.card : ℝ) ^ (2 * r)) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ (2 * r) := by
  obtain ⟨b, hb, hge⟩ := worstPeriod_pow_ge_avg hψ G r
  refine ⟨b, hb, le_trans ?_ hge⟩
  have hq1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  -- numerator monotone in the energy: q·L − |G|^{2r} ≤ q·E_r − |G|^{2r}
  have hqpos : (0 : ℝ) ≤ (Fintype.card F : ℝ) := le_of_lt (lt_trans one_pos hq)
  have hnum : (Fintype.card F : ℝ) * L - (G.card : ℝ) ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
    linarith [mul_le_mul_of_nonneg_left hL hqpos]
  exact div_le_div_of_nonneg_right hnum hq1.le

/-! ## Clean unconditional energy lower bounds (no open input) -/

/-- **Diagonal lower bound on the additive energy.**  `E_r(G) ≥ |G|^r`: the diagonal pairs `(v,v)`
(every `v` sums to itself) already number `|G|^r`.  Fully elementary.  At `r = 1` it is exact
and the core then reproduces Parseval; for `r ≥ 2` feeding only this diagonal bound into the core
can give a weaker floor than Parseval (e.g. `n = 4`, `q = 17`, `r = 2`: `1` versus `√(13/4)`). -/
theorem rEnergy_ge_diag (G : Finset F) (r : ℕ) : G.card ^ r ≤ rEnergy G r := by
  classical
  rw [rEnergy]
  -- E_r = ∑_v ∑_w [∑v=∑w] ≥ ∑_v [∑v=∑v] = ∑_v 1 = |G|^r
  have hdiag : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => G),
      (1 : ℕ) ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G), (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
    intro v hv
    calc (1 : ℕ) = (if ∑ i, v i = ∑ i, v i then 1 else 0) := by simp
      _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G), (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
          Finset.single_le_sum (f := fun w => (if ∑ i, v i = ∑ i, w i then 1 else 0))
            (fun i _ => by positivity) hv
  calc G.card ^ r = (Fintype.piFinset (fun _ : Fin r => G)).card := by
        rw [Fintype.card_piFinset]; simp
    _ = ∑ _v ∈ Fintype.piFinset (fun _ : Fin r => G), 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G), (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
        Finset.sum_le_sum hdiag

/-- **Monotonicity of the additive energy.**  If `H ⊆ G` then `E_r(H) ≤ E_r(G)`: every pair of
`H`-tuples with equal sum is also a pair of `G`-tuples with equal sum, and `E_r` is a sum of
nonnegative indicators over `piFinset H ⊆ piFinset G`.  Lets a *subgroup* energy lower-bound the
ambient one — in particular `E_r(μ_n) ≥ E_r(μ_2) = C(2r,r)`. -/
theorem rEnergy_mono {H G : Finset F} (hHG : H ⊆ G) (r : ℕ) : rEnergy H r ≤ rEnergy G r := by
  classical
  rw [rEnergy, rEnergy]
  have hsub : Fintype.piFinset (fun _ : Fin r => H) ⊆ Fintype.piFinset (fun _ : Fin r => G) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    exact fun i => hHG (hx i)
  -- inner sums are monotone in the inner index set; outer sum is monotone via subset + nonneg
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => Nat.zero_le _))
  refine Finset.sum_le_sum (fun v _ => ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => Nat.zero_le _)

/-! ## The constant ceiling: NOT-RAMANUJAN above a `β` threshold -/

/-- **The exact-Wick energy lower bound (over-strong; false in the thin regime)** at order `r`:
`E_r(G) ≥ (2r−1)‼·|G|^r`.  This is **not** proved in characteristic `0`: the antipodal-matching
count is `(2r−1)‼·∏_{i<r}(|G| − 2i)`, and dropping the falling-factorial correction is not
justified in a lower bound because the correction is negative.  For `r = 2` and an antipodal root
group with characteristic-zero energy, `E₂ = 3n² − 3n < 3n²`; `G = {1, −1}` gives `6 < 12`
(`not_wickEnergyLowerBound_pm_one`).  Kept only as the hypothesis of the conditional theorems
`not_ramanujan_of_wickLB` / `worstPeriod_gt_two_sqrt_of_wickLB`; use the corrected
`WickFallingEnergyLowerBound` instead. -/
def WickEnergyLowerBound (G : Finset F) (r : ℕ) : Prop :=
  (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r ≤ (rEnergy G r : ℝ)

/-- **The exact Wick input fails at `G = {1, −1}`, `r = 2`.**  Here `E₂ = 6` while
`(2·2−1)‼·2² = 12` (computed in `ZMod 3`, where `{1, −1}` has its characteristic-zero energy). -/
theorem not_wickEnergyLowerBound_pm_one :
    ¬ WickEnergyLowerBound ({1, -1} : Finset (ZMod 3)) 2 := by
  have hE : rEnergy ({1, -1} : Finset (ZMod 3)) 2 = 6 := by decide
  have hc : ({1, -1} : Finset (ZMod 3)).card = 2 := by decide
  unfold WickEnergyLowerBound
  rw [hE, hc]
  norm_num

/-- The antipodal-matching value `(2r−1)‼·∏_{i<r}(n − 2i)` (truncated subtraction in `ℕ`): the
number of zero-sum `2r`-tuples obtained from a perfect matching of the positions, an injective
choice of `r` antipodal classes, and a sign for each pair, when `G = −G` has `n` elements. -/
def wickFallingValue (n r : ℕ) : ℕ :=
  Nat.doubleFactorial (2 * r - 1) * ∏ i ∈ Finset.range r, (n - 2 * i)

/-- **The corrected (falling-factorial) Wick energy lower bound** at order `r`:
`E_r(G) ≥ (2r−1)‼·∏_{i<r}(|G| − 2i)`.  It holds whenever `G = −G`, `0 ∉ G` and `char F ≠ 2`
(distinct matched antipodal tuples are distinct zero-sum tuples), but that injection is not
formalized here, so this is an explicit named hypothesis.  For `r = 2` it reads
`E₂ ≥ 3n(n − 2)`, consistent with the characteristic-zero value `3n² − 3n`. -/
def WickFallingEnergyLowerBound (G : Finset F) (r : ℕ) : Prop :=
  wickFallingValue G.card r ≤ rEnergy G r

/-- **Conditional non-Ramanujan implication from the exact-Wick input, `2r`-th-power form.**  If
`G` (`|G| = n`) satisfies `E_r(G) ≥ (2r−1)‼·n^r` (`WickEnergyLowerBound`) and the field trigger
`q·((2r−1)‼ − 4^r) ≥ n^r`, then there is a nontrivial frequency `b` with

> `(2√n)^{2r} < ‖η_b‖^{2r}`.

The implication is valid, but its energy hypothesis is false for antipodal root groups with
characteristic-zero energy (`not_wickEnergyLowerBound_pm_one`; `E₂ = 3n² − 3n`), so this theorem
does not by itself establish non-Ramanujan behaviour.  The corrected version is
`not_ramanujan_of_fallingWickLB`.

Proof: moment-average core with `L = (2r−1)‼·n^r`, then `(q·L − n^{2r})/(q−1) > 4^r·n^r = (2√n)^{2r}`
rearranges to the trigger (multiplying through by `n^r > 0`). -/
theorem not_ramanujan_of_wickLB {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hq : (1 : ℝ) < Fintype.card F) (hG : 0 < G.card) (_hr : 1 ≤ r)
    (hwick : WickEnergyLowerBound G r)
    (htrig : (G.card : ℝ) ^ r
        ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) - (4 : ℝ) ^ r)) :
    ∃ b : F, b ≠ 0 ∧ (2 * Real.sqrt (G.card)) ^ (2 * r) < ‖eta ψ G b‖ ^ (2 * r) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  set D : ℝ := (Nat.doubleFactorial (2 * r - 1) : ℝ) with hDdef
  have hnpos0 : (0 : ℝ) < n := by rw [hndef]; exact_mod_cast hG
  have hnrpos : (0 : ℝ) < n ^ r := pow_pos hnpos0 r
  -- the moment-average lower bound at L = D·n^r
  obtain ⟨b, hb, hge⟩ := worstPeriod_pow_ge_of_energy_lb hψ G r (D * n ^ r) hq hwick
  refine ⟨b, hb, lt_of_lt_of_le ?_ hge⟩
  -- compute (2√n)^{2r} = 4^r · n^r
  have hsqrt_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (le_of_lt hnpos0)
  have hexp : (2 * Real.sqrt n) ^ (2 * r) = (4 : ℝ) ^ r * n ^ r := by
    have h1 : (2 * Real.sqrt n) ^ (2 * r) = ((2 * Real.sqrt n) ^ 2) ^ r := by
      rw [← pow_mul]
    rw [h1]
    have h2 : (2 * Real.sqrt n) ^ 2 = 4 * n := by
      rw [mul_pow, hsqrt_sq]; norm_num
    rw [h2, mul_pow]
  rw [hexp]
  -- goal: 4^r·n^r < (q·(D·n^r) − n^{2r})/(q−1)
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  rw [lt_div_iff₀ hq1]
  have hn2r : n ^ (2 * r) = n ^ r * n ^ r := by rw [two_mul, pow_add]
  -- from htrig: n^r ≤ q·(D − 4^r)
  have htrig' : n ^ r ≤ q * (D - (4 : ℝ) ^ r) := by rw [hqdef, hndef, hDdef]; exact htrig
  -- 4^r·n^r·(q−1) < q·D·n^r − n^{2r}
  rw [hn2r]
  -- multiply htrig' by n^r > 0:  n^r·n^r ≤ q·(D−4^r)·n^r = q·D·n^r − q·4^r·n^r
  have hmul : n ^ r * n ^ r ≤ q * (D - (4 : ℝ) ^ r) * n ^ r :=
    mul_le_mul_of_nonneg_right htrig' (le_of_lt hnrpos)
  -- strict slack from 4^r·n^r > 0
  have hslack : (0 : ℝ) < (4 : ℝ) ^ r * n ^ r := mul_pos (by positivity) hnrpos
  nlinarith [hmul, hslack]

/-- **Conditional non-Ramanujan implication, `B > 2√n` form (exact-Wick input).**  Under the same
hypotheses as `not_ramanujan_of_wickLB`, there is a nontrivial frequency with `2√|G| < ‖η_b‖`.
Obtained from the `2r`-th-power version by strict monotonicity of `t ↦ t^{2r}` on `ℝ≥0`.  The
input `WickEnergyLowerBound` is over-strong and false for antipodal root groups with
characteristic-zero energy; see `worstPeriod_gt_two_sqrt_of_fallingWickLB` for the corrected
form. -/
theorem worstPeriod_gt_two_sqrt_of_wickLB {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hq : (1 : ℝ) < Fintype.card F) (hG : 0 < G.card) (hr : 1 ≤ r)
    (hwick : WickEnergyLowerBound G r)
    (htrig : (G.card : ℝ) ^ r
        ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) - (4 : ℝ) ^ r)) :
    ∃ b : F, b ≠ 0 ∧ 2 * Real.sqrt (G.card) < ‖eta ψ G b‖ := by
  obtain ⟨b, hb, hpow⟩ := not_ramanujan_of_wickLB hψ G r hq hG hr hwick htrig
  refine ⟨b, hb, ?_⟩
  -- a^{2r} < c^{2r} with c ≥ 0 ⟹ a < c (strict monotonicity of the (2r)-th power)
  exact lt_of_pow_lt_pow_left₀ (2 * r) (norm_nonneg _) hpow

/-! ## The corrected (falling-factorial) Wick input and its recomputed trigger -/

/-- **Conditional non-Ramanujan implication from the corrected Wick input, `2r`-th-power form.**
If `E_r(G) ≥ L := (2r−1)‼·∏_{i<r}(n − 2i)` (`WickFallingEnergyLowerBound`, `n = |G|`) and the
recomputed trigger `n^{2r} ≤ q·(L − 4^r·n^r)` holds, then some `b ≠ 0` has
`(2√n)^{2r} < ‖η_b‖^{2r}`.

Proof: moment-average core with this `L`; the trigger gives `q·L − n^{2r} ≥ q·4^r·n^r`, which is
strictly larger than `(q−1)·4^r·n^r`. -/
theorem not_ramanujan_of_fallingWickLB {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hq : (1 : ℝ) < Fintype.card F) (hG : 0 < G.card)
    (hwick : WickFallingEnergyLowerBound G r)
    (htrig : (G.card : ℝ) ^ (2 * r)
        ≤ (Fintype.card F : ℝ)
          * ((wickFallingValue G.card r : ℝ) - (4 : ℝ) ^ r * (G.card : ℝ) ^ r)) :
    ∃ b : F, b ≠ 0 ∧ (2 * Real.sqrt (G.card)) ^ (2 * r) < ‖eta ψ G b‖ ^ (2 * r) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  set L : ℝ := (wickFallingValue G.card r : ℝ) with hLdef
  have hL : L ≤ (rEnergy G r : ℝ) := by
    rw [hLdef]
    exact_mod_cast hwick
  have hnpos0 : (0 : ℝ) < n := by rw [hndef]; exact_mod_cast hG
  have hnrpos : (0 : ℝ) < n ^ r := pow_pos hnpos0 r
  obtain ⟨b, hb, hge⟩ := worstPeriod_pow_ge_of_energy_lb hψ G r L hq hL
  refine ⟨b, hb, lt_of_lt_of_le ?_ hge⟩
  have hsqrt_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (le_of_lt hnpos0)
  have hexp : (2 * Real.sqrt n) ^ (2 * r) = (4 : ℝ) ^ r * n ^ r := by
    have h1 : (2 * Real.sqrt n) ^ (2 * r) = ((2 * Real.sqrt n) ^ 2) ^ r := by
      rw [← pow_mul]
    rw [h1]
    have h2 : (2 * Real.sqrt n) ^ 2 = 4 * n := by
      rw [mul_pow, hsqrt_sq]; norm_num
    rw [h2, mul_pow]
  rw [hexp]
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  rw [lt_div_iff₀ hq1]
  have hslack : (0 : ℝ) < (4 : ℝ) ^ r * n ^ r := mul_pos (by positivity) hnrpos
  have htrig' : n ^ (2 * r) ≤ q * (L - (4 : ℝ) ^ r * n ^ r) := htrig
  nlinarith [htrig', hslack]

/-- **Conditional non-Ramanujan implication from the corrected Wick input, `B > 2√n` form.**
Under the hypotheses of `not_ramanujan_of_fallingWickLB`, some `b ≠ 0` has `2√|G| < ‖η_b‖`.  The
only non-elementary input is the named, true-but-unformalized `WickFallingEnergyLowerBound`. -/
theorem worstPeriod_gt_two_sqrt_of_fallingWickLB {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hq : (1 : ℝ) < Fintype.card F) (hG : 0 < G.card)
    (hwick : WickFallingEnergyLowerBound G r)
    (htrig : (G.card : ℝ) ^ (2 * r)
        ≤ (Fintype.card F : ℝ)
          * ((wickFallingValue G.card r : ℝ) - (4 : ℝ) ^ r * (G.card : ℝ) ^ r)) :
    ∃ b : F, b ≠ 0 ∧ 2 * Real.sqrt (G.card) < ‖eta ψ G b‖ := by
  obtain ⟨b, hb, hpow⟩ := not_ramanujan_of_fallingWickLB hψ G r hq hG hwick htrig
  exact ⟨b, hb, lt_of_pow_lt_pow_left₀ (2 * r) (norm_nonneg _) hpow⟩

end ArkLib.ProximityGap.WorstPeriodMomentAvgLower

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.worstPeriod_pow_ge_avg
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.worstPeriod_pow_ge_of_energy_lb
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.rEnergy_ge_diag
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.rEnergy_mono
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.not_ramanujan_of_wickLB
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.worstPeriod_gt_two_sqrt_of_wickLB
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.not_wickEnergyLowerBound_pm_one
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.not_ramanujan_of_fallingWickLB
#print axioms ArkLib.ProximityGap.WorstPeriodMomentAvgLower.worstPeriod_gt_two_sqrt_of_fallingWickLB
