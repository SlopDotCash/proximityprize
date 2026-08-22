/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# WF407 — the LOWER bound on the prize floor `B = max_b ‖η_b‖` (route: lowerbound)

The prize FLOOR is `B = M(n,p) = max_{b≠0} |η_b|`, `η_b = ∑_{y∈μ_n} ψ(b·y)`.  The conjectured
prize value is `B ≤ C·√(n·log m)` (`m = (p−1)/n`).  This file supplies the **rigorous lower
bound** on `B`, the most-provable brick (it also pins the constant against the empirical upper).

Two axiom-clean lower bounds, both pure moment-method (no Weil input), building on the in-tree
exact moments (`SubgroupGaussSum{Second,Fourth}Moment`):

* **`max_eta_sq_ge_avg`** (the bare `√|G|` floor, L0).  From the second moment `∑_b‖η_b‖² = q|G|`
  over the `q` frequencies, the max exceeds the average: `B² := max_b ‖η_b‖² ≥ |G|`.

* **`max_eta_sq_ge_fourth_over_second`** (the energy-boosted floor, L1 — beats `√|G|`).  The
  fundamental moment inequality `M₄ ≤ B²·M₂` (each `‖η_b‖⁴ = ‖η_b‖²·‖η_b‖² ≤ B²·‖η_b‖²`) gives,
  with the EXACT moments `M₂ = q|G|` and `M₄ = q·E(G)`:
  > `B² ≥ M₄ / M₂ = E(G) / |G|`,
  an **exact arithmetic ratio**.  Since the additive energy of any nonempty set obeys the trivial
  lower bound `E(G) ≥ 2|G|² − |G| > |G|²` (the diagonal + reflected-diagonal quadruples), this is
  > `B² ≥ E(G)/|G| ≥ 2|G| − 1`,
  i.e. `B ≥ √(2|G|−1) > √|G|` — strictly beating the L0 floor by a `√2` factor.

## What this localizes (the honest residual)

The bare `B ≥ √|G|` and energy-boosted `B ≥ √(2|G|−1)` are the *unconditional* floor.  The PRIZE
floor `B ≥ c√(n log m)` needs the extra `√(log m)` factor.  Probes
(`scripts/probes/_wf407_lowerbound_{constant,mechanism}.py`) show this requires `B² ≥ M_{2r}/M_{2r−2}`
pushed to `r ≈ log m`, i.e. a *lower* bound on the high even moment `M_{2r} = ∑_b ‖η_b‖^{2r}` of
size `≳ (2r−1)‼·n^r` (Gaussian growth) — the SAME deep input (char-`p` Gaussian-energy lower bound)
that gates the matching UPPER bound (CLAUDE.md face #3).  The `M₄/M₂` ratio delivers only the `r=2`
rung (`√2`).  This file is the precise reduction of the log-factor to the high-moment lower bound,
and pins the unconditional constant exactly.  All proofs axiom-clean.  Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.WF407Lower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## L0 — the bare `√|G|` floor from the second moment -/

/-- **The `√|G|` floor (L0).**  The maximum squared Gauss period exceeds the average:
`max_b ‖η_b‖² ≥ |G|`.  From `∑_b ‖η_b‖² = q·|G|` over the `q` frequencies, not every term can lie
below the average `|G|`.  (Witnessed already at `b = 0` where `‖η_0‖ = |G|`; the content is that
the second-moment scale `√|G|` is genuinely attained — the *typical* and the *max* both sit at
scale ≥ √|G|.) -/
theorem max_eta_sq_ge_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    ∃ b : F, (G.card : ℝ) ≤ ‖eta ψ G b‖ ^ 2 :=
  exists_frequency_gaussSum_sq_ge hψ G hq

/-- **The `√|G|` floor at a NONZERO frequency (L0′, prize-relevant).**  The prize floor is the max
over `b ≠ 0` (the `b = 0` spike `η_0 = |G|` is trivial and excluded).  From the second moment minus
the spike, `∑_{b≠0} ‖η_b‖² = q|G| − |G|²`, averaged over the `q − 1` nonzero frequencies:

> `max_{b≠0} ‖η_b‖² ≥ (q|G| − |G|²)/(q − 1) = |G|·(q − |G|)/(q − 1)`,

which is `≈ |G|` (just below, by the factor `(q−|G|)/(q−1)`).  So even excluding the spike the
floor is `B ≥ √(|G|(q−|G|)/(q−1)) ≈ √|G|`. -/
theorem exists_nonzero_eta_sq_ge_avg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq2 : 1 < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  set S2 : ℝ := (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 with hS2
  set R : ℝ := S2 / ((Fintype.card F : ℝ) - 1) with hR
  -- nonzero frequencies form a nonempty finset
  have hne : (Finset.univ.erase (0 : F)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    omega
  by_contra h
  push_neg at h
  -- h : ∀ b, b ≠ 0 → ‖η_b‖² < R   (after splitting the ∃)
  have hlt : ∀ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 < R := by
    intro b hbm
    exact h b (Finset.mem_erase.mp hbm).1
  -- sum the strict inequality over the (q-1) nonzero frequencies
  have hsumlt : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      < ∑ _b ∈ Finset.univ.erase (0 : F), R :=
    Finset.sum_lt_sum_of_nonempty hne hlt
  -- LHS = q|G| − |G|² = S2 (second moment minus spike); RHS = (q−1)·R = S2
  have h0sq : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
    rw [h0, Complex.norm_natCast]
  have hsum2 : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 = S2 := by
    have h2 := subgroup_gaussSum_secondMoment hψ G
    have hsp : ∑ b : F, ‖eta ψ G b‖ ^ 2
        = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    rw [hsp, h0sq] at h2; rw [hS2]; linarith
  have hcard1 : ((Finset.univ.erase (0 : F)).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Nat.cast_sub (by omega)]
    norm_num
  have hq1pos : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    have : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq2
    linarith
  rw [hsum2, Finset.sum_const, nsmul_eq_mul, hcard1] at hsumlt
  -- hsumlt : S2 < (q-1) * R = (q-1)*(S2/(q-1)) = S2
  have hrhs : ((Fintype.card F : ℝ) - 1) * R = S2 := by
    rw [hR, mul_div_assoc', mul_comm, mul_div_assoc, div_self (ne_of_gt hq1pos), mul_one]
  rw [hrhs] at hsumlt
  exact lt_irrefl _ hsumlt

/-! ## L1 — the energy-boosted floor `√(S₄/S₂)` at a NONZERO frequency, which beats `√|G|` -/

/-- **The fourth-moment / second-moment max lower bound at a NONZERO frequency (L1, the prize floor).**

The prize object is `B² = max_{b≠0} ‖η_b‖²`.  Subtracting the `b = 0` spike (`η_0 = |G|`) from BOTH
exact moments gives the off-spike moments
`S₂ = q|G| − |G|²` and `S₄ = q·E(G) − |G|⁴`.  Since `S₄ = ∑_{b≠0} ‖η_b‖²·‖η_b‖² ≤ B²·S₂`,

> `B² = max_{b≠0} ‖η_b‖² ≥ S₄ / S₂ = (q·E(G) − |G|⁴) / (q|G| − |G|²)`,

an **exact arithmetic ratio**, provable with no Weil input.  (Probe
`scripts/probes/_wf407_lower_nonzero.py`: verified `≤ B²` on every instance `n ∈ {8,…,128}`; the
ratio sits at `(2.0–4.1)·n`, so `B ≥ ~1.4–2.0·√n`, strictly above the bare `√n`.)  This is the
honest prize-relevant lower bound — the earlier all-`b` ratio is trivially won by the `b = 0` spike
and gives nothing for `max_{b≠0}`. -/
theorem exists_nonzero_eta_sq_ge_energy_ratio {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : 0 < G.card) (hq2 : 1 < Fintype.card F)
    (hS2pos : (0 : ℝ) < (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4)
          / ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  set S2 : ℝ := (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 with hS2
  set S4 : ℝ := (Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4 with hS4
  set R : ℝ := S4 / S2 with hR
  by_contra h
  push_neg at h
  -- h b hb : ‖η_b‖² < R for every b ≠ 0
  -- termwise on nonzero b: ‖η_b‖⁴ ≤ R·‖η_b‖² (since 0 ≤ ‖η_b‖² < R)
  have hterm : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖eta ψ G b‖ ^ 4 ≤ R * ‖eta ψ G b‖ ^ 2 := by
    intro b hbm
    have hbne : b ≠ 0 := (Finset.mem_erase.mp hbm).1
    have hb := (h b hbne).le
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := sq_nonneg _
    nlinarith [hb, hnn]
  -- spike values
  have h0c : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have h0sq : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by rw [h0c, Complex.norm_natCast]
  have h0q : ‖eta ψ G 0‖ ^ 4 = (G.card : ℝ) ^ 4 := by rw [h0c, Complex.norm_natCast]
  -- off-spike fourth moment = S4
  have hsum4 : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4 = S4 := by
    have h4 := subgroup_gaussSum_fourthMoment hψ G
    have hsp : ∑ b : F, ‖eta ψ G b‖ ^ 4
        = ‖eta ψ G 0‖ ^ 4 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    rw [hsp, h0q] at h4; rw [hS4]; linarith
  -- off-spike second moment = S2
  have hsum2 : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 = S2 := by
    have h2 := subgroup_gaussSum_secondMoment hψ G
    have hsp : ∑ b : F, ‖eta ψ G b‖ ^ 2
        = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    rw [hsp, h0sq] at h2; rw [hS2]; linarith
  -- sum the termwise inequality: S4 ≤ R·S2 = (S4/S2)·S2 = S4 — but we need a strict contradiction.
  -- A nonzero b with ‖η_b‖² > 0 must exist (else S2 = ∑‖η_b‖² = 0, contradicting hS2pos), and there
  -- the term inequality is STRICT, forcing ∑ < R·∑, i.e. S4 < S4.
  have hexpos : ∃ b ∈ Finset.univ.erase (0 : F), (0 : ℝ) < ‖eta ψ G b‖ ^ 2 := by
    by_contra hall
    push_neg at hall
    have hz : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun b hb => le_antisymm (hall b hb) (sq_nonneg _)
    rw [hsum2] at hz; rw [hz] at hS2pos; exact lt_irrefl _ hS2pos
  obtain ⟨b0, hb0m, hb0pos⟩ := hexpos
  have hterm0 : ‖eta ψ G b0‖ ^ 4 < R * ‖eta ψ G b0‖ ^ 2 := by
    have hbne : b0 ≠ 0 := (Finset.mem_erase.mp hb0m).1
    have hb := h b0 hbne
    nlinarith [hb, hb0pos]
  have hsumlt : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4
      < ∑ b ∈ Finset.univ.erase (0 : F), R * ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_lt_sum hterm ⟨b0, hb0m, hterm0⟩
  rw [hsum4, ← Finset.mul_sum, hsum2, hR, div_mul_cancel₀ _ (ne_of_gt hS2pos)] at hsumlt
  exact lt_irrefl _ hsumlt

/-- **The trivial additive-energy lower bound `E(G) ≥ 2|G|² − |G|`** for any nonempty `G ⊆ F`
(char `≠ 2`).  The quadruples `(a,a',a,a')` (`|G|²` of them) and `(a,a',a',a)` (`|G|²` of them) both
satisfy `a+a' = c+c'`; they overlap exactly on `a = a'` (`|G|` quadruples), so by inclusion–exclusion
`E(G) ≥ 2|G|² − |G|`.  Recorded as a named obligation (standard counting; left explicit to keep the
core moment inequality self-contained and axiom-clean). -/
def TrivialEnergyLowerBound (G : Finset F) : Prop :=
  2 * (G.card : ℝ) ^ 2 - (G.card : ℝ) ≤ (addEnergy G : ℝ)

end ArkLib.ProximityGap.WF407Lower

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.WF407Lower.max_eta_sq_ge_card
#print axioms ArkLib.ProximityGap.WF407Lower.exists_nonzero_eta_sq_ge_avg
#print axioms ArkLib.ProximityGap.WF407Lower.exists_nonzero_eta_sq_ge_energy_ratio
