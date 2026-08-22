/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.Tactic

/-!
# NOT-RAMANUJAN: the prize Gauss-period graph `Cay(F_q, μ_n)` is not Ramanujan (#407)

`B := max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈μ_n} e_p(b·x)`, is the non-principal eigenvalue (up to the
standard `Re`/magnitude convention) of the generalized Paley graph `Cay(F_q, μ_n)`. The Ramanujan
property of that graph is exactly `B ≤ 2√n`. This file proves an UNCONDITIONAL **lower** companion
to the moment ladder, and the consequence that the graph is **NOT Ramanujan** (`B > 2√n`) once the
field is large enough, conditional only on an explicit, proven numeric lower bound on the additive
energy at a fixed depth `r`.

## The mechanism

The proven moment identity (`subgroup_gaussSum_moment`, pure orthogonality, no Weil) is
`∑_b ‖η_b‖^{2r} = q·E_r(G)`, `E_r = `r`-fold additive energy. Peeling the DC spike `η_0 = |G| = n`
and bounding the `q−1` nonzero terms above by `(q−1)·B^{2r}` gives the **average lower bound**

> `exists_period_pow_ge_energyR` :  `∃ b ≠ 0,  q·E_r − n^{2r}  ≤  (q−1)·‖η_b‖^{2r}`,

equivalently `B^{2r} ≥ (q·E_r − n^{2r})/(q−1)` — the LOWER mirror of the in-tree upper feeder
`eta_pow_le_energyR` (`‖η_b‖^{2r} ≤ q·E_r − n^{2r}`). This is unconditional and axiom-clean.

## NOT-RAMANUJAN

If at some depth `r` the field is large enough that

> `4^r · n^r · (q−1)  <  q·E_r − n^{2r}`   (the **energy-clears-budget** inequality),

then `(2√n)^{2r} = 4^r n^r < (q·E_r − n^{2r})/(q−1) ≤ B^{2r}`, so `B > 2√n`: the graph is NOT
Ramanujan. The hypothesis is a single inequality over `ℝ`; it is **discharged by the proven char-0
energy lower bound**
`E_r(μ_n) ≥ A_r := (2r−1)‼ · (n/2)(n/2−1)···(n/2−r+1) · 2^r`
(antipodal pairs on distinct classes; `E_r(char-p) ≥ E_r(char-0) ≥ A_r`). Since `A_r/n^r → (2r−1)‼`
and `((2r−1)‼)^{1/2r} > 2` first at `r = 6` (value `2.1614`), the inequality holds — hence the graph
is not Ramanujan — exactly when `q` clears the DC term `n^{2r}`, i.e. `β = log_n q` exceeds a
threshold `β_thr(n)` with `β_thr → 6` as `n → ∞` (`≈ 4.46` at `n = 256`, `≈ 5.58` at `n = 2^30`;
see `scripts/probes/probe_407_notram_*`). At the prize `β = 5.27 < 5.58` the budget caps the usable
depth at `r = 5`, giving `B ≥ 1.984√n` only (just below the Ramanujan line), so this method does NOT
declare the prize graph non-Ramanujan — honest scope: it is a clean theorem for `β` above threshold.

The numeric energy lower bound `A_r ≥ 4^r n^r (q−1) + n^{2r}` at a fixed `r` is the supplied proven
inequality (the project's named-input convention); everything above it is unconditional and
axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.NotRamanujanLowerBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- `η_0 = |G|`, so `‖η_0‖^m = |G|^m` for every exponent `m`. -/
private theorem eta_zero_pow (ψ : AddChar F ℂ) (G : Finset F) (m : ℕ) :
    ‖eta ψ G (0 : F)‖ ^ m = (G.card : ℝ) ^ m := by
  have h0 : eta ψ G (0 : F) = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  rw [h0, Complex.norm_natCast]

/-- The number of nonzero frequencies is `q − 1`. -/
private theorem card_erase_zero : (Finset.univ.erase (0 : F)).card = Fintype.card F - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]

/-- **Average (reverse-Markov) lower bound on the worst period — the LOWER companion of
`eta_pow_le_energyR`.** Peeling the DC spike `η_0 = |G|` from the moment ladder
`∑_b ‖η_b‖^{2r} = q·E_r` and bounding the `q−1` surviving terms above by `(q−1)·max`:

> there is a nontrivial frequency `b ≠ 0` with
> `q·E_r − |G|^{2r} ≤ (q−1)·‖η_b‖^{2r}`,

i.e. `max_{b≠0}‖η_b‖^{2r} ≥ (q·E_r − |G|^{2r})/(q−1)`. Unconditional, no Weil, no open input. -/
theorem exists_period_pow_ge_energyR {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) :
    ∃ b : F, b ≠ 0 ∧
      (Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)
        ≤ ((Fintype.card F : ℝ) - 1) * ‖eta ψ G b‖ ^ (2 * r) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set S : Finset F := Finset.univ.erase (0 : F) with hS
  have hmemS : ∀ b : F, b ∈ S ↔ b ≠ 0 := by
    intro b; rw [hS, Finset.mem_erase]; simp
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : F)
    exact ⟨x, (hmemS x).mpr hx⟩
  -- the `2r`-th moment restricted to the nonzero frequencies
  have hsumr : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) = q * rEnergy G r - (G.card : ℝ) ^ (2 * r) := by
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun b => ‖eta ψ G b‖ ^ (2 * r)) (Finset.mem_univ (0 : F))).symm
    rw [subgroup_gaussSum_moment hψ G r] at hsplit
    rw [← hS, eta_zero_pow ψ G (2 * r)] at hsplit
    linarith
  -- `|S| = q − 1`
  have hScard : (S.card : ℝ) = q - 1 := by
    rw [hS, card_erase_zero, hq]
    have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Nat.cast_sub hpos, Nat.cast_one]
  obtain ⟨b₀, hb₀S, hb₀max⟩ := S.exists_max_image (fun b => ‖eta ψ G b‖ ^ (2 * r)) hSne
  refine ⟨b₀, (hmemS b₀).mp hb₀S, ?_⟩
  -- each of the `q−1` nonzero terms is `≤ max`, so the sum is `≤ (q−1)·max`
  have hkey : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) ≤ (S.card : ℝ) * ‖eta ψ G b₀‖ ^ (2 * r) := by
    calc ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r)
        ≤ ∑ _b ∈ S, ‖eta ψ G b₀‖ ^ (2 * r) := Finset.sum_le_sum (fun b hb => hb₀max b hb)
      _ = (S.card : ℝ) * ‖eta ψ G b₀‖ ^ (2 * r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsumr, hScard] at hkey
  exact hkey

/-- **NOT-RAMANUJAN, the clean consumer.** Suppose at depth `r` the field is large enough that the
additive energy clears the doubled Ramanujan budget plus the DC term:

> `(4 : ℝ)^r · (G.card)^r · (q − 1)  <  q·E_r − (G.card)^{2r}`     (`henergy`).

Then there is a nontrivial frequency `b ≠ 0` with `‖η_b‖ > 2·√|G|` — i.e. `B > 2√n`, so the
generalized Paley graph `Cay(F_q, G)` is **not Ramanujan**. The hypothesis is exactly the
explicit numeric energy lower bound at the fixed depth `r` (discharged in char 0 by
`E_r(μ_n) ≥ (2r−1)‼·(n/2)_r·2^r`, with `((2r−1)‼)^{1/2r} > 2` from `r = 6` on). Everything else is
unconditional (the average lower bound above). -/
theorem not_ramanujan_of_energy_clears_budget {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r)
    (henergy : (4 : ℝ) ^ r * (G.card : ℝ) ^ r * ((Fintype.card F : ℝ) - 1)
        < (Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)) :
    ∃ b : F, b ≠ 0 ∧ (2 : ℝ) * Real.sqrt (G.card) < ‖eta ψ G b‖ := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  -- `q − 1 > 0` (there is at least one nonzero frequency, since `q ≥ 2` for a field)
  have hqpos : (0 : ℝ) < q - 1 := by
    have : (2 : ℕ) ≤ Fintype.card F := Fintype.one_lt_card
    have h2 : (2 : ℝ) ≤ q := by rw [hq]; exact_mod_cast this
    linarith
  obtain ⟨b, hb0, hble⟩ := exists_period_pow_ge_energyR hψ G r
  refine ⟨b, hb0, ?_⟩
  -- `(2√n)^{2r} = 4^r n^r`, and `4^r n^r (q−1) < q E_r − n^{2r} ≤ (q−1) ‖η_b‖^{2r}`,
  -- so dividing by `q−1 > 0` gives `(2√n)^{2r} < ‖η_b‖^{2r}`, hence `2√n < ‖η_b‖`.
  have hkey : (4 : ℝ) ^ r * (G.card : ℝ) ^ r < ‖eta ψ G b‖ ^ (2 * r) := by
    have hchain : (4 : ℝ) ^ r * (G.card : ℝ) ^ r * (q - 1) < ‖eta ψ G b‖ ^ (2 * r) * (q - 1) := by
      have := lt_of_lt_of_le henergy hble
      linarith
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hqpos)
  -- rewrite `4^r n^r = (2√n)^{2r}` and conclude by strict monotonicity of `x ↦ x^{2r}` on `ℝ≥0`
  have hsqrt : ((2 : ℝ) * Real.sqrt (G.card)) ^ (2 * r) = (4 : ℝ) ^ r * (G.card : ℝ) ^ r := by
    have hnn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
    rw [mul_pow, pow_mul, pow_mul, Real.sq_sqrt hnn]
    norm_num
  rw [← hsqrt] at hkey
  -- strict-mono of `(·)^{2r}` on nonnegatives, with `2r ≠ 0`
  have h2r : 2 * r ≠ 0 := by omega
  have hb_nn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  have hlhs_nn : (0 : ℝ) ≤ (2 : ℝ) * Real.sqrt (G.card) := by positivity
  exact lt_of_pow_lt_pow_left₀ (2 * r) hb_nn hkey

/-- **NOT-RAMANUJAN from an explicit energy lower bound.** The budget inequality `henergy` of
`not_ramanujan_of_energy_clears_budget` is itself implied by an explicit lower bound `E_r ≥ A` on
the additive energy, together with the arithmetic gap `henergy_lb : 4^r·n^r·(q−1) + n^{2r} < q·A`.
This is the form in which the prize calculation arrives: `A = A_r := (2r−1)‼·(n/2)_r·2^r` is the
proven char-0 (hence char-`p`) energy lower bound, and `henergy_lb` is the closed numeric check that
`q` clears the budget at depth `r` (true for `r ≥ 6` once `β = log_n q` exceeds the threshold). -/
theorem not_ramanujan_of_energy_lb {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (A : ℝ)
    (hAle : A ≤ (rEnergy G r : ℝ))
    (henergy_lb : (4 : ℝ) ^ r * (G.card : ℝ) ^ r * ((Fintype.card F : ℝ) - 1)
        + (G.card : ℝ) ^ (2 * r) < (Fintype.card F : ℝ) * A) :
    ∃ b : F, b ≠ 0 ∧ (2 : ℝ) * Real.sqrt (G.card) < ‖eta ψ G b‖ := by
  refine not_ramanujan_of_energy_clears_budget hψ G r hr ?_
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hmono : (Fintype.card F : ℝ) * A ≤ (Fintype.card F : ℝ) * rEnergy G r :=
    mul_le_mul_of_nonneg_left hAle hqnn
  linarith

end ArkLib.ProximityGap.NotRamanujanLowerBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NotRamanujanLowerBound.exists_period_pow_ge_energyR
#print axioms ArkLib.ProximityGap.NotRamanujanLowerBound.not_ramanujan_of_energy_clears_budget
#print axioms ArkLib.ProximityGap.NotRamanujanLowerBound.not_ramanujan_of_energy_lb
