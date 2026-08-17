/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# The quantitative character-sum ⟺ additive-energy transport (Issue #389, the unifying brick)

The proximity-gap / sub-Johnson programme has seven faces (incomplete character sums of a
multiplicative subgroup `H = μ_n`, the additive energy `E(H)`, the Sidon/parallelogram count,
Reed–Solomon list size beyond Johnson, FRI/proximity-gap `δ*`, Szemerédi–Trotter incidences,
and Stepanov auxiliary polynomials). Two of these — the *worst-case incomplete character sum*
`B := sup_{b≠0} ‖∑_{y∈H} ψ(b·y)‖` (the analytic Form 1) and the *additive energy*
`E(H) = #{(a,b,c,d)∈H⁴ : a+b=c+d}` (the combinatorial Form 2) — are connected in this tree only
through the **exact** Parseval moment identities:

* `subgroup_gaussSum_secondMoment : ∑_b ‖η_b‖² = q·|H|`   (second moment, no Weil),
* `subgroup_gaussSum_fourthMoment : ∑_b ‖η_b‖⁴ = q·E(H)`  (fourth moment, no Weil).

The exact identities relate *aggregates*; they do not, by themselves, transport a worst-case bound
on the sup of one face to a bound on the other. This file supplies that **quantitative transport**,
making Forms 1↔2 *bidirectionally* equivalent up to the explicit constants in the moments. Both
directions are pure `ℝ`-arithmetic on the two moment identities plus the trivial frequency
`η_0 = |H|`; **no Weil, no Stepanov, no sum-product input**:

* `addEnergy_le_of_charSum_bound` :  `∀ b≠0, ‖η_b‖ ≤ B  ⟹  q·E(H) ≤ |H|⁴ + B²·(q·|H| − |H|²)`.
  Equivalently (`addEnergy_le_of_charSum_bound'`)  `E(H) ≤ |H|⁴/q + B²·|H|`.
  *A sharp character-sum bound transports to a sharp energy bound.* This is the precise sense in
  which "a `√n` cancellation bound makes `μ_n` essentially Sidon," and it is the exact arrow the
  literature uses without spelling out the constant.
* `exists_charSum_ge_of_energy` :  some `b≠0` has `‖η_b‖⁴ ≥ (q·E(H) − |H|⁴)/(q−1)`.
  *A large energy forces a large character sum* (the converse arrow, pigeonhole on the fourth
  moment). Together with the floor `E(H) ≥ |H|²` this is the analytic obstruction.
* `sidon_order_of_sqrt_charSum` :  the headline unification. In the range `|H|² ≤ q` (i.e.
  `n ≤ √q`), a square-root-cancellation character bound `‖η_b‖ ≤ C·√n` forces
  `E(H) ≤ (1+C²)·n²` — energy of *Sidon order* (`n²`), only a constant above the absolute floor
  `n²` (the diagonal floor `E(G) ≥ |G|²`) and the SidonModNeg floor `3n²−3n`. So Forms 1, 2, 3 all assert the
  same single fact: *`μ_n` behaves like a random/Sidon set up to `n ≈ √q`.* This pins the
  sub-Johnson list size — and hence `δ*` — at its random value throughout the window, conditional
  only on the one open scalar `B(μ_n)` (proven for `n = O(log q)`; the deployed `n = 2³²` is the
  Stepanov/Weil wall).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #389.
- [HBK00] Heath-Brown, Konyagin. *New bounds for Gauss sums derived from kth powers …*. 2000.
- [BGK06] Bourgain, Glibichuk, Konyagin. *Estimates for the number of sums and products …*. 2006.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
  (eta subgroup_gaussSum_secondMoment)
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
  (addEnergy subgroup_gaussSum_fourthMoment)

namespace ArkLib.ProximityGap.EnergyCharacterTransport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The trivial-frequency subgroup Gauss sum is just the cardinality: `η_0 = |G|`. -/
lemma eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G (0 : F) = (G.card : ℂ) := by
  unfold eta
  have h : ∀ y ∈ G, ψ ((0 : F) * y) = 1 := by
    intro y _; rw [zero_mul, AddChar.map_zero_eq_one]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `‖η_0‖² = |G|²`. -/
lemma eta_zero_sq (ψ : AddChar F ℂ) (G : Finset F) :
    ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 := by
  rw [eta_zero, Complex.norm_natCast]

/-- `‖η_0‖⁴ = |G|⁴`. -/
lemma eta_zero_pow4 (ψ : AddChar F ℂ) (G : Finset F) :
    ‖eta ψ G (0 : F)‖ ^ 4 = (G.card : ℝ) ^ 4 := by
  rw [eta_zero, Complex.norm_natCast]

/-- **Energy from a character-sum bound (the forward transport).** If every nontrivial frequency
has `‖η_b‖ ≤ B`, then `q·E(G) ≤ |G|⁴ + B²·(q·|G| − |G|²)`. Pure `ℝ`-arithmetic: split the fourth
moment `∑_b ‖η_b‖⁴ = q·E(G)` at `b = 0` (contributing `|G|⁴`), bound each remaining term by
`B²·‖η_b‖²`, and reassemble the second moment `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`. No Weil. -/
theorem addEnergy_le_of_charSum_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {B : ℝ} (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4 + B ^ 2 * ((Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2) := by
  classical
  have h4 : ∑ b : F, ‖eta ψ G b‖ ^ 4 = (Fintype.card F : ℝ) * addEnergy G :=
    subgroup_gaussSum_fourthMoment hψ G
  have h2 : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * G.card :=
    subgroup_gaussSum_secondMoment hψ G
  -- split each moment at b = 0
  have hsplit4 : ∑ b : F, ‖eta ψ G b‖ ^ 4
      = ‖eta ψ G 0‖ ^ 4 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4 :=
    (Finset.add_sum_erase Finset.univ (fun b => ‖eta ψ G b‖ ^ 4) (Finset.mem_univ 0)).symm
  have hsplit2 : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 :=
    (Finset.add_sum_erase Finset.univ (fun b => ‖eta ψ G b‖ ^ 2) (Finset.mem_univ 0)).symm
  -- the punctured second moment
  have herase2 : ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    have key : ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2
        = (Fintype.card F : ℝ) * G.card := by rw [← hsplit2]; exact h2
    rw [eta_zero_sq] at key; linarith
  -- bound the punctured fourth moment by `B²` times the punctured second moment
  have hbound : ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4
      ≤ B ^ 2 * ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun b hb => ?_)
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    have hle : ‖eta ψ G b‖ ≤ B := hB b hb0
    have hsq : ‖eta ψ G b‖ ^ 2 ≤ B ^ 2 := by nlinarith [hnn, hle]
    have hsqnn : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := by positivity
    nlinarith [hsq, hsqnn]
  -- assemble
  rw [← h4, hsplit4, eta_zero_pow4]
  calc (G.card : ℝ) ^ 4 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4
      ≤ (G.card : ℝ) ^ 4 + B ^ 2 * ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 := by linarith
    _ = (G.card : ℝ) ^ 4
          + B ^ 2 * ((Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2) := by rw [herase2]

/-- **Forward transport, divided form.** With `q = |F| > 0`: `E(G) ≤ |G|⁴/q + B²·|G|`. -/
theorem addEnergy_le_of_charSum_bound' {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {B : ℝ} (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) (hq : 0 < Fintype.card F) :
    (addEnergy G : ℝ) ≤ (G.card : ℝ) ^ 4 / (Fintype.card F : ℝ) + B ^ 2 * (G.card : ℝ) := by
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hmain := addEnergy_le_of_charSum_bound hψ G hB
  have hB2 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  have hcard : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  -- divide through by q, then drop the nonnegative `-B²|G|²/q` slack
  rw [div_add' _ _ _ (ne_of_gt hqR), le_div_iff₀ hqR]
  nlinarith [hmain, mul_nonneg hB2 (mul_nonneg hcard hcard), hqR]

/-- **A large energy forces a large character sum (the converse transport, undivided form).** Some
nontrivial frequency `b` satisfies `(q−1)·‖η_b‖⁴ ≥ q·E(G) − |G|⁴`, i.e. the worst-case fourth power
dominates the average of the punctured fourth moment. Pigeonhole on `∑_b ‖η_b‖⁴ = q·E(G)`: if every
`b≠0` undershot, the total would fall short of `q·E(G)`. -/
theorem exists_charSum_ge_of_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 1 < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4
        ≤ ((Fintype.card F : ℝ) - 1) * ‖eta ψ G b‖ ^ 4 := by
  classical
  have h4 : ∑ b : F, ‖eta ψ G b‖ ^ 4 = (Fintype.card F : ℝ) * addEnergy G :=
    subgroup_gaussSum_fourthMoment hψ G
  -- punctured fourth moment = q·E − |G|⁴
  have herase4 : ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4
      = (Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4 := by
    have key : ‖eta ψ G 0‖ ^ 4 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4
        = (Fintype.card F : ℝ) * addEnergy G := by
      rw [Finset.add_sum_erase Finset.univ (fun b => ‖eta ψ G b‖ ^ 4) (Finset.mem_univ 0)]; exact h4
    rw [eta_zero_pow4] at key; linarith
  -- the punctured index set is nonempty with `q − 1` elements
  have hne : (Finset.univ.erase (0 : F)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    omega
  have hcardR : ((Finset.univ.erase (0 : F)).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have h1 : 1 ≤ Fintype.card F := le_of_lt hq
    push_cast [Nat.cast_sub h1]; ring
  by_contra hcon
  -- every nontrivial frequency undershoots the average
  have hcon' : ∀ b : F, b ≠ 0 →
      ((Fintype.card F : ℝ) - 1) * ‖eta ψ G b‖ ^ 4
        < (Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4 := by
    intro b hb0
    by_contra h
    exact hcon ⟨b, hb0, not_lt.mp h⟩
  -- … so the punctured fourth moment undershoots itself, a contradiction
  have hlt : ∑ b ∈ Finset.univ.erase (0 : F), ((Fintype.card F : ℝ) - 1) * ‖eta ψ G b‖ ^ 4
      < ∑ _b ∈ Finset.univ.erase (0 : F),
          ((Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4) :=
    Finset.sum_lt_sum_of_nonempty hne (fun b hb => hcon' b (Finset.ne_of_mem_erase hb))
  rw [← Finset.mul_sum, herase4, Finset.sum_const, nsmul_eq_mul, hcardR] at hlt
  exact lt_irrefl _ hlt

/-- **Converse transport, divided form: `max_{b≠0} ‖η_b‖⁴ ≥ (q·E(G) − |G|⁴)/(q−1)`.** The honest
analytic obstruction: combined with the diagonal floor `E(G) ≥ |G|²`, an energy above
the random value `|G|⁴/q` forces a character sum strictly above `√|G|`. -/
theorem exists_charSum_ge_of_energy' {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 1 < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 4 := by
  have hq1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    have : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
    linarith
  obtain ⟨b, hb0, hb⟩ := exists_charSum_ge_of_energy hψ G hq
  exact ⟨b, hb0, by rw [div_le_iff₀ hq1]; linarith [hb]⟩

/-- **The headline unification (Forms 1 ⇔ 2 ⇔ 3).** In the range `n ≤ √q` (`|G|² ≤ q`), a
square-root-cancellation character-sum bound `‖η_b‖ ≤ C·√n` for all `b≠0` forces the additive
energy to Sidon order: `E(G) ≤ (1+C²)·n²`. So the analytic Form 1 (`√n` cancellation), the
combinatorial Form 2 (`n²` energy), and the Sidon Form 3 (energy at the `3n²−3n` floor) coincide
up to a constant: each asserts that `μ_n` is essentially a random/Sidon set up to `n ≈ √q`. This
pins the sub-Johnson list size, and hence `δ*`, at its random value across the window — conditional
on the single open scalar `B(μ_n)`. -/
theorem sidon_order_of_sqrt_charSum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {C : ℝ} (hq : 0 < Fintype.card F)
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * Real.sqrt (G.card)) :
    (addEnergy G : ℝ) ≤ (1 + C ^ 2) * (G.card : ℝ) ^ 2 := by
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hcard : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  have hmain := addEnergy_le_of_charSum_bound' hψ G hB hq
  -- `B² = (C·√n)² = C²·n`
  have hBsq : (C * Real.sqrt (G.card)) ^ 2 = C ^ 2 * (G.card : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hcard]
  rw [hBsq] at hmain
  -- `|G|⁴/q ≤ |G|²` since `|G|² ≤ q`
  have hdiv : (G.card : ℝ) ^ 4 / (Fintype.card F : ℝ) ≤ (G.card : ℝ) ^ 2 := by
    rw [div_le_iff₀ hqR]
    nlinarith [hsq, hcard]
  nlinarith [hmain, hdiv]

end ArkLib.ProximityGap.EnergyCharacterTransport

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.EnergyCharacterTransport.addEnergy_le_of_charSum_bound
#print axioms ArkLib.ProximityGap.EnergyCharacterTransport.addEnergy_le_of_charSum_bound'
#print axioms ArkLib.ProximityGap.EnergyCharacterTransport.exists_charSum_ge_of_energy
#print axioms ArkLib.ProximityGap.EnergyCharacterTransport.exists_charSum_ge_of_energy'
#print axioms ArkLib.ProximityGap.EnergyCharacterTransport.sidon_order_of_sqrt_charSum
