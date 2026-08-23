/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# The prize structural constant `Λ(G)` — the single object behind BGK, Johnson, Gauss, BCHKS, Paley (#407)

Across **five different branches of mathematics** the Proximity Prize's hard core appears as the *same*
quantity. This file makes that quantity a **first-class object** — the **prize structural constant**

> `Λ²(ψ,G) := max_{b ≠ 0} ‖η_b‖²`,   `η_b = ∑_{y∈G} ψ(b·y)`   (`G = μ_n`, the smooth subgroup)

— defines it once (`prizeRadiusSq`), proves its **unconditional properties** (the worst-case-bound
predicate is *exactly* an upper bound on it; the Parseval floor `Λ² ≥ ~n` is unconditional), and names
its **single open property** (`DepthLogSubGaussian`), to which every branch's hard direction reduces.

## Why it deserves to be its own object — the five faces (all *exactly equal*, proven elsewhere in-tree)

* **Analytic number theory / BGK** — `Λ = max_{b≠0}|∑_{x∈μ_n} e_p(bx)|`, the **incomplete character-sum
  sup-norm** over a multiplicative subgroup (Bourgain–Glibichuk–Konyagin; di Benedetto–Garaev).
* **Spectral graph theory / Paley** — `Λ = λ₂(Cay(F_q, μ_n))`, the **second eigenvalue** of the
  generalized Paley graph (`GaussPeriodParsevalFloor`); `Λ ≤ 2√n ⟺` Ramanujan.
* **Additive combinatorics / BCHKS** — `∑_{b} ‖η_b‖^{2r} = q·E_r(μ_n)` (`SubgroupGaussSumMoment`), so `Λ`
  is the `L^∞` end of the **higher-additive-energy** ladder `E_r` (BCHKS Conj. 1.12 subset-sum spread).
* **Coding theory / Johnson** — via the **super-code bridge** the far-line incidence (hence `δ*`) is
  `average + (q/|V|)·𝒮` with `𝒮` the **Shaw operator** (`ShawOperator`); its worst case over far lines is
  `Λ`. The `r=1` (Parseval) rung *is* the Johnson radius `1−√ρ`.
* **Arithmetic geometry / Gauss** — by the completion identity `t·η_b = ∑_{j<t} g(χ^{dj},ψ_b)`, `Λ` is the
  sup-norm of a DFT of **Gauss sums** (each of modulus `√q`); its independence is Katz/Deligne monodromy.

These are not analogies — each is a *proven exact identity* in the cited file. `Λ` is the unique fixed
point they all name; that is the justification for promoting it to a defined object.

## Its log nature

`Λ` is the **extreme value of a deterministic, near-sub-Gaussian spectrum**: `{‖η_b‖}_{b≠0}` is a family of
`q−1` real(-ish) values with mean-square `≈ n` (the Parseval floor below), and `Λ` is their maximum. For an
i.i.d. sub-Gaussian family of size `N` with variance `n`, `max ≈ √(2n·log N)`; here `N ≈ q` frequencies, so
the conjectured `Λ ≤ √(2n·log q)` is precisely the **extreme-value / union-bound logarithm of the family
size**. *Every* branch's `log` is this same `log(#directions)`: the entropy of the search over `b`. The open
content is that the deterministic spectrum is sub-Gaussian *to depth `r ≈ log q`* (equivalently `E_r ≤
(2r−1)‼·n^r` survives the char-`p` wraparound to that depth) — a single statement, branch-independent.

## What is proven here (unconditional, axiom-clean)

* `worstCaseIncompleteSumBound_iff_prizeRadiusSq_le` — the named open predicate `WorstCaseIncompleteSumBound
  ψ G M` is **literally** `Λ² ≤ M`; so the whole prize is a *threshold on this one object*.
* `prizeRadiusSq_parseval_floor` — `Λ² ≥ (q·n − n²)/(q−1)` unconditionally (the `√n` Alon–Boppana floor;
  `max ≥ mean` over the Parseval second moment). The floor is real; only the matching `log`-ceiling is open.
* `DepthLogSubGaussian` — the **single open property** (`Λ² ≤ 2·n·log q`); the BGK/BCHKS/Paley/Johnson wall,
  now stated as one Prop on one object.

Axiom-clean (`propext, Classical.choice, Quot.sound`), no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.PrizeStructuralConstant

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonzero frequencies `F \ {0}` are nonempty (a field has `1 ≠ 0`). -/
theorem erase_zero_nonempty : (Finset.univ.erase (0 : F)).Nonempty :=
  ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ 1⟩⟩

/-- **The prize structural constant `Λ²(ψ,G) = max_{b≠0} ‖η_b‖²`.**  The single object behind the
BGK character-sum sup-norm, the Paley second eigenvalue, the BCHKS energy `L^∞`, the Shaw/Johnson
incidence worst case, and the Gauss-sum DFT max.  Defined as a `Finset.sup'` over the nonzero
frequencies. -/
noncomputable def prizeRadiusSq (ψ : AddChar F ℂ) (G : Finset F) : ℝ :=
  (Finset.univ.erase (0 : F)).sup' erase_zero_nonempty (fun b => ‖eta ψ G b‖ ^ 2)

/-- **The whole prize is a threshold on `Λ²`.**  The named open predicate `WorstCaseIncompleteSumBound
ψ G M` (`∀ b ≠ 0, ‖η_b‖² ≤ M`) is *exactly* `Λ²(ψ,G) ≤ M`.  So bounding the one structural constant `Λ`
*is* the prize core, in every branch. -/
theorem worstCaseIncompleteSumBound_iff_prizeRadiusSq_le (ψ : AddChar F ℂ) (G : Finset F) (M : ℝ) :
    WorstCaseIncompleteSumBound ψ G M ↔ prizeRadiusSq ψ G ≤ M := by
  unfold WorstCaseIncompleteSumBound prizeRadiusSq
  rw [Finset.sup'_le_iff]
  constructor
  · intro h b hb
    exact h b (Finset.mem_erase.mp hb).1
  · intro h b hb
    exact h b (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)

/-- **The unconditional Parseval floor `Λ² ≥ (q·n − n²)/(q−1)`.**  The maximum is at least the average,
and the average of `‖η_b‖²` over the `q−1` nonzero frequencies is `(q·|G| − |G|²)/(q−1)` by the exact
second moment `∑_b ‖η_b‖² = q·|G|` (with `‖η_0‖² = |G|²`).  This is the `√n` Alon–Boppana floor: the
scale of `Λ` is unavoidably `≥ √n`; only the matching `√(log q)` ceiling is open. -/
theorem prizeRadiusSq_parseval_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
      ≤ prizeRadiusSq ψ G := by
  classical
  set s : Finset F := Finset.univ.erase (0 : F) with hs
  set f : F → ℝ := fun b => ‖eta ψ G b‖ ^ 2 with hf
  -- sum over nonzero b = total − b=0 term
  have hsum_all : ∑ b : F, f b = (Fintype.card F : ℝ) * G.card :=
    subgroup_gaussSum_secondMoment hψ G
  have hz : f 0 = (G.card : ℝ) ^ 2 := by
    have he0 : eta ψ G 0 = (G.card : ℂ) := by
      simp only [eta, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [hf, he0, Complex.norm_natCast]
  have hsum_s : ∑ b ∈ s, f b = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    have : ∑ b : F, f b = f 0 + ∑ b ∈ s, f b := by
      rw [hs, Finset.add_sum_erase _ f (Finset.mem_univ 0)]
    rw [hsum_all, hz] at this; linarith
  -- max ≥ average: ∑_{b∈s} f ≤ |s| • sup'
  have hle : ∑ b ∈ s, f b ≤ s.card • prizeRadiusSq ψ G := by
    calc ∑ b ∈ s, f b ≤ ∑ _b ∈ s, prizeRadiusSq ψ G :=
          Finset.sum_le_sum (fun b hb => Finset.le_sup' f hb)
      _ = s.card • prizeRadiusSq ψ G := Finset.sum_const _
  have hcard : (s.card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have : 1 ≤ Fintype.card F := Fintype.card_pos
    push_cast [Nat.cast_sub this]; ring
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    have := Fintype.one_lt_card (α := F); rw [← hcard]
    have : 0 < s.card := Finset.card_pos.mpr erase_zero_nonempty
    positivity
  rw [div_le_iff₀ hqpos, hsum_s.symm]
  calc ∑ b ∈ s, f b ≤ s.card • prizeRadiusSq ψ G := hle
    _ = (s.card : ℝ) * prizeRadiusSq ψ G := by rw [nsmul_eq_mul]
    _ = prizeRadiusSq ψ G * ((Fintype.card F : ℝ) - 1) := by rw [hcard]; ring

/-- **The single open property of `Λ`** — `Λ² ≤ 2·n·log q` — to which the hard direction of BGK,
BCHKS Conj. 1.12, the Paley-graph conjecture, and the Johnson→capacity gap all reduce.  Stated as one
`Prop` on the one object.  (The matching floor `Λ² ≥ ~n` is proven above; this `√(log q)` ceiling is the
25-year-open content, equivalently char-`p` sub-Gaussianity of `E_r` to depth `r ≈ log q`.) -/
def DepthLogSubGaussian (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  prizeRadiusSq ψ G ≤ 2 * (G.card : ℝ) * Real.log (Fintype.card F)

end ArkLib.ProximityGap.PrizeStructuralConstant
