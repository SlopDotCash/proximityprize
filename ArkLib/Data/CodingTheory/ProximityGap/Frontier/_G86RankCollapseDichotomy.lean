/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# G86: rank-collapse dichotomy — generic planting of bad scalars is formally capped
  at `2(n−k)/(t−k) − 1` (#466 / #507)

Abstract Lean core of the G85 **linear-channel planting law** measured in
`scripts/probes/probe_rate_half_predecessor_count_largefield.py` and documented in
`docs/kb/deltastar-466-g85-wall-hypothesis-largefield-probe-2026-07-10.md`.

## The concrete law being abstracted

For a stack `(u₀, u₁)` over `F_p` and RS parameters `(n, k)` with agreement threshold `t`,
a scalar `γ` is *bad via `(S, c)`* iff the codeword `c` agrees with the line `u₀ + γ·u₁`
on the `t`-subset `S`.  For fixed `S`, "some codeword agrees on `S`" is the vanishing of
`t − k` GRS parity checks (dual of `RS_k` on `t` points), each **affine in γ** once the
stack is unknown: planting `r` distinct bad `γⱼ` via subsets `S_j` imposes `r·(t−k)`
homogeneous linear constraint rows on the stack `(u₀, u₁) ∈ F^{2n}`.  The kernel always
contains the `2k`-dimensional codeword-pair space (never bad), so the constraints act on
the `2(n−k)`-dimensional **syndrome space**, and a genuinely bad stack exists iff the
constraint rows do NOT span that space (rank `< 2(n−k)`).  Generically (independent rows)
this caps the plantable count at

  `r_max = 2(n−k)/(t−k) − 1`   (= 15 at `n=32, t−k=2`; = 31 at `n=64, t−k=2`;
                                 = 63 at production `2(n−k)=2^30, t−k=2^24+1`),

exactly the caps measured 8/8 and 9/9 by the G85 probe (`planted-r15` and `planted-r31` succeed at
rank `2(n−k) − 2`; `r+1, r+2` are UNPLANTABLE at full rank `2(n−k)`).

## Abstraction level

We do NOT re-formalize the GRS syndrome machinery.  The mathematical core is pure linear
algebra over an arbitrary field `F` and finite-dimensional syndrome space `V`
(concretely `V = F^{2(n−k)}`, `finrank F V = 2(n−k)`):

* each of the `r` planted scalars contributes `m = t − k` constraint **functionals**
  `φ (i, j) : Module.Dual F V` (the `j`-th GRS parity row of witness `i`, with the `γᵢ`
  weighting folded in — this is exactly the row `vec` built in `make_planted` of the
  probe, read modulo the codeword-pair kernel);
* a stack is *plantable* iff some **nonzero** syndrome vector is annihilated by all
  `r·m` functionals (`Plantable` below = "rank < 2(n−k)" in the probe);
* *generic position* = the `r·m` functionals are linearly independent
  (`LinearIndependent F φ`), which is the generic-rank situation the probe certifies.

## What is proved (all unconditional, axiom-clean)

* `constraint_card_le_finrank` — pigeonhole seal: independent constraint rows force
  `r·m ≤ dim V`.  Hence `dependence_certificate_of_overbudget`: if `r·m > dim V` there is
  an **explicit nontrivial dependence certificate** `c` with `∑ c p • φ p = 0` — a
  defined syzygy object among the witnesses `(Sᵢ, cᵢ)` that consumers can attack.
* `plantable_linearIndependent_cap` — the sharp `−1`: a plantable, generic-position
  family satisfies `r·m + 1 ≤ dim V` (the annihilated nonzero vector costs one full
  dimension: all rows live in the dual annihilator of its span, of dimension `dim V − 1`).
* `plantable_dichotomy` — the DICHOTOMY: any plantable family of `r` witnesses satisfies
  EITHER `r·m + 1 ≤ dim V` (i.e. `r ≤ (dim V − 1)/m ≤ 2(n−k)/(t−k) − 1`) OR its
  constraint rows carry an explicit nontrivial linear dependence (rank collapse).
* `plantable_generic_cap` — consumer form: generic-position plantable witnesses force
  `r ≤ (dim V − 1)/m`.
* `generic_planting_cap_n32 / _n64 / _production` — the three measured caps 15 / 31 / 63
  instantiated exactly (`dim V = 2(n−k) = 32, 64, 2^30`; `m = t−k = 2, 2, 2^24+1`).

## Honest scope

This kills the **generic-planting channel formally**: no adversary can plant more than
`2(n−k)/(t−k) − 1` distinct bad scalars while keeping the constraint rows in generic
position — matching the G85 measurements exactly.  It **localizes** any production
counterexample to the *rank-collapse/syzygy* configurations: to beat the cap, the
witnesses `(Sᵢ, cᵢ)` must produce a nontrivial linear dependence among their GRS
constraint rows (the certificate object exhibited here).  It does **NOT** prove the wall
hypothesis of `firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`:
rank-collapse configurations remain unexcluded (as do combinatorial channels at small
`p`), and the bridge from this abstract model to the concrete `mcaEvent` count is the
probe's exact reduction, not a Lean theorem.  CORE remains OPEN.

Honesty: no `sorry`, no `axiom`, no `native_decide`; `#print axioms` per theorem.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy

open Module Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {r m : ℕ}

/-- A planting configuration is *plantable* iff some **nonzero** syndrome vector is
annihilated by every constraint functional — the abstract form of the probe's
"`rank < 2(n−k)`, so a non-codeword-pair solution exists" condition. -/
def Plantable (φ : Fin r × Fin m → Module.Dual F V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ p : Fin r × Fin m, φ p v = 0

/-- **Pigeonhole seal.** Linearly independent constraint rows (generic position) force
`r·m ≤ dim V`: the total syndrome budget bounds the number of fresh parity constraints. -/
theorem constraint_card_le_finrank {φ : Fin r × Fin m → Module.Dual F V}
    (h : LinearIndependent F φ) : r * m ≤ finrank F V := by
  have hcard := h.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin, Subspace.dual_finrank_eq] using hcard

/-- **Explicit syzygy.** If the witnesses over-spend the syndrome budget
(`r·m > dim V`), their constraint rows carry a nontrivial linear dependence — a
concrete certificate `c` consumers can attack. -/
theorem dependence_certificate_of_overbudget {φ : Fin r × Fin m → Module.Dual F V}
    (h : finrank F V < r * m) :
    ∃ c : Fin r × Fin m → F,
      (∑ p : Fin r × Fin m, c p • φ p = 0) ∧ ∃ p : Fin r × Fin m, c p ≠ 0 := by
  have hnli : ¬ LinearIndependent F φ := fun hli =>
    absurd (constraint_card_le_finrank hli) (by omega)
  exact Fintype.not_linearIndependent_iff.mp hnli

/-- **The sharp `−1`.** A plantable family in generic position satisfies
`r·m + 1 ≤ dim V`: the annihilated nonzero vector forces every constraint row into the
dual annihilator of its span, a hyperplane of the dual space (dimension `dim V − 1`).
This is the exact source of the `−1` in `r_max = 2(n−k)/(t−k) − 1`. -/
theorem plantable_linearIndependent_cap {φ : Fin r × Fin m → Module.Dual F V}
    (hp : Plantable φ) (h : LinearIndependent F φ) : r * m + 1 ≤ finrank F V := by
  obtain ⟨v, hv, hann⟩ := hp
  set W : Subspace F (Module.Dual F V) := (F ∙ v).dualAnnihilator with hW
  have hmem : ∀ p : Fin r × Fin m, φ p ∈ W := by
    intro p
    rw [hW, Submodule.mem_dualAnnihilator]
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [hann p]
  set ψ : Fin r × Fin m → W := fun p => ⟨φ p, hmem p⟩ with hψ
  have hψli : LinearIndependent F ψ := by
    refine LinearIndependent.of_comp W.subtype ?_
    have : (W.subtype ∘ ψ) = φ := by funext p; simp [hψ]
    rwa [this]
  have hcard : r * m ≤ finrank F W := by
    have := hψli.fintype_card_le_finrank
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  have hsplit : finrank F (F ∙ v) + finrank F W = finrank F V :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq (F ∙ v)
  have hone : finrank F (F ∙ v) = 1 := finrank_span_singleton hv
  omega

/-- **The G86 rank-collapse dichotomy.** Any plantable family of `r` witnesses, each
contributing `m = t − k` constraint rows in a syndrome space of dimension
`dim V = 2(n−k)`, satisfies EITHER the generic cap `r·m + 1 ≤ dim V`
(so `r ≤ (2(n−k) − 1)/(t−k)`, i.e. `r ≤ 2(n−k)/(t−k) − 1` on the exact-division cells)
OR its constraint rows carry an explicit nontrivial linear dependence (rank collapse):
a `c ≠ 0` with `∑ c p • φ p = 0`. -/
theorem plantable_dichotomy {φ : Fin r × Fin m → Module.Dual F V} (hp : Plantable φ) :
    r * m + 1 ≤ finrank F V ∨
      ∃ c : Fin r × Fin m → F,
        (∑ p : Fin r × Fin m, c p • φ p = 0) ∧ ∃ p : Fin r × Fin m, c p ≠ 0 := by
  by_cases h : LinearIndependent F φ
  · exact Or.inl (plantable_linearIndependent_cap hp h)
  · exact Or.inr (Fintype.not_linearIndependent_iff.mp h)

/-- **Consumer form of the cap.** Generic-position (linearly independent rows) plantable
witnesses force `r ≤ (dim V − 1)/m` — with `dim V = 2(n−k)`, `m = t−k` this is
`r ≤ (2(n−k) − 1)/(t−k)`, the floor form of `2(n−k)/(t−k) − 1`. -/
theorem plantable_generic_cap {φ : Fin r × Fin m → Module.Dual F V} (hm : 0 < m)
    (hp : Plantable φ) (h : LinearIndependent F φ) : r ≤ (finrank F V - 1) / m := by
  have hcap := plantable_linearIndependent_cap hp h
  rw [Nat.le_div_iff_mul_le hm]
  omega

/-! ## The three measured caps (G85 probe), instantiated exactly

`n = 32, k = 16, t = 18`: syndrome dimension `2(n−k) = 32`, `m = t−k = 2`, cap `15`
(probe: `planted-r15` succeeds, `r16/r17` UNPLANTABLE, 8/8 primes through `2^40`). -/
theorem generic_planting_cap_n32 {φ : Fin r × Fin 2 → Module.Dual F V}
    (hD : finrank F V = 2 * (32 - 16)) (hp : Plantable φ) (h : LinearIndependent F φ) :
    r ≤ 15 := by
  have := plantable_linearIndependent_cap hp h
  rw [hD] at this
  omega

/-- `n = 64, k = 32, t = 34`: syndrome dimension `2(n−k) = 64`, `m = t−k = 2`, cap `31`
(probe: `planted-r31` succeeds, `r32/r33` UNPLANTABLE, 9/9 primes through `2^80`). -/
theorem generic_planting_cap_n64 {φ : Fin r × Fin 2 → Module.Dual F V}
    (hD : finrank F V = 2 * (64 - 32)) (hp : Plantable φ) (h : LinearIndependent F φ) :
    r ≤ 31 := by
  have := plantable_linearIndependent_cap hp h
  rw [hD] at this
  omega

/-- Production shape `n = 2^30, k = 2^29, t − k = 2^24 + 1`: syndrome dimension
`2(n−k) = 2^30`, `m = 2^24 + 1`, cap `⌊(2^30 − 1)/(2^24 + 1)⌋ = 63 ≪ 2^30` budget. -/
theorem generic_planting_cap_production {φ : Fin r × Fin (2 ^ 24 + 1) → Module.Dual F V}
    (hD : finrank F V = 2 ^ 30) (hp : Plantable φ) (h : LinearIndependent F φ) :
    r ≤ 63 := by
  have := plantable_linearIndependent_cap hp h
  rw [hD] at this
  -- r * (2^24 + 1) + 1 ≤ 2^30  ⟹  r ≤ 63
  omega

/-- Arithmetic cross-checks: the floor form `(2(n−k) − 1)/(t−k)` equals the probe's
`2(n−k)/(t−k) − 1` on the exact-division cells and gives `63` at production shape. -/
example : (2 * (32 - 16) - 1) / 2 = 2 * (32 - 16) / 2 - 1 := by norm_num
example : (2 * (64 - 32) - 1) / 2 = 2 * (64 - 32) / 2 - 1 := by norm_num
example : (2 ^ 30 - 1) / (2 ^ 24 + 1) = 63 := by norm_num

end ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.constraint_card_le_finrank
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.dependence_certificate_of_overbudget
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.plantable_linearIndependent_cap
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.plantable_dichotomy
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.plantable_generic_cap
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.generic_planting_cap_n32
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.generic_planting_cap_n64
#print axioms ArkLib.ProximityGap.Frontier.G86RankCollapseDichotomy.generic_planting_cap_production
