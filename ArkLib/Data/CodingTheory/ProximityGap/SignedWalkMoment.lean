/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# WF2-C2 scaffold (Issue #389) — the higher additive moment as a sum of squared fibers.

Numerically-confirmed conjecture WF2-C2 ("signed-basis lattice-walk moment identity") claims, for
`n = 2^m` and primes `p` above an explicit `r`-dependent threshold, that the `2r`-th additive moment

> `E_r(μ_n) := #{(a₁,…,a_{2r}) ∈ μ_n^{2r} : a₁+…+a_r = a_{r+1}+…+a_{2r}}`

equals the number `W_r(d)` (`d = n/2`) of closed length-`2r` walks on `ℤ^d` with steps `±eⱼ`, with
the closed form `W_r(d) = (2r)!·Σ_{k₁+…+k_d=r} ∏_j 1/(kⱼ!)²`. The `r = 2` case is the landed energy
`E(μ_n) = 3n² − 3n` (`SidonModNegEnergyEquality.mu_n_additiveEnergy_eq`).

The conjecture has three layers (see the issue-389 analysis):

* **Layer 1 (combinatorial, char-free):** the additive moment equals the sum of squared fiber
  counts (the Cauchy–Schwarz input). **Proved here, axiom-clean, over any field.**
* **Layer 2 (signed-basis reduction, char 0 / large `p`):** the fiber counts over `μ_n` are the
  lattice path-counts on `ℤ^d` because `{1,ζ,…,ζ^{d−1}}` is a `ℤ`-basis with `ζ^d = −1`
  (cyclotomic `Φ_{2^m} = X^d + 1`). This is the "no nontrivial mod-`p` collision" hypothesis.
* **Layer 3 (the explicit prime threshold):** that no nontrivial `F_p`-relation holds among
  `≤ 2r`-term signed root sums below the threshold. Genuinely research-grade number theory; the
  numeric probe shows the threshold grows with both `n` and `r` (e.g. `n=8, r=3` needs `p ≥ 337`).

This file lands **Layer 1** (the structural Cauchy–Schwarz core that all sub-Johnson list-counting
inputs rest on) and the **closed-form arithmetic** that unifies the `r = 2` walk count with the
landed energy formula `3n² − 3n`. It explicitly does NOT claim Layers 2–3 (the open kernel).

## Numeric evidence (sympy, exact)
`E_r(μ_n)` over `ℂ`/`F_p`-above-threshold and the lattice walk count `W_r(d)` agree:
`(n,r,value)` = `(2,2,6) (4,2,36) (8,2,168)` (= `3n²−3n`), `(2,3,20) (4,3,400) (8,3,5120)`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #389.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.WF2SignedWalkMoment

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `2r`-th **additive moment** of a finite set `S`:
`E_r(S) = #{(f, g) ∈ (Fin r → S)² : ∑ f = ∑ g}`, the number of ordered `r`-tuple pairs from `S`
with equal sums. (`r = 2` is the additive energy; see `additiveMoment_two_eq_energy`.) -/
noncomputable def additiveMoment (S : Finset F) (r : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => S) ×ˢ Fintype.piFinset (fun _ : Fin r => S)).filter
    (fun p => (∑ i, p.1 i) = (∑ i, p.2 i))).card

/-- The **fiber count**: the number of `r`-tuples from `S` summing to a fixed value `v`. -/
noncomputable def fiberCount (S : Finset F) (r : ℕ) (v : F) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => S)).filter (fun f => (∑ i, f i) = v)).card

/-- **Layer 1 — the squared-fiber identity (the Cauchy–Schwarz input).** The `2r`-th additive moment
of `S` is the sum, over the `r`-fold sumset of `S`, of the *squares* of the fiber counts:
`E_r(S) = Σ_{v ∈ rS} (fiberCount S r v)²`. This holds over **any** field (no number theory), and is
the exact structural form in which every sub-Johnson list-counting Cauchy–Schwarz input enters. -/
theorem additiveMoment_eq_sum_fiber_sq (S : Finset F) (r : ℕ) :
    additiveMoment S r
      = ∑ v ∈ (Fintype.piFinset (fun _ : Fin r => S)).image (fun f => ∑ i, f i),
          (fiberCount S r v) ^ 2 := by
  classical
  unfold additiveMoment fiberCount
  -- Group the pairs (f,g) with ∑f = ∑g by their common sum value v.
  set P := Fintype.piFinset (fun _ : Fin r => S) with hP
  -- The filtered product is the disjoint union over v of (fiber v) ×ˢ (fiber v).
  have hcard :
      ((P ×ˢ P).filter (fun p => (∑ i, p.1 i) = (∑ i, p.2 i))).card
        = ∑ v ∈ P.image (fun f => ∑ i, f i),
            ((P.filter (fun f => (∑ i, f i) = v)) ×ˢ (P.filter (fun g => (∑ i, g i) = v))).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨⟨hp1, hp2⟩, heq⟩
        exact ⟨∑ i, p.1 i, ⟨p.1, hp1, rfl⟩, ⟨⟨hp1, rfl⟩, ⟨hp2, heq.symm⟩⟩⟩
      · rintro ⟨v, _, ⟨⟨hp1, h1⟩, ⟨hp2, h2⟩⟩⟩
        exact ⟨⟨hp1, hp2⟩, h1.trans h2.symm⟩
    · intro v _ w _ hvw
      simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_filter]
      rintro p ⟨⟨_, h1⟩, _⟩ ⟨⟨_, h2⟩, _⟩
      exact hvw (h1.symm.trans h2)
  rw [hcard]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.card_product, sq]

/-- The additive moment at `r = 2` is exactly the Mathlib-style additive energy
`E(S) = ∑_{a,b∈S} #{y∈S : (a+b)−y∈S}` used by the landed `SidonModNeg` chain. This shows the general
`additiveMoment` of WF2-C2 genuinely **subsumes** the in-tree `additiveEnergy` (hence the landed
`E(μ_n) = 3n² − 3n` is the `r = 2` instance). -/
theorem additiveMoment_two_eq_energy (S : Finset F) :
    additiveMoment S 2 = ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy S := by
  classical
  -- Step 1: rewrite the energy double sum as the card of the quadruple set
  --   Q = {((a,b),(c,d)) ∈ (S×S)×(S×S) : a+b = c+d}.
  -- Per-pair: the representation count of `a+b` equals the number of ordered pairs
  -- `(c,d) ∈ S×S` with `c+d = a+b`, via the bijection `y ↦ (y, (a+b)−y)`.
  have hrep : ∀ a b : F,
      ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount S (a + b)
        = ((S ×ˢ S).filter (fun q => a + b = q.1 + q.2)).card := by
    intro a b
    unfold ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount
    refine Finset.card_bij' (fun y _ => (y, (a + b) - y)) (fun q _ => q.1) ?_ ?_ ?_ ?_
    · rintro y hy
      rw [Finset.mem_filter] at hy
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hy.1, hy.2⟩, by ring⟩
    · rintro ⟨c, d⟩ hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      rw [Finset.mem_filter]
      refine ⟨hq.1.1, ?_⟩
      have : (a + b) - c = d := by linear_combination hq.2
      rw [this]; exact hq.1.2
    · rintro y _; rfl
    · rintro ⟨c, d⟩ hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      have : (a + b) - c = d := by linear_combination hq.2
      simp [this]
  have hEnergy :
      ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy S
        = (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
            (fun p => p.1.1 + p.1.2 = p.2.1 + p.2.2)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    unfold ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_product] at hp
    rw [hrep p.1 p.2, Finset.card_filter, Finset.sum_product]
  -- Step 2: rewrite the moment as the card of the same quadruple set via the
  --   Fin-2-tuple ↔ ordered-pair bijection (f ↦ (f 0, f 1)).
  rw [hEnergy]
  unfold additiveMoment
  refine Finset.card_bij'
    (fun p _ => ((p.1 0, p.1 1), (p.2 0, p.2 1)))
    (fun q _ => (![q.1.1, q.1.2], ![q.2.1, q.2.2]))
    ?_ ?_ ?_ ?_
  · -- forward maps into the quadruple set
    rintro ⟨f, g⟩ hfg
    rw [Finset.mem_filter, Finset.mem_product] at hfg
    obtain ⟨⟨hfm, hgm⟩, heq⟩ := hfg
    have hf := Fintype.mem_piFinset.mp hfm
    have hg := Fintype.mem_piFinset.mp hgm
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_product]
    refine ⟨⟨⟨hf 0, hf 1⟩, ⟨hg 0, hg 1⟩⟩, ?_⟩
    simpa [Fin.sum_univ_two] using heq
  · -- backward maps into the moment-pair set
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_product] at hq
    obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, heq⟩ := hq
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨Fintype.mem_piFinset.mpr ?_, Fintype.mem_piFinset.mpr ?_⟩, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · simpa [Fin.sum_univ_two] using heq
  · -- left inverse
    rintro ⟨f, g⟩ hfg
    ext1 <;> · funext i; fin_cases i <;> rfl
  · -- right inverse
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
    rfl

/-! ## Closed-form arithmetic: the `r = 2` walk count unifies with the energy `3n² − 3n`.

The conjecture's `r = 2` case states `W_2(d) = 3·(2d)² − 3·(2d)`, i.e. with `n = 2d` it is exactly
the landed energy `3n² − 3n`. We record this arithmetic identity and the `r = 2`/`r = 3` numeric
walk values (probe-verified: `W_2(d)` at `d = 1,2,3,4` is `6, 36, 90, 168`; `W_3(d)` at `d = 1,2` is
`20, 400`, and `W_3(4) = 5120`). These are the closed-form generator outputs of WF2-C2. -/

/-- The explicit `r = 2` walk values `W_2(d) = 3(2d)² − 3(2d)` match the energy `3n² − 3n` at
`n = 2,4,8,16` (`d = 1,2,4,8`): `6, 36, 168, 720`. -/
theorem walk_two_values :
    (3 * (2 * 1) ^ 2 - 3 * (2 * 1) = 6) ∧
    (3 * (2 * 2) ^ 2 - 3 * (2 * 2) = 36) ∧
    (3 * (2 * 4) ^ 2 - 3 * (2 * 4) = 168) ∧
    (3 * (2 * 8) ^ 2 - 3 * (2 * 8) = 720) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

#print axioms additiveMoment_eq_sum_fiber_sq
#print axioms additiveMoment_two_eq_energy
#print axioms walk_two_values

end ArkLib.ProximityGap.WF2SignedWalkMoment
