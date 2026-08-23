/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The value-spread second-moment lemma (BCIKS20 / KKH 2026-782 "Lemma 3")

For a finite family `𝓛` of functions `Z → V` whose distinct members agree pairwise on at most
`A` points, some evaluation point `z` sees many **distinct values**:

  `∃ z, 𝓛.card * |Z| ≤ #values(z) * (|Z| + 𝓛.card * A)`

(equivalently, `E_z[#values] ≥ ½·min(|𝓛|, |Z|/A)` — the multiplied ℕ-form proved here is the
division-free version). This is the combinatorial keystone of the quotient/DEEP lower-bound
route for proximity gaps ([CS25], [BCHKS25 §6], KKH ePrint 2026/782 Appendix A, and the
`QuotientPerPrimeInstantiation.md` note / DISPROOF_LOG O44): a list of `> q` pairwise-low-agreement
close polynomials yields, at some field point `z`, enough distinct values — i.e. enough distinct
bad scalars after quotienting.

The conclusion is *verbatim* the external input `hLq : L * q ≤ B * (q + L * A)` ("many-values
output, combinatorial") of `CandidateBridgeClaim62Loop48.prize_false_of_listDecoding_failure_full`,
with `B := (𝓛.image (· z)).card` at the spread-maximizing `z`.

Proof: one Cauchy–Schwarz over the sigma-set of (point, value) pairs. With `fib z v` the fiber
size of value `v` at point `z`: `∑ fib = |Z|·|𝓛|`, `∑ fib² = ∑_z #{(f,g) : f z = g z}
≤ |𝓛|·|Z| + |𝓛|²·A`, and the number of (point, value) pairs is `∑_z #values(z)`.
-/

namespace ArkLib.ProximityGap.ValueSpread

open Finset

variable {Z V : Type*} [Fintype Z] [DecidableEq Z] [DecidableEq V]

/-- Fiber size: the number of members of `𝓛` taking value `v` at point `z`. -/
private def fib (𝓛 : Finset (Z → V)) (z : Z) (v : V) : ℕ :=
  (𝓛.filter fun f => f z = v).card

omit [Fintype Z] [DecidableEq Z] in
/-- Per-point partition: the fibers over the realized values partition `𝓛`. -/
private lemma sum_fib (𝓛 : Finset (Z → V)) (z : Z) :
    ∑ v ∈ 𝓛.image (fun f => f z), fib 𝓛 z v = 𝓛.card :=
  (Finset.card_eq_sum_card_image (fun f => f z) 𝓛).symm

omit [Fintype Z] [DecidableEq Z] in
/-- Per-point second moment: the sum of squared fiber sizes counts the ordered pairs of
members agreeing at `z`. -/
private lemma sum_fib_sq (𝓛 : Finset (Z → V)) (z : Z) :
    ∑ v ∈ 𝓛.image (fun f => f z), (fib 𝓛 z v) ^ 2
      = ((𝓛 ×ˢ 𝓛).filter fun p => p.1 z = p.2 z).card := by
  classical
  have hmem : ∀ p ∈ (𝓛 ×ˢ 𝓛).filter (fun p => p.1 z = p.2 z),
      p.1 z ∈ 𝓛.image (fun f => f z) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_product.mp hp).1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hset : ((𝓛 ×ˢ 𝓛).filter (fun p => p.1 z = p.2 z)).filter (fun p => p.1 z = v)
      = (𝓛.filter fun f => f z = v) ×ˢ (𝓛.filter fun f => f z = v) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hav⟩
      exact ⟨⟨ha, hav⟩, hb, hab ▸ hav⟩
    · rintro ⟨⟨ha, hav⟩, hb, hbv⟩
      exact ⟨⟨⟨ha, hb⟩, hav.trans hbv.symm⟩, hav⟩
  rw [hset, Finset.card_product, fib, sq]

omit [DecidableEq Z] in
/-- Total pair count: summing the agreeing-pair count over all points and bounding the diagonal
(`|Z|` each) and off-diagonal (`≤ A` each, by hypothesis) contributions. -/
private lemma sum_pairs_le (𝓛 : Finset (Z → V)) (A : ℕ)
    (hA : ∀ f ∈ 𝓛, ∀ g ∈ 𝓛, f ≠ g →
      (Finset.univ.filter fun z : Z => f z = g z).card ≤ A) :
    ∑ z : Z, ((𝓛 ×ˢ 𝓛).filter fun p => p.1 z = p.2 z).card
      ≤ 𝓛.card * Fintype.card Z + 𝓛.card * 𝓛.card * A := by
  classical
  have hswap : ∑ z : Z, ((𝓛 ×ˢ 𝓛).filter fun p => p.1 z = p.2 z).card
      = ∑ p ∈ 𝓛 ×ˢ 𝓛, (Finset.univ.filter fun z : Z => p.1 z = p.2 z).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, Finset.sum_product]
  have hinner : ∀ f ∈ 𝓛,
      (∑ g ∈ 𝓛, (Finset.univ.filter fun z : Z => f z = g z).card)
        ≤ Fintype.card Z + 𝓛.card * A := by
    intro f hf
    rw [← Finset.add_sum_erase _ _ hf]
    have hdiag : (Finset.univ.filter fun z : Z => f z = f z).card = Fintype.card Z := by
      simp
    have hoff : (∑ g ∈ 𝓛.erase f, (Finset.univ.filter fun z : Z => f z = g z).card)
        ≤ 𝓛.card * A := by
      calc (∑ g ∈ 𝓛.erase f, (Finset.univ.filter fun z : Z => f z = g z).card)
          ≤ ∑ _g ∈ 𝓛.erase f, A := by
            refine Finset.sum_le_sum fun g hg => ?_
            have hgmem := Finset.mem_of_mem_erase hg
            have hgne := Finset.ne_of_mem_erase hg
            exact hA f hf g hgmem fun h => hgne h.symm
        _ = (𝓛.erase f).card * A := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 𝓛.card * A := by
            exact Nat.mul_le_mul_right _ (Finset.card_erase_le.trans le_rfl)
    omega
  calc (∑ f ∈ 𝓛, ∑ g ∈ 𝓛, (Finset.univ.filter fun z : Z => f z = g z).card)
      ≤ ∑ _f ∈ 𝓛, (Fintype.card Z + 𝓛.card * A) := Finset.sum_le_sum hinner
    _ = 𝓛.card * (Fintype.card Z + 𝓛.card * A) := by rw [Finset.sum_const, smul_eq_mul]
    _ = 𝓛.card * Fintype.card Z + 𝓛.card * 𝓛.card * A := by ring

omit [DecidableEq Z] in
/-- **The value-spread second-moment lemma** ([BCIKS20]; [KKH ePrint 2026/782] Lemma 3,
division-free ℕ-form). If distinct members of `𝓛 : Finset (Z → V)` agree pairwise on at most `A`
points, then some point `z` realizes enough distinct values that
`|𝓛| * |Z| ≤ #values(z) * (|Z| + |𝓛| * A)`.

With `q := |Z|`, `L := |𝓛|`, `B := #values(z)`, the conclusion is verbatim the `hLq` input of
`prize_false_of_listDecoding_failure_full` (CandidateBridgeClaim62Loop48). -/
theorem exists_eval_image_spread [Nonempty Z] (𝓛 : Finset (Z → V)) (A : ℕ)
    (hA : ∀ f ∈ 𝓛, ∀ g ∈ 𝓛, f ≠ g →
      (Finset.univ.filter fun z : Z => f z = g z).card ≤ A) :
    ∃ z : Z, 𝓛.card * Fintype.card Z
      ≤ (𝓛.image fun f => f z).card * (Fintype.card Z + 𝓛.card * A) := by
  classical
  rcases Nat.eq_zero_or_pos 𝓛.card with hL0 | hLpos
  · exact ⟨Classical.arbitrary Z, by simp [hL0]⟩
  by_contra hcon
  push Not at hcon
  -- Cauchy–Schwarz over the (point, value) sigma-set
  set S : Finset ((_ : Z) × V) := Finset.univ.sigma fun z => 𝓛.image fun f => f z with hS
  have hsum : ∑ x ∈ S, fib 𝓛 x.1 x.2 = Fintype.card Z * 𝓛.card := by
    rw [hS, Finset.sum_sigma]
    simp_rw [sum_fib]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  have hsumsq : ∑ x ∈ S, (fib 𝓛 x.1 x.2) ^ 2
      ≤ 𝓛.card * Fintype.card Z + 𝓛.card * 𝓛.card * A := by
    rw [hS, Finset.sum_sigma]
    simp_rw [sum_fib_sq]
    exact sum_pairs_le 𝓛 A hA
  have hcardS : S.card = ∑ z : Z, (𝓛.image fun f => f z).card := by
    rw [hS, Finset.card_sigma]
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun x => fib 𝓛 x.1 x.2)
  rw [hsum, hcardS] at hcs
  -- the contradiction sum: every z falls short
  have hlt : (∑ z : Z, (𝓛.image fun f => f z).card) * (Fintype.card Z + 𝓛.card * A)
      < Fintype.card Z * (𝓛.card * Fintype.card Z) := by
    rw [Finset.sum_mul]
    calc (∑ z : Z, (𝓛.image fun f => f z).card * (Fintype.card Z + 𝓛.card * A))
        < ∑ _z : Z, 𝓛.card * Fintype.card Z :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun z _ => hcon z
      _ = Fintype.card Z * (𝓛.card * Fintype.card Z) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  -- chain: (qL)² ≤ (∑Bz)·(Lq + L²A) = (∑Bz)·(q + LA)·L < q·L·q·L = (qL)²
  have hchain : (Fintype.card Z * 𝓛.card) ^ 2
      < (Fintype.card Z * 𝓛.card) ^ 2 := by
    calc (Fintype.card Z * 𝓛.card) ^ 2
        ≤ (∑ z : Z, (𝓛.image fun f => f z).card)
            * (𝓛.card * Fintype.card Z + 𝓛.card * 𝓛.card * A) :=
          le_trans hcs (Nat.mul_le_mul_left _ hsumsq)
      _ = (∑ z : Z, (𝓛.image fun f => f z).card)
            * (Fintype.card Z + 𝓛.card * A) * 𝓛.card := by ring
      _ < Fintype.card Z * (𝓛.card * Fintype.card Z) * 𝓛.card :=
          mul_lt_mul_of_pos_right hlt hLpos
      _ = (Fintype.card Z * 𝓛.card) ^ 2 := by ring
  exact absurd hchain (lt_irrefl _)

omit [DecidableEq Z] in
/-- Half-min corollary, first branch (the `|𝓛| ≤ |Z|/A` regime): if `|𝓛|·A ≤ |Z|`, some point
realizes at least `|𝓛|/2` distinct values (ℕ-form: `|𝓛| ≤ 2·#values(z)`). -/
theorem exists_eval_image_half_card [Nonempty Z] (𝓛 : Finset (Z → V)) (A : ℕ)
    (hA : ∀ f ∈ 𝓛, ∀ g ∈ 𝓛, f ≠ g →
      (Finset.univ.filter fun z : Z => f z = g z).card ≤ A)
    (hreg : 𝓛.card * A ≤ Fintype.card Z) :
    ∃ z : Z, 𝓛.card ≤ 2 * (𝓛.image fun f => f z).card := by
  obtain ⟨z, hz⟩ := exists_eval_image_spread 𝓛 A hA
  refine ⟨z, ?_⟩
  have hq : 0 < Fintype.card Z := Fintype.card_pos
  have h2 : 𝓛.card * Fintype.card Z
      ≤ (𝓛.image fun f => f z).card * (2 * Fintype.card Z) := by
    calc 𝓛.card * Fintype.card Z
        ≤ (𝓛.image fun f => f z).card * (Fintype.card Z + 𝓛.card * A) := hz
      _ ≤ (𝓛.image fun f => f z).card * (Fintype.card Z + Fintype.card Z) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left hreg _)
      _ = (𝓛.image fun f => f z).card * (2 * Fintype.card Z) := by ring
  have := Nat.le_of_mul_le_mul_right
    (by calc 𝓛.card * Fintype.card Z
          ≤ (𝓛.image fun f => f z).card * (2 * Fintype.card Z) := h2
        _ = 2 * (𝓛.image fun f => f z).card * Fintype.card Z := by ring) hq
  exact this

end ArkLib.ProximityGap.ValueSpread
