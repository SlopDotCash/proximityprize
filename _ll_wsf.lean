/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTDoubleSlice
import ArkLib.Data.CodingTheory.ProximityGap.CRTPacketMinpoly
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnSquarefreePQ

/-!
# Issue #232 — de Bruijn 1953 WEIGHTED, squarefree two-prime case (grid form, O100)

The post-O99 frontier named "(a) the weighted classification at TWO-prime moduli"
as the gate to cofactor/multi-prime de Bruijn work.  This file lands its base
case — **de Bruijn's actual 1953 theorem with ℕ-multiplicities at `n = p·q`**, on
the CRT grid:

    `∑_{i<p, j<q} W i j · ξ^i · η^j = 0   ⟺   ∃ α β : ℕ → ℕ,
        W i j = α i + β j  (for all i < p, j < q)`

(`ξ, η` primitive `p`-th/`q`-th roots, char 0, `p ≠ q` primes).  The forward
POSITIVITY — nonnegative `α, β` exist, not merely integer ones — is the genuine
de Bruijn content; the witness is constructive (the argmin shift).

Mechanism (pure composition of landed engines, no new analytic content):
* the `ℚ(ξ)`-valued column sums `A j = ∑_i W i j · ξ^i` are ALL EQUAL:
  `CRTDoubleSlice.slice_of_packet_minpoly` (the weight-general slice engine) at
  `minpoly_{ℚ(ξ)} η = Φ_q`
  (`CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet`, `a = b = 1`);
* equal columns + prime-level ℚ-rigidity
  (`DeBruijnSquarefreePQ.vanishing_combination_const`) give the MODULAR EQUATION
  `W i j + W 0 0 = W i 0 + W 0 j`;
* the argmin shift `α i = W i 0 − min_i W i 0`, `β j = W i₀ j` is nonnegative and
  reproduces `W` (pure `omega` from the modular equation);
* converse: both parts die against the full geometric sums.

Corollary: the **weighted Lam–Leung ℕ-span law at `pq`** — the total weight of any
vanishing ℕ-weighted sum lies in `ℕ·q + ℕ·p`.

Falsified first: `scripts/probes/probe_weighted_squarefree_grid.py` (exact
arithmetic in `ℤ[x,y]/(Φ_p, Φ_q)`, exit 0): the iff EXHAUSTIVELY over full weight
boxes at `(p,q,B) = (2,3,3), (3,2,3), (2,5,2), (5,2,2), (3,5,1)` (vanishing family
= decomposable family, set identity), the modular equation and the argmin-shift
recipe verified on every vanishing `W`, bump/unit controls live.

## Honest scope

Squarefree `p·q` on the grid surface.  Remaining for the full weighted de Bruijn
at `p^a·q^b`: the exponent-surface transport (weighted `gridSet`/`gridMap`) and
the weighted digit descent (`ThreadSplit` restated for weights) — assembly-shaped;
beyond two primes the ℕ-span theorem is genuinely open (de Bruijn's conjecture is
false in general; Lam–Leung territory).
-/

namespace DeBruijnWeightedSquarefree

open Polynomial Finset IntermediateField

variable {L : Type*} [Field L] [CharZero L]

/-- **The equal-columns step**: a vanishing ℕ-weighted grid sum has all its
`ℚ(ξ)`-valued column sums equal — the weight-general slice engine fired at the
coprime packet minimal polynomial `minpoly_{ℚ(ξ)} η = Φ_q`. -/
lemma column_sums_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℕ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (W i j : L) * ξ ^ i * η ^ j = 0)
    {j j' : ℕ} (hj : j < q) (hj' : j' < q) :
    ∑ i ∈ Finset.range p, (W i j : L) * ξ ^ i
      = ∑ i ∈ Finset.range p, (W i j' : L) * ξ ^ i := by
  classical
  have hξ1 : IsPrimitiveRoot ξ (p ^ 1) := by rwa [pow_one]
  have hη1 : IsPrimitiveRoot η (q ^ 1) := by rwa [pow_one]
  have hmin : minpoly ℚ⟮ξ⟯ η
      = ∑ t ∈ Finset.range q, (X : Polynomial ℚ⟮ξ⟯) ^ (t * 1) := by
    have h := CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet
      hp hq hpq one_pos hξ1 hη1
    simpa using h
  set g : ℚ⟮ξ⟯ := IntermediateField.AdjoinSimple.gen ℚ ξ with hg
  have hmapA : ∀ c : ℕ,
      algebraMap ℚ⟮ξ⟯ L (∑ i ∈ Finset.range p, (W i c : ℚ⟮ξ⟯) * g ^ i)
        = ∑ i ∈ Finset.range p, (W i c : L) * ξ ^ i := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_natCast, hg,
      IntermediateField.AdjoinSimple.algebraMap_gen]
  have hsumA : ∑ c ∈ Finset.range (q * 1),
      (∑ i ∈ Finset.range p, (W i c : ℚ⟮ξ⟯) * g ^ i) • η ^ c = 0 := by
    rw [mul_one]
    have hswap : ∑ c ∈ Finset.range q,
        (∑ i ∈ Finset.range p, (W i c : ℚ⟮ξ⟯) * g ^ i) • η ^ c
        = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (W i j : L) * ξ ^ i * η ^ j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Algebra.smul_def, hmapA, Finset.sum_mul]
    rw [hswap]
    exact hsum
  have hAeq := CRTDoubleSlice.slice_of_packet_minpoly hmin hsumA hj hj'
    Nat.zero_lt_one
  simp only [mul_one, add_zero] at hAeq
  have hmapped := congrArg (algebraMap ℚ⟮ξ⟯ L) hAeq
  rwa [hmapA, hmapA] at hmapped

/-- **The modular equation**: a vanishing ℕ-weighted grid sum satisfies
`W i j + W 0 0 = W i 0 + W 0 j` — equal columns plus prime-level ℚ-rigidity. -/
lemma modular_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℕ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (W i j : L) * ξ ^ i * η ^ j = 0) :
    ∀ i < p, ∀ j < q, W i j + W 0 0 = W i 0 + W 0 j := by
  intro i hi j hj
  have hcol := column_sums_eq hp hq hpq hξ hη W hsum hj hq.pos
  have hdiff : ∑ i' ∈ Finset.range p,
      algebraMap ℚ L ((W i' j : ℚ) - (W i' 0 : ℚ)) * ξ ^ i' = 0 := by
    have hterm : ∀ i' ∈ Finset.range p,
        algebraMap ℚ L ((W i' j : ℚ) - (W i' 0 : ℚ)) * ξ ^ i'
          = (W i' j : L) * ξ ^ i' - (W i' 0 : L) * ξ ^ i' := by
      intro i' _
      rw [map_sub, map_natCast, map_natCast, sub_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hcol, sub_self]
  obtain ⟨c, hc⟩ := DeBruijnSquarefreePQ.vanishing_combination_const hp hξ
    (fun i' => (W i' j : ℚ) - (W i' 0 : ℚ)) hdiff
  have h1 := hc i hi
  have h2 := hc 0 hp.pos
  have h4 : (W i j : ℚ) + (W 0 0 : ℚ) = (W i 0 : ℚ) + (W 0 j : ℚ) := by
    have h3 : (W i j : ℚ) - (W i 0 : ℚ) = (W 0 j : ℚ) - (W 0 0 : ℚ) := by
      rw [h1, ← h2]
    linarith
  exact_mod_cast h4

/-- **DE BRUIJN 1953, WEIGHTED SQUAREFREE TWO-PRIME CASE (grid form)**: an
ℕ-weighted sum over the `p × q` root-of-unity grid vanishes **iff** the weight
matrix splits as a sum of a row function and a column function with NONNEGATIVE
values — the ℕ-combination of full prime packets, with the positivity (the genuine
de Bruijn content) witnessed constructively by the argmin shift. -/
theorem debruijn_weighted_squarefree {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℕ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (W i j : L) * ξ ^ i * η ^ j = 0) ↔
      ∃ α β : ℕ → ℕ, ∀ i < p, ∀ j < q, W i j = α i + β j := by
  constructor
  · intro hsum
    have hmod := modular_eq hp hq hpq hξ hη W hsum
    obtain ⟨i₀, hi₀mem, hi₀min⟩ := Finset.exists_min_image (Finset.range p)
      (fun i => W i 0) ⟨0, Finset.mem_range.mpr hp.pos⟩
    have hi₀p : i₀ < p := Finset.mem_range.mp hi₀mem
    refine ⟨fun i => W i 0 - W i₀ 0, fun j => W i₀ j, fun i hi j hj => ?_⟩
    have h1 := hmod i hi j hj
    have h2 := hmod i₀ hi₀p j hj
    have h3 := hi₀min i (Finset.mem_range.mpr hi)
    simp only at h3 ⊢
    omega
  · rintro ⟨α, β, hαβ⟩
    have hsplit : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (W i j : L) * ξ ^ i * η ^ j
        = (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (α i : L) * ξ ^ i * η ^ j)
          + ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
              (β j : L) * ξ ^ i * η ^ j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hαβ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
      push_cast
      ring
    have hpart1 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (α i : L) * ξ ^ i * η ^ j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, hη.geom_sum_eq_zero hq.one_lt, mul_zero]
    have hpart2 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (β j : L) * ξ ^ i * η ^ j = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hterm : ∀ i ∈ Finset.range p,
          (β j : L) * ξ ^ i * η ^ j = (β j : L) * η ^ j * ξ ^ i := by
        intro i _
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        hξ.geom_sum_eq_zero hp.one_lt, mul_zero]
    rw [hsplit, hpart1, hpart2, add_zero]

/-- **The weighted Lam–Leung ℕ-span law at `p·q`**: the total weight of a
vanishing ℕ-weighted grid sum lies in `ℕ·q + ℕ·p` (whole packets, counted with
multiplicity). -/
theorem weighted_total_span {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℕ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (W i j : L) * ξ ^ i * η ^ j = 0) :
    ∃ A B : ℕ, ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, W i j
      = A * q + B * p := by
  obtain ⟨α, β, hαβ⟩ :=
    (debruijn_weighted_squarefree hp hq hpq hξ hη W).mp hsum
  refine ⟨∑ i ∈ Finset.range p, α i, ∑ j ∈ Finset.range q, β j, ?_⟩
  have hstep : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, W i j
      = ∑ i ∈ Finset.range p, (α i * q + ∑ j ∈ Finset.range q, β j) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hrow : ∑ j ∈ Finset.range q, W i j
        = ∑ j ∈ Finset.range q, (α i + β j) :=
      Finset.sum_congr rfl fun j hj =>
        hαβ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
    rw [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_comm]
  rw [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.sum_mul, mul_comm p _]

/-! ## Teeth (fired at `ℂ`, `p = 2`, `q = 3`) -/

private lemma exp_two_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (2 : ℕ))) 2 :=
  Complex.isPrimitiveRoot_exp 2 (by norm_num)

private lemma exp_three_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))) 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- The converse FIRED at `ℂ`: the all-ones weight matrix (a genuine multiplicity,
every cell weighted) vanishes — produced by the split `α ≡ 1`, `β ≡ 0`. -/
example : ∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 3,
    ((1 : ℕ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / (2 : ℕ)) ^ i
      * Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ^ j = 0 := by
  refine (debruijn_weighted_squarefree Nat.prime_two Nat.prime_three
    (by norm_num) exp_two_primitive exp_three_primitive (fun _ _ => 1)).mpr ?_
  exact ⟨fun _ => 1, fun _ => 0, fun i _ j _ => rfl⟩

/-- The forward direction FIRED (with teeth): the unit matrix cannot vanish — a
decomposition would force `1 = α 0 + β 0` with `α 0 = β 0 = 0`. -/
example : ¬ (∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 3,
    ((if i = 0 ∧ j = 0 then 1 else 0 : ℕ) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I / (2 : ℕ)) ^ i
      * Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ^ j = 0) := by
  intro hcon
  obtain ⟨α, β, hαβ⟩ := (debruijn_weighted_squarefree Nat.prime_two
    Nat.prime_three (by norm_num) exp_two_primitive exp_three_primitive
    (fun i j => if i = 0 ∧ j = 0 then 1 else 0)).mp hcon
  have h00 := hαβ 0 (by norm_num) 0 (by norm_num)
  have h01 := hαβ 0 (by norm_num) 1 (by norm_num)
  have h10 := hαβ 1 (by norm_num) 0 (by norm_num)
  norm_num at h00 h01 h10
  omega

end DeBruijnWeightedSquarefree

#print axioms DeBruijnWeightedSquarefree.column_sums_eq
#print axioms DeBruijnWeightedSquarefree.modular_eq
#print axioms DeBruijnWeightedSquarefree.debruijn_weighted_squarefree
#print axioms DeBruijnWeightedSquarefree.weighted_total_span
