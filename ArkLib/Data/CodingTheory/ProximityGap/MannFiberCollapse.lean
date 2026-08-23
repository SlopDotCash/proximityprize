/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTDoubleSlice
import ArkLib.Data.CodingTheory.ProximityGap.CoprimePacketMinpoly

/-!
# Hypothesis K5 (O124/O116 kernel) — MANN'S FIBER COLLAPSE AT A SPLIT PRIME

The Lam–Leung positivity arc (O110 squarefree reduction → O116 minimal-sum reduction,
in-tree as `MinimalVanishingReduction.lam_leung_iff_minimal`) bottoms out in the
Conway–Jones/Mann minimal-sum structure theory, never formalized anywhere.  Mann's
induction step is: for `n = p * m` with `p` prime and `p ∤ m`, a vanishing sum over
`μ_n` groups by `ζ_p`-power into `p` fiber coordinates lying in `ℚ(ζ_m)`, and the
`ℚ(ζ_m)`-linear independence of `1, ζ_p, …, ζ_p^{p-2}` — i.e. that `Φ_p` STAYS the
minimal polynomial of `ζ_p` over the coprime cyclotomic field `ℚ(ζ_m)` — forces all
`p` fiber projections to COINCIDE (the all-ones relation `Φ_p(ζ_p) = 0` being the
only relation available).  This file lands that step, in the in-tree windowed-sum
language (`[Field L] [CharZero L]`, `ℕ`-weights, `Finset.range` sums), with the
convention `ζ_p := ζ^m`, `ζ_m := ζ^p` for `ζ` a primitive `n`-th root:

* `minpoly_pow_eq_cyclotomic` — **the linear-disjointness brick**:
  `minpoly ℚ⟮ζ^p⟯ (ζ^m) = cyclotomic p ℚ⟮ζ^p⟯`, now a direct specialization of
  `CoprimePacketMinpoly.minpoly_adjoin_coprime_eq_cyclotomic`.
* `linearIndependent_zetaP_pow` — **the independence brick (K5's deliverable)**:
  `1, ζ_p, …, ζ_p^{p-2}` are linearly independent over `ℚ(ζ_m)`.
* `relationCoeffs_eq` — **the forcing lemma**: any `ℚ(ζ_m)`-relation
  `∑_{i<p} a_i ζ_p^i = 0` has all coefficients EQUAL (`a_i = a_0`): a degree-`< p`
  annihilating polynomial is a constant multiple of `Φ_p = 1 + X + … + X^{p-1}`;
  equivalently, this is `CRTDoubleSlice.slice_of_packet_minpoly` at packet width `1`.
* `fiber_collapse_iff` — **MANN'S FIBER COLLAPSE**: for `ℕ`-weights `w i j` on the
  CRT grid `μ_p × μ_m`, the sum `∑_{i<p} ∑_{j<m} w i j · ζ^{i·m + j·p}` vanishes
  **iff** all `p` fiber projections `S_i := ∑_j w i j · (ζ^p)^j ∈ ℚ(ζ_m)` coincide.
* `fiber_collapse_dichotomy` — the dichotomy form: every fiber projection vanishes
  (the relation is a juxtaposition of level-`m` relations), or ALL `p` fibers carry
  the same nonzero projection (the relation genuinely crosses every fiber — the
  weight-gains-a-factor-`p` mechanism of Mann's minimality induction).
* `single_fiber_levelSum_eq_zero` — a vanishing sum supported in ONE fiber descends
  to a vanishing sum at level `m` (the base-change step of the induction).
* `fiber_collapse_of_vanishing` — the single-index form: a vanishing `ℕ`-sum
  `∑_{e<n} w e · ζ^e = 0` regrouped through the CRT bijection
  `(i,j) ↦ (i·m + j·p) % n` has all fiber projections equal
  (with `sum_crt_regroup` providing the regrouping identity).

## Honest provenance

First formalization of this structure step (checked: Mathlib has no Conway–Jones/Mann
theory).  `n` need NOT be squarefree here — only the split prime must be simple
(`p ∤ m`), which is exactly the generality Mann's induction consumes.  Char-0 is
load-bearing.  This is the coprime-tower analogue of the single-prime fiber collapse
in `PrimePowerMultisetWindow` (where the tower is `X^p - ζ_{p^k}` instead of `Φ_p`
and the forcing is shift-periodicity); combined with the in-tree
`lam_leung_iff_minimal` peeling, it is the engine for the two-prime case of the O124
multiset window law and the ≥ 3-prime Lam–Leung weight bound.
-/

namespace MannFiberCollapse

open Polynomial IntermediateField

variable {L : Type*} [Field L] [CharZero L]
variable {p m : ℕ} {ζ : L}

/-- `p ∤ m` forces `m ≠ 0`. -/
lemma m_pos (hpm : ¬ p ∣ m) : 0 < m :=
  Nat.pos_of_ne_zero fun h => hpm (h ▸ dvd_zero p)

/-! ## The tower count: `[ℚ(ζ_m)(ζ_p) : ℚ(ζ_m)] = p - 1` -/

/-- **The coprime cyclotomic tower degree**: adjoining `ζ_p = ζ^m` to
`ℚ(ζ_m) = ℚ⟮ζ^p⟯` has degree exactly `p - 1`, by the shared coprime minpoly
degree theorem. -/
theorem finrank_adjoin_zetaP (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) :
    Module.finrank ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ ^ m⟯ = p - 1 := by
  have hm : 0 < m := m_pos hpm
  have hn : 0 < p * m := Nat.mul_pos hp.pos hm
  have hζm : IsPrimitiveRoot (ζ ^ p) m := hζ.pow hn rfl
  have hζp : IsPrimitiveRoot (ζ ^ m) p := hζ.pow hn (mul_comm p m)
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  have hint : IsIntegral ℚ⟮ζ ^ p⟯ (ζ ^ m) := (hζp.isIntegral hp.pos).tower_top
  rw [IntermediateField.adjoin.finrank hint,
    CoprimePacketMinpoly.natDegree_minpoly_adjoin_coprime hm hp.pos hcop hζm hζp,
    Nat.totient_prime hp]

/-- **The linear-disjointness brick**: `Φ_p` remains the minimal polynomial of
`ζ_p = ζ^m` over the coprime cyclotomic field `ℚ(ζ_m) = ℚ⟮ζ^p⟯`. -/
theorem minpoly_pow_eq_cyclotomic (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) :
    minpoly ℚ⟮ζ ^ p⟯ (ζ ^ m) = cyclotomic p ℚ⟮ζ ^ p⟯ := by
  have hm : 0 < m := m_pos hpm
  have hn : 0 < p * m := Nat.mul_pos hp.pos hm
  have hζm : IsPrimitiveRoot (ζ ^ p) m := hζ.pow hn rfl
  have hζp : IsPrimitiveRoot (ζ ^ m) p := hζ.pow hn (mul_comm p m)
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  exact CoprimePacketMinpoly.minpoly_adjoin_coprime_eq_cyclotomic hm hp.pos hcop hζm hζp

/-! ## The forcing lemma and the independence brick -/

/-- **The relation forcing lemma**: any `ℚ(ζ_m)`-linear relation
`∑_{i<p} a_i ζ_p^i = 0` has all its coefficients equal — the only relation among
`1, ζ_p, …, ζ_p^{p-1}` over `ℚ(ζ_m)` is (a multiple of) the all-ones relation. -/
theorem relationCoeffs_eq (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) (a : ℕ → ℚ⟮ζ ^ p⟯)
    (hrel : ∑ i ∈ Finset.range p, (a i : L) * (ζ ^ m) ^ i = 0) :
    ∀ i < p, a i = a 0 := by
  have hm : 0 < m := m_pos hpm
  have hn : 0 < p * m := Nat.mul_pos hp.pos hm
  have hζm : IsPrimitiveRoot (ζ ^ p) m := hζ.pow hn rfl
  have hζp : IsPrimitiveRoot (ζ ^ m) p := hζ.pow hn (mul_comm p m)
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  have hmin : minpoly ℚ⟮ζ ^ p⟯ (ζ ^ m)
      = ∑ t ∈ Finset.range p, (X : Polynomial ℚ⟮ζ ^ p⟯) ^ (t * 1) :=
    CoprimePacketMinpoly.minpoly_adjoin_coprime_prime_eq_geom hm hp hcop hζm hζp
  have hsum : ∑ e ∈ Finset.range (p * 1), a e • (ζ ^ m) ^ e = 0 := by
    simpa [Algebra.smul_def, IntermediateField.algebraMap_apply] using hrel
  intro i hi
  have h := CRTDoubleSlice.slice_of_packet_minpoly hmin hsum (i := i) (i' := 0) (s := 0)
    hi hp.pos Nat.one_pos
  simpa using h

/-- **THE INDEPENDENCE BRICK (K5)**: `1, ζ_p, ζ_p^2, …, ζ_p^{p-2}` are linearly
independent over the coprime cyclotomic field `ℚ(ζ_m)` — here `ζ_p := ζ^m`,
`ℚ(ζ_m) := ℚ⟮ζ^p⟯` for `ζ` a primitive `(p·m)`-th root of unity, `p ∤ m`. -/
theorem linearIndependent_zetaP_pow (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) :
    LinearIndependent ℚ⟮ζ ^ p⟯ (fun i : Fin (p - 1) => (ζ ^ m) ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hgsum
  -- extend the coefficient vector by `0` at the top slot `p - 1`
  set a : ℕ → ℚ⟮ζ ^ p⟯ := fun i => if h : i < p - 1 then g ⟨i, h⟩ else 0 with ha
  have htop : a (p - 1) = 0 := by rw [ha]; exact dif_neg (lt_irrefl _)
  have hrel : ∑ i ∈ Finset.range p, (a i : L) * (ζ ^ m) ^ i = 0 := by
    rw [show Finset.range p = Finset.range ((p - 1) + 1) by
      congr 1; have := hp.pos; omega, Finset.sum_range_succ, htop]
    rw [ZeroMemClass.coe_zero, zero_mul, add_zero,
      ← Fin.sum_univ_eq_sum_range (fun i => (a i : L) * (ζ ^ m) ^ i) (p - 1), ← hgsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hai : a (i : ℕ) = g i := by rw [ha]; exact dif_pos i.isLt
    rw [hai, Algebra.smul_def, IntermediateField.algebraMap_apply]
  have hall := relationCoeffs_eq hp hpm hζ a hrel
  have ha0 : a 0 = 0 := by
    have h1 := hall (p - 1) (Nat.sub_lt hp.pos Nat.one_pos)
    rw [htop] at h1
    exact h1.symm
  intro i
  have hi : (i : ℕ) < p := lt_of_lt_of_le i.isLt (Nat.sub_le p 1)
  have h2 := hall (i : ℕ) hi
  have hai : a (i : ℕ) = g i := by rw [ha]; exact dif_pos i.isLt
  rw [hai, ha0] at h2
  exact h2

/-! ## Mann's fiber collapse -/

/-- The level-`m` weighted power sum `∑_{j<m} v j · ξ^j` — for `ξ := ζ^p` this is
the `ζ_p`-fiber projection, an element of `ℚ(ζ_m)`. -/
def levelSum (ξ : L) (m : ℕ) (v : ℕ → ℕ) : L :=
  ∑ j ∈ Finset.range m, (v j : L) * ξ ^ j

/-- Fiber projections land in `ℚ(ζ_m) = ℚ⟮ζ^p⟯`. -/
theorem levelSum_mem (v : ℕ → ℕ) : levelSum (ζ ^ p) m v ∈ ℚ⟮ζ ^ p⟯ := by
  refine sum_mem fun j _ => ?_
  exact mul_mem (IntermediateField.natCast_mem _ _)
    (pow_mem (mem_adjoin_simple_self ℚ (ζ ^ p)) j)

omit [CharZero L] in
/-- The CRT-grid sum factors through the fiber projections:
`∑_{i<p} ∑_{j<m} w i j · ζ^{i·m + j·p} = ∑_{i<p} S_i · ζ_p^i`. -/
theorem sum_fiber_factor (w : ℕ → ℕ → ℕ) :
    ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range m, (w i j : L) * ζ ^ (i * m + j * p)
      = ∑ i ∈ Finset.range p, levelSum (ζ ^ p) m (w i) * (ζ ^ m) ^ i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [levelSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show i * m + j * p = m * i + p * j by ring, pow_add, pow_mul, pow_mul]
  ring

/-- **MANN'S FIBER COLLAPSE (the K5 induction step)**: for `p` prime, `p ∤ m`, `ζ`
a primitive `(p·m)`-th root of unity in characteristic zero, and `ℕ`-weights
`w i j` on the CRT grid, the weighted sum over `μ_{p·m}` vanishes **iff** all `p`
fiber projections `S_i = ∑_{j<m} w i j · (ζ^p)^j ∈ ℚ(ζ_m)` coincide.  Forward:
the forcing lemma (only the all-ones relation survives over the coprime tower).
Backward: the all-ones relation itself (`∑_{i<p} ζ_p^i = 0`). -/
theorem fiber_collapse_iff (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℕ → ℕ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range m, (w i j : L) * ζ ^ (i * m + j * p) = 0)
      ↔ ∀ i < p, levelSum (ζ ^ p) m (w i) = levelSum (ζ ^ p) m (w 0) := by
  have hm : 0 < m := m_pos hpm
  have hn : 0 < p * m := Nat.mul_pos hp.pos hm
  have hζp : IsPrimitiveRoot (ζ ^ m) p := hζ.pow hn (mul_comm p m)
  constructor
  · intro hvan
    set a : ℕ → ℚ⟮ζ ^ p⟯ := fun i => ⟨levelSum (ζ ^ p) m (w i), levelSum_mem (w i)⟩
      with ha
    have hrel : ∑ i ∈ Finset.range p, (a i : L) * (ζ ^ m) ^ i = 0 := by
      rw [sum_fiber_factor w] at hvan
      exact hvan
    intro i hi
    have h1 := relationCoeffs_eq hp hpm hζ a hrel i hi
    exact congrArg Subtype.val h1
  · intro hcollapse
    rw [sum_fiber_factor w]
    have h2 : ∀ i ∈ Finset.range p,
        levelSum (ζ ^ p) m (w i) * (ζ ^ m) ^ i
          = levelSum (ζ ^ p) m (w 0) * (ζ ^ m) ^ i := fun i hi => by
      rw [hcollapse i (Finset.mem_range.mp hi)]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum,
      hζp.geom_sum_eq_zero hp.one_lt, mul_zero]

/-- **The dichotomy form of the collapse**: a vanishing `ℕ`-sum either has ALL
fiber projections zero (a juxtaposition of independent level-`m` relations), or
ALL `p` fibers alive with one common nonzero projection — the two branches of
Mann's minimality induction (descend into a fiber, or gain the weight factor `p`). -/
theorem fiber_collapse_dichotomy (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℕ → ℕ)
    (hvan : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range m,
      (w i j : L) * ζ ^ (i * m + j * p) = 0) :
    (∀ i < p, levelSum (ζ ^ p) m (w i) = 0)
      ∨ ((∀ i < p, levelSum (ζ ^ p) m (w i) = levelSum (ζ ^ p) m (w 0))
          ∧ levelSum (ζ ^ p) m (w 0) ≠ 0) := by
  have hcollapse := (fiber_collapse_iff hp hpm hζ w).mp hvan
  rcases eq_or_ne (levelSum (ζ ^ p) m (w 0)) 0 with h0 | h0
  · exact Or.inl fun i hi => (hcollapse i hi).trans h0
  · exact Or.inr ⟨hcollapse, h0⟩

/-- **Single-fiber descent**: a vanishing sum supported in one fiber `i₀` has
vanishing fiber projection — the relation descends to level `m` (Mann's base
change: from `μ_{p·m}` to `μ_m`). -/
theorem single_fiber_levelSum_eq_zero (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℕ → ℕ) {i₀ : ℕ} (hi₀ : i₀ < p)
    (hsupp : ∀ i < p, i ≠ i₀ → ∀ j < m, w i j = 0)
    (hvan : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range m,
      (w i j : L) * ζ ^ (i * m + j * p) = 0) :
    levelSum (ζ ^ p) m (w i₀) = 0 := by
  have hcollapse := (fiber_collapse_iff hp hpm hζ w).mp hvan
  -- pick a fiber other than i₀; its projection is a sum of zeros
  obtain ⟨i₁, hi₁p, hi₁ne⟩ : ∃ i₁, i₁ < p ∧ i₁ ≠ i₀ := by
    rcases eq_or_ne i₀ 0 with rfl | h
    · exact ⟨1, hp.one_lt, one_ne_zero⟩
    · exact ⟨0, hp.pos, Ne.symm h⟩
  have hzero : levelSum (ζ ^ p) m (w i₁) = 0 := by
    rw [levelSum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hsupp i₁ hi₁p hi₁ne j (Finset.mem_range.mp hj)]
    simp
  rw [hcollapse i₀ hi₀, ← hcollapse i₁ hi₁p, hzero]

/-! ## The single-index form: regrouping a `μ_n`-sum through the CRT bijection -/

omit [CharZero L] in
/-- Powers of `ζ` only depend on exponents mod `p·m`. -/
lemma pow_mod (hζ : IsPrimitiveRoot ζ (p * m)) (e : ℕ) :
    ζ ^ e = ζ ^ (e % (p * m)) := by
  conv_lhs => rw [← Nat.mod_add_div e (p * m)]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

omit [CharZero L] in
/-- **The CRT regrouping**: a weighted sum over `μ_{p·m}` regroups by `ζ_p`-power
into the fiber grid, via the bijection `(i, j) ↦ (i·m + j·p) % (p·m)` of
`[0,p) × [0,m)` onto `[0, p·m)` (no characteristic hypothesis needed). -/
theorem sum_crt_regroup (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℕ) :
    ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e
      = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range m,
          (w ((i * m + j * p) % (p * m)) : L) * ζ ^ (i * m + j * p) := by
  have hm : 0 < m := m_pos hpm
  have hn : 0 < p * m := Nat.mul_pos hp.pos hm
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  rw [← Finset.sum_product']
  -- both sides are sums of `f e := w e · ζ^e` — the right over the CRT image
  have hinj : ∀ a₁ ∈ Finset.range p ×ˢ Finset.range m,
      ∀ a₂ ∈ Finset.range p ×ˢ Finset.range m,
      (a₁.1 * m + a₁.2 * p) % (p * m) = (a₂.1 * m + a₂.2 * p) % (p * m) → a₁ = a₂ := by
    rintro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ heq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h₁ h₂
    have hmod : (i₁ * m + j₁ * p) ≡ (i₂ * m + j₂ * p) [MOD p * m] := heq
    -- mod p: kill the j·p terms, cancel the coprime factor m
    have hi : i₁ = i₂ := by
      have h3 : i₁ * m ≡ i₂ * m [MOD p] := by
        have h4 := hmod.of_dvd (dvd_mul_right p m)
        unfold Nat.ModEq at h4 ⊢
        rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at h4
      have h5 : i₁ ≡ i₂ [MOD p] :=
        Nat.ModEq.cancel_right_of_coprime hcop h3
      unfold Nat.ModEq at h5
      rwa [Nat.mod_eq_of_lt h₁.1, Nat.mod_eq_of_lt h₂.1] at h5
    -- mod m: kill the i·m terms, cancel the coprime factor p
    have hj : j₁ = j₂ := by
      have h3 : j₁ * p ≡ j₂ * p [MOD m] := by
        have h4 := hmod.of_dvd (dvd_mul_left m p)
        unfold Nat.ModEq at h4 ⊢
        rw [add_comm (i₁ * m) (j₁ * p), add_comm (i₂ * m) (j₂ * p)] at h4
        rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at h4
      have h5 : j₁ ≡ j₂ [MOD m] := by
        refine Nat.ModEq.cancel_right_of_coprime ?_ h3
        rw [Nat.gcd_comm]
        exact hcop
      unfold Nat.ModEq at h5
      rwa [Nat.mod_eq_of_lt h₁.2, Nat.mod_eq_of_lt h₂.2] at h5
    exact Prod.ext hi hj
  refine (Finset.sum_bij (fun a _ => (a.1 * m + a.2 * p) % (p * m)) ?_ hinj ?_ ?_).symm
  · intro a _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  · -- surjectivity from injectivity and equal cardinalities
    intro e he
    have hcard : (Finset.range (p * m)).card
        ≤ (Finset.range p ×ˢ Finset.range m).card := by
      rw [Finset.card_product, Finset.card_range, Finset.card_range, Finset.card_range]
    obtain ⟨a, ha, hae⟩ := Finset.surj_on_of_inj_on_of_card_le
      (fun a _ => (a.1 * m + a.2 * p) % (p * m))
      (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hn))
      (fun a₁ a₂ ha₁ ha₂ h => hinj a₁ ha₁ a₂ ha₂ h) hcard e he
    exact ⟨a, ha, hae.symm⟩
  · intro a _
    rw [← pow_mod hζ]

/-- **THE SINGLE-INDEX FIBER COLLAPSE**: a vanishing `ℕ`-weighted sum over the
full exponent range `[0, p·m)` has all its `p` CRT fiber projections equal — the
statement consumed by Mann's induction on the number of prime factors. -/
theorem fiber_collapse_of_vanishing (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℕ)
    (hvan : ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e = 0) :
    ∀ i < p, levelSum (ζ ^ p) m (fun j => w ((i * m + j * p) % (p * m)))
        = levelSum (ζ ^ p) m (fun j => w ((j * p) % (p * m))) := by
  have h1 := (fiber_collapse_iff hp hpm hζ
    (fun i j => w ((i * m + j * p) % (p * m)))).mp
    (by rw [← sum_crt_regroup hp hpm hζ w]; exact hvan)
  intro i hi
  have h2 := h1 i hi
  simpa using h2

end MannFiberCollapse

#print axioms MannFiberCollapse.finrank_adjoin_zetaP
#print axioms MannFiberCollapse.minpoly_pow_eq_cyclotomic
#print axioms MannFiberCollapse.relationCoeffs_eq
#print axioms MannFiberCollapse.linearIndependent_zetaP_pow
#print axioms MannFiberCollapse.sum_fiber_factor
#print axioms MannFiberCollapse.fiber_collapse_iff
#print axioms MannFiberCollapse.fiber_collapse_dichotomy
#print axioms MannFiberCollapse.single_fiber_levelSum_eq_zero
#print axioms MannFiberCollapse.sum_crt_regroup
#print axioms MannFiberCollapse.fiber_collapse_of_vanishing
