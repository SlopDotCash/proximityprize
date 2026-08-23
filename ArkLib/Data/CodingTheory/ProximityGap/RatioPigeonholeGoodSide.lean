/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadFamilyCensus
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Multiplicity

/-!
# The ratio-pigeonhole good side: the five-thirds strip (#371, round 10)

This file lands the **first completeness (good-side) theorem beyond the granularity
ladder**: on the strip

  `2t ≥ n + d + 2`  and  `5t ≥ 3n + 3d + 1`     (`t` = agreement threshold)

EVERY stack `(u₀, u₁)` has at most `n − t + 1` bad scalars for the degree-`≤ d` smooth
evaluation code — the simplex value, matching the landed floor
(`simplex_epsMCA_lower_bound`) EXACTLY, with **no field-size guard**.

## The proof (the coordinate-space ratio surface)

For each bad `γ` fix a witness codeword `q_γ` and take its full agreement set `A_γ`
(`|A_γ| ≥ t`; pairwise `|A_γ ∩ A_γ'| ≥ 2t − n`).  Through a fixed bad `γ₀`:

1. **Affine families.**  The pair-interpolant `r_γ := (q_{γ₀} − q_γ)/(γ₀ − γ)` agrees
   with `u₁` pointwise on `A_{γ₀} ∩ A_γ`, and `q_γ = a + γ·r_γ` with
   `a := q_{γ₀} − γ₀·r_γ`.  "Same `r`" partitions the bad set into affine families.
2. **The ratio pigeonhole (within a family).**  `A_γ = D ⊔ fibre(γ)` where
   `D = {i : u₀ = a, u₁ = r}` is the shared degenerate core and the fibres are
   disjoint level sets of the coordinate ratio `−(u₀−a)/(u₁−r)`; non-joint-
   explainability forces `≥ max(1, t − |D|)` fresh points per scalar (`a, r` ARE
   codewords).  Hence a single family carries `≤ (n−|D|)/(t−|D|) ≤ n−t+1` scalars.
3. **THE INTERACTION LAW (the new mechanism).**  For two families `i ≠ j` through
   `γ₀`: `a_j − a_i = γ₀(r_i − r_j)`, so at every point of the foreign core `D_j`,
   either `u₁ = r_i` (≤ `d` points: distinct degree-`≤ d` polynomials) or the
   family-`i` ratio collapses to EXACTLY `γ₀` — i.e. `D_j ⊆ fibre_i(γ₀) ∪ Z_{ij}`,
   `|Z_{ij}| ≤ d`.  Foreign cores eat the host's own fibre.
4. **Counting** `D_i ⊔ fibre_i(γ₀) ⊔ (member fibres)` inside the `n` points:
   `K ≥ 3` families force `5t ≤ 3n + 3d` (dead on the strip); `K = 2` forces
   `μ₁ + μ₂ ≤ n − t`; `K = 1` is the pigeonhole.  Total: `N ≤ n − t + 1`.

## Sharpness and reach

* The exhaustive round-8 census (`p = 17, n = 8`) **matches on every strip cell**
  ((d,t) = (1,6), (1,7), (2,7), (3,7), (2,8) ↦ 3, 2, 2, 2, 1 = `n−t+1`) and every
  censused violation misses the strip by EXACTLY one unit: `(2,6) = 4` fails
  `5t ≥ 31` by one, `(3,6) = 7` and `(1,5) = 8` fail `2t ≥ n+d+2` by one.  The
  mod-17 surpluses live strictly outside the strip: no `p₀` guard is needed.
* Beyond the ladder: `GranularityLadderRS` pins `δ* = j/n` for `3(j−1) + k ≤ n`,
  i.e. `t ≥ (2n+d+1)/3`.  The five-thirds strip reaches `t ≥ (3n+3d+1)/5`, which is
  LOWER for `n > 4d − 2` — at low rate a `Θ(n)`-wide band of new exact rungs
  (radius reach `1/3 → 2/5` of `n` asymptotically).
* At the deployed cell `RS[F₁₂₂₈₉, n = 16, d = 2]` the new rung is `t = 11`
  (`5·11 = 55 = 3·16+3·2+1`, exactly on the boundary; the ladder needs `t ≥ 12`):
  probe `scripts/probes/probe_ratio_pigeonhole.py` confirms max = 6 at
  `p ∈ {97, 257, 12289}` (catalogue + two-family grafts + hill-climbing), the
  graft trade-off curve `(c, N) = (0,6), (1,6), (2,5), …` realizing the interaction
  law 1-for-1.  Combined with the landed pencil bad side (8 scalars at `t = 10`),
  this closes the **first beyond-ladder exact band**:

    `δ*(RS[F₁₂₂₈₉, 16, d=2], ε*) = 3/8`  for every `ε* ∈ [6/p, 8/p)`.

## Honest scope

The strip is where the family count collapses (`K ≤ 2`).  Below it the multi-family
regime is real (the antipodal pencil at `t = 10` has K = 2 with `8 > 7` scalars; the
packing/staircase/explosion bands have `ω(n−t)` counts): the full
`CompleteEnvelopeConjecture` good side remains open there — the within-family
pigeonhole (step 2) and the interaction law (step 3) are the reusable bricks.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.KKH26DimGeneral
open ArkLib.ProximityGap.BadFamilyCensus

namespace ArkLib.ProximityGap.RatioPigeonhole

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy of the `private`
helper of the sibling files). -/
private lemma pow_inj_below_order''''' {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-! ## The main theorem: the five-thirds strip good side -/

open Classical in
/-- **THE FIVE-THIRDS STRIP GOOD SIDE** (#371 round 10).  On the strip
`2t ≥ n+d+2`, `5t ≥ 3n+3d+1`, every stack has at most `n − t + 1` bad scalars at
any radius `δ` whose witness sets are forced to carry `≥ t` points — the simplex
ceiling, exactly matching the landed simplex floor.  Field-size-free.

The hypothesis `hwit` packages the radius: at `δ = 1 − t/n` (and on the whole band
`δ < (n−t+1)/n`) it is discharged by cast arithmetic in the corollaries below. -/
theorem fiveThirds_badScalars_card_le {p n : ℕ} [Fact p.Prime] [NeZero n]
    {d t : ℕ} {g : ZMod p} (hg : orderOf g = n)
    (htn : t ≤ n) (hB : n + d + 2 ≤ 2 * t) (h53 : 3 * n + 3 * d + 1 ≤ 5 * t)
    (δ : ℝ≥0)
    (hwit : ∀ S : Finset (Fin n),
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) → t ≤ S.card)
    (u₀ u₁ : Fin n → ZMod p) :
    (univ.filter fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ).card
      ≤ n - t + 1 := by
  classical
  set Γ : Finset (ZMod p) := univ.filter fun γ : ZMod p =>
    mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ with hΓ
  by_contra hcon
  have hN : n - t + 2 ≤ Γ.card := by omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ n = 1 := by rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega : n ≠ 0)] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    exact Fin.ext (pow_inj_below_order''''' hg0 hg _ i.isLt _ j.isLt hij)
  -- extract per-scalar witness data (junk outside Γ)
  have hdata : ∀ γ : ZMod p, ∃ Sq : Finset (Fin n) × Polynomial (ZMod p), γ ∈ Γ →
      t ≤ Sq.1.card ∧ Sq.2.natDegree ≤ d ∧
        (∀ i ∈ Sq.1, Sq.2.eval (g ^ (i : ℕ)) = u₀ i + γ * u₁ i) ∧
        ¬ pairJointAgreesOn (evalCode g n d) Sq.1 u₀ u₁ := by
    intro γ
    by_cases hγ : γ ∈ Γ
    · obtain ⟨S, hcard, ⟨w, hwC, hagree⟩, hpair⟩ := (Finset.mem_filter.mp hγ).2
      obtain ⟨q, hqdeg, hq⟩ := hwC
      refine ⟨(S, q), fun _ => ⟨hwit S hcard, hqdeg, fun i hi => ?_, hpair⟩⟩
      rw [← hq i, hagree i hi, smul_eq_mul]
    · exact ⟨(∅, 0), fun h => absurd h hγ⟩
  choose SQ hSQ using hdata
  set qf : ZMod p → Polynomial (ZMod p) := fun γ => (SQ γ).2 with hqfdef
  -- the full agreement sets
  set Af : ZMod p → Finset (Fin n) := fun γ =>
    univ.filter fun i => (qf γ).eval (g ^ (i : ℕ)) = u₀ i + γ * u₁ i with hAfdef
  have hSA : ∀ γ ∈ Γ, (SQ γ).1 ⊆ Af γ := by
    intro γ hγ i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hSQ γ hγ).2.2.1 i hi⟩
  have hAcard : ∀ γ ∈ Γ, t ≤ (Af γ).card := fun γ hγ =>
    le_trans (hSQ γ hγ).1 (Finset.card_le_card (hSA γ hγ))
  have hqdeg : ∀ γ ∈ Γ, (qf γ).natDegree ≤ d := fun γ hγ => (hSQ γ hγ).2.1
  -- pick the anchor scalar γ₀
  obtain ⟨γ₀, hγ₀⟩ := Finset.card_pos.mp (show 0 < Γ.card by omega)
  set Γ' : Finset (ZMod p) := Γ.erase γ₀ with hΓ'def
  have hΓ'card : Γ'.card = Γ.card - 1 := Finset.card_erase_of_mem hγ₀
  have hΓ'sub : Γ' ⊆ Γ := Finset.erase_subset _ _
  -- the pair-interpolants
  set rf : ZMod p → Polynomial (ZMod p) := fun γ =>
    Polynomial.C (γ₀ - γ)⁻¹ * (qf γ₀ - qf γ) with hrfdef
  have hqdiff : ∀ γ ∈ Γ', Polynomial.C (γ₀ - γ) * rf γ = qf γ₀ - qf γ := by
    intro γ hγ
    have hne : γ₀ - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hγ))
    rw [hrfdef]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hne, Polynomial.C_1, one_mul]
  have hrdeg : ∀ γ ∈ Γ', (rf γ).natDegree ≤ d := by
    intro γ hγ
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (hqdeg γ₀ hγ₀) (hqdeg γ (hΓ'sub hγ)))
  -- the family intercepts and the family identity
  set aOf : Polynomial (ZMod p) → Polynomial (ZMod p) := fun rP =>
    qf γ₀ - Polynomial.C γ₀ * rP with haOfdef
  have haOfdeg : ∀ rP : Polynomial (ZMod p), rP.natDegree ≤ d →
      (aOf rP).natDegree ≤ d := by
    intro rP hrP
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    exact max_le (hqdeg γ₀ hγ₀) (le_trans (Polynomial.natDegree_C_mul_le _ _) hrP)
  have hγ₀fam : ∀ rP : Polynomial (ZMod p), qf γ₀ = aOf rP + Polynomial.C γ₀ * rP := by
    intro rP
    rw [haOfdef]
    ring
  have hfam : ∀ γ ∈ Γ', qf γ = aOf (rf γ) + Polynomial.C γ * rf γ := by
    intro γ hγ
    have h1 := hqdiff γ hγ
    rw [haOfdef]
    have h2 : Polynomial.C (γ₀ - γ) = Polynomial.C γ₀ - Polynomial.C γ :=
      Polynomial.C_sub
    rw [h2] at h1
    linear_combination h1
  -- the family cores and the collision loci
  set Dset : Polynomial (ZMod p) → Finset (Fin n) := fun rP =>
    univ.filter fun i => u₀ i = (aOf rP).eval (g ^ (i : ℕ)) ∧
      u₁ i = rP.eval (g ^ (i : ℕ)) with hDdef
  set Zset : Polynomial (ZMod p) → Polynomial (ZMod p) → Finset (Fin n) :=
    fun rP rP' => univ.filter fun i =>
      rP.eval (g ^ (i : ℕ)) = rP'.eval (g ^ (i : ℕ)) with hZdef
  -- distinct degree-≤ d interpolants collide at ≤ d points
  have hZcard : ∀ rP rP' : Polynomial (ZMod p), rP.natDegree ≤ d →
      rP'.natDegree ≤ d → rP ≠ rP' → (Zset rP rP').card ≤ d := by
    intro rP rP' h1 h2 hne
    by_contra hbig
    refine hne (fit_unique hginj (B := Zset rP rP') (by omega) h1 h2 ?_)
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  -- the agreement set of a family member is core ⊔ fibre
  have hAfam : ∀ (rP : Polynomial (ZMod p)) (γ : ZMod p),
      qf γ = aOf rP + Polynomial.C γ * rP →
      ∀ i : Fin n, i ∈ Af γ ↔
        (aOf rP).eval (g ^ (i : ℕ)) + γ * rP.eval (g ^ (i : ℕ))
          = u₀ i + γ * u₁ i := by
    intro rP γ hid i
    rw [hAfdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hid]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  -- core points belong to every member's agreement set
  have hDsubA : ∀ (rP : Polynomial (ZMod p)) (γ : ZMod p),
      qf γ = aOf rP + Polynomial.C γ * rP → Dset rP ⊆ Af γ := by
    intro rP γ hid i hi
    obtain ⟨h0, h1⟩ := (Finset.mem_filter.mp hi).2
    rw [hAfam rP γ hid i, ← h0, ← h1]
  -- fibre disjointness within a family
  have hfibDisj : ∀ (rP : Polynomial (ZMod p)) (γ γ' : ZMod p), γ ≠ γ' →
      qf γ = aOf rP + Polynomial.C γ * rP →
      qf γ' = aOf rP + Polynomial.C γ' * rP →
      Disjoint (Af γ \ Dset rP) (Af γ' \ Dset rP) := by
    intro rP γ γ' hne hid hid'
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨hiA, hiD⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hiA', -⟩ := Finset.mem_sdiff.mp hi'
    rw [hAfam rP γ hid i] at hiA
    rw [hAfam rP γ' hid' i] at hiA'
    have hu1 : u₁ i = rP.eval (g ^ (i : ℕ)) := by
      have hkey : (γ - γ') * (u₁ i - rP.eval (g ^ (i : ℕ))) = 0 := by
        linear_combination hiA' - hiA
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · linear_combination h
    have hu0 : u₀ i = (aOf rP).eval (g ^ (i : ℕ)) := by
      rw [hu1] at hiA
      linear_combination -hiA
    exact hiD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0, hu1⟩)
  -- member fibres are nonempty (non-joint-explainability) and ≥ t − |D|
  have hfibLB : ∀ (rP : Polynomial (ZMod p)), rP.natDegree ≤ d →
      ∀ γ ∈ Γ, qf γ = aOf rP + Polynomial.C γ * rP →
      1 ≤ (Af γ \ Dset rP).card ∧ t ≤ (Af γ \ Dset rP).card + (Dset rP).card := by
    intro rP hrP γ hγ hid
    constructor
    · rw [Nat.one_le_iff_ne_zero]
      intro hzero
      have hsub : Af γ ⊆ Dset rP :=
        Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hzero)
      refine (hSQ γ hγ).2.2.2 ⟨fun i => (aOf rP).eval (g ^ (i : ℕ)),
        ⟨aOf rP, haOfdeg rP hrP, fun i => rfl⟩,
        fun i => rP.eval (g ^ (i : ℕ)), ⟨rP, hrP, fun i => rfl⟩, ?_⟩
      intro i hi
      have hiD : i ∈ Dset rP := hsub (hSA γ hγ hi)
      obtain ⟨h0, h1⟩ := (Finset.mem_filter.mp hiD).2
      exact ⟨h0.symm, h1.symm⟩
    · calc t ≤ (Af γ).card := hAcard γ hγ
      _ ≤ (Af γ \ Dset rP).card + (Dset rP).card :=
          Finset.card_le_card_sdiff_add_card
  -- the core of a nonempty class is at least the pairwise overlap 2t − n
  have hcoreLB : ∀ γ ∈ Γ', 2 * t ≤ (Dset (rf γ)).card + n := by
    intro γ hγ
    have hsub : Af γ₀ ∩ Af γ ⊆ Dset (rf γ) := by
      intro i hi
      obtain ⟨hi0, hiγ⟩ := Finset.mem_inter.mp hi
      rw [hAfam (rf γ) γ₀ (hγ₀fam (rf γ)) i] at hi0
      rw [hAfam (rf γ) γ (hfam γ hγ) i] at hiγ
      have hu1 : u₁ i = (rf γ).eval (g ^ (i : ℕ)) := by
        have hne : γ₀ - γ ≠ 0 :=
          sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hγ))
        have hkey : (γ₀ - γ) * (u₁ i - (rf γ).eval (g ^ (i : ℕ))) = 0 := by
          linear_combination hiγ - hi0
        rcases mul_eq_zero.mp hkey with h | h
        · exact absurd h hne
        · linear_combination h
      have hu0 : u₀ i = (aOf (rf γ)).eval (g ^ (i : ℕ)) := by
        rw [hu1] at hi0
        linear_combination -hi0
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0, hu1⟩
    have hkey := Finset.card_union_add_card_inter (Af γ₀) (Af γ)
    have h1 : (Af γ₀ ∪ Af γ).card ≤ n := by
      calc (Af γ₀ ∪ Af γ).card ≤ (univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    have h2 : (Af γ₀ ∩ Af γ).card ≤ (Dset (rf γ)).card := Finset.card_le_card hsub
    have h3 := hAcard γ₀ hγ₀
    have h4 := hAcard γ (hΓ'sub hγ)
    omega
  -- THE INTERACTION LAW: foreign cores live inside γ₀'s own fibre (mod collisions)
  have hinteract : ∀ rP rP' : Polynomial (ZMod p),
      Dset rP' ⊆ (Af γ₀ \ Dset rP) ∪ Zset rP rP' := by
    intro rP rP' i hi
    obtain ⟨h0, h1⟩ := (Finset.mem_filter.mp hi).2
    by_cases hz : rP.eval (g ^ (i : ℕ)) = rP'.eval (g ^ (i : ℕ))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
    · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
      · -- i ∈ Af γ₀: the two family presentations of qf γ₀ agree
        rw [hAfam rP γ₀ (hγ₀fam rP) i]
        have hkey : (aOf rP) + Polynomial.C γ₀ * rP
            = (aOf rP') + Polynomial.C γ₀ * rP' := by
          rw [← hγ₀fam rP, ← hγ₀fam rP']
        have heval := congrArg (Polynomial.eval (g ^ (i : ℕ))) hkey
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
          at heval
        rw [heval, ← h0, ← h1]
      · -- i ∉ Dset rP: u₁ i = rP' ≠ rP there
        intro hiD
        exact hz (((Finset.mem_filter.mp hiD).2.2).symm.trans h1)
  -- cores of distinct families overlap only on the collision locus
  have hcoreInter : ∀ rP rP' : Polynomial (ZMod p),
      Dset rP ∩ Dset rP' ⊆ Zset rP rP' := by
    intro rP rP' i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← (Finset.mem_filter.mp hi1).2.2, ← (Finset.mem_filter.mp hi2).2.2]
  -- the universal family count: member fibres ⊔ an excluded set ⊔ the core fit in n
  have hfamCount : ∀ (rP : Polynomial (ZMod p)) (Φ : Finset (ZMod p)) (X : Finset (Fin n)),
      Φ ⊆ Γ' → (∀ γ ∈ Φ, qf γ = aOf rP + Polynomial.C γ * rP) →
      X ⊆ Af γ₀ \ Dset rP →
      (∀ γ ∈ Φ, Disjoint (Af γ \ Dset rP) X) →
      (∑ γ ∈ Φ, (Af γ \ Dset rP).card) + X.card + (Dset rP).card ≤ n := by
    intro rP Φ X hΦsub hΦfam hXsub hXdisj
    have hdisj : ∀ γ ∈ Φ, ∀ γ' ∈ Φ, γ ≠ γ' →
        Disjoint (Af γ \ Dset rP) (Af γ' \ Dset rP) := fun γ hγ γ' hγ' hne =>
      hfibDisj rP γ γ' hne (hΦfam γ hγ) (hΦfam γ' hγ')
    have hbu : (Φ.biUnion fun γ => Af γ \ Dset rP).card
        = ∑ γ ∈ Φ, (Af γ \ Dset rP).card := Finset.card_biUnion hdisj
    have hdisjX : Disjoint (Φ.biUnion fun γ => Af γ \ Dset rP) X :=
      Finset.disjoint_biUnion_left _ _ _ |>.mpr hXdisj
    have hsub : (Φ.biUnion fun γ => Af γ \ Dset rP) ∪ X ⊆ univ \ Dset rP := by
      refine Finset.union_subset ?_
        (Finset.Subset.trans hXsub
          (Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)))
      intro i hi
      obtain ⟨γ, -, hiγ⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hiγ).2⟩
    have hcard : ((Φ.biUnion fun γ => Af γ \ Dset rP) ∪ X).card
        = (∑ γ ∈ Φ, (Af γ \ Dset rP).card) + X.card := by
      rw [Finset.card_union_of_disjoint hdisjX, hbu]
    have hle : ((Φ.biUnion fun γ => Af γ \ Dset rP) ∪ X).card
        ≤ n - (Dset rP).card := by
      calc ((Φ.biUnion fun γ => Af γ \ Dset rP) ∪ X).card
          ≤ (univ \ Dset rP).card := Finset.card_le_card hsub
      _ = n - (Dset rP).card := by
          rw [Finset.card_univ_diff, Fintype.card_fin]
    have hDn : (Dset rP).card ≤ n := by
      calc (Dset rP).card ≤ (univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    omega
  -- ===================  the trichotomy on the family count  ===================
  by_cases hK1 : ∀ γ ∈ Γ', ∀ γ' ∈ Γ', rf γ = rf γ'
  · -- K = 1: a single affine family carries all of Γ — the ratio pigeonhole
    have hΓ'ne : Γ'.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨γr, hγr⟩ := hΓ'ne
    set rP := rf γr with hrPdef
    have hfamΓ : ∀ γ ∈ Γ, qf γ = aOf rP + Polynomial.C γ * rP := by
      intro γ hγ
      by_cases hγγ₀ : γ = γ₀
      · rw [hγγ₀]; exact hγ₀fam rP
      · have hγ' : γ ∈ Γ' := Finset.mem_erase.mpr ⟨hγγ₀, hγ⟩
        have := hfam γ hγ'
        rwa [hK1 γ hγ' γr hγr] at this
    -- count with Φ = Γ ∖ {γ₀} … in fact all of Γ: use Φ = Γ' plus γ₀ via X
    have hcount := hfamCount rP Γ' (Af γ₀ \ Dset rP) (Finset.Subset.refl _)
      (fun γ hγ => hfamΓ γ (hΓ'sub hγ)) (Finset.Subset.refl _)
      (fun γ hγ => hfibDisj rP γ γ₀ (Finset.ne_of_mem_erase hγ)
        (hfamΓ γ (hΓ'sub hγ)) (hγ₀fam rP))
    have hrPdeg : rP.natDegree ≤ d := hrdeg γr hγr
    -- per-member lower bounds
    have hLB1 : ∀ γ ∈ Γ', 1 ≤ (Af γ \ Dset rP).card := fun γ hγ =>
      (hfibLB rP hrPdeg γ (hΓ'sub hγ) (hfamΓ γ (hΓ'sub hγ))).1
    have hLBt : ∀ γ ∈ Γ', t ≤ (Af γ \ Dset rP).card + (Dset rP).card := fun γ hγ =>
      (hfibLB rP hrPdeg γ (hΓ'sub hγ) (hfamΓ γ (hΓ'sub hγ))).2
    have hγ₀LB := hfibLB rP hrPdeg γ₀ hγ₀ (hγ₀fam rP)
    set Dc := (Dset rP).card with hDc
    -- sum lower bounds
    have hsum1 : Γ'.card * 1 ≤ ∑ γ ∈ Γ', (Af γ \ Dset rP).card := by
      have := Finset.card_nsmul_le_sum Γ' (fun γ => (Af γ \ Dset rP).card) 1 hLB1
      simpa using this
    have hsumt : Γ'.card * (t - Dc) ≤ ∑ γ ∈ Γ', (Af γ \ Dset rP).card := by
      have := Finset.card_nsmul_le_sum Γ' (fun γ => (Af γ \ Dset rP).card) (t - Dc)
        (fun γ hγ => by
          have := hLBt γ hγ
          show t - Dc ≤ (Af γ \ Dset rP).card
          omega)
      simpa using this
    -- endgame
    rcases Nat.lt_or_ge Dc t with hDct | hDct
    · -- small core: the pigeonhole proper
      set s := t - Dc with hs
      have hs1 : 1 ≤ s := by omega
      obtain ⟨s', hs'⟩ : ∃ s'', s = s'' + 1 := ⟨s - 1, by omega⟩
      have hNs : (n - t + 1) * s ≤ Γ'.card * s :=
        Nat.mul_le_mul_right _ (by omega)
      have hchain : Γ'.card * s + (Af γ₀ \ Dset rP).card + Dc ≤ n := by
        have := le_trans hsumt (le_refl _)
        omega
      have hγ₀s : s ≤ (Af γ₀ \ Dset rP).card := by
        have := hγ₀LB.2
        omega
      have hbig : (n - t + 1) * s + s + Dc ≤ n := by
        calc (n - t + 1) * s + s + Dc
            ≤ Γ'.card * s + (Af γ₀ \ Dset rP).card + Dc := by
              have := hNs; have := hγ₀s; omega
        _ ≤ n := hchain
      have hexp : (n - t + 1) * (s' + 1) = (n - t) * s' + (n - t) + s' + 1 := by
        ring
      rw [hs'] at hbig
      rw [hexp] at hbig
      have hks : 0 ≤ (n - t) * s' := Nat.zero_le _
      have hDcs : Dc + (s' + 1) = t := by omega
      omega
    · -- huge core: every member needs a fresh point, only n − Dc ≤ n − t available
      have hchain : Γ'.card * 1 + (Af γ₀ \ Dset rP).card + Dc ≤ n := by
        have := le_trans hsum1 (le_refl _)
        omega
      have := hγ₀LB.1
      omega
  · -- K ≥ 2
    push Not at hK1
    obtain ⟨γa, hγa, γb, hγb, hab⟩ := hK1
    by_cases hK2 : ∀ γ ∈ Γ', rf γ = rf γa ∨ rf γ = rf γb
    · -- K = 2: the interaction law caps both classes
      set rPa := rf γa with hrPa
      set rPb := rf γb with hrPb
      have hadeg : rPa.natDegree ≤ d := hrdeg γa hγa
      have hbdeg : rPb.natDegree ≤ d := hrdeg γb hγb
      set Γa : Finset (ZMod p) := Γ'.filter fun γ => rf γ = rPa with hΓa
      set Γb : Finset (ZMod p) := Γ'.filter fun γ => ¬ (rf γ = rPa) with hΓb
      have hΓasub : Γa ⊆ Γ' := Finset.filter_subset _ _
      have hΓbsub : Γb ⊆ Γ' := Finset.filter_subset _ _
      have hsplit : Γa.card + Γb.card = Γ'.card :=
        Finset.card_filter_add_card_filter_not (s := Γ') (fun γ => rf γ = rPa)
      have hγaΓa : γa ∈ Γa := Finset.mem_filter.mpr ⟨hγa, rfl⟩
      have hγbΓb : γb ∈ Γb := Finset.mem_filter.mpr ⟨hγb, Ne.symm hab⟩
      have hfama : ∀ γ ∈ Γa, qf γ = aOf rPa + Polynomial.C γ * rPa := by
        intro γ hγ
        obtain ⟨hγ', hre⟩ := Finset.mem_filter.mp hγ
        have := hfam γ hγ'
        rwa [hre] at this
      have hfamb : ∀ γ ∈ Γb, qf γ = aOf rPb + Polynomial.C γ * rPb := by
        intro γ hγ
        obtain ⟨hγ', hre⟩ := Finset.mem_filter.mp hγ
        have hre' : rf γ = rPb := (hK2 γ hγ').resolve_left hre
        have := hfam γ hγ'
        rwa [hre'] at this
      have habne : rPa ≠ rPb := hab
      -- core sizes and interaction-card facts
      have hcoreA : 2 * t ≤ (Dset rPa).card + n := hcoreLB γa hγa
      have hcoreB : 2 * t ≤ (Dset rPb).card + n := by
        have h := hcoreLB γb hγb
        rwa [show rf γb = rPb from rfl] at h
      have hfaLB : (Dset rPb).card ≤ (Af γ₀ \ Dset rPa).card + d := by
        calc (Dset rPb).card
            ≤ ((Af γ₀ \ Dset rPa) ∪ Zset rPa rPb).card :=
              Finset.card_le_card (hinteract rPa rPb)
        _ ≤ (Af γ₀ \ Dset rPa).card + (Zset rPa rPb).card := Finset.card_union_le _ _
        _ ≤ (Af γ₀ \ Dset rPa).card + d := by
              have := hZcard rPa rPb hadeg hbdeg habne
              omega
      have hfbLB : (Dset rPa).card ≤ (Af γ₀ \ Dset rPb).card + d := by
        calc (Dset rPa).card
            ≤ ((Af γ₀ \ Dset rPb) ∪ Zset rPb rPa).card :=
              Finset.card_le_card (hinteract rPb rPa)
        _ ≤ (Af γ₀ \ Dset rPb).card + (Zset rPb rPa).card := Finset.card_union_le _ _
        _ ≤ (Af γ₀ \ Dset rPb).card + d := by
              have := hZcard rPb rPa hbdeg hadeg (Ne.symm habne)
              omega
      -- the two family counts (members + γ₀'s fibre + core)
      have hcountA := hfamCount rPa Γa (Af γ₀ \ Dset rPa) hΓasub hfama
        (Finset.Subset.refl _)
        (fun γ hγ => hfibDisj rPa γ γ₀ (Finset.ne_of_mem_erase (hΓasub hγ))
          (hfama γ hγ) (hγ₀fam rPa))
      have hcountB := hfamCount rPb Γb (Af γ₀ \ Dset rPb) hΓbsub hfamb
        (Finset.Subset.refl _)
        (fun γ hγ => hfibDisj rPb γ γ₀ (Finset.ne_of_mem_erase (hΓbsub hγ))
          (hfamb γ hγ) (hγ₀fam rPb))
      -- abbreviations
      set Da := (Dset rPa).card with hDa
      set Db := (Dset rPb).card with hDb
      set fa := (Af γ₀ \ Dset rPa).card with hfa
      set fb := (Af γ₀ \ Dset rPb).card with hfb
      set μa := Γa.card with hμa
      set μb := Γb.card with hμb
      have hμa1 : 1 ≤ μa := Finset.card_pos.mpr ⟨γa, hγaΓa⟩
      have hμb1 : 1 ≤ μb := Finset.card_pos.mpr ⟨γb, hγbΓb⟩
      -- member sum lower bounds
      have hSa1 : μa * (t - Da) ≤ ∑ γ ∈ Γa, (Af γ \ Dset rPa).card := by
        have := Finset.card_nsmul_le_sum Γa (fun γ => (Af γ \ Dset rPa).card)
          (t - Da) (fun γ hγ => by
            have := (hfibLB rPa hadeg γ (hΓ'sub (hΓasub hγ)) (hfama γ hγ)).2
            show t - Da ≤ (Af γ \ Dset rPa).card
            omega)
        simpa using this
      have hSa2 : μa ≤ ∑ γ ∈ Γa, (Af γ \ Dset rPa).card := by
        have := Finset.card_nsmul_le_sum Γa (fun γ => (Af γ \ Dset rPa).card) 1
          (fun γ hγ => (hfibLB rPa hadeg γ (hΓ'sub (hΓasub hγ)) (hfama γ hγ)).1)
        simpa using this
      have hSb1 : μb * (t - Db) ≤ ∑ γ ∈ Γb, (Af γ \ Dset rPb).card := by
        have := Finset.card_nsmul_le_sum Γb (fun γ => (Af γ \ Dset rPb).card)
          (t - Db) (fun γ hγ => by
            have := (hfibLB rPb hbdeg γ (hΓ'sub (hΓbsub hγ)) (hfamb γ hγ)).2
            show t - Db ≤ (Af γ \ Dset rPb).card
            omega)
        simpa using this
      have hSb2 : μb ≤ ∑ γ ∈ Γb, (Af γ \ Dset rPb).card := by
        have := Finset.card_nsmul_le_sum Γb (fun γ => (Af γ \ Dset rPb).card) 1
          (fun γ hγ => (hfibLB rPb hbdeg γ (hΓ'sub (hΓbsub hγ)) (hfamb γ hγ)).1)
        simpa using this
      have hμsum : n - t + 1 ≤ μa + μb := by
        rw [hμa, hμb, hsplit, hΓ'card]
        omega
      -- linearized counts
      have hCA1 : μa * (t - Da) + fa + Da ≤ n := by
        have := le_trans hSa1 (le_refl _)
        omega
      have hCA2 : μa + fa + Da ≤ n := by
        have := le_trans hSa2 (le_refl _)
        omega
      have hCB1 : μb * (t - Db) + fb + Db ≤ n := by
        have := le_trans hSb1 (le_refl _)
        omega
      have hCB2 : μb + fb + Db ≤ n := by
        have := le_trans hSb2 (le_refl _)
        omega
      -- products needed below, in atom form
      have hsbP : t - Db ≤ μb * (t - Db) := by
        conv_lhs => rw [← one_mul (t - Db)]
        exact Nat.mul_le_mul hμb1 le_rfl
      have hsaP : t - Da ≤ μa * (t - Da) := by
        conv_lhs => rw [← one_mul (t - Da)]
        exact Nat.mul_le_mul hμa1 le_rfl
      -- case: one core at least t
      rcases Nat.lt_or_ge Da t with hDat | hDat
      rcases Nat.lt_or_ge Db t with hDbt | hDbt
      · -- both cores < t: the full chain
        obtain ⟨μa', hμa'⟩ : ∃ k, μa = k + 1 := ⟨μa - 1, by omega⟩
        obtain ⟨μb', hμb'⟩ : ∃ k, μb = k + 1 := ⟨μb - 1, by omega⟩
        have hRa : μa * (t - Da) = μa' * (t - Da) + (t - Da) := by
          rw [hμa']; ring
        have hRb : μb * (t - Db) = μb' * (t - Db) + (t - Db) := by
          rw [hμb']; ring
        -- Bv ≤ t − Da and Bv ≤ t − Db, where Bv := 2t − (n+d)
        have hBva : 2 * t - (n + d) ≤ t - Da := by
          -- Da ≤ fb + d and t + fb ≤ n (from the b-count)
          have h1 : t + fb ≤ n := by omega
          omega
        have hBvb : 2 * t - (n + d) ≤ t - Db := by
          have h1 : t + fa ≤ n := by omega
          omega
        have hqa : μa' * (2 * t - (n + d)) ≤ μa' * (t - Da) :=
          Nat.mul_le_mul le_rfl hBva
        have hqb : μb' * (2 * t - (n + d)) ≤ μb' * (t - Db) :=
          Nat.mul_le_mul le_rfl hBvb
        -- the summed product bound
        have hWle : (n - t - 1) * (2 * t - (n + d))
            ≤ μa' * (2 * t - (n + d)) + μb' * (2 * t - (n + d)) := by
          have h1 : n - t - 1 ≤ μa' + μb' := by omega
          have h2 : (n - t - 1) * (2 * t - (n + d))
              ≤ (μa' + μb') * (2 * t - (n + d)) := Nat.mul_le_mul h1 le_rfl
          rwa [add_mul] at h2
        have hWge : (n - t - 1) * 2 ≤ (n - t - 1) * (2 * t - (n + d)) :=
          Nat.mul_le_mul le_rfl (by omega)
        -- close
        have hfaBv : 2 * t - (n + d) ≤ fa := by omega
        have hfbBv : 2 * t - (n + d) ≤ fb := by omega
        omega
      · -- Db ≥ t: dead via the a-side count and the interaction
        -- t − Da ≤ fibre sum, t ≤ Db ≤ fa + d, t + fa ≤ … forces 2t ≤ n + d
        have h1 : t - Da + fa + Da ≤ n := by omega
        omega
      · -- Da ≥ t: dead via the b-side count and the interaction
        have h1 : t - Db + fb + Db ≤ n := by omega
        omega
    · -- K ≥ 3: the interaction law floods γ₀'s fibre — dead on the strip
      push Not at hK2
      obtain ⟨γc, hγc, hca, hcb⟩ := hK2
      set rPa := rf γa with hrPa
      set rPb := rf γb with hrPb
      set rPc := rf γc with hrPc
      have hadeg : rPa.natDegree ≤ d := hrdeg γa hγa
      have hbdeg : rPb.natDegree ≤ d := hrdeg γb hγb
      have hcdeg : rPc.natDegree ≤ d := hrdeg γc hγc
      -- the three cores
      have hcoreA : 2 * t ≤ (Dset rPa).card + n := hcoreLB γa hγa
      have hcoreB : 2 * t ≤ (Dset rPb).card + n := hcoreLB γb hγb
      have hcoreC : 2 * t ≤ (Dset rPc).card + n := hcoreLB γc hγc
      -- both foreign cores flood the a-fibre of γ₀
      have hflood : (Dset rPb).card + (Dset rPc).card
          ≤ (Af γ₀ \ Dset rPa).card + 3 * d := by
        have hsubU : Dset rPb ∪ Dset rPc
            ⊆ (Af γ₀ \ Dset rPa) ∪ (Zset rPa rPb ∪ Zset rPa rPc) := by
          intro i hi
          rcases Finset.mem_union.mp hi with hib | hic
          · rcases Finset.mem_union.mp (hinteract rPa rPb hib) with h | h
            · exact Finset.mem_union_left _ h
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
          · rcases Finset.mem_union.mp (hinteract rPa rPc hic) with h | h
            · exact Finset.mem_union_left _ h
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
        have hZab := hZcard rPa rPb hadeg hbdeg hab
        have hZac := hZcard rPa rPc hadeg hcdeg (Ne.symm hca)
        have hZbc := hZcard rPb rPc hbdeg hcdeg (Ne.symm hcb)
        have hUcard : (Dset rPb ∪ Dset rPc).card
            ≤ (Af γ₀ \ Dset rPa).card + 2 * d := by
          calc (Dset rPb ∪ Dset rPc).card
              ≤ ((Af γ₀ \ Dset rPa) ∪ (Zset rPa rPb ∪ Zset rPa rPc)).card :=
                Finset.card_le_card hsubU
          _ ≤ (Af γ₀ \ Dset rPa).card + (Zset rPa rPb ∪ Zset rPa rPc).card :=
                Finset.card_union_le _ _
          _ ≤ (Af γ₀ \ Dset rPa).card + ((Zset rPa rPb).card + (Zset rPa rPc).card) := by
                have := Finset.card_union_le (Zset rPa rPb) (Zset rPa rPc)
                omega
          _ ≤ (Af γ₀ \ Dset rPa).card + 2 * d := by omega
        have hIcard : (Dset rPb ∩ Dset rPc).card ≤ d := by
          calc (Dset rPb ∩ Dset rPc).card ≤ (Zset rPb rPc).card :=
            Finset.card_le_card (hcoreInter rPb rPc)
          _ ≤ d := hZbc
        have hkey := Finset.card_union_add_card_inter (Dset rPb) (Dset rPc)
        omega
      -- the a-family count with Φ = {γa}
      have hγaid : qf γa = aOf rPa + Polynomial.C γa * rPa := hfam γa hγa
      have hcount := hfamCount rPa {γa} (Af γ₀ \ Dset rPa)
        (Finset.singleton_subset_iff.mpr hγa)
        (fun γ hγ => by rw [Finset.mem_singleton.mp hγ]; exact hγaid)
        (Finset.Subset.refl _)
        (fun γ hγ => by
          rw [Finset.mem_singleton.mp hγ]
          exact hfibDisj rPa γa γ₀ (Finset.ne_of_mem_erase hγa) hγaid (hγ₀fam rPa))
      rw [Finset.sum_singleton] at hcount
      have hfibA := hfibLB rPa hadeg γa (hΓ'sub hγa) hγaid
      omega

/-! ## Radius corollaries -/

/-- Witness-size discharge at the exact radius `δ = 1 − t/n`. -/
private lemma hwit_of_exact {n t : ℕ} (hn0 : 0 < n) (htn : t ≤ n)
    (S : Finset (Fin n))
    (h : (S.card : ℝ≥0) ≥ (1 - (1 - (t : ℝ≥0) / (n : ℝ≥0)))
      * (Fintype.card (Fin n) : ℝ≥0)) : t ≤ S.card := by
  have hn0' : ((n : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hn0.ne'
  have hle1 : (t : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
    rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0'))]
    exact_mod_cast htn
  have h1δ : (1 : ℝ≥0) - (1 - (t : ℝ≥0) / (n : ℝ≥0)) = (t : ℝ≥0) / (n : ℝ≥0) :=
    tsub_tsub_cancel_of_le hle1
  rw [h1δ, Fintype.card_fin, div_mul_cancel₀ _ hn0'] at h
  exact_mod_cast h

/-- Witness-size discharge on the whole band `δ < (n−t+1)/n`. -/
private lemma hwit_of_band {n t : ℕ} (hn0 : 0 < n) (ht1 : 1 ≤ t) (htn : t ≤ n)
    {δ : ℝ≥0} (hδ : δ < ((n - t + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0))
    (S : Finset (Fin n))
    (h : (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) : t ≤ S.card := by
  have hn0' : ((n : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hn0.ne'
  have hn0lt : (0 : ℝ≥0) < ((n : ℕ) : ℝ≥0) :=
    lt_of_le_of_ne (zero_le _) (Ne.symm hn0')
  -- (t−1)/n < 1 − δ
  have hkey : ((t - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) < 1 - δ := by
    rw [lt_tsub_iff_right]
    have hsum : ((t - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) + δ
        < ((t - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)
          + ((n - t + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := by
      gcongr
    have hone : ((t - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)
        + ((n - t + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) = 1 := by
      rw [← add_div]
      have hcast : ((t - 1 : ℕ) : ℝ≥0) + ((n - t + 1 : ℕ) : ℝ≥0)
          = ((n : ℕ) : ℝ≥0) := by
        have : (t - 1) + (n - t + 1) = n := by omega
        exact_mod_cast congrArg (Nat.cast (R := ℝ≥0)) this
      rw [hcast, div_self hn0']
    rwa [hone] at hsum
  -- so (t−1 : ℝ≥0) < (1−δ)·n ≤ S.card
  have hlt : ((t - 1 : ℕ) : ℝ≥0) < (1 - δ) * ((n : ℕ) : ℝ≥0) := by
    have h1 : ((t - 1 : ℕ) : ℝ≥0) = (((t - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0))
        * ((n : ℕ) : ℝ≥0) := by
      rw [div_mul_cancel₀ _ hn0']
    rw [h1]
    exact mul_lt_mul_of_pos_right hkey hn0lt
  rw [Fintype.card_fin] at h
  have hfin : ((t - 1 : ℕ) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hlt h
  have : t - 1 < S.card := by exact_mod_cast hfin
  omega

open Classical in
/-- **Five-thirds strip, `ε_mca` form**: on the strip, the MCA error at radius
`1 − t/n` is at most `(n−t+1)/p` — the simplex value. -/
theorem fiveThirds_epsMCA_le {p n : ℕ} [Fact p.Prime] [NeZero n]
    {d t : ℕ} {g : ZMod p} (hg : orderOf g = n)
    (htn : t ≤ n) (hB : n + d + 2 ≤ 2 * t) (h53 : 3 * n + 3 * d + 1 ≤ 5 * t) :
    epsMCA (F := ZMod p) (evalCode g n d) (1 - (t : ℝ≥0) / (n : ℝ≥0))
      ≤ ((n - t + 1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h := ProximityGap.epsMCA_le_of_card_le (F := ZMod p)
    (evalCode g n d) (1 - (t : ℝ≥0) / (n : ℝ≥0)) (n - t + 1)
    (fun u => fiveThirds_badScalars_card_le hg htn hB h53 _
      (fun S hS => hwit_of_exact hn0 htn S hS) (u 0) (u 1))
  refine le_trans h (le_of_eq ?_)
  have hcardF : (Fintype.card (ZMod p) : ℝ≥0) = ((p : ℕ) : ℝ≥0) := by
    rw [ZMod.card p]
  rw [hcardF, ENNReal.coe_natCast, ENNReal.coe_natCast]

open Classical in
/-- **Five-thirds strip, band form**: the same bound holds at EVERY radius
`δ < (n−t+1)/n` (the witness threshold stays `t` on the whole band). -/
theorem fiveThirds_epsMCA_le_of_lt {p n : ℕ} [Fact p.Prime] [NeZero n]
    {d t : ℕ} {g : ZMod p} (hg : orderOf g = n)
    (htn : t ≤ n) (hB : n + d + 2 ≤ 2 * t) (h53 : 3 * n + 3 * d + 1 ≤ 5 * t)
    {δ : ℝ≥0} (hδ : δ < ((n - t + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) :
    epsMCA (F := ZMod p) (evalCode g n d) δ
      ≤ ((n - t + 1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have ht1 : 1 ≤ t := by omega
  have h := ProximityGap.epsMCA_le_of_card_le (F := ZMod p)
    (evalCode g n d) δ (n - t + 1)
    (fun u => fiveThirds_badScalars_card_le hg htn hB h53 _
      (fun S hS => hwit_of_band hn0 ht1 htn hδ S hS) (u 0) (u 1))
  refine le_trans h (le_of_eq ?_)
  have hcardF : (Fintype.card (ZMod p) : ℝ≥0) = ((p : ℕ) : ℝ≥0) := by
    rw [ZMod.card p]
  rw [hcardF, ENNReal.coe_natCast, ENNReal.coe_natCast]

/-! ## The exact band theorems -/

/-- **The exact `ε_mca` value on the strip**: the good side above meets the landed
simplex floor — `ε_mca(C, 1 − t/n) = (n−t+1)/p` exactly, for every smooth instance
and every strip threshold with `d+2 ≤ t ≤ n−1`. -/
theorem fiveThirds_epsMCA_eq {p n : ℕ} [Fact p.Prime] [NeZero n]
    {d t : ℕ} {g : ZMod p} (hg : orderOf g = n)
    (hdt : d + 2 ≤ t) (htn : t + 1 ≤ n)
    (hB : n + d + 2 ≤ 2 * t) (h53 : 3 * n + 3 * d + 1 ≤ 5 * t) :
    epsMCA (F := ZMod p) (evalCode g n d) (1 - (t : ℝ≥0) / (n : ℝ≥0))
      = ((n - t + 1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  refine le_antisymm (fiveThirds_epsMCA_le hg (by omega) hB h53) ?_
  have h := simplex_epsMCA_lower_bound (p := p) (n := n) (d := d) (e := n - t)
    (g := g) hg (by omega) (by omega)
  have he : n - (n - t) = t := by omega
  rw [he] at h
  have hc : ((n - t) + 1 : ℕ) = (n - t + 1 : ℕ) := rfl
  exact_mod_cast h

open Classical in
/-- **THE FIVE-THIRDS δ* PIN (general)**: on the strip with `d+3 ≤ t ≤ n`, for every
budget `ε* ∈ [(n−t+1)/p, (n−t+2)/p)`,

  `mcaDeltaStar (evalCode g n d) ε* = (n−t+1)/n`  — EXACTLY.

The good side is the ratio-pigeonhole bound on the band `δ < (n−t+1)/n`; the bad
side is the landed simplex floor at threshold `t−1`.  Beyond the granularity ladder
(`3t < 2n+d+1`, i.e. `n > 4d−2` near the strip floor) these are NEW exact values of
the δ*(ε*) staircase. -/
theorem fiveThirds_deltaStar_pin {p n : ℕ} [Fact p.Prime] [NeZero n]
    {d t : ℕ} {g : ZMod p} (hg : orderOf g = n)
    (hdt : d + 3 ≤ t) (htn : t ≤ n)
    (hB : n + d + 2 ≤ 2 * t) (h53 : 3 * n + 3 * d + 1 ≤ 5 * t)
    (εstar : ℝ≥0∞)
    (hlo : ((n - t + 1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((n - t + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar
      = ((n - t + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn0' : ((n : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hn0.ne'
  have hradle1 : ((n - t + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) ≤ 1 := by
    rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0'))]
    exact_mod_cast (by omega : n - t + 1 ≤ n)
  refine le_antisymm ?_ ?_
  · -- bad side: the simplex floor at threshold t − 1 carries n − t + 2 scalars
    refine mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi ?_)
    have h := simplex_epsMCA_lower_bound (p := p) (n := n) (d := d) (e := n - t + 1)
      (g := g) hg (by omega) (by omega)
    have he : n - (n - t + 1) = t - 1 := by omega
    rw [he] at h
    have hrad : (1 : ℝ≥0) - ((t - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)
        = ((n - t + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := by
      refine tsub_eq_of_eq_add ?_
      rw [← add_div]
      have hcast : ((n - t + 1 : ℕ) : ℝ≥0) + ((t - 1 : ℕ) : ℝ≥0)
          = ((n : ℕ) : ℝ≥0) := by
        have : (n - t + 1) + (t - 1) = n := by omega
        exact_mod_cast congrArg (Nat.cast (R := ℝ≥0)) this
      rw [hcast, div_self hn0']
    rw [hrad] at h
    have hcnt : ((n - t + 1) + 1 : ℕ) = (n - t + 2 : ℕ) := by omega
    rw [hcnt] at h
    exact h
  · -- good side: every radius below (n−t+1)/n is good
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hmem : c ∈ mcaGoodRadii (F := ZMod p) (A := ZMod p)
        (evalCode g n d) εstar := by
      refine ⟨le_of_lt (lt_of_lt_of_le hc2 hradle1), ?_⟩
      exact le_trans (fiveThirds_epsMCA_le_of_lt hg htn hB h53 hc2) hlo
    have hle := le_mcaDeltaStar_of_good (F := ZMod p) (A := ZMod p)
      (evalCode g n d) εstar hmem.1 hmem.2
    exact absurd hle (not_le.mpr hc1)

/-! ## The first beyond-ladder exact band at the deployed shape
(`p = 12289`, `n = 16`, `d = 2`, rate 3/16)

The new rung is `t = 11` (`5·11 = 55 = 3n+3d+1` exactly on the strip boundary):
the granularity ladder (`GranularityLadderRS`, `3(j−1)+k ≤ n`) stops at `t = 12`.
The band's upper edge is the antipodal pencil count `8` at `t = 10` (NOT the
simplex `7`): the value `j = 7` is skipped and the band is TWO budget units wide. -/

section Concrete12289

local instance fact_prime_12289''''' : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- **The exact MCA error at the new rung**: `ε_mca(RS[F₁₂₂₈₉,16,d=2], 5/16) = 6/p`
— the first exact `ε_mca` value beyond the granularity ladder at the deployed
shape. -/
theorem epsMCA_eq_six_F12289_d2 :
    epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) (5 / 16 : ℝ≥0)
      = (6 : ℝ≥0∞) / (12289 : ℝ≥0∞) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := fiveThirds_epsMCA_eq (p := 12289) (n := 16) (d := 2) (t := 11)
    (g := (4134 : ZMod 12289)) orderOf_4134
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 : (1 : ℝ≥0) - ((11 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 5 / 16 := by
    have hd : ((11 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 11 / 16 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  have e2 : ((16 - 11 + 1 : ℕ) : ℝ≥0∞) = (6 : ℝ≥0∞) := by norm_num
  have e3 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  rw [e1, e2, e3] at h
  exact h

/-- **THE FIRST BEYOND-LADDER EXACT BAND**: for every `ε* ∈ [6/p, 8/p)`,

  `δ*(RS[F₁₂₂₈₉, 16, d = 2], ε*) = 3/8`  — EXACTLY.

Good side: the ratio-pigeonhole strip bound at `t = 11` (`≤ 6` bad scalars at every
radius `< 3/8`).  Bad side: the landed antipodal pencil (`8` scalars at radius
`3/8`, `pencil_rung_epsMCA_lower_bound` at `h = 8, s = 2`) — so the band is two
budget units wide, skipping `j = 7` entirely.  The granularity ladder reaches only
`ε* < 6/p` at this cell; this is the next exact step of the δ*(ε*) staircase. -/
theorem deltaStar_eq_threeEighths_F12289_d2 (εstar : ℝ≥0∞)
    (hlo : (6 : ℝ≥0∞) / (12289 : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < (8 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar = 3 / 8 := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  refine le_antisymm ?_ ?_
  · -- bad side: the antipodal pencil (X^8, X^10): 8 scalars at radius 3/8
    refine mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi ?_)
    have h := pencil_rung_epsMCA_lower_bound (p := 12289) (n := 16) (h := 8)
      (d := 2) (s := 2) (by norm_num) (by norm_num)
      (g := (4134 : ZMod 12289)) orderOf_4134
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have e1 : ((16 / 2 : ℕ) : ℝ≥0∞) = (8 : ℝ≥0∞) := by norm_num
    have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
    have e3 : (1 : ℝ≥0) - ((8 + 2 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 3 / 8 := by
      have hd : ((8 + 2 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 5 / 8 := by norm_num
      rw [hd]
      refine tsub_eq_of_eq_add ?_
      norm_num
    rw [e1, e2, e3] at h
    exact h
  · -- good side: every radius below 3/8 = 6/16 carries ≤ 6 bad scalars
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hband : c < ((16 - 11 + 1 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) := by
      have he : ((16 - 11 + 1 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 3 / 8 := by
        norm_num
      rw [he]
      exact hc2
    have hgood := fiveThirds_epsMCA_le_of_lt (p := 12289) (n := 16) (d := 2)
      (t := 11) (g := (4134 : ZMod 12289)) orderOf_4134
      (by norm_num) (by norm_num) (by norm_num) hband
    have e2 : ((16 - 11 + 1 : ℕ) : ℝ≥0∞) = (6 : ℝ≥0∞) := by norm_num
    have e3 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
    rw [e2, e3] at hgood
    have hmem : c ∈ mcaGoodRadii (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 2 : Set (Fin 16 → ZMod 12289)) εstar := by
      refine ⟨le_of_lt (lt_of_lt_of_le hc2 (show (3 / 8 : ℝ≥0) ≤ 1 by
        rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]; norm_num)), ?_⟩
      exact le_trans hgood hlo
    have hle := le_mcaDeltaStar_of_good (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar hmem.1 hmem.2
    exact absurd hle (not_le.mpr hc1)

end Concrete12289

end ArkLib.ProximityGap.RatioPigeonhole

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.RatioPigeonhole.fiveThirds_badScalars_card_le
#print axioms ArkLib.ProximityGap.RatioPigeonhole.fiveThirds_epsMCA_le
#print axioms ArkLib.ProximityGap.RatioPigeonhole.fiveThirds_epsMCA_le_of_lt
#print axioms ArkLib.ProximityGap.RatioPigeonhole.fiveThirds_epsMCA_eq
#print axioms ArkLib.ProximityGap.RatioPigeonhole.fiveThirds_deltaStar_pin
#print axioms ArkLib.ProximityGap.RatioPigeonhole.epsMCA_eq_six_F12289_d2
#print axioms ArkLib.ProximityGap.RatioPigeonhole.deltaStar_eq_threeEighths_F12289_d2
