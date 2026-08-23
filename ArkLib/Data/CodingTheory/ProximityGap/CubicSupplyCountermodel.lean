/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The Sylvester-cubic countermodel to the "linear supply law" (#389)

The #389 census concluded the per-word `ExplainableCoreSupply` was "empirically
linear, `B = O(n)`".  This is FALSE.  The graph of `w(x) = x³` (a function graph,
one point per domain `x`) carries `Θ(n²)` explainable 3-cores — the classical
Sylvester cubic, where three points `(a,a³),(b,b³),(c,c³)` are collinear iff
`a + b + c = 0`.  Each such collinear triple is explained by a single affine
codeword of `rsCode dom 2`.

* `cubic_triple_explainable` — the mechanism: a domain triple summing to zero is
  explained by the line through two of its cubic points.
* `explainable_core_supply_ge_sumZero` — hence `B ≥ #{3-subsets summing to 0}`.
* `sumZero_card_quadratic` / `cubic_supply_quadratic` — on the full field
  (`n = |F|`), `#{sum-zero 3-subsets} ≥ (n²−3n)/9`, so `n² ≤ 9·B + 3·n`: **no
  `B = O(n)` is admissible**.  Sparse-robust (probe `_scratch_cubic_and_t4.py`:
  the count is independent of `|F|`).

This is the unconditional obstruction behind the asymptotic vacuity of the
conditional linear law `mean_degree_law_deep_general` (whose `hdeep` hypothesis
`2s·cap·C(n,s)·(n−s) ≤ t²(t−s)C(t,s)` is `10n(n−1) ≤ 54` at `k=2`, false for
`n ≥ 3`).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Cubic

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The cubic word: `w(x) = (dom x)³`. -/
def cubicWord (dom : Fin n ↪ F) : Fin n → F := fun x => (dom x) ^ 3

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- **The Sylvester mechanism**: any triple of domain points whose values sum to
zero is collinear, hence explained by a single affine codeword of `rsCode dom 2`.
The explainer is the line through `(a,a³)` and `(b,b³)`; it passes through the
third point exactly because `a + b + c = 0` (`c³ = (−a−b)³`). -/
theorem cubic_triple_explainable (dom : Fin n ↪ F) {i j l : Fin n}
    (hsum : dom i + dom j + dom l = 0) :
    ExplainableOn dom 2 (cubicWord dom) {i, j, l} := by
  set a := dom i with ha
  set b := dom j with hb
  set P : F[X] := (C (a^2 + a*b + b^2)) * (X - C a) + C (a^3) with hP
  refine ⟨fun x => P.eval (dom x), ⟨P, ?_, rfl⟩, ?_⟩
  · -- degree < 2
    have h1 : ((C (a^2 + a*b + b^2)) * (X - C a)).degree ≤ 1 := by
      calc ((C (a^2 + a*b + b^2)) * (X - C a)).degree
          ≤ (C (a^2 + a*b + b^2)).degree + (X - C a).degree :=
            Polynomial.degree_mul_le _ _
        _ ≤ 0 + 1 := by
            rw [Polynomial.degree_X_sub_C]
            exact add_le_add Polynomial.degree_C_le le_rfl
        _ = 1 := zero_add 1
    have hle : P.degree ≤ 1 := by
      rw [hP]
      calc ((C (a^2 + a*b + b^2)) * (X - C a) + C (a^3)).degree
          ≤ max ((C (a^2 + a*b + b^2)) * (X - C a)).degree (C (a^3)).degree :=
            Polynomial.degree_add_le _ _
        _ ≤ 1 := max_le h1 (le_trans Polynomial.degree_C_le (by decide))
    exact lt_of_le_of_lt hle (by exact_mod_cast Nat.one_lt_two)
  · -- agreement on {i, j, l}
    intro x hx
    show P.eval (dom x) = cubicWord dom x
    rw [hP, cubicWord]
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · rw [h, ← ha]; ring
    · rw [h, ← hb]; ring
    · -- x = l, dom l = c with a + b + c = 0; cofactor (a+b+c)(−c²+(a+b)c−ab)
      rw [h]
      linear_combination (-(dom l)^2 + (a + b) * (dom l) - a * b) * hsum

open Classical in
/-- Every 3-subset of the domain whose values sum to zero is an explainable
3-core of the cubic word. -/
theorem sumZero_subset_explainable (dom : Fin n ↪ F) :
    ((Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0))
      ⊆ (Finset.univ.powersetCard 3).filter
          (fun T => ExplainableOn dom 2 (cubicWord dom) T) := by
  intro T hT
  obtain ⟨hTmem, hsum⟩ := Finset.mem_filter.mp hT
  obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
  refine Finset.mem_filter.mpr ⟨hTmem, ?_⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hTcard
  have hsum' : dom a + dom b + dom c = 0 := by
    rw [Finset.sum_insert (by simp [hab, hac]),
      Finset.sum_insert (by simp [hbc]), Finset.sum_singleton] at hsum
    linear_combination hsum
  exact cubic_triple_explainable dom hsum'

open Classical in
/-- **The cubic countermodel reduction**: any `ExplainableCoreSupply` bound `B`
for the cubic word at `(k, m) = (2, 0)` (core size `3`) is at least the number
of domain 3-subsets summing to zero — the Sylvester collinear triples. -/
theorem explainable_core_supply_ge_sumZero (dom : Fin n ↪ F) {B : ℕ}
    (hB : ExplainableCoreSupply dom 2 0 B) :
    ((Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0)).card ≤ B :=
  le_trans (Finset.card_le_card (sumZero_subset_explainable dom)) (hB (cubicWord dom))

/-- **The quadratic lower bound on sum-zero 3-subsets of the full field.** When
`dom` is a bijection (the full evaluation domain `n = |F|`), the domain 3-subsets
summing to zero number `≥ (n² − 3n)/9`: pairs `(a,b)` with `a, b, −(a+b)` pairwise
distinct number `≥ n² − 3n`, and `(a,b) ↦ {a, b, −(a+b)}` is at most `9`-to-one. -/
theorem sumZero_card_quadratic (dom : Fin n ↪ F)
    (hbij : Function.Bijective (⇑dom : Fin n → F)) :
    (n : ℕ) ^ 2
      ≤ 9 * ((Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0)).card
        + 3 * n := by
  classical
  set e : Fin n ≃ F := Equiv.ofBijective _ hbij with he
  have hde : ∀ x, dom x = e x := fun x => (Equiv.ofBijective_apply _ hbij x).symm
  have hen : ∀ y, dom (e.symm y) = y := fun y => by rw [hde]; exact e.apply_symm_apply y
  set neg : Fin n × Fin n → Fin n := fun p => e.symm (-(dom p.1 + dom p.2)) with hnegdef
  have hdomneg : ∀ p, dom (neg p) = -(dom p.1 + dom p.2) := fun p => hen _
  set f : Fin n × Fin n → Finset (Fin n) := fun p => {p.1, p.2, neg p} with hfdef
  set good : Fin n × Fin n → Prop := fun p =>
    dom p.1 ≠ dom p.2 ∧ dom p.1 ≠ -(dom p.1 + dom p.2)
      ∧ dom p.2 ≠ -(dom p.1 + dom p.2) with hgood
  set S : Finset (Fin n × Fin n) := Finset.univ.filter good with hSdef
  set Z : Finset (Finset (Fin n)) :=
    (Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0) with hZdef
  have hdistinct : ∀ p ∈ S, p.1 ≠ p.2 ∧ p.1 ≠ neg p ∧ p.2 ≠ neg p := by
    intro p hp
    obtain ⟨hA, hB, hC⟩ := (Finset.mem_filter.mp hp).2
    refine ⟨fun h => hA (congrArg (⇑dom) h), fun h => hB ?_, fun h => hC ?_⟩
    · rw [← hdomneg p]; exact congrArg (⇑dom) h
    · rw [← hdomneg p]; exact congrArg (⇑dom) h
  have hmaps : ∀ p ∈ S, f p ∈ Z := by
    intro p hp
    obtain ⟨h12, h1n, h2n⟩ := hdistinct p hp
    have hcard3 : (f p).card = 3 := by
      rw [hfdef, Finset.card_insert_of_notMem (by simp [h12, h1n]),
        Finset.card_insert_of_notMem (by simp [h2n]), Finset.card_singleton]
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard3⟩, ?_⟩
    rw [hfdef, Finset.sum_insert (by simp [h12, h1n]),
      Finset.sum_insert (by simp [h2n]), Finset.sum_singleton, hdomneg]
    ring
  have hfiber : ∀ U ∈ Z, (S.filter (fun p => f p = U)).card ≤ 9 := by
    intro U hU
    have hUcard : U.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).2
    have hsub : S.filter (fun p => f p = U) ⊆ U ×ˢ U := by
      intro p hp
      obtain ⟨-, hfU⟩ := Finset.mem_filter.mp hp
      have h1 : p.1 ∈ f p := by rw [hfdef]; exact Finset.mem_insert_self _ _
      have h2 : p.2 ∈ f p := by
        rw [hfdef]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      rw [hfU] at h1 h2
      exact Finset.mem_product.mpr ⟨h1, h2⟩
    calc (S.filter (fun p => f p = U)).card ≤ (U ×ˢ U).card := Finset.card_le_card hsub
      _ = U.card * U.card := Finset.card_product _ _
      _ = 9 := by rw [hUcard]
  have hSZ : S.card ≤ 9 * Z.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 9 hfiber
  have hbad : (Finset.univ.filter (fun p : Fin n × Fin n => ¬ good p)).card ≤ 3 * n := by
    have hcov : Finset.univ.filter (fun p : Fin n × Fin n => ¬ good p)
        ⊆ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2))
          ∪ (Finset.univ.filter (fun p : Fin n × Fin n => dom p.1 = -(dom p.1 + dom p.2)))
          ∪ (Finset.univ.filter (fun p : Fin n × Fin n => dom p.2 = -(dom p.1 + dom p.2))) := by
      intro p hp
      have hng := (Finset.mem_filter.mp hp).2
      simp only [hgood, not_and_or, not_not] at hng
      rcases hng with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbij.1 h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hd1 : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)).card ≤ n := by
      refine le_trans (Finset.card_le_card_of_injOn (fun p => p.1)
        (fun _ _ => Finset.mem_univ _) ?_) (le_of_eq (by simp))
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact Prod.ext hab (ha'.symm.trans (hab.trans hb'))
    have hd2 : (Finset.univ.filter
        (fun p : Fin n × Fin n => dom p.1 = -(dom p.1 + dom p.2))).card ≤ n := by
      refine le_trans (Finset.card_le_card_of_injOn (fun p => p.1)
        (fun _ _ => Finset.mem_univ _) ?_) (le_of_eq (by simp))
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      refine Prod.ext hab (hbij.1 ?_)
      have hdab : dom a.1 = dom b.1 := congrArg (⇑dom) hab
      linear_combination ha' - hb' - 2 * hdab
    have hd3 : (Finset.univ.filter
        (fun p : Fin n × Fin n => dom p.2 = -(dom p.1 + dom p.2))).card ≤ n := by
      refine le_trans (Finset.card_le_card_of_injOn (fun p => p.2)
        (fun _ _ => Finset.mem_univ _) ?_) (le_of_eq (by simp))
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      refine Prod.ext (hbij.1 ?_) hab
      have hdab : dom a.2 = dom b.2 := congrArg (⇑dom) hab
      linear_combination ha' - hb' - 2 * hdab
    calc (Finset.univ.filter (fun p : Fin n × Fin n => ¬ good p)).card
        ≤ _ := Finset.card_le_card hcov
      _ ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ (n + n) + n := by
          gcongr
          exact le_trans (Finset.card_union_le _ _) (by omega)
      _ = 3 * n := by ring
  have hsplit : S.card
      + (Finset.univ.filter (fun p : Fin n × Fin n => ¬ good p)).card = n ^ 2 := by
    rw [hSdef, Finset.filter_card_add_filter_neg_card_eq_card,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  calc (n : ℕ) ^ 2 = S.card
        + (Finset.univ.filter (fun p : Fin n × Fin n => ¬ good p)).card := hsplit.symm
    _ ≤ 9 * Z.card + 3 * n := by gcongr
    _ = 9 * ((Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0)).card
          + 3 * n := by rw [hZdef]

/-- **THE SYLVESTER-CUBIC COUNTERMODEL** to the "linear supply law" (#389): for the
full-domain RS code `rsCode dom 2` (`n = |F|`, e.g. `dom = F` for `F = ZMod q`), the
cubic word `x ↦ x³` forces any `ExplainableCoreSupply` bound `B` to satisfy

  `n² ≤ 9·B + 3·n`,  i.e.  `B ≥ (n² − 3n)/9 = Θ(n²)`.

So **no `B = O(n)` is admissible** — the per-word explainable-core supply is
quadratic, not linear.  Mechanism: Sylvester (1868), `(a,a³),(b,b³),(c,c³)`
collinear iff `a+b+c = 0`; a full field has `Θ(n²)` such triples, independent
of `|F|` (sparse-robust). -/
theorem cubic_supply_quadratic (dom : Fin n ↪ F)
    (hbij : Function.Bijective (⇑dom : Fin n → F)) {B : ℕ}
    (hB : ExplainableCoreSupply dom 2 0 B) :
    (n : ℕ) ^ 2 ≤ 9 * B + 3 * n :=
  le_trans (sumZero_card_quadratic dom hbij)
    (by gcongr; exact explainable_core_supply_ge_sumZero dom hB)

end ProximityGap.Cubic

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Cubic.cubic_triple_explainable
#print axioms ProximityGap.Cubic.explainable_core_supply_ge_sumZero
#print axioms ProximityGap.Cubic.cubic_supply_quadratic
