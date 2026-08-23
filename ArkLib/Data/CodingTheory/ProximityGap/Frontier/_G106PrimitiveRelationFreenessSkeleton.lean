/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G103CenteredTripleDepthFiveConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G104DepthSixStratifiedConsumer

/-!
# G106: the primitive-relation-freeness skeleton — antipodal-only relations kill every
disjoint primitive equal-sum mass

This file is the machine-checked convergence point of the two live lanes of the #466 δ*
campaign:

* the **padded-collision ladder** (G102–G105): G102 proved pair statistics dead at depth ≥ 5,
  G103 closed depth 5 from centered triples, G104 closed depth 6 from stratified primitive
  quadruples — the surviving fiber objects are *primitive* tuples (no antipodal pair, no
  zero-sum triple) with prescribed sums; and
* the **#444 window-interior core**: the char-p Lam–Leung transfer, i.e. the classification of
  short vanishing sums over the multiplicative subgroup `μ_n ⊂ F_p^×`.

**The named hypothesis.**  `AntipodalOnlyRelations S L`: every vanishing sum over `S` of
length `≤ L` is empty or contains an antipodal sub-pair `{y, -y}`.  Over ℂ this is the
Lam–Leung / Conway–Jones classification specialised to 2-power `n` (T.Y. Lam, K.H. Leung,
"On vanishing sums of roots of unity", J. Algebra 224 (2000); Conway–Jones, Acta Arith. 30
(1976)): for `n = 2^k` the only minimal vanishing sums of `n`-th roots of unity are antipodal
pairs.  The production instance the lane needs is `AntipodalOnlyRelations μ_{2^30} 220`
**in characteristic p** — the char-p Lam–Leung transfer — which is OPEN; this file consumes
it, it does not prove it.  `PrimitiveRelationFreeness` is the weaker sub-multiset form;
`prf_of_aor` records the implication.

**What is proved (axiom-clean, conditional only on the stated `hAOR` argument).**  With `S`
symmetric (`∀ x ∈ S, -x ∈ S`):

* `no_disjoint_primitive_equalSum_quad_pairs` (under `AntipodalOnlyRelations S 8`): no two
  antipodal-free 4-tuples from `S` with equal sums and disjoint value multisets exist.  Proof
  shape: the length-8 multiset (values of the first tuple) + (negated values of the second)
  vanishes, so AOR plants an antipodal pair in it; both elements in one half yield an
  antipodal pair of that tuple, and a split placement yields a shared value — every case is
  contradicted.  Zero-triple-freeness is NOT needed: antipodal-freeness plus disjointness
  suffices.
* `no_disjoint_centered_equalSum_triple_pairs` (under `AntipodalOnlyRelations S 6`): the
  depth-5 analog for G103's centered (`¬IsDeg`) triples.
* `disjointPrimQuadPairCount_eq_zero`, `disjointCentTriplePairCount_eq_zero`: the
  disjoint-refined equal-sum pair masses vanish identically — so under AOR the G103/G104
  concentration inputs reduce to the non-disjoint (shared-value) sectors of the J-masses.

The exclusion is total, not merely bounded.  Probe evidence: total suppression of disjoint
primitive equal-sum pairs on real subgroups, validated against a random control
(`scripts/probes/probe_466_g105_primitive_relation_suppression.py`).  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G106PrimitiveRelationFreenessSkeleton

open Finset
open ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer
open ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The named hypotheses -/

/-- A two-element multiset of the form `{y, -y}`. -/
def IsAntipodalPair (t : Multiset G) : Prop := ∃ y : G, t = {y, -y}

/-- **AntipodalOnlyRelations** (the char-p Lam–Leung transfer surrogate): every vanishing sum
over `S` of length at most `L` is empty or contains an antipodal sub-pair.  For multiplicative
subgroups `μ_n ⊂ F_p^×` with `n` a 2-power this matches the ℂ-side Lam–Leung/Conway–Jones
classification; the char-p instance at production shape is a NAMED OPEN hypothesis, not proved
here. -/
def AntipodalOnlyRelations (S : Finset G) (L : ℕ) : Prop :=
  ∀ t : Multiset G, (∀ x ∈ t, x ∈ S) → t.card ≤ L → t.sum = 0 →
    t = 0 ∨ ∃ y : G, ({y, -y} : Multiset G) ≤ t

/-- **PrimitiveRelationFreeness** (sub-multiset form): every vanishing sum over `S` of length
in `[3, L]` has a proper nonempty vanishing sub-multiset.  Implied by
`AntipodalOnlyRelations` (`prf_of_aor`). -/
def PrimitiveRelationFreeness (S : Finset G) (L : ℕ) : Prop :=
  ∀ t : Multiset G, (∀ x ∈ t, x ∈ S) → 3 ≤ t.card → t.card ≤ L → t.sum = 0 →
    ∃ u : Multiset G, u ≤ t ∧ u ≠ 0 ∧ u ≠ t ∧ u.sum = 0

/-- `AntipodalOnlyRelations` restated through `IsAntipodalPair`. -/
theorem aor_iff_antipodalPair_le (S : Finset G) (L : ℕ) :
    AntipodalOnlyRelations S L ↔
      ∀ t : Multiset G, (∀ x ∈ t, x ∈ S) → t.card ≤ L → t.sum = 0 →
        t = 0 ∨ ∃ v : Multiset G, IsAntipodalPair v ∧ v ≤ t := by
  constructor
  · intro h t hmem hL hsum
    rcases h t hmem hL hsum with h0 | ⟨y, hy⟩
    · exact Or.inl h0
    · exact Or.inr ⟨{y, -y}, ⟨y, rfl⟩, hy⟩
  · intro h t hmem hL hsum
    rcases h t hmem hL hsum with h0 | ⟨v, hAP, hv⟩
    · exact Or.inl h0
    · obtain ⟨y, hy⟩ := (hAP : ∃ y : G, v = {y, -y})
      exact Or.inr ⟨y, hy ▸ hv⟩

/-- Monotonicity of the hypothesis in the length budget. -/
theorem aor_mono (S : Finset G) {L L' : ℕ} (hLL : L ≤ L')
    (h : AntipodalOnlyRelations S L') : AntipodalOnlyRelations S L :=
  fun t hmem hcard hsum => h t hmem (hcard.trans hLL) hsum

/-- AOR already forbids `0 ∈ S`: `{0}` would be a vanishing 1-sum with no room for a pair. -/
theorem zero_notMem_of_aor (S : Finset G) (hAOR : AntipodalOnlyRelations S 1) :
    (0 : G) ∉ S := by
  intro h0
  have hmem : ∀ x ∈ ({0} : Multiset G), x ∈ S := by
    intro x hx
    rw [Multiset.mem_singleton] at hx
    rw [hx]
    exact h0
  have hcard : Multiset.card ({0} : Multiset G) ≤ 1 := by simp
  have hsum : Multiset.sum ({0} : Multiset G) = 0 := by simp
  rcases hAOR {0} hmem hcard hsum with h | ⟨y, hy⟩
  · have hc := congrArg Multiset.card h
    simp at hc
  · have hc := Multiset.card_le_card hy
    simp [Multiset.insert_eq_cons] at hc

/-- The antipodal-only hypothesis implies primitive-relation-freeness: the antipodal pair is
the proper nonempty vanishing sub-multiset. -/
theorem prf_of_aor (S : Finset G) (L : ℕ) (h : AntipodalOnlyRelations S L) :
    PrimitiveRelationFreeness S L := by
  intro t hmem h3 hL hsum
  rcases h t hmem hL hsum with h0 | ⟨y, hle⟩
  · rw [h0] at h3
    simp at h3
  · refine ⟨{y, -y}, hle, ?_, ?_, ?_⟩
    · intro heq
      have hc := congrArg Multiset.card heq
      simp [Multiset.insert_eq_cons] at hc
    · intro heq
      rw [← heq] at h3
      simp [Multiset.insert_eq_cons] at h3
    · simp [Multiset.insert_eq_cons]

/-! ## Value multisets and negation -/

/-- The value multiset of a 4-tuple (G104 shape). -/
def quadMS (t : (G × G) × (G × G)) : Multiset G := {t.1.1, t.1.2, t.2.1, t.2.2}

/-- The value multiset of a 3-tuple (G103 shape). -/
def tripMS (t : G × G × G) : Multiset G := {t.1, t.2.1, t.2.2}

theorem quadMS_mk (a b c d : G) : quadMS ((a, b), (c, d)) = {a, b, c, d} := rfl

theorem tripMS_mk (a b c : G) : tripMS (a, b, c) = {a, b, c} := rfl

/-- Elementwise negation of a multiset. -/
def negMS (m : Multiset G) : Multiset G := m.map Neg.neg

theorem negMS_sum (m : Multiset G) : (negMS m).sum = -m.sum :=
  Multiset.sum_map_neg' m

theorem negMS_card (m : Multiset G) : Multiset.card (negMS m) = Multiset.card m :=
  Multiset.card_map _ _

theorem negMS_count (m : Multiset G) (y : G) :
    Multiset.count y (negMS m) = Multiset.count (-y) m := by
  have h := Multiset.count_map_eq_count' (Neg.neg : G → G) m neg_injective (-y)
  simpa [negMS] using h

theorem mem_negMS {m : Multiset G} {y : G} : y ∈ negMS m ↔ -y ∈ m := by
  rw [← Multiset.count_pos, ← Multiset.count_pos, negMS_count]

/-! ## Small multiset computations -/

private theorem card_four (a1 a2 a3 a4 : G) :
    Multiset.card ({a1, a2, a3, a4} : Multiset G) = 4 := by
  simp [Multiset.insert_eq_cons]

private theorem card_three (a1 a2 a3 : G) :
    Multiset.card ({a1, a2, a3} : Multiset G) = 3 := by
  simp [Multiset.insert_eq_cons]

private theorem sum_four (a1 a2 a3 a4 : G) :
    Multiset.sum ({a1, a2, a3, a4} : Multiset G) = a1 + a2 + a3 + a4 := by
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  abel

private theorem sum_three (a1 a2 a3 : G) :
    Multiset.sum ({a1, a2, a3} : Multiset G) = a1 + a2 + a3 := by
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  abel

private theorem mem_four {a1 a2 a3 a4 y : G}
    (h : y ∈ ({a1, a2, a3, a4} : Multiset G)) :
    y = a1 ∨ y = a2 ∨ y = a3 ∨ y = a4 := by
  simpa [Multiset.insert_eq_cons] using h

private theorem mem_three {a1 a2 a3 y : G}
    (h : y ∈ ({a1, a2, a3} : Multiset G)) :
    y = a1 ∨ y = a2 ∨ y = a3 := by
  simpa [Multiset.insert_eq_cons] using h

private theorem two_of_count {a1 a2 a3 a4 y : G}
    (h : 2 ≤ Multiset.count y ({a1, a2, a3, a4} : Multiset G)) :
    (y = a1 ∧ y = a2) ∨ (y = a1 ∧ y = a3) ∨ (y = a1 ∧ y = a4) ∨
      (y = a2 ∧ y = a3) ∨ (y = a2 ∧ y = a4) ∨ (y = a3 ∧ y = a4) := by
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at h
  split_ifs at h <;> first | omega | tauto

private theorem two_of_count₃ {a1 a2 a3 y : G}
    (h : 2 ≤ Multiset.count y ({a1, a2, a3} : Multiset G)) :
    (y = a1 ∧ y = a2) ∨ (y = a1 ∧ y = a3) ∨ (y = a2 ∧ y = a3) := by
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at h
  split_ifs at h <;> first | omega | tauto

/-! ## From placed pairs to `HasAntipodal` / `IsDeg` -/

private theorem hasAntipodal_of_two_pos {a1 a2 a3 a4 y z : G} (h0 : y + z = 0)
    (h : (y = a1 ∧ z = a2) ∨ (y = a1 ∧ z = a3) ∨ (y = a1 ∧ z = a4) ∨
      (y = a2 ∧ z = a3) ∨ (y = a2 ∧ z = a4) ∨ (y = a3 ∧ z = a4)) :
    HasAntipodal ((a1, a2), (a3, a4)) := by
  show a1 + a2 = 0 ∨ a1 + a3 = 0 ∨ a1 + a4 = 0 ∨ a2 + a3 = 0 ∨ a2 + a4 = 0 ∨ a3 + a4 = 0
  rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [← e1, ← e2] <;> tauto

private theorem isDeg_of_two_pos {a1 a2 a3 y z : G} (h0 : y + z = 0)
    (h : (y = a1 ∧ z = a2) ∨ (y = a1 ∧ z = a3) ∨ (y = a2 ∧ z = a3)) :
    IsDeg (a1, a2, a3) := by
  show a1 + a2 = 0 ∨ a1 + a3 = 0 ∨ a2 + a3 = 0
  rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [← e1, ← e2] <;> tauto

private theorem hasAntipodal_of_mem_mem {a1 a2 a3 a4 y : G} (hy : y ≠ -y)
    (h1 : y = a1 ∨ y = a2 ∨ y = a3 ∨ y = a4)
    (h2 : -y = a1 ∨ -y = a2 ∨ -y = a3 ∨ -y = a4) :
    HasAntipodal ((a1, a2), (a3, a4)) := by
  have h0 : y + -y = 0 := add_neg_cancel y
  have h0' : -y + y = 0 := neg_add_cancel y
  show a1 + a2 = 0 ∨ a1 + a3 = 0 ∨ a1 + a4 = 0 ∨ a2 + a3 = 0 ∨ a2 + a4 = 0 ∨ a3 + a4 = 0
  rcases h1 with e1 | e1 | e1 | e1 <;> rcases h2 with e2 | e2 | e2 | e2
  · exact absurd (e1.trans e2.symm) hy
  · exact Or.inl (by rw [← e1, ← e2]; exact h0)
  · exact Or.inr (Or.inl (by rw [← e1, ← e2]; exact h0))
  · exact Or.inr (Or.inr (Or.inl (by rw [← e1, ← e2]; exact h0)))
  · exact Or.inl (by rw [← e2, ← e1]; exact h0')
  · exact absurd (e1.trans e2.symm) hy
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← e1, ← e2]; exact h0))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← e1, ← e2]; exact h0)))))
  · exact Or.inr (Or.inl (by rw [← e2, ← e1]; exact h0'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← e2, ← e1]; exact h0'))))
  · exact absurd (e1.trans e2.symm) hy
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← e1, ← e2]; exact h0)))))
  · exact Or.inr (Or.inr (Or.inl (by rw [← e2, ← e1]; exact h0')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← e2, ← e1]; exact h0')))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← e2, ← e1]; exact h0')))))
  · exact absurd (e1.trans e2.symm) hy

private theorem isDeg_of_mem_mem {a1 a2 a3 y : G} (hy : y ≠ -y)
    (h1 : y = a1 ∨ y = a2 ∨ y = a3)
    (h2 : -y = a1 ∨ -y = a2 ∨ -y = a3) :
    IsDeg (a1, a2, a3) := by
  have h0 : y + -y = 0 := add_neg_cancel y
  have h0' : -y + y = 0 := neg_add_cancel y
  show a1 + a2 = 0 ∨ a1 + a3 = 0 ∨ a2 + a3 = 0
  rcases h1 with e1 | e1 | e1 <;> rcases h2 with e2 | e2 | e2
  · exact absurd (e1.trans e2.symm) hy
  · exact Or.inl (by rw [← e1, ← e2]; exact h0)
  · exact Or.inr (Or.inl (by rw [← e1, ← e2]; exact h0))
  · exact Or.inl (by rw [← e2, ← e1]; exact h0')
  · exact absurd (e1.trans e2.symm) hy
  · exact Or.inr (Or.inr (by rw [← e1, ← e2]; exact h0))
  · exact Or.inr (Or.inl (by rw [← e2, ← e1]; exact h0'))
  · exact Or.inr (Or.inr (by rw [← e2, ← e1]; exact h0'))
  · exact absurd (e1.trans e2.symm) hy

/-! ## The depth-6 lane: no disjoint antipodal-free equal-sum 4-tuple pairs -/

/-- **AOR at length 8 kills every disjoint antipodal-free equal-sum 4-tuple pair.**  Only
antipodal-freeness (not full G104 primitivity) is needed: the welded length-8 vanishing
multiset receives an antipodal pair from AOR, and every placement is contradicted. -/
theorem no_disjoint_primitive_equalSum_quad_pairs
    (S : Finset G) (hsym : ∀ x ∈ S, -x ∈ S)
    (hAOR : AntipodalOnlyRelations S 8)
    (t u : (G × G) × (G × G))
    (ht : t ∈ (S ×ˢ S) ×ˢ (S ×ˢ S)) (hu : u ∈ (S ×ˢ S) ×ˢ (S ×ˢ S))
    (htA : ¬HasAntipodal t) (huA : ¬HasAntipodal u)
    (hsum : qsum t = qsum u)
    (hdisj : ∀ y ∈ quadMS t, y ∉ quadMS u) : False := by
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := t
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := u
  have hmt := Finset.mem_product.mp ht
  have hmt1 := Finset.mem_product.mp hmt.1
  have hmt2 := Finset.mem_product.mp hmt.2
  have ha1 : a1 ∈ S := hmt1.1
  have ha2 : a2 ∈ S := hmt1.2
  have ha3 : a3 ∈ S := hmt2.1
  have ha4 : a4 ∈ S := hmt2.2
  have hmu := Finset.mem_product.mp hu
  have hmu1 := Finset.mem_product.mp hmu.1
  have hmu2 := Finset.mem_product.mp hmu.2
  have hb1 : b1 ∈ S := hmu1.1
  have hb2 : b2 ∈ S := hmu1.2
  have hb3 : b3 ∈ S := hmu2.1
  have hb4 : b4 ∈ S := hmu2.2
  have hsum' : a1 + a2 + a3 + a4 = b1 + b2 + b3 + b4 := hsum
  simp only [quadMS_mk] at hdisj
  -- the welded length-8 vanishing multiset
  have hmemw : ∀ x ∈ ({a1, a2, a3, a4} : Multiset G) + negMS {b1, b2, b3, b4}, x ∈ S := by
    intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · rcases mem_four hx with rfl | rfl | rfl | rfl <;> assumption
    · have hx' : -x ∈ ({b1, b2, b3, b4} : Multiset G) := mem_negMS.mp hx
      have hxx : x = - -x := (neg_neg x).symm
      rcases mem_four hx' with h | h | h | h <;> rw [hxx, h] <;>
        exact hsym _ (by assumption)
  have hcardw :
      Multiset.card (({a1, a2, a3, a4} : Multiset G) + negMS {b1, b2, b3, b4}) = 8 := by
    rw [Multiset.card_add, negMS_card, card_four, card_four]
  have hsumw :
      Multiset.sum (({a1, a2, a3, a4} : Multiset G) + negMS {b1, b2, b3, b4}) = 0 := by
    rw [Multiset.sum_add, negMS_sum, sum_four, sum_four, hsum', add_neg_cancel]
  rcases hAOR _ hmemw (le_of_eq hcardw) hsumw with h0 | ⟨y, hle⟩
  · rw [h0] at hcardw
    simp at hcardw
  by_cases hy : y = -y
  · -- order-2 case: the pair contributes count 2 of `y`
    have hcw : 2 ≤
        Multiset.count y (({a1, a2, a3, a4} : Multiset G) + negMS {b1, b2, b3, b4}) := by
      have h1 : Multiset.count y ({y, -y} : Multiset G) = 2 := by
        rw [Multiset.insert_eq_cons, Multiset.count_cons_self, Multiset.count_singleton,
          if_pos hy]
      exact h1 ▸ Multiset.count_le_of_le y hle
    rw [Multiset.count_add, negMS_count] at hcw
    have h2y : y + y = 0 := add_eq_zero_iff_eq_neg.mpr hy
    rcases Nat.lt_or_ge (Multiset.count y ({a1, a2, a3, a4} : Multiset G)) 2 with hcA | hcA
    · rcases Nat.lt_or_ge (Multiset.count (-y) ({b1, b2, b3, b4} : Multiset G)) 2 with
        hcB | hcB
      · -- one copy on each side: a shared value
        have hmA : y ∈ ({a1, a2, a3, a4} : Multiset G) :=
          Multiset.count_pos.mp (by omega)
        have hmB : -y ∈ ({b1, b2, b3, b4} : Multiset G) :=
          Multiset.count_pos.mp (by omega)
        have hmB' : y ∈ ({b1, b2, b3, b4} : Multiset G) := by
          rw [hy]
          exact hmB
        exact hdisj y hmA hmB'
      · -- two copies of `-y` among `u`'s values: antipodal pair in `u`
        have h2y' : (-y) + (-y) = 0 := by
          rw [← hy]
          exact h2y
        exact huA (hasAntipodal_of_two_pos h2y' (two_of_count hcB))
    · -- two copies of `y` among `t`'s values: antipodal pair in `t`
      exact htA (hasAntipodal_of_two_pos h2y (two_of_count hcA))
  · -- generic case: `y` and `-y` are distinct members of the weld
    have hyw : y ∈ ({a1, a2, a3, a4} : Multiset G) + negMS {b1, b2, b3, b4} :=
      Multiset.mem_of_le hle (by simp [Multiset.insert_eq_cons])
    have hnyw : -y ∈ ({a1, a2, a3, a4} : Multiset G) + negMS {b1, b2, b3, b4} :=
      Multiset.mem_of_le hle (by simp [Multiset.insert_eq_cons])
    rcases Multiset.mem_add.mp hyw with hyA | hyB
    · rcases Multiset.mem_add.mp hnyw with hnyA | hnyB
      · exact htA (hasAntipodal_of_mem_mem hy (mem_four hyA) (mem_four hnyA))
      · -- `y` from `t`, `-y` from the negated `u`: `y` is a shared value
        have hsh : -(-y) ∈ ({b1, b2, b3, b4} : Multiset G) := mem_negMS.mp hnyB
        rw [neg_neg] at hsh
        exact hdisj y hyA hsh
    · rcases Multiset.mem_add.mp hnyw with hnyA | hnyB
      · -- `-y` from `t`, `y` from the negated `u`: `-y` is a shared value
        have hsh : -y ∈ ({b1, b2, b3, b4} : Multiset G) := mem_negMS.mp hyB
        exact hdisj (-y) hnyA hsh
      · -- both from the negated `u`: antipodal pair in `u`
        have h1 : -y ∈ ({b1, b2, b3, b4} : Multiset G) := mem_negMS.mp hyB
        have h2 : -(-y) ∈ ({b1, b2, b3, b4} : Multiset G) := mem_negMS.mp hnyB
        exact huA (hasAntipodal_of_mem_mem (fun h => hy (neg_injective h))
          (mem_four h1) (mem_four h2))

/-! ## The depth-5 lane: no disjoint centered equal-sum triple pairs -/

/-- **AOR at length 6 kills every disjoint centered equal-sum triple pair** (G103's centered
triples are exactly the `¬IsDeg` ones). -/
theorem no_disjoint_centered_equalSum_triple_pairs
    (S : Finset G) (hsym : ∀ x ∈ S, -x ∈ S)
    (hAOR : AntipodalOnlyRelations S 6)
    (t u : G × G × G)
    (ht : t ∈ S ×ˢ S ×ˢ S) (hu : u ∈ S ×ˢ S ×ˢ S)
    (htC : ¬IsDeg t) (huC : ¬IsDeg u)
    (hsum : t.1 + t.2.1 + t.2.2 = u.1 + u.2.1 + u.2.2)
    (hdisj : ∀ y ∈ tripMS t, y ∉ tripMS u) : False := by
  obtain ⟨a1, a2, a3⟩ := t
  obtain ⟨b1, b2, b3⟩ := u
  have hmt := Finset.mem_product.mp ht
  have hmt2 := Finset.mem_product.mp hmt.2
  have ha1 : a1 ∈ S := hmt.1
  have ha2 : a2 ∈ S := hmt2.1
  have ha3 : a3 ∈ S := hmt2.2
  have hmu := Finset.mem_product.mp hu
  have hmu2 := Finset.mem_product.mp hmu.2
  have hb1 : b1 ∈ S := hmu.1
  have hb2 : b2 ∈ S := hmu2.1
  have hb3 : b3 ∈ S := hmu2.2
  have hsum' : a1 + a2 + a3 = b1 + b2 + b3 := hsum
  simp only [tripMS_mk] at hdisj
  have hmemw : ∀ x ∈ ({a1, a2, a3} : Multiset G) + negMS {b1, b2, b3}, x ∈ S := by
    intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · rcases mem_three hx with rfl | rfl | rfl <;> assumption
    · have hx' : -x ∈ ({b1, b2, b3} : Multiset G) := mem_negMS.mp hx
      have hxx : x = - -x := (neg_neg x).symm
      rcases mem_three hx' with h | h | h <;> rw [hxx, h] <;>
        exact hsym _ (by assumption)
  have hcardw : Multiset.card (({a1, a2, a3} : Multiset G) + negMS {b1, b2, b3}) = 6 := by
    rw [Multiset.card_add, negMS_card, card_three, card_three]
  have hsumw : Multiset.sum (({a1, a2, a3} : Multiset G) + negMS {b1, b2, b3}) = 0 := by
    rw [Multiset.sum_add, negMS_sum, sum_three, sum_three, hsum', add_neg_cancel]
  rcases hAOR _ hmemw (le_of_eq hcardw) hsumw with h0 | ⟨y, hle⟩
  · rw [h0] at hcardw
    simp at hcardw
  by_cases hy : y = -y
  · have hcw : 2 ≤ Multiset.count y (({a1, a2, a3} : Multiset G) + negMS {b1, b2, b3}) := by
      have h1 : Multiset.count y ({y, -y} : Multiset G) = 2 := by
        rw [Multiset.insert_eq_cons, Multiset.count_cons_self, Multiset.count_singleton,
          if_pos hy]
      exact h1 ▸ Multiset.count_le_of_le y hle
    rw [Multiset.count_add, negMS_count] at hcw
    have h2y : y + y = 0 := add_eq_zero_iff_eq_neg.mpr hy
    rcases Nat.lt_or_ge (Multiset.count y ({a1, a2, a3} : Multiset G)) 2 with hcA | hcA
    · rcases Nat.lt_or_ge (Multiset.count (-y) ({b1, b2, b3} : Multiset G)) 2 with hcB | hcB
      · have hmA : y ∈ ({a1, a2, a3} : Multiset G) := Multiset.count_pos.mp (by omega)
        have hmB : -y ∈ ({b1, b2, b3} : Multiset G) := Multiset.count_pos.mp (by omega)
        have hmB' : y ∈ ({b1, b2, b3} : Multiset G) := by
          rw [hy]
          exact hmB
        exact hdisj y hmA hmB'
      · have h2y' : (-y) + (-y) = 0 := by
          rw [← hy]
          exact h2y
        exact huC (isDeg_of_two_pos h2y' (two_of_count₃ hcB))
    · exact htC (isDeg_of_two_pos h2y (two_of_count₃ hcA))
  · have hyw : y ∈ ({a1, a2, a3} : Multiset G) + negMS {b1, b2, b3} :=
      Multiset.mem_of_le hle (by simp [Multiset.insert_eq_cons])
    have hnyw : -y ∈ ({a1, a2, a3} : Multiset G) + negMS {b1, b2, b3} :=
      Multiset.mem_of_le hle (by simp [Multiset.insert_eq_cons])
    rcases Multiset.mem_add.mp hyw with hyA | hyB
    · rcases Multiset.mem_add.mp hnyw with hnyA | hnyB
      · exact htC (isDeg_of_mem_mem hy (mem_three hyA) (mem_three hnyA))
      · have hsh : -(-y) ∈ ({b1, b2, b3} : Multiset G) := mem_negMS.mp hnyB
        rw [neg_neg] at hsh
        exact hdisj y hyA hsh
    · rcases Multiset.mem_add.mp hnyw with hnyA | hnyB
      · have hsh : -y ∈ ({b1, b2, b3} : Multiset G) := mem_negMS.mp hyB
        exact hdisj (-y) hnyA hsh
      · have h1 : -y ∈ ({b1, b2, b3} : Multiset G) := mem_negMS.mp hyB
        have h2 : -(-y) ∈ ({b1, b2, b3} : Multiset G) := mem_negMS.mp hnyB
        exact huC (isDeg_of_mem_mem (fun h => hy (neg_injective h))
          (mem_three h1) (mem_three h2))

/-! ## The disjoint-refined equal-sum masses vanish -/

/-- Value-multiset disjointness of two 4-tuples. -/
def ValueDisjoint (t u : (G × G) × (G × G)) : Prop := ∀ y ∈ quadMS t, y ∉ quadMS u

instance moduleInstance_G106PrimitiveRelationFreenessSkeleton_1 : ∀ t u : (G × G) × (G × G), Decidable (ValueDisjoint t u) := fun t u => by
  unfold ValueDisjoint
  infer_instance

/-- Value-multiset disjointness of two 3-tuples. -/
def TripValueDisjoint (t u : G × G × G) : Prop := ∀ y ∈ tripMS t, y ∉ tripMS u

instance moduleInstance_G106PrimitiveRelationFreenessSkeleton_2 : ∀ t u : G × G × G, Decidable (TripValueDisjoint t u) := fun t u => by
  unfold TripValueDisjoint
  infer_instance

/-- Ordered pairs of G104-primitive 4-tuples from `S` with equal sums and disjoint values —
the disjoint-refined depth-6 collision objects. -/
def disjointPrimQuadPairCount (S : Finset G) : ℕ :=
  ((((S ×ˢ S) ×ˢ (S ×ˢ S)) ×ˢ ((S ×ˢ S) ×ˢ (S ×ˢ S))).filter fun p =>
    (¬HasAntipodal p.1 ∧ ¬HasZeroTriple p.1) ∧ (¬HasAntipodal p.2 ∧ ¬HasZeroTriple p.2) ∧
      qsum p.1 = qsum p.2 ∧ ValueDisjoint p.1 p.2).card

/-- Ordered pairs of G103-centered 3-tuples from `S` with equal sums and disjoint values —
the disjoint-refined depth-5 collision objects. -/
def disjointCentTriplePairCount (S : Finset G) : ℕ :=
  (((S ×ˢ S ×ˢ S) ×ˢ (S ×ˢ S ×ˢ S)).filter fun p =>
    ¬IsDeg p.1 ∧ ¬IsDeg p.2 ∧
      p.1.1 + p.1.2.1 + p.1.2.2 = p.2.1 + p.2.2.1 + p.2.2.2 ∧
      TripValueDisjoint p.1 p.2).card

/-- **Headline (depth 6): the disjoint primitive equal-sum mass is identically zero under
`AntipodalOnlyRelations S 8`.** -/
theorem disjointPrimQuadPairCount_eq_zero (S : Finset G)
    (hsym : ∀ x ∈ S, -x ∈ S) (hAOR : AntipodalOnlyRelations S 8) :
    disjointPrimQuadPairCount S = 0 := by
  unfold disjointPrimQuadPairCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  intro hcond
  have hm := Finset.mem_product.mp hp
  exact no_disjoint_primitive_equalSum_quad_pairs S hsym hAOR p.1 p.2 hm.1 hm.2
    hcond.1.1 hcond.2.1.1 hcond.2.2.1 hcond.2.2.2

/-- **Headline (depth 5): the disjoint centered equal-sum mass is identically zero under
`AntipodalOnlyRelations S 6`.** -/
theorem disjointCentTriplePairCount_eq_zero (S : Finset G)
    (hsym : ∀ x ∈ S, -x ∈ S) (hAOR : AntipodalOnlyRelations S 6) :
    disjointCentTriplePairCount S = 0 := by
  unfold disjointCentTriplePairCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  intro hcond
  have hm := Finset.mem_product.mp hp
  exact no_disjoint_centered_equalSum_triple_pairs S hsym hAOR p.1 p.2 hm.1 hm.2
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2

/-! ## Axiom audit -/
#print axioms aor_iff_antipodalPair_le
#print axioms aor_mono
#print axioms zero_notMem_of_aor
#print axioms prf_of_aor
#print axioms negMS_sum
#print axioms negMS_count
#print axioms mem_negMS
#print axioms no_disjoint_primitive_equalSum_quad_pairs
#print axioms no_disjoint_centered_equalSum_triple_pairs
#print axioms disjointPrimQuadPairCount_eq_zero
#print axioms disjointCentTriplePairCount_eq_zero

end ArkLib.ProximityGap.Frontier.G106PrimitiveRelationFreenessSkeleton
