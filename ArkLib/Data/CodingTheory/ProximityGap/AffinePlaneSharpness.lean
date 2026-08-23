/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The affine-plane sharpness witness: the pole at `t² = s·n` is real (#389)

The deep-band mean-degree law (`mean_degree_law_deep`) and its Cauchy–Schwarz
sharpening bound the total mass `Σ_{A ∈ S} |A|` of a pairwise-`≤ 1`-intersecting
family of `≥ t`-sets by `2n`, for `t` above the Johnson line.  This file proves the
matching LOWER bound construction showing the route stops there **sharply**:

> **`lineFamily`** — over a finite field `F` with `q` elements, the `q²` graphs of the
> affine maps `x ↦ a·x + b` inside the ground set `F × F` form a pairwise-`≤ 1`-
> intersecting family of `q`-sets — `t = q`, `n = q²`, i.e. **exactly at the pole
> `t² = s·n` (`s = 1`)** — of total mass `q³ = t·n`.

> **`no_mean_degree_law_at_pole`** — consequently, for EVERY constant `C` there is an
> instance with `n ≤ t²` where the mass exceeds `C·n`: no constant-`C` mean-degree law
> holds at the pole.  The deep hypothesis `2n² ≤ t²(t−1)` (equivalently the CS-range
> `t² ≥ 2n`) cannot be weakened to `t² ≥ n`, and no pairwise-intersection set-system
> argument alone crosses the Johnson line — sub-Johnson supply bounds MUST couple the
> word.

Probe: `scripts/probes/probe_affine_sharpness_triple_moment.py` (section A, exact at
`q = 3, 5, 7, 11, 13`).  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The graph of the affine map `x ↦ a·x + b`, as a finset of the plane `F × F`. -/
def lineGraph (a b : F) : Finset (F × F) :=
  (univ : Finset F).image fun x => (x, a * x + b)

lemma mem_lineGraph {a b x y : F} :
    (x, y) ∈ lineGraph a b ↔ y = a * x + b := by
  simp only [lineGraph, mem_image, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨x', rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨x, rfl, rfl⟩

lemma card_lineGraph (a b : F) : (lineGraph a b).card = Fintype.card F := by
  have hinj : Function.Injective (fun x : F => (x, a * x + b)) := by
    intro u v huv
    exact ((Prod.mk.injEq _ _ _ _).mp huv).1
  rw [lineGraph, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- Two distinct affine graphs meet in at most one point of the plane. -/
lemma lineGraph_inter_card_le {a b a' b' : F} (h : (a, b) ≠ (a', b')) :
    (lineGraph a b ∩ lineGraph a' b').card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq
  rw [Finset.mem_inter] at hp hq
  have h1 : y = a * x + b := mem_lineGraph.mp hp.1
  have h2 : y = a' * x + b' := mem_lineGraph.mp hp.2
  have h3 : y' = a * x' + b := mem_lineGraph.mp hq.1
  have h4 : y' = a' * x' + b' := mem_lineGraph.mp hq.2
  by_cases haa : a = a'
  · exfalso
    subst haa
    have hb : b = b' := by linear_combination h2 - h1
    exact h (by rw [hb])
  · have hx : x = x' := by
      have h5 : (a - a') * (x - x') = 0 := by linear_combination -h1 + h2 + h3 - h4
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd (sub_eq_zero.mp h6) haa
      · exact sub_eq_zero.mp h6
    subst hx
    have hy : y = y' := by rw [h1, h3]
    rw [hy]

/-- Distinct coefficient pairs give distinct graphs. -/
lemma lineGraph_injective :
    Function.Injective (fun ab : F × F => lineGraph ab.1 ab.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only at h
  have key : ∀ x : F, a * x + b = a' * x + b' := by
    intro x
    have hm : (x, a * x + b) ∈ lineGraph a b := mem_lineGraph.mpr rfl
    rw [h] at hm
    exact mem_lineGraph.mp hm
  have hb : b = b' := by simpa using key 0
  have ha : a = a' := by
    have h1 := key 1
    rw [hb] at h1
    have h2 : a * 1 = a' * 1 := by linear_combination h1
    simpa using h2
  rw [ha, hb]

/-- **The witness family**: all `q²` affine graphs in the plane `F × F`. -/
def lineFamily (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Finset (F × F)) :=
  (univ : Finset (F × F)).image fun ab => lineGraph ab.1 ab.2

lemma lineFamily_card : (lineFamily F).card = Fintype.card F ^ 2 := by
  rw [lineFamily, Finset.card_image_of_injective _ lineGraph_injective,
    Finset.card_univ, Fintype.card_prod, sq]

/-- Every member is a `t`-set with `t = q`. -/
lemma card_of_mem_lineFamily {A : Finset (F × F)} (hA : A ∈ lineFamily F) :
    A.card = Fintype.card F := by
  obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hA
  exact card_lineGraph a b

/-- The family is pairwise `≤ 1`-intersecting. -/
lemma lineFamily_pairwise {A B : Finset (F × F)} (hA : A ∈ lineFamily F)
    (hB : B ∈ lineFamily F) (hAB : A ≠ B) : (A ∩ B).card ≤ 1 := by
  obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨⟨a', b'⟩, -, rfl⟩ := Finset.mem_image.mp hB
  refine lineGraph_inter_card_le ?_
  intro hcoef
  cases hcoef
  exact hAB rfl

/-- **The mass**: total size `q³ = t·n` — at the pole `t² = n`. -/
lemma lineFamily_mass : ∑ A ∈ lineFamily F, A.card = Fintype.card F ^ 3 := by
  rw [lineFamily, Finset.sum_image (fun x _ y _ h => lineGraph_injective h)]
  simp only [card_lineGraph]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring

/-- At the pole, the mass beats `C·n` for every `C < q`. -/
theorem lineFamily_mass_gt (C : ℕ) (hC : C < Fintype.card F) :
    C * Fintype.card (F × F) < ∑ A ∈ lineFamily F, A.card := by
  rw [lineFamily_mass, Fintype.card_prod]
  have h2 : (0 : ℕ) < Fintype.card F * Fintype.card F := by positivity
  calc C * (Fintype.card F * Fintype.card F)
      < Fintype.card F * (Fintype.card F * Fintype.card F) :=
        mul_lt_mul_of_pos_right hC h2
    _ = Fintype.card F ^ 3 := by ring

/-- **The pole witness, `Fin n` form**: for every constant `C` there is an instance
exactly at the pole `t² = n` — a pairwise-`≤ 1`-intersecting family of `≥ t`-sets of
total mass `> C·n`. -/
theorem mean_degree_pole_witness (C : ℕ) :
    ∃ (n t : ℕ) (S : Finset (Finset (Fin n))), 2 ≤ t ∧ t * t = n ∧
      (∀ A ∈ S, t ≤ A.card) ∧
      (∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1) ∧
      C * n < ∑ A ∈ S, A.card := by
  classical
  obtain ⟨p, hpC, hp⟩ := Nat.exists_infinite_primes (max (C + 1) 3)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hC1 : C + 1 ≤ p := le_trans (le_max_left _ _) hpC
  have h3 : 3 ≤ p := le_trans (le_max_right _ _) hpC
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  set e := Fintype.equivFin (ZMod p × ZMod p) with he
  refine ⟨Fintype.card (ZMod p × ZMod p), Fintype.card (ZMod p),
    (lineFamily (ZMod p)).image (fun A => A.map e.toEmbedding),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; omega
  · exact (Fintype.card_prod _ _).symm
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hA'
    rw [Finset.card_map]
    exact le_of_eq (card_of_mem_lineFamily hA).symm
  · intro A' hA' B' hB' hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hA'
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
    have hABne : A ≠ B := fun hEq => hne (by rw [hEq])
    rw [← Finset.map_inter, Finset.card_map]
    exact lineFamily_pairwise hA hB hABne
  · have hsum : ∑ A' ∈ (lineFamily (ZMod p)).image (fun A => A.map e.toEmbedding),
        A'.card = ∑ A ∈ lineFamily (ZMod p), A.card := by
      rw [Finset.sum_image
        (fun x _ y _ h => Finset.map_injective e.toEmbedding h)]
      simp only [Finset.card_map]
    rw [hsum]
    exact lineFamily_mass_gt C (by rw [hcard]; omega)

/-- **THE POLE IS REAL**: no constant-`C` mean-degree law holds at `t² = n` — the
mean-degree hypothesis `2n² ≤ t²(t−1)` (and the CS range `2n ≤ t²`) cannot be
weakened to `n ≤ t²`.  Any sub-Johnson supply bound must use more than sizes and
pairwise intersections: it must couple the word. -/
theorem no_mean_degree_law_at_pole (C : ℕ) :
    ¬ (∀ (n t : ℕ) (S : Finset (Finset (Fin n))), 2 ≤ t →
        (∀ A ∈ S, t ≤ A.card) →
        (∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1) →
        n ≤ t * t →
        ∑ A ∈ S, A.card ≤ C * n) := by
  intro hlaw
  obtain ⟨n, t, S, ht, hpole, hsize, hpair, hmass⟩ := mean_degree_pole_witness C
  exact (not_le.mpr hmass) (hlaw n t S ht hsize hpair hpole.ge)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.lineFamily_mass
#print axioms ProximityGap.PairRank.mean_degree_pole_witness
#print axioms ProximityGap.PairRank.no_mean_degree_law_at_pole
