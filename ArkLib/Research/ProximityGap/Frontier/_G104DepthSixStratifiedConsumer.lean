/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Research.ProximityGap.Frontier._G87DepthFourPairSumReduction

/-!
# G104: depth six via the stratified-L² primitive-concentration ladder

G102 closed pair statistics at depth ≥ 5; G103 closed depth 5 from the centered triple
concentration.  This file climbs to depth six and, in doing so, establishes the corrected
mechanism of the all-depth ladder: at depth ≥ 6 the naive `J_s ≤ maxN_s·n^s` chain is LOSSY
(the antipodal tower concentrates `maxN₆` at the few targets with positive pair count and
overshoots the budget by `2^5`), so the consumer must run a **stratified L² split** whose
stratum squares recurse through lower-depth equal-sum masses.

**Strata.**  A 4-tuple is *antipodal-degenerate* if two entries sum to zero, and
*zero-triple-degenerate* if three entries sum to zero; otherwise it is **primitive**.
Machine-checked bounds:

  `antipQuadCount x ≤ 6·n·pairCount x`      (six position-pair injections)
  `ztQuadCount x   ≤ 4·zeroTripleCount`     (four position-triple injections)
  `quadCount x     = prim + antip + zt`     (exact partition)

**The stratified chain.**  With `sextCount = pairCount ∗ quadCount` (the (2,4) convolution)
split as `P + A + B` along the strata:

  `Σ P² ≤ M₄ᵖ·n⁸`,   `Σ A² ≤ 36·n²·J₄`,   `Σ B² ≤ 16·Z₃²·n⁵`,
  `J₄ ≤ (M₄ᵖ + 6n² + 4Z₃)·n⁴`,
  `4·(P+A+B)² ≤ 5P² + 40A² + 40B²`   (exact: the defect is `(P−4A−4B)² + 20(A−B)²`),

so `4·J₆ ≤ 5·M₄ᵖn⁸ + 40·36n²·J₄ + 40·16Z₃²n⁵`, and the production kernel closes at
`(M₄ᵖ, Z₃) = (2^22, 2^53)`: a *pointwise* primitive-quad cap at the Stepanov level
`4·n^{2/3} = 2^22` and a *total* zero-triple count up to `2^53` (the `Z₃` term is far from
binding at `2^22`; exact recomputation shows the kernel holds up to `log₂ Z₃ ≈ 53.26`).  The two
hypotheses are of different kinds and are not "at the same level".  For a multiplicative
subgroup `S`, scaling by `S` acts freely on zero-sum triples, so `Z₃ ∈ |S|·ℕ`
(`_G105ZeroTripleQuantizationFence.lean`).  Depth six needs NO pair-concentration hypothesis
at all: the crude `pairCount ≤ n` suffices inside the recursion.

The probes measure the primitive quadruple concentration of real `μ_n` at `4!·{1,1,1,1,3,7}`
at small scale (O(1)-ish; the `2^{19}` headroom is an extrapolation to production).  The
scoping archive's proposed all-depth input — one uniform PrimitiveConcentration cap
`4·n^{2/3}` for every arity `3..108` — is **refuted** at production scale (arity 8 by an
averaging/pigeonhole argument, arity 11 by
`scripts/probes/probe_466_g104_primitive_concentration_factorial_no_go.py`), and its
`n^{0.73..0.87}` threshold band used a `C(110,s)²` envelope rather than the formal
`descFactorial(110,s)²` decoder normalization (audit T117).  It is not an input interface
for the padded-collision lane; the depth-six consumer here, with its explicit primitive-quad
hypothesis `M₄ᵖ`, is unaffected.  Probes:
`scripts/probes/_out_466_g104_ladder_scoping.txt`,
`scripts/probes/probe_466_g103_centered_triple_concentration.py`.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer

open Finset
open scoped Nat

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Counts and strata -/

/-- Ordered pairs from `S` with sum `c`. -/
def pairCount (S : Finset G) (c : G) : ℕ :=
  ((S ×ˢ S).filter fun q => q.1 + q.2 = c).card

/-- Ordered zero-sum triples from `S`. -/
def zeroTripleCount (S : Finset G) : ℕ :=
  ((S ×ˢ S ×ˢ S).filter fun t => t.1 + t.2.1 + t.2.2 = 0).card

/-- Two entries of the 4-tuple sum to zero. -/
def HasAntipodal (t : (G × G) × (G × G)) : Prop :=
  t.1.1 + t.1.2 = 0 ∨ t.1.1 + t.2.1 = 0 ∨ t.1.1 + t.2.2 = 0 ∨
    t.1.2 + t.2.1 = 0 ∨ t.1.2 + t.2.2 = 0 ∨ t.2.1 + t.2.2 = 0

instance moduleInstance_G104DepthSixStratifiedConsumer_1 : DecidablePred (HasAntipodal (G := G)) := fun t => by
  unfold HasAntipodal
  infer_instance

/-- Three entries of the 4-tuple sum to zero. -/
def HasZeroTriple (t : (G × G) × (G × G)) : Prop :=
  t.1.1 + t.1.2 + t.2.1 = 0 ∨ t.1.1 + t.1.2 + t.2.2 = 0 ∨
    t.1.1 + t.2.1 + t.2.2 = 0 ∨ t.1.2 + t.2.1 + t.2.2 = 0

instance moduleInstance_G104DepthSixStratifiedConsumer_2 : DecidablePred (HasZeroTriple (G := G)) := fun t => by
  unfold HasZeroTriple
  infer_instance

/-- The sum of a 4-tuple. -/
def qsum (t : (G × G) × (G × G)) : G := t.1.1 + t.1.2 + t.2.1 + t.2.2

/-- Ordered 4-tuples from `S` with sum `x`. -/
def quadCount (S : Finset G) (x : G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x).card

/-- Primitive 4-tuples: no antipodal pair, no zero-sum triple. -/
def primQuadCount (S : Finset G) (x : G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t =>
    qsum t = x ∧ ¬HasAntipodal t ∧ ¬HasZeroTriple t).card

/-- Antipodal-degenerate 4-tuples. -/
def antipQuadCount (S : Finset G) (x : G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x ∧ HasAntipodal t).card

/-- Zero-triple-degenerate (but not antipodal) 4-tuples. -/
def ztQuadCount (S : Finset G) (x : G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t =>
    qsum t = x ∧ ¬HasAntipodal t ∧ HasZeroTriple t).card

/-- Ordered (pair, 4-tuple) tuples with total sum `a` — depth 6 in the (2,4) shape. -/
def sextCount (S : Finset G) (a : G) : ℕ :=
  (((S ×ˢ S) ×ˢ ((S ×ˢ S) ×ˢ (S ×ˢ S))).filter
    fun q => q.1.1 + q.1.2 + qsum q.2 = a).card

/-- The depth-6 equal-sum mass `J₆`. -/
def equalSumSextMass (S : Finset G) : ℕ :=
  ∑ a : G, sextCount S a ^ 2

/-! ## Elementary identities (delegated to the G87 depth-four kernel)

`pairCount` here is definitionally G87's `pairCount`, and `quadCount` agrees with G87's
`quadCount` up to reassociation of the sum; the pair/quad kernel lemmas are taken from
`_G87DepthFourPairSumReduction.lean` rather than re-proved. -/

theorem pairCount_eq_G87 (S : Finset G) (c : G) :
    pairCount S c = ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.pairCount S c :=
  rfl

theorem quadCount_eq_G87 (S : Finset G) (x : G) :
    quadCount S x = ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.quadCount S x := by
  unfold quadCount ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.quadCount qsum
  congr 1
  exact Finset.filter_congr fun t _ => by rw [add_assoc (t.1.1 + t.1.2)]

theorem pairCount_le_card (S : Finset G) (c : G) : pairCount S c ≤ S.card :=
  ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.pairCount_le_card S c

theorem sum_pairCount (S : Finset G) : ∑ c : G, pairCount S c = S.card ^ 2 :=
  ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.sum_pairCount S

theorem sum_quadCount (S : Finset G) : ∑ x : G, quadCount S x = S.card ^ 4 := by
  simp only [quadCount_eq_G87]
  exact ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.sum_quadCount S

/-- Exact stratum partition of the 4-tuple fiber. -/
theorem quadCount_split (S : Finset G) (x : G) :
    quadCount S x = antipQuadCount S x + (ztQuadCount S x + primQuadCount S x) := by
  classical
  unfold quadCount antipQuadCount ztQuadCount primQuadCount
  have h1 : (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x).card =
      ((((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x).filter
        fun t => HasAntipodal t).card +
      ((((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x).filter
        fun t => ¬HasAntipodal t).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have h2 : ((((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x).filter
        fun t => ¬HasAntipodal t).card =
      (((((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x).filter
        fun t => ¬HasAntipodal t).filter fun t => HasZeroTriple t).card +
      (((((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x).filter
        fun t => ¬HasAntipodal t).filter fun t => ¬HasZeroTriple t).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  rw [h1, h2]
  congr 1
  · rw [Finset.filter_filter]
  congr 1
  · rw [Finset.filter_filter, Finset.filter_filter]
  · rw [Finset.filter_filter, Finset.filter_filter]

/-! ## Fixed-position filters and coordinate permutations

Both degenerate strata are covered by *fixed-position* filters `qsum t = x ∧ P t`.  Instead of
one injection per position set, we prove one base injection per stratum and transport it to
every other position set by a coordinate permutation `σ` of the 4-tuple, which preserves the
box `S⁴` and the total sum `qsum`. -/

private theorem mem4 (S : Finset G) (t : (G × G) × (G × G))
    (ht : t ∈ (S ×ˢ S) ×ˢ (S ×ˢ S)) :
    t.1.1 ∈ S ∧ t.1.2 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S := by
  have h1 := Finset.mem_product.mp ht
  have h2 := Finset.mem_product.mp h1.1
  have h3 := Finset.mem_product.mp h1.2
  exact ⟨h2.1, h2.2, h3.1, h3.2⟩

private theorem mem4_mk (S : Finset G) {a b c d : G}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    ((a, b), (c, d)) ∈ (S ×ˢ S) ×ˢ (S ×ˢ S) :=
  Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, Finset.mem_product.mpr ⟨hc, hd⟩⟩

/-- The fixed-position filter shape used by the stratum injections. -/
private def fixedFilter (S : Finset G) (x : G) (P : (G × G) × (G × G) → Prop)
    [DecidablePred P] : Finset ((G × G) × (G × G)) :=
  ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x ∧ P t

/-- A coordinate permutation `σ` (injective, box- and sum-preserving) transports the
fixed-position filter of `P ∘ σ` into that of `P`. -/
private theorem fixedFilter_comp_card_le (S : Finset G) (x : G)
    (σ : (G × G) × (G × G) → (G × G) × (G × G)) (hσ : Function.Injective σ)
    (hbox : ∀ t ∈ (S ×ˢ S) ×ˢ (S ×ˢ S), σ t ∈ (S ×ˢ S) ×ˢ (S ×ˢ S))
    (hsum : ∀ t, qsum (σ t) = qsum t)
    (P : (G × G) × (G × G) → Prop) [DecidablePred P] :
    (fixedFilter S x (fun t => P (σ t))).card ≤ (fixedFilter S x P).card := by
  classical
  refine Finset.card_le_card_of_injOn σ (fun t ht => ?_) hσ.injOn
  have ht' := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hbox t ht'.1, (hsum t).trans ht'.2.1, ht'.2.2⟩

/-- The coordinate permutations of `((a,b),(c,d))` used by the stratum transports:
`0..4` move the antipodal pair `(1,3),(1,4),(2,3),(2,4),(3,4)` to the front, and `5..7` move
the zero triple `(1,2,4),(1,3,4),(2,3,4)` to the front.  Injectivity, box and sum preservation
are discharged uniformly. -/
private def perm4 (k : Fin 8) (t : (G × G) × (G × G)) : (G × G) × (G × G) :=
  match k with
  | 0 => ((t.1.1, t.2.1), (t.1.2, t.2.2))
  | 1 => ((t.1.1, t.2.2), (t.1.2, t.2.1))
  | 2 => ((t.1.2, t.2.1), (t.1.1, t.2.2))
  | 3 => ((t.1.2, t.2.2), (t.1.1, t.2.1))
  | 4 => ((t.2.1, t.2.2), (t.1.1, t.1.2))
  | 5 => ((t.1.1, t.1.2), (t.2.2, t.2.1))
  | 6 => ((t.1.1, t.2.1), (t.2.2, t.1.2))
  | 7 => ((t.1.2, t.2.1), (t.2.2, t.1.1))

private theorem perm4_injective (k : Fin 8) : Function.Injective (perm4 (G := G) k) := by
  rintro ⟨⟨a1, a2⟩, a3, a4⟩ ⟨⟨b1, b2⟩, b3, b4⟩ h
  fin_cases k <;> simp_all [perm4]

private theorem perm4_box (S : Finset G) (k : Fin 8) :
    ∀ t ∈ (S ×ˢ S) ×ˢ (S ×ˢ S), perm4 k t ∈ (S ×ˢ S) ×ˢ (S ×ˢ S) := by
  intro t ht
  obtain ⟨h1, h2, h3, h4⟩ := mem4 S t ht
  fin_cases k <;> exact mem4_mk S ‹_› ‹_› ‹_› ‹_›

private theorem perm4_qsum (k : Fin 8) (t : (G × G) × (G × G)) :
    qsum (perm4 k t) = qsum t := by
  fin_cases k <;> simp only [perm4, qsum] <;> abel

/-- Transport of a fixed-position bound along `perm4 k`. -/
private theorem fixedFilter_perm4_le (S : Finset G) (x : G) (k : Fin 8)
    (P : (G × G) × (G × G) → Prop) [DecidablePred P] :
    (fixedFilter S x (fun t => P (perm4 k t))).card ≤ (fixedFilter S x P).card :=
  fixedFilter_comp_card_le S x (perm4 k) (perm4_injective k) (perm4_box S k) (perm4_qsum k) P

/-- Cardinality of a six- (or four-) fold union of fixed-position filters. -/
private theorem card_union_le_sum {α : Type*} [DecidableEq α] (A B C D : Finset α) :
    (A ∪ B ∪ C ∪ D).card ≤ A.card + B.card + C.card + D.card := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  exact Finset.card_union_le _ _

/-! ## The antipodal stratum: one base injection, five permutations -/

/-- Base case: the `(1,2)`-antipodal fiber injects into `S × (pair fiber)` via
`t ↦ (t₁, (t₃, t₄))`. -/
private theorem antip12_le (S : Finset G) (x : G) :
    (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card ≤ S.card * pairCount S x := by
  classical
  have hmaps : ∀ t ∈ fixedFilter S x (fun t => t.1.1 + t.1.2 = 0),
      (t.1.1, (t.2.1, t.2.2)) ∈ S ×ˢ ((S ×ˢ S).filter fun q : G × G => q.1 + q.2 = x) := by
    intro t ht
    have hm := mem4 S t (Finset.mem_filter.mp ht).1
    have hc := (Finset.mem_filter.mp ht).2
    refine Finset.mem_product.mpr ⟨hm.1, Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hm.2.2.1, hm.2.2.2⟩, ?_⟩⟩
    have hq : t.1.1 + t.1.2 + t.2.1 + t.2.2 = x := hc.1
    have : t.1.1 + t.1.2 + t.2.1 + t.2.2 = (t.1.1 + t.1.2) + (t.2.1 + t.2.2) := by abel
    rw [this, hc.2, zero_add] at hq
    exact hq
  have hinj : Set.InjOn (fun t : (G × G) × (G × G) => (t.1.1, (t.2.1, t.2.2)))
      ((fixedFilter S x (fun t => t.1.1 + t.1.2 = 0) : Finset ((G × G) × (G × G))) :
        Set ((G × G) × (G × G))) := by
    rintro ⟨⟨a1, a2⟩, a3, a4⟩ ha ⟨⟨b1, b2⟩, b3, b4⟩ hb h
    have ha' : a1 + a2 = 0 := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2.2
    have hb' : b1 + b2 = 0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.2
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h3, h4⟩ := h
    have h2 : a2 = b2 := by
      rw [(neg_eq_of_add_eq_zero_right ha').symm, (neg_eq_of_add_eq_zero_right hb').symm, h1]
    simp [h1, h2, h3, h4]
  calc (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card
      ≤ (S ×ˢ ((S ×ˢ S).filter fun q : G × G => q.1 + q.2 = x)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = S.card * pairCount S x := by rw [Finset.card_product]; rfl

/-- **Antipodal stratum bound**: at most `6·n·pairCount x`. -/
theorem antipQuadCount_le (S : Finset G) (x : G) :
    antipQuadCount S x ≤ 6 * (S.card * pairCount S x) := by
  classical
  unfold antipQuadCount
  have hsubset : (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = x ∧ HasAntipodal t) ⊆
      (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.2.1 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.2.2 = 0)) ∪
      fixedFilter S x (fun t => t.1.2 + t.2.1 = 0) ∪
      fixedFilter S x (fun t => t.1.2 + t.2.2 = 0) ∪
      fixedFilter S x (fun t => t.2.1 + t.2.2 = 0) := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    simp only [Finset.mem_union]
    rcases ht'.2.2 with h | h | h | h | h | h
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <|
        Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr <|
        Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inr <|
        Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inl <| Or.inl <| Or.inr <| Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inl <| Or.inr <| Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inr <| Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
  have h12 := antip12_le S x
  have h13 : (fixedFilter S x (fun t => t.1.1 + t.2.1 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card :=
    fixedFilter_perm4_le S x 0 (fun t => t.1.1 + t.1.2 = 0)
  have h14 : (fixedFilter S x (fun t => t.1.1 + t.2.2 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card :=
    fixedFilter_perm4_le S x 1 (fun t => t.1.1 + t.1.2 = 0)
  have h23 : (fixedFilter S x (fun t => t.1.2 + t.2.1 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card :=
    fixedFilter_perm4_le S x 2 (fun t => t.1.1 + t.1.2 = 0)
  have h24 : (fixedFilter S x (fun t => t.1.2 + t.2.2 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card :=
    fixedFilter_perm4_le S x 3 (fun t => t.1.1 + t.1.2 = 0)
  have h34 : (fixedFilter S x (fun t => t.2.1 + t.2.2 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card :=
    fixedFilter_perm4_le S x 4 (fun t => t.1.1 + t.1.2 = 0)
  have hA := card_union_le_sum
    (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0))
    (fixedFilter S x (fun t => t.1.1 + t.2.1 = 0))
    (fixedFilter S x (fun t => t.1.1 + t.2.2 = 0))
    (fixedFilter S x (fun t => t.1.2 + t.2.1 = 0))
  have hB := card_union_le_sum
    (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.2.1 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.2.2 = 0))
    (fixedFilter S x (fun t => t.1.2 + t.2.1 = 0))
    (fixedFilter S x (fun t => t.1.2 + t.2.2 = 0))
    (fixedFilter S x (fun t => t.2.1 + t.2.2 = 0))
  have hC := Finset.card_le_card hsubset
  have hU3 : (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.2.1 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.2.2 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 = 0)).card +
      (fixedFilter S x (fun t => t.1.1 + t.2.1 = 0)).card +
      (fixedFilter S x (fun t => t.1.1 + t.2.2 = 0)).card :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  omega

/-! ## The zero-triple stratum: one base injection, three permutations -/

/-- Base case: the `(1,2,3)`-zero-triple fiber injects into the zero-sum triples via
`t ↦ (t₁, t₂, t₃)` (the fourth entry is recovered from the sum). -/
private theorem zt123_le (S : Finset G) (x : G) :
    (fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.1 = 0)).card ≤ zeroTripleCount S := by
  apply Finset.card_le_card_of_injOn (fun t => (t.1.1, t.1.2, t.2.1))
  · intro t ht
    have hm := mem4 S t (Finset.mem_filter.mp ht).1
    have hc := (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm.1,
      Finset.mem_product.mpr ⟨hm.2.1, hm.2.2.1⟩⟩, hc.2⟩
  · rintro ⟨⟨a1, a2⟩, a3, a4⟩ ha ⟨⟨b1, b2⟩, b3, b4⟩ hb h
    have ha' : qsum ((a1, a2), a3, a4) = x ∧ a1 + a2 + a3 = 0 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' : qsum ((b1, b2), b3, b4) = x ∧ b1 + b2 + b3 = 0 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have h4 : a4 = b4 := by
      have e1 : a1 + a2 + a3 + a4 = x := ha'.1
      have e2 : b1 + b2 + b3 + b4 = x := hb'.1
      rw [ha'.2, zero_add] at e1
      rw [hb'.2, zero_add] at e2
      exact e1.trans e2.symm
    simp [h1, h2, h3, h4]

/-- **Zero-triple stratum bound**: at most `4·zeroTripleCount`.  (The `¬HasAntipodal`
side condition of the stratum is not needed for this bound.) -/
theorem ztQuadCount_le (S : Finset G) (x : G) :
    ztQuadCount S x ≤ 4 * zeroTripleCount S := by
  classical
  unfold ztQuadCount
  have hsubset : (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
      fun t => qsum t = x ∧ ¬HasAntipodal t ∧ HasZeroTriple t) ⊆
      fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.1 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.2 = 0) ∪
      fixedFilter S x (fun t => t.1.1 + t.2.1 + t.2.2 = 0) ∪
      fixedFilter S x (fun t => t.1.2 + t.2.1 + t.2.2 = 0) := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    simp only [Finset.mem_union]
    rcases ht'.2.2.2 with h | h | h | h
    · exact Or.inl <| Or.inl <| Or.inl <| Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inl <| Or.inl <| Or.inr <| Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inl <| Or.inr <| Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
    · exact Or.inr <| Finset.mem_filter.mpr ⟨ht'.1, ht'.2.1, h⟩
  have h123 := zt123_le S x
  have h124 : (fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.2 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.1 = 0)).card :=
    fixedFilter_perm4_le S x 5 (fun t => t.1.1 + t.1.2 + t.2.1 = 0)
  have h134 : (fixedFilter S x (fun t => t.1.1 + t.2.1 + t.2.2 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.1 = 0)).card :=
    fixedFilter_perm4_le S x 6 (fun t => t.1.1 + t.1.2 + t.2.1 = 0)
  have h234 : (fixedFilter S x (fun t => t.1.2 + t.2.1 + t.2.2 = 0)).card ≤
      (fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.1 = 0)).card :=
    fixedFilter_perm4_le S x 7 (fun t => t.1.1 + t.1.2 + t.2.1 = 0)
  have hU := card_union_le_sum
    (fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.1 = 0))
    (fixedFilter S x (fun t => t.1.1 + t.1.2 + t.2.2 = 0))
    (fixedFilter S x (fun t => t.1.1 + t.2.1 + t.2.2 = 0))
    (fixedFilter S x (fun t => t.1.2 + t.2.1 + t.2.2 = 0))
  have hC := Finset.card_le_card hsubset
  omega

/-! ## The (2,4) and (2,2) convolution identities -/

/-- **Depth-4 convolution identity** (G87's `quadCount_eq_conv`). -/
theorem quadCount_eq_conv (S : Finset G) (x : G) :
    quadCount S x = ∑ c : G, pairCount S c * pairCount S (x - c) := by
  rw [quadCount_eq_G87]
  exact ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.quadCount_eq_conv S x

/-- The depth-6 fiber over a fixed leading-pair sum `c` splits off a full quad fiber. -/
theorem sext_fiber_eq_product (S : Finset G) (a c : G) :
    ((((S ×ˢ S) ×ˢ ((S ×ˢ S) ×ˢ (S ×ˢ S))).filter
        fun q => q.1.1 + q.1.2 + qsum q.2 = a).filter
      fun q => q.1.1 + q.1.2 = c) =
    ((S ×ˢ S).filter fun q : G × G => q.1 + q.2 = c) ×ˢ
      (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => qsum t = a - c) := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, htot⟩, hfst⟩
    refine ⟨⟨h1, hfst⟩, h2, ?_⟩
    calc qsum q.2
        = (q.1.1 + q.1.2 + qsum q.2) - (q.1.1 + q.1.2) := by abel
      _ = a - c := by rw [htot, hfst]
  · rintro ⟨⟨h1, hfst⟩, h2, hsnd⟩
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, hfst⟩
    calc q.1.1 + q.1.2 + qsum q.2
        = (q.1.1 + q.1.2) + qsum q.2 := by abel
      _ = c + (a - c) := by rw [hfst, hsnd]
      _ = a := by abel

/-- **Depth-6 (2,4) convolution identity**. -/
theorem sextCount_eq_conv (S : Finset G) (a : G) :
    sextCount S a = ∑ c : G, pairCount S c * quadCount S (a - c) := by
  classical
  unfold sextCount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun q : (G × G) × ((G × G) × (G × G)) => q.1.1 + q.1.2) (t := Finset.univ)
    (fun q _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sext_fiber_eq_product S a c, Finset.card_product]
  rfl

/-! ## Stratified convolutions -/

/-- Convolution of the pair count against the primitive quad stratum. -/
def convP (S : Finset G) (a : G) : ℕ :=
  ∑ c : G, pairCount S c * primQuadCount S (a - c)

/-- Convolution of the pair count against the antipodal quad stratum. -/
def convA (S : Finset G) (a : G) : ℕ :=
  ∑ c : G, pairCount S c * antipQuadCount S (a - c)

/-- Convolution of the pair count against the zero-triple quad stratum. -/
def convB (S : Finset G) (a : G) : ℕ :=
  ∑ c : G, pairCount S c * ztQuadCount S (a - c)

/-- The depth-6 fiber count splits along the quad strata. -/
theorem sextCount_split (S : Finset G) (a : G) :
    sextCount S a = convP S a + convA S a + convB S a := by
  rw [sextCount_eq_conv]
  unfold convP convA convB
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [quadCount_split]
  ring

/-! ## Total masses of the strata -/

theorem primQuadCount_le_quadCount (S : Finset G) (x : G) :
    primQuadCount S x ≤ quadCount S x := by
  have h := quadCount_split S x
  omega

theorem sum_primQuadCount_le (S : Finset G) :
    ∑ x : G, primQuadCount S x ≤ S.card ^ 4 := by
  calc ∑ x : G, primQuadCount S x
      ≤ ∑ x : G, quadCount S x :=
        Finset.sum_le_sum fun x _ => primQuadCount_le_quadCount S x
    _ = S.card ^ 4 := sum_quadCount S

/-- Encoding of a zero-triple 4-tuple: which triple vanishes, the ordered triple, and the
remaining fourth entry (kept as data, NOT recovered from the sum). -/
private def ztEncode : (G × G) × (G × G) → ℕ × (G × G × G) × G := fun t =>
  if t.1.1 + t.1.2 + t.2.1 = 0 then (0, (t.1.1, t.1.2, t.2.1), t.2.2)
  else if t.1.1 + t.1.2 + t.2.2 = 0 then (1, (t.1.1, t.1.2, t.2.2), t.2.1)
  else if t.1.1 + t.2.1 + t.2.2 = 0 then (2, (t.1.1, t.2.1, t.2.2), t.1.2)
  else (3, (t.1.2, t.2.1, t.2.2), t.1.1)

private def ztDecode : ℕ × (G × G × G) × G → (G × G) × (G × G) := fun q =>
  if q.1 = 0 then ((q.2.1.1, q.2.1.2.1), (q.2.1.2.2, q.2.2))
  else if q.1 = 1 then ((q.2.1.1, q.2.1.2.1), (q.2.2, q.2.1.2.2))
  else if q.1 = 2 then ((q.2.1.1, q.2.2), (q.2.1.2.1, q.2.1.2.2))
  else ((q.2.2, q.2.1.1), (q.2.1.2.1, q.2.1.2.2))

private theorem ztDecode_ztEncode (t : (G × G) × (G × G)) :
    ztDecode (ztEncode t) = t := by
  obtain ⟨⟨x, y⟩, z, w⟩ := t
  unfold ztEncode
  by_cases c1 : x + y + z = 0
  · rw [if_pos c1]
    simp [ztDecode]
  · rw [if_neg c1]
    by_cases c2 : x + y + w = 0
    · rw [if_pos c2]
      simp [ztDecode]
    · rw [if_neg c2]
      by_cases c3 : x + z + w = 0
      · rw [if_pos c3]
        simp [ztDecode]
      · rw [if_neg c3]
        simp [ztDecode]

/-- **Total zero-triple stratum mass**: at most `4·Z₃·n`. -/
theorem sum_ztQuadCount_le (S : Finset G) :
    ∑ x : G, ztQuadCount S x ≤ 4 * zeroTripleCount S * S.card := by
  classical
  have hfib : ∑ x : G, ztQuadCount S x =
      (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
        fun t => ¬HasAntipodal t ∧ HasZeroTriple t).card := by
    unfold ztQuadCount
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun t : (G × G) × (G × G) => qsum t) (t := Finset.univ)
      (fun t _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.filter_filter]
    exact congrArg Finset.card (Finset.filter_congr fun t _ => and_comm)
  rw [hfib]
  have hmap : ∀ t ∈ ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
      (fun t => ¬HasAntipodal t ∧ HasZeroTriple t),
      ztEncode t ∈ (Finset.range 4) ×ˢ
        (((S ×ˢ S ×ˢ S).filter fun u : G × G × G => u.1 + u.2.1 + u.2.2 = 0) ×ˢ S) := by
    intro t ht
    have ht' : t ∈ ((S ×ˢ S) ×ˢ (S ×ˢ S)) ∧ (¬HasAntipodal t ∧ HasZeroTriple t) :=
      Finset.mem_filter.mp ht
    have hm := mem4 S t ht'.1
    unfold ztEncode
    by_cases c1 : t.1.1 + t.1.2 + t.2.1 = 0
    · rw [if_pos c1]
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num),
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm.1,
          Finset.mem_product.mpr ⟨hm.2.1, hm.2.2.1⟩⟩, c1⟩, hm.2.2.2⟩⟩
    · rw [if_neg c1]
      by_cases c2 : t.1.1 + t.1.2 + t.2.2 = 0
      · rw [if_pos c2]
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num),
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm.1,
            Finset.mem_product.mpr ⟨hm.2.1, hm.2.2.2⟩⟩, c2⟩, hm.2.2.1⟩⟩
      · rw [if_neg c2]
        by_cases c3 : t.1.1 + t.2.1 + t.2.2 = 0
        · rw [if_pos c3]
          exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num),
            Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm.1,
              Finset.mem_product.mpr ⟨hm.2.2.1, hm.2.2.2⟩⟩, c3⟩, hm.2.1⟩⟩
        · rw [if_neg c3]
          have c4 : t.1.2 + t.2.1 + t.2.2 = 0 := by
            rcases ht'.2.2 with h | h | h | h
            · exact absurd h c1
            · exact absurd h c2
            · exact absurd h c3
            · exact h
          exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num),
            Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm.2.1,
              Finset.mem_product.mpr ⟨hm.2.2.1, hm.2.2.2⟩⟩, c4⟩, hm.1⟩⟩
  have hinj : Set.InjOn ztEncode
      (((((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun t => ¬HasAntipodal t ∧ HasZeroTriple t) :
        Finset ((G × G) × (G × G))) : Set ((G × G) × (G × G))) := by
    intro t _ t' _ he
    rw [← ztDecode_ztEncode t, ← ztDecode_ztEncode t', he]
  calc (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
        fun t => ¬HasAntipodal t ∧ HasZeroTriple t).card
      ≤ ((Finset.range 4) ×ˢ
          (((S ×ˢ S ×ˢ S).filter fun u : G × G × G => u.1 + u.2.1 + u.2.2 = 0) ×ˢ S)).card :=
        Finset.card_le_card_of_injOn ztEncode hmap hinj
    _ = 4 * zeroTripleCount S * S.card := by
        simp only [Finset.card_product, Finset.card_range]
        unfold zeroTripleCount
        ring

/-! ## Generic convolution bounds -/

/-- Pointwise convolution bound from a pointwise bound on the second factor. -/
private theorem conv_le (S : Finset G) (f : G → ℕ) {M : ℕ}
    (hM : ∀ x : G, f x ≤ M) (a : G) :
    ∑ c : G, pairCount S c * f (a - c) ≤ M * S.card ^ 2 := by
  calc ∑ c : G, pairCount S c * f (a - c)
      ≤ ∑ c : G, pairCount S c * M :=
        Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hM _)
    _ = (∑ c : G, pairCount S c) * M := by rw [← Finset.sum_mul]
    _ = M * S.card ^ 2 := by rw [sum_pairCount]; ring

/-- Total convolution bound from a total bound on the second factor. -/
private theorem sum_conv_le (S : Finset G) (f : G → ℕ) {T : ℕ}
    (hT : ∑ x : G, f x ≤ T) :
    ∑ a : G, ∑ c : G, pairCount S c * f (a - c) ≤ S.card ^ 2 * T := by
  classical
  rw [Finset.sum_comm]
  calc ∑ c : G, ∑ a : G, pairCount S c * f (a - c)
      = ∑ c : G, pairCount S c * ∑ a : G, f (a - c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ c : G, pairCount S c * ∑ x : G, f x := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Fintype.sum_equiv (Equiv.subRight c) (fun a => f (a - c)) f (fun a => rfl)]
    _ ≤ ∑ c : G, pairCount S c * T :=
        Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ hT
    _ = (∑ c : G, pairCount S c) * T := by rw [← Finset.sum_mul]
    _ = S.card ^ 2 * T := by rw [sum_pairCount]

/-! ## The three stratum square-masses -/

/-- **Primitive stratum L² bound**: `Σ P² ≤ (M₄ᵖ·n²)·(n²·n⁴)`. -/
theorem sum_convP_sq (S : Finset G) {M4 : ℕ}
    (hM4 : ∀ y : G, primQuadCount S y ≤ M4) :
    ∑ a : G, convP S a ^ 2 ≤ (M4 * S.card ^ 2) * (S.card ^ 2 * S.card ^ 4) := by
  have hpt : ∀ a : G, convP S a ≤ M4 * S.card ^ 2 := fun a =>
    conv_le S (primQuadCount S) hM4 a
  have hsum : ∑ a : G, convP S a ≤ S.card ^ 2 * S.card ^ 4 :=
    sum_conv_le S (primQuadCount S) (sum_primQuadCount_le S)
  calc ∑ a : G, convP S a ^ 2
      ≤ ∑ a : G, (M4 * S.card ^ 2) * convP S a := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [sq]
        exact Nat.mul_le_mul_right _ (hpt a)
    _ = (M4 * S.card ^ 2) * ∑ a : G, convP S a := by rw [Finset.mul_sum]
    _ ≤ (M4 * S.card ^ 2) * (S.card ^ 2 * S.card ^ 4) := Nat.mul_le_mul_left _ hsum

/-- The antipodal convolution recurses through the full depth-4 fiber. -/
theorem convA_le (S : Finset G) (a : G) :
    convA S a ≤ 6 * S.card * quadCount S a := by
  unfold convA
  calc ∑ c : G, pairCount S c * antipQuadCount S (a - c)
      ≤ ∑ c : G, pairCount S c * (6 * (S.card * pairCount S (a - c))) :=
        Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (antipQuadCount_le S (a - c))
    _ = 6 * S.card * ∑ c : G, pairCount S c * pairCount S (a - c) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = 6 * S.card * quadCount S a := by rw [← quadCount_eq_conv]

/-- **Antipodal stratum L² bound**: `Σ A² ≤ 36·n²·J₄`. -/
theorem sum_convA_sq (S : Finset G) :
    ∑ a : G, convA S a ^ 2 ≤ 36 * S.card ^ 2 * ∑ x : G, quadCount S x ^ 2 := by
  calc ∑ a : G, convA S a ^ 2
      ≤ ∑ a : G, (6 * S.card * quadCount S a) ^ 2 :=
        Finset.sum_le_sum fun a _ => Nat.pow_le_pow_left (convA_le S a) 2
    _ = ∑ a : G, 36 * S.card ^ 2 * quadCount S a ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = 36 * S.card ^ 2 * ∑ a : G, quadCount S a ^ 2 := by rw [Finset.mul_sum]

/-- **Depth-4 L² recursion**: `J₄ ≤ (M₄ᵖ + 6n² + 4Z₃)·n⁴`. -/
theorem J4_le (S : Finset G) {M4 Z3 : ℕ}
    (hM4 : ∀ x : G, primQuadCount S x ≤ M4) (hZ3 : zeroTripleCount S ≤ Z3) :
    ∑ x : G, quadCount S x ^ 2 ≤ (M4 + 6 * S.card ^ 2 + 4 * Z3) * S.card ^ 4 := by
  have hpt : ∀ x : G, quadCount S x ≤ M4 + 6 * S.card ^ 2 + 4 * Z3 := by
    intro x
    have hsplit := quadCount_split S x
    have hPr := hM4 x
    have hA' : antipQuadCount S x ≤ 6 * S.card ^ 2 := by
      calc antipQuadCount S x
          ≤ 6 * (S.card * pairCount S x) := antipQuadCount_le S x
        _ ≤ 6 * (S.card * S.card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (pairCount_le_card S x))
        _ = 6 * S.card ^ 2 := by ring
    have hZ' : ztQuadCount S x ≤ 4 * Z3 := by
      calc ztQuadCount S x
          ≤ 4 * zeroTripleCount S := ztQuadCount_le S x
        _ ≤ 4 * Z3 := Nat.mul_le_mul_left _ hZ3
    omega
  calc ∑ x : G, quadCount S x ^ 2
      ≤ ∑ x : G, (M4 + 6 * S.card ^ 2 + 4 * Z3) * quadCount S x := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [sq]
        exact Nat.mul_le_mul_right _ (hpt x)
    _ = (M4 + 6 * S.card ^ 2 + 4 * Z3) * ∑ x : G, quadCount S x := by
        rw [Finset.mul_sum]
    _ = (M4 + 6 * S.card ^ 2 + 4 * Z3) * S.card ^ 4 := by rw [sum_quadCount]

/-- **Zero-triple stratum L² bound**: `Σ B² ≤ (4Z₃·n²)·(n²·(4Z₃·n))`. -/
theorem sum_convB_sq (S : Finset G) {Z3 : ℕ} (hZ3 : zeroTripleCount S ≤ Z3) :
    ∑ a : G, convB S a ^ 2 ≤ (4 * Z3 * S.card ^ 2) * (S.card ^ 2 * (4 * Z3 * S.card)) := by
  have hptB : ∀ x : G, ztQuadCount S x ≤ 4 * Z3 := fun x =>
    le_trans (ztQuadCount_le S x) (Nat.mul_le_mul_left _ hZ3)
  have hpt : ∀ a : G, convB S a ≤ 4 * Z3 * S.card ^ 2 := fun a =>
    conv_le S (ztQuadCount S) hptB a
  have hsum : ∑ a : G, convB S a ≤ S.card ^ 2 * (4 * Z3 * S.card) := by
    refine sum_conv_le S (ztQuadCount S) ?_
    calc ∑ x : G, ztQuadCount S x
        ≤ 4 * zeroTripleCount S * S.card := sum_ztQuadCount_le S
      _ ≤ 4 * Z3 * S.card :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZ3)
  calc ∑ a : G, convB S a ^ 2
      ≤ ∑ a : G, (4 * Z3 * S.card ^ 2) * convB S a := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [sq]
        exact Nat.mul_le_mul_right _ (hpt a)
    _ = (4 * Z3 * S.card ^ 2) * ∑ a : G, convB S a := by rw [Finset.mul_sum]
    _ ≤ (4 * Z3 * S.card ^ 2) * (S.card ^ 2 * (4 * Z3 * S.card)) :=
        Nat.mul_le_mul_left _ hsum

/-! ## The weighted-square inequality and the production consumer -/

/-- Exact weighted split: `5p² + 40a² + 40b² − 4(p+a+b)² = (p−4a−4b)² + 20(a−b)² ≥ 0`. -/
theorem weighted_sq (p a b : ℕ) :
    4 * (p + a + b) ^ 2 ≤ 5 * p ^ 2 + 40 * a ^ 2 + 40 * b ^ 2 := by
  have hz : (4 : ℤ) * ((p : ℤ) + (a : ℤ) + (b : ℤ)) ^ 2 ≤
      5 * (p : ℤ) ^ 2 + 40 * (a : ℤ) ^ 2 + 40 * (b : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((p : ℤ) - 4 * (a : ℤ) - 4 * (b : ℤ)),
      sq_nonneg ((a : ℤ) - (b : ℤ))]
  exact_mod_cast hz

/-- **The stratified depth-6 mass bound at production numbers**:
`4·J₆ ≤ 5·ΣP² + 40·ΣA² + 40·ΣB²` with each stratum square-mass instantiated at
`(M₄ᵖ, n) = (2^22, 2^30)` and a **parametric** zero-triple total `Z₃`. -/
theorem four_mul_mass_le (S : Finset G) {Z3 : ℕ}
    (hcard : S.card = 2 ^ 30)
    (hM4 : ∀ x : G, primQuadCount S x ≤ 2 ^ 22)
    (hZ3 : zeroTripleCount S ≤ Z3) :
    4 * equalSumSextMass S ≤
      5 * (2 ^ 22 * (2 ^ 30) ^ 2 * ((2 ^ 30) ^ 2 * (2 ^ 30) ^ 4)) +
        40 * (36 * (2 ^ 30) ^ 2 *
          ((2 ^ 22 + 6 * (2 ^ 30) ^ 2 + 4 * Z3) * (2 ^ 30) ^ 4)) +
        40 * ((4 * Z3 * (2 ^ 30) ^ 2) * ((2 ^ 30) ^ 2 * (4 * Z3 * (2 ^ 30)))) := by
  have hstep : 4 * equalSumSextMass S ≤
      5 * ∑ a : G, convP S a ^ 2 + 40 * ∑ a : G, convA S a ^ 2 +
        40 * ∑ a : G, convB S a ^ 2 := by
    unfold equalSumSextMass
    rw [Finset.mul_sum]
    calc ∑ a : G, 4 * sextCount S a ^ 2
        ≤ ∑ a : G, (5 * convP S a ^ 2 + 40 * convA S a ^ 2 + 40 * convB S a ^ 2) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [sextCount_split S a]
          exact weighted_sq _ _ _
      _ = 5 * ∑ a : G, convP S a ^ 2 + 40 * ∑ a : G, convA S a ^ 2 +
          40 * ∑ a : G, convB S a ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hP := sum_convP_sq S hM4
  have hA := sum_convA_sq S
  have hJ4 := J4_le S hM4 hZ3
  have hB := sum_convB_sq S hZ3
  rw [hcard] at hP hA hJ4 hB
  have hA' : ∑ a : G, convA S a ^ 2 ≤
      36 * (2 ^ 30) ^ 2 * ((2 ^ 22 + 6 * (2 ^ 30) ^ 2 + 4 * Z3) * (2 ^ 30) ^ 4) := by
    calc ∑ a : G, convA S a ^ 2
        ≤ 36 * (2 ^ 30) ^ 2 * ∑ x : G, quadCount S x ^ 2 := hA
      _ ≤ 36 * (2 ^ 30) ^ 2 * ((2 ^ 22 + 6 * (2 ^ 30) ^ 2 + 4 * Z3) * (2 ^ 30) ^ 4) :=
          Nat.mul_le_mul_left _ hJ4
  refine le_trans hstep ?_
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hP)
    (Nat.mul_le_mul_left _ hA')) (Nat.mul_le_mul_left _ hB)

theorem choose_110_6 : Nat.choose 110 6 = 2141851635 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rfl

/-- Production kernel: the stratified depth-6 bound at `(M₄ᵖ, Z₃) = (2^22, 2^53)` fits inside
four times the depth-6 share of one full Wick budget at `(n, r) = (2^30, 110)`
(margin `≈ 2^{0.37}`; the kernel fails at `Z₃ = 2^54`, so `2^53` is the largest power of two
the stratified chain absorbs). -/
theorem production_kernel :
    (5 * (2 ^ 22 * (2 ^ 30) ^ 2 * ((2 ^ 30) ^ 2 * (2 ^ 30) ^ 4)) +
        40 * (36 * (2 ^ 30) ^ 2 *
          ((2 ^ 22 + 6 * (2 ^ 30) ^ 2 + 4 * 2 ^ 53) * (2 ^ 30) ^ 4)) +
        40 * ((4 * 2 ^ 53 * (2 ^ 30) ^ 2) * ((2 ^ 30) ^ 2 * (4 * 2 ^ 53 * (2 ^ 30))))) *
      (2141851635 ^ 2 * (104)!) ≤ 4 * (Nat.doubleFactorial 219 * (2 ^ 30) ^ 6) := by
  decide

/-- **Headline: depth six is absorbed under primitive-quad concentration `2^22` and
zero-triple total `2^53`.**  The two hypotheses are of different kinds: `M₄ᵖ ≤ 2^22` is a
*pointwise* fiber cap (the Stepanov level `4·n^{2/3}`), while `Z₃ ≤ 2^53` bounds the *total*
number of ordered zero-sum triples; they are not "at the same level".  For a multiplicative
subgroup such as `μ_n`, scaling by the subgroup acts freely on zero-sum triples, so `Z₃` is a
multiple of `n = 2^30` (see `_G105ZeroTripleQuantizationFence.lean`); the hypothesis thus
allows at most `2^23` packets of triples.  Both are named external hypotheses, consumed
arithmetically here.  No pair-concentration hypothesis is needed: the crude `pairCount ≤ n`
suffices inside the stratified L² recursion. -/
theorem production_depth6_of_primitive_quad (S : Finset G)
    (hcard : S.card = 2 ^ 30)
    (hM4 : ∀ x : G, primQuadCount S x ≤ 2 ^ 22)
    (hZ3 : zeroTripleCount S ≤ 2 ^ 53) :
    equalSumSextMass S * (Nat.choose 110 6 ^ 2 * (104)!) ≤
      Nat.doubleFactorial 219 * (2 ^ 30) ^ 6 := by
  have h4 := four_mul_mass_le S hcard hM4 hZ3
  rw [choose_110_6]
  have hmul : 4 * (equalSumSextMass S * (2141851635 ^ 2 * (104)!)) ≤
      4 * (Nat.doubleFactorial 219 * (2 ^ 30) ^ 6) := by
    calc 4 * (equalSumSextMass S * (2141851635 ^ 2 * (104)!))
        = (4 * equalSumSextMass S) * (2141851635 ^ 2 * (104)!) := by ring
      _ ≤ (5 * (2 ^ 22 * (2 ^ 30) ^ 2 * ((2 ^ 30) ^ 2 * (2 ^ 30) ^ 4)) +
            40 * (36 * (2 ^ 30) ^ 2 *
              ((2 ^ 22 + 6 * (2 ^ 30) ^ 2 + 4 * 2 ^ 53) * (2 ^ 30) ^ 4)) +
            40 * ((4 * 2 ^ 53 * (2 ^ 30) ^ 2) *
              ((2 ^ 30) ^ 2 * (4 * 2 ^ 53 * (2 ^ 30))))) *
            (2141851635 ^ 2 * (104)!) :=
          Nat.mul_le_mul_right _ h4
      _ ≤ 4 * (Nat.doubleFactorial 219 * (2 ^ 30) ^ 6) := production_kernel
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

end ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.quadCount_split
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.antipQuadCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.ztQuadCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.quadCount_eq_conv
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.sextCount_eq_conv
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.sextCount_split
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.sum_ztQuadCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.sum_convP_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.sum_convA_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.J4_le
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.sum_convB_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.weighted_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.four_mul_mass_le
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.production_kernel
#print axioms
  ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer.production_depth6_of_primitive_quad
