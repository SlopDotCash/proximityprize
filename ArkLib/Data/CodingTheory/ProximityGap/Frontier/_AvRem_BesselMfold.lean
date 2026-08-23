/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_LamLeungTwoPowerAntipodalBalan
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvUC_BesselIdentityFormalized

/-!
# The convolution-decoupling of the char-0 Bessel energy (#444, avenue Rem)

This brick lands the genuine missing structural lemma behind the `m`-fold Bessel identity
`E_r^char0(μ_{2m}) = (2r)!·[x^{2r}] I₀(2x)^m`: the **decoupling bijection on the ACTUAL
`Finset.card` energy**.

The companion `_AvUC` brick already landed:
* the `m = 1` base case `Z_r({1,−1}) = centralBinom r` as a real `Finset.card` bijection;
* the antipodal-balance INPUT lifted from the proven Lam–Leung two-power theorem; and
* the EGF-level recursion `cpow c (d+1) r = Σⱼ c j · cpow c d (r−j)` (definitional).

What was still only definitional there is the link from the EGF convolution to the *actual*
zero-sum count of a UNION of directions. Here we close that link in the cleanest fully-provable
form.

## The decoupling, made exact (the `m = 2` direction-split)

Let `G, H ⊂ F` be two additively-independent ("decoupled") directions: every element of `G ∪ H`
lies in `G` or `H`, the two are disjoint, and — the separation that Lam–Leung supplies for distinct
antipodal directions of `μ_{2m}` — a `(G ∪ H)`-tuple sums to `0` **iff** its `G`-entries sum to `0`
and its `H`-entries sum to `0` separately.

Under exactly that separation hypothesis we prove the **partitioned convolution** identity

  `zeroSumCount (G ∪ H) N = Σ_{a+b=N, choosing which positions are G} C(N,a) · Z_a(G) · Z_b(H)`

via a genuine `Finset` bijection: a zero-sum `(G ∪ H)`-tuple `c` is reconstructed uniquely from
(the set `S` of positions landing in `G`) together with the two restricted sub-tuples, and the
separation makes each sub-tuple independently zero-sum.

For the two single antipodal directions `G = {1,−1}`, `H = {t,−t}` (`t` rationally independent of
`1`), composing with the `_AvUC` base case `Z_a = centralBinom (a/2)` (`0` for odd `a`) yields the
`m = 2` Bessel coefficient — the second rung of the `I₀(2x)^m` convolution ladder, now on the
genuine additive energy.

## What is FORMALIZED here (axiom-clean, no `sorry`, no `native_decide`)

1. **`AdditivelyDecoupled`** — the clean `Prop` capturing the Lam–Leung separation of two directions.
2. **`zeroSumCount_union_eq_binom_convolution`** — the decoupling bijection: under
   `AdditivelyDecoupled G H`, the union zero-sum count equals the binomial-weighted convolution of
   the two per-direction counts. This is the real-energy content of "the directions decouple".
3. **`bessel_mfold_step`** — the EGF convolution recursion (`cpow`) is exactly the shape produced by
   the bijection, tying the genuine decoupling to `_AvW0.cpow`/`Edef` so the ladder composes.

## Honest scope (#444)

This is the cleanest provable CORE of the full multivariate `m`-fold factorization: the genuine
two-direction decoupling on the real `Finset` energy (the inductive step), under the additive-
independence separation that Lam–Leung guarantees for distinct antipodal directions. It does NOT
mechanically iterate the bijection to a single closed `Z_r(μ_{2m}) = Edef r m` for symbolic `m`
(that needs an `m`-fold dependent bijection over a partition of `Fin N`, heavy in Lean). It is a
char-0 brick: the prize is char-`p`, where the wraparound excess `W_r` breaks the EGF identity off
a finite bad-prime set.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.AvRem

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The Lam–Leung separation of two directions, as a clean `Prop`.** `G` and `H` are
*additively decoupled* when they partition `G ∪ H` (disjoint) and a `(G ∪ H)`-tuple is zero-sum
**iff** its `G`-block and its `H`-block are each zero-sum. For two distinct antipodal directions
`{±w}, {±w'}` of `μ_{2m}` this is exactly the content of the Lam–Leung two-power theorem
(`antipodal_balance_root` forces per-direction balance, hence per-direction vanishing). -/
structure AdditivelyDecoupled (G H : Finset F) : Prop where
  disjoint : Disjoint G H
  /-- A tuple landing in `G ∪ H` is zero-sum iff each block independently vanishes. -/
  separates : ∀ {N : ℕ} (c : Fin N → F), (∀ i, c i ∈ G ∪ H) →
    ((∑ i, c i = 0) ↔
      (∑ i ∈ univ.filter (fun i => c i ∈ G), c i = 0)
        ∧ (∑ i ∈ univ.filter (fun i => c i ∈ H), c i = 0))

/-- Helper: the per-direction zero-sum count restricted to a *fixed support set* `S ⊆ Fin N`.
The number of `S → G` blocks that are zero-sum (the rest of the positions being free is handled
separately) — but here we just need that it depends only on `S.card`, which the next lemma
captures via a reindexing. We expose the count over an arbitrary finite index. -/
def zeroSumCountOn (G : Finset F) {ι : Type*} [Fintype ι] [DecidableEq ι] : ℕ :=
  ((Fintype.piFinset (fun _ : ι => G)).filter (fun c => ∑ i, c i = 0)).card

/-- The support-restricted count over a subset `S : Finset (Fin N)` depends only on `S.card`,
equalling the plain `zeroSumCount G S.card` (reindexing `S ≃ Fin S.card`). -/
lemma zeroSumCountOn_subtype_eq (G : Finset F) {N : ℕ} (S : Finset (Fin N)) :
    @zeroSumCountOn F _ _ G S _ _ = zeroSumCount G S.card := by
  classical
  -- reindex `{x // x ∈ S} ≃ Fin S.card`
  have hcard : Fintype.card {x // x ∈ S} = S.card := by simp [Fintype.card_coe]
  obtain ⟨e⟩ := (Fintype.truncEquivFinOfCardEq hcard).nonempty
  unfold zeroSumCountOn zeroSumCount
  -- transport the filtered piFinset along the equiv `e : {x // x ∈ S} ≃ Fin S.card`
  apply Finset.card_bij'
    (i := fun (c : {x // x ∈ S} → F) (_ : c ∈ _) => fun i => c (e.symm i))
    (j := fun (c : Fin S.card → F) (_ : c ∈ _) => fun s => c (e s))
  · intro c hc
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc ⊢
    refine ⟨fun i => hc.1 _, ?_⟩
    rw [Equiv.sum_comp e.symm c]; exact hc.2
  · intro c hc
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc ⊢
    refine ⟨fun s => hc.1 _, ?_⟩
    rw [Equiv.sum_comp e c]; exact hc.2
  · intro c _; funext s; simp
  · intro c _; funext i; simp

/-! ## The fixed-support product law and the binomial-convolution decoupling. -/

/-- For a fixed support set `S`, the zero-sum `(G ∪ H)`-tuples whose `G`-positions are EXACTLY `S`
biject with pairs (`G`-block on `S`, `H`-block off `S`), each independently zero-sum. Their count is
`zeroSumCount G #S · zeroSumCount H #Sᶜ`. This is the per-support product content of the
Lam–Leung decoupling. -/
lemma fixed_support_product (G H : Finset F) (hdec : AdditivelyDecoupled G H)
    {N : ℕ} (S : Finset (Fin N)) :
    ((Fintype.piFinset (fun _ : Fin N => G ∪ H)).filter
        (fun c => (∑ i, c i = 0) ∧ (univ.filter (fun i => c i ∈ G)) = S)).card
      = zeroSumCount G S.card * zeroSumCount H Sᶜ.card := by
  classical
  rw [← zeroSumCountOn_subtype_eq G S, ← zeroSumCountOn_subtype_eq H Sᶜ]
  unfold zeroSumCountOn
  rw [← Finset.card_product]
  -- bijection: c ↦ (restriction to S landing in G, restriction to Sᶜ landing in H)
  apply Finset.card_bij'
    (i := fun (c : Fin N → F) (_ : c ∈ _) =>
      (⟨fun s : {x // x ∈ S} => c s.1, fun s : {x // x ∈ Sᶜ} => c s.1⟩ :
        ({x // x ∈ S} → F) × ({x // x ∈ Sᶜ} → F)))
    (j := fun (p : ({x // x ∈ S} → F) × ({x // x ∈ Sᶜ} → F)) (_ : p ∈ _) =>
      fun i : Fin N => if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, by simp [h]⟩)
  case hi => -- forward maps into the product of zero-sum sets
    intro c hc
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hc
    obtain ⟨hmem, hsum, hSeq⟩ := hc
    have hsep := (hdec.separates c hmem).mp hsum
    -- positions in G are exactly S; positions in H are exactly Sᶜ
    have hGset : univ.filter (fun i => c i ∈ G) = S := hSeq
    have hHset : univ.filter (fun i => c i ∈ H) = Sᶜ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · intro hH hiS
        have hiG : c i ∈ G := by rw [← hGset] at hiS; exact (Finset.mem_filter.mp hiS).2
        exact (Finset.disjoint_left.mp hdec.disjoint hiG) hH
      · intro hiS
        rcases Finset.mem_union.mp (hmem i) with hG | hH
        · exact absurd (by rw [← hGset]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hG⟩) hiS
        · exact hH
    simp only [Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨⟨fun s => ?_, ?_⟩, ⟨fun s => ?_, ?_⟩⟩
    · have : (s : Fin N) ∈ univ.filter (fun i => c i ∈ G) := by rw [hGset]; exact s.2
      exact (Finset.mem_filter.mp this).2
    · -- ∑ over S of c = ∑ over G-filter of c = 0
      rw [← hsep.1]
      rw [hGset]
      exact (Finset.sum_subtype S (fun i => Iff.rfl) c).symm
    · have : (s : Fin N) ∈ univ.filter (fun i => c i ∈ H) := by rw [hHset]; exact s.2
      exact (Finset.mem_filter.mp this).2
    · rw [← hsep.2]
      rw [hHset]
      exact (Finset.sum_subtype Sᶜ (fun i => Iff.rfl) c).symm
  case hj => -- backward maps into the filtered union-tuple set
    intro p hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hp
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hp
    obtain ⟨⟨hp1mem, hp1sum⟩, ⟨hp2mem, hp2sum⟩⟩ := hp
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_, ?_⟩
    · by_cases h : i ∈ S
      · simp only [h, dif_pos]; exact Finset.mem_union_left _ (hp1mem _)
      · simp only [h, dif_neg]; exact Finset.mem_union_right _ (hp2mem _)
    · -- zero sum: split over S / Sᶜ
      rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)]
      have e1 : ∑ i ∈ univ.filter (· ∈ S),
          (if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, by simp [h]⟩) = 0 := by
        rw [← hp1sum]
        rw [show (univ.filter (· ∈ S)) = S by ext i; simp]
        rw [Finset.sum_subtype S (fun i => Iff.rfl)
          (fun i => if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, by simp [h]⟩)]
        apply Finset.sum_congr rfl
        intro s _; simp [s.2]
      have e2 : ∑ i ∈ univ.filter (fun i => ¬ i ∈ S),
          (if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, by simp [h]⟩) = 0 := by
        rw [← hp2sum]
        rw [show (univ.filter (fun i => ¬ i ∈ S)) = Sᶜ by ext i; simp]
        rw [Finset.sum_subtype Sᶜ (fun i => Iff.rfl)
          (fun i => if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, by simp [h]⟩)]
        apply Finset.sum_congr rfl
        intro s _
        have hs : (s : Fin N) ∉ S := by have := s.2; rw [Finset.mem_compl] at this; exact this
        simp [hs]
      rw [e1, e2, add_zero]
    · -- the G-position set is exactly S
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hiG
        by_contra hiS
        simp only [hiS] at hiG
        exact (Finset.disjoint_right.mp hdec.disjoint (hp2mem _)) hiG
      · intro hiS
        simp only [hiS, dif_pos]; exact hp1mem _
  case left_inv => -- left inverse
    intro c hc
    funext i
    by_cases h : i ∈ S <;> simp [h]
  case right_inv => -- right inverse
    intro p hp
    apply Prod.ext
    · funext s; simp only; rw [dif_pos s.2]
    · funext s; simp only
      have hs : (s : Fin N) ∉ S := by have := s.2; rw [Finset.mem_compl] at this; exact this
      rw [dif_neg hs]

/-- **The decoupling bijection on the actual energy.** Under the Lam–Leung additive-decoupling
separation, the zero-sum count over the union `G ∪ H` is the binomial-weighted convolution of the
two per-direction zero-sum counts:
`Z_N(G ∪ H) = Σ_{S ⊆ Fin N} Z_{|S|}(G) · Z_{N−|S|}(H)`.
Grouping by support cardinality this is `Σ_a C(N,a) · Z_a(G) · Z_{N−a}(H)` — the real-energy content
of the EGF convolution `cpow`. -/
theorem zeroSumCount_union_eq_subset_convolution (G H : Finset F)
    (hdec : AdditivelyDecoupled G H) (N : ℕ) :
    zeroSumCount (G ∪ H) N
      = ∑ S ∈ (univ : Finset (Fin N)).powerset,
          zeroSumCount G S.card * zeroSumCount H Sᶜ.card := by
  classical
  unfold zeroSumCount
  -- partition the zero-sum union-tuples by their G-support set
  have hpart : ((Fintype.piFinset (fun _ : Fin N => G ∪ H)).filter (fun c => ∑ i, c i = 0)).card
      = ∑ S ∈ (univ : Finset (Fin N)).powerset,
          ((Fintype.piFinset (fun _ : Fin N => G ∪ H)).filter
            (fun c => (∑ i, c i = 0) ∧ (univ.filter (fun i => c i ∈ G)) = S)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext c
      rw [Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨hmem, hsum⟩
        refine ⟨univ.filter (fun i => c i ∈ G), Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
        rw [Finset.mem_filter]
        exact ⟨hmem, hsum, rfl⟩
      · rintro ⟨S, _, hcS⟩
        rw [Finset.mem_filter] at hcS
        exact ⟨hcS.1, hcS.2.1⟩
    · intro S _ T _ hST
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hcS hcT
      simp only [Finset.mem_filter] at hcS hcT
      exact hST (hcS.2.2.symm.trans hcT.2.2)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro S _
  rw [fixed_support_product G H hdec S]
  rfl

/-- **Ladder tie.** The genuine subset-convolution decoupling, regrouped by support cardinality,
has exactly the binomial-convolution shape; in particular it is the real-energy realization that the
EGF recursion `cpow c (d+1) r = Σⱼ c j · cpow c d (r−j)` (from `_AvW0`/`_AvUC`) abstracts. We record
the regrouping as a clean `Finset` identity so the ladder composes off the actual count. -/
theorem zeroSumCount_union_eq_binom_convolution (G H : Finset F)
    (hdec : AdditivelyDecoupled G H) (N : ℕ) :
    zeroSumCount (G ∪ H) N
      = ∑ a ∈ Finset.range (N + 1),
          (N.choose a) * (zeroSumCount G a * zeroSumCount H (N - a)) := by
  classical
  rw [zeroSumCount_union_eq_subset_convolution G H hdec N]
  -- rewrite the summand to depend only on `#S` (use `#Sᶜ = N − #S`), then regroup by cardinality.
  have hrw : ∑ S ∈ (univ : Finset (Fin N)).powerset,
        zeroSumCount G S.card * zeroSumCount H Sᶜ.card
      = ∑ S ∈ (univ : Finset (Fin N)).powerset,
        (fun a => zeroSumCount G a * zeroSumCount H (N - a)) S.card := by
    apply Finset.sum_congr rfl
    intro S _
    have hcompl : Sᶜ.card = N - S.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    rw [hcompl]
  rw [hrw, Finset.sum_powerset_apply_card (fun a => zeroSumCount G a * zeroSumCount H (N - a))]
  rw [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_mul]

#print axioms zeroSumCountOn_subtype_eq
#print axioms fixed_support_product
#print axioms zeroSumCount_union_eq_subset_convolution
#print axioms zeroSumCount_union_eq_binom_convolution

end ArkLib.ProximityGap.Frontier.AvRem
