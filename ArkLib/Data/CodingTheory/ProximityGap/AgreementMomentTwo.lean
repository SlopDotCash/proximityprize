/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AgreementMomentOne

/-!
# Issue #334 — the second moment of the coset agreement spectrum (O120's M2)

The successor to `AgreementMomentOne`: where M1 computed the mean of the agreement
spectrum `a_j(u) = #{p : deg < k, p agrees with u on exactly j points of D}` over all
received words, this file lands the **second moment** — the variance input to the
O120 derandomization program.  Statements were numeric-gated against brute-force
enumeration before proving (`scripts/probes/moments/gate/gate_m2_statements.py`); the
probe layer for the surrounding program is `scripts/probes/moments/` (O133: M3 is the
FIRST domain-dependent agreement moment — the M2 below is domain-independent, entering
only through the weight enumerator, which MDS-ness pins).

* `pairAgreementCount` — the closed form for the generic two-constraint count: with
  `d` disagreement points and `e` agreement points between `f` and `g` over a
  `q`-element codomain, the number of `u` agreeing with `f` on exactly `j₁` and with
  `g` on exactly `j₂` coordinates is
  `∑_{s ≤ min j₁ j₂} C(e,s)·(q−1)^(e−s)·C(d,j₁−s)·C(d−(j₁−s),j₂−s)·(q−2)^(d−(j₁−s)−(j₂−s))`,
  all subtraction truncated (out-of-range terms self-annihilate through
  `Nat.choose = 0`, and the `q < 2` degeneracies are absorbed by `0 ^ 0 = 1`);
* `card_exact_pair_agreement` — **the generic count** (ToMathlib-grade): the
  two-exact-agreement count for any `f g : α → β` equals `pairAgreementCount`
  at `q = |β|`, `d = #{x | f x ≠ g x}`, `e = #{x | f x = g x}`;
* `sum_agreement_spectrum_sq` — **M2**: summing `a_j(u)²` over ALL received words
  `u : D → F` gives `q^k · ∑_{c : deg < k} pairAgreementCount q (wt c) (|D| − wt c) j j`
  where `wt c = #{x ∈ D | c(x) ≠ 0}` — the domain enters ONLY through the weight
  enumerator of the code;
* `sq_agreement_le_sum_agreement_spectrum_sq` — the per-word corollary:
  `a_j(u₀)² ≤` the M2 right-hand side, for every fixed `u₀`.
-/

namespace AgreementMomentTwo

open Finset

/-- The closed-form **pair-agreement count**: over a `q`-element codomain, given a
reference pair `(f, g)` with `d` disagreement and `e` agreement coordinates, the
number of functions agreeing with `f` on exactly `j₁` and with `g` on exactly `j₂`
coordinates, summed over the size `s` of the common agreement inside the equal set.
All subtraction is truncated (`Nat`): terms with `s` out of range self-annihilate
via `Nat.choose = 0`, and `q ≤ 2` degeneracies are absorbed by `0 ^ 0 = 1`. -/
def pairAgreementCount (q d e j₁ j₂ : ℕ) : ℕ :=
  ∑ s ∈ Finset.Iic (min j₁ j₂),
    e.choose s * (q - 1) ^ (e - s)
      * d.choose (j₁ - s) * (d - (j₁ - s)).choose (j₂ - s)
      * (q - 2) ^ (d - (j₁ - s) - (j₂ - s))

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The per-coordinate **zone**: the values `u x` compatible with the prescribed
agreement pattern (`x ∈ T` ⟺ `u x = f x`, and `x ∈ G` ⟺ `u x = g x`). -/
private def zone (f g : α → β) (T G : Finset α) (x : α) : Finset β :=
  (if x ∈ T then {f x} else {f x}ᶜ) ∩ (if x ∈ G then {g x} else {g x}ᶜ)

/-- The pair-agreement fiber: functions whose two exact agreement SETS are `(T, G)`
form the `piFinset` of the zones. -/
private lemma pair_agreement_fiber (f g : α → β) (T G : Finset α) :
    ((Finset.univ : Finset (α → β)).filter
        (fun u => Finset.univ.filter (fun x => u x = f x) = T
          ∧ Finset.univ.filter (fun x => u x = g x) = G))
      = Fintype.piFinset (zone f g T G) := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, zone,
    Finset.mem_inter]
  constructor
  · rintro ⟨rfl, rfl⟩ x
    constructor
    · by_cases h : u x = f x <;> simp [h]
    · by_cases h : u x = g x <;> simp [h]
  · intro h
    constructor
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨h1, -⟩ := h x
      by_cases hx : x ∈ T
      · rw [if_pos hx] at h1
        simp only [Finset.mem_singleton] at h1
        exact ⟨fun _ => hx, fun _ => h1⟩
      · rw [if_neg hx] at h1
        simp only [Finset.mem_compl, Finset.mem_singleton] at h1
        exact ⟨fun hc => absurd hc h1, fun hc => absurd hc hx⟩
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨-, h2⟩ := h x
      by_cases hx : x ∈ G
      · rw [if_pos hx] at h2
        simp only [Finset.mem_singleton] at h2
        exact ⟨fun _ => hx, fun _ => h2⟩
      · rw [if_neg hx] at h2
        simp only [Finset.mem_compl, Finset.mem_singleton] at h2
        exact ⟨fun hc => absurd hc h2, fun hc => absurd hc hx⟩

/-- Fiber cardinality at a compatible index: `S` inside the equal set, `A, B`
disjoint inside the unequal set give `(q−1)^(e−|S|) · (q−2)^(d−|A|−|B|)`. -/
private lemma card_pair_fiber (f g : α → β) (S A B : Finset α)
    (hS : S ⊆ Finset.univ.filter (fun x => f x = g x))
    (hA : A ⊆ Finset.univ.filter (fun x => f x ≠ g x))
    (hB : B ⊆ Finset.univ.filter (fun x => f x ≠ g x))
    (hAB : Disjoint A B) :
    (Fintype.piFinset (zone f g (S ∪ A) (S ∪ B))).card
      = (Fintype.card β - 1)
          ^ ((Finset.univ.filter (fun x => f x = g x)).card - S.card)
        * (Fintype.card β - 2)
          ^ ((Finset.univ.filter (fun x => f x ≠ g x)).card - A.card - B.card) := by
  rw [Fintype.card_piFinset]
  have hcards : ∀ x : α, (zone f g (S ∪ A) (S ∪ B) x).card
      = if x ∈ S ∪ A ∪ B then 1
        else if f x = g x then Fintype.card β - 1 else Fintype.card β - 2 := by
    intro x
    by_cases hfg : f x = g x
    · have hxA : x ∉ A := fun hc => by
        have := hA hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this hfg
      have hxB : x ∉ B := fun hc => by
        have := hB hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this hfg
      by_cases hxS : x ∈ S
      · have h1 : x ∈ S ∪ A := Finset.mem_union_left _ hxS
        have h2 : x ∈ S ∪ B := Finset.mem_union_left _ hxS
        have h3 : x ∈ S ∪ A ∪ B := Finset.mem_union_left _ h1
        rw [zone, if_pos h1, if_pos h2, if_pos h3, hfg, Finset.inter_self,
          Finset.card_singleton]
      · have h1 : x ∉ S ∪ A := by simp [hxS, hxA]
        have h2 : x ∉ S ∪ B := by simp [hxS, hxB]
        have h3 : x ∉ S ∪ A ∪ B := by simp [hxS, hxA, hxB]
        rw [zone, if_neg h1, if_neg h2, if_neg h3, if_pos hfg, hfg, Finset.inter_self,
          Finset.card_compl, Finset.card_singleton]
    · have hxS : x ∉ S := fun hc => by
        have := hS hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact hfg this
      by_cases hxA : x ∈ A
      · have hxB : x ∉ B := Finset.disjoint_left.mp hAB hxA
        have h1 : x ∈ S ∪ A := Finset.mem_union_right _ hxA
        have h2 : x ∉ S ∪ B := by simp [hxS, hxB]
        have h3 : x ∈ S ∪ A ∪ B := Finset.mem_union_left _ h1
        rw [zone, if_pos h1, if_neg h2, if_pos h3,
          Finset.singleton_inter_of_mem (by
            simp only [Finset.mem_compl, Finset.mem_singleton]; exact hfg),
          Finset.card_singleton]
      · by_cases hxB : x ∈ B
        · have h1 : x ∉ S ∪ A := by simp [hxS, hxA]
          have h2 : x ∈ S ∪ B := Finset.mem_union_right _ hxB
          have h3 : x ∈ S ∪ A ∪ B := Finset.mem_union_right _ hxB
          rw [zone, if_neg h1, if_pos h2, if_pos h3, Finset.inter_comm,
            Finset.singleton_inter_of_mem (by
              simp only [Finset.mem_compl, Finset.mem_singleton]
              exact fun hc => hfg hc.symm),
            Finset.card_singleton]
        · have h1 : x ∉ S ∪ A := by simp [hxS, hxA]
          have h2 : x ∉ S ∪ B := by simp [hxS, hxB]
          have h3 : x ∉ S ∪ A ∪ B := by simp [hxS, hxA, hxB]
          rw [zone, if_neg h1, if_neg h2, if_neg h3, if_neg hfg,
            ← Finset.compl_union, Finset.card_compl, Finset.singleton_union,
            Finset.card_pair hfg]
  rw [Finset.prod_congr rfl fun x _ => hcards x, Finset.prod_ite, Finset.prod_const,
    one_pow, one_mul, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hfilter1 : ((Finset.univ.filter (fun x => x ∉ S ∪ A ∪ B)).filter
        (fun x => f x = g x))
      = (Finset.univ.filter (fun x => f x = g x)) \ S := by
    ext x
    simp only [Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨hnotin, hfg⟩
      exact ⟨hfg, fun hxS => hnotin (Finset.mem_union_left _ (Finset.mem_union_left _ hxS))⟩
    · rintro ⟨hfg, hxS⟩
      refine ⟨fun hmem => ?_, hfg⟩
      rcases Finset.mem_union.mp hmem with hSA | hxB
      · rcases Finset.mem_union.mp hSA with hxS' | hxA
        · exact hxS hxS'
        · have := hA hxA
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this hfg
      · have := hB hxB
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this hfg
  have hfilter2 : ((Finset.univ.filter (fun x => x ∉ S ∪ A ∪ B)).filter
        (fun x => ¬ f x = g x))
      = (Finset.univ.filter (fun x => f x ≠ g x)) \ (A ∪ B) := by
    ext x
    simp only [Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, ne_eq]
    constructor
    · rintro ⟨hnotin, hfg⟩
      exact ⟨hfg, fun hmem => hnotin (by
        rcases Finset.mem_union.mp hmem with hxA | hxB
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxA)
        · exact Finset.mem_union_right _ hxB)⟩
    · rintro ⟨hfg, hnotAB⟩
      refine ⟨fun hmem => ?_, hfg⟩
      rcases Finset.mem_union.mp hmem with hSA | hxB
      · rcases Finset.mem_union.mp hSA with hxS | hxA
        · have := hS hxS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact hfg this
        · exact hnotAB (Finset.mem_union_left _ hxA)
      · exact hnotAB (Finset.mem_union_right _ hxB)
  rw [hfilter1, hfilter2, Finset.card_sdiff, Finset.inter_eq_left.mpr hS,
    Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.union_subset hA hB),
    Finset.card_union_of_disjoint hAB, Nat.sub_sub]

/-- **The generic exact-pair-agreement count**: functions `u : α → β` agreeing with
`f` on exactly `j₁` coordinates AND with `g` on exactly `j₂` coordinates number
`pairAgreementCount |β| d e j₁ j₂`, where `d = #{x | f x ≠ g x}` and
`e = #{x | f x = g x}`.  Partition by the triple
`(S, A, B) = (common agreement inside the equal set, f-only agreement, g-only
agreement)`; each fiber is a `piFinset` of singletons, punctured, and
doubly-punctured codomains. -/
theorem card_exact_pair_agreement (f g : α → β) (j₁ j₂ : ℕ) :
    ((Finset.univ : Finset (α → β)).filter
        (fun u => (Finset.univ.filter (fun x => u x = f x)).card = j₁
          ∧ (Finset.univ.filter (fun x => u x = g x)).card = j₂)).card
      = pairAgreementCount (Fintype.card β)
          (Finset.univ.filter (fun x => f x ≠ g x)).card
          (Finset.univ.filter (fun x => f x = g x)).card j₁ j₂ := by
  classical
  set E := Finset.univ.filter (fun x => f x = g x) with hE
  set Ec := Finset.univ.filter (fun x => f x ≠ g x) with hEc
  -- membership in E/Ec is exclusive
  have hEEc : ∀ {x : α}, x ∈ E → x ∈ Ec → False := by
    intro x hx hx'
    simp only [hE, hEc, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hx' hx
  -- component recovery from the unions
  have hrec1 : ∀ {S₀ A₀ : Finset α}, S₀ ⊆ E → A₀ ⊆ Ec → (S₀ ∪ A₀) ∩ E = S₀ := by
    intro S₀ A₀ hS₀ hA₀
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxE⟩
      · exact hx
      · exact absurd hxE (fun hc => hEEc hc (hA₀ hx))
    · intro hx
      exact ⟨Or.inl hx, hS₀ hx⟩
  have hrec2 : ∀ {S₀ A₀ : Finset α}, S₀ ⊆ E → A₀ ⊆ Ec → (S₀ ∪ A₀) \ E = A₀ := by
    intro S₀ A₀ hS₀ hA₀
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxE⟩
      · exact absurd (hS₀ hx) hxE
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun hc => hEEc hc (hA₀ hx)⟩
  -- the sigma index: s, then S ⊆ E of card s, A ⊆ Ec of card j₁−s,
  -- then B ⊆ Ec \ A of card j₂−s
  set I : Finset ((_s : ℕ) × (_S : Finset α) × (_A : Finset α) × Finset α) :=
    (Finset.Iic (min j₁ j₂)).sigma (fun s =>
      (E.powersetCard s).sigma (fun _S =>
        (Ec.powersetCard (j₁ - s)).sigma (fun A =>
          (Ec \ A).powersetCard (j₂ - s)))) with hI
  have hmemI : ∀ {t}, t ∈ I ↔ t.1 ≤ min j₁ j₂ ∧ (t.2.1 ⊆ E ∧ t.2.1.card = t.1)
      ∧ (t.2.2.1 ⊆ Ec ∧ t.2.2.1.card = j₁ - t.1)
      ∧ (t.2.2.2 ⊆ Ec \ t.2.2.1 ∧ t.2.2.2.card = j₂ - t.1) := by
    intro t
    simp only [hI, Finset.mem_sigma, Finset.mem_Iic, Finset.mem_powersetCard, and_assoc]
  -- the partition of the count filter by the canonical index
  have hpart : ((Finset.univ : Finset (α → β)).filter
        (fun u => (Finset.univ.filter (fun x => u x = f x)).card = j₁
          ∧ (Finset.univ.filter (fun x => u x = g x)).card = j₂))
      = I.biUnion (fun t =>
          (Finset.univ : Finset (α → β)).filter
            (fun u => Finset.univ.filter (fun x => u x = f x) = t.2.1 ∪ t.2.2.1
              ∧ Finset.univ.filter (fun x => u x = g x) = t.2.1 ∪ t.2.2.2)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩
      set T := Finset.univ.filter (fun x => u x = f x) with hT
      set G := Finset.univ.filter (fun x => u x = g x) with hG
      have hTE_eq_GE : T ∩ E = G ∩ E := by
        ext x
        simp only [hT, hG, hE, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨huf, hfg⟩
          exact ⟨hfg ▸ huf, hfg⟩
        · rintro ⟨hug, hfg⟩
          exact ⟨hfg ▸ hug, hfg⟩
      have hTEsub : T \ E ⊆ Ec := by
        intro x hx
        obtain ⟨-, hxE⟩ := Finset.mem_sdiff.mp hx
        simp only [hEc, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hfg
        exact hxE (by simp [hE, hfg])
      have hGEsub : G \ E ⊆ Ec := by
        intro x hx
        obtain ⟨-, hxE⟩ := Finset.mem_sdiff.mp hx
        simp only [hEc, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hfg
        exact hxE (by simp [hE, hfg])
      refine ⟨⟨(T ∩ E).card, T ∩ E, T \ E, G \ E⟩, hmemI.mpr ⟨?_, ⟨Finset.inter_subset_right, rfl⟩,
        ⟨hTEsub, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩
      · refine le_min (h1 ▸ Finset.card_le_card Finset.inter_subset_left)
          (h2 ▸ hTE_eq_GE ▸ Finset.card_le_card Finset.inter_subset_left)
      · have := Finset.card_inter_add_card_sdiff T E
        dsimp only
        omega
      · -- G \ E avoids T \ E
        intro x hx
        obtain ⟨hxG, hxE⟩ := Finset.mem_sdiff.mp hx
        refine Finset.mem_sdiff.mpr ⟨hGEsub hx, fun hc => ?_⟩
        obtain ⟨hxT, -⟩ := Finset.mem_sdiff.mp hc
        have huf : u x = f x := by simpa [hT] using hxT
        have hug : u x = g x := by simpa [hG] using hxG
        exact hxE (by simp [hE, huf.symm.trans hug])
      · have := Finset.card_inter_add_card_sdiff G E
        dsimp only
        rw [hTE_eq_GE]
        omega
      · rw [Finset.union_comm, Finset.sdiff_union_inter]
      · rw [hTE_eq_GE, Finset.union_comm, Finset.sdiff_union_inter]
    · rintro ⟨⟨s, S, A, B⟩, htI, hTu, hGu⟩
      obtain ⟨hsle, ⟨hSE, hScard⟩, ⟨hAEc, hAcard⟩, ⟨hBEcA, hBcard⟩⟩ := hmemI.mp htI
      obtain ⟨hs1, hs2⟩ := le_min_iff.mp hsle
      have hSA : Disjoint S A :=
        Finset.disjoint_left.mpr fun x hxS hxA => hEEc (hSE hxS) (hAEc hxA)
      have hSB : Disjoint S B :=
        Finset.disjoint_left.mpr fun x hxS hxB =>
          hEEc (hSE hxS) ((Finset.mem_sdiff.mp (hBEcA hxB)).1)
      constructor
      · rw [hTu, Finset.card_union_of_disjoint hSA, hScard, hAcard]
        exact Nat.add_sub_cancel' hs1
      · rw [hGu, Finset.card_union_of_disjoint hSB, hScard, hBcard]
        exact Nat.add_sub_cancel' hs2
  -- fibers at distinct indices are disjoint
  have hdisj : ∀ t ∈ I, ∀ t' ∈ I, t ≠ t' →
      Disjoint ((Finset.univ : Finset (α → β)).filter
          (fun u => Finset.univ.filter (fun x => u x = f x) = t.2.1 ∪ t.2.2.1
            ∧ Finset.univ.filter (fun x => u x = g x) = t.2.1 ∪ t.2.2.2))
        ((Finset.univ : Finset (α → β)).filter
          (fun u => Finset.univ.filter (fun x => u x = f x) = t'.2.1 ∪ t'.2.2.1
            ∧ Finset.univ.filter (fun x => u x = g x) = t'.2.1 ∪ t'.2.2.2)) := by
    rintro ⟨s, S, A, B⟩ ht ⟨s', S', A', B'⟩ ht' hne
    obtain ⟨-, ⟨hSE, hScard⟩, ⟨hAEc, -⟩, ⟨hBEcA, -⟩⟩ := hmemI.mp ht
    obtain ⟨-, ⟨hSE', hScard'⟩, ⟨hAEc', -⟩, ⟨hBEcA', -⟩⟩ := hmemI.mp ht'
    dsimp only at hSE hScard hAEc hBEcA hSE' hScard' hAEc' hBEcA'
    have hBEc : B ⊆ Ec := fun x hx => (Finset.mem_sdiff.mp (hBEcA hx)).1
    have hBEc' : B' ⊆ Ec := fun x hx => (Finset.mem_sdiff.mp (hBEcA' hx)).1
    rw [Finset.disjoint_left]
    rintro u hu hu'
    obtain ⟨-, hT, hG⟩ := Finset.mem_filter.mp hu
    obtain ⟨-, hT', hG'⟩ := Finset.mem_filter.mp hu'
    dsimp only at hT hG hT' hG'
    have hTT : S ∪ A = S' ∪ A' := hT ▸ hT'
    have hGG : S ∪ B = S' ∪ B' := hG ▸ hG'
    have hSeq : S = S' := by
      rw [← hrec1 hSE hAEc, hTT, hrec1 hSE' hAEc']
    have hAeq : A = A' := by
      rw [← hrec2 hSE hAEc, hTT, hrec2 hSE' hAEc']
    have hBeq : B = B' := by
      rw [← hrec2 hSE hBEc, hGG, hrec2 hSE' hBEc']
    have hseq : s = s' := by rw [← hScard, ← hScard', hSeq]
    subst hseq hSeq hAeq hBeq
    exact hne rfl
  -- per-fiber cardinality
  have hfib : ∀ t ∈ I,
      ((Finset.univ : Finset (α → β)).filter
          (fun u => Finset.univ.filter (fun x => u x = f x) = t.2.1 ∪ t.2.2.1
            ∧ Finset.univ.filter (fun x => u x = g x) = t.2.1 ∪ t.2.2.2)).card
        = (Fintype.card β - 1) ^ (E.card - t.1)
          * (Fintype.card β - 2) ^ (Ec.card - (j₁ - t.1) - (j₂ - t.1)) := by
    rintro ⟨s, S, A, B⟩ ht
    obtain ⟨-, ⟨hSE, hScard⟩, ⟨hAEc, hAcard⟩, ⟨hBEcA, hBcard⟩⟩ := hmemI.mp ht
    dsimp only at hSE hScard hAEc hAcard hBEcA hBcard ⊢
    have hBEc : B ⊆ Ec := fun x hx => (Finset.mem_sdiff.mp (hBEcA hx)).1
    have hAB : Disjoint A B :=
      Finset.disjoint_right.mpr fun x hxB => (Finset.mem_sdiff.mp (hBEcA hxB)).2
    rw [pair_agreement_fiber, card_pair_fiber f g S A B hSE hAEc hBEc hAB, hScard,
      hAcard, hBcard]
  rw [hpart, Finset.card_biUnion hdisj, Finset.sum_congr rfl hfib]
  -- evaluate the sigma sums
  rw [hI, Finset.sum_sigma, pairAgreementCount]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.sum_sigma]
  have hinner : ∀ S₀ ∈ E.powersetCard s,
      (∑ x ∈ (Ec.powersetCard (j₁ - s)).sigma
          (fun A => (Ec \ A).powersetCard (j₂ - s)),
        (Fintype.card β - 1) ^ (E.card - s)
          * (Fintype.card β - 2) ^ (Ec.card - (j₁ - s) - (j₂ - s)))
      = Ec.card.choose (j₁ - s) * ((Ec.card - (j₁ - s)).choose (j₂ - s)
          * ((Fintype.card β - 1) ^ (E.card - s)
            * (Fintype.card β - 2) ^ (Ec.card - (j₁ - s) - (j₂ - s)))) := by
    intro S₀ _
    rw [Finset.sum_sigma]
    have hA_inner : ∀ A₀ ∈ Ec.powersetCard (j₁ - s),
        (∑ _B ∈ (Ec \ A₀).powersetCard (j₂ - s),
          (Fintype.card β - 1) ^ (E.card - s)
            * (Fintype.card β - 2) ^ (Ec.card - (j₁ - s) - (j₂ - s)))
        = (Ec.card - (j₁ - s)).choose (j₂ - s)
            * ((Fintype.card β - 1) ^ (E.card - s)
              * (Fintype.card β - 2) ^ (Ec.card - (j₁ - s) - (j₂ - s))) := by
      intro A₀ hA₀
      obtain ⟨hA₀sub, hA₀card⟩ := Finset.mem_powersetCard.mp hA₀
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hA₀sub, hA₀card, smul_eq_mul]
    rw [Finset.sum_congr rfl hA_inner, Finset.sum_const, Finset.card_powersetCard,
      smul_eq_mul]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard,
    smul_eq_mul]
  ring

/-! ## The RS instance: the agreement-spectrum second moment -/

open LamLeungTwoPow Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Difference of two `degree < k` polynomials stays in `polysDegLT`. -/
private lemma sub_mem_polysDegLT {k : ℕ} {p₁ p₂ : F[X]}
    (h₁ : p₁ ∈ polysDegLT (F := F) k) (h₂ : p₂ ∈ polysDegLT (F := F) k) :
    p₁ - p₂ ∈ polysDegLT (F := F) k := by
  rw [mem_polysDegLT] at h₁ h₂ ⊢
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h₁ h₂)

/-- Sum of two `degree < k` polynomials stays in `polysDegLT`. -/
private lemma add_mem_polysDegLT {k : ℕ} {p₁ p₂ : F[X]}
    (h₁ : p₁ ∈ polysDegLT (F := F) k) (h₂ : p₂ ∈ polysDegLT (F := F) k) :
    p₁ + p₂ ∈ polysDegLT (F := F) k := by
  rw [mem_polysDegLT] at h₁ h₂ ⊢
  exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt h₁ h₂)

/-- **M2 — the agreement-spectrum second moment** (the O120 variance input): summed
over ALL received words `u : D → F`, the square of the number of degree-`< k`
polynomials agreeing with `u` on exactly `j` points of `D` is
`q^k · ∑_{c : deg < k} pairAgreementCount q (wt c) (|D| − wt c) j j`, where
`wt c = #{x ∈ D | c.eval x ≠ 0}` is the evaluation weight on `D`.  Expand the square
over ordered pairs `(p₁, p₂)`, count per pair via `card_exact_pair_agreement`
(translating by `p₂`), then collapse the pair sum by the sub/add closure of
`polysDegLT`.  The domain enters ONLY through the weight enumerator. -/
theorem sum_agreement_spectrum_sq (D : Finset F) (k j : ℕ) :
    ∑ u : ↥D → F, ((polysDegLT (F := F) k).filter
        (fun p => (Finset.univ.filter
          (fun x : ↥D => p.eval x.val = u x)).card = j)).card ^ 2
      = Fintype.card F ^ k * ∑ c ∈ polysDegLT (F := F) k,
          pairAgreementCount (Fintype.card F)
            (Finset.univ.filter (fun x : ↥D => c.eval x.val ≠ 0)).card
            (D.card - (Finset.univ.filter (fun x : ↥D => c.eval x.val ≠ 0)).card)
            j j := by
  classical
  -- step 1: expand the square into a sum over ordered pairs of code polynomials
  have hsq : ∀ u : ↥D → F,
      ((polysDegLT (F := F) k).filter
          (fun p => (Finset.univ.filter
            (fun x : ↥D => p.eval x.val = u x)).card = j)).card ^ 2
        = ∑ p₁ ∈ polysDegLT (F := F) k, ∑ p₂ ∈ polysDegLT (F := F) k,
            if ((Finset.univ.filter (fun x : ↥D => p₁.eval x.val = u x)).card = j
              ∧ (Finset.univ.filter (fun x : ↥D => p₂.eval x.val = u x)).card = j)
            then 1 else 0 := by
    intro u
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
    split_ifs with h1 h2 h3 h4 <;> simp_all
  rw [Finset.sum_congr rfl fun u _ => hsq u]
  -- step 2: swap the sums so the received word is innermost, then count per pair
  rw [Finset.sum_comm]
  have hswap : ∀ p₁ ∈ polysDegLT (F := F) k,
      (∑ u : ↥D → F, ∑ p₂ ∈ polysDegLT (F := F) k,
        if ((Finset.univ.filter (fun x : ↥D => p₁.eval x.val = u x)).card = j
          ∧ (Finset.univ.filter (fun x : ↥D => p₂.eval x.val = u x)).card = j)
        then 1 else 0)
      = ∑ p₂ ∈ polysDegLT (F := F) k, ∑ u : ↥D → F,
          if ((Finset.univ.filter (fun x : ↥D => p₁.eval x.val = u x)).card = j
            ∧ (Finset.univ.filter (fun x : ↥D => p₂.eval x.val = u x)).card = j)
          then 1 else 0 := fun p₁ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hswap]
  -- step 3: the inner sum over u is the generic pair count
  have hcount : ∀ p₁ p₂ : F[X],
      (∑ u : ↥D → F,
        if ((Finset.univ.filter (fun x : ↥D => p₁.eval x.val = u x)).card = j
          ∧ (Finset.univ.filter (fun x : ↥D => p₂.eval x.val = u x)).card = j)
        then 1 else 0)
      = pairAgreementCount (Fintype.card F)
          (Finset.univ.filter
            (fun x : ↥D => ¬ p₁.eval x.val = p₂.eval x.val)).card
          (Finset.univ.filter
            (fun x : ↥D => p₁.eval x.val = p₂.eval x.val)).card j j := by
    intro p₁ p₂
    rw [← card_exact_pair_agreement (fun x : ↥D => p₁.eval x.val)
      (fun x : ↥D => p₂.eval x.val) j j, Finset.card_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 2
    · ext
      simp only [eq_comm]
    · ext
      simp only [eq_comm]
  rw [Finset.sum_congr rfl fun p₁ h₁ =>
    Finset.sum_congr rfl fun p₂ h₂ => hcount p₁ p₂]
  -- step 4: rewrite the pair data through the difference polynomial
  have hdata : ∀ p₁ p₂ : F[X],
      (Finset.univ.filter
          (fun x : ↥D => ¬ p₁.eval x.val = p₂.eval x.val)).card
        = (Finset.univ.filter
            (fun x : ↥D => (p₁ - p₂).eval x.val ≠ 0)).card
      ∧ (Finset.univ.filter
          (fun x : ↥D => p₁.eval x.val = p₂.eval x.val)).card
        = D.card - (Finset.univ.filter
            (fun x : ↥D => (p₁ - p₂).eval x.val ≠ 0)).card := by
    intro p₁ p₂
    have hfe : (Finset.univ.filter
        (fun x : ↥D => ¬ p₁.eval x.val = p₂.eval x.val))
        = (Finset.univ.filter (fun x : ↥D => (p₁ - p₂).eval x.val ≠ 0)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Polynomial.eval_sub,
        ne_eq, sub_eq_zero]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ↥D))
      (p := fun x : ↥D => p₁.eval x.val = p₂.eval x.val)
    rw [Finset.card_univ, Fintype.card_coe] at hpartition
    refine ⟨by rw [hfe], ?_⟩
    rw [← hfe]
    omega
  have hstep4 : ∀ p₁ ∈ polysDegLT (F := F) k, ∀ p₂ ∈ polysDegLT (F := F) k,
      pairAgreementCount (Fintype.card F)
          (Finset.univ.filter
            (fun x : ↥D => ¬ p₁.eval x.val = p₂.eval x.val)).card
          (Finset.univ.filter
            (fun x : ↥D => p₁.eval x.val = p₂.eval x.val)).card j j
        = pairAgreementCount (Fintype.card F)
            (Finset.univ.filter
              (fun x : ↥D => (p₁ - p₂).eval x.val ≠ 0)).card
            (D.card - (Finset.univ.filter
              (fun x : ↥D => (p₁ - p₂).eval x.val ≠ 0)).card) j j := by
    intro p₁ _ p₂ _
    rw [(hdata p₁ p₂).1, (hdata p₁ p₂).2]
  rw [Finset.sum_congr rfl fun p₁ h₁ =>
    Finset.sum_congr rfl fun p₂ h₂ => hstep4 p₁ h₁ p₂ h₂]
  -- step 5: collapse the ordered-pair sum via the translation bijection
  have hcollapse : ∀ p₂ ∈ polysDegLT (F := F) k,
      (∑ p₁ ∈ polysDegLT (F := F) k,
        pairAgreementCount (Fintype.card F)
          (Finset.univ.filter
            (fun x : ↥D => (p₁ - p₂).eval x.val ≠ 0)).card
          (D.card - (Finset.univ.filter
            (fun x : ↥D => (p₁ - p₂).eval x.val ≠ 0)).card) j j)
      = ∑ c ∈ polysDegLT (F := F) k,
          pairAgreementCount (Fintype.card F)
            (Finset.univ.filter (fun x : ↥D => c.eval x.val ≠ 0)).card
            (D.card - (Finset.univ.filter
              (fun x : ↥D => c.eval x.val ≠ 0)).card) j j := by
    intro p₂ h₂
    refine Finset.sum_nbij' (fun p₁ => p₁ - p₂) (fun c => c + p₂) ?_ ?_ ?_ ?_ ?_
    · intro p₁ h₁
      exact sub_mem_polysDegLT h₁ h₂
    · intro c hc
      exact add_mem_polysDegLT hc h₂
    · intro p₁ _
      ring
    · intro c _
      ring
    · intro p₁ _
      rfl
  rw [Finset.sum_comm, Finset.sum_congr rfl hcollapse, Finset.sum_const,
    card_polysDegLT, smul_eq_mul]

/-- **The per-word second-moment bound**: for every fixed received word `u₀`, the
squared agreement-spectrum entry `a_j(u₀)²` is at most the full M2 sum — one term of
a sum of squares is at most the sum. -/
theorem sq_agreement_le_sum_agreement_spectrum_sq (D : Finset F) (k j : ℕ)
    (u₀ : ↥D → F) :
    ((polysDegLT (F := F) k).filter
        (fun p => (Finset.univ.filter
          (fun x : ↥D => p.eval x.val = u₀ x)).card = j)).card ^ 2
      ≤ Fintype.card F ^ k * ∑ c ∈ polysDegLT (F := F) k,
          pairAgreementCount (Fintype.card F)
            (Finset.univ.filter (fun x : ↥D => c.eval x.val ≠ 0)).card
            (D.card - (Finset.univ.filter (fun x : ↥D => c.eval x.val ≠ 0)).card)
            j j := by
  rw [← sum_agreement_spectrum_sq D k j]
  exact Finset.single_le_sum (f := fun u : ↥D → F =>
    ((polysDegLT (F := F) k).filter
      (fun p => (Finset.univ.filter
        (fun x : ↥D => p.eval x.val = u x)).card = j)).card ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ u₀)

end AgreementMomentTwo
