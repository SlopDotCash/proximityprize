/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SliceLocusCount

/-!
# Issue #232 — the first moment of the coset agreement spectrum (O120 target)

O120 reframed the derandomization question: the mean (and variance) of coset
list sizes over received words are domain-independent closed forms, so the
entire domain-dependence of `δ*` lives in higher moments.  This file lands the
mean as a theorem — **the M1 double-counting identity**:

* `card_exact_agreement` — the generic count: functions `u : α → β` agreeing
  with a fixed `f` on EXACTLY `j` coordinates number
  `C(|α|, j) · (|β| − 1)^(|α| − j)` — partition by the agreement set; each
  fiber is a `piFinset` of singletons and punctured codomains;
* `sum_agreement_spectrum` — **M1**: summing the agreement spectrum
  `a_j(u) = #{p : deg < k, p agrees with u on exactly j points of D}` over ALL
  received words `u : D → F` gives `q^k · C(|D|, j) · (q − 1)^(|D| − j)` —
  for EVERY `|D|`-point domain `D`, smooth or not.  Verified numerically as an
  exact integer identity over all `q^n` received words in
  `scripts/probes/probe_coset_agreement_moments.py` (O120).
-/

namespace AgreementMomentOne

open Finset

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The agreement-fiber description: functions agreeing with `f` exactly on
`A` form the `piFinset` of singletons on `A` and punctured codomains off `A`. -/
lemma exact_agreement_fiber (f : α → β) (A : Finset α) :
    (Finset.univ : Finset (α → β)).filter
        (fun u => Finset.univ.filter (fun x => u x = f x) = A)
      = Fintype.piFinset (fun x => if x ∈ A then {f x} else {f x}ᶜ) := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.mem_piFinset]
  constructor
  · rintro rfl
    intro x
    by_cases hx : u x = f x
    · simp [hx]
    · simp [hx]
  · intro h
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := h x
    by_cases hmem : x ∈ A
    · rw [if_pos hmem] at hx
      simp only [Finset.mem_singleton] at hx
      exact ⟨fun _ => hmem, fun _ => hx⟩
    · rw [if_neg hmem] at hx
      simp only [Finset.mem_compl, Finset.mem_singleton] at hx
      exact ⟨fun h' => absurd h' hx, fun h' => absurd h' hmem⟩

/-- **The generic exact-agreement count**: functions `u : α → β` agreeing with
a fixed `f` on exactly `j` coordinates number
`C(|α|, j) · (|β| − 1)^(|α| − j)`. -/
theorem card_exact_agreement (f : α → β) (j : ℕ) :
    ((Finset.univ : Finset (α → β)).filter
        (fun u => (Finset.univ.filter (fun x => u x = f x)).card = j)).card
      = (Fintype.card α).choose j
        * (Fintype.card β - 1) ^ (Fintype.card α - j) := by
  classical
  have hpart : (Finset.univ : Finset (α → β)).filter
        (fun u => (Finset.univ.filter (fun x => u x = f x)).card = j)
      = (Finset.univ.powersetCard j).biUnion (fun A =>
          (Finset.univ : Finset (α → β)).filter
            (fun u => Finset.univ.filter (fun x => u x = f x) = A)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_powersetCard]
    constructor
    · intro hcard
      exact ⟨Finset.univ.filter (fun x => u x = f x),
        ⟨Finset.subset_univ _, hcard⟩, rfl⟩
    · rintro ⟨A, ⟨_, hcard⟩, rfl⟩
      exact hcard
  have hdisj : ∀ A ∈ Finset.univ.powersetCard j,
      ∀ A' ∈ Finset.univ.powersetCard j, A ≠ A' →
      Disjoint ((Finset.univ : Finset (α → β)).filter
          (fun u => Finset.univ.filter (fun x => u x = f x) = A))
        ((Finset.univ : Finset (α → β)).filter
          (fun u => Finset.univ.filter (fun x => u x = f x) = A')) := by
    intro A _ A' _ hne
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨-, hA⟩ := Finset.mem_filter.mp hu
    obtain ⟨-, hA'⟩ := Finset.mem_filter.mp hu'
    exact hne (hA ▸ hA')
  have hfiber : ∀ A ∈ Finset.univ.powersetCard j,
      ((Finset.univ : Finset (α → β)).filter
          (fun u => Finset.univ.filter (fun x => u x = f x) = A)).card
        = (Fintype.card β - 1) ^ (Fintype.card α - j) := by
    intro A hA
    obtain ⟨-, hAcard⟩ := Finset.mem_powersetCard.mp hA
    rw [exact_agreement_fiber, Fintype.card_piFinset]
    have hcards : ∀ x : α,
        (if x ∈ A then ({f x} : Finset β) else {f x}ᶜ).card
        = if x ∈ A then 1 else Fintype.card β - 1 := by
      intro x
      by_cases hx : x ∈ A
      · simp [hx]
      · simp [hx, Finset.card_compl]
    rw [Finset.prod_congr rfl fun x _ => hcards x, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const, one_pow, one_mul]
    congr 1
    rw [Finset.filter_not, Finset.filter_univ_mem, Finset.card_sdiff,
      Finset.card_univ, Finset.inter_univ, hAcard]
  rw [hpart, Finset.card_biUnion hdisj, Finset.sum_congr rfl hfiber,
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]

/-! ## The RS instance: the agreement-spectrum first moment -/

open LamLeungTwoPow Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **M1 — the agreement-spectrum first moment** (the O120 closed form):
summed over ALL received words `u : D → F`, the number of degree-`< k`
polynomials agreeing with `u` on exactly `j` points of `D` is
`q^k · C(|D|, j) · (q − 1)^(|D| − j)` — for EVERY domain `D`.  The mean coset
list size is domain-independent; `δ*`'s domain-dependence is strictly a
higher-moment/tail phenomenon. -/
theorem sum_agreement_spectrum (D : Finset F) (k j : ℕ) :
    ∑ u : ↥D → F, ((polysDegLT (F := F) k).filter
        (fun p => (Finset.univ.filter
          (fun x : ↥D => p.eval x.val = u x)).card = j)).card
      = Fintype.card F ^ k * ((D.card.choose j)
        * (Fintype.card F - 1) ^ (D.card - j)) := by
  classical
  have hswap : ∑ u : ↥D → F, ((polysDegLT (F := F) k).filter
        (fun p => (Finset.univ.filter
          (fun x : ↥D => p.eval x.val = u x)).card = j)).card
      = ∑ p ∈ polysDegLT (F := F) k,
          ((Finset.univ : Finset (↥D → F)).filter
            (fun u => (Finset.univ.filter
              (fun x : ↥D => u x = p.eval x.val)).card = j)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    have hsum : (∑ i : ↥D, if p.eval i.val = u i then (1 : ℕ) else 0)
        = ∑ i : ↥D, if u i = p.eval i.val then (1 : ℕ) else 0 :=
      Finset.sum_congr rfl fun x _ => if_congr eq_comm rfl rfl
    rw [hsum]
  rw [hswap]
  have hinner : ∀ p ∈ polysDegLT (F := F) k,
      ((Finset.univ : Finset (↥D → F)).filter
        (fun u => (Finset.univ.filter
          (fun x : ↥D => u x = p.eval x.val)).card = j)).card
      = (D.card.choose j) * (Fintype.card F - 1) ^ (D.card - j) := by
    intro p _
    have := card_exact_agreement (fun x : ↥D => p.eval x.val) j
    rwa [Fintype.card_coe] at this
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, card_polysDegLT,
    smul_eq_mul]

end AgreementMomentOne
