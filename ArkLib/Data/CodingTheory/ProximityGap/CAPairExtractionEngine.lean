/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Round 17 (Issue #232) — the CA pair-extraction engine: RVW13 half-threshold uniqueness and the
# equal-threshold `C(n, k+1)` ceiling (the verified kernel of ePrint 2026/858)

The May-2026 ePrints 2026/858 ("FRI Soundness Above the Johnson Bound via Threshold Halving",
Chai–Fan) and 2026/861 claim above-Johnson FRI soundness. Our adversarial deep-read (posted to
#232) found: the protocol result **sidesteps** the open-zone combinatorics (fold once into the
unique-decoding regime where BCIKS locks the distance, pay ~2× queries — conclusion threshold
`δ/2`) and does NOT touch the prize quantity (zero-loss/equal-threshold CA/MCA in the open zone —
their own claim map marks it "Not solved here"). The genuinely reusable mathematical kernel is two
clean correlated-agreement facts, both powered by ONE engine — *two bad γ's solve for the codeword
pair*. We formalize both, self-contained, in exact agreement-count (ℕ) form.

**The engine** (`pair_of_two_bad`): if `f₁ + γ·f₂` agrees with a codeword `c` on `S` and
`f₁ + γ'·f₂` agrees with `c'` on `S'` (`γ ≠ γ'`), then on `S ∩ S'` the pair `(f₁, f₂)` agrees with
the pair `(g₁, g₂) := (c − γ·g₂, (γ−γ')⁻¹·(c − c'))` — solving two linear equations in two
unknowns pointwise.

**Theorem A** (`bad_card_le_one`, = RVW13 / 2026/858 Thm 5): if every codeword pair has joint
agreement `≤ J` with `(f₁, f₂)` and the bad threshold `a` satisfies the half-threshold condition
`J + n < 2a` (two `a`-agreement sets must overlap in `> J` points), then **at most one γ is bad**.
This is the engine behind the threshold-halving FRI soundness (`1/|F|` per round, unconditional,
at conclusion threshold `δ/2` — the intrinsic ~2× query cost of any CA-framework proof).

**Theorem B** (`bad_card_le_choose`, = 2026/858 Thm 7): at the equal threshold — bad means
agreement `≥ k+1` with some codeword while every pair has joint agreement `≤ k` — the bad set
injects into the `(k+1)`-subsets of the domain: `#bad ≤ C(n, k+1)`. **Field-independent.**

**Prize relevance (honest).** Theorem B is the "OP1 ceiling": the equal-threshold CA error obeys
`ε_ca ≤ C(n,k+1)/|F|` — formally `O(1)/|F|` at fixed `n` but exponential in `n`, hence VACUOUS at
prize scale (`C(n,k+1) ≫ ε*·|F| ≤ 2^128` once `n·H(ρ) > 128`). The matching tightness
(2026/858 Prop 9) needs `|F| > C(n,w)²` — astronomically beyond the prize cap `|F| < 2^256` — so
in the prize regime the equal-threshold CA value remains genuinely open between the (vacuous)
ceiling and the (non-fitting) tightness construction. Neither external paper closes the prize
window; this file extracts what is true, verified, and reusable from them.
-/

open Finset

namespace Round17CAPair

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The joint agreement set of the pair `(f₁, f₂)` with the codeword pair `(g₁, g₂)`. -/
def jointAgreeSet (f₁ f₂ g₁ g₂ : ι → F) : Finset ι :=
  Finset.univ.filter (fun x => f₁ x = g₁ x ∧ f₂ x = g₂ x)

/-- Inclusion–exclusion in agreement-count form: two sets of size `≥ a` in an `n`-point domain
intersect in `≥ 2a − n` points. -/
theorem inter_card_ge {S S' : Finset ι} {a : ℕ}
    (hS : a ≤ S.card) (hS' : a ≤ S'.card) :
    2 * a ≤ (S ∩ S').card + Fintype.card ι := by
  have hunion : (S ∪ S').card ≤ Fintype.card ι := by
    calc (S ∪ S').card ≤ (Finset.univ : Finset ι).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card ι := Finset.card_univ
  have hie : (S ∪ S').card + (S ∩ S').card = S.card + S'.card :=
    Finset.card_union_add_card_inter S S'
  omega

/-! ## The engine: two bad γ's solve for the codeword pair -/

/-- **Pair extraction.** If `γ ≠ γ'`, `f₁ + γ·f₂ = c` on `S`, and `f₁ + γ'·f₂ = c'` on `S'`, then
with `g₂ := (γ − γ')⁻¹ • (c − c')` and `g₁ := c − γ • g₂`, the pair `(f₁, f₂)` agrees with
`(g₁, g₂)` on all of `S ∩ S'`. -/
theorem pair_of_two_bad {f₁ f₂ c c' : ι → F} {γ γ' : F} (hne : γ ≠ γ')
    {S S' : Finset ι}
    (hS : ∀ x ∈ S, f₁ x + γ * f₂ x = c x)
    (hS' : ∀ x ∈ S', f₁ x + γ' * f₂ x = c' x) :
    S ∩ S' ⊆ jointAgreeSet f₁ f₂
      (c - γ • ((γ - γ')⁻¹ • (c - c'))) ((γ - γ')⁻¹ • (c - c')) := by
  intro x hx
  obtain ⟨hxS, hxS'⟩ := Finset.mem_inter.mp hx
  have h1 := hS x hxS
  have h2 := hS' x hxS'
  have hsub : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
  rw [jointAgreeSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · -- f₁ x = c x − γ·(γ−γ')⁻¹·(c x − c' x)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (-γ') * h1 + γ * h2
  · -- f₂ x = (γ−γ')⁻¹·(c x − c' x)
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linear_combination h1 - h2

/-! ## The bad set and the two theorems -/

variable [Fintype F]

/-- The agreement set of `f₁ + γ·f₂` with the codeword `c`. -/
def lineAgree (f₁ f₂ : ι → F) (γ : F) (c : ι → F) : Finset ι :=
  Finset.univ.filter (fun x => f₁ x + γ * f₂ x = c x)

/-- `γ` is **`a`-bad** for `(f₁, f₂)` w.r.t. the code `C` if `f₁ + γ·f₂` agrees with some codeword
on at least `a` points. -/
def badSet (C : Finset (ι → F)) (f₁ f₂ : ι → F) (a : ℕ) : Finset F :=
  Finset.univ.filter (fun γ => ∃ c ∈ C, a ≤ (lineAgree f₁ f₂ γ c).card)

/-- The closure hypothesis: `C` is closed under the two-term linear combinations the pair
extraction produces (any `F`-linear code satisfies this). -/
def PairClosed (C : Finset (ι → F)) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, ∀ γ γ' : F, γ ≠ γ' →
    ((γ - γ')⁻¹ • (c - c') ∈ C ∧ c - γ • ((γ - γ')⁻¹ • (c - c')) ∈ C)

/-- **Theorem A — RVW13 half-threshold uniqueness (= ePrint 2026/858 Thm 5).** If every codeword
pair has joint agreement `≤ J` with `(f₁, f₂)` and the half-threshold condition
`J + n < 2a` holds, then at most one `γ` is `a`-bad. -/
theorem bad_card_le_one (C : Finset (ι → F)) (hC : PairClosed C) (f₁ f₂ : ι → F) {a J : ℕ}
    (hjoint : ∀ g₁ ∈ C, ∀ g₂ ∈ C, (jointAgreeSet f₁ f₂ g₁ g₂).card ≤ J)
    (hhalf : J + Fintype.card ι < 2 * a) :
    (badSet C f₁ f₂ a).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  by_contra hne
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hγ hγ'
  obtain ⟨c, hc, hac⟩ := hγ
  obtain ⟨c', hc', hac'⟩ := hγ'
  -- pair extraction on the two agreement sets
  have hsubset := pair_of_two_bad hne
    (S := lineAgree f₁ f₂ γ c) (S' := lineAgree f₁ f₂ γ' c')
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  obtain ⟨hg₂, hg₁⟩ := hC c hc c' hc' γ γ' hne
  -- the intersection is large …
  have hinter := inter_card_ge hac hac'
  -- … but the joint agreement is small.
  have hsmall : ((lineAgree f₁ f₂ γ c) ∩ (lineAgree f₁ f₂ γ' c')).card ≤ J :=
    le_trans (Finset.card_le_card hsubset) (hjoint _ hg₁ _ hg₂)
  omega

/-- **Theorem B — the equal-threshold `C(n, k+1)` ceiling (= ePrint 2026/858 Thm 7).** If every
codeword pair has joint agreement `≤ k` with `(f₁, f₂)`, then the set of `(k+1)`-bad `γ` injects
into the `(k+1)`-subsets of the domain:

  `#(badSet C f₁ f₂ (k+1)) ≤ C(n, k+1)`.

**Field-independent.** Each bad `γ` owns a `(k+1)`-subset of its agreement set; two bad `γ`s
sharing the same `(k+1)`-subset would, by pair extraction, produce a codeword pair jointly
agreeing with `(f₁, f₂)` on `k+1 > k` points. -/
theorem bad_card_le_choose (C : Finset (ι → F)) (hC : PairClosed C) (f₁ f₂ : ι → F) {k : ℕ}
    (hjoint : ∀ g₁ ∈ C, ∀ g₂ ∈ C, (jointAgreeSet f₁ f₂ g₁ g₂).card ≤ k) :
    (badSet C f₁ f₂ (k + 1)).card ≤ (Fintype.card ι).choose (k + 1) := by
  classical
  -- choose, for each bad γ, a witness codeword and a (k+1)-subset of the agreement set.
  have hwit : ∀ γ ∈ badSet C f₁ f₂ (k + 1),
      ∃ c ∈ C, ∃ A : Finset ι, A ⊆ lineAgree f₁ f₂ γ c ∧ A.card = k + 1 := by
    intro γ hγ
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    obtain ⟨c, hc, hac⟩ := hγ
    obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hac
    exact ⟨c, hc, A, hA, hAcard⟩
  choose cw hcw A hA hAcard using hwit
  -- the assignment γ ↦ A γ is injective into the (k+1)-subsets of univ.
  have hmaps : ∀ γ (hγ : γ ∈ badSet C f₁ f₂ (k + 1)),
      A γ hγ ∈ (Finset.univ : Finset ι).powersetCard (k + 1) := by
    intro γ hγ
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hAcard γ hγ⟩
  -- count via the attach-image
  have hinj : ∀ γ (hγ : γ ∈ badSet C f₁ f₂ (k + 1)) γ' (hγ' : γ' ∈ badSet C f₁ f₂ (k + 1)),
      A γ hγ = A γ' hγ' → γ = γ' := by
    intro γ hγ γ' hγ' hAA
    by_contra hne
    -- both line equations hold on the COMMON set A γ hγ
    have hOnA : ∀ x ∈ A γ hγ, f₁ x + γ * f₂ x = cw γ hγ x := by
      intro x hx
      have := hA γ hγ hx
      exact (Finset.mem_filter.mp this).2
    have hOnA' : ∀ x ∈ A γ hγ, f₁ x + γ' * f₂ x = cw γ' hγ' x := by
      intro x hx
      rw [hAA] at hx
      have := hA γ' hγ' hx
      exact (Finset.mem_filter.mp this).2
    -- pair extraction over S = S' = A γ hγ
    have hsubset := pair_of_two_bad hne
      (S := A γ hγ) (S' := A γ hγ) hOnA hOnA'
    rw [Finset.inter_self] at hsubset
    obtain ⟨hg₂, hg₁⟩ := hC (cw γ hγ) (hcw γ hγ) (cw γ' hγ') (hcw γ' hγ') γ γ' hne
    have hsmall : (A γ hγ).card ≤ k :=
      le_trans (Finset.card_le_card hsubset) (hjoint _ hg₁ _ hg₂)
    rw [hAcard γ hγ] at hsmall
    omega
  -- conclude by injecting the attached bad set
  have := Finset.card_le_card_of_injOn
    (f := fun γp : {γ // γ ∈ badSet C f₁ f₂ (k + 1)} => A γp.1 γp.2)
    (s := (badSet C f₁ f₂ (k + 1)).attach)
    (t := (Finset.univ : Finset ι).powersetCard (k + 1))
    (fun γp _ => hmaps γp.1 γp.2)
    (fun γp _ γp' _ h => Subtype.ext (hinj γp.1 γp.2 γp'.1 γp'.2 h))
  rw [Finset.card_attach] at this
  calc (badSet C f₁ f₂ (k + 1)).card
      ≤ ((Finset.univ : Finset ι).powersetCard (k + 1)).card := this
    _ = (Fintype.card ι).choose (k + 1) := by
        rw [Finset.card_powersetCard, Finset.card_univ]

/-! ## Non-vacuity -/

/-- `5` is prime (for the `ZMod 5` field instance). -/
instance primeFact_CAPairExtractionEngine_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Non-vacuity of the closure hypothesis: the zero code over `ZMod 5` is `PairClosed`, so both
theorems instantiate with concrete inhabitants. -/
theorem pairClosed_zero_code :
    PairClosed (({fun _ => (0 : ZMod 5)} : Finset (Fin 3 → ZMod 5))) := by
  intro c hc c' hc' γ γ' _
  simp only [Finset.mem_singleton] at hc hc'
  subst hc; subst hc'
  constructor
  · rw [Finset.mem_singleton]
    funext x
    simp
  · rw [Finset.mem_singleton]
    funext x
    simp

end Round17CAPair

#print axioms Round17CAPair.pair_of_two_bad
#print axioms Round17CAPair.bad_card_le_one
#print axioms Round17CAPair.bad_card_le_choose
#print axioms Round17CAPair.pairClosed_zero_code
