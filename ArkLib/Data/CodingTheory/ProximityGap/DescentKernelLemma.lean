/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Issue #232 — the Descent Kernel Lemma (Lemma K) and pattern rigidity, machine-checked

This file formalizes the **queued Lean bricks of the O13″/O14 descent program**
(see `DISPROOF_LOG.md`, entries O13–O14′): the converse-FRI even/odd descent writes a
degree-`< 2κ` candidate list element as `c(d) = e(d²) + d·f(d²)` with `deg e, deg f < κ`,
and its agreement pattern with a received word `w` on a `±`-paired smooth domain splits
per level-1 point `z = d²` into

* **both-sided** (`z ∈ B`): two linear constraints on `(e(z), f(z))`,
* **one-sided** (`z ∈ O₁`): one `σ`-twisted affine constraint `e(z) + σ_z·f(z) = w(σ_z)`
  where `σ_z` is the agreeing square root of `z`,
* none.

Main results (all characteristic-free):

* `glue` and its API: `glue e f = (expand F 2 e) + X * (expand F 2 f)` — the inverse of the
  even/odd split — with coefficient extraction, evaluation, degree bound, and injectivity.
* `kernel_rigidity` (**Lemma K**, DISPROOF_LOG O14): a pair `(e, f)` of degree-`< κ`
  polynomials satisfying the *homogeneous* twisted system `e(z) + r_z·f(z) = 0` on `≥ 2κ`
  points `z` with chosen square roots `r_z` is identically zero. The smooth-domain `d² = z`
  parametrization supplies **unconditional kernel rigidity** — the mechanism-level answer to
  "what randomness supplies that smoothness must replace".
* `solution_unique`: the inhomogeneous one-sided system has **at most one** solution once
  `|O| ≥ 2κ` — per-pattern solutions ≤ 1.
* `pattern_rigidity` (sharp weighted form): a full `(B, O₁, σ)` pattern with the *weighted*
  count `2·|B| + |O₁| ≥ 2κ` pins `(e, f)` uniquely. Since a beyond-rate list element at
  agreement `a` has `2·|B| + |O₁| = a ≥ k = 2κ`, **every list element is uniquely determined
  by its agreement pattern** — hence `ℓ(θ) = #(consistent patterns)`, and Conjecture D is
  purely inhomogeneous consistency-rarity (cyclotomic identity counting; C19's exhaustive
  4480 → 16 enumeration is the worked instance).
* `agreement_count` (Descent Lemma counting identity, O13″): on a `±`-paired domain,
  `#(agreements of c with w) = 2·|B| + |O₁|` — the overdetermination bookkeeping
  `constraints − unknowns ≥ a − 2κ` is then immediate.
* `both_agreement_iff` / `one_sided_agreement_iff`: the per-`z` trichotomy bridges between
  level-0 agreement of the glued polynomial and the level-1 constraint shapes.

Everything here is elementary degree counting — but it is the rigidity engine that makes the
descent program's reduction (`ℓ(θ)` = pattern count) rigorous, now machine-checked.
-/

namespace DescentKernel

open Polynomial Finset

/-! ## The glue map and its API -/

section GlueAPI

variable {F : Type*} [CommRing F]

/-- The glue of an even part `e` and an odd part `f`: the unique polynomial with
`(glue e f)(d) = e(d²) + d·f(d²)`. This inverts the FRI/WHIR even–odd split,
characteristic-free. -/
noncomputable def glue (e f : F[X]) : F[X] := expand F 2 e + X * expand F 2 f

@[simp]
lemma glue_eval (e f : F[X]) (d : F) :
    (glue e f).eval d = e.eval (d ^ 2) + d * f.eval (d ^ 2) := by
  simp [glue, expand_eval]

/-- `X * expand F 2 f` has no even coefficients. -/
lemma coeff_X_mul_expand_even (f : F[X]) (n : ℕ) :
    (X * expand F 2 f).coeff (2 * n) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h2n : 2 * n = (2 * n - 1) + 1 := by omega
    rw [h2n, coeff_X_mul, coeff_expand (by norm_num : 0 < 2)]
    have hnd : ¬ ((2 : ℕ) ∣ (2 * n - 1)) := by omega
    simp [hnd]

lemma glue_coeff_even (e f : F[X]) (n : ℕ) : (glue e f).coeff (2 * n) = e.coeff n := by
  simp only [glue, coeff_add]
  rw [coeff_expand_mul' (by norm_num : 0 < 2), coeff_X_mul_expand_even, add_zero]

lemma glue_coeff_odd (e f : F[X]) (n : ℕ) : (glue e f).coeff (2 * n + 1) = f.coeff n := by
  simp only [glue, coeff_add]
  rw [coeff_expand (by norm_num : 0 < 2)]
  have hnd : ¬ ((2 : ℕ) ∣ (2 * n + 1)) := by omega
  rw [if_neg hnd, coeff_X_mul, coeff_expand_mul' (by norm_num : 0 < 2), zero_add]

/-- The glue map is injective: a vanishing glue forces both parts to vanish.
(No characteristic assumption — the even and odd coefficient supports are disjoint.) -/
lemma eq_zero_of_glue_eq_zero {e f : F[X]} (h : glue e f = 0) : e = 0 ∧ f = 0 := by
  constructor <;> ext n
  · have hc := glue_coeff_even e f n
    rw [h, coeff_zero] at hc
    simpa using hc.symm
  · have hc := glue_coeff_odd e f n
    rw [h, coeff_zero] at hc
    simpa using hc.symm

/-- Degree bound: gluing degree-`< κ` parts gives degree `< 2κ`. -/
lemma glue_natDegree_lt {κ : ℕ} {e f : F[X]}
    (he : e.natDegree < κ) (hf : f.natDegree < κ) :
    (glue e f).natDegree < 2 * κ := by
  have hg : (glue e f).natDegree
      ≤ max (expand F 2 e).natDegree (X * expand F 2 f).natDegree :=
    natDegree_add_le _ _
  have h1 : (expand F 2 e).natDegree = e.natDegree * 2 := natDegree_expand 2 e
  have h2 : (X * expand F 2 f).natDegree ≤ 1 + f.natDegree * 2 := by
    calc (X * expand F 2 f).natDegree
        ≤ X.natDegree + (expand F 2 f).natDegree := natDegree_mul_le
      _ ≤ 1 + f.natDegree * 2 := by
          rw [natDegree_expand]
          have hX : (X : F[X]).natDegree ≤ 1 := natDegree_X_le
          omega
  rw [h1] at hg
  omega

/-- **Existence of the descent decomposition**: every polynomial of degree `< 2κ` is the
glue of an even part and an odd part of degree `< κ` — so the rigidity theorems below
apply to every candidate list element. (Uniqueness follows from
`eq_zero_of_glue_eq_zero` applied to a difference of decompositions.) -/
theorem exists_glue_decomposition {κ : ℕ} {c : F[X]}
    (hc : c.natDegree < 2 * κ) :
    ∃ e f : F[X], e.natDegree < κ ∧ f.natDegree < κ ∧ c = glue e f := by
  refine ⟨∑ j ∈ Finset.range κ, Polynomial.monomial j (c.coeff (2 * j)),
          ∑ j ∈ Finset.range κ, Polynomial.monomial j (c.coeff (2 * j + 1)), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun j hj =>
      le_trans (natDegree_monomial_le _) (by
        simp only [Finset.mem_range] at hj
        omega))
      (by omega : κ - 1 < κ)
  · exact lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun j hj =>
      le_trans (natDegree_monomial_le _) (by
        simp only [Finset.mem_range] at hj
        omega))
      (by omega : κ - 1 < κ)
  · ext n
    have hcoeff : ∀ (g : ℕ → F) (m : ℕ),
        (∑ j ∈ Finset.range κ, Polynomial.monomial j (g j)).coeff m
          = if m < κ then g m else 0 := by
      intro g m
      rw [Polynomial.finset_sum_coeff]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' (Finset.range κ) m g]
      simp [Finset.mem_range]
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hn : n = 2 * m := by omega
      rw [hn, glue_coeff_even, hcoeff]
      by_cases hmκ : m < κ
      · simp [hmκ]
      · simp only [hmκ, if_false]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
    · have hn : n = 2 * m + 1 := by omega
      rw [hn, glue_coeff_odd, hcoeff]
      by_cases hmκ : m < κ
      · simp [hmκ]
      · simp only [hmκ, if_false]
        exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Both-sided agreement of the glued polynomial at the pair `{d, -d}` is exactly the
two-constraint system on `(e(z), f(z))` at `z = d²`. -/
lemma both_agreement_iff (e f : F[X]) (w : F → F) {z d : F} (hd : d ^ 2 = z) :
    ((glue e f).eval d = w d ∧ (glue e f).eval (-d) = w (-d)) ↔
      (e.eval z + d * f.eval z = w d ∧ e.eval z - d * f.eval z = w (-d)) := by
  rw [glue_eval, glue_eval, neg_sq, hd]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linear_combination h2⟩

/-- One-sided agreement of the glued polynomial at a single chosen root `d` of `z` is
exactly one σ-twisted affine constraint on `(e(z), f(z))`. -/
lemma one_sided_agreement_iff (e f : F[X]) (w : F → F) {z d : F} (hd : d ^ 2 = z) :
    (glue e f).eval d = w d ↔ e.eval z + d * f.eval z = w d := by
  rw [glue_eval, hd]

end GlueAPI

/-! ## The Descent Lemma counting identity: agreement = `2|B| + |O₁|` -/

section Counting

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- Every element of the agreement pair `{y z, -y z}` squares to `z`. -/
lemma sq_of_mem_pair {y : F → F} {z x : F} (hy : (y z) ^ 2 = z)
    (hx : x ∈ ({y z, -y z} : Finset F)) : x ^ 2 = z := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hy
  · rw [Finset.mem_singleton.mp hx, neg_sq]
    exact hy

/-- **The descent agreement-count identity (O13″).** On a `±`-paired level-0 domain
(the fibers `{y z, -y z}` over level-1 points `z ∈ D₁`), the number of agreements of any
polynomial `c` with the received word `w` equals `2·|B| + |O₁|`, where `B` is the set of
both-sided level-1 points and `O₁` the set of exactly-one-sided ones.

Combined with `pattern_rigidity` this gives the overdetermination bookkeeping: a list
element of degree `< 2κ = k` at agreement `a = 2|B| + |O₁| ≥ k` is an `(a − k)`-fold
degeneracy, uniquely pinned by its pattern. -/
theorem agreement_count {D₁ : Finset F} {y : F → F} (w : F → F)
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hyne : ∀ z ∈ D₁, y z ≠ -y z)
    (c : F[X]) :
    ((D₁.biUnion fun z => ({y z, -y z} : Finset F)).filter
        (fun x => c.eval x = w x)).card
      = 2 * (D₁.filter fun z =>
            c.eval (y z) = w (y z) ∧ c.eval (-y z) = w (-y z)).card
        + (D₁.filter fun z =>
            ¬ (c.eval (y z) = w (y z) ↔ c.eval (-y z) = w (-y z))).card := by
  classical
  have hpairwise : ∀ z ∈ D₁, ∀ z' ∈ D₁, z ≠ z' →
      Disjoint (({y z, -y z} : Finset F).filter (fun x => c.eval x = w x))
               (({y z', -y z'} : Finset F).filter (fun x => c.eval x = w x)) := by
    intro z hz z' hz' hne
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hne (by rw [← sq_of_mem_pair (hy z hz) hx, sq_of_mem_pair (hy z' hz') hx'])
  rw [Finset.filter_biUnion, Finset.card_biUnion hpairwise]
  have hper : ∀ z ∈ D₁,
      ((({y z, -y z} : Finset F)).filter (fun x => c.eval x = w x)).card
        = 2 * (if c.eval (y z) = w (y z) ∧ c.eval (-y z) = w (-y z) then 1 else 0)
          + (if ¬ (c.eval (y z) = w (y z) ↔ c.eval (-y z) = w (-y z)) then 1 else 0) := by
    intro z hz
    rw [Finset.card_filter, Finset.sum_pair (hyne z hz)]
    by_cases h₁ : c.eval (y z) = w (y z) <;> by_cases h₂ : c.eval (-y z) = w (-y z) <;>
      simp [h₁, h₂]
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.card_filter, ← Finset.card_filter]

end Counting

/-! ## Lemma K and pattern rigidity -/

section Rigidity

variable {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]

/-- **Lemma K (the Descent Kernel Lemma).** A pair `(e, f)` of degree-`< κ` polynomials
satisfying the homogeneous σ-twisted system `e(z) + r_z · f(z) = 0` on at least `2κ` points
`z` admitting square roots `r_z` is identically zero.

Proof mechanism: substitute `z = r_z²` — the glued polynomial `g(d) = e(d²) + d·f(d²)` has
degree `< 2κ` but vanishes at the `≥ 2κ` distinct points `r_z`, hence `g = 0`, hence
`e = f = 0` by even/odd coefficient disjointness. The `d² = z` parametrization supplies
unconditional rigidity: no genericity assumption on the twist `r`. -/
theorem kernel_rigidity {κ : ℕ} {O : Finset F} {r : F → F}
    (hr : ∀ z ∈ O, (r z) ^ 2 = z)
    {e f : F[X]} (he : e.natDegree < κ) (hf : f.natDegree < κ)
    (hcard : 2 * κ ≤ O.card)
    (hvanish : ∀ z ∈ O, e.eval z + r z * f.eval z = 0) :
    e = 0 ∧ f = 0 := by
  apply eq_zero_of_glue_eq_zero
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (glue e f) (O.image r)
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [glue_eval, hr z hz]
    exact hvanish z hz
  · have hinj : Set.InjOn r ↑O := by
      intro z hz z' hz' hzz
      have hsq : (r z) ^ 2 = (r z') ^ 2 := by rw [hzz]
      rwa [hr z (Finset.mem_coe.mp hz), hr z' (Finset.mem_coe.mp hz')] at hsq
    rw [Finset.card_image_of_injOn hinj]
    exact lt_of_lt_of_le (glue_natDegree_lt he hf) hcard

/-- **Per-pattern solutions ≤ 1**: the inhomogeneous one-sided system
`e(z) + r_z · f(z) = w_z` on `≥ 2κ` twisted points has at most one degree-`< κ` solution
pair. Consequence (O14): in the overdetermined regime the list count equals the number of
consistent `(B, O, σ)` patterns. -/
theorem solution_unique {κ : ℕ} {O : Finset F} {r : F → F} {w : F → F}
    (hr : ∀ z ∈ O, (r z) ^ 2 = z) (hcard : 2 * κ ≤ O.card)
    {e₁ f₁ e₂ f₂ : F[X]}
    (he₁ : e₁.natDegree < κ) (hf₁ : f₁.natDegree < κ)
    (he₂ : e₂.natDegree < κ) (hf₂ : f₂.natDegree < κ)
    (h₁ : ∀ z ∈ O, e₁.eval z + r z * f₁.eval z = w z)
    (h₂ : ∀ z ∈ O, e₂.eval z + r z * f₂.eval z = w z) :
    e₁ = e₂ ∧ f₁ = f₂ := by
  have h := kernel_rigidity (e := e₁ - e₂) (f := f₁ - f₂) hr
    (lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt he₁ he₂))
    (lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hf₁ hf₂))
    hcard
    (fun z hz => by
      simp only [eval_sub]
      linear_combination h₁ z hz - h₂ z hz)
  exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2⟩

/-- **Pattern rigidity (sharp weighted form).** A full descent pattern — both-sided
constraints on `B` (two equations per point) and one-sided σ-twisted constraints on `O₁`
(one equation per point) — pins the pair `(e, f)` uniquely as soon as the *weighted*
constraint count satisfies `2·|B| + |O₁| ≥ 2κ`.

Since a list element at agreement `a` with the received word has exactly `2·|B| + |O₁| = a`
(see `agreement_count`), every beyond-rate (`a ≥ k = 2κ`) list element is uniquely
determined by its pattern: `ℓ(θ) = #(consistent patterns)`. This is the precise statement
making Conjecture D pure consistency-rarity. -/
theorem pattern_rigidity {κ : ℕ} {B O₁ : Finset F} (hBO : Disjoint B O₁)
    {y σ : F → F} {w : F → F}
    (hyB : ∀ z ∈ B, (y z) ^ 2 = z) (hyne : ∀ z ∈ B, y z ≠ -y z)
    (hσ : ∀ z ∈ O₁, (σ z) ^ 2 = z)
    {e₁ f₁ e₂ f₂ : F[X]}
    (he₁ : e₁.natDegree < κ) (hf₁ : f₁.natDegree < κ)
    (he₂ : e₂.natDegree < κ) (hf₂ : f₂.natDegree < κ)
    (hcard : 2 * κ ≤ 2 * B.card + O₁.card)
    (hB₁ : ∀ z ∈ B, e₁.eval z + y z * f₁.eval z = w (y z)
                  ∧ e₁.eval z - y z * f₁.eval z = w (-y z))
    (hB₂ : ∀ z ∈ B, e₂.eval z + y z * f₂.eval z = w (y z)
                  ∧ e₂.eval z - y z * f₂.eval z = w (-y z))
    (hO₁ : ∀ z ∈ O₁, e₁.eval z + σ z * f₁.eval z = w (σ z))
    (hO₂ : ∀ z ∈ O₁, e₂.eval z + σ z * f₂.eval z = w (σ z)) :
    e₁ = e₂ ∧ f₁ = f₂ := by
  set g : F[X] := glue (e₁ - e₂) (f₁ - f₂) with hgdef
  set S : Finset F := (B.biUnion fun z => ({y z, -y z} : Finset F)) ∪ O₁.image σ with hSdef
  -- g vanishes on all of S
  have hvan : ∀ x ∈ S, g.eval x = 0 := by
    intro x hx
    rw [hSdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨z, hz, hpair⟩ := Finset.mem_biUnion.mp hx
      have hsq : x ^ 2 = z := sq_of_mem_pair (hyB z hz) hpair
      rw [hgdef, glue_eval, hsq, eval_sub, eval_sub]
      rcases Finset.mem_insert.mp hpair with rfl | hone
      · linear_combination (hB₁ z hz).1 - (hB₂ z hz).1
      · obtain rfl := Finset.mem_singleton.mp hone
        linear_combination (hB₁ z hz).2 - (hB₂ z hz).2
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      rw [hgdef, glue_eval, hσ z hz, eval_sub, eval_sub]
      linear_combination hO₁ z hz - hO₂ z hz
  -- |S| = 2|B| + |O₁|
  have hdisjS : Disjoint (B.biUnion fun z => ({y z, -y z} : Finset F)) (O₁.image σ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨z, hz, hpair⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hx'
    have h1 : (σ z') ^ 2 = z := sq_of_mem_pair (hyB z hz) hpair
    have h2 : (σ z') ^ 2 = z' := hσ z' hz'
    have hzz : z = z' := by rw [← h1, h2]
    exact Finset.disjoint_left.mp hBO hz (hzz ▸ hz')
  have hpairwise : ∀ z ∈ B, ∀ z' ∈ B, z ≠ z' →
      Disjoint ({y z, -y z} : Finset F) ({y z', -y z'} : Finset F) := by
    intro z hz z' hz' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hne (by rw [← sq_of_mem_pair (hyB z hz) hx, sq_of_mem_pair (hyB z' hz') hx'])
  have hpaircard : ∀ z ∈ B, ({y z, -y z} : Finset F).card = 2 := by
    intro z hz
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact hyne z hz), Finset.card_singleton]
  have himg : (O₁.image σ).card = O₁.card := by
    apply Finset.card_image_of_injOn
    intro z hz z' hz' h
    rw [← hσ z (Finset.mem_coe.mp hz), h, hσ z' (Finset.mem_coe.mp hz')]
  have hcardS : S.card = 2 * B.card + O₁.card := by
    rw [hSdef, Finset.card_union_of_disjoint hdisjS, Finset.card_biUnion hpairwise,
        Finset.sum_congr rfl hpaircard, Finset.sum_const, smul_eq_mul, himg]
    ring
  -- root counting
  have hg0 : g = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g S hvan
    rw [hcardS]
    exact lt_of_lt_of_le
      (glue_natDegree_lt
        (lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt he₁ he₂))
        (lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hf₁ hf₂)))
      hcard
  have h := eq_zero_of_glue_eq_zero hg0
  exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2⟩

end Rigidity

end DescentKernel
