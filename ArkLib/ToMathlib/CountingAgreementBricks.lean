/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Counting / polynomial-agreement / hypercube bricks

WHIR #113, Fiat-Shamir #116, sumcheck #13/#114.

* `card_filter_forall_pi` — the count of length-`s` tuples whose every coordinate satisfies a
  predicate `Q` is `(#Q)^s` (WHIR out-of-domain / FS union-bound counting, #113/#116).
* `card_filter_exists_not_pi` — the complementary exact count of tuples with at least one bad
  coordinate, `|β|^s - (#Q)^s`.
* `uniform_event_mass` — the uniform finite event probability as `#E / #α`.
* `Polynomial.card_eval_agreement_le_of_natDegree_lt` — two distinct polynomials of degree `< N`
  agree on at most `N-1` field points (the counting/Schwartz–Zippel dual used in collision-count
  arguments, #113/#116).
* `Polynomial.card_eval_disagreement_ge_of_natDegree_lt` — the complementary lower bound on
  disagreement points.
* `Polynomial.card_filter_forall_isRoot_le` — for a nonzero polynomial of degree `< N`, at most
  `(N-1)^s` length-`s` tuples are all roots.
* `Polynomial.card_filter_exists_not_isRoot_ge` — the complementary lower bound on length-`s`
  tuples with at least one non-root coordinate.
* `Polynomial.card_filter_forall_isRoot_le_of_natDegree_le` /
  `Polynomial.card_filter_exists_not_isRoot_ge_of_natDegree_le` — direct `D^s` count bounds
  from a degree bound `natDegree ≤ D`.
* `Polynomial.card_filter_forall_eval_eq_le_of_natDegree_lt` — two distinct degree-`< N`
  polynomials agree on every coordinate of at most `(N-1)^s` length-`s` tuples.
* `Polynomial.card_filter_exists_eval_ne_ge_of_natDegree_lt` — the complementary lower bound on
  length-`s` tuples with at least one coordinate of disagreement.
* `Polynomial.card_filter_forall_eval_eq_le_of_sub_natDegree_le` /
  `Polynomial.card_filter_exists_eval_ne_ge_of_sub_natDegree_le` — direct `D^s` count bounds
  from a degree bound `(p - q).natDegree ≤ D`.
* `Polynomial.card_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le` /
  `Polynomial.card_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le` — direct `D^s` count
  bounds for one polynomial hitting or missing a fixed field value.
* `Polynomial.card_filter_forall_eval_eq_const_le_of_natDegree_le` /
  `Polynomial.card_filter_exists_eval_ne_const_ge_of_natDegree_le` — fixed-value count wrappers
  when callers have the simpler bound `p.natDegree ≤ D`.
* `Polynomial.card_filter_forall_eval_eq_const_le_of_ne_C_natDegree_le` /
  `Polynomial.card_filter_exists_eval_ne_const_ge_of_ne_C_natDegree_le` — fixed-value count
  wrappers when callers express nonconstancy as `p ≠ C a`.
* `Polynomial.prob_filter_forall_isRoot_le` /
  `Polynomial.prob_filter_exists_not_isRoot_ge` — uniform-tuple probability wrappers for the
  one-polynomial root and non-root counting bounds.
* `Polynomial.prob_filter_forall_isRoot_le_of_natDegree_le` /
  `Polynomial.prob_filter_exists_not_isRoot_ge_of_natDegree_le` — the direct degree-bound
  probability wrappers for the same root/non-root events.
* `Polynomial.prob_filter_forall_eval_eq_le_of_natDegree_lt` /
  `Polynomial.prob_filter_exists_eval_ne_ge_of_natDegree_lt` — uniform-tuple probability wrappers
  for the agreement and disagreement counting bounds.
* `Polynomial.prob_filter_forall_eval_eq_le_of_sub_natDegree_le` /
  `Polynomial.prob_filter_exists_eval_ne_ge_of_sub_natDegree_le` — the direct degree-bound
  probability wrappers for coordinatewise agreement/disagreement.
* `Polynomial.prob_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le` /
  `Polynomial.prob_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le` — the corresponding
  fixed-value probability wrappers.
* `Polynomial.prob_filter_forall_eval_eq_const_le_of_natDegree_le` /
  `Polynomial.prob_filter_exists_eval_ne_const_ge_of_natDegree_le` — fixed-value probability
  wrappers from a direct degree bound on `p`.
* `Polynomial.prob_filter_forall_eval_eq_const_le_of_ne_C_natDegree_le` /
  `Polynomial.prob_filter_exists_eval_ne_const_ge_of_ne_C_natDegree_le` — fixed-value
  probability wrappers from `p ≠ C a` and a direct degree bound on `p`.
* `Finset.sum_boolCube_prod_factor_eq_prod_sum` — the boolean-hypercube identity
  `∑_{x∈{0,1}^σ} ∏ᵢ (xᵢ=0 ? aᵢ : bᵢ) = ∏ᵢ (aᵢ + bᵢ)` underlying multilinear-extension sumcheck
  folding (#13/#114).
-/

open Finset Polynomial
open scoped ENNReal

/-- Count of length-`s` tuples whose every coordinate satisfies `Q` equals `(#Q)^s`. -/
theorem card_filter_forall_pi {β : Type*} [Fintype β] [DecidableEq β] (s : ℕ)
    (Q : β → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i))).card
      = (Finset.univ.filter Q).card ^ s := by
  have h : (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i)))
      = Fintype.piFinset (fun _ : Fin s => Finset.univ.filter Q) := by
    ext r; simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]; simp

/-- Count of length-`s` tuples with at least one coordinate outside `Q`. -/
theorem card_filter_exists_not_pi {β : Type*} [Fintype β] [DecidableEq β] (s : ℕ)
    (Q : β → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun r : Fin s → β => ∃ i, ¬ Q (r i))).card
      = Fintype.card β ^ s - (Finset.univ.filter Q).card ^ s := by
  have hgood := card_filter_forall_pi (β := β) s Q
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s → β))) (p := fun r => ∀ i, Q (r i))
  have hbad_filter :
      (Finset.univ.filter (fun r : Fin s → β => ¬ ∀ i, Q (r i)))
        = Finset.univ.filter (fun r : Fin s → β => ∃ i, ¬ Q (r i)) := by
    ext r
    simp
  have hcard_fun : Fintype.card (Fin s → β) = Fintype.card β ^ s := by
    simp
  have hcard_univ : (Finset.univ : Finset (Fin s → β)).card = Fintype.card β ^ s := by
    rw [Finset.card_univ, hcard_fun]
  rw [hbad_filter] at hsplit
  rw [hgood, hcard_univ] at hsplit
  omega

/-- The mass of a finite event under the uniform distribution is its cardinality divided by the
sample-space cardinality. -/
theorem uniform_event_mass {α : Type*} [Fintype α] [Nonempty α] (E : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure (E : Set α)
      = (E.card : ℝ≥0∞) / Fintype.card α := by
  classical
  rw [PMF.toOuterMeasure_apply_finset]
  have hval : ∀ a ∈ E, (PMF.uniformOfFintype α) a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    intro a _
    exact PMF.uniformOfFintype_apply a
  rw [Finset.sum_congr rfl hval]
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.div_eq_inv_mul]
  ring

namespace Polynomial

/-- Two distinct polynomials of degree `< N` agree on at most `N-1` field points. -/
theorem card_eval_agreement_le_of_natDegree_lt {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {N : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N) (hq : q.natDegree < N) :
    (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card ≤ N - 1 := by
  have hr : p - q ≠ 0 := sub_ne_zero_of_ne hpq
  have hdeg : (p - q).natDegree < N := (natDegree_sub_le p q).trans_lt (max_lt hp hq)
  have hsub : (Finset.univ.filter (fun x : F => p.eval x = q.eval x)) ⊆ (p - q).roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hr, Polynomial.IsRoot.def,
      Polynomial.eval_sub, sub_eq_zero]
    exact hx
  calc (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := Polynomial.card_roots' _
    _ ≤ N - 1 := by omega

/-- Two distinct polynomials of degree `< N` disagree on at least `|F| - (N-1)` field points. -/
theorem card_eval_disagreement_ge_of_natDegree_lt {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {N : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N)
    (hq : q.natDegree < N) :
    Fintype.card F - (N - 1) ≤
      (Finset.univ.filter (fun x : F => p.eval x ≠ q.eval x)).card := by
  have hagree :=
    Polynomial.card_eval_agreement_le_of_natDegree_lt (F := F) (N := N) (p := p) (q := q)
      hpq hp hq
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset F)) (p := fun x : F => p.eval x = q.eval x)
  have hdisagree_filter :
      (Finset.univ.filter (fun x : F => ¬ p.eval x = q.eval x))
        = Finset.univ.filter (fun x : F => p.eval x ≠ q.eval x) := by
    ext x
    simp
  have hcard : (Finset.univ : Finset F).card = Fintype.card F := by
    simp
  rw [hdisagree_filter, hcard] at hsplit
  omega

/-- If `p` is nonzero of degree `< N`, then at most `(N-1)^s` length-`s` tuples
are made entirely of roots of `p`. -/
theorem card_filter_forall_isRoot_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {N s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree < N) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.IsRoot (r i))).card ≤
      (N - 1) ^ s := by
  classical
  have hroot_card :
      (Finset.univ.filter (fun x : F => p.IsRoot x)).card ≤ N - 1 := by
    have hsub : (Finset.univ.filter (fun x : F => p.IsRoot x)) ⊆ p.roots.toFinset := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      exact hx
    calc (Finset.univ.filter (fun x : F => p.IsRoot x)).card
        ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' _
      _ ≤ N - 1 := by omega
  rw [card_filter_forall_pi (β := F) s (fun x : F => p.IsRoot x)]
  exact Nat.pow_le_pow_left hroot_card s

/-- If `p` is nonzero of degree `< N`, then at least `|F|^s - (N-1)^s` length-`s`
tuples have some non-root coordinate. -/
theorem card_filter_exists_not_isRoot_ge {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {N s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree < N) :
    Fintype.card F ^ s - (N - 1) ^ s ≤
      (Finset.univ.filter (fun r : Fin s → F => ∃ i, ¬ p.IsRoot (r i))).card := by
  have hroot :=
    Polynomial.card_filter_forall_isRoot_le (F := F) (N := N) (s := s) (p := p) hp0 hp
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s → F)))
      (p := fun r : Fin s → F => ∀ i, p.IsRoot (r i))
  have hbad_filter :
      (Finset.univ.filter (fun r : Fin s → F => ¬ ∀ i, p.IsRoot (r i)))
        = Finset.univ.filter (fun r : Fin s → F => ∃ i, ¬ p.IsRoot (r i)) := by
    ext r
    simp
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcard_univ : (Finset.univ : Finset (Fin s → F)).card = Fintype.card F ^ s := by
    rw [Finset.card_univ, hcard_fun]
  rw [hbad_filter, hcard_univ] at hsplit
  omega

/-- Direct degree-bound version of `card_filter_forall_isRoot_le`. -/
theorem card_filter_forall_isRoot_le_of_natDegree_le {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {D s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree ≤ D) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.IsRoot (r i))).card ≤ D ^ s := by
  have hlt : p.natDegree < D + 1 := by omega
  simpa using
    Polynomial.card_filter_forall_isRoot_le (F := F) (N := D + 1) (s := s) (p := p)
      hp0 hlt

/-- Direct degree-bound version of `card_filter_exists_not_isRoot_ge`. -/
theorem card_filter_exists_not_isRoot_ge_of_natDegree_le {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {D s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree ≤ D) :
    Fintype.card F ^ s - D ^ s ≤
      (Finset.univ.filter (fun r : Fin s → F => ∃ i, ¬ p.IsRoot (r i))).card := by
  have hlt : p.natDegree < D + 1 := by omega
  simpa using
    Polynomial.card_filter_exists_not_isRoot_ge (F := F) (N := D + 1) (s := s) (p := p)
      hp0 hlt

/-- Two distinct polynomials of degree `< N` agree on every coordinate of at most `(N-1)^s`
length-`s` tuples. -/
theorem card_filter_forall_eval_eq_le_of_natDegree_lt {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {N s : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N)
    (hq : q.natDegree < N) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i))).card ≤
      (N - 1) ^ s := by
  have hagree :=
    Polynomial.card_eval_agreement_le_of_natDegree_lt (F := F) (N := N) (p := p) (q := q)
      hpq hp hq
  rw [card_filter_forall_pi (β := F) s (fun x : F => p.eval x = q.eval x)]
  exact Nat.pow_le_pow_left hagree s

/-- Two distinct polynomials of degree `< N` disagree on at least one coordinate of at least
`|F|^s - (N-1)^s` length-`s` tuples. -/
theorem card_filter_exists_eval_ne_ge_of_natDegree_lt {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {N s : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N)
    (hq : q.natDegree < N) :
    Fintype.card F ^ s - (N - 1) ^ s ≤
      (Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ q.eval (r i))).card := by
  have hagree :=
    Polynomial.card_filter_forall_eval_eq_le_of_natDegree_lt (F := F) (N := N) (s := s)
      (p := p) (q := q) hpq hp hq
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s → F)))
      (p := fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i))
  have hbad_filter :
      (Finset.univ.filter (fun r : Fin s → F => ¬ ∀ i, p.eval (r i) = q.eval (r i)))
        = Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ q.eval (r i)) := by
    ext r
    simp
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcard_univ : (Finset.univ : Finset (Fin s → F)).card = Fintype.card F ^ s := by
    rw [Finset.card_univ, hcard_fun]
  rw [hbad_filter, hcard_univ] at hsplit
  omega

/-- If `p - q` has degree at most `D`, then at most `D^s` tuples agree coordinatewise. -/
theorem card_filter_forall_eval_eq_le_of_sub_natDegree_le {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {D s : ℕ} {p q : F[X]} (hpq : p ≠ q) (hdeg : (p - q).natDegree ≤ D) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i))).card ≤
      D ^ s := by
  have hsub0 : p - q ≠ 0 := sub_ne_zero_of_ne hpq
  have hroots :
      (Finset.univ.filter (fun r : Fin s → F => ∀ i, (p - q).IsRoot (r i))).card ≤
        D ^ s :=
    Polynomial.card_filter_forall_isRoot_le_of_natDegree_le
      (F := F) (D := D) (s := s) (p := p - q) hsub0 hdeg
  have hsubset :
      Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i)) ⊆
        Finset.univ.filter (fun r : Fin s → F => ∀ i, (p - q).IsRoot (r i)) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    intro i
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero]
    exact hr i
  exact (Finset.card_le_card hsubset).trans hroots

/-- Complementary disagreement count from a direct degree bound on `p - q`. -/
theorem card_filter_exists_eval_ne_ge_of_sub_natDegree_le {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {D s : ℕ} {p q : F[X]} (hpq : p ≠ q) (hdeg : (p - q).natDegree ≤ D) :
    Fintype.card F ^ s - D ^ s ≤
      (Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ q.eval (r i))).card := by
  have hagree :=
    Polynomial.card_filter_forall_eval_eq_le_of_sub_natDegree_le
      (F := F) (D := D) (s := s) (p := p) (q := q) hpq hdeg
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s → F)))
      (p := fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i))
  have hbad_filter :
      (Finset.univ.filter (fun r : Fin s → F => ¬ ∀ i, p.eval (r i) = q.eval (r i)))
        = Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ q.eval (r i)) := by
    ext r
    simp
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcard_univ : (Finset.univ : Finset (Fin s → F)).card = Fintype.card F ^ s := by
    rw [Finset.card_univ, hcard_fun]
  rw [hbad_filter, hcard_univ] at hsplit
  omega

/-- If `p - C a` has degree at most `D`, then at most `D^s` tuples evaluate to `a`
at every coordinate. -/
theorem card_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hdeg : (p - C a).natDegree ≤ D) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = a)).card ≤
      D ^ s := by
  have hroots :
      (Finset.univ.filter (fun r : Fin s → F => ∀ i, (p - C a).IsRoot (r i))).card ≤
        D ^ s :=
    Polynomial.card_filter_forall_isRoot_le_of_natDegree_le
      (F := F) (D := D) (s := s) (p := p - C a) hp0 hdeg
  have hsubset :
      Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = a) ⊆
        Finset.univ.filter (fun r : Fin s → F => ∀ i, (p - C a).IsRoot (r i)) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    intro i
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero]
    exact hr i
  exact (Finset.card_le_card hsubset).trans hroots

/-- Complementary count from a direct degree bound on `p - C a`. -/
theorem card_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hdeg : (p - C a).natDegree ≤ D) :
    Fintype.card F ^ s - D ^ s ≤
      (Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ a)).card := by
  have hagree :=
    Polynomial.card_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le
      (F := F) (D := D) (s := s) (p := p) (a := a) hp0 hdeg
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s → F)))
      (p := fun r : Fin s → F => ∀ i, p.eval (r i) = a)
  have hbad_filter :
      (Finset.univ.filter (fun r : Fin s → F => ¬ ∀ i, p.eval (r i) = a))
        = Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ a) := by
    ext r
    simp
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcard_univ : (Finset.univ : Finset (Fin s → F)).card = Fintype.card F ^ s := by
    rw [Finset.card_univ, hcard_fun]
  rw [hbad_filter, hcard_univ] at hsplit
  omega

/-- Fixed-value count from a direct degree bound on `p`. This is the same wrapper as
`card_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le`, with `(p - C a).natDegree ≤ D`
derived for callers from `p.natDegree ≤ D`. -/
theorem card_filter_forall_eval_eq_const_le_of_natDegree_le {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hp : p.natDegree ≤ D) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = a)).card ≤
      D ^ s := by
  have hC : (C a : F[X]).natDegree ≤ D := by
    simp
  have hdeg : (p - C a).natDegree ≤ D :=
    (natDegree_sub_le p (C a)).trans (max_le hp hC)
  exact card_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) hp0 hdeg

/-- Complementary fixed-value count from a direct degree bound on `p`. -/
theorem card_filter_exists_eval_ne_const_ge_of_natDegree_le {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hp : p.natDegree ≤ D) :
    Fintype.card F ^ s - D ^ s ≤
      (Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ a)).card := by
  have hC : (C a : F[X]).natDegree ≤ D := by
    simp
  have hdeg : (p - C a).natDegree ≤ D :=
    (natDegree_sub_le p (C a)).trans (max_le hp hC)
  exact card_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) hp0 hdeg

/-- Fixed-value count from `p ≠ C a` and a direct degree bound on `p`. -/
theorem card_filter_forall_eval_eq_const_le_of_ne_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {D s : ℕ} {p : F[X]} {a : F}
    (hpC : p ≠ C a) (hp : p.natDegree ≤ D) :
    (Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = a)).card ≤
      D ^ s := by
  exact card_filter_forall_eval_eq_const_le_of_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) (sub_ne_zero_of_ne hpC) hp

/-- Complementary fixed-value count from `p ≠ C a` and a direct degree bound on `p`. -/
theorem card_filter_exists_eval_ne_const_ge_of_ne_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {D s : ℕ} {p : F[X]} {a : F}
    (hpC : p ≠ C a) (hp : p.natDegree ≤ D) :
    Fintype.card F ^ s - D ^ s ≤
      (Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ a)).card := by
  exact card_filter_exists_eval_ne_const_ge_of_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) (sub_ne_zero_of_ne hpC) hp

/-- Uniform-tuple probability upper bound for all sampled coordinates being roots of a nonzero
degree-`< N` polynomial. -/
theorem prob_filter_forall_isRoot_le {F : Type*} [Field F] [Fintype F] [Nonempty F]
    {N s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree < N) :
    (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
        {r : Fin s → F | ∀ i, p.IsRoot (r i)}
      ≤ (((N - 1) ^ s : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ s := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∀ i, p.IsRoot (r i))
  have hset :
      {r : Fin s → F | ∀ i, p.IsRoot (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : E.card ≤ (N - 1) ^ s :=
    _root_.Polynomial.card_filter_forall_isRoot_le
      (F := F) (N := N) (s := s) (p := p) hp0 hp
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple root-event probability from a direct degree bound. -/
theorem prob_filter_forall_isRoot_le_of_natDegree_le {F : Type*} [Field F] [Fintype F]
    [Nonempty F] {D s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree ≤ D) :
    (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
        {r : Fin s → F | ∀ i, p.IsRoot (r i)}
      ≤ ((D ^ s : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ s := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∀ i, p.IsRoot (r i))
  have hset :
      {r : Fin s → F | ∀ i, p.IsRoot (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : E.card ≤ D ^ s :=
    _root_.Polynomial.card_filter_forall_isRoot_le_of_natDegree_le
      (F := F) (D := D) (s := s) (p := p) hp0 hp
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple probability lower bound for seeing at least one non-root coordinate of a
nonzero degree-`< N` polynomial. -/
theorem prob_filter_exists_not_isRoot_ge {F : Type*} [Field F] [Fintype F] [Nonempty F]
    {N s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree < N) :
    (((Fintype.card F ^ s - (N - 1) ^ s : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ^ s)
      ≤ (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
          {r : Fin s → F | ∃ i, ¬ p.IsRoot (r i)} := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∃ i, ¬ p.IsRoot (r i))
  have hset :
      {r : Fin s → F | ∃ i, ¬ p.IsRoot (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : Fintype.card F ^ s - (N - 1) ^ s ≤ E.card :=
    _root_.Polynomial.card_filter_exists_not_isRoot_ge
      (F := F) (N := N) (s := s) (p := p) hp0 hp
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple non-root probability lower bound from a direct degree bound. -/
theorem prob_filter_exists_not_isRoot_ge_of_natDegree_le {F : Type*} [Field F] [Fintype F]
    [Nonempty F] {D s : ℕ} {p : F[X]} (hp0 : p ≠ 0) (hp : p.natDegree ≤ D) :
    (((Fintype.card F ^ s - D ^ s : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ^ s)
      ≤ (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
          {r : Fin s → F | ∃ i, ¬ p.IsRoot (r i)} := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∃ i, ¬ p.IsRoot (r i))
  have hset :
      {r : Fin s → F | ∃ i, ¬ p.IsRoot (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : Fintype.card F ^ s - D ^ s ≤ E.card :=
    _root_.Polynomial.card_filter_exists_not_isRoot_ge_of_natDegree_le
      (F := F) (D := D) (s := s) (p := p) hp0 hp
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple probability upper bound for all-coordinate agreement of two distinct
degree-`< N` polynomials. -/
theorem prob_filter_forall_eval_eq_le_of_natDegree_lt {F : Type*} [Field F] [Fintype F]
    [Nonempty F] {N s : ℕ} {p q : F[X]} (hpq : p ≠ q)
    (hp : p.natDegree < N) (hq : q.natDegree < N) :
    (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
        {r : Fin s → F | ∀ i, p.eval (r i) = q.eval (r i)}
      ≤ (((N - 1) ^ s : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ s := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i))
  have hset :
      {r : Fin s → F | ∀ i, p.eval (r i) = q.eval (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : E.card ≤ (N - 1) ^ s :=
    _root_.Polynomial.card_filter_forall_eval_eq_le_of_natDegree_lt
      (F := F) (N := N) (s := s) (p := p) (q := q) hpq hp hq
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple coordinatewise agreement probability from a direct degree bound on `p - q`. -/
theorem prob_filter_forall_eval_eq_le_of_sub_natDegree_le {F : Type*} [Field F] [Fintype F]
    [Nonempty F] {D s : ℕ} {p q : F[X]} (hpq : p ≠ q) (hdeg : (p - q).natDegree ≤ D) :
    (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
        {r : Fin s → F | ∀ i, p.eval (r i) = q.eval (r i)}
      ≤ ((D ^ s : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ s := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = q.eval (r i))
  have hset :
      {r : Fin s → F | ∀ i, p.eval (r i) = q.eval (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : E.card ≤ D ^ s :=
    _root_.Polynomial.card_filter_forall_eval_eq_le_of_sub_natDegree_le
      (F := F) (D := D) (s := s) (p := p) (q := q) hpq hdeg
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple probability lower bound for seeing at least one disagreement between two
distinct degree-`< N` polynomials. -/
theorem prob_filter_exists_eval_ne_ge_of_natDegree_lt {F : Type*} [Field F] [Fintype F]
    [Nonempty F] {N s : ℕ} {p q : F[X]} (hpq : p ≠ q)
    (hp : p.natDegree < N) (hq : q.natDegree < N) :
    (((Fintype.card F ^ s - (N - 1) ^ s : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ^ s)
      ≤ (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
          {r : Fin s → F | ∃ i, p.eval (r i) ≠ q.eval (r i)} := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ q.eval (r i))
  have hset :
      {r : Fin s → F | ∃ i, p.eval (r i) ≠ q.eval (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : Fintype.card F ^ s - (N - 1) ^ s ≤ E.card :=
    _root_.Polynomial.card_filter_exists_eval_ne_ge_of_natDegree_lt
      (F := F) (N := N) (s := s) (p := p) (q := q) hpq hp hq
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple disagreement probability lower bound from a direct degree bound on `p - q`. -/
theorem prob_filter_exists_eval_ne_ge_of_sub_natDegree_le {F : Type*} [Field F] [Fintype F]
    [Nonempty F] {D s : ℕ} {p q : F[X]} (hpq : p ≠ q) (hdeg : (p - q).natDegree ≤ D) :
    (((Fintype.card F ^ s - D ^ s : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ^ s)
      ≤ (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
          {r : Fin s → F | ∃ i, p.eval (r i) ≠ q.eval (r i)} := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ q.eval (r i))
  have hset :
      {r : Fin s → F | ∃ i, p.eval (r i) ≠ q.eval (r i)} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : Fintype.card F ^ s - D ^ s ≤ E.card :=
    _root_.Polynomial.card_filter_exists_eval_ne_ge_of_sub_natDegree_le
      (F := F) (D := D) (s := s) (p := p) (q := q) hpq hdeg
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple fixed-value probability from a direct degree bound on `p - C a`. -/
theorem prob_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [Nonempty F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hdeg : (p - C a).natDegree ≤ D) :
    (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
        {r : Fin s → F | ∀ i, p.eval (r i) = a}
      ≤ ((D ^ s : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ s := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∀ i, p.eval (r i) = a)
  have hset :
      {r : Fin s → F | ∀ i, p.eval (r i) = a} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : E.card ≤ D ^ s :=
    _root_.Polynomial.card_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le
      (F := F) (D := D) (s := s) (p := p) (a := a) hp0 hdeg
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple non-fixed-value probability from a direct degree bound on `p - C a`. -/
theorem prob_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [Nonempty F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hdeg : (p - C a).natDegree ≤ D) :
    (((Fintype.card F ^ s - D ^ s : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ^ s)
      ≤ (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
          {r : Fin s → F | ∃ i, p.eval (r i) ≠ a} := by
  classical
  let E : Finset (Fin s → F) :=
    Finset.univ.filter (fun r : Fin s → F => ∃ i, p.eval (r i) ≠ a)
  have hset :
      {r : Fin s → F | ∃ i, p.eval (r i) ≠ a} = (E : Set (Fin s → F)) := by
    ext r
    simp [E]
  have hcard_fun : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcount : Fintype.card F ^ s - D ^ s ≤ E.card :=
    _root_.Polynomial.card_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le
      (F := F) (D := D) (s := s) (p := p) (a := a) hp0 hdeg
  rw [hset, _root_.uniform_event_mass, hcard_fun]
  rw [Nat.cast_pow]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

/-- Uniform-tuple fixed-value probability from a direct degree bound on `p`. -/
theorem prob_filter_forall_eval_eq_const_le_of_natDegree_le {F : Type*}
    [Field F] [Fintype F] [Nonempty F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hp : p.natDegree ≤ D) :
    (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
        {r : Fin s → F | ∀ i, p.eval (r i) = a}
      ≤ ((D ^ s : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ s := by
  have hC : (C a : F[X]).natDegree ≤ D := by
    simp
  have hdeg : (p - C a).natDegree ≤ D :=
    (natDegree_sub_le p (C a)).trans (max_le hp hC)
  exact prob_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) hp0 hdeg

/-- Uniform-tuple non-fixed-value probability from a direct degree bound on `p`. -/
theorem prob_filter_exists_eval_ne_const_ge_of_natDegree_le {F : Type*}
    [Field F] [Fintype F] [Nonempty F] {D s : ℕ} {p : F[X]} {a : F}
    (hp0 : p - C a ≠ 0) (hp : p.natDegree ≤ D) :
    (((Fintype.card F ^ s - D ^ s : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ^ s)
      ≤ (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
          {r : Fin s → F | ∃ i, p.eval (r i) ≠ a} := by
  have hC : (C a : F[X]).natDegree ≤ D := by
    simp
  have hdeg : (p - C a).natDegree ≤ D :=
    (natDegree_sub_le p (C a)).trans (max_le hp hC)
  exact prob_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) hp0 hdeg

/-- Uniform-tuple fixed-value probability from `p ≠ C a` and a direct degree bound on `p`. -/
theorem prob_filter_forall_eval_eq_const_le_of_ne_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [Nonempty F] {D s : ℕ} {p : F[X]} {a : F}
    (hpC : p ≠ C a) (hp : p.natDegree ≤ D) :
    (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
        {r : Fin s → F | ∀ i, p.eval (r i) = a}
      ≤ ((D ^ s : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ s := by
  exact prob_filter_forall_eval_eq_const_le_of_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) (sub_ne_zero_of_ne hpC) hp

/-- Uniform-tuple non-fixed-value probability from `p ≠ C a` and a direct degree bound on `p`. -/
theorem prob_filter_exists_eval_ne_const_ge_of_ne_C_natDegree_le {F : Type*}
    [Field F] [Fintype F] [Nonempty F] {D s : ℕ} {p : F[X]} {a : F}
    (hpC : p ≠ C a) (hp : p.natDegree ≤ D) :
    (((Fintype.card F ^ s - D ^ s : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ^ s)
      ≤ (PMF.uniformOfFintype (Fin s → F)).toOuterMeasure
          {r : Fin s → F | ∃ i, p.eval (r i) ≠ a} := by
  exact prob_filter_exists_eval_ne_const_ge_of_natDegree_le
    (F := F) (D := D) (s := s) (p := p) (a := a) (sub_ne_zero_of_ne hpC) hp

end Polynomial

namespace Finset

/-- Boolean-hypercube sum of per-coordinate two-way products factors as the product of sums. -/
theorem sum_boolCube_prod_factor_eq_prod_sum {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
    (a b : σ → R) :
    ∑ x : σ → Fin 2, ∏ i : σ, (if x i = 0 then a i else b i) = ∏ i : σ, (a i + b i) := by
  have key : (∏ i : σ, ∑ j : Fin 2, (if j = 0 then a i else b i))
      = ∑ x : σ → Fin 2, ∏ i : σ, (if x i = 0 then a i else b i) := by
    rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]
  rw [← key]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]; simp

end Finset

#print axioms card_filter_forall_pi
#print axioms card_filter_exists_not_pi
#print axioms uniform_event_mass
#print axioms Polynomial.card_eval_agreement_le_of_natDegree_lt
#print axioms Polynomial.card_eval_disagreement_ge_of_natDegree_lt
#print axioms Polynomial.card_filter_forall_isRoot_le
#print axioms Polynomial.card_filter_exists_not_isRoot_ge
#print axioms Polynomial.card_filter_forall_isRoot_le_of_natDegree_le
#print axioms Polynomial.card_filter_exists_not_isRoot_ge_of_natDegree_le
#print axioms Polynomial.card_filter_forall_eval_eq_le_of_natDegree_lt
#print axioms Polynomial.card_filter_exists_eval_ne_ge_of_natDegree_lt
#print axioms Polynomial.card_filter_forall_eval_eq_le_of_sub_natDegree_le
#print axioms Polynomial.card_filter_exists_eval_ne_ge_of_sub_natDegree_le
#print axioms Polynomial.card_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le
#print axioms Polynomial.card_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le
#print axioms Polynomial.card_filter_forall_eval_eq_const_le_of_natDegree_le
#print axioms Polynomial.card_filter_exists_eval_ne_const_ge_of_natDegree_le
#print axioms Polynomial.card_filter_forall_eval_eq_const_le_of_ne_C_natDegree_le
#print axioms Polynomial.card_filter_exists_eval_ne_const_ge_of_ne_C_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_forall_isRoot_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_exists_not_isRoot_ge
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_forall_isRoot_le_of_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_exists_not_isRoot_ge_of_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_forall_eval_eq_le_of_natDegree_lt
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_exists_eval_ne_ge_of_natDegree_lt
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_forall_eval_eq_le_of_sub_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_exists_eval_ne_ge_of_sub_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_forall_eval_eq_const_le_of_sub_C_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_exists_eval_ne_const_ge_of_sub_C_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_forall_eval_eq_const_le_of_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_exists_eval_ne_const_ge_of_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_forall_eval_eq_const_le_of_ne_C_natDegree_le
set_option linter.style.longLine false in
#print axioms Polynomial.prob_filter_exists_eval_ne_const_ge_of_ne_C_natDegree_le
#print axioms Finset.sum_boolCube_prod_factor_eq_prod_sum
