/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.LinearizedSupport

/-!
# BKR06 subspace polynomials are `q`-linearized (the `hlin` residual, discharged)

This file discharges the single named residual `hlin` of the tight BKR06 list-size
chain (`ArkLib.ToMathlib.LinearizedSupport`): for every finite `𝔽_q`-subspace
`W ⊆ K` (with `q = #𝔽`), the subspace polynomial
`L_W = ∏_{w ∈ W} (X − C w)` is **`q`-linearized**, i.e. its support is contained in
the `q`-power exponents `{q^0, q^1, …}` (`Polynomial.IsQLinearized`).

The proof is BKR06's **flag recursion** (Prop 3.2):

> for `x ∉ W₀` and `W = W₀ ⊔ 𝔽·x`,
> `L_W = L_{W₀}^q − C((L_{W₀}.eval x)^{q−1}) · L_{W₀}`.

The *support side* of this recursion (`p ↦ p^q − C c · p` preserves `q`-linearizedness)
is already proven in `LinearizedSupport` as `Polynomial.IsQLinearized.pow_sub_C_mul`.
What this file adds is:

* `BKR06.subspacePoly_eval_smul` — **`𝔽`-homogeneity** of the evaluation map
  `eval (c • y) L_W = algebraMap 𝔽 K c * eval y L_W` (`c ∈ 𝔽`), by reindexing the
  defining product `w ↦ c • w` and `c^{q^{dim W}} = c` (`FiniteField.pow_card_pow`).
* `BKR06.subspacePoly_flag_recursion` — the **flag recursion identity** itself, proven
  by a monic-degree + divisibility (root-set) argument: both sides are monic of degree
  `q^{dim W₀ + 1}`, and every element of `W = W₀ ⊔ 𝔽·x` is a (simple) root of the RHS
  (using `𝔽`-homogeneity + additivity), so `L_W ∣ RHS` and they coincide.
* `BKR06.subspacePoly_isQLinearized` — the **main theorem**, by `Finset.induction` on a
  generating set of `W` (`W = span 𝔽 ↑(subFinset W)`), applying the recursion +
  `IsQLinearized.pow_sub_C_mul` at each insertion step (base: `L_⊥ = X`).
* `BKR06.subspacePoly_isQLinearized_card` — the exact `hlin` shape (`IsQLinearized (#𝔽)`).

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

The setting requires `[Algebra 𝔽 K]` (a genuine subfield action `c • z = algebraMap c * z`,
`Algebra.smul_def`), which holds in the BKR06 application `𝔽 = 𝔽_q ⊆ K = 𝔽_{q^m}`; the
bare `[Module 𝔽 K]` of the upstream signature is *not* enough for linearizedness (an
arbitrary module action need not be field multiplication).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

open Polynomial BigOperators Finset

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-- A submodule of a finite vector space is finite. -/
local instance instFintypeSubmoduleLinearized (W : Submodule F K) : Fintype W :=
  Fintype.ofFinite W

/-! ## `𝔽`-homogeneity of the subspace-polynomial evaluation map -/

/-- **`𝔽`-homogeneity.**  For `c ∈ 𝔽` and `y ∈ K`,
`L_W(c • y) = algebraMap 𝔽 K c * L_W(y)`.

Proof: reindex the defining product `L_W(c•y) = ∏_{w ∈ W} (c•y − w)` along the bijection
`w ↦ c • w` of the `𝔽`-subspace `W` (valid since `c ≠ 0`), giving
`∏_{w} (c•y − c•w) = ∏_{w} c•(y − w) = (algebraMap c)^{|W|} · L_W(y)`; and
`(algebraMap c)^{|W|} = (algebraMap c)^{q^{dim W}} = algebraMap c` by `c^q = c` in `𝔽`. -/
theorem subspacePoly_eval_smul (W : Submodule F K) (c : F) (y : K) :
    (subspacePoly (subFinset W)).eval (c • y)
      = (algebraMap F K c) * (subspacePoly (subFinset W)).eval y := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, map_zero, zero_mul]
    exact subspacePoly_eval_zero _ (by simp [W.zero_mem])
  · have hcdef : ∀ (a : K), c • a = algebraMap F K c * a := fun a => Algebra.smul_def c a
    have hcard : (subFinset W).card = Fintype.card F ^ (Module.finrank F W) := by
      rw [subFinset]; simp only [Set.toFinset_card]
      exact Module.card_eq_pow_finrank (K := F) (V := W)
    unfold subspacePoly
    rw [eval_prod, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    -- reindex ℓ = c • ℓ' over the bijection ℓ' ↦ c • ℓ' of subFinset W
    have key : ∏ ℓ ∈ subFinset W, (c • y - ℓ)
        = ∏ ℓ' ∈ subFinset W, (c • y - c • ℓ') := by
      refine (Finset.prod_nbij' (fun ℓ' => c • ℓ') (fun ℓ => c⁻¹ • ℓ) ?_ ?_ ?_ ?_ ?_).symm
      · intro ℓ' hℓ'; rw [mem_subFinset] at hℓ' ⊢; exact W.smul_mem _ hℓ'
      · intro ℓ hℓ; rw [mem_subFinset] at hℓ ⊢; exact W.smul_mem _ hℓ
      · intro ℓ' _; simp only; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      · intro ℓ _; simp only; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      · intro ℓ' _; rfl
    rw [key]
    have hfac : ∀ ℓ' : K, c • y - c • ℓ' = algebraMap F K c * (y - ℓ') := by
      intro ℓ'; rw [← smul_sub, hcdef]
    simp only [hfac]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, ← map_pow,
        FiniteField.pow_card_pow]

/-! ## The flag recursion identity -/

/-- The recursion right-hand side `L_{W₀}^q − C(a^{q−1}) · L_{W₀}` is **monic** of degree
`q · |W₀|`, where `a := L_{W₀}.eval x`, `q := #𝔽`.  The subtracted term has strictly
smaller degree (`|W₀| < q·|W₀|`), so the leading `q·|W₀|` term comes from `L_{W₀}^q`. -/
theorem subspacePoly_recursion_monic
    (W₀ : Submodule F K) (hq : 2 ≤ Fintype.card F) (x : K) :
    ((subspacePoly (subFinset W₀)) ^ (Fintype.card F)
      - C (((subspacePoly (subFinset W₀)).eval x) ^ (Fintype.card F - 1))
        * subspacePoly (subFinset W₀)).Monic := by
  set f := subspacePoly (subFinset W₀) with hf
  set q := Fintype.card F with hqdef
  have hfmon : f.Monic := subspacePoly_monic _
  have hfdeg : f.natDegree = (subFinset W₀).card := subspacePoly_natDegree _
  have hcard_pos : 0 < (subFinset W₀).card :=
    Finset.card_pos.2 ⟨0, by rw [mem_subFinset]; exact W₀.zero_mem⟩
  have hsub_deg :
      (C ((f.eval x) ^ (q - 1)) * f).degree < (f ^ q).degree := by
    apply Polynomial.degree_lt_degree
    rw [hfmon.natDegree_pow]
    calc (C ((f.eval x) ^ (q - 1)) * f).natDegree
        ≤ f.natDegree := le_trans Polynomial.natDegree_mul_le (by rw [natDegree_C, zero_add])
      _ < q * f.natDegree := by
          have hfdpos : 0 < f.natDegree := by rw [hfdeg]; exact hcard_pos
          nlinarith [hfdpos, hq]
  exact (hfmon.pow q).sub_of_left hsub_deg

/-- Degree of the recursion RHS equals `q · |W₀|`. -/
theorem subspacePoly_recursion_natDegree
    (W₀ : Submodule F K) (hq : 2 ≤ Fintype.card F) (x : K) :
    ((subspacePoly (subFinset W₀)) ^ (Fintype.card F)
      - C (((subspacePoly (subFinset W₀)).eval x) ^ (Fintype.card F - 1))
        * subspacePoly (subFinset W₀)).natDegree
      = Fintype.card F * (subFinset W₀).card := by
  set f := subspacePoly (subFinset W₀) with hf
  set q := Fintype.card F with hqdef
  have hfmon : f.Monic := subspacePoly_monic _
  have hfdeg : f.natDegree = (subFinset W₀).card := subspacePoly_natDegree _
  have hcard_pos : 0 < (subFinset W₀).card :=
    Finset.card_pos.2 ⟨0, by rw [mem_subFinset]; exact W₀.zero_mem⟩
  have hsub_nat :
      (C ((f.eval x) ^ (q - 1)) * f).natDegree < (f ^ q).natDegree := by
    rw [hfmon.natDegree_pow]
    calc (C ((f.eval x) ^ (q - 1)) * f).natDegree
        ≤ f.natDegree := le_trans Polynomial.natDegree_mul_le (by rw [natDegree_C, zero_add])
      _ < q * f.natDegree := by
          have hfdpos : 0 < f.natDegree := by rw [hfdeg]; exact hcard_pos
          nlinarith [hfdpos, hq]
  -- natDegree of the difference = natDegree of the dominant power term
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hsub_nat]
  rw [hfmon.natDegree_pow, hfdeg]

/-- **Cardinality of the doubled subspace.**  When `x ∉ W₀`,
`|W₀ ⊔ 𝔽·x| = q · |W₀|` (the new dimension is `dim W₀ + 1`). -/
theorem subFinset_sup_span_singleton_card
    (W₀ : Submodule F K) (x : K) (hx : x ∉ W₀) :
    (subFinset ((W₀ ⊔ Submodule.span F {x} : Submodule F K))).card
      = Fintype.card F * (subFinset W₀).card := by
  have hdisj : Disjoint W₀ (Submodule.span F {x}) :=
    Submodule.disjoint_span_singleton_of_notMem hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ W₀.zero_mem)
  set W : Submodule F K := W₀ ⊔ Submodule.span F {x} with hW
  have hfr : Module.finrank F W = Module.finrank F W₀ + 1 := by
    have aux := Submodule.finrank_sup_add_finrank_inf_eq W₀ (Submodule.span F {x})
    rw [hdisj.eq_bot, finrank_bot, add_zero, finrank_span_singleton hx0, ← hW] at aux
    omega
  have hcardW : (subFinset W).card = Fintype.card F ^ (Module.finrank F W) := by
    rw [subFinset]; simp only [Set.toFinset_card]
    exact Module.card_eq_pow_finrank (K := F) (V := W)
  have hcardW0 : (subFinset W₀).card = Fintype.card F ^ (Module.finrank F W₀) := by
    rw [subFinset]; simp only [Set.toFinset_card]
    exact Module.card_eq_pow_finrank (K := F) (V := W₀)
  rw [hcardW, hfr, hcardW0, pow_succ]; ring

/-- Every element of `W₀ ⊔ 𝔽·x` is a **root** of the recursion RHS.

For `y = w + c•x` (`w ∈ W₀`, `c ∈ 𝔽`): by additivity and `𝔽`-homogeneity
`L_{W₀}(y) = algebraMap c · a` (`a := L_{W₀}.eval x`), so the RHS evaluates to
`(algebraMap c · a)^q − a^{q−1}·(algebraMap c · a) = ((algebraMap c)^q − algebraMap c)·a^q = 0`
since `(algebraMap c)^q = algebraMap c`. -/
theorem subspacePoly_recursion_isRoot
    (W₀ : Submodule F K) (x : K) {y : K}
    (hy : y ∈ (W₀ ⊔ Submodule.span F {x} : Submodule F K)) :
    ((subspacePoly (subFinset W₀)) ^ (Fintype.card F)
      - C (((subspacePoly (subFinset W₀)).eval x) ^ (Fintype.card F - 1))
        * subspacePoly (subFinset W₀)).eval y = 0 := by
  set f := subspacePoly (subFinset W₀) with hf
  set q := Fintype.card F with hqdef
  set a := f.eval x with ha_def
  rw [Submodule.mem_sup] at hy
  obtain ⟨w, hw, z, hz, rfl⟩ := hy
  rw [Submodule.mem_span_singleton] at hz
  obtain ⟨c, rfl⟩ := hz
  have hadd : f.eval (w + c • x) = f.eval w + f.eval (c • x) :=
    subspacePoly_eval_add_submodule W₀ w (c • x)
  have hw0 : f.eval w = 0 := (subspacePoly_isRoot_iff _ w).2 (by rw [mem_subFinset]; exact hw)
  have hcx : f.eval (c • x) = algebraMap F K c * a := subspacePoly_eval_smul W₀ c x
  have hfy : f.eval (w + c • x) = algebraMap F K c * a := by rw [hadd, hw0, hcx, zero_add]
  simp only [eval_sub, eval_pow, eval_mul, eval_C]
  rw [hfy]
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hcpow : (algebraMap F K c) ^ q = algebraMap F K c := by
    rw [← map_pow, FiniteField.pow_card]
  rw [mul_pow, hcpow]
  have ha : a ^ (q - 1) * a = a ^ q := by rw [← pow_succ]; congr 1; omega
  rw [show a ^ (q - 1) * (algebraMap F K c * a) = algebraMap F K c * (a ^ (q - 1) * a) by ring,
      ha, sub_self]

/-- **BKR06 flag recursion identity (Prop 3.2).**  For `x ∉ W₀`,
`L_{W₀ ⊔ 𝔽·x} = L_{W₀}^q − C((L_{W₀}.eval x)^{q−1}) · L_{W₀}`  (`q = #𝔽`).

Both sides are monic of degree `q·|W₀| = |W₀ ⊔ 𝔽·x|`; the LHS is the split product over the
`|W₀ ⊔ 𝔽·x|` distinct roots `W₀ ⊔ 𝔽·x`, all of which are roots of the RHS
(`subspacePoly_recursion_isRoot`), so `LHS ∣ RHS`.  Two monic polynomials of equal degree,
one dividing the other, are equal. -/
theorem subspacePoly_flag_recursion
    (W₀ : Submodule F K) (hq : 2 ≤ Fintype.card F) (x : K) (hx : x ∉ W₀) :
    subspacePoly (subFinset (W₀ ⊔ Submodule.span F {x} : Submodule F K))
      = (subspacePoly (subFinset W₀)) ^ (Fintype.card F)
        - C (((subspacePoly (subFinset W₀)).eval x) ^ (Fintype.card F - 1))
          * subspacePoly (subFinset W₀) := by
  classical
  set W : Submodule F K := W₀ ⊔ Submodule.span F {x} with hW
  set RHS := (subspacePoly (subFinset W₀)) ^ (Fintype.card F)
      - C (((subspacePoly (subFinset W₀)).eval x) ^ (Fintype.card F - 1))
        * subspacePoly (subFinset W₀) with hRHS
  have hRHS_mon : RHS.Monic := subspacePoly_recursion_monic W₀ hq x
  have hRHS_ne : RHS ≠ 0 := hRHS_mon.ne_zero
  have hLHS_mon : (subspacePoly (subFinset W)).Monic := subspacePoly_monic _
  -- degrees agree: |W| = q·|W₀| = RHS.natDegree
  have hLHS_deg : (subspacePoly (subFinset W)).natDegree
      = Fintype.card F * (subFinset W₀).card := by
    rw [subspacePoly_natDegree, hW, subFinset_sup_span_singleton_card W₀ x hx]
  have hRHS_deg : RHS.natDegree = Fintype.card F * (subFinset W₀).card :=
    subspacePoly_recursion_natDegree W₀ hq x
  -- divisibility LHS ∣ RHS via root multiset containment
  have hdvd : subspacePoly (subFinset W) ∣ RHS := by
    -- L_W = (subFinset W).val.map (X - C ·) |>.prod
    have hLeq : subspacePoly (subFinset W)
        = ((subFinset W).val.map (fun a => X - C a)).prod := by
      unfold subspacePoly; rw [Finset.prod_eq_multiset_prod]
    rw [hLeq, Multiset.prod_X_sub_C_dvd_iff_le_roots hRHS_ne]
    -- (subFinset W).val ≤ RHS.roots: nodup + each element a root
    rw [Multiset.le_iff_count]
    intro r
    by_cases hmem : r ∈ subFinset W
    · -- r ∈ subFinset W: count in val is 1, count in roots ≥ 1
      have hrootmem : r ∈ (W₀ ⊔ Submodule.span F {x} : Submodule F K) := by
        rw [mem_subFinset, hW] at hmem; exact hmem
      rw [Multiset.count_eq_one_of_mem (subFinset W).nodup hmem]
      -- 1 ≤ count r RHS.roots ⇐ r ∈ RHS.roots (IsRoot ∧ RHS ≠ 0)
      have hr : r ∈ RHS.roots := by
        rw [Polynomial.mem_roots hRHS_ne]
        exact subspacePoly_recursion_isRoot W₀ x hrootmem
      exact Multiset.one_le_count_iff_mem.2 hr
    · -- r ∉ subFinset W: count in val is 0
      rw [Multiset.count_eq_zero_of_notMem hmem]; exact Nat.zero_le _
  -- monic of equal degree + dvd ⟹ equal
  refine Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hdvd ?_ ?_
  · rw [hLHS_deg, hRHS_deg]
  · rw [hLHS_mon.leadingCoeff, hRHS_mon.leadingCoeff]

end BKR06

/-! ## The main `q`-linearizedness theorem -/

namespace BKR06

open Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

local instance instFintypeSubmoduleLin2 (W : Submodule F K) : Fintype W :=
  Fintype.ofFinite W

/-- `subFinset ⊥ = {0}`. -/
@[simp] theorem subFinset_bot : subFinset (⊥ : Submodule F K) = {0} := by
  ext x; simp only [mem_subFinset, Submodule.mem_bot, Finset.mem_singleton]

/-- `L_⊥ = X` (the base case of the flag induction). -/
theorem subspacePoly_subFinset_bot :
    subspacePoly (subFinset (⊥ : Submodule F K)) = X := by
  rw [subFinset_bot]; unfold subspacePoly; simp

/-- **Linearizedness along a generating set.**  For any finset `s ⊆ K`, the subspace
polynomial of the `𝔽`-span of `s` is `(#𝔽)`-linearized.  By `Finset.induction` on `s`:
base `span ∅ = ⊥`, `L_⊥ = X` (`isQLinearized_X`); step inserts `a` — either `a ∈ span s`
(span unchanged, IH) or `a ∉ span s`, where `span (insert a s) = span s ⊔ 𝔽·a` and the flag
recursion + `IsQLinearized.pow_sub_C_mul` give the result. -/
theorem subspacePoly_isQLinearized_span
    (p : ℕ) [ExpChar K p] (t : ℕ) (hpt : Fintype.card F = p ^ t)
    (s : Finset K) :
    IsQLinearized (Fintype.card F)
      (subspacePoly (subFinset (Submodule.span F (s : Set K)))) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hspan : Submodule.span F ((∅ : Finset K) : Set K) = (⊥ : Submodule F K) := by
        simp
      rw [hspan, subspacePoly_subFinset_bot]
      exact isQLinearized_X _
  | @insert a s ha ih =>
      rw [Finset.coe_insert, Submodule.span_insert]
      by_cases hain : a ∈ Submodule.span F (s : Set K)
      · -- a already in span: span (insert a s) = span s
        have hsup : (F ∙ a) ⊔ Submodule.span F (s : Set K)
            = Submodule.span F (s : Set K) := by
          rw [sup_eq_right, Submodule.span_singleton_le_iff_mem]; exact hain
        rw [hsup]; exact ih
      · -- a ∉ span s: flag step with W₀ = span s, x = a
        set W₀ : Submodule F K := Submodule.span F (s : Set K) with hW₀
        have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
        -- span (insert a s) = W₀ ⊔ 𝔽·a  (commute the sup to match the recursion shape)
        have hcomm : (F ∙ a) ⊔ W₀ = (W₀ ⊔ Submodule.span F {a} : Submodule F K) :=
          sup_comm _ _
        rw [hcomm, subspacePoly_flag_recursion W₀ hq a hain]
        -- IsQLinearized (p^t) (L_{W₀}^{p^t} − C(...)·L_{W₀})  via pow_sub_C_mul
        have ihpt : IsQLinearized (p ^ t) (subspacePoly (subFinset W₀)) := by
          rw [← hpt]; exact ih
        -- rewrite every `#𝔽` to `p^t` (predicate arg + the polynomial's exponents)
        rw [hpt]
        exact ihpt.pow_sub_C_mul
          (((subspacePoly (subFinset W₀)).eval a) ^ (p ^ t - 1))

/-- **Main theorem (`hlin` residual, discharged).**  For *every* finite `𝔽_q`-subspace
`W ⊆ K` (`q = #𝔽`), the subspace polynomial `L_W` is `q`-linearized: its support is
contained in the `q`-power exponents `{q^0, q^1, …}`.

Reduces to `subspacePoly_isQLinearized_span` via `W = span 𝔽 ↑(subFinset W)`
(`Submodule.span_eq`), obtaining the `(p, t)` with `#𝔽 = p^t` and `[ExpChar K p]` from
the finite field `K`. -/
theorem subspacePoly_isQLinearized (W : Submodule F K) :
    IsQLinearized (Fintype.card F) (subspacePoly (subFinset W)) := by
  classical
  -- the prime p = char K, with #F = p^t and [ExpChar K p]
  obtain ⟨p, hcharK, n, hpprime, _hcardK⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hpprime⟩
  haveI : CharP K p := hcharK
  haveI : ExpChar K p := ExpChar.prime hpprime
  -- F also has characteristic p (pulled back along the injective algebraMap from K)
  haveI hcharF : CharP F p :=
    (algebraMap F K).charP (FaithfulSMul.algebraMap_injective F K) p
  obtain ⟨t, _, ht⟩ := FiniteField.card (K := F) p
  -- W = span 𝔽 of its own carrier finset
  have hWspan : Submodule.span F ((subFinset W : Finset K) : Set K) = W := by
    have : ((subFinset W : Finset K) : Set K) = (W : Set K) := by
      ext x; simp [mem_subFinset]
    rw [this, Submodule.span_eq]
  have := subspacePoly_isQLinearized_span (F := F) (K := K) p (t : ℕ) ht (subFinset W)
  rwa [hWspan] at this

/-- **`hlin` shape.**  The exact uniform-over-dimension residual consumed by
`LinearizedSupport.bkr06_tight_pigeonhole_family_card` / `bkr06_tight_family_hfamily`:
for every dimension-`v` subspace, `L_W` is `q`-linearized.  (Holds for *all* `W`, with no
dimension restriction; the dimension hypothesis is simply not needed.) -/
theorem subspacePoly_isQLinearized_of_finrank
    (q : ℕ) (hqcard : Fintype.card F = q) (v : ℕ)
    (W : Submodule F K) (_hW : Module.finrank F W = v) :
    IsQLinearized q (subspacePoly (subFinset W)) := by
  rw [← hqcard]; exact subspacePoly_isQLinearized W

end BKR06

/-! ## End-to-end: the unconditional tight BKR06 family

Composing the discharged `hlin` (`subspacePoly_isQLinearized_of_finrank`) with the proven
tight pigeonhole + `hexp` pipeline `BKR06.bkr06_tight_family_hfamily`
(`LinearizedSupport`), the linearizedness hypothesis is *eliminated*: the only remaining
input is the documented parameter identity `hparam` (`m·u − v² = (α−β²)·log q`) and the
nonneg side condition `hexp_nonneg`. -/

namespace BKR06

open Polynomial

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-- **BKR06 tight family, `hlin` eliminated.**  Identical conclusion to
`bkr06_tight_family_hfamily`, but with the linearizedness residual `hlin` *discharged* by
`subspacePoly_isQLinearized_of_finrank` (valid for the genuine subfield action
`[Algebra F K]`).  The only non-proven inputs left are the parameter identity `hparam` and
the nonnegativity side condition `hexp_nonneg`. -/
theorem bkr06_tight_family_hfamily_unconditional
    (α β : ℝ)
    (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u)
    (hparam : ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) = (α - β ^ 2) * Real.log q) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j, subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))
          ∈ Polynomial.degreeLT K (q ^ u + 1)) ∧
      (q : ℝ) ^ ((α - β ^ 2) * Real.log q) ≤ (Fintype.card ι : ℝ) :=
  bkr06_tight_family_hfamily α β q hq hqcard v u hv huv hexp_nonneg
    (fun W hW => subspacePoly_isQLinearized_of_finrank q hqcard v W hW)
    hparam

/-! ## Side-condition discharge: explicit cutoff index and explicit `α`

`bkr06_tight_family_hfamily_unconditional` still carries two parameter side conditions —
the nonnegativity `hexp_nonneg : v² ≤ m·u` (together with `huv : u ≤ v`) and the
parameter identity `hparam : (m·u − v² : ℝ) = (α − β²)·log q`.  Both are pure
bookkeeping, discharged here:

* `bkr06CutoffIndex` — the explicit cutoff `u := ⌈v²/m⌉` (BKR06's `k = q^u` window
  convention); `le_mul_bkr06CutoffIndex` and `bkr06CutoffIndex_le` prove `v² ≤ m·u`
  and `u ≤ v` from `v ≤ m` alone.
* `bkr06_tight_family_hfamily_param_free` — `hparam` *eliminated*: instantiating
  `α := (m·u − v²)/log q` (with `β = 0`; `log q ≠ 0` from `2 ≤ q`) makes the identity
  true by algebra, and the conclusion is restated with the concrete tight exponent
  `q^{m·u − v²}`.
* `bkr06_tight_family_hfamily_alpha_of_beta` — the α/β-form connector: for *any*
  `β`, the explicit `α := β² + (m·u − v²)/log q` satisfies `hparam` by algebra, and
  the conclusion keeps the bare statement's `q^{(α−β²)·log q}` exponent shape.
* `bkr06_tight_family_explicit` — everything discharged at once: the only remaining
  inputs are `2 ≤ q`, `#F = q`, and `v ≤ m`.
-/

/-- **Explicit BKR06 cutoff index** `u := ⌈v²/m⌉` (computed as `(v² + m − 1)/m`).
This is the smallest cutoff making the tight exponent `m·u − v²` nonnegative; the two
side conditions `v² ≤ m·u` (`le_mul_bkr06CutoffIndex`) and `u ≤ v`
(`bkr06CutoffIndex_le`, from `v ≤ m`) then hold automatically. -/
def bkr06CutoffIndex (m v : ℕ) : ℕ := (v ^ 2 + m - 1) / m

/-- The explicit cutoff makes the tight exponent nonnegative: `v² ≤ m·⌈v²/m⌉`. -/
lemma le_mul_bkr06CutoffIndex (m v : ℕ) (hm : 0 < m) :
    v ^ 2 ≤ m * bkr06CutoffIndex m v := by
  unfold bkr06CutoffIndex
  have hdm := Nat.div_add_mod (v ^ 2 + m - 1) m
  have hmod : (v ^ 2 + m - 1) % m < m := Nat.mod_lt _ hm
  -- abstract the nonlinear atoms so the remaining problem is linear arithmetic
  set p := m * ((v ^ 2 + m - 1) / m) with hp
  set r := (v ^ 2 + m - 1) % m with hr
  set s := v ^ 2 with hs
  omega

/-- The explicit cutoff stays below the dimension: `⌈v²/m⌉ ≤ v` whenever `v ≤ m`. -/
lemma bkr06CutoffIndex_le (m v : ℕ) (hm : 0 < m) (hvm : v ≤ m) :
    bkr06CutoffIndex m v ≤ v := by
  unfold bkr06CutoffIndex
  have hvv : v ^ 2 ≤ v * m := by
    have h := Nat.mul_le_mul_left v hvm
    simpa [pow_two] using h
  have hlt : v ^ 2 + m - 1 < (v + 1) * m := by
    have hexp : (v + 1) * m = v * m + m := by ring
    rw [hexp]
    set s := v ^ 2 with hs
    set t := v * m with ht
    omega
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hm).mpr hlt)

/-- The extension degree is positive: `K` is a nontrivial finite `F`-module, so
`#K = q^m ≥ 2` forces `m ≥ 1`. -/
lemma finrank_pos : 0 < Module.finrank F K := by
  rcases Nat.eq_zero_or_pos (Module.finrank F K) with h0 | h
  · exfalso
    have hcard := Module.card_eq_pow_finrank (K := F) (V := K)
    rw [h0, pow_zero] at hcard
    exact absurd hcard Fintype.one_lt_card.ne'
  · exact h

/-- **Tight family, parameter-free form (`hparam` eliminated).**  Identical family
conclusion to `bkr06_tight_family_hfamily_unconditional`, with the size bound stated
at the concrete tight exponent `q^{m·u − v²}`.  The parameter identity is discharged
internally by instantiating `α := (m·u − v²)/log q`, `β := 0` (`log q ≠ 0` from
`2 ≤ q`); no `α`/`β` hypothesis remains. -/
theorem bkr06_tight_family_hfamily_param_free
    (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j, subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))
          ∈ Polynomial.degreeLT K (q ^ u + 1)) ∧
      (q : ℝ) ^ ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) ≤ (Fintype.card ι : ℝ) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hq
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  obtain ⟨ι, hF, hD, 𝓛, hFL, h1, h2, h3, h4⟩ :=
    bkr06_tight_family_hfamily_unconditional
      (α := ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) / Real.log q) (β := 0)
      q hq hqcard v u hv huv hexp_nonneg (by
        field_simp [hlogq]
        ring)
  refine ⟨ι, hF, hD, 𝓛, hFL, h1, h2, h3, ?_⟩
  have hexp : (((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) / Real.log q - 0 ^ 2)
      * Real.log q = (Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2 := by
    field_simp [hlogq]
    ring
  rwa [hexp] at h4

/-- **α/β-form connector (`hparam` discharged at explicit `α`).**  For *any* `β : ℝ`,
the explicit `α := β² + (m·u − v²)/log q` satisfies the parameter identity by algebra,
so the tight-family conclusion holds in the bare statement's `q^{(α−β²)·log q}`
exponent form with no parameter hypothesis.  (This is the exact `α`/`β` bookkeeping
BKR06 performs under `v ≈ β·m` and the `k = q^u` cutoff convention.) -/
theorem bkr06_tight_family_hfamily_alpha_of_beta
    (β : ℝ) (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j, subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))
          ∈ Polynomial.degreeLT K (q ^ u + 1)) ∧
      (q : ℝ) ^ (((β ^ 2 + ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) / Real.log q)
          - β ^ 2) * Real.log q) ≤ (Fintype.card ι : ℝ) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hq
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  exact bkr06_tight_family_hfamily_unconditional
    (α := β ^ 2 + ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) / Real.log q) (β := β)
    q hq hqcard v u hv huv hexp_nonneg (by
      field_simp [hlogq]
      ring)

/-- **Fully explicit tight family: all side conditions discharged.**  At the explicit
cutoff `u := bkr06CutoffIndex m v = ⌈v²/m⌉`, the only remaining inputs are `2 ≤ q`,
`#F = q`, and the dimension range `v ≤ m`; the conclusion carries the concrete tight
exponent `q^{m·u − v²}`. -/
theorem bkr06_tight_family_explicit
    (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v : ℕ) (hv : v ≤ Module.finrank F K) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j, subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))
          ∈ Polynomial.degreeLT K
              (q ^ (bkr06CutoffIndex (Module.finrank F K) v) + 1)) ∧
      (q : ℝ) ^ ((Module.finrank F K : ℝ) * (bkr06CutoffIndex (Module.finrank F K) v)
          - (v : ℝ) ^ 2) ≤ (Fintype.card ι : ℝ) :=
  bkr06_tight_family_hfamily_param_free q hq hqcard v _ hv
    (bkr06CutoffIndex_le _ _ (finrank_pos (F := F) (K := K)) hv)
    (le_mul_bkr06CutoffIndex _ _ (finrank_pos (F := F) (K := K)))

end BKR06
