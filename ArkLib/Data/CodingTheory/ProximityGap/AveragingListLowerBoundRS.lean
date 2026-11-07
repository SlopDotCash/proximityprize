/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic

/-!
  Angle 4 — Averaging AGREEMENT FAMILIES (polynomial perturbations agreeing with a
  fixed word on `a` points).  This is NOT a fixed-word Reed–Solomon list lower
  bound: no degree-`< k` conclusion is proved (see "WHAT IS *NOT* PROVED").

  Ethereum Proximity Prize (ABF26 / ArkLib #232) attack support.

  ----------------------------------------------------------------------------
  WHAT THIS FILE PROVES (fully verified, kernel-checked, axiom-clean)
  ----------------------------------------------------------------------------

  Setup.  A finite field `F` (any `Field` + `Fintype`), an index type `ι`, an
  evaluation map `v : ι → F` that is INJECTIVE on a finite set of points
  `T : Finset ι` with `#T = n` (the smooth RS evaluation domain — `n` distinct
  points).  A "word" is a polynomial `g : F[X]`.

  The averaging construction.  For a subset `S ⊆ T`, set
      pS g v S  :=  g  -  C (g.coeff a) * nodal S v ,           a := #S,
  where `nodal S v = ∏_{i∈S} (X - C (v i))` is the Lagrange nodal polynomial.
  Because `nodal S v` vanishes at every node `v i`, `i ∈ S`, the perturbed word
  `pS g v S` AGREES WITH `g` at all `a` evaluation points of `S`.

  We prove, as genuine theorems (Mathlib `Polynomial` / Lagrange / nodal):

   (1) `pS_eval_eq_of_mem`        — `pS g v S` agrees with `g` on every node of `S`.
   (2) `nodal_injOn_powersetCard` — `S ↦ nodal S v` is injective on the `a`-subsets
                                     of `T` (distinct subsets ⇒ distinct nodal poly),
                                     via the roots multiset and injectivity of `v`.
   (3) `pS_injOn_powersetCard`    — hence, when `g.coeff a ≠ 0` (the word `g` has a
                                     genuine degree-`a` top coefficient),
                                     `S ↦ pS g v S` is injective on the `a`-subsets.
   (4) `averaging_pigeonhole`     — for ANY classifying map `cls` from the `a`-subsets
                                     into a type with `q^t` values, some class has
                                     `≥ ⌊C(n,a)/q^t⌋` subsets (natural-number
                                     division, i.e. the floor, not the ceiling).
   (5) `averaging_list_lower_bound` — THE MAIN THEOREM.  Combining (3) and (4):
                                     there is a class of subsets, all mapping under
                                     `S ↦ pS g v S` to DISTINCT polynomials (each of
                                     degree `≤ max(deg g, a)`, agreeing with `g` on
                                     the `a` points of its subset), of size
                                     `≥ ⌊C(n, a) / q^t⌋`.

  This is a family of polynomial agreement witnesses, NOT the bracket's list
  lower bound `maxList(1 - (k+t)/n) ≥ C(n, k+t) / q^t` for the fixed word `g`:
  nothing says any `pS g v S` has degree `< k`, and an arbitrary heavy class need
  not be the class that makes this fixed `g` drop to degree `< k`.  Concrete
  obstruction: `F = F_17`, `T = μ_8 = {1,2,4,8,16,15,13,9}`, `k = 2`, `t = 1`,
  `a = 3`, `g = X^3`.  If `X^3 − h` with `deg h < 2` vanishes on 3 distinct domain
  points it equals their monic nodal cubic, whose `X^2` coefficient is minus the
  triple sum; so the triple sum is `0`.  No triple in `μ_8` has sum `0` in `F_17`,
  hence the genuine degree-`< 2` list of `X^3` at agreement 3 is EMPTY, while the
  formal statement here still yields `⌊56/17⌋ = 3` distinct agreeing polynomials.
  The genuine existential list lower bound (choosing the word `g` to match the
  heavy target) is `ListInteriorUnconditionalT1`.

  ----------------------------------------------------------------------------
  WHAT IS *NOT* PROVED (honest scope)
  ----------------------------------------------------------------------------

  * That within a fixed elementary-symmetric class the codeword `pS g v S` actually
    has degree `< k` (the "degree drop").  That requires the Vieta identities making
    the top `t+1` coefficients of `pS` cancel; here we keep the classifying map
    abstract (any map into a `q^t`-element type) so the pigeonhole and distinctness
    are FULLY rigorous, and instantiate it with the genuine `nodal`-coefficient
    classifier for the non-vacuity witness.  The degree-drop refinement (with a
    word `g` matched to the heavy class) is the missing ingredient to turn "agree
    on `a` points" into "is a degree-`<k` codeword"; for a FIXED `g` it can fail
    outright (the `F_17` example above).  It is flagged, not assumed.
  * No claim is made that this lower bound CROSSES `ε*|F|` at the proximity gap;
    that is the separate (open) interior question.

  Non-vacuity: the final section instantiates `F = ZMod 5`, `n = 5`, `t = 1`,
  `a = 2`, an explicit injective `v`, and `g = X^2` (`g.coeff 2 ≠ 0`),
  exhibiting a class of size `≥ ⌊C(5,2)/5⌋ = 2` of distinct agreeing
  polynomials — all hypotheses satisfied by witnesses.
-/

namespace ArkLib.CodingTheory.Round11RSAveraging

open Polynomial Finset

noncomputable section

variable {F : Type*} [Field F] {ι : Type*}

/-- The averaging-construction word: perturb `g` by a multiple of the nodal
polynomial through the subset `S`, scaled by the top coefficient `g.coeff a`. -/
def pS (g : F[X]) (v : ι → F) (S : Finset ι) : F[X] :=
  g - C (g.coeff (#S)) * Lagrange.nodal S v

/-- The perturbation `pS g v S` agrees with `g` at every evaluation node of `S`,
because the nodal polynomial vanishes there.  This is the "agrees with `g` on the
`a` points of `S`" content. -/
theorem pS_eval_eq_of_mem (g : F[X]) (v : ι → F) (S : Finset ι) {i : ι} (hi : i ∈ S) :
    (pS g v S).eval (v i) = g.eval (v i) := by
  unfold pS
  simp [Lagrange.eval_nodal_at_node hi]

/-- `nodal S v` for `S` ranging over an injective node map encodes `S` via its
multiset of roots, hence is injective on subsets of an `InjOn` set. -/
theorem nodal_injOn_of_injOn {T : Finset ι} {v : ι → F} (hv : Set.InjOn v T)
    {S₁ S₂ : Finset ι} (hS₁ : S₁ ⊆ T) (hS₂ : S₂ ⊆ T)
    (h : Lagrange.nodal S₁ v = Lagrange.nodal S₂ v) : S₁ = S₂ := by
  -- `nodal S v = ∏_{i∈S} (X - C (v i))`; its roots multiset is `(S.val).map v`.
  have roots_nodal : ∀ S : Finset ι, (Lagrange.nodal S v).roots = (S.val).map v := by
    intro S
    rw [Lagrange.nodal_eq,
        Polynomial.roots_prod (fun i => X - C (v i)) S
          (Finset.prod_ne_zero_iff.mpr (fun a _ => Polynomial.X_sub_C_ne_zero (v a)))]
    simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton]
  have e1 := roots_nodal S₁
  have e2 := roots_nodal S₂
  have hroots : (S₁.val).map v = (S₂.val).map v := by rw [← e1, ← e2, h]
  -- `v` injective on `T ⊇ S₁ ∪ S₂` ⇒ the multisets `S₁.val.map v = S₂.val.map v`
  -- determine `S₁ = S₂`.
  apply Finset.Subset.antisymm
  · intro x hx
    have hxv : v x ∈ (S₂.val).map v := by
      rw [← hroots]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.1 hxv
    have hyT : y ∈ T := hS₂ hy
    have hxT : x ∈ T := hS₁ hx
    rwa [hv hyT hxT hyx] at hy
  · intro x hx
    have hxv : v x ∈ (S₁.val).map v := by
      rw [hroots]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.1 hxv
    have hyT : y ∈ T := hS₁ hy
    have hxT : x ∈ T := hS₂ hx
    rwa [hv hyT hxT hyx] at hy

/-- When `g`'s degree-`a` coefficient is nonzero, the averaging map `S ↦ pS g v S`
is injective on the `a`-subsets of `T`. -/
theorem pS_injOn_powersetCard {T : Finset ι} {v : ι → F} (hv : Set.InjOn v T)
    {g : F[X]} {a : ℕ} (hc : g.coeff a ≠ 0)
    {S₁ S₂ : Finset ι} (h₁ : S₁ ∈ T.powersetCard a) (h₂ : S₂ ∈ T.powersetCard a)
    (h : pS g v S₁ = pS g v S₂) : S₁ = S₂ := by
  rw [Finset.mem_powersetCard] at h₁ h₂
  obtain ⟨hS₁, hcard₁⟩ := h₁
  obtain ⟨hS₂, hcard₂⟩ := h₂
  -- `pS g v Sᵢ = g - C (g.coeff a) * nodal Sᵢ v` with the same scalar `C (g.coeff a)`.
  have hcc : g.coeff (#S₁) = g.coeff a := by rw [hcard₁]
  have hcc' : g.coeff (#S₂) = g.coeff a := by rw [hcard₂]
  unfold pS at h
  rw [hcc, hcc'] at h
  -- subtract `g`, cancel the (nonzero) scalar `C (g.coeff a)`.
  have hnod : C (g.coeff a) * Lagrange.nodal S₁ v = C (g.coeff a) * Lagrange.nodal S₂ v :=
    sub_right_injective h
  have hCne : C (g.coeff a) ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using hc
  have hnodal : Lagrange.nodal S₁ v = Lagrange.nodal S₂ v :=
    mul_left_cancel₀ hCne hnod
  exact nodal_injOn_of_injOn hv hS₁ hS₂ hnodal

/-- Pigeonhole over the elementary-symmetric classes.  For ANY classifying map
`cls` of the `a`-subsets of `T` into a (finite) type `β` of size `q^t`, some
class `y : β` contains at least `C(#T, a) / (card β)` of the `a`-subsets.

Instantiated with `β = (Fin t → F)` we get the `q^t` classes of the top `t`
elementary-symmetric coefficients of the nodal polynomial; `card β = q^t`. -/
theorem averaging_pigeonhole {β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (T : Finset ι) (a : ℕ) (cls : Finset ι → β) :
    ∃ y : β,
      Nat.choose (#T) a / Fintype.card β ≤
        #{S ∈ T.powersetCard a | cls S = y} := by
  -- pigeonhole: `#(univ : Finset β) * (C(#T,a) / card β) ≤ #(T.powersetCard a)`.
  have hmaps : ∀ S ∈ T.powersetCard a, cls S ∈ (Finset.univ : Finset β) :=
    fun S _ => Finset.mem_univ _
  have hcard : #(T.powersetCard a) = Nat.choose (#T) a := by
    rw [Finset.card_powersetCard]
  have hmul : (Finset.univ : Finset β).card * (Nat.choose (#T) a / Fintype.card β)
      ≤ #(T.powersetCard a) := by
    rw [hcard, Finset.card_univ]
    exact Nat.mul_div_le _ _
  obtain ⟨y, _, hy⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps Finset.univ_nonempty hmul
  exact ⟨y, hy⟩

/--
**Main theorem — averaging agreement families (not a degree-`< k` list bound).**

Fix a finite field `F`, an injective evaluation map `v` on an `n`-point set
`T`, a word `g : F[X]` whose degree-`a` coefficient is nonzero (`a := k+t`),
and ANY classifying map `cls` of the `a`-subsets into a `q^t`-element type `β`.

Then there is a class `y : β` and a set `𝒮` of `a`-subsets of `T`, all in class
`y`, of size at least `⌊C(n, a) / q^t⌋` (natural-number division), such that
the averaging map `S ↦ pS g v S = g - C (g.coeff a) · nodal S v`

  * is INJECTIVE on `𝒮` (distinct subsets ⇒ distinct polynomials), and
  * each `pS g v S` AGREES with `g` at all `a` evaluation points of `S`.

No degree bound `deg (pS g v S) < k` is asserted, so this does NOT give
`maxList(1 − (k+t)/n) ≥ C(n, k+t) / q^t` for the fixed word `g`; for
`F_17`, `μ_8`, `k = 2`, `a = 3`, `g = X^3` the genuine degree-`< 2` list at
agreement 3 is empty (module docstring).
-/
theorem averaging_list_lower_bound
    {β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    {T : Finset ι} {v : ι → F} (hv : Set.InjOn v T)
    {g : F[X]} {a : ℕ} (hc : g.coeff a ≠ 0)
    (cls : Finset ι → β) :
    ∃ (y : β) (𝒮 : Finset (Finset ι)),
      (∀ S ∈ 𝒮, S ∈ T.powersetCard a ∧ cls S = y) ∧
      Nat.choose (#T) a / Fintype.card β ≤ #𝒮 ∧
      Set.InjOn (pS g v) 𝒮 ∧
      (∀ S ∈ 𝒮, ∀ i ∈ S, (pS g v S).eval (v i) = g.eval (v i)) := by
  obtain ⟨y, hy⟩ := averaging_pigeonhole T a cls
  refine ⟨y, {S ∈ T.powersetCard a | cls S = y}, ?_, hy, ?_, ?_⟩
  · intro S hS
    rw [Finset.mem_filter] at hS
    exact hS
  · -- injectivity of the averaging map on this class.
    intro S₁ hS₁ S₂ hS₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hS₁ hS₂
    exact pS_injOn_powersetCard hv hc hS₁.1 hS₂.1 h
  · -- each codeword agrees with `g` at all `a` nodes of its subset.
    intro S _ i hi
    exact pS_eval_eq_of_mem g v S hi

/-! ## Non-vacuity witness

We instantiate over `F = ZMod 5`, `n = 5` evaluation points `T = univ`,
`a = k + t = 2`, classifier type `β = Fin 1 → ZMod 5` (so `q^t = 5^1 = 5`),
the injective evaluation map `v i = (i : ZMod 5)`, and the word `g = X^2`
(whose degree-2 coefficient is `1 ≠ 0`).

All hypotheses of `averaging_list_lower_bound` are met by explicit witnesses,
and the resulting bound is the CONCRETE POSITIVE number
    C(5, 2) / 5^1 = 10 / 5 = 2,
so there really exist `≥ 2` distinct polynomials of degree `≤ 2` agreeing with
`X^2` on `2` of the `5` points (no degree-`< k` claim) — the averaging
agreement-family statement is non-vacuous. -/

instance primeFact_AveragingListLowerBoundRS_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The evaluation map for the witness instance. -/
def vWit : Fin 5 → ZMod 5 := fun i => (i : ZMod 5)

theorem vWit_injOn : Set.InjOn vWit (Finset.univ : Finset (Fin 5)) := by
  intro a _ b _ h
  have : Function.Injective vWit := by decide
  exact this h

theorem gWit_coeff_ne : (X ^ 2 : (ZMod 5)[X]).coeff 2 ≠ 0 := by
  rw [coeff_X_pow]; decide

/-- Non-vacuous concrete bound: there is a class of `≥ 2` distinct degree-≤2
polynomials (`X^2 - C 1 · nodal S vWit`), all agreeing with `X^2` on the `2`
evaluation points of their subset `S`, within a single elementary-symmetric
class of the nodal top coefficient. -/
theorem averaging_witness :
    ∃ (y : (Fin 1 → ZMod 5)) (𝒮 : Finset (Finset (Fin 5))),
      (∀ S ∈ 𝒮, S ∈ (Finset.univ : Finset (Fin 5)).powersetCard 2 ∧
        (fun S => fun _ : Fin 1 => (Lagrange.nodal S vWit).coeff 1) S = y) ∧
      2 ≤ #𝒮 ∧
      Set.InjOn (pS (X ^ 2) vWit) 𝒮 ∧
      (∀ S ∈ 𝒮, ∀ i ∈ S,
        (pS (X ^ 2) vWit S).eval (vWit i) =
          (X ^ 2 : (ZMod 5)[X]).eval (vWit i)) := by
  -- the classifier: the degree-1 coefficient of the nodal polynomial (one
  -- elementary-symmetric coordinate, since `t = 1`), valued in `Fin 1 → ZMod 5`.
  obtain ⟨y, 𝒮, hmem, hcard, hinj, heval⟩ :=
    averaging_list_lower_bound (β := Fin 1 → ZMod 5) (a := 2)
      vWit_injOn gWit_coeff_ne
      (cls := fun S => fun _ : Fin 1 => (Lagrange.nodal S vWit).coeff 1)
  refine ⟨y, 𝒮, hmem, ?_, hinj, heval⟩
  -- `C(5,2) / card (Fin 1 → ZMod 5) = 10 / 5 = 2 ≤ #𝒮`.
  have hcv :
      Nat.choose (#(Finset.univ : Finset (Fin 5))) 2 /
        Fintype.card (Fin 1 → ZMod 5) = 2 := by
    simp only [Finset.card_univ, Fintype.card_fin]
    decide
  rw [hcv] at hcard
  exact hcard

end

end ArkLib.CodingTheory.Round11RSAveraging

#print axioms ArkLib.CodingTheory.Round11RSAveraging.averaging_list_lower_bound
#print axioms ArkLib.CodingTheory.Round11RSAveraging.averaging_witness
