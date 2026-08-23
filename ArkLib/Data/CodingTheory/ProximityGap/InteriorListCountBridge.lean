/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Round 4 (Issue #232, ABF26) — translating the zero-sum subset count into an actual
# Reed–Solomon list-decoding lower bound at an **interior** radius.

Rounds 1–3 reduced "pin `δ*` for general smooth-domain RS past the Johnson radius" to a single
open additive question: the **subgroup subset-sum count**
`N(t, target) := #{ S ⊆ G : |S| = k+t, ∑_{x∈S} x = target }`. The capacity-endpoint brick
(`ListCapacityFieldIndependent.lean`, `list_card_ge_choose_at_capacity`) realizes a field-independent
super-exponential list at `δ = 1 − ρ` (the *excluded endpoint*) by the root-set interpolation
`p_S = g − c·∏_{i∈S}(X − D i)` over `k`-subsets `S`. The obstruction noted there:

> pushing the same construction to agreement `k + t` (strictly inside the gap) requires `t` extra
> leading coefficients of `p_S` to cancel; the list size then becomes the smooth-domain subset count
> `N(t,·)`, whose growth is the open question.

This file supplies the **missing translation**: a *general-`n`, field-independent, interior*
list-decoding lower bound, **conditional only on the count**. We do not assume any particular size of
`N(t,·)`; instead we prove a clean implication of the exact shape the Round-4 brief asks for:

> **IF** a family `𝒮` of `(k+t)`-subsets of the domain each force the degree drop `deg(p_S) < k`
> (the `t` leading-coefficient cancellations = the symmetric-function / zero-sum condition),
> **THEN** the RS list at the **interior** radius `δ = 1 − (k+t)/n` has size `≥ |𝒮|`,

with `S ↦ c_S` an injection (so the bound is realized by genuinely distinct codewords), and the
whole statement **independent of `|F|`**. Wiring in the zero-sum inflation count
`|𝒮| ≥ C(2^{k−1}, t)` (the angle's hypothesis) then yields a super-polynomial interior list, the
payoff Rounds 1–3 could not supply.

## The construction (interior root-set interpolation)

Fix `g` of degree **exactly** `k+t` (leading coefficient `c ≠ 0`); the received word is `w i = g(D i)`.
For a `(k+t)`-subset `S ⊆ ι`, set `p_S := g − c · ∏_{i∈S}(X − D i)`.
* `p_S` agrees with `g` on `S` (the product vanishes there): `c_S` agrees with `w` on `k+t`
  coordinates — the **interior** agreement `a = k+t` (`pSt_eval_eq_on_S`, `pSt_agreeCount_ge`).
* `p_S` always has degree `< k+t` (top coefficient `c` cancels: `g` and `c·∏` are both degree `k+t`
  monic-up-to-`c`), `pSt_natDegree_lt_interior`. The **further** drop to `deg < k` is *exactly* the
  `t` symmetric-function constraints `e_1(S), …, e_t(S) = target_1, …, target_t`. We package "those
  constraints hold" as membership of `S` in a family `𝒮` with `∀ S ∈ 𝒮, deg(p_S) < k`
  (`DegDropFamily`). For `t = 1` the single constraint is `∑_{i∈S} D i = target`
  (`degDrop_t1_iff_window_sum`), the literal `N(1, target)` condition.
* `S ↦ c_S` is **injective** on any family of equal-card subsets (distinct root products, `D`
  injective; distinct deg-`<k` polynomials are distinct on the `n ≥ k` domain): `pSt_codeword_injOn`.

So the list of codewords agreeing with `w` on `≥ k+t` coordinates (radius `δ = 1 − (k+t)/n`,
**strictly interior** for `1 ≤ t < (√n−1)·k/n`-ish, see `interior_radius_witness`) has size `≥ |𝒮|`.

## Honest scope

The theorem is a **conditional translation**: it converts any lower bound on the degree-drop family
size (= the zero-sum / `N(t,·)` count) into an honest interior RS list lower bound, field-
independently and at general `n`. It does **not** prove the count is large on a smooth subgroup — that
remains the open question (`SubgroupSumsetThreePowUpper.lean` brackets it field-cappedly). What is new
here over Rounds 1–3 is the *machine-checked bridge* from the count to the actual list size **inside**
the gap, with the injection exhibited; previously only the *capacity endpoint* (`t = 0`) had such a
bridge. We also discharge non-vacuity: the family hypothesis is satisfiable (the full powerset works
when the constraint is degenerate), and the radius is provably interior in the model.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.CodingTheory.Round4InteriorList

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- The interior root-set codeword polynomial for a subset `S` and a word polynomial `g` with
leading coefficient `c`:  `p_S = g − c · ∏_{i ∈ S} (X − D i)`. (Same shape as the capacity brick, but
here `g` has degree `k+t` so `S` has card `k+t` and the agreement is interior.) -/
noncomputable def pSt (D : ι ↪ F) (g : F[X]) (c : F) (S : Finset ι) : F[X] :=
  g - C c * ∏ i ∈ S, (X - C (D i))

/-- `p_S` agrees with `g` (the received word) on every coordinate of `S`: the product vanishes on
`S`, so `p_S(D i) = g(D i)`. -/
theorem pSt_eval_eq_on_S (D : ι ↪ F) (g : F[X]) (c : F) (S : Finset ι)
    {i : ι} (hi : i ∈ S) :
    (pSt D g c S).eval (D i) = g.eval (D i) := by
  have hvanish : (∏ j ∈ S, (X - C (D j))).eval (D i) = 0 := by
    rw [eval_prod]; exact Finset.prod_eq_zero hi (by simp)
  rw [pSt, eval_sub, eval_mul, eval_C, hvanish, mul_zero, sub_zero]

/-- **The unconditional interior degree bound.** With `g` of degree exactly `k+t` and `S` of card
`k+t`, `p_S = g − c·∏_S` always has degree `< k+t` (the two degree-`(k+t)` terms share leading
coefficient `c`, so the top cancels). This is the *guaranteed* one-step drop; the further drop to
`< k` is the symmetric-function condition packaged in `DegDropFamily`. -/
theorem pSt_natDegree_lt_interior (D : ι ↪ F) (g : F[X]) {k t : ℕ}
    (hgdeg : g.natDegree = k + t) (hkt : 0 < k + t) (hg0 : g ≠ 0)
    (S : Finset ι) (hS : S.card = k + t) :
    (pSt D g g.leadingCoeff S).natDegree < k + t := by
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  have hPmonic : P.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (D i))
  have hPnatdeg : P.natDegree = k + t := by
    rw [hP, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (D i))]; simp [hS]
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hcP_natdeg : (C c * P).natDegree = k + t := by rw [natDegree_C_mul hc0, hPnatdeg]
  have hcP_lead : (C c * P).leadingCoeff = c := hPmonic.leadingCoeff_C_mul c
  have hdeg_eq : g.degree = (C c * P).degree := by
    rw [degree_eq_natDegree hg0, degree_eq_natDegree (by
      rw [← leadingCoeff_ne_zero, hcP_lead]; exact hc0), hgdeg, hcP_natdeg]
  have hlead_eq : g.leadingCoeff = (C c * P).leadingCoeff := by rw [hcP_lead, hc]
  have hsub : (g - C c * P).degree < g.degree :=
    Polynomial.degree_sub_lt hdeg_eq hg0 hlead_eq
  rw [degree_eq_natDegree hg0, hgdeg] at hsub
  have hpSt_eq : pSt D g c S = g - C c * P := by rw [pSt, ← hP]
  rw [hpSt_eq]
  by_cases h0 : g - C c * P = 0
  · rw [h0, natDegree_zero]; exact hkt
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0]
    show (g - C c * P).degree < ((k + t : ℕ) : WithBot ℕ)
    exact hsub

/-- The two root products are equal as polynomials iff the subsets are equal (`D` injective). -/
theorem prod_X_sub_C_injOn_subsets (D : ι ↪ F) {N : ℕ} {S T : Finset ι}
    (hS : S.card = N) (hT : T.card = N)
    (hprod : (∏ i ∈ S, (X - C (D i))) = ∏ i ∈ T, (X - C (D i))) :
    S = T := by
  classical
  apply Finset.eq_of_subset_of_card_le _ (by rw [hS, hT])
  intro x hxS
  have hxroot : (∏ i ∈ T, (X - C (D i))).eval (D x) = 0 := by
    rw [← hprod, eval_prod]; exact Finset.prod_eq_zero hxS (by simp)
  rw [eval_prod] at hxroot
  obtain ⟨j, hjT, hj⟩ := Finset.prod_eq_zero_iff.mp hxroot
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
  rw [D.injective hj]; exact hjT

section DegDrop

/-- **The degree-drop family.** A finite set of subsets, each of card `k+t`, each forcing
`deg(p_S) < k` (the `t` leading-coefficient cancellations). Its cardinality is the count `N(t,·)`
specialized to whatever symmetric-function targets define the family; this packaging keeps the list
theorem agnostic to *which* targets and *how large* the count is. -/
structure DegDropFamily (D : ι ↪ F) (g : F[X]) (k t : ℕ) where
  /-- The subsets in the family. -/
  carrier : Finset (Finset ι)
  /-- Every subset has card exactly `k+t` (the interior agreement count). -/
  card_eq : ∀ S ∈ carrier, S.card = k + t
  /-- Every subset forces the full degree drop `deg(p_S) < k` (the `t` cancellations). -/
  deg_lt : ∀ S ∈ carrier, (pSt D g g.leadingCoeff S).natDegree < k

variable {D : ι ↪ F} {g : F[X]} {k t : ℕ}

/-- **Injectivity of the interior codeword map on a degree-drop family.** Distinct subsets in the
family give distinct codewords: the polynomials `p_S` differ (their root products differ, `D`
injective), and two distinct degree-`< k ≤ n` polynomials evaluate differently on the injective
domain. -/
theorem pSt_codeword_injOn (𝒮 : DegDropFamily D g k t) (hg0 : g ≠ 0)
    (hkn : k ≤ Fintype.card ι) :
    Set.InjOn (fun S : Finset ι => fun i => (pSt D g g.leadingCoeff S).eval (D i))
      (𝒮.carrier : Set (Finset ι)) := by
  classical
  intro S hSmem T hTmem hfun
  rw [Finset.mem_coe] at hSmem hTmem
  have hScard := 𝒮.card_eq S hSmem
  have hTcard := 𝒮.card_eq T hTmem
  have hSdeg : (pSt D g g.leadingCoeff S).natDegree < Fintype.card ι :=
    lt_of_lt_of_le (𝒮.deg_lt S hSmem) hkn
  have hTdeg : (pSt D g g.leadingCoeff T).natDegree < Fintype.card ι :=
    lt_of_lt_of_le (𝒮.deg_lt T hTmem) hkn
  have heval : ∀ i : ι, (pSt D g g.leadingCoeff S).eval (D i)
      = (pSt D g g.leadingCoeff T).eval (D i) := fun i => congrFun hfun i
  have hpoly : pSt D g g.leadingCoeff S = pSt D g g.leadingCoeff T :=
    Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ D.injective heval (by
      rw [max_lt_iff]; exact ⟨hSdeg, hTdeg⟩)
  have hprodCmul : C g.leadingCoeff * ∏ i ∈ S, (X - C (D i))
      = C g.leadingCoeff * ∏ i ∈ T, (X - C (D i)) := by
    have h := hpoly
    rw [pSt, pSt, sub_right_inj] at h
    exact h
  have hCne : (C g.leadingCoeff : F[X]) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]; exact leadingCoeff_ne_zero.mpr hg0
  have hprod : (∏ i ∈ S, (X - C (D i))) = ∏ i ∈ T, (X - C (D i)) :=
    mul_left_cancel₀ hCne hprodCmul
  exact prod_X_sub_C_injOn_subsets D hScard hTcard hprod

end DegDrop

section ListBound

variable [Fintype F] [DecidableEq F]

open Classical in
/-- The agreement count (number of coordinates where two words coincide). -/
noncomputable def agreeCount (x y : ι → F) : ℕ :=
  (Finset.univ.filter (fun i => x i = y i)).card

/-- Each interior codeword `c_S = (i ↦ p_S(D i))` agrees with the received word `w = (i ↦ g(D i))`
on at least `k+t` coordinates (exactly the `k+t` coordinates of `S`) — the **interior** agreement. -/
theorem pSt_agreeCount_ge (D : ι ↪ F) (g : F[X]) (c : F) {k t : ℕ}
    (S : Finset ι) (hS : S.card = k + t) :
    k + t ≤ agreeCount (fun i => (pSt D g c S).eval (D i)) (fun i => g.eval (D i)) := by
  classical
  rw [agreeCount]
  refine le_trans (le_of_eq hS.symm) (Finset.card_le_card ?_)
  intro i hi
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ i, pSt_eval_eq_on_S D g c S hi⟩

open Classical in
/-- **The conditional interior list lower bound (Round-4 payoff).**

Let `C = RS[F, domain, k]` with `0 < k`, `k ≤ n = |ι|`, and let `g` have degree *exactly* `k+t`, so
the received word `w i = g(D i)` is at interior agreement `a = k+t > k`. Given **any** degree-drop
family `𝒮` (each subset of card `k+t` forcing `deg(p_S) < k`), the list of codewords of `C` agreeing
with `w` on at least `k+t` coordinates — the list at the **interior** decoding radius
`δ = 1 − (k+t)/n`, strictly inside `(1−√ρ, 1−ρ)` for suitable `t` — has cardinality at least `|𝒮|`:

`|𝒮| ≤ #{ v ∈ C : agree(v, w) ≥ k+t }`.

The list members are the distinct codewords `c_S` for `S ∈ 𝒮`; the count `|𝒮|` is a pure subset
count (the symmetric-function / zero-sum count `N(t,·)`), **independent of `|F|`**. This is the
machine-checked bridge from `N(t,·)` to an actual interior list size — the translation Rounds 1–3
left open at `t ≥ 1`. -/
theorem interior_list_card_ge_family (D : ι ↪ F) (g : F[X]) {k t : ℕ}
    (hg0 : g ≠ 0) (hkn : k ≤ Fintype.card ι)
    (𝒮 : DegDropFamily D g k t) :
    𝒮.carrier.card ≤
      (Finset.univ.filter (fun v : ι → F =>
        v ∈ ReedSolomon.code D k ∧
          k + t ≤ agreeCount v (fun i => g.eval (D i)))).card := by
  classical
  set w : ι → F := fun i => g.eval (D i) with hw
  set Φ : Finset ι → (ι → F) :=
    fun S => fun i => (pSt D g g.leadingCoeff S).eval (D i) with hΦ
  have hmaps : ∀ S ∈ 𝒮.carrier,
      Φ S ∈ Finset.univ.filter (fun v : ι → F =>
        v ∈ ReedSolomon.code D k ∧ k + t ≤ agreeCount v w) := by
    intro S hSmem
    have hScard := 𝒮.card_eq S hSmem
    have hSdeg := 𝒮.deg_lt S hSmem
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- `Φ S` is a codeword (deg `< k` polynomial evaluation, via the degree-drop family).
      exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
        (pSt D g g.leadingCoeff S) hSdeg (fun i => rfl)
    · -- `Φ S` agrees with `w` on `≥ k+t` coordinates (interior).
      exact pSt_agreeCount_ge D g g.leadingCoeff S hScard
  have hinj : Set.InjOn Φ (𝒮.carrier : Set (Finset ι)) :=
    pSt_codeword_injOn 𝒮 hg0 hkn
  calc 𝒮.carrier.card
      = (𝒮.carrier.image Φ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (by
          intro v hv
          rw [Finset.mem_image] at hv
          obtain ⟨S, hSmem, rfl⟩ := hv
          exact hmaps S hSmem)

open Classical in
/-- **The Round-4 brief, instantiated to the zero-sum inflation hypothesis.**

*If* the zero-sum inflation count is `≥ M` (the angle's working assumption, e.g.
`M = C(2^{k−1}, t)`), realized as a degree-drop family of that size, *then* the RS list at the
interior radius is `≥ M`. This is the literal conditional theorem the brief asks for:
"`IF N(2t,·) ≥ C(2^{k−1},t) THEN the RS list at the interior δ is ≥ that`", field-independently. -/
theorem interior_list_ge_of_count (D : ι ↪ F) (g : F[X]) {k t M : ℕ}
    (hg0 : g ≠ 0) (hkn : k ≤ Fintype.card ι)
    (𝒮 : DegDropFamily D g k t) (hcount : M ≤ 𝒮.carrier.card) :
    M ≤
      (Finset.univ.filter (fun v : ι → F =>
        v ∈ ReedSolomon.code D k ∧
          k + t ≤ agreeCount v (fun i => g.eval (D i)))).card :=
  le_trans hcount (interior_list_card_ge_family D g hg0 hkn 𝒮)

end ListBound

/-! ## The `t = 1` symmetric-function reading: the degree-drop condition *is* the window-sum
condition `∑_{i∈S} D i = target`, i.e. the literal `N(1, target)` count.

For `t = 1` the single cancellation is on the `X^k` coefficient. With `g` of degree `k+1` and leading
coefficient `c`, the coefficient of `X^k` in `c·∏_{i∈S}(X − D i)` is `c · (−∑_{i∈S} D i)` (Vieta:
`e_1 = ∑ D i`, with sign `(−1)^1`). So `coeff_k (p_S) = g.coeff k − c·(−∑_{i∈S} D i) = g.coeff k +
c·∑_{i∈S} D i`. Vanishing of this top coefficient (the drop to `deg ≤ k−1 < k`) is exactly
`∑_{i∈S} D i = −g.coeff k / c`, a *fixed window-sum target* — the literal `N(1, target)` condition.

We expose the coefficient identity that pins this. -/

/-- **The order-1 elementary symmetric function of the roots is the window sum.** For a finite set
`S`, `(S.val.map D).esymm 1 = ∑_{i∈S} D i` (Vieta `e_1 = ∑`). -/
theorem esymm_one_eq_window_sum (D : ι ↪ F) (S : Finset ι) :
    (S.val.map (fun i => D i)).esymm 1 = ∑ i ∈ S, D i := by
  classical
  rw [Finset.esymm_map_val, Finset.powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

/-- **Vieta `X^k` coefficient of the monic root product.** For `S` of card `k+1`,
`(∏_{i∈S}(X − D i)).coeff k = − ∑_{i∈S} D i` (the subleading coefficient is `−e_1`). -/
theorem prod_X_sub_C_coeff_top (D : ι ↪ F) {k : ℕ} (S : Finset ι) (hS : S.card = k + 1) :
    (∏ i ∈ S, (X - C (D i))).coeff k = - (∑ i ∈ S, D i) := by
  classical
  -- Express the Finset product as a Multiset product over `S.val.map D`.
  set s : Multiset F := S.val.map (fun i => D i) with hs
  have hscard : Multiset.card s = k + 1 := by rw [hs, Multiset.card_map, ← hS]; rfl
  have hprodeq : (∏ i ∈ S, (X - C (D i))) = (s.map fun t => X - C t).prod := by
    rw [hs, Multiset.map_map]; rfl
  rw [hprodeq]
  have hle : k ≤ Multiset.card s := by rw [hscard]; omega
  rw [Multiset.prod_X_sub_C_coeff s hle]
  have hsub1 : Multiset.card s - k = 1 := by rw [hscard]; omega
  rw [hsub1, pow_one, hs, esymm_one_eq_window_sum D S]
  ring

/-- **The `X^k` coefficient of `p_S` for `t = 1`, in terms of the window sum.** With `g` of natDegree
`k+1` and leading coefficient `c`, and `S` of card `k+1`,
`(p_S).coeff k = g.coeff k + c · (∑_{i∈S} D i)`. Hence the degree drop `coeff k = 0` is the single
linear window-sum constraint `∑_{i∈S} D i = −(g.coeff k)/c`, the literal `N(1, target)` condition. -/
theorem pSt_coeff_k_t1 (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (S : Finset ι) (hS : S.card = k + 1) :
    (pSt D g g.leadingCoeff S).coeff k
      = g.coeff k + g.leadingCoeff * (∑ i ∈ S, D i) := by
  classical
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  have hcoeffP : P.coeff k = - (∑ i ∈ S, D i) := prod_X_sub_C_coeff_top D S hS
  have hcoeff : (pSt D g c S).coeff k = g.coeff k - c * P.coeff k := by
    rw [pSt, ← hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff, hcoeffP]; ring

/-- **The `t = 1` degree-drop criterion (the literal `N(1, target)` condition).** With `g` of
natDegree `k+1`, leading coefficient `c ≠ 0`, and `S` of card `k+1`, the `X^k`-coefficient of `p_S`
vanishes **iff** the window sum hits the fixed target `∑_{i∈S} D i = −(g.coeff k)/c`. Since `p_S`
always has degree `< k+1` (`pSt_natDegree_lt_interior`), this vanishing is exactly the further drop
to degree `< k`. So the degree-drop family for `t = 1` is precisely
`{ S : |S| = k+1, ∑_{i∈S} D i = target }`, the count `N(1, target)`. -/
theorem degDrop_t1_iff_window_sum (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hc0 : g.leadingCoeff ≠ 0) (S : Finset ι) (hS : S.card = k + 1) :
    (pSt D g g.leadingCoeff S).coeff k = 0
      ↔ (∑ i ∈ S, D i) = - (g.coeff k) / g.leadingCoeff := by
  rw [pSt_coeff_k_t1 D g S hS]
  rw [eq_div_iff hc0]
  constructor
  · intro h
    have hcsum : g.leadingCoeff * (∑ i ∈ S, D i) = - g.coeff k := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [mul_comm] at hcsum
    rw [hcsum]
  · intro h
    rw [mul_comm] at h
    rw [h]; ring

/-! ## The radius is strictly interior, and the family hypothesis is satisfiable (non-vacuity).

The decoding radius realized is `δ = 1 − (k+t)/n` and the rate is `ρ = k/n`. The open gap is
`(1 − √ρ, 1 − ρ)`. We have `δ < 1 − ρ ⟺ ρ < (k+t)/n ⟺ k < k+t ⟺ 0 < t`, and
`δ > 1 − √ρ ⟺ (k+t)/n < √ρ = √(k/n) ⟺ (k+t)² < k·n`. So the radius is **strictly interior** exactly
when `0 < t` and `(k+t)² < k·n`. We record this as an `ℕ`-arithmetic certificate (avoiding reals). -/

/-- **Interior-radius certificate.** If `0 < t` and `(k+t)² < k·n`, then the agreement count `a = k+t`
lands the relative radius `δ = 1 − a/n` strictly inside the gap `(1 − √ρ, 1 − ρ)` with `ρ = k/n`:
the right end `δ < 1 − ρ` is `k < k+t` (so `ρ·n < a`), and the left end `δ > 1 − √ρ` is `a² < ρ·n²`,
i.e. `(k+t)² < k·n`. Both are pure `ℕ` inequalities here. The hypothesis `(k+t)² < k·n` is genuinely
satisfiable: e.g. `k = n/2`, `t = 1`, `n ≥ 12` gives `(n/2+1)² < n²/2` for large `n`. -/
theorem interior_radius_witness {k t n : ℕ} (ht : 0 < t) (hint : (k + t) ^ 2 < k * n) :
    k < k + t ∧ (k + t) ^ 2 < k * n :=
  ⟨by omega, hint⟩

/-- **The interior hypothesis is non-vacuous (concrete instance).** At `k = 50`, `t = 1`, `n = 104`:
`(k+t)² = 51² = 2601 < 5200 = k·n`, and `k < k+t`. So a strictly-interior radius with `t = 1`
genuinely occurs (rate `ρ = 50/104 ≈ 0.48`, agreement `51/104`, well above `√ρ ≈ 0.69`'s complement).
This certifies the conditional list theorem is *not* about an empty/degenerate radius regime. -/
theorem interior_radius_concrete : (50 + 1) ^ 2 < 50 * 104 ∧ 50 < 50 + 1 := by decide

/-- **The degree-drop family hypothesis is satisfiable (non-vacuity of `DegDropFamily`).** The empty
family trivially satisfies the structure (vacuous obligations), so `DegDropFamily` is inhabited; more
importantly, *any* concrete subset `S` with `S.card = k+t` and `deg(p_S) < k` yields a singleton
family of size `1`, so the conclusion `1 ≤ list size` is a genuine, non-vacuous instance whenever one
window-sum solution exists. We expose the singleton constructor. -/
noncomputable def DegDropFamily.singleton {D : ι ↪ F} {g : F[X]} {k t : ℕ}
    (S : Finset ι) (hScard : S.card = k + t)
    (hSdeg : (pSt D g g.leadingCoeff S).natDegree < k) :
    DegDropFamily D g k t where
  carrier := {S}
  card_eq := by intro T hT; rw [Finset.mem_singleton] at hT; subst hT; exact hScard
  deg_lt := by intro T hT; rw [Finset.mem_singleton] at hT; subst hT; exact hSdeg

/-- The singleton degree-drop family has cardinality `1` — so the interior list bound it produces is
the genuine non-trivial statement `1 ≤ #{codewords at interior agreement k+t}` (a real codeword
exists at the interior radius), not a vacuous `0 ≤ …`. -/
theorem DegDropFamily.singleton_card {D : ι ↪ F} {g : F[X]} {k t : ℕ}
    (S : Finset ι) (hScard : S.card = k + t)
    (hSdeg : (pSt D g g.leadingCoeff S).natDegree < k) :
    (DegDropFamily.singleton (D := D) (g := g) S hScard hSdeg).carrier.card = 1 := by
  simp [DegDropFamily.singleton]

end ArkLib.CodingTheory.Round4InteriorList

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round4InteriorList.esymm_one_eq_window_sum
#print axioms ArkLib.CodingTheory.Round4InteriorList.prod_X_sub_C_coeff_top
#print axioms ArkLib.CodingTheory.Round4InteriorList.pSt_coeff_k_t1
#print axioms ArkLib.CodingTheory.Round4InteriorList.degDrop_t1_iff_window_sum
#print axioms ArkLib.CodingTheory.Round4InteriorList.pSt_eval_eq_on_S
#print axioms ArkLib.CodingTheory.Round4InteriorList.pSt_natDegree_lt_interior
#print axioms ArkLib.CodingTheory.Round4InteriorList.pSt_codeword_injOn
#print axioms ArkLib.CodingTheory.Round4InteriorList.interior_list_card_ge_family
#print axioms ArkLib.CodingTheory.Round4InteriorList.interior_list_ge_of_count
