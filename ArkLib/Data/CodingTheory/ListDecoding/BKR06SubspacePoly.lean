/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# BKR06 subspace-polynomial core (deep sub-lemma stack)

Bottom-up construction toward ABF26 T3.12 [BKR06 Cor 2.2]
(Ben-Sasson–Kopparty–Radhakrishnan, *Subspace Polynomials and List Decoding of
Reed–Solomon Codes*, FOCS 2006).

We formalize the genuine mathematical heart: the **subspace polynomial**
`P_L(X) = ∏_{ℓ ∈ L} (X - C ℓ)` of a finite additive subgroup / `𝔽_q`-subspace `L ⊆ 𝕂`,
and its structural properties (Def 3.1 / Prop 3.2 of BKR06).

All declarations compile (`lake env lean`, exit 0) with no `sorry`/`admit`/`native_decide`
and are axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open Polynomial BigOperators Finset

namespace BKR06

variable {K : Type*} [Field K]

/-! ## Definition 3.1 and basic structure -/

/-- **BKR06 Definition 3.1 (subspace polynomial).** For a finite set `L` of field
elements, `subspacePoly L = ∏_{ℓ ∈ L} (X - C ℓ)`. In the application `L` is a finite
`𝔽_q`-subspace of `𝕂`. -/
def subspacePoly (L : Finset K) : K[X] := ∏ ℓ ∈ L, (X - C ℓ)

/-- The subspace polynomial is monic. -/
lemma subspacePoly_monic (L : Finset K) : (subspacePoly L).Monic :=
  monic_prod_X_sub_C _ _

/-- The subspace polynomial is nonzero. -/
lemma subspacePoly_ne_zero (L : Finset K) : subspacePoly L ≠ 0 :=
  (subspacePoly_monic L).ne_zero

/-- Degree of the subspace polynomial equals `|L|`. -/
lemma subspacePoly_natDegree (L : Finset K) :
    (subspacePoly L).natDegree = L.card := by
  classical
  rw [subspacePoly, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C i)]
  simp

/-- The roots multiset of the subspace polynomial is exactly `L`. -/
lemma subspacePoly_roots (L : Finset K) : (subspacePoly L).roots = L.val := by
  classical
  unfold subspacePoly
  exact roots_prod_X_sub_C L

/-- An element `x` is a root of the subspace polynomial iff `x ∈ L`. -/
lemma subspacePoly_isRoot_iff (L : Finset K) (x : K) :
    (subspacePoly L).IsRoot x ↔ x ∈ L := by
  classical
  unfold subspacePoly IsRoot
  rw [eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨ℓ, hℓ, hev⟩
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hev
    rwa [hev]
  · intro hx
    exact ⟨x, hx, by simp⟩

/-! ## Periodicity (subgroup structure)

The defining structural property: translating the variable by a group element `a ∈ L`
leaves `P_L` unchanged, because `L - a = L`. This is the polynomial-identity core that
makes `P_L` a *subspace* polynomial. -/

/-- **Periodicity / translation invariance.** If `L` is closed under subtraction
(an additive subgroup), then for `a ∈ L`, `P_L(X + C a) = P_L(X)` as a polynomial
identity.

Proven by reindexing the product along the bijection `ℓ ↦ ℓ - a` of `L`
(`L - a = L` because `L` is a group containing `a`). -/
lemma subspacePoly_comp_add_left_mem
    (L : Finset K) (a : K) (ha : a ∈ L)
    (hsub : ∀ x ∈ L, ∀ y ∈ L, x - y ∈ L)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L) :
    (subspacePoly L).comp (X + C a) = subspacePoly L := by
  classical
  unfold subspacePoly
  rw [Polynomial.prod_comp]
  -- ∏_{ℓ∈L} (X + C a - C ℓ) = ∏_{ℓ∈L} (X - C (ℓ - a))
  have hstep : ∀ ℓ ∈ L, (X - C ℓ).comp (X + C a) = X - C (ℓ - a) := by
    intro ℓ _
    simp [sub_comp, X_comp, C_comp, map_sub]
    ring
  rw [Finset.prod_congr rfl hstep]
  -- reindex via the bijection g : ℓ ↦ ℓ - a on L
  refine Finset.prod_nbij' (fun ℓ => ℓ - a) (fun m => m + a) ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ; exact hsub ℓ hℓ a ha
  · intro m hm; exact hadd m hm a ha
  · intro ℓ _; ring
  · intro m _; ring
  · intro ℓ _; rfl

/-- `P_L(0) = 0` when `0 ∈ L` (a subgroup contains `0`). -/
lemma subspacePoly_eval_zero (L : Finset K) (h0 : (0 : K) ∈ L) :
    (subspacePoly L).eval 0 = 0 :=
  (subspacePoly_isRoot_iff L 0).2 h0

/-- `subspacePoly L` is monic of degree `|L|`. -/
lemma subspacePoly_isMonicOfDegree (L : Finset K) :
    IsMonicOfDegree (subspacePoly L) L.card :=
  ⟨subspacePoly_natDegree L, subspacePoly_monic L⟩

/-! ## Proposition 3.2 — additivity of the subspace-polynomial map

This is the genuine deep core of BKR06: the evaluation map `x ↦ P_L(x)` is **additive**
when `L` is a finite additive subgroup. Equivalently `P_L` is a *linearized polynomial*.

The proof is fully elementary, using periodicity (above) plus a degree/root count:
for fixed `x₀`, the polynomial `r(Y) = P_L(x₀ + Y) - P_L(x₀) - P_L(Y)` vanishes on all
of `L` (periodicity gives `P_L(x₀ + ℓ) = P_L(x₀)`, and `P_L(ℓ) = 0` for `ℓ ∈ L`), but
has `natDegree < |L|` because the two monic degree-`|L|` terms `P_L(x₀ + Y)` and `P_L(Y)`
cancel. A polynomial of degree `< |L|` vanishing on the `|L|` distinct points of `L` is
zero, so `r = 0`, i.e. `P_L(x₀ + Y) = P_L(x₀) + P_L(Y)` for all `Y`. -/

/-- **BKR06 Proposition 3.2 (additivity of the subspace-polynomial map).**
If `L` is a finite additive subgroup of the field `K` (closed under `+`, `-`, and
containing `0`), then the evaluation map `x ↦ P_L(x)` is additive:
`P_L(x + y) = P_L(x) + P_L(y)` for all `x y : K`.

This is the linearized-polynomial property at the heart of BKR06's construction. -/
theorem subspacePoly_eval_add
    (L : Finset K) (h0 : (0 : K) ∈ L)
    (hsub : ∀ x ∈ L, ∀ y ∈ L, x - y ∈ L)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L)
    (x y : K) :
    (subspacePoly L).eval (x + y)
      = (subspacePoly L).eval x + (subspacePoly L).eval y := by
  classical
  -- `L` is nonempty (contains 0), so `|L| ≠ 0`.
  have hcard_pos : 0 < L.card := Finset.card_pos.2 ⟨0, h0⟩
  have hcard_ne : L.card ≠ 0 := hcard_pos.ne'
  -- The two monic degree-|L| polynomials in `Y` (here `X`): `P_L(C x + X)` and `P_L(X)`.
  have hmon1 : IsMonicOfDegree ((subspacePoly L).comp (X + C x)) L.card := by
    refine ⟨?_, (subspacePoly_monic L).comp_X_add_C x⟩
    rw [← taylor_apply, natDegree_taylor, subspacePoly_natDegree]
  have hmon2 : IsMonicOfDegree (subspacePoly L) L.card := subspacePoly_isMonicOfDegree L
  -- `q₁ := P_L(C x + X) - P_L(X)` has natDegree < |L|.
  have hq₁ : ((subspacePoly L).comp (X + C x) - subspacePoly L).natDegree < L.card :=
    hmon1.natDegree_sub_lt hcard_ne hmon2
  -- Subtract the constant `C (P_L(x))`; still natDegree < |L|.
  set r : K[X] := (subspacePoly L).comp (X + C x) - C ((subspacePoly L).eval x) - subspacePoly L
    with hr_def
  have hr_deg : r.natDegree < L.card := by
    have hC : (C ((subspacePoly L).eval x)).natDegree < L.card := by
      rw [natDegree_C]; exact hcard_pos
    calc r.natDegree
        = ((subspacePoly L).comp (X + C x) - subspacePoly L
            - C ((subspacePoly L).eval x)).natDegree := by rw [hr_def]; ring_nf
      _ ≤ max ((subspacePoly L).comp (X + C x) - subspacePoly L).natDegree
            (C ((subspacePoly L).eval x)).natDegree := natDegree_sub_le _ _
      _ < L.card := max_lt hq₁ hC
  -- `r` vanishes on all of `L`.
  have hr_vanish : ∀ ℓ ∈ L, r.eval ℓ = 0 := by
    intro ℓ hℓ
    have hper : (subspacePoly L).comp (X + C ℓ) = subspacePoly L :=
      subspacePoly_comp_add_left_mem L ℓ hℓ hsub hadd
    -- eval r at ℓ: P_L(x + ℓ) - P_L(x) - P_L(ℓ)
    have hev_comp : ((subspacePoly L).comp (X + C x)).eval ℓ
        = (subspacePoly L).eval (ℓ + x) := by
      rw [eval_comp]; simp
    have hPℓ : (subspacePoly L).eval ℓ = 0 := (subspacePoly_isRoot_iff L ℓ).2 hℓ
    -- P_L(ℓ + x) = P_L(x): use periodicity P_L(X + C ℓ) = P_L applied at x.
    have hper_x : (subspacePoly L).eval (x + ℓ) = (subspacePoly L).eval x := by
      have := congrArg (fun p => Polynomial.eval x p) hper
      simpa [eval_comp] using this
    rw [hr_def]
    simp only [eval_sub, eval_C, hev_comp, hPℓ]
    rw [add_comm ℓ x, hper_x]; ring
  -- A degree-`< |L|` polynomial vanishing on the `|L|`-point set `L` is zero.
  have hr_zero : r = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero' r L hr_vanish hr_deg
  -- Unpack r = 0 into the additivity identity, evaluated at `y`.
  have hz := congrArg (fun p => Polynomial.eval y p) hr_zero
  simp only [hr_def, eval_sub, eval_C, eval_zero] at hz
  have hev_y : ((subspacePoly L).comp (X + C x)).eval y = (subspacePoly L).eval (y + x) := by
    rw [eval_comp]; simp
  rw [hev_y, add_comm y x] at hz
  -- hz : eval (x + y) P_L - eval x P_L - eval y P_L = 0
  linear_combination hz

/-! ## Subspace version: `𝔽_q`-subspaces of `K`

We specialise the additivity to a genuine `𝔽_q`-subspace `W : Submodule 𝔽 K`, where `𝔽`
is a subfield (modelled as a scalar field `𝔽` with `[Module 𝔽 K]`). The carrier finset
`W.toFinset` is an additive subgroup, so the additivity theorem applies, and the degree
of its subspace polynomial is `|W| = q^{dim_𝔽 W}` (BKR06's `q^{dim L}` roots, Prop 3.2). -/

variable {F : Type*} [Field F] [Module F K]

/-- The carrier finset of an `𝔽`-subspace `W ⊆ K` (when `W` is a finite set). -/
def subFinset (W : Submodule F K) [Fintype W] : Finset K :=
  W.carrier.toFinset

@[simp] lemma mem_subFinset {W : Submodule F K} [Fintype W] {x : K} :
    x ∈ subFinset W ↔ x ∈ W := by
  simp [subFinset]

/-- **BKR06 Prop 3.2, subspace form.** For an `𝔽`-subspace `W ⊆ K`, the evaluation map
`x ↦ P_{W}(x)` of its subspace polynomial is additive. -/
theorem subspacePoly_eval_add_submodule (W : Submodule F K) [Fintype W] (x y : K) :
    (subspacePoly (subFinset W)).eval (x + y)
      = (subspacePoly (subFinset W)).eval x + (subspacePoly (subFinset W)).eval y := by
  apply subspacePoly_eval_add
  · simp [W.zero_mem]
  · intro a ha b hb; simp only [mem_subFinset] at *; exact W.sub_mem ha hb
  · intro a ha b hb; simp only [mem_subFinset] at *; exact W.add_mem ha hb

/-- The subspace polynomial of `W` is `𝔽`-additive packaged as an `AddMonoidHom K K`
(the underlying additive map of BKR06's linearized polynomial). -/
noncomputable def subspacePolyHom (W : Submodule F K) [Fintype W] : K →+ K where
  toFun x := (subspacePoly (subFinset W)).eval x
  map_zero' := by
    change (subspacePoly (subFinset W)).eval 0 = 0
    exact subspacePoly_eval_zero _ (by simp [W.zero_mem])
  map_add' x y := subspacePoly_eval_add_submodule W x y

/-- **BKR06 Prop 3.2, cardinality.** The subspace polynomial of a finite-dimensional
`𝔽`-subspace `W ⊆ K` has degree `q^{dim_𝔽 W}` where `q = |𝔽|`. This is BKR06's
"`P_L` has exactly `q^{dim L}` roots" — the degree input to the Lemma-3.5 counting. -/
theorem subspacePoly_natDegree_eq_pow_finrank
    [Fintype F] (W : Submodule F K) [Fintype W] :
    (subspacePoly (subFinset W)).natDegree
      = (Fintype.card F) ^ (Module.finrank F W) := by
  rw [subspacePoly_natDegree]
  -- |subFinset W| = |W| = |F|^{finrank F W}
  have hcard : (subFinset W).card = Fintype.card W := by
    rw [subFinset]
    simp [Set.toFinset_card]
  rw [hcard, Module.card_eq_pow_finrank (K := F) (V := W)]

/-! ## Arithmetic bridge toward the BKR06 list-size lower bound (ABF26 T3.12)

The BKR06 list-decoding construction produces, for an `𝔽_q`-subspace `L ⊆ 𝕂 = 𝔽_{q^m}`
of dimension `d`, a Reed–Solomon close-codeword family whose size is at least the number
of roots of the subspace polynomial `P_L`, i.e. `q^d` (Lemma 3.5 of BKR06; the genuine
list-size→roots conversion is the still-external counting step).  ABF26 T3.12 asks for the
list size `≥ q^{(α-β²)·log q}`.  The *purely arithmetic* part — that `q^d` dominates the
target whenever the dimension `d` meets the threshold `d ≥ (α-β²)·log q` — is proven here,
isolating exactly the non-arithmetic residual (the roots→close-codewords count). -/

open scoped Real

/-- **BKR06 degree/count arithmetic bridge.**  The number of roots of the subspace
polynomial of a `d`-dimensional `𝔽_q`-subspace is `(subspacePoly L).natDegree = q^d`, and
this dominates the ABF26 T3.12 target `q^{(α-β²)·log q}` whenever the dimension meets the
threshold `d ≥ (α-β²)·log q` (with `q ≥ 1`).  Pure real-exponent monotonicity; the only
non-arithmetic input is the threshold dimension bound supplied by the caller. -/
theorem subspacePoly_natDegree_ge_target
    [Fintype F] (W : Submodule F K) [Fintype W]
    (q : ℕ) (hq : Fintype.card F = q) (hq1 : (1 : ℝ) ≤ q)
    (target : ℝ) (hthr : target ≤ (Module.finrank F W : ℝ)) :
    (q : ℝ) ^ target
      ≤ ((subspacePoly (subFinset W)).natDegree : ℝ) := by
  rw [subspacePoly_natDegree_eq_pow_finrank, hq]
  rw [Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) (Module.finrank F W)]
  exact Real.rpow_le_rpow_of_exponent_le hq1 hthr

end BKR06

-- Axiom audit (in-file, on the freshly elaborated declarations).
#print axioms BKR06.subspacePoly_eval_add
#print axioms BKR06.subspacePoly_comp_add_left_mem
#print axioms BKR06.subspacePoly_isRoot_iff
#print axioms BKR06.subspacePoly_natDegree
#print axioms BKR06.subspacePoly_eval_add_submodule
#print axioms BKR06.subspacePolyHom
#print axioms BKR06.subspacePoly_natDegree_eq_pow_finrank
#print axioms BKR06.subspacePoly_natDegree_ge_target
