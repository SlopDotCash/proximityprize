/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SbetaPackaging
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorDegreeOverRatFunc

/-!
# The per-coordinate kill in budget form (#302, hypothesis R2)

BCIKS20 Claim 5.10's second half — the named open residual `CoordinateUpgrade` — needs, at a
rich coordinate `x`, that the element `B := γ(x) − w(x,Z)` vanish once its `π_z`-fibers vanish
at more than threshold-many places.  The paper kills `B` by the Claim A.2 `Λ`-weight recursion;
the in-tree refutations kill budget-free `Λ`-carvings.  This file lands the **R2 route**: the
kill needs NO recursion — only a `Z`-degree budget on the canonical representative — because
the in-tree `Lemma_A_1` already contains the Sylvester bound
`deg_Z res_T(β, H̃) ≤ Λ(β)·d_H`, and `Λ` of a budgeted representative is itself elementary.

## Part 1 — the `𝒪`-level kill (`CoordinateKill`)

* `weight_Λ_le_of_budgets` / `weight_Λ_over_𝒪_le_of_coeff_budget` — the `Λ`-weight of an
  element whose canonical representative has coefficient `Z`-degrees `≤ b` is at most
  `(d_H − 1)·(D + 1 − d_H) + b`: **the weight is not recursive data, it is read off the
  budget** (this is the precise sense in which the A.2 recursion is bypassed);
* `eq_zero_of_coeff_budget_of_many_vanishing` — the budget form of Lemma A.1: fibers vanishing
  at more than `((d_H−1)·(D+1−d_H) + b)·d_H` places kill a budgeted element *in `𝒪`* (not just
  its embedding — injectivity is composed in);
* **`eq_section_of_many_fiber_agreements`** — THE key lemma (Claim 5.10's per-coordinate
  output shape): an `𝒪`-element whose `π_z`-fibers agree with the values of a `Z`-polynomial
  `w` of degree `≤ dw` at more than `((d_H−1)·(D+1−d_H) + max b dw)·d_H` places **is** the
  section `mk (C w)`;
* `fiber_eq_section_everywhere_of_many_agreements` — the upgrade: thereafter EVERY fiber (at
  every place, every root) agrees — the witness-set-majority caveat is removed, which is
  exactly the gap between `capture_on_rich_subcell` and `CoordinateUpgrade`.

## Part 2 — the elementary per-factor kill (`FactorKill`), sharper threshold

At a fixed coordinate the branch data is a *polynomial* fiber factor, and there the kill is
elementary — no `𝒪`, no resultant, no monicization:

* `section_root_of_many_agreements` — flat-budget defect count: a factor `Hp` with coefficient
  `Z`-degrees `≤ B` agreeing with `w` (degree `≤ dw`) at more than `B + deg_Y Hp · dw` scalars
  has `w` as an identical root (`Hp(w(Z), Z) = 0`);
* **`fiber_root_eq_section_of_irreducible_of_many_agreements`** — the kill: an *irreducible*
  such factor is `c·(Y − w(Z))`, hence **its every fiber root at every scalar equals the
  section value** — agreement at `> B + d·dw` places upgrades to agreement everywhere;
* `coeff_budget_of_dvd` — the budget supply: divisors inherit flat coefficient budgets, so the
  sloped-interpolant budget (`GSInterpolantSloped`, landed) supplies `B = D_YZ` for every
  fiber factor — **no Claim A.2 input anywhere in the budget chain**;
* `exists_witness_rich_factor` — the pigeonhole feeder: if the fold agreements on a witness
  set `W` exceed `(#factors)·τ`, some irreducible factor carries `> τ` of them.

## The honest residual (falsification analysis of R2)

R2 claimed the coefficient budget for `γ(x) − w(x,Z)` might require the A.2 recursion.  It
does **not**: at a fixed coordinate every object in the kill is a fiber-factor polynomial, and
its budget is inherited from the interpolant by divisibility (`coeff_budget_of_dvd`).  What
the kill *does* still need — and what neither the budgets nor this file supplies — is the
**assignment coherence**: that each *unwitnessed* cell scalar's decode value at the coordinate
roots in a *witness-rich* factor.  Witnessed scalars root in rich factors by construction
(pigeonhole, `exists_witness_rich_factor`); a rogue scalar whose decode roots only in a factor
carrying `≤ B + d·dw` witnessed agreements escapes every budget argument, and is excluded in
the paper only by the global single-branch capture (all decodes are fibers of ONE branch —
the in-tree `GSPerScalarCapture`/section-factor lane, NOT the weight recursion).  So the
A.2-free reduction is: `CoordinateUpgrade ⟸ per-coordinate witness-rich factor assignment`,
with the latter as the new named residual (see `Hab25CoordinateUpgradeWeld`).

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, Claim 5.10, Appendix A (Lemma A.1, Claim A.2).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

open Polynomial Polynomial.Bivariate Ideal BCIKS20AppendixA

namespace ArkLib

/-! ## Part 1 — the `𝒪`-level kill in canonical-representative budget form -/

namespace CoordinateKill

variable {F : Type} [Field F]

/-- **The `Λ`-weight is read off the budgets** — no recursion: if every monomial of `f` has
`Y`-exponent `≤ d` and coefficient `Z`-degree `≤ b`, then
`Λ(f) ≤ d·(D + 1 − deg_Y H) + b`. -/
lemma weight_Λ_le_of_budgets {f H : F[X][Y]} {D d b : ℕ}
    (hdeg : ∀ n ∈ f.support, n ≤ d)
    (hb : ∀ n, (f.coeff n).natDegree ≤ b) :
    weight_Λ f H D ≤
      (WithBot.some (d * (D + 1 - Bivariate.natDegreeY H) + b) : WithBot ℕ) := by
  rw [weight_Λ_le_iff]
  intro n hn
  have h1 := hdeg n hn
  have h2 := hb n
  have h3 := Nat.mul_le_mul_right (D + 1 - Bivariate.natDegreeY H) h1
  omega

/-- The `𝒪`-level budget bound: an element whose canonical representative has coefficient
`Z`-degrees `≤ b` has `Λ`-weight `≤ (d_H − 1)·(D + 1 − d_H) + b` — the `Y`-exponent budget
`d_H − 1` is automatic from the canonical reduction. -/
lemma weight_Λ_over_𝒪_le_of_coeff_budget {H : F[X][Y]} (hH : 0 < H.natDegree)
    (β : 𝒪 H) {D b : ℕ}
    (hb : ∀ n, ((canonicalRepOf𝒪 hH β).coeff n).natDegree ≤ b) :
    weight_Λ_over_𝒪 hH β D ≤
      (WithBot.some ((H.natDegree - 1) * (D + 1 - Bivariate.natDegreeY H) + b)
        : WithBot ℕ) := by
  rw [weight_Λ_over_𝒪]
  refine weight_Λ_le_of_budgets ?_ hb
  intro n hn
  have hne : canonicalRepOf𝒪 hH β ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp at hn
  have hnat : (canonicalRepOf𝒪 hH β).natDegree < H.natDegree := by
    have hlt := Polynomial.natDegree_lt_natDegree hne (canonicalRepOf𝒪_degree_lt hH β)
    rwa [natDegree_H_tilde' hH] at hlt
  have hsupp := Polynomial.le_natDegree_of_mem_supp n hn
  omega

/-- Multiplication by a `ℕ`-coercion is monotone through a `WithBot ℕ` bound. -/
private lemma withBot_mul_coe_le {x : WithBot ℕ} {W : ℕ} (d : ℕ)
    (hx : x ≤ (WithBot.some W : WithBot ℕ)) :
    x * (WithBot.some d : WithBot ℕ) ≤ (WithBot.some (W * d) : WithBot ℕ) := by
  rcases eq_or_ne x ⊥ with rfl | hxb
  · rcases eq_or_ne d 0 with rfl | hd
    · rw [Nat.mul_zero, WithBot.coe_zero, mul_zero]
    · rw [WithBot.bot_mul (fun h => hd (WithBot.coe_eq_zero.mp h))]
      exact bot_le
  · obtain ⟨a, rfl⟩ := WithBot.ne_bot_iff_exists.mp hxb
    have ha : a ≤ W := WithBot.coe_le_coe.mp hx
    rw [← WithBot.coe_mul]
    exact WithBot.coe_le_coe.mpr (Nat.mul_le_mul_right d ha)

/-- **The budget form of Lemma A.1, concluded in `𝒪`.**  An element whose canonical
representative carries the coefficient `Z`-degree budget `b`, and whose `π_z`-fibers vanish at
more than `((d_H − 1)·(D + 1 − d_H) + b)·d_H` places, is zero — Lemma A.1 with the `Λ`-weight
hypothesis replaced by the elementary budget, and the conclusion pulled back through the
injective embedding `𝒪 ↪ 𝕃`. -/
theorem eq_zero_of_coeff_budget_of_many_vanishing {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) {D b : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hb : ∀ n, ((canonicalRepOf𝒪 hH β).coeff n).natDegree ≤ b)
    {S : Finset F}
    (hS : ∀ z ∈ S, ∃ root : rationalRoot (H_tilde' H) z, π_z z root β = 0)
    (hcard : ((H.natDegree - 1) * (D + 1 - Bivariate.natDegreeY H) + b) * H.natDegree
      < S.card) :
    β = 0 := by
  have hTsub : (↑S : Set F) ⊆ S_β β := fun z hz => hS z (Finset.mem_coe.mp hz)
  have hwt := weight_Λ_over_𝒪_le_of_coeff_budget hH β (D := D) hb
  have hmul := withBot_mul_coe_le H.natDegree hwt
  have hlt : (↑S.card : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree := by
    rw [gt_iff_lt]
    simp only [Nat.cast_withBot]
    exact lt_of_le_of_lt hmul (WithBot.coe_lt_coe.mpr hcard)
  have hemb := ArkLib.embedding_eq_zero_of_finset_subset_S_β hH β D hD hTsub hlt
  have h0 : embeddingOf𝒪Into𝕃 H β = embeddingOf𝒪Into𝕃 H 0 := by
    rw [hemb, RingHom.map_zero]
  exact embeddingOf𝒪Into𝕃_injective hH h0

/-- **THE PER-COORDINATE KILL (the key lemma of hypothesis R2).**  An `𝒪`-element whose
`π_z`-fibers agree with the values of a `Z`-polynomial `w` of degree `≤ dw` at more than
`((d_H − 1)·(D + 1 − d_H) + max b dw)·d_H` places **is** the section `mk (C w)` — BCIKS20
Claim 5.10's per-coordinate output `γ(x) = w(x, Z)`, proven with no Claim A.2 recursion:
the difference `β − mk (C w)` keeps the coefficient budget, its fibers vanish on the
agreement set, and the budget-form Lemma A.1 kills it. -/
theorem eq_section_of_many_fiber_agreements {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) {D b : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hb : ∀ n, ((canonicalRepOf𝒪 hH β).coeff n).natDegree ≤ b)
    {w : F[X]} {dw : ℕ} (hw : w.natDegree ≤ dw)
    {S : Finset F}
    (hS : ∀ z ∈ S, ∃ root : rationalRoot (H_tilde' H) z, π_z z root β = w.eval z)
    (hcard : ((H.natDegree - 1) * (D + 1 - Bivariate.natDegreeY H) + max b dw) * H.natDegree
      < S.card) :
    β = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C w) := by
  classical
  set wO : 𝒪 H := Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C w) with hwO
  -- the canonical representative of the difference is the difference of representatives
  have hCw_deg : (Polynomial.C w : F[X][Y]).degree < (H_tilde' H).degree := by
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero, natDegree_H_tilde' hH]
    exact_mod_cast hH
  have hrepw : canonicalRepOf𝒪 hH (β - wO) = canonicalRepOf𝒪 hH β - Polynomial.C w := by
    have h1 : β - wO = Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (canonicalRepOf𝒪 hH β - Polynomial.C w) := by
      rw [RingHom.map_sub, mk_canonicalRepOf𝒪]
    rw [h1, canonicalRepOf𝒪_mk]
    refine (Polynomial.modByMonic_eq_self_iff (H_tilde'_monic H hH)).2 ?_
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
    exact max_lt (canonicalRepOf𝒪_degree_lt hH β) hCw_deg
  -- the difference keeps the coefficient budget
  have hb' : ∀ n, ((canonicalRepOf𝒪 hH (β - wO)).coeff n).natDegree ≤ max b dw := by
    intro n
    rw [hrepw, Polynomial.coeff_sub]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le_max (hb n) ?_
    by_cases hn : n = 0
    · subst hn
      rw [Polynomial.coeff_C_zero]
      exact hw
    · rw [Polynomial.coeff_C, if_neg hn]
      simp
  -- the fibers of the difference vanish on the agreement set
  have hvan : ∀ z ∈ S, ∃ root : rationalRoot (H_tilde' H) z, π_z z root (β - wO) = 0 := by
    intro z hz
    obtain ⟨root, hroot⟩ := hS z hz
    refine ⟨root, ?_⟩
    rw [RingHom.map_sub, hroot, hwO, π_z_mk, Polynomial.evalEval_C, sub_self]
  -- fire the budget-form Lemma A.1
  have h0 : β - wO = 0 :=
    eq_zero_of_coeff_budget_of_many_vanishing hH (β - wO) hD hb' hvan hcard
  rw [hwO] at h0 ⊢
  exact sub_eq_zero.mp h0

/-- Fibers of a `Z`-polynomial section are its values — the trivial direction. -/
lemma fiber_eq_section_of_eq_section {H : F[X][Y]} {w : F[X]} (β : 𝒪 H)
    (hβ : β = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C w))
    (z : F) (root : rationalRoot (H_tilde' H) z) :
    π_z z root β = w.eval z := by
  rw [hβ, π_z_mk, Polynomial.evalEval_C]

/-- **The coordinate upgrade, `𝒪`-level**: many fiber agreements upgrade to agreement at
EVERY place and EVERY root — the witness-set-majority caveat of the Step-7 counting is
removed, which is exactly the content `CoordinateUpgrade` (Claim 5.10) adds over
`capture_on_rich_subcell`. -/
theorem fiber_eq_section_everywhere_of_many_agreements {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) {D b : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hb : ∀ n, ((canonicalRepOf𝒪 hH β).coeff n).natDegree ≤ b)
    {w : F[X]} {dw : ℕ} (hw : w.natDegree ≤ dw)
    {S : Finset F}
    (hS : ∀ z ∈ S, ∃ root : rationalRoot (H_tilde' H) z, π_z z root β = w.eval z)
    (hcard : ((H.natDegree - 1) * (D + 1 - Bivariate.natDegreeY H) + max b dw) * H.natDegree
      < S.card) :
    ∀ (z : F) (root : rationalRoot (H_tilde' H) z), π_z z root β = w.eval z :=
  fun z root => fiber_eq_section_of_eq_section β
    (eq_section_of_many_fiber_agreements hH β hD hb hw hS hcard) z root

end CoordinateKill

/-! ## Part 2 — the elementary per-factor kill (sharper threshold, no `𝒪`) -/

namespace FactorKill

variable {F : Type} [Field F]

/-- Evaluating `Y` at a section then specializing `Z` equals specializing first and
evaluating at the specialized section value. -/
lemma eval_section_specializes (G : F[X][Y]) (w : F[X]) (z : F) :
    (Polynomial.eval w G).eval z =
      Polynomial.eval (w.eval z) (G.map (Polynomial.evalRingHom z)) := by
  have h := Polynomial.hom_eval₂ G (RingHom.id F[X]) (Polynomial.evalRingHom z) w
  rw [RingHom.comp_id] at h
  rw [show Polynomial.eval w G = Polynomial.eval₂ (RingHom.id F[X]) w G from rfl,
    Polynomial.eval_map]
  exact h

/-- **Flat-budget section capture.**  A section `w` of degree `≤ dw` agreeing with a root of
the specialized factor at more than `B + deg_Y·dw` scalars is an identical root: the defect
`Hp(w(Z), Z)` has degree `≤ B + deg_Y·dw` and vanishes at too many points.  (The flat-budget
sibling of the sloped `fold_divides_fiber_of_many_agreements`; the flat budget is what
divisors of the interpolant inherit.) -/
theorem section_root_of_many_agreements {Hp : F[X][Y]} {B dw : ℕ}
    (hB : ∀ k, (Hp.coeff k).natDegree ≤ B)
    {w : F[X]} (hw : w.natDegree ≤ dw)
    (S : Finset F) (hcard : B + Hp.natDegree * dw < S.card)
    (hvan : ∀ z ∈ S, (Hp.map (Polynomial.evalRingHom z)).eval (w.eval z) = 0) :
    Polynomial.eval w Hp = 0 := by
  classical
  set δ : F[X] := Polynomial.eval w Hp with hδ
  have hδdeg : δ.natDegree ≤ B + Hp.natDegree * dw := by
    rw [hδ, Polynomial.eval_eq_sum_range]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 := hB k
    have h2 : (w ^ k).natDegree ≤ k * dw :=
      le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left k hw)
    have hkle : k ≤ Hp.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h3 : k * dw ≤ Hp.natDegree * dw := Nat.mul_le_mul_right dw hkle
    omega
  have hδvan : ∀ z ∈ S, δ.eval z = 0 := by
    intro z hz
    rw [hδ, eval_section_specializes]
    exact hvan z hz
  by_contra hδ0
  have hsub : S ⊆ δ.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hδ0]
    exact hδvan z hz
  have hle : S.card ≤ B + Hp.natDegree * dw :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Multiset.toFinset_card_le _)
        (le_trans (Polynomial.card_roots' _) hδdeg))
  omega

/-- **THE ELEMENTARY PER-FACTOR KILL.**  An irreducible factor with flat coefficient budget
`B` agreeing with the section `w` at more than `B + deg_Y·dw` scalars is `c·(Y − w(Z))` —
hence **its every fiber root, at every scalar, equals the section value**.  This upgrades
witnessed agreement to agreement everywhere with no `Λ`-weight, no resultant, and no
monicization: irreducibility plus the factor theorem force fiber-linearity. -/
theorem fiber_root_eq_section_of_irreducible_of_many_agreements
    {Hp : F[X][Y]} (hirr : Irreducible Hp) {B dw : ℕ}
    (hB : ∀ k, (Hp.coeff k).natDegree ≤ B)
    {w : F[X]} (hw : w.natDegree ≤ dw)
    (S : Finset F) (hcard : B + Hp.natDegree * dw < S.card)
    (hvan : ∀ z ∈ S, (Hp.map (Polynomial.evalRingHom z)).eval (w.eval z) = 0) :
    ∀ z y : F, (Hp.map (Polynomial.evalRingHom z)).eval y = 0 → y = w.eval z := by
  have hroot : Polynomial.eval w Hp = 0 :=
    section_root_of_many_agreements hB hw S hcard hvan
  have hdvd : (Polynomial.X - Polynomial.C w) ∣ Hp := Polynomial.dvd_iff_isRoot.mpr hroot
  obtain ⟨q, hq⟩ := hdvd
  have hXw_nu : ¬ IsUnit (Polynomial.X - Polynomial.C w) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at h1
    exact one_ne_zero h1
  have hqu : IsUnit q := (hirr.isUnit_or_isUnit hq).resolve_left hXw_nu
  intro z y hy
  have hmap : Hp.map (Polynomial.evalRingHom z)
      = (Polynomial.X - Polynomial.C (w.eval z)) * q.map (Polynomial.evalRingHom z) := by
    rw [hq, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [hmap, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hy
  have hqz : IsUnit ((q.map (Polynomial.evalRingHom z)).eval y) := by
    have h1 : IsUnit (q.map (Polynomial.evalRingHom z)) := by
      have := hqu.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))
      rwa [Polynomial.coe_mapRingHom] at this
    have := h1.map (Polynomial.evalRingHom y)
    rwa [Polynomial.coe_evalRingHom] at this
  rcases mul_eq_zero.mp hy with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hqz.ne_zero

/-- **The budget supply**: divisors inherit flat coefficient budgets — so the fiber factors
carry the (landed) sloped-interpolant budget `B = D_YZ` with no Claim A.2 input. -/
lemma coeff_budget_of_dvd {G Hp : F[X][Y]} (hdvd : Hp ∣ G) (hG : G ≠ 0)
    {B : ℕ} (hB : ∀ k, (G.coeff k).natDegree ≤ B) (k : ℕ) :
    (Hp.coeff k).natDegree ≤ B := by
  refine le_trans (Polynomial.Bivariate.coeff_natDegree_le_degreeX_of_dvd hdvd hG k) ?_
  exact Finset.sup_le fun m _ => hB m

/-- **The pigeonhole feeder.**  If the fold agreements on a witness set `W` exceed
`(#factors)·τ`, some factor of the fiber carries more than `τ` of them — the witness-rich
factor exists unconditionally. -/
theorem exists_witness_rich_factor {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {Hf : ι → F[X][Y]} {G : F[X][Y]} (hG : G = ∏ i ∈ s, Hf i)
    {w : F[X]} (W : Finset F) (τ : ℕ)
    (hvan : ∀ ζ ∈ W, (G.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)
    (hcount : s.card * τ < W.card) :
    ∃ i ∈ s, τ < (W.filter (fun ζ =>
      ((Hf i).map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)).card := by
  classical
  by_contra hcon
  push Not at hcon
  have hcover : W ⊆ s.biUnion (fun i => W.filter (fun ζ =>
      ((Hf i).map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)) := by
    intro ζ hζ
    have h0 := hvan ζ hζ
    rw [hG, ← Polynomial.coe_mapRingHom, map_prod, Polynomial.eval_prod] at h0
    obtain ⟨i, hi, hzero⟩ := Finset.prod_eq_zero_iff.mp h0
    rw [Polynomial.coe_mapRingHom] at hzero
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hζ, hzero⟩⟩
  have hcard := Finset.card_le_card hcover
  have hsum : ∑ i ∈ s, (W.filter (fun ζ =>
      ((Hf i).map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)).card
      ≤ s.card * τ := by
    calc ∑ i ∈ s, (W.filter (fun ζ =>
          ((Hf i).map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)).card
        ≤ ∑ _i ∈ s, τ := Finset.sum_le_sum fun i hi => hcon i hi
      _ = s.card * τ := by rw [Finset.sum_const, smul_eq_mul]
  have hbi := Finset.card_biUnion_le (s := s) (t := fun i => W.filter (fun ζ =>
    ((Hf i).map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0))
  omega

end FactorKill

end ArkLib

/-! ## Axiom audit — all kernel-clean. -/
#print axioms ArkLib.CoordinateKill.weight_Λ_le_of_budgets
#print axioms ArkLib.CoordinateKill.weight_Λ_over_𝒪_le_of_coeff_budget
#print axioms ArkLib.CoordinateKill.eq_zero_of_coeff_budget_of_many_vanishing
#print axioms ArkLib.CoordinateKill.eq_section_of_many_fiber_agreements
#print axioms ArkLib.CoordinateKill.fiber_eq_section_everywhere_of_many_agreements
#print axioms ArkLib.FactorKill.section_root_of_many_agreements
#print axioms ArkLib.FactorKill.fiber_root_eq_section_of_irreducible_of_many_agreements
#print axioms ArkLib.FactorKill.coeff_budget_of_dvd
#print axioms ArkLib.FactorKill.exists_witness_rich_factor
