/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.HenselSeriesCoeff
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra

/-!
# Hensel branch rigidity: a fiber point determines the polynomial branch

This is the first **Step S6** brick of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`): at a good base point `x₀` (the
S5 output: the factor's specialization is *separable*), a polynomial factor admits **at most
one polynomial branch through each fiber point**. This is the uniqueness half of the Hensel
lift, transported from the in-tree power-series engine
(`ProximityPrize.HenselSeriesCoeff.root_unique_seriesCoeff`) along the **recentering
embedding** `R[X] →+* R⟦X⟧`, `q(X) ↦ q(x₀ + X)`:

* `recenter x₀` — the recentering ring hom (Taylor expansion at `x₀` viewed in `R⟦X⟧`),
  with `constantCoeff (recenter x₀ q) = q.eval x₀` and injectivity;
* `branch_eq_of_fiber_eq` — if `p, p'` are polynomial roots of `G : R[X][Y]`
  (`(Y − C p) ∣ G`, the decoded-branch shape), the specialization `G(x₀, ·)` has a *unit*
  derivative at the common fiber value `p(x₀) = p'(x₀)`, then `p = p'`;
* `branch_eq_of_fiber_eq_of_separable` — over a field, the unit-derivative hypothesis is
  exactly the S5 payload: `G(x₀,·)` separable and the fiber value is a root;
* `branch_eq_of_fiber_eq_expand` — the characteristic-`p` factor shape: if the factor is
  `R = G(Y^{q^e})` (`expand` of its separable core, the
  `GSSeparableCoreDescent.lean` output), branches of `R` through a common fiber point
  coincide — the `q^e`-power map folds branches onto core branches, Hensel rigidity applies
  to the core, and the Frobenius (`sub_pow_expChar_pow`) recovers injectivity.

Why this is the right S6 entry point: the Hab25/BCIKS20 unique-affine-pair argument runs the
Hensel lift at `x₀` for each irreducible factor and uses that the (finitely many) decoded
branches are *pinned* by their fiber values — existence of the lift gives the branch, and
THIS rigidity gives its uniqueness. Combined with the residual-free branch separation
(`gs_decoded_eval_injective`) and the S5 good point, the decoded list at `x₀` injects into
the simple roots of the specialized cores.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace ProximityPrize.HenselBranchRigidity

variable {R : Type*} [CommRing R]

/-! ## The recentering embedding `R[X] →+* R⟦X⟧` -/

/-- The **recentering ring hom** at `x₀`: `q(X) ↦ q(x₀ + X)`, viewed as a power series.
Concretely the Taylor expansion of `q` at `x₀`, coerced into `R⟦X⟧`. -/
noncomputable def recenter (x₀ : R) : R[X] →+* PowerSeries R :=
  (Polynomial.coeToPowerSeries.ringHom).comp
    ((Polynomial.aeval (Polynomial.X + Polynomial.C x₀)).toRingHom)

lemma recenter_apply (x₀ : R) (q : R[X]) :
    recenter x₀ q = ((Polynomial.taylor x₀ q : R[X]) : PowerSeries R) := by
  have h : Polynomial.aeval (Polynomial.X + Polynomial.C x₀) q = Polynomial.taylor x₀ q := by
    rw [Polynomial.taylor_apply, Polynomial.aeval_def, Polynomial.algebraMap_eq]
    rfl
  simp only [recenter, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.coeToPowerSeries.ringHom_apply, h]

/-- The recentering hom is injective: Taylor expansion is injective, and so is the
polynomial-to-power-series coercion. -/
lemma recenter_injective (x₀ : R) : Function.Injective (recenter x₀) := by
  intro a b hab
  rw [recenter_apply, recenter_apply] at hab
  have hcoe : (Polynomial.taylor x₀ a : R[X]) = Polynomial.taylor x₀ b := by
    ext n
    have := congrArg (PowerSeries.coeff n) hab
    simpa [Polynomial.coeff_coe] using this
  exact Polynomial.taylor_injective x₀ hcoe

/-- The constant coefficient of the recentered polynomial is its value at the center. -/
@[simp] lemma constantCoeff_recenter (x₀ : R) (q : R[X]) :
    PowerSeries.constantCoeff (recenter x₀ q) = q.eval x₀ := by
  rw [recenter_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Polynomial.coeff_coe, Polynomial.taylor_coeff_zero]

/-- Recentering intertwines specialization at `x₀` with the power-series constant
coefficient: `constantCoeff ∘ recenter x₀ = evalRingHom x₀`. -/
lemma constantCoeff_comp_recenter (x₀ : R) :
    (PowerSeries.constantCoeff (R := R)).comp (recenter x₀) = Polynomial.evalRingHom x₀ :=
  RingHom.ext fun q => by simp [Polynomial.coe_evalRingHom]

/-! ## Branch rigidity -/

/-- **Hensel branch rigidity (general form).** Let `G : R[X][Y]` and `p, p' : R[X]` be
polynomial roots of `G` in the outer variable (the decoded-branch shape `(Y − C p) ∣ G`).
If `p` and `p'` pass through the same fiber point over `x₀` (`p.eval x₀ = p'.eval x₀`) and
the specialization `G(x₀, ·) ∈ R[Y]` has a **unit derivative** at that point (the root is
simple), then `p = p'`: recentering turns both branches into power-series roots of `G` with
equal constant coefficient, and the in-tree power-series Hensel uniqueness pins them. -/
theorem branch_eq_of_fiber_eq {G : R[X][Y]} {x₀ : R} {p p' : R[X]}
    (hp : Polynomial.eval p G = 0) (hp' : Polynomial.eval p' G = 0)
    (hfiber : p.eval x₀ = p'.eval x₀)
    (hu : IsUnit (Polynomial.eval (p.eval x₀)
      (Polynomial.derivative (G.map (Polynomial.evalRingHom x₀))))) :
    p = p' := by
  classical
  set τ : R[X] →+* PowerSeries R := recenter x₀ with hτ
  -- both branches recenter to power-series roots of `G.map τ`
  have hroot : Polynomial.eval (τ p) (G.map τ) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hp, map_zero]
  have hroot' : Polynomial.eval (τ p') (G.map τ) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hp', map_zero]
  -- the order-0 polynomial of the recentered factor is the specialization at `x₀`
  have hQ₀ : ProximityPrize.HenselSeriesCoeff.Q₀ (G.map τ) =
      G.map (Polynomial.evalRingHom x₀) := by
    rw [ProximityPrize.HenselSeriesCoeff.Q₀, Polynomial.map_map, hτ,
      constantCoeff_comp_recenter]
  -- equal constant coefficients
  have hcc : PowerSeries.constantCoeff (τ p) = PowerSeries.constantCoeff (τ p') := by
    rw [hτ, constantCoeff_recenter, constantCoeff_recenter]
    exact hfiber
  -- the simple-root unit, transported
  have hu' : IsUnit (Polynomial.eval (PowerSeries.constantCoeff (τ p))
      (Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀ (G.map τ)))) := by
    rw [hQ₀, hτ, constantCoeff_recenter]
    exact hu
  -- power-series Hensel uniqueness, then injectivity of recentering
  have := ProximityPrize.HenselSeriesCoeff.root_unique_seriesCoeff hcc hu' hroot hroot'
  exact recenter_injective x₀ this

/-- **Branch rigidity from the S5 payload.** Over a field, if the specialization `G(x₀,·)`
is *separable* (the S5 good-point output) then every fiber value is automatically a simple
point: two decoded branches `(Y − C p) ∣ G`, `(Y − C p') ∣ G` through the same fiber value
over `x₀` coincide. -/
theorem branch_eq_of_fiber_eq_of_separable {K : Type*} [Field K]
    {G : K[X][Y]} {x₀ : K} {p p' : K[X]}
    (hsep : (G.map (Polynomial.evalRingHom x₀)).Separable)
    (hdvd : (Polynomial.X - Polynomial.C p) ∣ G)
    (hdvd' : (Polynomial.X - Polynomial.C p') ∣ G)
    (hfiber : p.eval x₀ = p'.eval x₀) :
    p = p' := by
  have hp : Polynomial.eval p G = 0 := by
    rw [← Polynomial.dvd_iff_isRoot.mp hdvd]
  have hp' : Polynomial.eval p' G = 0 := by
    rw [← Polynomial.dvd_iff_isRoot.mp hdvd']
  -- the fiber value is a root of the specialization
  have hc0 : Polynomial.eval (p.eval x₀) (G.map (Polynomial.evalRingHom x₀)) = 0 := by
    have h2 := Polynomial.eval₂_at_apply (p := G) (Polynomial.evalRingHom x₀) p
    rw [Polynomial.coe_evalRingHom] at h2
    rw [Polynomial.eval_map, h2, hp, Polynomial.eval_zero]
  -- separability makes it a simple root: Bézout for `(g, g')` evaluated at the root
  obtain ⟨a, b, hab⟩ := hsep
  have hu : IsUnit (Polynomial.eval (p.eval x₀)
      (Polynomial.derivative (G.map (Polynomial.evalRingHom x₀)))) := by
    have heval := congrArg (Polynomial.eval (p.eval x₀)) hab
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hc0, mul_zero,
      zero_add, Polynomial.eval_one] at heval
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans heval)
  exact branch_eq_of_fiber_eq hp hp' hfiber hu

/-- **Branch rigidity through the inseparable shell (characteristic `p` factor shape).**
If the factor is `Rf = expand (q^e) G` — a `q`-power expansion of its separable core `G`,
the `GSSeparableCoreDescent` output — and the core's specialization `G(x₀,·)` is separable,
then two decoded branches of `Rf` through the same fiber value over `x₀` coincide: the
`q^e`-power map folds the branches onto branches of the core (where Hensel rigidity
applies), and the Frobenius is injective (`sub_pow_expChar_pow` over the domain `K[X]`). -/
theorem branch_eq_of_fiber_eq_expand {K : Type*} [Field K] (q : ℕ) [ExpChar K q]
    {Rf G : K[X][Y]} {x₀ : K} {p p' : K[X]} (e : ℕ)
    (hexp : Polynomial.expand _ (q ^ e) G = Rf)
    (hsep : (G.map (Polynomial.evalRingHom x₀)).Separable)
    (hdvd : (Polynomial.X - Polynomial.C p) ∣ Rf)
    (hdvd' : (Polynomial.X - Polynomial.C p') ∣ Rf)
    (hfiber : p.eval x₀ = p'.eval x₀) :
    p = p' := by
  haveI : ExpChar K[X] q :=
    expChar_of_injective_ringHom (Polynomial.C_injective (R := K)) q
  -- fold the branches onto the core: `p^{q^e}` is a branch of `G`
  have hpR : Polynomial.eval p Rf = 0 := by
    rw [← Polynomial.dvd_iff_isRoot.mp hdvd]
  have hp'R : Polynomial.eval p' Rf = 0 := by
    rw [← Polynomial.dvd_iff_isRoot.mp hdvd']
  have hpG : (Polynomial.X - Polynomial.C (p ^ q ^ e)) ∣ G := by
    rw [Polynomial.dvd_iff_isRoot]
    have := hpR
    rw [← hexp, Polynomial.expand_eval] at this
    exact this
  have hp'G : (Polynomial.X - Polynomial.C (p' ^ q ^ e)) ∣ G := by
    rw [Polynomial.dvd_iff_isRoot]
    have := hp'R
    rw [← hexp, Polynomial.expand_eval] at this
    exact this
  -- fiber values of the folded branches agree
  have hfib' : (p ^ q ^ e).eval x₀ = (p' ^ q ^ e).eval x₀ := by
    rw [Polynomial.eval_pow, Polynomial.eval_pow, hfiber]
  -- Hensel rigidity on the core
  have hfold : p ^ q ^ e = p' ^ q ^ e :=
    branch_eq_of_fiber_eq_of_separable hsep hpG hp'G hfib'
  -- Frobenius injectivity over the domain `K[X]`
  have hsub : (p - p') ^ q ^ e = 0 := by
    rw [sub_pow_expChar_pow p p' e, hfold, sub_self]
  have : p - p' = 0 := pow_eq_zero_iff (pow_ne_zero e (expChar_pos K q).ne') |>.mp hsub
  exact sub_eq_zero.mp this

/-- **Fiber-evaluation injectivity on the branch set.** At a point `x₀` where the
specialization of `G` is separable, the map `p ↦ p.eval x₀` is injective on the set of
polynomial branches of `G` — so the decoded branches of a factor inject into the (simple)
roots of `G(x₀,·)`. This is the S6 bookkeeping shape: at a good point, branches are pinned
by fiber values. -/
theorem branch_evalAt_injOn {K : Type*} [Field K] {G : K[X][Y]} {x₀ : K}
    (hsep : (G.map (Polynomial.evalRingHom x₀)).Separable) :
    Set.InjOn (fun p : K[X] => p.eval x₀)
      {p : K[X] | (Polynomial.X - Polynomial.C p) ∣ G} := by
  intro p hp p' hp' hfib
  exact branch_eq_of_fiber_eq_of_separable hsep hp hp' hfib

/-! ## Branch existence and per-factor fiber counting -/

/-- Specializing a polynomial branch: if `p` is a polynomial root of `G : R[X][Y]`, then
`p.eval x₀` is a root of the specialization `G(x₀, ·)`. -/
lemma eval_specialization_eq_zero {G : R[X][Y]} {x₀ : R} {p : R[X]}
    (hp : Polynomial.eval p G = 0) :
    Polynomial.eval (p.eval x₀) (G.map (Polynomial.evalRingHom x₀)) = 0 := by
  have h2 := Polynomial.eval₂_at_apply (p := G) (Polynomial.evalRingHom x₀) p
  rw [Polynomial.coe_evalRingHom] at h2
  rw [Polynomial.eval_map, h2, hp, Polynomial.eval_zero]

/-- **Unique Hensel branch through a simple fiber point (existence + uniqueness).** If `c` is
a simple root of the specialization `G(x₀,·)`, there is a **unique** power-series branch
`γ ∈ R⟦T⟧` through `(x₀, c)`: `constantCoeff γ = c` and `γ` is a root of the recentered
factor `G.map (recenter x₀)`. This is the abstract S6 Hensel lift at the good point,
assembled from the in-tree existence and uniqueness engines. -/
theorem existsUnique_branch_series {G : R[X][Y]} {x₀ c : R}
    (hroot : Polynomial.eval c (G.map (Polynomial.evalRingHom x₀)) = 0)
    (hu : IsUnit (Polynomial.eval c
      (Polynomial.derivative (G.map (Polynomial.evalRingHom x₀))))) :
    ∃! γ : PowerSeries R, PowerSeries.constantCoeff γ = c ∧
      Polynomial.eval γ (G.map (recenter x₀)) = 0 := by
  have hQ₀ : ProximityPrize.HenselSeriesCoeff.Q₀ (G.map (recenter x₀)) =
      G.map (Polynomial.evalRingHom x₀) := by
    rw [ProximityPrize.HenselSeriesCoeff.Q₀, Polynomial.map_map, constantCoeff_comp_recenter]
  have hc0 : Polynomial.eval c
      (ProximityPrize.HenselSeriesCoeff.Q₀ (G.map (recenter x₀))) = 0 := by
    rw [hQ₀]; exact hroot
  have hu' : IsUnit (Polynomial.eval c (Polynomial.derivative
      (ProximityPrize.HenselSeriesCoeff.Q₀ (G.map (recenter x₀))))) := by
    rw [hQ₀]; exact hu
  obtain ⟨γ, hγc, hγ⟩ :=
    ProximityPrize.HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff hc0 hu'
  refine ⟨γ, ⟨hγc, hγ⟩, ?_⟩
  rintro γ' ⟨hγ'c, hγ'⟩
  exact ProximityPrize.HenselSeriesCoeff.root_unique_seriesCoeff
    (by rw [hγ'c, hγc]) (by rw [hγ'c]; exact hu') hγ' hγ

/-- **Per-factor fiber count.** At a point `x₀` where the specialization of `G` is separable
and nonzero, any finite set of polynomial branches of `G` injects (via `p ↦ p.eval x₀`,
branch rigidity) into the roots of `G(x₀,·)`, hence has at most `deg_Y G(x₀,·)` elements —
the S6 per-factor list-size bookkeeping. -/
theorem card_branches_le_natDegree {K : Type*} [Field K] {G : K[X][Y]} {x₀ : K}
    (hsep : (G.map (Polynomial.evalRingHom x₀)).Separable)
    (hG0 : G.map (Polynomial.evalRingHom x₀) ≠ 0)
    (Ps : Finset K[X]) (hPs : ∀ p ∈ Ps, (Polynomial.X - Polynomial.C p) ∣ G) :
    Ps.card ≤ (G.map (Polynomial.evalRingHom x₀)).natDegree := by
  classical
  have himg : ∀ p ∈ Ps,
      p.eval x₀ ∈ (G.map (Polynomial.evalRingHom x₀)).roots.toFinset := by
    intro p hp
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hG0, eval_specialization_eq_zero (Polynomial.dvd_iff_isRoot.mp (hPs p hp))⟩
  have hinj : Set.InjOn (fun p : K[X] => p.eval x₀) Ps := fun p hp p' hp' h =>
    branch_eq_of_fiber_eq_of_separable hsep (hPs p hp) (hPs p' hp') h
  calc Ps.card
      = (Ps.image (fun p => p.eval x₀)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (G.map (Polynomial.evalRingHom x₀)).roots.toFinset.card := by
        refine Finset.card_le_card ?_
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
        exact himg p hp
    _ ≤ Multiset.card (G.map (Polynomial.evalRingHom x₀)).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (G.map (Polynomial.evalRingHom x₀)).natDegree := Polynomial.card_roots' _

end ProximityPrize.HenselBranchRigidity

/-! ## Axiom audit — all kernel-clean. -/
#print axioms ProximityPrize.HenselBranchRigidity.recenter_injective
#print axioms ProximityPrize.HenselBranchRigidity.constantCoeff_recenter
#print axioms ProximityPrize.HenselBranchRigidity.branch_eq_of_fiber_eq
#print axioms ProximityPrize.HenselBranchRigidity.branch_eq_of_fiber_eq_of_separable
#print axioms ProximityPrize.HenselBranchRigidity.branch_eq_of_fiber_eq_expand
#print axioms ProximityPrize.HenselBranchRigidity.branch_evalAt_injOn
#print axioms ProximityPrize.HenselBranchRigidity.existsUnique_branch_series
#print axioms ProximityPrize.HenselBranchRigidity.card_branches_le_natDegree
