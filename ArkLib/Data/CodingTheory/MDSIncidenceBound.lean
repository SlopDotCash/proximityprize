/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The higher-order-MDS incidence bound: general dimension `d` (#389)

The window-interior δ\* (the proximity-prize core) reduces to the interleaved-list **count** bound
beyond Johnson, which in the affinely-dependent regime is a **hyperplane incidence count** over the
linear code.  `LineListBound.lean` proves the dimension-1 (line) slice unconditionally and
`PlaneIncidenceBound.lean` the dimension-2 (plane) slice from order-2 MDS.  This file proves the
**general dimension-`d`** statement, which subsumes both:

`mds_incidence_card_le` — parameterize a `d`-dimensional affine family of codewords by `p ∈ Fᵈ`,
position `i` agreeing when `N i ⬝ᵥ p = c i` (here the row `N i ∈ Fᵈ` is the `i`-th hyperplane
normal).  If the `d × n` normal matrix is **order-`d` MDS** — every `d` columns independent, i.e.
`det (N ∘ σ) ≠ 0` for every injective `σ : Fin d → ι` — then any set of "heavy" parameters (each
agreeing on `≥ k` positions) satisfies

`|Heavy| · C(k,d) ≤ C(n,d)`,  i.e.  `|Heavy| ≤ C(n,d) / C(k,d)`.

Mechanism (Cramer uniqueness + double counting): each position is an affine hyperplane in `Fᵈ`;
order-`d` MDS makes any `d` of them meet in exactly one point (the `d × d` system is invertible),
so each unordered `d`-subset of positions is charged to at most one heavy parameter, giving
`∑ₚ C(|fibreₚ|, d) ≤ C(n, d)`.

This is exactly "higher-order MDS ⟹ beyond-Johnson interleaved list decoding", proven
unconditionally from the order-`d` MDS hypothesis, in full generality.  Specializations: `d = 1`
recovers `|Heavy| · k ≤ n` (the line bound, when all normals are nonzero); `d = 2` recovers the
plane bound `|Heavy| · C(k,2) ≤ C(n,2)`.  The remaining open part of the prize core is producing
the order-`d` MDS certificate itself for the *explicit* smooth Reed–Solomon evaluation points — the
GM-MDS / higher-order-MDS question.  `vandermonde_incidence_card_le` discharges the order-`d` MDS
hypothesis unconditionally for the degree-`<d` Reed–Solomon evaluation map at distinct points (the
Vandermonde determinant), giving the list bound `|Heavy| · C(k,d) ≤ C(n,d)` outright there.
Axiom-clean.
-/

open Finset Matrix

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **The higher-order-MDS incidence list bound (general dimension `d`).**
Heavy parameters of a `d`-dimensional affine codeword family, each agreeing on `≥ k` positions
`N i ⬝ᵥ p = c i`, number at most `C(n,d) / C(k,d)` when the normal matrix is order-`d` MDS
(`det (N ∘ σ) ≠ 0` for every injective `σ : Fin d → ι`).  The `d` independent hyperplanes through
a heavy point meet in exactly one point (Cramer), so each `d`-subset of agreeing positions is
charged to one heavy parameter: `∑ₚ C(|fibreₚ|,d) ≤ C(n,d)`.  Subsumes the line (`d=1`) and plane
(`d=2`) bounds. -/
theorem mds_incidence_card_le {d : ℕ} (N : ι → (Fin d → F)) (c : ι → F) {k : ℕ}
    (hmds : ∀ σ : Fin d → ι, Function.Injective σ →
      (Matrix.of (fun b => N (σ b)) : Matrix (Fin d) (Fin d) F).det ≠ 0)
    (Heavy : Finset (Fin d → F))
    (hHeavy : ∀ p ∈ Heavy,
      k ≤ (univ.filter (fun i => N i ⬝ᵥ p = c i)).card) :
    Heavy.card * k.choose d ≤ (Fintype.card ι).choose d := by
  classical
  set S : (Fin d → F) → Finset ι :=
    fun p => univ.filter (fun i => N i ⬝ᵥ p = c i) with hS
  -- `d` positions with independent normals meet in at most one parameter (Cramer uniqueness)
  have huniq : ∀ (p p' : Fin d → F) (σ : Fin d → ι), Function.Injective σ →
      (∀ b, σ b ∈ S p) → (∀ b, σ b ∈ S p') → p = p' := by
    intro p p' σ hσ hp hp'
    set M : Matrix (Fin d) (Fin d) F := Matrix.of (fun b => N (σ b)) with hMdef
    have hdetU : IsUnit M.det := isUnit_iff_ne_zero.mpr (hmds σ hσ)
    have hMp : M.mulVec p = M.mulVec p' := by
      funext b
      have hpb := hp b
      have hp'b := hp' b
      simp only [hS, mem_filter, mem_univ, true_and] at hpb hp'b
      change N (σ b) ⬝ᵥ p = N (σ b) ⬝ᵥ p'
      rw [hpb, hp'b]
    have step : M⁻¹.mulVec (M.mulVec p) = M⁻¹.mulVec (M.mulVec p') := by rw [hMp]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hdetU,
      Matrix.one_mulVec, Matrix.one_mulVec] at step
  have htarget : (univ.powersetCard d : Finset (Finset ι)).card = (Fintype.card ι).choose d := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  have hsig : (Heavy.sigma (fun p => (S p).powersetCard d)).card
      = ∑ p ∈ Heavy, (S p).card.choose d := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun p _ => Finset.card_powersetCard d (S p))
  -- charge each (heavy param, agreeing `d`-subset) to that subset; order-`d` MDS fixes the param
  have hcard_le : (∑ p ∈ Heavy, (S p).card.choose d) ≤ (Fintype.card ι).choose d := by
    rw [← hsig, ← htarget]
    apply Finset.card_le_card_of_injOn (fun x => x.2)
    · rintro ⟨p, s⟩ hps
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard, Finset.subset_univ,
        true_and] at hps ⊢
      exact hps.2.2
    · rintro ⟨p, s⟩ hps ⟨p', s'⟩ hps' heq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hps hps'
      have hss : s = s' := heq
      subst hss
      -- extract an injective `σ : Fin d → ι` enumerating the `d`-subset `s`
      set e := s.equivFinOfCardEq hps.2.2 with he
      set σ : Fin d → ι := fun b => (e.symm b : ι) with hσdef
      have hσinj : Function.Injective σ := fun b b' h =>
        e.symm.injective (Subtype.ext h)
      have hσs : ∀ b, σ b ∈ s := fun b => (e.symm b).2
      have hpp : p = p' :=
        huniq p p' σ hσinj (fun b => hps.2.1 (hσs b)) (fun b => hps'.2.1 (hσs b))
      subst hpp; rfl
  have hlb : Heavy.card * k.choose d ≤ ∑ p ∈ Heavy, (S p).card.choose d := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    exact Nat.choose_le_choose d (hHeavy p hp)
  exact le_trans hlb hcard_le

omit [DecidableEq ι] in
/-- **The Vandermonde (degree-`<d` Reed–Solomon) incidence list bound, unconditional.**
Instantiate `mds_incidence_card_le` with the degree filtration `N i = (1, xᵢ, …, xᵢ^{d-1})`: a
heavy parameter is a degree-`<d` polynomial `p` (read off its coefficient vector) agreeing with
`c` on `≥ k` of the distinct evaluation points `x i`.  The order-`d` MDS hypothesis is then the
**Vandermonde determinant** `∏_{i<j} (x_{σ j} − x_{σ i}) ≠ 0`, automatic from distinctness — so for
distinct points the list bound `|Heavy| · C(k,d) ≤ C(n,d)` holds with *no* extra hypothesis. This
is the affinely-independent (primal-RS) corner of the prize core, recovered concretely. -/
theorem vandermonde_incidence_card_le {d : ℕ} (x : ι → F) (hx : Function.Injective x)
    (c : ι → F) {k : ℕ} (Heavy : Finset (Fin d → F))
    (hHeavy : ∀ p ∈ Heavy,
      k ≤ (univ.filter (fun i => (fun b : Fin d => x i ^ (b : ℕ)) ⬝ᵥ p = c i)).card) :
    Heavy.card * k.choose d ≤ (Fintype.card ι).choose d := by
  refine mds_incidence_card_le (fun i b => x i ^ (b : ℕ)) c (fun σ hσ => ?_) Heavy hHeavy
  have hv : (Matrix.of (fun b => (fun a : Fin d => x (σ b) ^ (a : ℕ))) :
      Matrix (Fin d) (Fin d) F) = Matrix.vandermonde (fun b => x (σ b)) := rfl
  rw [hv, Matrix.det_vandermonde, Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [sub_ne_zero]
  intro h
  exact absurd (hσ (hx h)) (Finset.mem_Ioi.mp hj).ne'
