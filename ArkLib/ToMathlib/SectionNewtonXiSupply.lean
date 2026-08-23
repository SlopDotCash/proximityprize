/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Issue #304 — the section-Newton `ξ̄` supply: simple-root certificates at the decoded section

The elementary route (`PolyRootGradedBound`, `PowerSeriesNewton`) needs, at the seed
`(x₀, v)`, the **slice-derivative reading** `ξ̄ := (∂_T Q).eval v ∈ F[Z]` of the slice
`Q := evalX (C x₀) R ∈ F[Z][T]` to be nonzero — i.e. `v` a *simple* root of `Q` — plus its
per-place nonvanishing `ξ̄(z) ≠ 0` off a counted exceptional set.  Crucially this must NOT go
through `ClaimA2.Hypotheses.separable_evalX` (`F[Z]`-level `Separable`), which is
**unsatisfiable** at every multi-branch slice (F13, `SliceSeparabilityBoundary`): there `ξ̄`
is forced to be a unit, which fails at real GS data.  This file supplies the honest weak
forms:

* `derivative_eval_eq_of_eq_X_sub_C_mul` — the `ξ̄` value identity: for `Q = (T − C v)·G`,
  `ξ̄ = G.eval v` (the branch-separation reading).
* `derivative_eval_ne_zero_of_squarefree_of_dvd` — **simple root of squarefree at a
  section**: `Squarefree Q` and `(T − C v) ∣ Q` give `ξ̄ ≠ 0` — mere nonvanishing, exactly
  the gap between `Squarefree` (true for radicals) and `Separable` over `F[Z]` (false, F13).
* `section_dvd_radical_slice` + `xiBar_radical_ne_zero` — the **unconditional** radical
  route: for ANY nonzero slice `Q` with the section divisor, the radical keeps the section
  (`T − C v` is prime) and its `ξ̄` is nonzero, with no hypothesis beyond `Q ≠ 0`.
* `card_filter_eval_eq_zero_le` / `exists_eval_ne_zero_of_natDegree_lt_card` /
  `card_bad_places_radical_le` — the **counted exceptional set**: `ξ̄(z) ≠ 0` off at most
  `deg ξ̄` places (roots of a nonzero polynomial of `F[Z]`).
* `eval_map_apply_of_comm`, `eval_map_section_eq_zero`, `derivative_eval_map_section_eq`,
  `derivative_eval_map_section_ne_zero` — the **Newton seed transport** along any (injective)
  ring map `φ : F[Z] →+* K` (e.g. `algebraMap F[Z] (RatFunc F)`): the seed residue
  `(Q.map φ).eval (φ v) = 0` and the simple-root certificate
  `(∂(Q.map φ)).eval (φ v) = φ ξ̄ ≠ 0` — the exact inputs of the Hensel/Newton lift over
  `Frac(F[Z])`.
* `derivative_eval_place_eq` — the **per-place reading**: at `φ := evalRingHom z` the
  transported certificate is literally `ξ̄.eval z`, so off the counted set the specialized
  slice has `v.eval z` as a simple root (the per-place Newton seeds).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6, Appendix A; the F13 boundary (`SliceSeparabilityBoundary.lean`).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate UniqueFactorizationMonoid

namespace ArkLib

namespace SectionNewtonXiSupply

/-! ## §1 — the `ξ̄` value identity and the squarefree simple-root certificate -/

/-- **The `ξ̄` value identity**: for a split `Q = (X − C v)·G`, the derivative reading at the
section is the branch separation, `Q′.eval v = G.eval v`. -/
theorem derivative_eval_eq_of_eq_X_sub_C_mul {R : Type*} [CommRing R] {Q G : R[X]} {v : R}
    (hsplit : Q = (X - C v) * G) :
    Q.derivative.eval v = G.eval v := by
  rw [hsplit]
  simp [derivative_mul]

/-- **Simple root of a squarefree polynomial at a section** (the honest replacement of the
F13-poisoned `separable_evalX`): if `Q` is squarefree and `(X − C v) ∣ Q`, then
`ξ̄ := Q′.eval v ≠ 0`.  Mere nonvanishing — not the unit that `Separable` over a non-field
base would force. -/
theorem derivative_eval_ne_zero_of_squarefree_of_dvd {R : Type*} [CommRing R] [Nontrivial R]
    {Q : R[X]} {v : R} (hsq : Squarefree Q) (hdvd : (X - C v) ∣ Q) :
    Q.derivative.eval v ≠ 0 := by
  obtain ⟨G, hG⟩ := hdvd
  rw [derivative_eval_eq_of_eq_X_sub_C_mul hG]
  intro h0
  have hdG : (X - C v) ∣ G := dvd_iff_isRoot.mpr h0
  have hsqd : (X - C v) * (X - C v) ∣ Q := by
    rw [hG]; exact mul_dvd_mul_left _ hdG
  exact Polynomial.not_isUnit_X_sub_C v (hsq _ hsqd)

/-! ## §2 — the radical route: unconditional `ξ̄ ≠ 0` at any section of any nonzero slice -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- The section divisor survives the radical: `T − C v` is prime over the domain `F[Z]`. -/
theorem section_dvd_radical_slice {Q : F[X][Y]} (hQ : Q ≠ 0) {v : F[X]}
    (hdvd : (X - C v) ∣ Q) : (X - C v) ∣ radical Q :=
  (dvd_radical_iff_of_irreducible (Polynomial.prime_X_sub_C v).irreducible hQ).mpr hdvd

/-- **The unconditional `ξ̄` certificate**: for ANY nonzero slice with the section divisor,
the radical's derivative reading at the section is nonzero — no separability, no
squarefreeness hypothesis on `Q` itself. -/
theorem xiBar_radical_ne_zero {Q : F[X][Y]} (hQ : Q ≠ 0) {v : F[X]}
    (hdvd : (X - C v) ∣ Q) :
    ((radical Q).derivative).eval v ≠ 0 :=
  derivative_eval_ne_zero_of_squarefree_of_dvd squarefree_radical
    (section_dvd_radical_slice hQ hdvd)

/-! ## §3 — the counted exceptional set -/

/-- **The bad-place count**: a nonzero `ξ̄ ∈ F[Z]` vanishes on at most `deg ξ̄` places of any
finite place set. -/
theorem card_filter_eval_eq_zero_le {ξ : F[X]} (hξ : ξ ≠ 0) (S : Finset F) :
    (S.filter (fun z => ξ.eval z = 0)).card ≤ ξ.natDegree := by
  have hsub : S.filter (fun z => ξ.eval z = 0) ⊆ ξ.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hξ]
    exact (Finset.mem_filter.mp hz).2
  calc (S.filter (fun z => ξ.eval z = 0)).card
      ≤ ξ.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card ξ.roots := ξ.roots.toFinset_card_le
    _ ≤ ξ.natDegree := Polynomial.card_roots' ξ

/-- A nonzero `ξ̄` has a nonvanishing place in any set larger than its degree. -/
theorem exists_eval_ne_zero_of_natDegree_lt_card {ξ : F[X]} (hξ : ξ ≠ 0) {S : Finset F}
    (h : ξ.natDegree < S.card) : ∃ z ∈ S, ξ.eval z ≠ 0 := by
  by_contra hall
  have hall' : ∀ z ∈ S, ξ.eval z = 0 := fun z hz => by
    by_contra hne
    exact hall ⟨z, hz, hne⟩
  have hfull : S.filter (fun z => ξ.eval z = 0) = S :=
    Finset.filter_eq_self.mpr hall'
  have := card_filter_eval_eq_zero_le hξ S
  rw [hfull] at this
  omega

/-- **The radical `ξ̄` bad-place count, assembled**: for any nonzero slice with the section
divisor, the radical's `ξ̄` vanishes on at most `deg ξ̄` places. -/
theorem card_bad_places_radical_le {Q : F[X][Y]} (hQ : Q ≠ 0) {v : F[X]}
    (hdvd : (X - C v) ∣ Q) (S : Finset F) :
    (S.filter (fun z => (((radical Q).derivative).eval v).eval z = 0)).card
      ≤ (((radical Q).derivative).eval v).natDegree :=
  card_filter_eval_eq_zero_le (xiBar_radical_ne_zero hQ hdvd) S

/-! ## §4 — the Newton seed transport along a (injective) coefficient map -/

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Evaluation at a mapped point commutes with the coefficient map. -/
theorem eval_map_apply_of_comm (Q : R[X]) (v : R) :
    (Q.map φ).eval (φ v) = φ (Q.eval v) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- **The Newton seed residue**: the global section divisor maps to the vanishing of the
transported slice at the transported section — the `eval c (Q₀ …) = 0` input of the
constructive Newton root over `Frac(F[Z])`. -/
theorem eval_map_section_eq_zero {Q : R[X]} {v : R} (hdvd : (X - C v) ∣ Q) :
    (Q.map φ).eval (φ v) = 0 := by
  rw [eval_map_apply_of_comm, Polynomial.dvd_iff_isRoot.mp hdvd, map_zero]

/-- The transported derivative reading IS the mapped `ξ̄`. -/
theorem derivative_eval_map_section_eq (Q : R[X]) (v : R) :
    ((Q.map φ).derivative).eval (φ v) = φ (Q.derivative.eval v) := by
  rw [Polynomial.derivative_map, eval_map_apply_of_comm]

/-- **The transported simple-root certificate**: along an injective coefficient map (e.g.
`algebraMap F[Z] (RatFunc F)`), `ξ̄ ≠ 0` transports to the nonvanishing of the derivative of
the transported slice at the transported section — the Newton/Hensel simple-root seed. -/
theorem derivative_eval_map_section_ne_zero (hφ : Function.Injective φ) {Q : R[X]} {v : R}
    (hξ : Q.derivative.eval v ≠ 0) :
    ((Q.map φ).derivative).eval (φ v) ≠ 0 := by
  rw [derivative_eval_map_section_eq]
  exact fun h0 => hξ ((map_eq_zero_iff φ hφ).mp h0)

end Transport

/-- **The per-place reading**: at the place map `φ := evalRingHom z` the transported
certificate is literally `ξ̄.eval z` — so off the counted exceptional set of §3 the
specialized slice has `v.eval z` as a simple root (the per-place Newton seeds). -/
theorem derivative_eval_place_eq {F : Type*} [CommRing F] (Q : (Polynomial F)[X])
    (v : Polynomial F) (z : F) :
    ((Q.map (Polynomial.evalRingHom z)).derivative).eval (v.eval z)
      = (Q.derivative.eval v).eval z := by
  simpa [Polynomial.coe_evalRingHom] using
    derivative_eval_map_section_eq (Polynomial.evalRingHom z) Q v

end SectionNewtonXiSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonXiSupply.derivative_eval_eq_of_eq_X_sub_C_mul
#print axioms ArkLib.SectionNewtonXiSupply.derivative_eval_ne_zero_of_squarefree_of_dvd
#print axioms ArkLib.SectionNewtonXiSupply.section_dvd_radical_slice
#print axioms ArkLib.SectionNewtonXiSupply.xiBar_radical_ne_zero
#print axioms ArkLib.SectionNewtonXiSupply.card_filter_eval_eq_zero_le
#print axioms ArkLib.SectionNewtonXiSupply.exists_eval_ne_zero_of_natDegree_lt_card
#print axioms ArkLib.SectionNewtonXiSupply.card_bad_places_radical_le
#print axioms ArkLib.SectionNewtonXiSupply.eval_map_apply_of_comm
#print axioms ArkLib.SectionNewtonXiSupply.eval_map_section_eq_zero
#print axioms ArkLib.SectionNewtonXiSupply.derivative_eval_map_section_eq
#print axioms ArkLib.SectionNewtonXiSupply.derivative_eval_map_section_ne_zero
#print axioms ArkLib.SectionNewtonXiSupply.derivative_eval_place_eq
