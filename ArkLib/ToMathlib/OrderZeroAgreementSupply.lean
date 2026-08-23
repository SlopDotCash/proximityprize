/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HenselMatchingPolySupply

/-!
# Issue #304 — the order-0 agreement `h0`: honest sources at the Hensel base point

`HenselMatchingPolySupply.InterpolantInput` (and through it `HenselApproxSupply` and the
whole `HPzBridge.HenselDatum` lane) consumes, per good `z`, the order-0 agreement

```
h0 : (P z).coeff 0 = (((map C v₀) + (C X) * (map C v₁)).eval (C z)).coeff 0
```

— the BCIKS20 §6.2 / Appendix A.5.2 **base-point agreement**: the two competitors (the
decoded `P z` and the representative specialisation) reduce, mod the power-series variable,
to the same value at the expansion centre.  This file isolates what is *provable* about
`h0` from the in-tree GS cargo and names the irreducible remainder.

## The mathematical content

The in-tree power-series convention is centred at `0`: the order-0 reduction of a coerced
polynomial `↑p : F⟦X⟧` is `p.coeff 0 = p.eval 0` — evaluation of the inner (RS) variable at
the centre.  Three facts organise the frontier:

1. **Both base values are roots of the SAME base polynomial — unconditionally.**  The two
   `InterpolantInput` divisibilities `(Y − C (P z)) ∣ Q z` and `(Y − C (lift z)) ∣ Q z`
   descend along the coefficient evaluation `F[X] →+* F` at the centre to the *base
   specialisation* `baseSpec (Q z) := (Q z).map (evalRingHom 0)` — the centre fiber
   `Q z (0, ·)` of the per-`z` GS interpolant.  Hence `(P z).coeff 0` and
   `(lift z).coeff 0` are both roots of `baseSpec (Q z)`
   (`isRoot_baseSpec_of_dvd`; coherence with the power-series lift:
   `constantCoeff_map_fSeries`).  This is proved here, with no hypotheses beyond the
   divisibilities already carried by `InterpolantInput`.

2. **What `h0` concretely says.**  `(lift.eval (C z)).coeff 0 = v₀.eval z`
   (`lift_eval_coeff_zero`): the base point of the representative specialisation is the
   order-0 representative coefficient `v₀` evaluated at the curve parameter.  So `h0` reads
   *"the decoded polynomial's value at the expansion centre equals `v₀(z)`"* — exactly the
   App A.5.2 statement that the Hensel solution and the decoded word share the base point
   `a₀ = α₀(z)`.

3. **What pins the two base roots EQUAL.**  Not derivable from the divisibilities alone
   (a separable centre fiber has many distinct roots); the two honest sources, both
   formalized here as producers with named non-goal-shaped hypotheses:

   * **(i) the uniqueness route** (App A.5.2: the base point is the *unique* relevant root
     of the centre fiber): if `baseSpec (Q z)` has at most one root in a class `S z`
     containing both base values (`UniqueRootOn` — the unique-decoding-at-the-centre /
     pinned-base-root fact, a count/distance input in BCIKS20), the agreement follows
     (`coeff_zero_eq_of_dvd_of_uniqueRootOn`, family form `h0_supply_of_uniqueRootOn`).
     The linear-fiber witness — the centre fiber is (a unit times) a single linear factor,
     the unique-decoding sub-case — is proved closed (`uniqueRootOn_of_eq_C_mul_X_sub_C`).

   * **(ii) the graph route** (§6.2 curve geometry: both competitors pass through the graph
     point over the centre): if the evaluation domain hits the centre (`domain i₀ = 0`) and
     BOTH competitors agree with the folded word `w_z = ∑ t, z^t • u t` at `i₀` — i.e. the
     centre lies in both agreement sets — then `h0` follows from
     `coeff 0 = eval 0` (`h0_supply_of_centre_agreement`).  For the lift competitor the
     agreement hypothesis reads `v₀.eval z = w_z i₀` — the §5 fact that the representative's
     base coefficient interpolates the word at the centre.

## Wiring (the deliverables)

* `interpolantInput_of_uniqueRootOn` / `interpolantInput_of_centre_agreement` — full
  `HenselMatchingPolySupply.InterpolantInput` with the `h0` field replaced by the weaker
  honest sources (route (i) resp. (ii)); all other fields passed through.
* `henselDatum_of_uniqueRootOn` / `henselDatum_of_centre_agreement` — the compositions to
  `HPzBridge.HenselDatum` (ready for `HPzBridge.hPz_of_henselDatum`).

## Honest residuals

Neither route's named hypothesis is goal-shaped.  Route (i)'s `UniqueRootOn (baseSpec (Q z))
(S z)` is a property of the interpolant's centre fiber *alone* (plus the two class
memberships) — the BCIKS20 count/distance fact that the centre is uncorrupted enough to pin a
unique base root; no in-tree lemma supplies it yet (production lane: the §5 centre-fiber
counting).  Route (ii)'s agreement facts relate each competitor separately to the *word*
(the §5 agreement-set cargo: `0` lies in both agreement sets), never the competitors to each
other.  `h0` itself — a competitor-competitor identity — is DERIVED.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5), §6.2 (Theorem 6.2), Appendix A §5.2 (the base point `α₀` of the
  Hensel expansion).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

namespace ArkLib

namespace OrderZeroAgreementSupply

/-! ## The base specialisation (the centre fiber of the interpolant) -/

section Bricks

variable {F : Type} [Field F]

/-- **The base specialisation of the per-`z` GS interpolant** — the centre fiber
`Q(0, ·) : F[Y]`: the inner (RS) variable evaluated at the expansion centre `0`
coefficientwise.  Both competitors' order-0 values are roots of it
(`isRoot_baseSpec_of_dvd`); it is the order-0 reduction of the matching polynomial
`fSeries Q` (`constantCoeff_map_fSeries`). -/
noncomputable def baseSpec (Q : F[X][Y]) : Polynomial F :=
  Q.map (Polynomial.evalRingHom (0 : F))

/-- **Coherence with the power-series lift**: the constant-coefficient reduction of the
matching polynomial `fSeries Q : (F⟦X⟧)[Y]` IS the base specialisation.  The order-0 story
can therefore be told entirely at the `F[X][Y]` level. -/
theorem constantCoeff_map_fSeries (Q : F[X][Y]) :
    (HenselMatchingPolySupply.fSeries Q).map
        (PowerSeries.constantCoeff : PowerSeries F →+* F)
      = baseSpec Q := by
  unfold HenselMatchingPolySupply.fSeries baseSpec
  rw [Polynomial.map_map]
  congr 1
  refine RingHom.ext fun v => ?_
  simp [RingHom.comp_apply, Polynomial.coeff_zero_eq_eval_zero]

/-- **Order-0 descent of the matching-factor divisibility (the unconditional half of
`h0`).**  If `Y − C v` divides the interpolant `Q` over `F[X][Y]` (the exact
`InterpolantInput.hPdvd`/`hQdvd` shape), then the base value `v.coeff 0` is a root of the
centre fiber `baseSpec Q`. -/
theorem isRoot_baseSpec_of_dvd {Q : F[X][Y]} {v : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C v) ∣ Q) :
    (baseSpec Q).IsRoot (v.coeff 0) := by
  have h := Polynomial.map_dvd (Polynomial.evalRingHom (0 : F)) hdvd
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
  have hv : (Polynomial.evalRingHom (0 : F)) v = v.coeff 0 := by
    simp [Polynomial.coeff_zero_eq_eval_zero]
  rw [hv] at h
  exact Polynomial.dvd_iff_isRoot.mp h

/-- **Order-0 descent at the power-series level** (for `HenselDatum`-shaped consumers with
an abstract matching polynomial `f`): a coerced-polynomial root of `f` descends to a root of
the constant-coefficient reduction of `f`, at the constant term. -/
theorem isRoot_constantCoeff_map_of_isRoot {f : Polynomial (PowerSeries F)} {p : F[X]}
    (h : f.IsRoot ((p : F[X]) : PowerSeries F)) :
    (f.map (PowerSeries.constantCoeff : PowerSeries F →+* F)).IsRoot (p.coeff 0) := by
  simpa using
    (Polynomial.IsRoot.map (f := (PowerSeries.constantCoeff : PowerSeries F →+* F)) h)

/-! ## Route (i): the base root is unique in the relevant class -/

/-- **The honest uniqueness source (route (i)).**  `f₀` has at most one root in the class
`S`.  Instantiated at `f₀ := baseSpec (Q z)` and `S z :=` the class containing both
competitors' base values, this is the BCIKS20 App A.5.2 *pinned base point*: the centre
fiber of the GS interpolant determines a unique relevant root (unique decoding at the
uncorrupted expansion centre — a count/distance fact).  No in-tree lemma supplies it yet;
it is a property of the interpolant's centre fiber alone, NOT of the pair of competitors,
hence strictly below the `h0` goal. -/
def UniqueRootOn (f₀ : Polynomial F) (S : Set F) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, f₀.IsRoot a → f₀.IsRoot b → a = b

/-- **The closed linear-fiber witness for route (i)** (the unique-decoding sub-case): if the
centre fiber is a nonzero scalar times a single linear factor `Y − a`, the uniqueness
witness holds on every class. -/
theorem uniqueRootOn_of_eq_C_mul_X_sub_C {f₀ : Polynomial F} {c a : F} (hc : c ≠ 0)
    (h : f₀ = Polynomial.C c * (Polynomial.X - Polynomial.C a)) (S : Set F) :
    UniqueRootOn f₀ S := by
  have key : ∀ x : F, f₀.IsRoot x → x = a := by
    intro x hx
    rw [h] at hx
    have hx' : c * (x - a) = 0 := by simpa [Polynomial.IsRoot] using hx
    rcases mul_eq_zero.mp hx' with h1 | h2
    · exact absurd h1 hc
    · exact sub_eq_zero.mp h2
  intro x _ y _ hx hy
  rw [key x hx, key y hy]

/-- **The order-0 agreement from the uniqueness source, single `z`.**  Both matching-factor
divisibilities + both class memberships + the uniqueness witness on the centre fiber pin the
two base values equal — the `h0` content at one parameter. -/
theorem coeff_zero_eq_of_dvd_of_uniqueRootOn {Q : F[X][Y]} {v w : F[X]} {S : Set F}
    (hv : (Polynomial.X - Polynomial.C v) ∣ Q)
    (hw : (Polynomial.X - Polynomial.C w) ∣ Q)
    (hvS : v.coeff 0 ∈ S) (hwS : w.coeff 0 ∈ S)
    (huniq : UniqueRootOn (baseSpec Q) S) :
    v.coeff 0 = w.coeff 0 :=
  huniq _ hvS _ hwS (isRoot_baseSpec_of_dvd hv) (isRoot_baseSpec_of_dvd hw)

/-! ## Route (ii): the centre is a common graph point -/

/-- The constant coefficient is evaluation at the centre: two polynomials agreeing at `0`
share their constant term. -/
theorem coeff_zero_eq_of_eval_zero_eq {p q : F[X]} (h : p.eval 0 = q.eval 0) :
    p.coeff 0 = q.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero]
  exact h

/-- **What `h0` concretely says**: the base point of the lift specialisation is the order-0
representative coefficient evaluated at the curve parameter,
`(lift.eval (C z)).coeff 0 = v₀.eval z`.  So `h0` reads
"`(P z).eval 0 = v₀.eval z`" — the decoded value at the expansion centre equals the Hensel
base coefficient at `z` (BCIKS20 App A.5.2's `a₀ = α₀(z)`). -/
theorem lift_eval_coeff_zero (v₀ v₁ : F[X]) (z : F) :
    (((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z)).coeff 0 = v₀.eval z := by
  have h₀ : (Polynomial.map Polynomial.C v₀).eval (Polynomial.C z)
      = Polynomial.C (v₀.eval z) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have h₁ : (Polynomial.map Polynomial.C v₁).eval (Polynomial.C z)
      = Polynomial.C (v₁.eval z) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, h₀, h₁]
  simp

end Bricks

/-! ## The per-`z` family producers on the good set -/

section Family

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Route (i), family form, abstract competitor.**  Per-`z` matching-factor
divisibilities for the decoded `P z` and ANY second family `Qz'`, class memberships of both
base values, and the per-`z` uniqueness witness on the centre fiber yield the order-0
agreement family — the `h0` shape with `Qz'` in place of the lift specialisation. -/
theorem h0_supply_of_uniqueRootOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (Q : F → F[X][Y]) (P Qz' : F → Polynomial F)
    (S : F → Set F)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (Qz' z)) ∣ Q z)
    (hPmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0 ∈ S z)
    (hQmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Qz' z).coeff 0 ∈ S z)
    (huniq : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      UniqueRootOn (baseSpec (Q z)) (S z)) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0 = (Qz' z).coeff 0 :=
  fun z hz =>
    coeff_zero_eq_of_dvd_of_uniqueRootOn (hPdvd z hz) (hQdvd z hz)
      (hPmem z hz) (hQmem z hz) (huniq z hz)

/-- **Route (i) at the lift family — the `h0` field of `InterpolantInput`, verbatim.**
The lift-side class membership is stated in its interpretable form `v₀.eval z ∈ S z`
(`lift_eval_coeff_zero`). -/
theorem h0_of_lift_uniqueRootOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (Q : F → F[X][Y]) (P : F → Polynomial F)
    (v₀ v₁ : F[X]) (S : F → Set F)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))) ∣ Q z)
    (hPmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0 ∈ S z)
    (hQmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      v₀.eval z ∈ S z)
    (huniq : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      UniqueRootOn (baseSpec (Q z)) (S z)) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0
        = (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).coeff 0 := by
  intro z hz
  refine coeff_zero_eq_of_dvd_of_uniqueRootOn (hPdvd z hz) (hQdvd z hz) (hPmem z hz) ?_
    (huniq z hz)
  rw [lift_eval_coeff_zero]
  exact hQmem z hz

/-- **Route (ii), family form, abstract competitor.**  If the evaluation domain hits the
expansion centre (`domain i₀ = 0`) and BOTH competitors agree with the folded word
`w_z = ∑ t, z^t • u t` at `i₀` (the centre lies in both agreement sets — §5 agreement-set
cargo), the order-0 agreement family follows from `coeff 0 = eval 0`. -/
theorem h0_supply_of_centre_agreement {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (P Qz' : F → Polynomial F) (i₀ : ι)
    (hdom : domain i₀ = 0)
    (hPagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).eval (domain i₀) = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀)
    (hQagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Qz' z).eval (domain i₀) = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0 = (Qz' z).coeff 0 := by
  intro z hz
  apply coeff_zero_eq_of_eval_zero_eq
  rw [← hdom, hPagree z hz, hQagree z hz]

/-- **Route (ii) at the lift family — the `h0` field of `InterpolantInput`, verbatim.**
The lift-side agreement is stated in its interpretable form `v₀.eval z = w_z i₀` (the
representative's base coefficient interpolates the word at the centre — the curve passes
through the graph point over the centre). -/
theorem h0_of_lift_centre_agreement {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (P : F → Polynomial F) (v₀ v₁ : F[X]) (i₀ : ι)
    (hdom : domain i₀ = 0)
    (hPagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).eval (domain i₀) = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀)
    (hQagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      v₀.eval z = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0
        = (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).coeff 0 := by
  intro z hz
  rw [lift_eval_coeff_zero, Polynomial.coeff_zero_eq_eval_zero, ← hdom, hPagree z hz,
    hQagree z hz]

/-! ## Wiring into `InterpolantInput` and `HenselDatum` -/

/-- **`InterpolantInput` with `h0` replaced by the route-(i) uniqueness source.**  All other
fields pass through; the residuals are exactly: the two GS divisibilities, separability, the
two class memberships, and the per-`z` `UniqueRootOn` witness on the centre fiber. -/
noncomputable def interpolantInput_of_uniqueRootOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (Q : F → F[X][Y]) (S : F → Set F)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))) ∣ Q z)
    (hPmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0 ∈ S z)
    (hQmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      v₀.eval z ∈ S z)
    (huniq : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      UniqueRootOn (baseSpec (Q z)) (S z))
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable) :
    HenselMatchingPolySupply.InterpolantInput
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ where
  Q := Q
  hPdvd := hPdvd
  hQdvd := hQdvd
  h0 := h0_of_lift_uniqueRootOn Q P v₀ v₁ S hPdvd hQdvd hPmem hQmem huniq
  hsep := hsep

/-- **`InterpolantInput` with `h0` replaced by the route-(ii) centre-agreement source.** -/
noncomputable def interpolantInput_of_centre_agreement {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (Q : F → F[X][Y]) (i₀ : ι) (hdom : domain i₀ = 0)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))) ∣ Q z)
    (hPagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).eval (domain i₀) = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀)
    (hQagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      v₀.eval z = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀)
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable) :
    HenselMatchingPolySupply.InterpolantInput
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ where
  Q := Q
  hPdvd := hPdvd
  hQdvd := hQdvd
  h0 := h0_of_lift_centre_agreement P v₀ v₁ i₀ hdom hPagree hQagree
  hsep := hsep

/-- **`HPzBridge.HenselDatum` with `h0` replaced by the route-(i) uniqueness source**
(through `henselDatum_of_interpolantInput`; ready for `HPzBridge.hPz_of_henselDatum`). -/
noncomputable def henselDatum_of_uniqueRootOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (Q : F → F[X][Y]) (S : F → Set F)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))) ∣ Q z)
    (hPmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0 ∈ S z)
    (hQmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      v₀.eval z ∈ S z)
    (huniq : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      UniqueRootOn (baseSpec (Q z)) (S z))
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  HenselMatchingPolySupply.henselDatum_of_interpolantInput
    (interpolantInput_of_uniqueRootOn Q S hPdvd hQdvd hPmem hQmem huniq hsep)

/-- **`HPzBridge.HenselDatum` with `h0` replaced by the route-(ii) centre-agreement
source.** -/
noncomputable def henselDatum_of_centre_agreement {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (Q : F → F[X][Y]) (i₀ : ι) (hdom : domain i₀ = 0)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))) ∣ Q z)
    (hPagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).eval (domain i₀) = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀)
    (hQagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      v₀.eval z = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀)
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  HenselMatchingPolySupply.henselDatum_of_interpolantInput
    (interpolantInput_of_centre_agreement Q i₀ hdom hPdvd hQdvd hPagree hQagree hsep)

end Family

end OrderZeroAgreementSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.OrderZeroAgreementSupply.baseSpec
#print axioms ArkLib.OrderZeroAgreementSupply.constantCoeff_map_fSeries
#print axioms ArkLib.OrderZeroAgreementSupply.isRoot_baseSpec_of_dvd
#print axioms ArkLib.OrderZeroAgreementSupply.isRoot_constantCoeff_map_of_isRoot
#print axioms ArkLib.OrderZeroAgreementSupply.UniqueRootOn
#print axioms ArkLib.OrderZeroAgreementSupply.uniqueRootOn_of_eq_C_mul_X_sub_C
#print axioms ArkLib.OrderZeroAgreementSupply.coeff_zero_eq_of_dvd_of_uniqueRootOn
#print axioms ArkLib.OrderZeroAgreementSupply.coeff_zero_eq_of_eval_zero_eq
#print axioms ArkLib.OrderZeroAgreementSupply.lift_eval_coeff_zero
#print axioms ArkLib.OrderZeroAgreementSupply.h0_supply_of_uniqueRootOn
#print axioms ArkLib.OrderZeroAgreementSupply.h0_of_lift_uniqueRootOn
#print axioms ArkLib.OrderZeroAgreementSupply.h0_supply_of_centre_agreement
#print axioms ArkLib.OrderZeroAgreementSupply.h0_of_lift_centre_agreement
#print axioms ArkLib.OrderZeroAgreementSupply.interpolantInput_of_uniqueRootOn
#print axioms ArkLib.OrderZeroAgreementSupply.interpolantInput_of_centre_agreement
#print axioms ArkLib.OrderZeroAgreementSupply.henselDatum_of_uniqueRootOn
#print axioms ArkLib.OrderZeroAgreementSupply.henselDatum_of_centre_agreement
