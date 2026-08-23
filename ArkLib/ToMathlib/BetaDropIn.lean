/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsStrong

/-!
# `BetaDropIn` — the kernel disposition record of the `L13` drop-in

This file closes the bookkeeping of the `L13` drop-in (replace the trivial in-tree `β_regular`
witness by the genuine App-A.4 recursion `ArkLib.betaRec`) by recording, **as kernel theorems**,
both sides of its final disposition:

1. **The negative side (why the literal in-place drop-in is impossible).**  The legacy
   `RationalFunctions.β` is `Exists.choose` of `β_regular`, whose statement asserts *only* the
   weight upper bound `Λ(β) ≤ (2t+1)·d_R·D`.  Because `Exists.choose` depends only on the
   *proposition* (proof irrelevance), swapping the trivial `β = 0` witness for `betaRec` inside
   `β_regular`'s proof would change **nothing**: `β R t` is determined by the statement alone.
   And the statement underdetermines it — this file proves, kernel-clean, that the defining
   predicate `betaRegularSpec` admits **two distinct witnesses** (`0` and `mk X = betaRec … 0`),
   so no theorem of the form `β R t = betaRec … t` (route (a) of `BetaIdentify`) can exist:
   `not_betaRegularSpec_forces_betaRec` exhibits the failure of the uniqueness route at `t = 0`.
   Pinning the value therefore requires *strengthening the statement* of the existence lemma, and
   the pinned statement needs `x₀ : F`, `hHyp : Hypotheses x₀ R H`, and the Hasse numerators
   `Bcoeff` — data the legacy signature `β (R : F[X][X][Y]) (t : ℕ)` structurally lacks.  This is
   the genuine interface gap; it is mathematics, not file ownership.

2. **The positive side (the executed drop-in).**  The signature-grown replacement *has been
   executed* by the `L13` architectural split: `RationalFunctionsCore.lean` carries the App-A
   machinery, `BetaRecursion.lean` imports *Core* (no import cycle), and
   `RationalFunctionsStrong.lean` defines the honest in-tree numerator `β_strong`, whose defining
   property pins the embedding to `betaRec`'s, whence `beta_strong_eq_betaRec` —
   the exact "definitional bridge lemma `β_eq_betaRec` under matching hypotheses" that the drop-in
   sought.  We re-export it here (`dropIn_bridge`) so this file is the one-stop audit record.

Everything here is `sorry`-free; the `#print axioms` block at the bottom must show only
`[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  Appendix A.4 (the recursion (A.1)), Claim A.2 (the weight bound that `β_regular` asserts).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace BetaDropIn

variable {F : Type} [Field F]

/-! ## The defining predicate of the legacy `β_regular`

`β_regular R H hH hD t` asserts `∃ β : 𝒪 H, weight_Λ_over_𝒪 hH β D ≤ (2t+1)·d_R·D`.  The predicate
below is that existential's body — the *sole* property the legacy `β R t = (β_regular …).choose`
provably satisfies. -/

/-- The defining predicate of `β_regular` at index `t`: the Claim-A.2 weight upper bound.  This is
the **entire** in-tree specification of the legacy numerator `β R t`. -/
def betaRegularSpec (R : F[X][X][Y]) (H : F[X][Y]) (hH : 0 < H.natDegree) (D t : ℕ)
    (b : 𝒪 H) : Prop :=
  weight_Λ_over_𝒪 hH b D ≤ (((2 * t + 1) * Bivariate.natDegreeY R * D : ℕ) : WithBot ℕ)

/-- `0` satisfies the legacy defining predicate (this is exactly the trivial witness used by the
in-tree `β_regular`): the `𝒪`-weight of `0` is `⊥`. -/
theorem betaRegularSpec_zero (R : F[X][X][Y]) (H : F[X][Y]) (hH : 0 < H.natDegree) (D t : ℕ) :
    betaRegularSpec R H hH D t (0 : 𝒪 H) := by
  unfold betaRegularSpec
  rw [weight_Λ_over_𝒪_zero]
  exact bot_le

/-- The legacy in-tree numerator `β R t` satisfies its defining predicate at `D = totalDegree H`
(this is `Exists.choose_spec`, the *only* provable fact about `β R t`). -/
theorem legacy_β_satisfies_spec (R : F[X][X][Y]) {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hH : 0 < H.natDegree) (t : ℕ) :
    betaRegularSpec R H hH (Bivariate.totalDegree H) t (β (H := H) R t) := by
  unfold betaRegularSpec
  have hval : β (H := H) R t
      = (β_regular R H hH (Nat.le_refl _) (D := Bivariate.totalDegree H) t).choose := by
    unfold β
    rw [dif_pos hH]
  rw [hval]
  exact (β_regular R H hH (Nat.le_refl _) (D := Bivariate.totalDegree H) t).choose_spec

/-! ## The second witness: `mk X` (the class of `T`, which is `betaRec … 0`)

The generator `T = mk X` of `𝒪 H` also satisfies the predicate, for every `t` and every `D`, as
soon as the Y-degree of `R` is positive (`d_R ≥ 1`, true for every separable §5 interpolant) and
`H` is a genuine curve (`d_H ≥ 2`).  Its weight is `D + 1 − d_H ≤ D ≤ (2t+1)·d_R·D`. -/

/-- The class of `X` (App-A's `T`) satisfies the legacy defining predicate, for **every** `t`. -/
theorem betaRegularSpec_mk_X (R : F[X][X][Y]) (H : F[X][Y]) (hH : 0 < H.natDegree)
    (hH2 : 1 < H.natDegree) (hdR : 0 < Bivariate.natDegreeY R) (D t : ℕ) :
    betaRegularSpec R H hH D t
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) Polynomial.X : 𝒪 H) := by
  unfold betaRegularSpec
  -- `X` is already reduced mod `H_tilde'` (degree 1 < d_H), so the `𝒪`-weight is `Λ(X)`.
  have hdegX : (Polynomial.X : F[X][Y]).degree < (H_tilde' H).degree := by
    have hmonic := H_tilde'_monic H hH
    rw [Polynomial.degree_X, Polynomial.degree_eq_natDegree hmonic.ne_zero,
      natDegree_H_tilde' hH]
    exact_mod_cast hH2
  rw [weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdegX]
  -- `Λ(X) ≤ D + 1 − d_H` (the `k = 1` monomial weight).
  have hX : weight_Λ (Polynomial.X : F[X][Y]) H D
      ≤ ((D + 1 - Bivariate.natDegreeY H : ℕ) : WithBot ℕ) := by
    simpa [pow_one, one_mul] using weight_Λ_X_pow_le H D 1
  refine hX.trans ?_
  -- `D + 1 − d_H ≤ D ≤ (2t+1)·d_R·D` since `d_H ≥ 1` and `(2t+1)·d_R ≥ 1`.
  have hYH : 1 ≤ Bivariate.natDegreeY H := by
    unfold Polynomial.Bivariate.natDegreeY
    omega
  have h1 : D + 1 - Bivariate.natDegreeY H ≤ D := by omega
  have hpos : 0 < (2 * t + 1) * Bivariate.natDegreeY R := Nat.mul_pos (by omega) hdR
  have h2 : D ≤ (2 * t + 1) * Bivariate.natDegreeY R * D := Nat.le_mul_of_pos_left D hpos
  exact_mod_cast h1.trans h2

/-- `mk X ≠ 0` in `𝒪 H` once `H` is a genuine curve (`1 < d_H`): `H_tilde'` is monic of `T`-degree
`d_H > 1`, so it cannot divide the degree-1 polynomial `X`. -/
theorem mk_X_ne_zero (H : F[X][Y]) (hH2 : 1 < H.natDegree) :
    (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) Polynomial.X : 𝒪 H) ≠ 0 := by
  have hH : 0 < H.natDegree := lt_trans one_pos hH2
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  have hle : (H_tilde' H).natDegree ≤ (Polynomial.X : F[X][Y]).natDegree :=
    Polynomial.natDegree_le_of_dvd h Polynomial.X_ne_zero
  rw [natDegree_H_tilde' hH, Polynomial.natDegree_X] at hle
  omega

/-! ## The underdetermination certificate (route (a) is dead, kernel-proven)

Two distinct elements satisfy the legacy defining predicate at every index `t`.  Hence the
predicate does not determine its witness, and — since `Exists.choose` depends only on the
proposition — **no** choice of proof for `β_regular` can make `β R t` provably equal to any
particular element (in particular not to `betaRec … t`). -/

/-- **The legacy `β_regular` specification is underdetermined**: at every index `t`, both `0` and
`mk X ≠ 0` satisfy it.  This is the kernel-proven form of the `BetaIdentify` route-(a) blockage:
the weight inequality pins nothing, so the opaque `β R t` cannot be identified with any specific
element. -/
theorem betaRegularSpec_two_witnesses (R : F[X][X][Y]) (H : F[X][Y]) (hH : 0 < H.natDegree)
    (hH2 : 1 < H.natDegree) (hdR : 0 < Bivariate.natDegreeY R) (D t : ℕ) :
    ∃ b₁ b₂ : 𝒪 H, b₁ ≠ b₂ ∧ betaRegularSpec R H hH D t b₁ ∧ betaRegularSpec R H hH D t b₂ :=
  ⟨0, Ideal.Quotient.mk (Ideal.span {H_tilde' H}) Polynomial.X,
    fun h => mk_X_ne_zero H hH2 h.symm,
    betaRegularSpec_zero R H hH D t,
    betaRegularSpec_mk_X R H hH hH2 hdR D t⟩

/-- The genuine recursion at `t = 0` satisfies the legacy defining predicate (it is `mk X`). -/
theorem betaRegularSpec_betaRec_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (hH2 : 1 < H.natDegree) (hdR : 0 < Bivariate.natDegreeY R) (D t : ℕ) :
    betaRegularSpec R H hH D t (betaRec x₀ R H hHyp Bcoeff 0) := by
  rw [betaRec_zero]
  exact betaRegularSpec_mk_X R H hH hH2 hdR D t

/-- **The uniqueness route to the drop-in is refuted, kernel-clean.**  There is no derivation
`betaRegularSpec b → b = betaRec … t` already at `t = 0`: the predicate is satisfied by `0`, while
`betaRec … 0 = mk X ≠ 0`.  Consequently the legacy `β R t` (an `Exists.choose` whose proposition is
exactly this predicate) can never be proven equal to `betaRec … t`; the in-place `L13` drop-in is
**mathematically impossible** without strengthening the statement — which requires the data
`(x₀, hHyp, Bcoeff)` absent from the legacy signature.  The executed resolution is `β_strong`
(`dropIn_bridge` below). -/
theorem not_betaRegularSpec_forces_betaRec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (hH2 : 1 < H.natDegree) (D : ℕ) :
    ¬ ∀ b : 𝒪 H, betaRegularSpec R H hH D 0 b → b = betaRec x₀ R H hHyp Bcoeff 0 := by
  intro hforce
  have h0 : (0 : 𝒪 H) = betaRec x₀ R H hHyp Bcoeff 0 :=
    hforce 0 (betaRegularSpec_zero R H hH D 0)
  rw [betaRec_zero] at h0
  exact mk_X_ne_zero H hH2 h0.symm

/-! ## The positive side: the executed drop-in (re-export)

The signature-grown numerator `β_strong` (`RationalFunctionsStrong.lean`) carries exactly the data
`(x₀, hHyp, Bcoeff)` that the pinning statement needs, and **is** the recursion. -/

/-- **The `L13` drop-in bridge, executed.**  The strong in-tree numerator equals the genuine
App-A.4 recursion — the "definitional bridge lemma `β_eq_betaRec` under matching hypotheses" that
the drop-in plan called for.  (Re-export of
`BCIKS20AppendixA.ClaimA2.beta_strong_eq_betaRec` for the audit record of this file.) -/
theorem dropIn_bridge (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (hH : 0 < H.natDegree) (t : ℕ) :
    β_strong x₀ R H hHyp Bcoeff t = betaRec x₀ R H hHyp Bcoeff t :=
  beta_strong_eq_betaRec x₀ R H hHyp Bcoeff hH t

end BetaDropIn

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BetaDropIn.betaRegularSpec_zero
#print axioms ArkLib.BetaDropIn.legacy_β_satisfies_spec
#print axioms ArkLib.BetaDropIn.betaRegularSpec_mk_X
#print axioms ArkLib.BetaDropIn.mk_X_ne_zero
#print axioms ArkLib.BetaDropIn.betaRegularSpec_two_witnesses
#print axioms ArkLib.BetaDropIn.betaRegularSpec_betaRec_zero
#print axioms ArkLib.BetaDropIn.not_betaRegularSpec_forces_betaRec
#print axioms ArkLib.BetaDropIn.dropIn_bridge
