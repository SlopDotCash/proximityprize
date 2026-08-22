/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BCIKS20PigeonholeSupply
import ArkLib.ToMathlib.BCIKS20ConcreteJohnson
import ArkLib.ToMathlib.DiscriminantSeparable

/-!
# Claim 5.7 residual bundle — per-field discharge brick (BCIKS20 §5)

`ProximityGap.Claim57Residuals` (`Agreement.lean`) is the typed input bundle gating the BCIKS20
Claim-5.7 keystone.  Its eight fields are
`hx0`, `hsep`, `hS_nonempty`, `A`, `hA`, `hcount`, `hlarge`, `hfactor`.  This file is the *honest
per-field discharge brick*: for each field it either supplies a genuine proof from in-tree
substrate, reduces it to a strictly more primitive named §5 hypothesis (with citation), or records
the precise structural reason the field is *not* dischargeable outright.

Two upstream supply files already did substantial work, which this brick builds on rather than
duplicates:

* `Claim57Supply.lean` (`claim57Residuals_of_johnson` /
  `claim57Residuals_of_natCeil_johnson`) canonicalises `A := matching_coords_for_z`, making `hA`
  automatic, derives `hS_nonempty` from `hlarge`, and reduces `hcount` to the per-`z` Johnson
  counting inequality.
* `Section5ConcreteJohnson.lean` (`claim57Residuals_of_gsInterpolant`) further reduces the per-`z`
  `hcount` to the **single** `z`-independent Johnson budget `hJohnson` on the GS interpolant via
  `BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le`.

So `A`/`hA`/`hcount`/`hS_nonempty` are **already discharged** upstream.  The genuinely-remaining
inputs that those assemblers carry as raw hypotheses are exactly `hx0`, `hsep`, `hlarge`, and
`hfactor`.  This file addresses those:

## Per-field verdict

* **`hfactor`** — *reduced to a named hypothesis with a structural impossibility note; the provable
  fragment is supplied.*  `pg_Rset h_gs = (normalizedFactors Q).toFinset`
  (`Extraction.pg_Rset`), whereas `(irreducible_factorization_of_gs_solution h_gs).choose_spec.choose`
  is the list of **descended primitive separable** factors `r` produced by `eq512_factor_descent`,
  where each *positive-degree* normalized factor `g` satisfies `g = C u · expand nn r`.  These two
  factor families coincide only when every factor is separable with `nn = 1` (e.g. characteristic
  `0`); in characteristic `p` an inseparable normalized factor `g` is a proper `p`-power image of
  its descended root `r ≠ g`, and degree-`0` normalized factors are dropped entirely.  Hence
  `hfactor` (`R ∈ pg_Rset → R ∈ descended list`) is **not provable outright**.  We supply the
  honestly-provable fragment `claim57_hfactor_irreducible_of_pg_Rset` (every `pg_Rset` member is
  irreducible) and keep `hfactor` itself as the documented bridge hypothesis.

* **`hx0`** — *discharged outright, in the exact consumer (X) shape (Finding F12 resolved).*  The
  earlier `exists_good_x₀_evalX_discr_y_ne` is **`Z`-shaped** (`evalX x₀ (discr_y R)` specializes the
  *inner* `Z` variable of `discr_y R : F[Z][X]`), but the `hx0`/`hsep` consumer fields are
  **`X`-shaped** (`evalX (C x₀) R` specializes the *middle* `X` variable of `R : (F[Z][X])[Y]`).
  These specialize different variables, so the `Z`-producer does not feed the `X`-consumer.
  `exists_good_x₀_X_shape_ne` **reruns the avoidance argument against the `X`-specialization**
  directly, producing — outright — an `x₀ : F` with `evalX (C x₀) R ≠ 0` for every `R ∈ pg_Rset`,
  under the honest per-factor `Z`-witness `hlead` (a `Z`-value not killing the `X`-leading
  coefficient) and the [BCIKS20] large-field budget `hcard`.  The exact finiteness is made precise:
  `evalX (C x₀) R = 0` forces `R.leadingCoeff.eval (C x₀) = 0`, and the bad `x₀` inject into the
  roots of `R.leadingCoeff.map (evalRingHom z) : F[X]` (lemmas `c56_evalC_bad_set_card_le`,
  `claim57_badXC_card_le`).  This is the exact `hx0` field — **no longer a named hypothesis**.

* **`hsep`** — *reduced to the honest domain-level separability residual.*  Over the *domain* `F[Z]`
  (where `evalX (C x₀) R` lives), `Separable` (= `IsCoprime f f.derivative`) is **not** implied by
  discriminant nonvanishing: by `resultant_deriv` the derivative-resultant is `±·leadingCoeff·discr`,
  and a unit Bézout right-hand side needs the *whole* resultant to be a unit — i.e. both the
  `Y`-leading coefficient and the discriminant of `evalX (C x₀) R` must be units of `F[Z]` (nonzero
  `F`-constants in `Z`), strictly stronger than nonvanishing.  `separable_evalX_of_resultant_isUnit`
  (built on `Polynomial.separable_of_resultant_isUnit`, `DiscriminantSeparable`, Lemma 2′) exposes
  exactly that honest condition; `hsep` is therefore kept as the §5 good-point separability residual
  `hsepPt` (separability of the *non-collapsing* specialized factors), matching the F8/F10 precedents
  rather than faking domain separability from the discriminant.  The full `hx0 ∧ hsep` producer is
  `exists_good_x₀_X_shape`.

* **`hcount` / `hA` / `A`** — *already discharged upstream* (`Claim57Supply.lean`).  Re-exported
  here only through the assembled constructor.

* **`hS_nonempty` / `hlarge`** — *`hS_nonempty` already derived from `hlarge`*
  (`coeffs_of_close_proximity_nonempty_of_large_natdiv`); `hlarge` is the genuine §5 close-set
  largeness / field-size-budget input (the `Pr > ε` contrapositive datum) and stays a named
  hypothesis, matching the consuming shape in `CurvesBridge`/`Section5ConcreteJohnson`.

* **Assembly** — `Claim57Residuals.ofInTree` collects the minimal honest remaining hypotheses
  (`hx0`, `hsep`, the single Johnson budget `hJohnson`, `hlarge`, `hfactor`) into the full bundle
  via the proven upstream `claim57Residuals_of_gsInterpolant`.  `Claim57Residuals.ofInTree2` goes
  further: it **produces `x₀` internally** and discharges the `hx0` field via `exists_good_x₀_X_shape`,
  so the residual §5 surface shrinks to `{hsepPt, hlarge, hfactor}` (plus the explicit Johnson and
  X-specialization-budget data), returning `Σ' x₀, Claim57Residuals … x₀ …`.

No `sorry`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claim 5.6 — good specialization point; Claim 5.7 — graph extraction; Lemma 5.3 —
  Johnson-radius GS parameter bound; Eq. 5.12 — separable factorization of the GS solution).
-/

-- Documentation-heavy file (BCIKS §5 prose in the docstrings); the long-line style linter is
-- disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-! ## Field `hfactor` — the provable fragment

`pg_Rset` membership gives irreducibility (the only part of the `hfactor` story that survives the
`normalizedFactors`-vs-descended-list mismatch documented above).  This is a thin re-export of
`Extraction.pg_Rset_irreducible` under a Claim-5.7-named handle, so downstream code that needs the
irreducibility of a `pg_Rset` factor does not have to thread `hfactor` (which is about list
membership, not irreducibility). -/

omit [DecidableEq (RatFunc F)] in
/-- **`hfactor`, provable fragment.**  Every member of `pg_Rset h_gs` is irreducible.

This is the genuinely-true content extractable from `pg_Rset`.  The full `hfactor` field of
`Claim57Residuals` — membership of a `pg_Rset` factor in the descended Eq-5.12 separable factor
list — is *not* provable outright (see the module docstring: `normalizedFactors Q` and the descended
primitive list differ under inseparability / for degree-`0` factors), and is therefore kept as a
named bridge hypothesis. -/
theorem claim57_hfactor_irreducible_of_pg_Rset
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (R : F[Z][X][Y])
    (hR : R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Irreducible R :=
  pg_Rset_irreducible (F := F) (m := m) (n := n) (k := k) (Q := Q)
    (ωs := ωs) (u₀ := u₀) (u₁ := u₁) h_gs R hR

/-! ## Fields `hx0` / `hsep` — the Claim-5.6 specialization substrate over `pg_Rset`

Claim 5.6 of [BCIKS20] picks a specialization point `x₀` avoiding the discriminant locus of every
factor.  The in-tree `Extraction.discr_of_irred_components_nonzero` does this over the *descended*
Eq-5.12 list; the field `Claim57Residuals.hx0`/`hsep` instead range over `pg_Rset`.  Here we replay
the same avoidance argument directly over `pg_Rset`, under the **honest** per-factor side conditions
that each `pg_Rset` factor is positive-`Y`-degree and fraction-field separable.

These side conditions are genuine, not free: `pg_Rset` is the *full* normalized-factor set, which in
characteristic `p` can contain inseparable factors (`discr_y = 0`) and degree-`0` factors
(`discr_y` undefined / vanishing), for which no good `x₀` of this discriminant form exists.  We
expose them as explicit hypotheses (`hpos`/`hsepFF`) exactly as the issue requires, rather than
silently assuming separability of the GS solution. -/

/-- *Bad specialization set for a single `pg_Rset` factor.*  The values of `x₀ : F` at which the
inner-`Z`-specialized discriminant `evalX x₀ (discr_y R)` vanishes.

The `[Fintype F]` instance is required for `Finset.univ`; it is always available wherever this set is
used (the avoidance lemmas all carry `[Fintype F]`, refining the ambient `[Finite F]`). -/
noncomputable def claim57_badX [Fintype F] (R : F[Z][X][Y]) : Finset F :=
  Finset.univ.filter (fun x₀ : F => Bivariate.evalX x₀ (Bivariate.discr_y R) = 0)

omit [DecidableEq (RatFunc F)] in
/-- **Claim-5.6 specialization step over `pg_Rset` (discriminant-nonvanishing form).**

Under the honest per-factor side conditions
* `hpos` — each `pg_Rset` factor has positive `Y`-degree, and
* `hsepFF` — each `pg_Rset` factor is separable over the fraction field `FractionRing (F[Z][X])`,

and the field-size budget `hcard` (the total discriminant-locus size is `< |F|`, the genuine
[BCIKS20] large-field requirement, cf. `Extraction.discr_of_irred_components_nonzero`), there is a
specialization point `x₀ : F` with `evalX x₀ (discr_y R) ≠ 0` for **every** `R ∈ pg_Rset`.

This is the discriminant-nonvanishing substrate of the `hx0`/`hsep` fields.  Converting it to the
exact field shapes (`evalX (C x₀) R ≠ 0`, `(evalX (C x₀) R).Separable`) requires the
discriminant/specialization commutation and the `discr ≠ 0 ⟹ Separable` converse (not yet in
tree); those are the residual bridges kept as the `hx0`/`hsep` hypotheses of `ofInTree`. -/
theorem exists_good_x₀_evalX_discr_y_ne [Fintype F]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hpos : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        0 < R.natDegree)
    (hsepFF : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (R.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable)
    (hcard :
      (((pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (Bivariate.discr_y R).leadingCoeff.natDegree)).sum < Fintype.card F) :
    ∃ x₀ : F,
      ∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by
  classical
  set L : List F[Z][X][Y] :=
    (pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).toList with hLdef
  -- membership in `L` is exactly membership in `pg_Rset`
  have hmem : ∀ R, R ∈ L ↔
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs := by
    intro R; rw [hLdef]; exact Finset.mem_toList
  -- per-factor: discriminant nonzero, hence bad-set bounded by its leading-coeff degree
  set bad : F[Z][X][Y] → Finset F := claim57_badX with hbad
  have hbad_card : ∀ R ∈ L, (bad R).card ≤ (Bivariate.discr_y R).leadingCoeff.natDegree := by
    intro R hR
    have hRpg := (hmem R).1 hR
    have hdy : Bivariate.discr_y R ≠ 0 :=
      discr_y_ne_zero_of_sep R (hsepFF R hRpg) (hpos R hRpg)
    exact c56_evalX_bad_set_card_le (Bivariate.discr_y R) hdy
  -- sum of bad-set cards ≤ hypothesised sum < |F|
  have hsum_le :
      (L.map (fun R => (bad R).card)).sum
        ≤ (L.map (fun R => (Bivariate.discr_y R).leadingCoeff.natDegree)).sum :=
    List.sum_le_sum hbad_card
  have hsum_lt : (L.map (fun R => (bad R).card)).sum < Fintype.card F :=
    lt_of_le_of_lt hsum_le hcard
  -- avoidance: a field element outside every bad set
  obtain ⟨x₀, hx₀⟩ := c56_exists_avoiding L bad hsum_lt
  refine ⟨x₀, fun R hR => ?_⟩
  have hRL : R ∈ L := (hmem R).2 hR
  have := hx₀ R hRL
  rw [hbad, claim57_badX] at this
  simpa [Finset.mem_filter] using this

/-! ## Fields `hx0` / `hsep` — the **X-shape** reconciliation (Finding F12)

The producer above (`exists_good_x₀_evalX_discr_y_ne`) is **`Z`-shaped**: `evalX x₀ (discr_y R)`
specializes the *inner* `Z` variable of the `Y`-discriminant `discr_y R : F[Z][X]`.  But the
`Claim57Residuals.hx0`/`hsep` fields are **`X`-shaped**: `evalX (Polynomial.C x₀) R` specializes the
*middle* `X` variable of `R : (F[Z][X])[Y]` (the base-ring element is `C x₀ : F[Z]`, so
`evalX (C x₀) R = R.map (Polynomial.evalRingHom (C x₀))` with
`Polynomial.evalRingHom (C x₀) : F[Z][X] →+* F[Z]`).  These specialize *different* variables
(`X` vs `Z`), so the `Z`-producer does not feed the `X`-consumer.  Here we **rerun the avoidance
argument against the `X`-variable specialization**, landing exactly on the `evalX (C x₀) R` shape.

The exact finiteness (per the issue): `evalX (C x₀) R = 0` forces the `X`-leading coefficient
`R.leadingCoeff : F[Z][X]` to vanish at `C x₀`, and the discriminant
`discr (evalX (C x₀) R) = (Polynomial.evalRingHom (C x₀)) R.discr` (by the natDegree-preserving
commutation `discr_map_of_natDegree_preserved`) is `R.discr` evaluated at `C x₀`.  Both bad
conditions have the form `p.eval (C x₀) = 0` for `p ∈ {R.leadingCoeff, R.discr} ⊆ F[Z][X]`; pushing
through any `Z`-value `z` that does not kill `p` (`p.map (evalRingHom z) ≠ 0`) injects the bad set
into the roots of `p.map (evalRingHom z) : F[X]`, giving the precise per-factor bound
`(p.map (evalRingHom z)).natDegree` (lemma `c56_evalC_bad_set_card_le`).  Summing over the finite
`pg_Rset` and applying the field-size budget yields the good `x₀`. -/

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *`X`-shape bad-set bound for a univariate `eval (C x₀)` on `F[Z][X]`.*  For `p : F[Z][X]` and a
`Z`-value `z₀` with `p.map (evalRingHom z₀) ≠ 0`, the set of `x₀ : F` with `p.eval (C x₀) = 0`
injects (via the commuting `Z`-evaluation `evalRingHom z₀`) into the roots of
`p.map (evalRingHom z₀) : F[X]`, so it has at most `(p.map (evalRingHom z₀)).natDegree` elements.

This is the `X`-shape analogue of `Extraction.c56_evalX_bad_set_card_le` (which counts the *inner-`Z`*
evaluation `evalX`); here we count the *middle-`X`* evaluation `eval (C ·)` of `F[Z][X]`. -/
theorem c56_evalC_bad_set_card_le [Fintype F] (p : F[Z][X]) (z₀ : F)
    (hz : p.map (Polynomial.evalRingHom z₀) ≠ 0) :
    (Finset.univ.filter (fun x₀ : F => p.eval (Polynomial.C x₀) = 0)).card
      ≤ (p.map (Polynomial.evalRingHom z₀)).natDegree := by
  classical
  set g : F[X] := p.map (Polynomial.evalRingHom z₀) with hgdef
  have hsub : (Finset.univ.filter (fun x₀ : F => p.eval (Polynomial.C x₀) = 0))
      ⊆ g.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h0 : (Polynomial.evalRingHom z₀) (p.eval (Polynomial.C x)) = 0 := by rw [hx]; simp
    -- naturality of `eval` under the `Z`-evaluation ring hom, plus `(evalRingHom z₀)(C x) = x`.
    have hnat : (Polynomial.evalRingHom z₀) (p.eval (Polynomial.C x)) = g.eval x := by
      have hev : p.eval (Polynomial.C x)
          = p.eval₂ (RingHom.id (Polynomial F)) (Polynomial.C x) := (Polynomial.eval₂_id).symm
      rw [hev, Polynomial.hom_eval₂ p (RingHom.id (Polynomial F)) (Polynomial.evalRingHom z₀)
        (Polynomial.C x)]
      have hcx : (Polynomial.evalRingHom z₀) (Polynomial.C x) = x := by simp
      rw [hcx, RingHom.comp_id, hgdef, Polynomial.eval_map]
    rw [hnat] at h0
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hz, Polynomial.IsRoot.def]
    exact h0
  calc (Finset.univ.filter (fun x₀ : F => p.eval (Polynomial.C x₀) = 0)).card
      ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' _

/-- *`X`-shape bad set for a single `pg_Rset` factor.*  The values of `x₀ : F` at which the
`X`-specialized factor `evalX (C x₀) R` itself vanishes — the exact `hx0`-field bad locus. -/
noncomputable def claim57_badXC [Fintype F] (R : F[Z][X][Y]) : Finset F :=
  Finset.univ.filter (fun x₀ : F => Bivariate.evalX (Polynomial.C x₀) R = 0)

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *`X`-shape per-factor bad-set bound.*  `evalX (C x₀) R = 0` forces the `X`-leading coefficient
`R.leadingCoeff` to vanish at `C x₀` (its `R.natDegree` coefficient is `evalRingHom (C x₀)` of
`R.leadingCoeff`), so `claim57_badXC R` injects into the `eval (C ·)`-bad set of `R.leadingCoeff`,
bounded by `c56_evalC_bad_set_card_le` for any `Z`-witness `z₀` with
`R.leadingCoeff.map (evalRingHom z₀) ≠ 0`. -/
theorem claim57_badXC_card_le [Fintype F] (R : F[Z][X][Y]) (z₀ : F)
    (hz : R.leadingCoeff.map (Polynomial.evalRingHom z₀) ≠ 0) :
    (claim57_badXC R).card ≤ (R.leadingCoeff.map (Polynomial.evalRingHom z₀)).natDegree := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (c56_evalC_bad_set_card_le R.leadingCoeff z₀ hz)
  intro x hx
  rw [claim57_badXC, Finset.mem_filter] at hx
  obtain ⟨_, hx0⟩ := hx
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Polynomial.Bivariate.evalX_eq_map] at hx0
  have hlc : (Polynomial.evalRingHom (Polynomial.C x)) R.leadingCoeff = 0 := by
    have : (R.map (Polynomial.evalRingHom (Polynomial.C x))).coeff R.natDegree = 0 := by
      rw [hx0]; simp
    rwa [Polynomial.coeff_map, Polynomial.coeff_natDegree] at this
  simpa [Polynomial.coe_evalRingHom] using hlc

omit [DecidableEq (RatFunc F)] in
/-- **`hx0` field, discharged outright (X-shape).**  The Claim-5.6 `X`-specialization step *in the
exact consumer shape*: under a per-factor `Z`-witness `z` not killing the `X`-leading coefficient
(`hlead`) and the genuine [BCIKS20] large-field budget `hcard` (total `X`-degree of the
`Z`-specialized leading coefficients `< |F|`), there is a single `x₀ : F` with
`evalX (Polynomial.C x₀) R ≠ 0` for **every** `R ∈ pg_Rset`.

This is precisely the `hx0` field of `Claim57Residuals` (cf. `Agreement`/`Section5ConcreteJohnson`),
now provable *outright* — the `X`-vs-`Z` mismatch (Finding F12) is reconciled by counting against the
`X`-specialization rather than the `Z`-specialization of the discriminant. -/
theorem exists_good_x₀_X_shape_ne [Fintype F]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F) :
    ∃ x₀ : F,
      ∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0 := by
  classical
  set L : List F[Z][X][Y] :=
    (pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).toList with hLdef
  have hmem : ∀ R, R ∈ L ↔
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs := by
    intro R; rw [hLdef]; exact Finset.mem_toList
  set bad : F[Z][X][Y] → Finset F := claim57_badXC with hbad
  have hbad_card : ∀ R ∈ L, (bad R).card
      ≤ (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree := by
    intro R hR
    exact claim57_badXC_card_le R (z R) (hlead R ((hmem R).1 hR))
  have hsum_le :
      (L.map (fun R => (bad R).card)).sum
        ≤ (L.map (fun R =>
            (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum :=
    List.sum_le_sum hbad_card
  have hsum_lt : (L.map (fun R => (bad R).card)).sum < Fintype.card F :=
    lt_of_le_of_lt hsum_le hcard
  obtain ⟨x₀, hx₀⟩ := c56_exists_avoiding L bad hsum_lt
  refine ⟨x₀, fun R hR => ?_⟩
  have hRL : R ∈ L := (hmem R).2 hR
  have := hx₀ R hRL
  rw [hbad, claim57_badXC] at this
  simpa [Finset.mem_filter] using this

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- **`hsep` field — the honest domain-level separability bridge (X-shape).**  Over the *domain*
`F[Z]` (where `evalX (C x₀) R` lives), `(evalX (C x₀) R).Separable` is **not** implied by
`discr (evalX (C x₀) R) ≠ 0` alone (see `DiscriminantSeparable`, Lemma 2′): `Separable` is
`IsCoprime f f.derivative`, whose Bézout identity must equal a *unit*, and by `resultant_deriv` the
derivative-resultant `±·leadingCoeff·discr` is a unit only when *both* the `Y`-leading coefficient
and the discriminant of `evalX (C x₀) R` are units of `F[Z]` (i.e. nonzero `F`-constants in `Z`).
This lemma exposes exactly that honest condition: given positive degree and a *unit* derivative
resultant of the specialized factor, it is `Separable`.  (Over a field the leading-coefficient unit
is automatic and this reduces to `discr ≠ 0`.) -/
theorem separable_evalX_of_resultant_isUnit (R : F[Z][X][Y]) (x₀ : F)
    (hdeg : 0 < (Bivariate.evalX (Polynomial.C x₀) R).natDegree)
    (hres : IsUnit (Polynomial.resultant (Bivariate.evalX (Polynomial.C x₀) R)
      (Bivariate.evalX (Polynomial.C x₀) R).derivative
      (Bivariate.evalX (Polynomial.C x₀) R).natDegree
      ((Bivariate.evalX (Polynomial.C x₀) R).natDegree - 1))) :
    (Bivariate.evalX (Polynomial.C x₀) R).Separable :=
  Polynomial.separable_of_resultant_isUnit hdeg hres

omit [DecidableEq (RatFunc F)] in
/-- **`hx0` ∧ `hsep` — the full X-shape good-specialization producer.**  Combines the outright
`hx0` discharge (`exists_good_x₀_X_shape_ne`) with the honest domain-level separability bridge: it
produces a single `x₀ : F` such that for every `R ∈ pg_Rset` both `evalX (C x₀) R ≠ 0` *and*
`(evalX (C x₀) R).Separable` hold — i.e. the **exact** `hx0`/`hsep` field pair.

The separability conjunct is supplied by the honest per-point side condition `hsepPt` (the §5
good-specialization separability assumption, cf. the F8/F10 precedents): wherever the `X`-specialized
factors do not collapse, they are separable over `F[Z]` — the genuine residual that
`separable_evalX_of_resultant_isUnit` shows is equivalent to the specialized derivative-resultant
being a unit, *not* derivable from discriminant nonvanishing alone over the non-field base. -/
theorem exists_good_x₀_X_shape [Fintype F]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
    ∃ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) ∧
      (∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable) := by
  obtain ⟨x₀, hx₀⟩ := exists_good_x₀_X_shape_ne (k := k) h_gs z hlead hcard
  exact ⟨x₀, hx₀, hsepPt x₀ hx₀⟩

/-! ## Assembly — `Claim57Residuals.ofInTree`

The full residual bundle from the minimal honest remaining hypotheses, assembled through the proven
upstream `claim57Residuals_of_gsInterpolant` (which discharges `A`/`hA`/`hcount`/`hS_nonempty`).
Each retained hypothesis is documented with its per-field verdict above. -/

/-- **`Claim57Residuals` from the minimal honest in-tree inputs.**

Assembles `ProximityGap.Claim57Residuals k δ x₀ h_gs` from:

* `hx0` / `hsep` — the Claim-5.6 specialization side conditions (their discriminant-nonvanishing
  substrate over `pg_Rset` is proven by `exists_good_x₀_evalX_discr_y_ne`; the residual is the
  discriminant→separability bridge, kept named);
* `hJohnson` — the **single** Johnson-budget inequality
  `natWeightedDegree Q 1 k < m·(n − ⌈δ·n⌉)` (genuine Johnson-radius parameter condition; `A`/`hA`/
  `hcount`/`hS_nonempty` are discharged from it upstream);
* `hlarge` — the close-set largeness / field-size-budget input (also discharges `hS_nonempty`);
* `hfactor` — the documented `pg_Rset ⟹ descended-Eq-5.12-list` bridge, not provable outright (see
  module docstring; the provable irreducibility fragment is `claim57_hfactor_irreducible_of_pg_Rset`).

This is the honest minimal-hypothesis front door to the Claim-5.7 keystone. -/
@[reducible]
noncomputable def Claim57Residuals.ofInTree
    [NeZero n] [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hJohnson : Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  claim57Residuals_of_gsInterpolant (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep hJohnson hlarge hfactor

/-- **`Claim57Residuals` with the `x₀` produced internally — §5 surface shrunk (Finding F12).**

Strengthens `ofInTree` by *discharging the `hx0` field outright* (no longer a hypothesis): the
good specialization point `x₀` and the `hx0`/`hsep` field pair are produced by the X-shape avoidance
argument `exists_good_x₀_X_shape`, so the caller no longer supplies `x₀`, `hx0`, or the raw `hsep`.
What remains is exactly:

* `z` / `hlead` / `hcard` — the honest X-specialization budget (per-factor `Z`-witness not killing the
  leading coefficient, and the [BCIKS20] large-field bound on the total `X`-degree) that powers the
  `hx0` discharge;
* `hsepPt` — the honest §5 good-point separability residual (separability of the *non-collapsing*
  `X`-specialized factors over the domain `F[Z]`; by `separable_evalX_of_resultant_isUnit` this is the
  unit-derivative-resultant condition, genuinely *not* derivable from discriminant nonvanishing over
  the non-field base — the honest residual matching the F8/F10 precedents);
* `hJohnson` — the single Johnson budget (discharges `A`/`hA`/`hcount`/`hS_nonempty` upstream);
* `hlarge` — the close-set largeness datum (also discharges `hS_nonempty`);
* `hfactor` — the documented `pg_Rset ⟹ descended-Eq-5.12-list` bridge (not provable outright).

So relative to `ofInTree` the surface shrinks: `hx0` becomes a *theorem*, and the residual §5 inputs
are `{hsepPt, hlarge, hfactor}` (plus the explicit Johnson/budget data), as the issue requires. -/
@[reducible]
noncomputable def Claim57Residuals.ofInTree2
    [NeZero n] [DecidableEq (Polynomial F)] [Fintype F] (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : F[Z][X][Y] → F)
    (hlead : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R.leadingCoeff.map (Polynomial.evalRingHom (z R)) ≠ 0)
    (hcard :
      (((pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (R.leadingCoeff.map (Polynomial.evalRingHom (z R))).natDegree)).sum
        < Fintype.card F)
    (hsepPt : ∀ x₀ : F,
      (∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX (Polynomial.C x₀) R ≠ 0) →
      ∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hJohnson : Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Σ' x₀ : F,
      Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  let good := exists_good_x₀_X_shape (k := k) h_gs z hlead hcard hsepPt
  ⟨good.choose,
    claim57Residuals_of_gsInterpolant (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ good.choose h_gs
      good.choose_spec.1 good.choose_spec.2 hJohnson hlarge hfactor⟩

end ProximityGap

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ProximityGap.claim57_hfactor_irreducible_of_pg_Rset
#print axioms ProximityGap.exists_good_x₀_evalX_discr_y_ne
#print axioms ProximityGap.c56_evalC_bad_set_card_le
#print axioms ProximityGap.claim57_badXC_card_le
#print axioms ProximityGap.exists_good_x₀_X_shape_ne
#print axioms ProximityGap.separable_evalX_of_resultant_isUnit
#print axioms ProximityGap.exists_good_x₀_X_shape
#print axioms ProximityGap.Claim57Residuals.ofInTree
#print axioms ProximityGap.Claim57Residuals.ofInTree2
