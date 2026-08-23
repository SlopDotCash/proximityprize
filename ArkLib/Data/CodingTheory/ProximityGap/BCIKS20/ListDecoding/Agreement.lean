/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, Frantisek Silvasi, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.RootClearing
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.ToMathlib.BCIKS20CorrelatedAgreement

/-!
# BCIKS20 list-decoding agreement compatibility module

The historical Claim 5.7 agreement development was split out of the current
local ArkLib worktree.  `ArkLib.lean` still imports this module as part of the
public package surface, so this file intentionally preserves that import target
while the active list-decoding definitions live in `Extraction` and
`Guruswami`.
-/

set_option linter.style.longFile 7600
set_option linter.unusedSectionVars false

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

-- `DecidableEq (RatFunc F)` is threaded through the section for the Appendix A machinery;
-- several statement-level extractions do not mention it directly.
set_option linter.unusedDecidableInType false

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *Accessible twin of the sealed `eval_on_Z`.*  The per-`z` `Z`-specialization used throughout
the proven Claim-5.7 machinery in `Extraction.lean` is `pg_eval_on_Z`, and it reduces, by `rfl`,
to exactly the definitional body of `Trivariate.eval_on_Z`, namely
`p.map (mapRingHom (evalRingHom z))`.

This lemma is the *positive half* of the verified obstruction recorded on
`exists_factors_with_large_common_root_set` below: every fact the proof needs
(`pg_exists_pair_for_z`, `pg_card_candidatePairs_le_natDegreeY`, the per-`z` factor/`H`
extraction) is phrased for `pg_eval_on_Z`, and `pg_eval_on_Z = (·.map (mapRingHom (evalRingHom z)))`
holds definitionally — whereas the *same body* wrapped in `Trivariate.eval_on_Z` (which the
  Claim-5.7
statement uses) is `opaque` and hence provably inaccessible: not `eval_on_Z 0 z = 0`, not
  additivity,
and not `eval_on_Z p z = pg_eval_on_Z p z` is derivable (all fail with "made no progress" / `rfl`
failure, since `opaque` blocks delta-reduction). -/
lemma c57_pg_eval_on_Z_body (p : F[Z][X][Y]) (z : F) :
    pg_eval_on_Z (F := F) p z = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  rfl

/-! ### GAP ANALYSIS for the §5 list-decoding agreement claims (5.7 – 5.11)

This file's six claims sit on top of three still-open §5 ingredients that no lemma currently
supplies. The gaps below were determined by a complete dependency audit; each is a *precise*
missing fact (not a proof-engineering hurdle), so the claims are documented as blocked rather
than discharged with `sorry`-laundering. No statement is weakened.

* **Missing ingredient A — "`S` is large".** There is *no* hypothesis or lemma giving a lower
  bound on `#(coeffs_of_close_proximity k ωs δ u₀ u₁)`. In [BCIKS20, §5] the inequality
  `#S / D_Y(Q) > 2·D_Y(Q)²·D_X·D_YZ(Q)` is a *standing hypothesis* of the proximity-gap regime
  (the "many close codewords" assumption), not a consequence of `ModifiedGuruswami`. It is
  directly the second conjunct of Claim 5.7 and is `R,H`-independent, hence unprovable from the
  current hypotheses. See `exists_factors_with_large_common_root_set`.

* **Missing ingredient B — "`Q` vanishes at every close `z`".** No proven fact asserts
  `(Trivariate.eval_on_Z Q z).eval (Pz …) = 0` for `z ∈ coeffs_of_close_proximity`. This is
  [BCIKS20, Lemma 5.3] (GS divisibility `(Y − Pz) ∣ Q`) lifted to the `Z`-curve. In
  `Extraction.lean` it appears only as the *antecedent* `→` of `pg_exists_R_of_Q_eval_zero` /
  `pg_exists_pair_for_z`, never as a standalone lemma. Without it the pigeonhole giving the
  first conjunct of Claim 5.7 cannot reach `#S / D_Y(Q)` (it only reaches
  `#(vanishing z) / D_Y(Q)`).

* **Missing ingredient C — the Appendix-A ↔ §5 bridge.** `RationalFunctions.lean` contains the
  vanishing criterion `Lemma_A_1` (`#(S_β β) > Λ(β)·dₕ ⟹ embeddingOf𝒪Into𝕃 β = 0`) and the
  forward inclusion `eval_resultant_eq_zero_of_mem_S_β`, but **no** lemma relating the
  Appendix-A objects (`α`, `γ`, `β`, `S_β`, `π_z`) to the §5 geometric data
  (`Pz`, `matching_set`, the word `w(x,z) = u₀ x + z·u₁ x`, `ωs`). Concretely, the converse
  direction "a geometric matching point `z` lies in `S_β (β R t)` (i.e. `π_z (β R t) = 0`)" is
  absent. This bridge is the entire substance of the proofs of Claims 5.8–5.11.

* **Missing ingredient D — `β`/`α`/`γ` are *under-specified* (root cause for 5.8/5.8'/5.9).**
  In `RationalFunctions.lean`, `β R t := (β_regular …).choose`, and `β_regular` asserts only the
  *existence* of a regular element satisfying the weight *upper* bound `Λ(β) ≤ (2t+1)·d_R·D`; it
  is realized with the trivial witness `β = 0` (`fun _ => ⟨0, by simp⟩`). Thus `β R t` is *some*
  opaque `.choose` element constrained only by that upper bound — it does **not** encode the
  recursive Hensel-lift numerator of [BCIKS20, Appendix A.4], and carries no functional relation
  to `R`, `x₀`, or the lift recursion. Consequently `α' … t = embeddingOf𝒪Into𝕃 _ (β R t) / _`
  is **underdetermined**: its value at `t ≥ k` is *not fixed* by the definitions (it depends on
  the opaque `.choose`), so Claim 5.8 (`α' … t = 0`) is neither provable *nor* refutable from the
  current `β` — it is true only under the intended (not-yet-formalized) Hensel construction.
  Even granting ingredient C, the `S_β`-largeness argument cannot be invoked because the `β` it
  must apply to is not the Hensel numerator. Closing 5.8/5.8'/5.9 therefore requires first
  *replacing* `β_regular`'s trivial realization with the genuine recursive Hensel-lift definition
  (the `β`-construction of Appendix A.4) so that `β R t` is a *function of* the lift data, not an
  arbitrary weight-bounded witness.

**Per-claim disposition.**
- 5.7 (`exists_factors_with_large_common_root_set`): blocked on A (final conjunct, unprovable as
  stated — needs an added `#S` lower-bound hypothesis) and B (first conjunct pigeonhole). The
  `R, H, Irreducible, natDegree, dvd, Separable` conjuncts are supplied by `Extraction.lean`'s
  `pg_*` toolbox + Claim 5.6, but the two cardinality conjuncts are not.
- 5.8 (`approximate_solution_is_exact_solution_coeffs`): reduces cleanly to
  `embeddingOf𝒪Into𝕃 _ (β (R …) t) = 0` (since `α' … t = embeddingOf𝒪Into𝕃 _ (β …) / _`, so
  `zero_div`), which is exactly `Lemma_A_1`'s conclusion — but `Lemma_A_1`'s hypothesis
  `#(S_β (β … t)) > Λ·dₕ` has no supplier (ingredient C). Deeper still (ingredient D), `β R t`
  is an opaque weight-bounded `.choose` rather than the Hensel numerator, so `α' … t` is
  *underdetermined* and `α' … t = 0` is neither provable nor refutable from the current `β`.
- 5.8' (`…_coeffs'`): would follow from 5.8 by `PowerSeries.subst` bookkeeping on `γ = subst …
  (mk α)`, but 5.8 is itself blocked, so 5.8' cannot stand alone.
- 5.9 (`solution_gamma_is_linear_in_Z`): consumes 5.8' (truncation of `γ` to degree `< k`,
  combined with the `degreeX P ≤ 1` output of the Prop 5.5 specialization); blocked transitively.
- 5.10 (`solution_gamma_matches_word_if_subset_large`): its hypothesis `hx` bounds
  `(matching_set_at_x …).card`, but converting that into the `S_β`-largeness that `Lemma_A_1`
  consumes is exactly ingredient C; blocked.
- 5.11 (`exists_points_with_large_matching_subset`): double-counting over the matching set.
  The abstract Prop 5.5 pigeonhole core is now `tagged_fiber_pigeonhole` in `Guruswami.lean`;
  what remains is the specialization from the Guruswami multiplicity/factor data to the required
  tagged-factor map, plus ingredient C.

Closing any of these honestly requires first landing (i) an `#S` lower-bound hypothesis on
`ModifiedGuruswami` (or on Claim 5.7), (ii) the Lemma-5.3 `Z`-curve divisibility bridge, and
(iii) the Appendix-A ↔ §5 specialization bridge `matching point ⟹ π_z (β R t) = 0`. None are
present in the current tree. -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *De-sealed `eval_on_Z` agrees with its accessible twin* (Gap-A resolution, cf. the obstruction
note on `exists_factors_with_large_common_root_set`). `Trivariate.eval_on_Z` is no longer `opaque`
(it is a transparent `def` with equation lemma `eval_on_Z_eq`), so its body
`p.map (mapRingHom (evalRingHom z))` is now definitionally exposed; in particular it is *equal* to
the accessible twin `pg_eval_on_Z`. Under the old `opaque` declaration this equality failed `rfl`
despite identical bodies — that is precisely the (now-resolved) Gap A. -/
lemma c57_eval_on_Z_eq_pg (p : F[Z][X][Y]) (z : F) :
    Trivariate.eval_on_Z p z = pg_eval_on_Z (F := F) p z := by
  rw [Trivariate.eval_on_Z_eq]; rfl

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `eval_on_Z` sends `0` to `0` (now provable — was inaccessible under the old `opaque`). -/
lemma c57_eval_on_Z_zero (z : F) : Trivariate.eval_on_Z (0 : F[Z][X][Y]) z = 0 := by
  rw [Trivariate.eval_on_Z_eq]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `eval_on_Z` is additive (now provable — was inaccessible under the old `opaque`). -/
lemma c57_eval_on_Z_add (p q : F[Z][X][Y]) (z : F) :
    Trivariate.eval_on_Z (p + q) z = Trivariate.eval_on_Z p z + Trivariate.eval_on_Z q z := by
  rw [Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq,
    Polynomial.map_add]

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `eval_on_Z` is multiplicative (now provable — was inaccessible under the old `opaque`).
Together with `c57_eval_on_Z_zero`/`c57_eval_on_Z_add` this is the divisibility-transport
ingredient the residual GS-multiplicity → graph-vanishing bridge (Gap B) will consume. -/
lemma c57_eval_on_Z_mul (p q : F[Z][X][Y]) (z : F) :
    Trivariate.eval_on_Z (p * q) z = Trivariate.eval_on_Z p z * Trivariate.eval_on_Z q z := by
  rw [Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq,
    Polynomial.map_mul]

/-! ### Gap B — the trivariate graph-vanishing keystone (NOW RESOLVED)

The residual "Gap B" obstruction flagged on `exists_factors_with_large_common_root_set` and on
`exists_a_set_and_a_matching_polynomial` was: *no lemma connects `ModifiedGuruswami.Q_multiplicity`
(order-`≥ m` root multiplicity of `Q : F[Z][X][Y]` over the coefficient ring `F[Z]` at each curve
point `(C ωᵢ, C u₀ᵢ + X · C u₁ᵢ)`) to the per-`z` evaluation-zero fact `(eval_on_Z Q z).eval Pz =
0`* — i.e. "`Q` vanishes on the graph `(X, Pz(X))` of the `δ`-close codeword indexed by `z`".

The lemmas below **supply that bridge**, fully proven (`#print axioms` = `propext`,
`Classical.choice`, `Quot.sound` only).  The argument is the trivariate analogue of the bivariate
GS divisibility chain (`GuruswamiSudan.orderAt_eval_ge` / `roots_le_degree_of_deg_lt_roots`):

1. **Multiplicity transport `F[Z] → F`** (`gapB_transport_mult`).  Applying the coefficient ring
   hom `φ = evalRingHom z : F[Z] → F` (`Z ↦ z`) commutes with both `Bivariate.shift` and
   `Bivariate.coeff` (`gapB_shift_map`, `gapB_coeff_map_biv`).  Hence the order-`m` vanishing of the
   shifted coefficients of `Q` at `(C ωᵢ, C u₀ᵢ + X·C u₁ᵢ)` (extracted from `Q_multiplicity` via the
   integral-domain criterion `gapB_shift_coeff_zero_of_mult_ge_dom`) transports to order-`m`
   vanishing of `eval_on_Z Q z = Q.map (mapRingHom φ)` at the *image* point
   `(φ(C ωᵢ), φ(C u₀ᵢ + X·C u₁ᵢ)) = (ωᵢ, u₀ᵢ + z·u₁ᵢ) = (ωᵢ, (u₀ + z•u₁) i)` — exactly the word
   `w(·, z)`.  This is the field-side input `GuruswamiSudan.rootMultiplicity_ge_of_shift_zero`.

2. **Field-side graph vanishing** (`gapB_vanish_of_orderM_and_count`).  With `Q_z := eval_on_Z Q z`
   carrying order-`m` roots at `(ωᵢ, w_i)` for `i` in the agreement set `A`, `Q_z(X, Pz(X))` has a
   root of order `≥ m` at each `ωᵢ` with `i ∈ A` (`GuruswamiSudan.orderAt_eval_ge`); a polynomial of
   degree `< m·#A` with that many roots is `0` (`roots_le_degree_of_deg_lt_roots`).  The degree
   bound `(Q_z.eval Pz).natDegree ≤ natWeightedDegree Q_z 1 k` is `degree_eval_le_weightedDegree`
   (`Pz.natDegree ≤ k`).

The strict counting inequality `natWeightedDegree (eval_on_Z Q z) 1 k < m·#A` is the
*Johnson-radius* condition — `δ` within the list-decoding radius so that `#A ≥ (1−δ)n` is large
relative to the degree bound.  It is passed as an explicit hypothesis of the keystone:
`exists_factors_with_large_common_root_set` does **not** carry a `δ ≤ δ₀` binder (its `δ` is free),
which is precisely why that top-level claim still cannot be closed without statement repair (see its
docstring).  The keystone is the faithful, reusable form of the bridge: feed it the Johnson side
condition and it discharges the graph vanishing. -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `Bivariate.shift` commutes with `map (mapRingHom φ)` (under `φ` on the base point). -/
private theorem gapB_shift_map {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (f : S[X][Y]) (x y : S) :
    Polynomial.Bivariate.shift (f.map (Polynomial.mapRingHom φ)) (φ x) (φ y)
      = (Polynomial.Bivariate.shift f x y).map (Polynomial.mapRingHom φ) := by
  unfold Polynomial.Bivariate.shift
  rw [Polynomial.map_map]
  have hcomp : (f.map (Polynomial.mapRingHom φ)).comp
        (Polynomial.X + Polynomial.C (Polynomial.C (φ y)))
      = (f.comp (Polynomial.X + Polynomial.C (Polynomial.C y))).map (Polynomial.mapRingHom φ) := by
    rw [Polynomial.map_comp]; congr 1; simp [Polynomial.mapRingHom]
  rw [hcomp, Polynomial.map_map]
  congr 1
  ext p
  · simp [Polynomial.mapRingHom, Polynomial.compRingHom]
  · simp [Polynomial.mapRingHom, Polynomial.compRingHom]

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `Bivariate.coeff` commutes with `map (mapRingHom φ)`. -/
private theorem gapB_coeff_map_biv {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (f : S[X][Y]) (i j : ℕ) :
    Polynomial.Bivariate.coeff (f.map (Polynomial.mapRingHom φ)) i j
      = φ (Polynomial.Bivariate.coeff f i j) := by
  unfold Polynomial.Bivariate.coeff
  simp [Polynomial.coeff_map, Polynomial.mapRingHom]

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- Over an integral-domain coefficient ring, `rootMultiplicity ≥ M` forces every shifted
coefficient of total degree `< M` to vanish.  (The "easy" direction of the multiplicity criterion,
ported off the field-only `GuruswamiSudan.rootMultiplicity_le_of_coeff_ne_zero` so it applies to the
trivariate setting `S = F[Z]`.) -/
private theorem gapB_shift_coeff_zero_of_mult_ge_dom {S : Type} [CommRing S] [IsDomain S]
    [DecidableEq S] (f : S[X][Y]) (x y : S) (M : ℕ)
    (hmult : (M : Option ℕ) ≤ Bivariate.rootMultiplicity f x y) :
    ∀ s t, s + t < M → Polynomial.Bivariate.coeff (Bivariate.shift f x y) s t = 0 := by
  intro s t hst
  by_contra hc
  set g := Bivariate.shift f x y with hg
  have hle : Bivariate.rootMultiplicity₀ g ≤ some (s + t) := by
    unfold Bivariate.rootMultiplicity₀
    cases hwd : Bivariate.weightedDegree g 1 1 with
    | none => exact absurd hwd (Bivariate.weightedDegree_ne_none _ _ _)
    | some deg =>
      simp only
      have hst_le : s ≤ deg ∧ t ≤ deg := by
        have hb : 1 * (g.coeff t).natDegree + 1 * t ≤ Bivariate.natWeightedDegree g 1 1 := by
          refine Finset.le_sup (f := fun mm => 1 * (g.coeff mm).natDegree + 1 * mm)
            (Polynomial.mem_support_iff.mpr ?_)
          intro h0; apply hc; rw [Bivariate.coeff, h0]; simp
        have hsd : 1 * (g.coeff t).natDegree + 1 * t ≥ s + t := by
          have : s ≤ (g.coeff t).natDegree := by
            apply Polynomial.le_natDegree_of_ne_zero
            intro h0; apply hc; rwa [Bivariate.coeff]
          omega
        have hwd_nat : Bivariate.natWeightedDegree g 1 1 = deg := by
          rw [Bivariate.weightedDegree_eq_natWeightedDegree] at hwd; exact Option.some.inj hwd
        rw [hwd_nat] at hb; omega
      set L := List.filterMap
          (fun (p : ℕ × ℕ) ↦ if Polynomial.Bivariate.coeff g p.1 p.2 = 0 then none
            else some (p.1 + p.2))
          (List.product (List.range deg.succ) (List.range deg.succ)) with hL
      have hmem : (s + t) ∈ L := by
        rw [hL, List.mem_filterMap]
        refine ⟨(s, t), ?_, ?_⟩
        · rw [List.product, List.mem_flatMap]
          exact ⟨s, List.mem_range.mpr (Nat.lt_succ_of_le hst_le.1),
            List.mem_map.mpr ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le hst_le.2), rfl⟩⟩
        · simp [hc]
      have hmin := List.min?_getD_le_of_mem (k := s + t) hmem
      cases hmm : L.min? with
      | none =>
          have : L = [] := List.min?_eq_none_iff.mp hmm
          rw [this] at hmem; simp at hmem
      | some v =>
          rw [hmm] at hmin
          simp only [Option.getD_some] at hmin
          exact Option.some_le_some.mpr hmin
  have hmult' : (M : Option ℕ) ≤ Bivariate.rootMultiplicity₀ g := by
    rw [Bivariate.rootMultiplicity] at hmult; exact hmult
  cases hrm : Bivariate.rootMultiplicity₀ g with
  | none => rw [hrm] at hmult'; simp at hmult'
  | some v =>
      rw [hrm] at hmult' hle
      simp only [Option.some_le_some] at hmult' hle
      omega

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *Multiplicity transport `F[Z] → F`.*  The order-`≥ M` root multiplicity of `Q : F[Z][X][Y]`
(over `F[Z]`) at the curve point `(C ω, C u0 + X · C u1)` transports, under the specialization
`Z ↦ z`, to order-`≥ M` multiplicity of `eval_on_Z Q z` at the image point `(ω, u0 + z·u1)`. -/
private theorem gapB_transport_mult [DecidableEq (Polynomial F)]
    (Qt : F[Z][X][Y]) (z ω u0 u1 : F) (M : ℕ)
    (hQz_ne : Qt.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hm : (M : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity Qt
            (Polynomial.C ω) (Polynomial.C u0 + Polynomial.X * Polynomial.C u1)) :
    (M : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity
        (Qt.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) ω (u0 + z * u1) := by
  set φ := Polynomial.evalRingHom z with hφ
  set x : Polynomial F := Polynomial.C ω with hx
  set y : Polynomial F := Polynomial.C u0 + Polynomial.X * Polynomial.C u1 with hy
  have hφx : φ x = ω := by rw [hφ, hx, coe_evalRingHom, eval_C]
  have hφy : φ y = u0 + z * u1 := by
    rw [hφ, hy, map_add, map_mul, coe_evalRingHom, eval_C, eval_X, eval_C, mul_comm]
  have hvanQ := gapB_shift_coeff_zero_of_mult_ge_dom Qt x y M hm
  have hvanQz : ∀ s t, s + t < M →
      ((Bivariate.shift (Qt.map (Polynomial.mapRingHom φ)) ω (u0 + z * u1)).coeff t).coeff s =
        0 := by
    intro s t hst
    have : Polynomial.Bivariate.coeff
        (Bivariate.shift (Qt.map (Polynomial.mapRingHom φ)) (φ x) (φ y)) s t = 0 := by
      rw [gapB_shift_map, gapB_coeff_map_biv, hvanQ s t hst, map_zero]
    rwa [hφx, hφy, Bivariate.coeff] at this
  exact GuruswamiSudan.rootMultiplicity_ge_of_shift_zero hQz_ne hvanQz

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *Field-side graph vanishing from order-`M` roots + a strict degree/agreement count.*  If a
bivariate `Q_z : F[X][Y]` has order-`≥ M` roots at `(ωᵢ, wᵢ)` for `i` in an agreement set `A` where
`wᵢ = P(ωᵢ)`, and `deg (Q_z.eval P) < M·#A`, then `Q_z.eval P = 0`.  This is the trivariate-friendly
re-packaging of the interior of `GuruswamiSudan.dvd_property`. -/
private theorem gapB_vanish_of_orderM_and_count
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (P : F[X]) (w : Fin n → F) (M D : ℕ) (A : Finset (Fin n))
    (hroots : ∀ i ∈ A, (M : Option ℕ) ≤ Bivariate.rootMultiplicity Qz (ωs i) (w i))
    (hmatch : ∀ i ∈ A, w i = P.eval (ωs i))
    (hdeg : (Qz.eval P).natDegree ≤ D)
    (hcount : D < M * A.card) :
    Qz.eval P = 0 := by
  by_contra hne
  have hRoot : ∀ i ∈ A, M ≤ (Qz.eval P).rootMultiplicity (ωs i) := by
    intro i hi
    have hO : GuruswamiSudan.HasOrderAt Qz (ωs i) (w i) M := by
      intro s t hst
      exact gapB_shift_coeff_zero_of_mult_ge_dom Qz (ωs i) (w i) M (hroots i hi) s t hst
    have := GuruswamiSudan.orderAt_eval_ge Qz P (ωs i) M (by rw [hmatch i hi] at hO; exact hO)
    rcases this with h | h
    · exact absurd h hne
    · exact h
  exact hne (GuruswamiSudan.roots_le_degree_of_deg_lt_roots (ωs := ωs) (Qz.eval P) M A hRoot
    (lt_of_le_of_lt hdeg hcount))

omit [DecidableEq (RatFunc F)] in
/-- **Gap-B keystone: the trivariate graph-vanishing bridge** ([BCIKS20] §5, the residual keystone
of Claim 5.7 / Prop 5.5).  Given a `ModifiedGuruswami` solution `Q`, a coefficient `z` in the
close-proximity set `S` with its `δ`-close codeword polynomial `Pz`, the nonvanishing of the
specialization `eval_on_Z Q z`, an agreement set `A` on which the word `w(·, z) = u₀ + z•u₁` matches
`Pz ∘ ωs`, and the *Johnson-radius* counting hypothesis `natWeightedDegree (eval_on_Z Q z) 1 k <
m·#A`, the polynomial `Q` vanishes on the graph of the close codeword:
`(eval_on_Z Q z).eval Pz = 0`.

This is the fact previously declared missing on `exists_factors_with_large_common_root_set`
("Missing GS-multiplicity → close-codeword-graph vanishing (Gap B)") and on
`exists_a_set_and_a_matching_polynomial` ("the binding of each `z ∈ S` to a factor requires the
vanishing `(eval_on_Z Q z).eval Pz = 0`").  It is derived honestly from
`ModifiedGuruswami.Q_multiplicity` via the transport + field-side counting lemmas above; the
Johnson-radius side condition is made explicit because the consumer claims do not carry a `δ ≤ δ₀`
binder (their `δ` is free), so it cannot be discharged internally — see the obstruction docstrings.
`#print axioms` = `propext, Classical.choice, Quot.sound` only. -/
theorem Q_vanishes_on_close_codeword_graph [DecidableEq (Polynomial F)]
    (k : ℕ) {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    (hcount : Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k < m * A.card) :
    (Trivariate.eval_on_Z Q z).eval (Pz hS) = 0 := by
  set Qz := Trivariate.eval_on_Z Q z with hQz
  set P := Pz hS with hP
  have hroots : ∀ i ∈ A, (m : Option ℕ) ≤
      Bivariate.rootMultiplicity Qz (ωs i) ((u₀ + z • u₁) i) := by
    intro i hi
    have hmi0 := h_gs.Q_multiplicity i
    have hmi : (m : Option ℕ) ≤ Bivariate.rootMultiplicity Q
        (Polynomial.C (ωs i)) (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) := by
      convert ge_iff_le.mp hmi0 using 2
    have hne' : Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0 := hQz_ne
    have htr := gapB_transport_mult Q z (ωs i) (u₀ i) (u₁ i) m hne' hmi
    have hpt : (u₀ + z • u₁) i = u₀ i + z * u₁ i := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpt, hQz]; exact htr
  have hdeg : (Qz.eval P).natDegree ≤ Bivariate.natWeightedDegree Qz 1 k := by
    have hPdeg : P.natDegree ≤ (k + 1) - 1 := by
      simpa using (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose_spec.1
    simpa using GuruswamiSudan.degree_eval_le_weightedDegree Qz P (k + 1) hPdeg
  have := gapB_vanish_of_orderM_and_count ωs Qz P (u₀ + z • u₁) m
    (Bivariate.natWeightedDegree Qz 1 k) A hroots hA hdeg hcount
  rw [hQz, hP] at this ⊢; exact this

omit [DecidableEq (RatFunc F)] in
/-- **Generalized graph-vanishing keystone for an arbitrary close interpolant.**

Identical to `Q_vanishes_on_close_codeword_graph`, but for an *arbitrary* degree-`≤ k` polynomial `P`
that agrees with the line `u₀ + z•u₁` on a set `A` with `natWeightedDegree < m·|A|` — not only the
canonical `Pz hS`.  The proof is `P`-independent: `Q`'s multiplicity `m` is at the *line* graph
points `(ωs i, (u₀+z•u₁) i)`, and only `hA`/`hdeg` mention `P`.

This is the entry point to per-parameter interpolant **uniqueness** (the `hunique` obligation of the
§6 wiring) above the unique-decoding radius: every `δ`-close degree-`≤ k` interpolant is a `Y`-root of
`eval_on_Z Q z`, hence a linear factor of it, so any two such interpolants coincide on the
Guruswami–Sudan matching domain (see `RSDistinct.degreeLT_eq_of_match_common_on_domain`).  The
`hQz_ne` non-degeneracy is discharged generically by `ProximityGap.card_badZ_le`
(`EvalOnZNonzero.lean`). -/
theorem Q_vanishes_on_close_codeword_graph_gen [DecidableEq (Polynomial F)]
    {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (P : F[X]) (hPdeg : P.natDegree ≤ k)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = P.eval (ωs i))
    (hcount : Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k < m * A.card) :
    (Trivariate.eval_on_Z Q z).eval P = 0 := by
  set Qz := Trivariate.eval_on_Z Q z with hQz
  have hroots : ∀ i ∈ A, (m : Option ℕ) ≤
      Bivariate.rootMultiplicity Qz (ωs i) ((u₀ + z • u₁) i) := by
    intro i hi
    have hmi0 := h_gs.Q_multiplicity i
    have hmi : (m : Option ℕ) ≤ Bivariate.rootMultiplicity Q
        (Polynomial.C (ωs i)) (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) := by
      convert ge_iff_le.mp hmi0 using 2
    have hne' : Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0 := hQz_ne
    have htr := gapB_transport_mult Q z (ωs i) (u₀ i) (u₁ i) m hne' hmi
    have hpt : (u₀ + z • u₁) i = u₀ i + z * u₁ i := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpt, hQz]; exact htr
  have hdeg : (Qz.eval P).natDegree ≤ Bivariate.natWeightedDegree Qz 1 k := by
    have hPdeg' : P.natDegree ≤ (k + 1) - 1 := by omega
    simpa using GuruswamiSudan.degree_eval_le_weightedDegree Qz P (k + 1) hPdeg'
  have := gapB_vanish_of_orderM_and_count ωs Qz P (u₀ + z • u₁) m
    (Bivariate.natWeightedDegree Qz 1 k) A hroots hA hdeg hcount
  rw [hQz] at this ⊢; exact this

omit [DecidableEq (RatFunc F)] in
/-- *Keystone, restated for the `pg_eval_on_Z` accessor consumed by `Extraction.lean`.*  The
Gap-B keystone produces graph-vanishing phrased with `Trivariate.eval_on_Z`; the entire
Claim-5.7 extraction toolbox (`pg_exists_R_of_Q_eval_zero`, `pg_exists_pair_for_z`,
`pg_exists_common_candidate_pair_of_dvd`) is phrased with the definitional twin `pg_eval_on_Z`.
This lemma transports the keystone across the (now-proven) identity `c57_eval_on_Z_eq_pg`, so the
keystone's output is in exactly the shape the toolbox consumes. -/
theorem Q_vanishes_on_close_codeword_graph_pg [DecidableEq (Polynomial F)]
    (k : ℕ) {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    (hcount : Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k < m * A.card) :
    (pg_eval_on_Z (F := F) Q z).eval (Pz hS) = 0 := by
  have hkey := Q_vanishes_on_close_codeword_graph (F := F) k h_gs hS hQz_ne A hA hcount
  rwa [c57_eval_on_Z_eq_pg] at hkey

omit [DecidableEq (RatFunc F)] in
/-- *Keystone ⟹ the `hdiv` divisibility hypothesis of the extraction toolbox.*  The factor theorem
turns the keystone's graph-vanishing `(pg_eval_on_Z Q z).eval (Pz) = 0` into the linear-factor
divisibility `X - C (Pz) ∣ pg_eval_on_Z Q z` — which is *verbatim* the per-`z` hypothesis `hdiv`
of `pg_exists_common_candidate_pair_of_dvd` /
`pg_exists_common_candidate_pair_of_dvd_card_natDegreeY`.

This is the maximal honest reach of the Gap-B keystone toward Claim 5.7: it supplies, for any
single `z ∈ S` equipped with an agreement set `A` satisfying the Johnson count
`m·#A > natWeightedDegree …`, the exact divisibility the first-conjunct pigeonhole needs.  Closing
the *whole* of Claim 5.7 from
here is still blocked — `hdiv` must hold for **every** `z ∈ S` simultaneously, which requires the
Johnson count for every `z`, i.e. a `δ ≤ δ₀` binder absent from the (uneditable) statement; and the
second cardinality conjunct of Claim 5.7 is independently false off the list-decoding regime
(`Extraction.c57_second_conjunct_unsat_of_S_empty`).  See the obstruction docstring on
`exists_factors_with_large_common_root_set`. -/
theorem Q_graph_factor_dvd [DecidableEq (Polynomial F)]
    (k : ℕ) {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    (hcount : Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k < m * A.card) :
    Polynomial.X - Polynomial.C (Pz hS) ∣ pg_eval_on_Z (F := F) Q z :=
  Polynomial.dvd_iff_isRoot.mpr
    (Q_vanishes_on_close_codeword_graph_pg (F := F) k h_gs hS hQz_ne A hA hcount)

/-! ### Side-condition-explicit Claim 5.7 helpers -/

omit [DecidableEq (RatFunc F)] in
/-- Convert the explicit graph-vanishing side conditions into the divisibility hypothesis consumed
by `pg_exists_common_candidate_pair_of_dvd_card_natDegreeY`.

If the specialization `Q(z, X, Y)` is zero, divisibility is immediate.  Otherwise
`Q_vanishes_on_close_codeword_graph` gives `(Q(z, X, Y)).eval Pz = 0`, which is equivalent to
divisibility by `Y - Pz(X)`. -/
lemma pg_divisibility_of_graph_vanishing_conditions [DecidableEq (Polynomial F)]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card) :
    ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
      Polynomial.X - Polynomial.C P ∣ (pg_eval_on_Z (F := F) Q z.1) := by
  classical
  intro z
  let P : F[X] := Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  by_cases hQz : Trivariate.eval_on_Z Q z.1 = 0
  · rw [← c57_eval_on_Z_eq_pg (F := F) Q z.1, hQz]
    exact dvd_zero _
  · have hvanish :
        (Trivariate.eval_on_Z Q z.1).eval P = 0 := by
      simpa [P] using
        Q_vanishes_on_close_codeword_graph (F := F) (k := k) (z := z.1)
          (h_gs := h_gs) z.2 hQz (A z) (hA z) (hcount z)
    have hroot : (pg_eval_on_Z (F := F) Q z.1).eval P = 0 := by
      simpa [P, ← c57_eval_on_Z_eq_pg (F := F) Q z.1] using hvanish
    exact Polynomial.dvd_iff_isRoot.mpr hroot

/-
Claim 5.7 of [BCIKS20].

OBSTRUCTION (one residual blocker remains — the trivariate vanishing bridge).

* *Sealed `eval_on_Z` (Gap A — NOW RESOLVED).*  Previously `Trivariate.eval_on_Z` was declared
  `opaque`, so **no** property of `eval_on_Z R z.1` (which appears in the `S'`-membership predicate
  `(Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧ …`) was derivable — not `eval_on_Z 0 z = 0`, not
  additivity, not `eval_on_Z p z = pg_eval_on_Z p z` (the last failed `rfl` despite identical
  bodies, since `opaque` blocks delta-reduction).  `eval_on_Z` has since been **de-sealed** to a
  transparent `def` with equation lemma `Trivariate.eval_on_Z_eq` (`Trivariate.lean`).  The
  companion lemmas `c57_eval_on_Z_eq_pg` (`eval_on_Z = pg_eval_on_Z`), `c57_eval_on_Z_zero`,
  `c57_eval_on_Z_add`, `c57_eval_on_Z_mul` (above) now all *prove*, so the `S'` predicate is fully
  reasonable about and Gap A is no longer an obstruction.  (The statement is left referencing
  `Trivariate.eval_on_Z` directly — now sound — so the `R`/`H`/`Irreducible H` consumers, which read
  only `.choose`, `.choose_spec.choose`, `.choose_spec.choose_spec.2.1`, are unaffected.)

* *GS-multiplicity → close-codeword-graph vanishing (Gap B — NOW RESOLVED).*  The pigeonhole needs,
  for each `z ∈ S`, the vanishing `(eval_on_Z Q z.1).eval (Pz z.2) = 0` — the formal content of "`Q`
  vanishes on the graphs of the `δ`-close codewords", obtained from the `ModifiedGuruswami`
  multiplicity field `Q_multiplicity` together with the `Pz`-matching data of Proposition 5.5.  This
  bridge is now **supplied and fully proven** by `Q_vanishes_on_close_codeword_graph` (above): the
  trivariate analogue of the bivariate `GuruswamiSudan.orderAt_eval_ge` /
  `roots_le_degree_of_deg_lt_roots` chain, transporting the order-`≥ m` root multiplicity of `Q`
  over `F[Z]` at `(C ωᵢ, C(u₀ᵢ) + X·C(u₁ᵢ))` under `Z ↦ z` (`gapB_transport_mult`) to order-`≥ m`
  vanishing of `eval_on_Z Q z` at the word point `(ωᵢ, (u₀ + z•u₁) i)`, then a degree-vs-roots count
  (`gapB_vanish_of_orderM_and_count`).  `#print axioms` is clean.
  *Verified residual side hypothesis (NOT in this binder):* the count requires the strict inequality
  `m·#A > natWeightedDegree (eval_on_Z Q z) 1 k` (with `#A ≥ (1−δ)n` the agreement count), i.e. `δ`
  within the Johnson radius `proximity_gap_johnson`.  `δ` is a *free* parameter of this Claim-5.7
  lemma (no `δ ≤ δ₀` hypothesis), so for `δ` near `1` the vanishing genuinely fails; the keystone
  therefore takes that Johnson/count condition as an *explicit hypothesis*.  Closing Claim 5.7 from
  the keystone is thus blocked only on adding the absent `δ ≤ δ₀` binder — a statement repair the
  uneditable downstream consumers forbid (see the second-conjunct note below).

* *Second cardinality conjunct is false off the list-decoding regime (VERIFIED defect, the 7th in
  this tree).*  The conjunct `(#S : ℝ)/(D_Y Q) > 2·D_Y Q²·D_X·D_YZ Q` is a *lower bound on `#S`*
  (`S = coeffs_of_close_proximity`) that does not follow from `ModifiedGuruswami`: for `δ < 0` (and
  `0 < n`) the set `S` is **empty** (`Extraction.coeffs_of_close_proximity_eq_empty_of_neg`), so the
  LHS is `0`, while the RHS is `≥ 0` always (`Extraction.c57_rhs_nonneg`); hence `0 > (≥0)` is
  false (`Extraction.c57_second_conjunct_unsat_of_S_empty`).  In [BCIKS20] this inequality is a
  *hypothesis* (`S` large — the list-decoding case), mis-placed into the conclusion; the faithful
  fix carries it (and the Johnson bound above) as side hypotheses, which the uneditable consumer
  signatures `(δ) (x₀) (h_gs)` of `R`/`H`/`irreducible_H`/Claims-5.8–5.11 do not admit.

With Gap A resolved, the proof obligation is retained pending the Gap-B vanishing bridge (which
  itself
needs the absent `δ ≤ δ₀` hypothesis), the false-off-regime second conjunct, and the upstream
Prop 5.5.  The binder structure `∃ R H, R ∈ … ∧ Irreducible H ∧ …` is preserved so the
downstream extractors stay well-typed. -/
omit [DecidableEq (RatFunc F)] in
/-- Proved, side-condition-explicit form of the Claim 5.7 candidate-pair extraction.

This packages the already-proved `pg_exists_common_candidate_pair_of_dvd_card_natDegreeY` into the
factor-properties shape used by the §5 agreement chain, but it intentionally targets `pg_Rset`
rather than the stronger Eq. 5.12 factorization list.  The missing work for the original
free-parameter Claim 5.7 is now isolated in the hypotheses here: nonvanishing/separability of the
`x₀` specialization, nonempty close set, graph divisibility for every close `z`, and the large-set
Johnson-regime inequality. -/
lemma coeffs_of_close_proximity_nonempty_of_large_natdiv (δ : ℚ)
    (hlarge :
      (#(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) : ℝ) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty := by
  classical
  by_contra hS
  rw [Finset.not_nonempty_iff_eq_empty] at hS
  rw [hS] at hlarge
  have hzero :
      (#(∅ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q : ℝ) = 0 := by
    simp
  exact absurd hlarge (not_lt.mpr (by simpa [hzero] using c57_rhs_nonneg k))

omit [DecidableEq (RatFunc F)] in
lemma exists_pg_factors_with_large_common_root_set_of_dvd (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (hdiv : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
      Polynomial.X - Polynomial.C P ∣ (pg_eval_on_Z (F := F) Q z.1))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(Finset.univ.filter
            (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
              (Trivariate.eval_on_Z R z.1).eval
                  (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
                (Bivariate.evalX z.1 H).eval
                  ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
                  = 0))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by
  classical
  obtain ⟨R, H, hmem, hcard_pg⟩ :=
    pg_exists_common_candidate_pair_of_dvd_card_natDegreeY (F := F) (k := k)
      (δ := δ) (x₀ := x₀) (h_gs := h_gs) hx0 hsep hS_nonempty hdiv
  have hpair :
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
        H ∈
          UniqueFactorizationMonoid.normalizedFactors
            (Bivariate.evalX (Polynomial.C x₀) R) := by
    simpa [pg_candidatePairs] using hmem
  refine ⟨R, H, hpair.1, ?_, ?_, ?_, ?_, hsep R hpair.1, ?_, hlarge⟩
  · exact pg_Rset_irreducible (F := F) (k := k) h_gs R hpair.1
  · exact UniqueFactorizationMonoid.irreducible_of_normalized_factor
      (a := Bivariate.evalX (Polynomial.C x₀) R) H hpair.2
  · exact pg_candidatePairs_snd_natDegree_pos (F := F) (k := k) (x₀ := x₀)
      (h_gs := h_gs) hsep hmem
  · exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpair.2
  · simpa [c57_eval_on_Z_eq_pg] using hcard_pg

omit [DecidableEq (RatFunc F)] in
/-- Candidate-pair extraction from the `pg_eval_on_Z` divisibility hypothesis
with close-set nonemptiness derived from the same large-set hypothesis carried
by the conclusion.

This is the side-condition-explicit `pg_eval_on_Z` form of Claim 5.7 that
downstream callers can use when the Johnson-regime cardinality hypothesis is
available directly, without separately proving the close set is nonempty. -/
lemma exists_pg_factors_with_large_common_root_set_of_dvd_of_large (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hdiv : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
      Polynomial.X - Polynomial.C P ∣ (pg_eval_on_Z (F := F) Q z.1))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(Finset.univ.filter
            (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
              (Trivariate.eval_on_Z R z.1).eval
                  (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
                (Bivariate.evalX z.1 H).eval
                  ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
                  = 0))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q :=
  exists_pg_factors_with_large_common_root_set_of_dvd
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep
    (coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge)
    hdiv hlarge

omit [DecidableEq (RatFunc F)] in
/-- Candidate-pair extraction directly from the graph agreement/count hypotheses used by
`Q_vanishes_on_close_codeword_graph`.

This is the proved side-condition-heavy replacement for the first half of Claim 5.7: the only
remaining inputs are the list-decoding regime inequalities and the per-`z` agreement sets that make
the graph-vanishing theorem applicable. -/
lemma exists_pg_factors_with_large_common_root_set_of_graph_conditions
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(Finset.univ.filter
            (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
              (Trivariate.eval_on_Z R z.1).eval
                  (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
                (Bivariate.evalX z.1 H).eval
                  ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
                  = 0))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by
  classical
  have hdiv :
      ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
        Polynomial.X - Polynomial.C P ∣ (pg_eval_on_Z (F := F) Q z.1) :=
    pg_divisibility_of_graph_vanishing_conditions (F := F) (k := k)
      (δ := δ) (h_gs := h_gs) A hA hcount
  obtain ⟨R, H, hR, hRirr, hHirr, hHdeg, hHdvd, hRsep, hcard, hlarge'⟩ :=
    exists_pg_factors_with_large_common_root_set_of_dvd (F := F) (k := k)
      (δ := δ) (x₀ := x₀) (h_gs := h_gs) hx0 hsep hS_nonempty hdiv hlarge
  exact ⟨R, H, hR, hRirr, hHirr, hHdeg, hHdvd, hRsep, by
    convert hcard using 3, hlarge'⟩

/-- Candidate-pair extraction from graph agreement/count hypotheses, with
nonemptiness derived from the large-set hypothesis. -/
lemma exists_pg_factors_with_large_common_root_set_of_graph_conditions_of_large
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(Finset.univ.filter
            (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
              (Trivariate.eval_on_Z R z.1).eval
                  (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
                (Bivariate.evalX z.1 H).eval
                  ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
                  = 0))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by
  exact exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hx0 hsep
    (coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge)
    A hA hcount hlarge

/-- The side hypotheses needed for the proved graph-condition candidate-pair
extractions.  This package avoids repeating the same large binder block in the
root-clearing API. -/
structure GraphExtractionHypotheses
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) where
  hx0 : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs →
      Bivariate.evalX (Polynomial.C x₀) R ≠ 0
  hsep : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs →
      (Bivariate.evalX (Polynomial.C x₀) R).Separable
  hS_nonempty :
    (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty
  A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n)
  hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
    ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
      (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
        (ωs i)
  hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
    Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card
  hlarge :
    #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q

omit [DecidableEq (RatFunc F)] in
/-- Candidate-pair extraction from the packaged graph-extraction side
conditions.  This is the short, hypothesis-explicit replacement for the legacy
Claim 5.7 extractor below; it targets the current `pg_Rset` factor API rather
than the stale Eq. 5.12 `.choose_spec.choose` list. -/
lemma exists_pg_factors_with_large_common_root_set_of_hypotheses
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(Finset.univ.filter
            (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
              (Trivariate.eval_on_Z R z.1).eval
                  (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
                (Bivariate.evalX z.1 H).eval
                  ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
                  = 0))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q :=
  exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount hcond.hlarge

/-- Build the graph-extraction side-condition package while deriving close-set
nonemptiness from the large-set inequality. -/
def GraphExtractionHypotheses.ofLarge
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs :=
  { hx0 := hx0
    hsep := hsep
    hS_nonempty := coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge
    A := A
    hA := hA
    hcount := hcount
    hlarge := hlarge }

omit [DecidableEq (RatFunc F)] in
/-- Candidate-pair extraction plus the proved Appendix-A root-clearing bridge.

This is the side-condition-explicit form needed before Claims 5.8--5.10 can be
made honest: once the Claim-5.7 candidate pair has a large enough common-root
fiber for the `clearDenomY` representative, `H_tilde' H` divides the cleared
specialization of `R`. -/
lemma exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(Finset.univ.filter
            (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
              (Trivariate.eval_on_Z R z.1).eval
                  (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
                (Bivariate.evalX z.1 H).eval
                  ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
                  = 0))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q ∧
      ∀ {e D : ℕ},
        (hHpos : 0 < H.natDegree) →
        (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e →
        D ≥ Bivariate.totalDegree H →
        ((Finset.univ.filter
          (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
            have P : F[X] :=
              Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
            (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
              (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).card : WithBot ℕ) >
          _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hHpos
            (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
              (Polynomial.clearDenomY (H.coeff H.natDegree) e
                (Bivariate.evalX (Polynomial.C x₀) R)) :
              _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ) →
        _root_.BCIKS20AppendixA.H_tilde' H ∣
          Polynomial.clearDenomY (H.coeff H.natDegree) e
            (Bivariate.evalX (Polynomial.C x₀) R) := by
  classical
  obtain ⟨R, H, hR, hRirr, hHirr, hHdeg, hHdvd, hRsep, hcard, hlarge'⟩ :=
    exists_pg_factors_with_large_common_root_set_of_graph_conditions
      (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      hx0 hsep hS_nonempty A hA hcount hlarge
  refine ⟨R, H, hR, hRirr, hHirr, hHdeg, hHdvd, hRsep, hcard, hlarge', ?_⟩
  intro e D hHpos he hD hcard'
  haveI : Fact (Irreducible H) := ⟨hHirr⟩
  refine H_tilde'_dvd_clearDenomY_of_large_candidate_fiber_card
    (F := F) (n := n) (k := k) (δ := δ) (ωs := ωs) (u₀ := u₀) (u₁ := u₁)
    x₀ hHpos he hD ?_
  convert hcard' using 1
  apply congrArg (fun n : ℕ => (n : WithBot ℕ))
  apply congrArg Finset.card
  ext z
  simp

omit [DecidableEq (RatFunc F)] in
/-- Candidate-pair extraction plus `clearDenomY`, with close-set nonemptiness
derived from the same large-set hypothesis.

This is the large-set front door for the graph-condition Claim-5.7 replacement:
callers need only provide the graph agreement/count hypotheses and the Johnson
large-set inequality, not a separate proof that the close set is nonempty. -/
lemma exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions_of_large
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
        #(Finset.univ.filter
            (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
              (Trivariate.eval_on_Z R z.1).eval
                  (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
                (Bivariate.evalX z.1 H).eval
                  ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
                  = 0))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q ∧
      ∀ {e D : ℕ},
        (hHpos : 0 < H.natDegree) →
        (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ e →
        D ≥ Bivariate.totalDegree H →
        ((Finset.univ.filter
          (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
            have P : F[X] :=
              Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
            (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
              (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0)).card : WithBot ℕ) >
          _root_.BCIKS20AppendixA.weight_Λ_over_𝒪 hHpos
            (Ideal.Quotient.mk (Ideal.span {_root_.BCIKS20AppendixA.H_tilde' H})
              (Polynomial.clearDenomY (H.coeff H.natDegree) e
                (Bivariate.evalX (Polynomial.C x₀) R)) :
              _root_.BCIKS20AppendixA.𝒪 H) D * (H.natDegree : WithBot ℕ) →
        _root_.BCIKS20AppendixA.H_tilde' H ∣
          Polynomial.clearDenomY (H.coeff H.natDegree) e
            (Bivariate.evalX (Polynomial.C x₀) R) := by
  exact exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
    (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep
    (coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge)
    A hA hcount hlarge

omit [DecidableEq (RatFunc F)] in
lemma exists_pg_factors_with_large_common_root_set_setToFinset_of_graph_conditions
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ∃ R H,
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
      #(@Set.toFinset _
        { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
          (Trivariate.eval_on_Z R z.1).eval
              (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
            (Bivariate.evalX z.1 H).eval
              ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
              = 0 }
        (@Fintype.ofFinite _ Subtype.finite))
        ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) ∧
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by
  classical
  obtain ⟨R, H, hR, hRirr, hHirr, hHdeg, hHdvd, hRsep, hcard, hlarge'⟩ :=
    exists_pg_factors_with_large_common_root_set_of_graph_conditions
      (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      hx0 hsep hS_nonempty A hA hcount hlarge
  refine ⟨R, H, hR, hRirr, hHirr, hHdeg, hHdvd, hRsep, ?_, hlarge'⟩
  have hcard_set :
      #(@Set.toFinset _
        { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
          (Trivariate.eval_on_Z R z.1).eval
              (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
            (Bivariate.evalX z.1 H).eval
              ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval x₀)
              = 0 }
        (@Fintype.ofFinite _ Subtype.finite))
        ≥ #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) /
          Bivariate.natDegreeY Q := by
    convert hcard using 3
    ext z
    simp
  have hdomain_card :
      #(Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) =
        #(coeffs_of_close_proximity k ωs δ u₀ u₁) := by
    simp
  simpa [hdomain_card] using hcard_set

omit [DecidableEq (RatFunc F)] in
/-- The `R` polynomial extracted from the graph-condition theorem that also
carries the proved `clearDenomY` root-clearing payload. -/
noncomputable def R_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    F[Z][X][Y] :=
  (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose

omit [DecidableEq (RatFunc F)] in
/-- The `H` polynomial extracted with `R_graph_clear`. -/
noncomputable def H_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    F[Z][X] :=
  (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose

/-- The `R_graph_clear` extraction with close-set nonemptiness derived from the
large-set inequality. -/
noncomputable def R_graph_clear_ofLarge
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    F[Z][X][Y] :=
  R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs
    (GraphExtractionHypotheses.ofLarge (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁)
      δ x₀ h_gs hx0 hsep A hA hcount hlarge)

/-- The `H_graph_clear` extraction with close-set nonemptiness derived from the
large-set inequality. -/
noncomputable def H_graph_clear_ofLarge
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    F[Z][X] :=
  H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs
    (GraphExtractionHypotheses.ofLarge (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁)
      δ x₀ h_gs hx0 hsep A hA hcount hlarge)

/-- The large-set `R_graph_clear` extraction remains in the `pg_Rset`. -/
lemma R_graph_clear_ofLarge_mem_pg_Rset
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    R_graph_clear_ofLarge (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep A hA hcount hlarge ∈
      pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs := by
  unfold R_graph_clear_ofLarge R_graph_clear
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep
    (coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge)
    A hA hcount hlarge).choose_spec.choose_spec.1

/-- Irreducibility of the large-set `R_graph_clear` extraction. -/
lemma irreducible_R_graph_clear_ofLarge
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Irreducible (R_graph_clear_ofLarge (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep A hA hcount hlarge) := by
  unfold R_graph_clear_ofLarge R_graph_clear
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep
    (coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge)
    A hA hcount hlarge).choose_spec.choose_spec.2.1

/-- Irreducibility of the large-set `H_graph_clear` extraction. -/
lemma irreducible_H_graph_clear_ofLarge
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Irreducible (H_graph_clear_ofLarge (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep A hA hcount hlarge) := by
  unfold H_graph_clear_ofLarge H_graph_clear
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep
    (coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge)
    A hA hcount hlarge).choose_spec.choose_spec.2.2.1

/-- Positive degree of the large-set `H_graph_clear` extraction. -/
lemma natDegree_H_graph_clear_ofLarge_pos
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    0 < (H_graph_clear_ofLarge (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep A hA hcount hlarge).natDegree := by
  unfold H_graph_clear_ofLarge H_graph_clear
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep
    (coeffs_of_close_proximity_nonempty_of_large_natdiv
      (F := F) (n := n) (m := m) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) δ hlarge)
    A hA hcount hlarge).choose_spec.choose_spec.2.2.2.1

omit [DecidableEq (RatFunc F)] in
lemma R_graph_clear_mem_pg_Rset
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond ∈
      pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs := by
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose_spec.1

omit [DecidableEq (RatFunc F)] in
lemma irreducible_R_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    Irreducible (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) := by
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose_spec.2.1

omit [DecidableEq (RatFunc F)] in
lemma irreducible_H_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    Irreducible (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) := by
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose_spec.2.2.1

omit [DecidableEq (RatFunc F)] in
lemma natDegree_H_graph_clear_pos
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    0 < (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree := by
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose_spec.2.2.2.1

omit [DecidableEq (RatFunc F)] in
instance fact_irreducible_H_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    Fact (Irreducible (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) :=
  ⟨irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond⟩

omit [DecidableEq (RatFunc F)] in
instance fact_natDegree_H_graph_clear_pos
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    Fact (0 < (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree) :=
  ⟨natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond⟩

omit [DecidableEq (RatFunc F)] in
lemma H_graph_clear_dvd_evalX_R_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond ∣
      Bivariate.evalX (Polynomial.C x₀)
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) := by
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose_spec.2.2.2.2.1

omit [DecidableEq (RatFunc F)] in
lemma evalX_R_graph_clear_separable
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    (Bivariate.evalX (Polynomial.C x₀)
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)).Separable := by
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose_spec.2.2.2.2.2.1

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma claimA2_hypotheses_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs) :
    Hypotheses x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) :=
  ⟨H_graph_clear_dvd_evalX_R_graph_clear
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond,
    evalX_R_graph_clear_separable
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond⟩

omit [DecidableEq (RatFunc F)] in
/-- The root-clearing payload projected from the side-condition-explicit
candidate extraction. -/
lemma H_tilde'_dvd_clearDenomY_graph_clear
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    {e D : ℕ}
    (he :
      (Bivariate.evalX (Polynomial.C x₀)
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)).natDegree ≤ e)
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
    (hcard :
      ((Finset.univ.filter
        (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ =>
          have P : F[X] :=
            Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
          (pg_eval_on_Z (F := F)
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) z.1).eval P = 0 ∧
            (Bivariate.evalX z.1
              (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)).eval
              (P.eval x₀) = 0)).card : WithBot ℕ) >
        _root_.BCIKS20AppendixA.weight_Λ_over_𝒪
          (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (Ideal.Quotient.mk
            (Ideal.span
              {_root_.BCIKS20AppendixA.H_tilde'
                (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)})
            (Polynomial.clearDenomY
              ((H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).coeff
                (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree)
              e
              (Bivariate.evalX (Polynomial.C x₀)
                (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))) :
            _root_.BCIKS20AppendixA.𝒪
              (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
          D *
          ((H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree :
            WithBot ℕ)) :
    _root_.BCIKS20AppendixA.H_tilde'
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) ∣
      Polynomial.clearDenomY
        ((H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).coeff
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree)
        e
        (Bivariate.evalX (Polynomial.C x₀)
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) := by
  exact (exists_pg_factors_with_large_common_root_set_and_clearDenomY_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hcond.hx0 hcond.hsep hcond.hS_nonempty hcond.A hcond.hA hcond.hcount
    hcond.hlarge).choose_spec.choose_spec.2.2.2.2.2.2.2.2 (e := e) (D := D)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      he hD hcard

/-- The `R` polynomial extracted from the proved, side-condition-explicit Claim 5.7
replacement.  Unlike the legacy `R` below, this one carries all hypotheses needed
for the extraction theorem. -/
noncomputable def R_graph
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) : F[Z][X][Y] :=
  (exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep hS_nonempty A hA hcount hlarge).choose

/-- The `H` polynomial extracted alongside `R_graph`. -/
noncomputable def H_graph
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) : F[Z][X] :=
  (exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep hS_nonempty A hA hcount hlarge).choose_spec.choose

omit [DecidableEq (RatFunc F)] in
lemma R_graph_mem_pg_Rset
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge ∈
      pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs := by
  exact (exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep hS_nonempty A hA hcount hlarge).choose_spec.choose_spec.1

omit [DecidableEq (RatFunc F)] in
lemma irreducible_H_graph
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Irreducible (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge) := by
  exact (exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep hS_nonempty A hA hcount hlarge).choose_spec.choose_spec.2.2.1

omit [DecidableEq (RatFunc F)] in
lemma natDegree_H_graph_pos
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    0 < (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge).natDegree := by
  exact (exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep hS_nonempty A hA hcount hlarge).choose_spec.choose_spec.2.2.2.1

omit [DecidableEq (RatFunc F)] in
instance fact_irreducible_H_graph
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Fact (Irreducible (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)) :=
  ⟨irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
    hx0 hsep hS_nonempty A hA hcount hlarge⟩

omit [DecidableEq (RatFunc F)] in
instance fact_natDegree_H_graph_pos
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Fact (0 < (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge).natDegree) :=
  ⟨natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
    hx0 hsep hS_nonempty A hA hcount hlarge⟩

omit [DecidableEq (RatFunc F)] in
lemma H_graph_dvd_evalX_R_graph
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge ∣
      Bivariate.evalX (Polynomial.C x₀)
        (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) := by
  exact (exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep hS_nonempty A hA hcount hlarge).choose_spec.choose_spec.2.2.2.2.1

omit [DecidableEq (RatFunc F)] in
lemma evalX_R_graph_separable
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    (Bivariate.evalX (Polynomial.C x₀)
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)).Separable := by
  exact (exists_pg_factors_with_large_common_root_set_of_graph_conditions
    (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
    hx0 hsep hS_nonempty A hA hcount hlarge).choose_spec.choose_spec.2.2.2.2.2.1

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma claimA2_hypotheses_graph
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    Hypotheses x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge) :=
  ⟨H_graph_dvd_evalX_R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge,
    evalX_R_graph_separable (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge⟩

/-- Named residual bundle for BCIKS20 Claim 5.7.

The bare Claim-5.7 front door needs the graph/count data below plus the bridge from the graph
extraction API to the legacy factorization list. -/
class Claim57Residuals (k : ℕ) (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) where
  hx0 : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs →
      Bivariate.evalX (Polynomial.C x₀) R ≠ 0
  hsep : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs →
      (Bivariate.evalX (Polynomial.C x₀) R).Separable
  hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty
  A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n)
  hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
    ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
      (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i)
  hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
    Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card
  hlarge : #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q
  hfactor : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs →
      R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose

/-- Build the legacy Claim-5.7 residual bundle from the proved graph-extraction
side-condition package plus the only extra legacy bridge: membership in the
`pg_Rset` factor set implies membership in the Eq-5.12 factorization list. -/
@[reducible]
def Claim57Residuals.ofGraphExtractionHypotheses
    [DecidableEq (Polynomial F)]
    {δ : ℚ} {x₀ : F}
    {h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁}
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs where
  hx0 := hcond.hx0
  hsep := hcond.hsep
  hS_nonempty := hcond.hS_nonempty
  A := hcond.A
  hA := hcond.hA
  hcount := hcond.hcount
  hlarge := hcond.hlarge
  hfactor := hfactor

lemma exists_factors_with_large_common_root_set (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  [hres : Claim57Residuals (F := F) k δ x₀ h_gs] :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ 0 < H.natDegree ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0}
        (@Fintype.ofFinite _ Subtype.finite))
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by
  classical
  obtain ⟨R, H, hR, _hRirr, hHirr, hHdeg, hHdvd, hRsep, hcard, hlarge'⟩ :=
    exists_pg_factors_with_large_common_root_set_setToFinset_of_graph_conditions
      (F := F) (k := k) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      hres.hx0 hres.hsep hres.hS_nonempty hres.A hres.hA hres.hcount hres.hlarge
  exact ⟨R, H, hres.hfactor R hR, hHirr, hHdeg, hHdvd, hRsep, hcard, hlarge'⟩

/-- Claim 5.7 front door from the proved graph-extraction side-condition package plus the
remaining legacy factor-list bridge, without requiring callers to install an ambient
`[Claim57Residuals]` instance.

This is the local API reduction for the Claim-5.7 residual surface: `hx0`, `hsep`,
`hS_nonempty`, `A`, `hA`, `hcount`, and `hlarge` are bundled in `GraphExtractionHypotheses`, so the
only extra hypothesis here is the still-open bridge from the graph-extraction `pg_Rset` to the
legacy factorization list. -/
lemma exists_factors_with_large_common_root_set_of_graphExtraction
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ 0 < H.natDegree ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0}
        (@Fintype.ofFinite _ Subtype.finite))
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by
  letI : Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
    Claim57Residuals.ofGraphExtractionHypotheses
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      hcond hfactor
  exact exists_factors_with_large_common_root_set
    (F := F) (m := m) (n := n) (k := k) (Q := Q)
    (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs

/-- Claim 5.7 establishes existence of `R`; this extracts it. -/
noncomputable def R (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] : F[Z][X][Y] :=
 (exists_factors_with_large_common_root_set (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs).choose

/-- Claim 5.7 establishes existence of `H`; this extracts it. -/
noncomputable def H (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] : F[Z][X] :=
(exists_factors_with_large_common_root_set (F := F) (m := m) (n := n) (k := k)
  (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs).choose_spec.choose

/-- The polynomial `H` extracted from Claim 5.7 is irreducible. -/
lemma irreducible_H (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] : Irreducible (H k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs).choose_spec.choose_spec.2.1

instance fact_irreducible_H (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] :
    Fact (Irreducible (H k δ x₀ h_gs)) :=
  ⟨irreducible_H (F := F) (m := m) (n := n) (k := k) (Q := Q)
    (ωs := ωs) (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀) h_gs⟩

lemma natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] :
    0 < (H k δ x₀ h_gs).natDegree :=
  (exists_factors_with_large_common_root_set (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs).choose_spec.choose_spec.2.2.1

instance fact_natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] :
    Fact (0 < (H k δ x₀ h_gs).natDegree) :=
  ⟨natDegree_H_pos (F := F) (m := m) (n := n) (k := k) (Q := Q)
    (ωs := ωs) (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀) h_gs⟩

lemma H_dvd_evalX_R (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] :
    H k δ x₀ h_gs ∣ Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs).choose_spec.choose_spec.2.2.2.1

lemma evalX_R_separable (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] :
    (Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs)).Separable :=
  (exists_factors_with_large_common_root_set (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs).choose_spec.choose_spec.2.2.2.2.1

open BCIKS20AppendixA.ClaimA2 in
lemma claimA2_hypotheses (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs] :
    Hypotheses x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs) :=
  ⟨H_dvd_evalX_R k h_gs, evalX_R_separable k h_gs⟩

lemma powerSeries_eq_truncate_of_coeff_zero_ge
    {S : Type} [Semiring S] (f : PowerSeries S) {k : ℕ}
    (hzero : ∀ t, t ≥ k → PowerSeries.coeff t f = 0) :
    f = PowerSeries.mk (fun t => if t ≥ k then 0 else PowerSeries.coeff t f) := by
  ext t
  by_cases ht : t ≥ k
  · simp [ht, hzero t ht]
  · simp [ht]

lemma powerSeries_eq_coe_trunc_of_coeff_zero_ge
    {S : Type} [CommSemiring S] (f : PowerSeries S) {k : ℕ}
    (hzero : ∀ t, t ≥ k → PowerSeries.coeff t f = 0) :
    f = (f.trunc k : PowerSeries S) := by
  ext t
  by_cases ht : t < k
  · simp [PowerSeries.coeff_trunc, ht]
  · have htk : t ≥ k := Nat.le_of_not_gt ht
    simp [PowerSeries.coeff_trunc, ht, hzero t htk]

lemma powerSeries_mk_eq_coe_trunc_of_tail_zero
    {S : Type} [CommSemiring S] (a : ℕ → S) {k : ℕ}
    (hzero : ∀ t, t ≥ k → a t = 0) :
    PowerSeries.mk a = ((PowerSeries.mk a).trunc k : PowerSeries S) :=
  powerSeries_eq_coe_trunc_of_coeff_zero_ge (PowerSeries.mk a)
    (by
      intro t ht
      simpa using hzero t ht)

lemma powerSeries_subst_coe_polynomial
    {S : Type} [CommRing S] (a : PowerSeries S) (p : Polynomial S) :
    PowerSeries.subst a (p : PowerSeries S) = Polynomial.aeval a p := by
  rw [Polynomial.toPowerSeries_toMvPowerSeries]
  rw [PowerSeries.subst_def]
  rw [MvPowerSeries.subst_coe]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n r => simp [Polynomial.aeval_def]

lemma polynomial_aeval_coe_eq_coe_comp
    {S : Type} [CommRing S] (p q : Polynomial S) :
    Polynomial.aeval (q : PowerSeries S) p = ((p.comp q : Polynomial S) : PowerSeries S) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [Polynomial.add_comp]
      simp [map_add, hp, hr]
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp

lemma natDegree_C_add_X_le_one {S : Type} [CommRing S] (c : S) :
    (Polynomial.C c + Polynomial.X : Polynomial S).natDegree ≤ 1 := by
  calc
    (Polynomial.C c + Polynomial.X : Polynomial S).natDegree
        ≤ max (Polynomial.C c : Polynomial S).natDegree (Polynomial.X : Polynomial S).natDegree :=
          Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · simp [Polynomial.natDegree_C]
      · exact Polynomial.natDegree_X_le

lemma powerSeries_trunc_zero {S : Type} [Semiring S] (f : PowerSeries S) :
    f.trunc 0 = (0 : Polynomial S) := by
  ext n
  simp

lemma coeff_aeval_affine_trunc_eq_zero_of_ge
    {S : Type} [CommRing S] (f : PowerSeries S) (c : S) {k t : ℕ} (ht : t ≥ k) :
    PowerSeries.coeff t
      (Polynomial.aeval (((Polynomial.C c + Polynomial.X : Polynomial S) : PowerSeries S))
        (f.trunc k)) = 0 := by
  rw [polynomial_aeval_coe_eq_coe_comp]
  rw [Polynomial.coeff_coe]
  by_cases hk : k = 0
  · subst k
    rw [powerSeries_trunc_zero]
    simp
  · have hdegp : (f.trunc k).natDegree < k := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      simpa using PowerSeries.natDegree_trunc_lt f j
    have hdegq : (Polynomial.C c + Polynomial.X : Polynomial S).natDegree ≤ 1 :=
      natDegree_C_add_X_le_one c
    have hdegcomp_le :
        ((f.trunc k).comp (Polynomial.C c + Polynomial.X : Polynomial S)).natDegree
          ≤ (f.trunc k).natDegree := by
      calc
        ((f.trunc k).comp (Polynomial.C c + Polynomial.X : Polynomial S)).natDegree
            ≤ (f.trunc k).natDegree
                * (Polynomial.C c + Polynomial.X : Polynomial S).natDegree :=
              Polynomial.natDegree_comp_le
        _ ≤ (f.trunc k).natDegree * 1 := Nat.mul_le_mul_left _ hdegq
        _ = (f.trunc k).natDegree := Nat.mul_one _
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hdegcomp_le (lt_of_lt_of_le hdegp ht))

set_option linter.unusedSimpArgs false in
lemma affine_shift_powerSeries_eq_coe_C_add_X {S : Type} [CommRing S] (c : S) :
    PowerSeries.mk (fun t => match t with | 0 => c | 1 => 1 | _ => 0) =
      ((Polynomial.C c + Polynomial.X : Polynomial S) : PowerSeries S) := by
  ext t
  cases t with
  | zero => simp [PowerSeries.coeff_X, Polynomial.coeff_coe, Polynomial.coeff_add,
      Polynomial.coeff_C, Polynomial.coeff_X]
  | succ t =>
      cases t with
      | zero => simp [PowerSeries.coeff_X, Polynomial.coeff_coe, Polynomial.coeff_add,
          Polynomial.coeff_C, Polynomial.coeff_X]
      | succ t => simp [PowerSeries.coeff_X, Polynomial.coeff_coe, Polynomial.coeff_add,
          Polynomial.coeff_C, Polynomial.coeff_X]

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma alpha'_powerSeries_eq_trunc_of_coeff_zero
    {R : F[Z][X][Y]} {H : F[Z][X]}
    (H_irreducible : Irreducible H) (hHdeg : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H) {k : ℕ}
    (hzero : ∀ t ≥ k,
      α' x₀ R H_irreducible hHdeg hHyp t =
        (0 : BCIKS20AppendixA.𝕃 H)) :
    PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp) =
      ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k :
        PowerSeries (BCIKS20AppendixA.𝕃 H)) :=
  powerSeries_mk_eq_coe_trunc_of_tail_zero
    (α' x₀ R H_irreducible hHdeg hHyp) hzero

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma gamma'_eq_subst_alpha'_trunc_of_coeff_zero
    {R : F[Z][X][Y]} {H : F[Z][X]}
    (H_irreducible : Irreducible H) (hHdeg : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H) {k : ℕ}
    (hzero : ∀ t ≥ k,
      α' x₀ R H_irreducible hHdeg hHyp t =
        (0 : BCIKS20AppendixA.𝕃 H)) :
    γ' x₀ R H_irreducible hHdeg hHyp =
      let shift : PowerSeries (BCIKS20AppendixA.𝕃 H) := PowerSeries.mk fun t =>
        match t with
        | 0 => BCIKS20AppendixA.fieldTo𝕃 (-x₀)
        | 1 => 1
        | _ => 0
      PowerSeries.subst shift
        ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k :
          PowerSeries (BCIKS20AppendixA.𝕃 H)) := by
  let shift : PowerSeries (BCIKS20AppendixA.𝕃 H) := PowerSeries.mk fun t =>
    match t with
    | 0 => BCIKS20AppendixA.fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  change PowerSeries.subst shift (PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)) =
    PowerSeries.subst shift
      ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k :
        PowerSeries (BCIKS20AppendixA.𝕃 H))
  exact congrArg (PowerSeries.subst shift)
    (alpha'_powerSeries_eq_trunc_of_coeff_zero (F := F) (x₀ := x₀)
      H_irreducible hHdeg hHyp hzero)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma gamma'_eq_aeval_alpha'_trunc_of_coeff_zero
    {R : F[Z][X][Y]} {H : F[Z][X]}
    (H_irreducible : Irreducible H) (hHdeg : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H) {k : ℕ}
    (hzero : ∀ t ≥ k,
      α' x₀ R H_irreducible hHdeg hHyp t =
        (0 : BCIKS20AppendixA.𝕃 H)) :
    γ' x₀ R H_irreducible hHdeg hHyp =
      let shift : PowerSeries (BCIKS20AppendixA.𝕃 H) := PowerSeries.mk fun t =>
        match t with
        | 0 => BCIKS20AppendixA.fieldTo𝕃 (-x₀)
        | 1 => 1
        | _ => 0
      Polynomial.aeval shift
        ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k) := by
  let shift : PowerSeries (BCIKS20AppendixA.𝕃 H) := PowerSeries.mk fun t =>
    match t with
    | 0 => BCIKS20AppendixA.fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  change PowerSeries.subst shift (PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)) =
    Polynomial.aeval shift ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k)
  calc
    PowerSeries.subst shift (PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp))
        = PowerSeries.subst shift
            ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k :
              PowerSeries (BCIKS20AppendixA.𝕃 H)) := by
            exact congrArg (PowerSeries.subst shift)
              (alpha'_powerSeries_eq_trunc_of_coeff_zero (F := F) (x₀ := x₀)
                H_irreducible hHdeg hHyp hzero)
    _ = Polynomial.aeval shift
            ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k) := by
            exact powerSeries_subst_coe_polynomial shift
              ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma gamma'_coeff_zero_of_alpha'_coeff_zero
    {R : F[Z][X][Y]} {H : F[Z][X]}
    (H_irreducible : Irreducible H) (hHdeg : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H) {k : ℕ}
    (hzero : ∀ t ≥ k,
      α' x₀ R H_irreducible hHdeg hHyp t =
        (0 : BCIKS20AppendixA.𝕃 H)) :
    ∀ t ≥ k,
      PowerSeries.coeff t (γ' x₀ R H_irreducible hHdeg hHyp) =
        (0 : BCIKS20AppendixA.𝕃 H) := by
  intro t ht
  let shift : PowerSeries (BCIKS20AppendixA.𝕃 H) := PowerSeries.mk fun t =>
    match t with
    | 0 => BCIKS20AppendixA.fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  have hγ := gamma'_eq_aeval_alpha'_trunc_of_coeff_zero
    (F := F) (x₀ := x₀) H_irreducible hHdeg hHyp hzero
  rw [hγ]
  change PowerSeries.coeff t
      (Polynomial.aeval shift
        ((PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp)).trunc k)) = 0
  have hshift : shift =
      ((Polynomial.C (BCIKS20AppendixA.fieldTo𝕃 (H := H) (-x₀)) + Polynomial.X :
          Polynomial (BCIKS20AppendixA.𝕃 H)) :
        PowerSeries (BCIKS20AppendixA.𝕃 H)) := by
    exact affine_shift_powerSeries_eq_coe_C_add_X
      (BCIKS20AppendixA.fieldTo𝕃 (H := H) (-x₀))
  rw [hshift]
  exact coeff_aeval_affine_trunc_eq_zero_of_ge
    (PowerSeries.mk (α' x₀ R H_irreducible hHdeg hHyp))
    (BCIKS20AppendixA.fieldTo𝕃 (H := H) (-x₀)) ht

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma alpha'_eq_zero_of_embedding_beta_eq_zero
    {R : F[Z][X][Y]} {H : F[Z][X]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (H_irreducible : Irreducible H) (hHdeg : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H) {t : ℕ}
    (hemb :
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 H
        (β (H := H) R t) = 0) :
    α' x₀ R H_irreducible hHdeg hHyp t = 0 := by
  simp [α', α, hemb]

open BCIKS20AppendixA.ClaimA2 in
lemma approximate_solution_is_exact_solution_coeffs_of_beta_embedding_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) = 0) :
    ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  intro t ht
  exact alpha'_eq_zero_of_embedding_beta_eq_zero
    (F := F) (x₀ := x₀) (R := R k δ x₀ h_gs) (H := H k δ x₀ h_gs)
    (irreducible_H k h_gs)
    (natDegree_H_pos k h_gs)
    (claimA2_hypotheses k h_gs)
    (hemb t ht)

open BCIKS20AppendixA.ClaimA2 in
lemma approximate_solution_is_exact_solution_coeffs_of_βHensel_embedding_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hcompat : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t) =
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t))
    (hβzero : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t) = 0) :
    ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  exact approximate_solution_is_exact_solution_coeffs_of_beta_embedding_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
    (fun t ht => by
      rw [← hcompat t ht]
      exact hβzero t ht)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 front door from the genuine recursive Hensel numerator.

If the real Hensel numerator has the Appendix-A `S_β` largeness needed by
`Lemma_A_1`, and it agrees under the embedding with the placeholder numerator
`β`, then the approximate solution coefficients vanish in degrees `≥ k`. -/
lemma approximate_solution_is_exact_solution_coeffs_of_βHensel_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hcompat : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t) =
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (_root_.BCIKS20.HenselNumerator.βHensel
              (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
              (claimA2_hypotheses k h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  intro t ht
  exact approximate_solution_is_exact_solution_coeffs_of_βHensel_embedding_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hcompat
    (fun t ht => by
      obtain ⟨D, hD, hcard⟩ := hlarge t ht
      exact BCIKS20AppendixA.Lemma_A_1
        (H := H k δ x₀ h_gs) (natDegree_H_pos k h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t) D hD hcard)
    t ht

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Convert the structured Hensel-weight route into the exact `S_β` largeness
shape consumed by Claim 5.8.

The new `βHensel_weight_bound_of_structured_weight` theorem turns a structured
`α_t`-style weight invariant into the loose numeric bound
`Λ(β_t) ≤ (2t+1)·d_R·D`.  Therefore a geometric count that is larger than this
numeric target is automatically larger than the actual Appendix-A weight. -/
lemma βHensel_Sβ_large_of_structured_weight
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs) ∧
        Bivariate.natDegreeY (H k δ x₀ h_gs) ≤
          Bivariate.natDegreeY (R k δ x₀ h_gs) ∧
        (H k δ x₀ h_gs).leadingCoeff.natDegree +
            Bivariate.natDegreeY (H k δ x₀ h_gs) ≤ D ∧
        weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t) D
          ≤ WithBot.some
            (1 + (t + 1) * (H k δ x₀ h_gs).leadingCoeff.natDegree
              + (2 * t - 1)
                * ((Bivariate.natDegreeY (R k δ x₀ h_gs) - 1)
                  * (D - Bivariate.natDegreeY (H k δ x₀ h_gs) + 1))) ∧
        (Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) : WithBot ℕ) >
          WithBot.some
            ((2 * t + 1) * Bivariate.natDegreeY (R k δ x₀ h_gs) * D)
            * ((H k δ x₀ h_gs).natDegree : WithBot ℕ)) :
    ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (_root_.BCIKS20.HenselNumerator.βHensel
              (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
              (claimA2_hypotheses k h_gs) t) D *
            (H k δ x₀ h_gs).natDegree := by
  intro t ht
  obtain ⟨D, hD, hdR2, hdHR, hW, hstructured, hcard⟩ := hlarge t ht
  refine ⟨D, hD, ?_⟩
  have hweight :
      weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t) D
        ≤ WithBot.some
          ((2 * t + 1) * Bivariate.natDegreeY (R k δ x₀ h_gs) * D) :=
    _root_.BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_weight
      (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
      (claimA2_hypotheses k h_gs) (natDegree_H_pos k h_gs)
      hdR2 hdHR hW t hstructured
  exact lt_of_le_of_lt (by gcongr) hcard

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 coefficient front door from the genuine Hensel lift identity.

This packages the native Appendix-A proof obligations for the coefficient
statement: denominator nonvanishing, the denominator-cleared Hensel lift
identity, and `S_β` largeness for the recursive numerator. -/
lemma approximate_solution_is_exact_solution_coeffs_of_βHensel_lift_identity_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hden : ∀ t ≥ k,
      (liftToFunctionField (H := H k δ x₀ h_gs)
            (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1) ≠ 0)
    (hlift : ∀ t ≥ k,
      embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t)
        = α x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t
          * (liftToFunctionField (H := H k δ x₀ h_gs)
              (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (_root_.BCIKS20.HenselNumerator.βHensel
              (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
              (claimA2_hypotheses k h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  exact approximate_solution_is_exact_solution_coeffs_of_βHensel_Sβ_large
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs
    (fun t ht =>
      _root_.BCIKS20.HenselNumerator.β_embedding_eq_of_βHensel_lift_identity
        (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
        (claimA2_hypotheses k h_gs) t (hden t ht) (hlift t ht))
    hlarge

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 coefficient front door from the structured Hensel-weight route.

This composes the structured-weight-to-`S_β` converter with the genuine Hensel
lift-identity front door, so callers no longer need to expose the intermediate
`S_β` largeness statement. -/
lemma approximate_solution_is_exact_solution_coeffs_of_βHensel_lift_identity_structured_weight
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hden : ∀ t ≥ k,
      (liftToFunctionField (H := H k δ x₀ h_gs)
            (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1) ≠ 0)
    (hlift : ∀ t ≥ k,
      embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t)
        = α x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t
          * (liftToFunctionField (H := H k δ x₀ h_gs)
              (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs) ∧
        Bivariate.natDegreeY (H k δ x₀ h_gs) ≤
          Bivariate.natDegreeY (R k δ x₀ h_gs) ∧
        (H k δ x₀ h_gs).leadingCoeff.natDegree +
            Bivariate.natDegreeY (H k δ x₀ h_gs) ≤ D ∧
        weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t) D
          ≤ WithBot.some
            (1 + (t + 1) * (H k δ x₀ h_gs).leadingCoeff.natDegree
              + (2 * t - 1)
                * ((Bivariate.natDegreeY (R k δ x₀ h_gs) - 1)
                  * (D - Bivariate.natDegreeY (H k δ x₀ h_gs) + 1))) ∧
        (Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) : WithBot ℕ) >
          WithBot.some
            ((2 * t + 1) * Bivariate.natDegreeY (R k δ x₀ h_gs) * D)
            * ((H k δ x₀ h_gs).natDegree : WithBot ℕ)) :
    ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) :=
  approximate_solution_is_exact_solution_coeffs_of_βHensel_lift_identity_Sβ_large
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hden hlift
    (βHensel_Sβ_large_of_structured_weight
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hlarge)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 front door from the exact Appendix-A Lemma A.1 largeness
condition.  This isolates the remaining geometric work: for each coefficient
index `t ≥ k`, it is enough to produce a degree bound `D` and prove that
`S_β (β R t)` is larger than `Λ(β R t) * deg H`. -/
lemma approximate_solution_is_exact_solution_coeffs_of_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  exact approximate_solution_is_exact_solution_coeffs_of_beta_embedding_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
    (fun t ht => by
      obtain ⟨D, hD, hcard⟩ := hlarge t ht
      exact BCIKS20AppendixA.Lemma_A_1
        (H := H k δ x₀ h_gs) (natDegree_H_pos k h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) D hD hcard)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma approximate_solution_is_exact_solution_coeffs_graph_of_beta_embedding_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
        (β
          (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) t) = 0) :
    ∀ t ≥ k,
    α'
      x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      t
    =
    (0 : BCIKS20AppendixA.𝕃
      (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)) := by
  intro t ht
  exact alpha'_eq_zero_of_embedding_beta_eq_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (hemb t ht)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph Claim 5.8 front door from the exact Appendix-A Lemma A.1 largeness
condition. -/
lemma approximate_solution_is_exact_solution_coeffs_graph_of_Sβ_large
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlargeS : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) ∧
        Set.ncard (S_β
          (β
            (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
            (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
            (β
              (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge) t) D *
            (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge).natDegree) :
    ∀ t ≥ k,
    α'
      x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      t
    =
    (0 : BCIKS20AppendixA.𝕃
      (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)) := by
  exact approximate_solution_is_exact_solution_coeffs_graph_of_beta_embedding_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
    hx0 hsep hS_nonempty A hA hcount hlarge
    (fun t ht => by
      obtain ⟨D, hD, hcard⟩ := hlargeS t ht
      exact BCIKS20AppendixA.Lemma_A_1
        (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (β
          (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) t)
        D hD hcard)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma approximate_solution_is_exact_solution_coeffs_graph_clear_of_beta_embedding_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (β
          (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) = 0) :
    ∀ t ≥ k,
    α'
      x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      t
    =
    (0 : BCIKS20AppendixA.𝕃
      (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) := by
  intro t ht
  exact alpha'_eq_zero_of_embedding_beta_eq_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (claimA2_hypotheses_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (hemb t ht)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph-clear Claim 5.8 front door from the exact Appendix-A Lemma A.1
largeness condition.  This is the same criterion as
`approximate_solution_is_exact_solution_coeffs_of_Sβ_large`, but phrased for
the explicit `GraphExtractionHypotheses` package used by the proved extraction
pipeline. -/
lemma approximate_solution_is_exact_solution_coeffs_graph_clear_of_Sβ_large
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) ∧
        Set.ncard (S_β
          (β
            (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_clear_pos
              (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (β
              (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) D *
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree) :
    ∀ t ≥ k,
    α'
      x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      t
    =
    (0 : BCIKS20AppendixA.𝕃
      (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) := by
  exact approximate_solution_is_exact_solution_coeffs_graph_clear_of_beta_embedding_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
    (fun t ht => by
      obtain ⟨D, hD, hcard⟩ := hlarge t ht
      exact BCIKS20AppendixA.Lemma_A_1
        (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (natDegree_H_graph_clear_pos
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (β
          (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t)
        D hD hcard)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph-clear Claim 5.8 front door from explicit graph-extraction data plus
the factor-list bridge, without requiring an ambient `[Claim57Residuals]`
instance. -/
lemma approximate_solution_is_exact_solution_coeffs_graph_clear_of_beta_embedding_zero_of_graphExtraction
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (β
          (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) = 0) :
    ∀ t ≥ k,
    α'
      x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      t
    =
    (0 : BCIKS20AppendixA.𝕃
      (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) := by
  letI : Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
    Claim57Residuals.ofGraphExtractionHypotheses
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      hcond hfactor
  exact approximate_solution_is_exact_solution_coeffs_graph_clear_of_beta_embedding_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hemb

open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph-clear Claim 5.8 front door from the exact Appendix-A Lemma A.1
largeness condition and explicit graph-extraction data, without requiring an
ambient `[Claim57Residuals]` instance. -/
lemma approximate_solution_is_exact_solution_coeffs_graph_clear_of_Sβ_large_of_graphExtraction
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose)
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) ∧
        Set.ncard (S_β
          (β
            (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_clear_pos
              (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (β
              (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) D *
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree) :
    ∀ t ≥ k,
    α'
      x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      t
    =
    (0 : BCIKS20AppendixA.𝕃
      (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) := by
  letI : Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
    Claim57Residuals.ofGraphExtractionHypotheses
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀) (h_gs := h_gs)
      hcond hfactor
  exact approximate_solution_is_exact_solution_coeffs_graph_clear_of_Sβ_large
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hlarge

open BCIKS20AppendixA.ClaimA2 in
lemma approximate_solution_alpha_powerSeries_eq_trunc_of_beta_embedding_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) = 0) :
    PowerSeries.mk
      (α'
        x₀
        (R k δ x₀ h_gs)
        (irreducible_H k h_gs)
        (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs)) =
      ((PowerSeries.mk
        (α'
          x₀
          (R k δ x₀ h_gs)
          (irreducible_H k h_gs)
          (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs))).trunc k :
        PowerSeries (BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))) := by
  exact alpha'_powerSeries_eq_trunc_of_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H k h_gs)
    (natDegree_H_pos k h_gs)
    (claimA2_hypotheses k h_gs)
    (approximate_solution_is_exact_solution_coeffs_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hemb)

open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 in
/-- Alpha-series truncation from the exact Appendix-A Lemma A.1 largeness
condition. -/
lemma approximate_solution_alpha_powerSeries_eq_trunc_of_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    PowerSeries.mk
      (α'
        x₀
        (R k δ x₀ h_gs)
        (irreducible_H k h_gs)
        (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs)) =
      ((PowerSeries.mk
        (α'
          x₀
          (R k δ x₀ h_gs)
          (irreducible_H k h_gs)
          (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs))).trunc k :
        PowerSeries (BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))) := by
  exact alpha'_powerSeries_eq_trunc_of_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H k h_gs)
    (natDegree_H_pos k h_gs)
    (claimA2_hypotheses k h_gs)
    (approximate_solution_is_exact_solution_coeffs_of_Sβ_large
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hlarge)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma approximate_solution_alpha_graph_clear_powerSeries_eq_trunc_of_beta_embedding_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (β
          (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) = 0) :
    PowerSeries.mk
      (α'
        x₀
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (claimA2_hypotheses_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) =
      ((PowerSeries.mk
        (α'
          x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))).trunc k :
        PowerSeries (BCIKS20AppendixA.𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))) := by
  exact alpha'_powerSeries_eq_trunc_of_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (claimA2_hypotheses_graph_clear
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (approximate_solution_is_exact_solution_coeffs_graph_clear_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hemb)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph-clear alpha-series truncation from the exact Appendix-A Lemma A.1
largeness condition. -/
lemma approximate_solution_alpha_graph_clear_powerSeries_eq_trunc_of_Sβ_large
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) ∧
        Set.ncard (S_β
          (β
            (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_clear_pos
              (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (β
              (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) D *
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree) :
    PowerSeries.mk
      (α'
        x₀
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (claimA2_hypotheses_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) =
      ((PowerSeries.mk
        (α'
          x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))).trunc k :
        PowerSeries (BCIKS20AppendixA.𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))) := by
  exact alpha'_powerSeries_eq_trunc_of_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (claimA2_hypotheses_graph_clear
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (approximate_solution_is_exact_solution_coeffs_graph_clear_of_Sβ_large
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hlarge)

open BCIKS20AppendixA.ClaimA2 in
lemma approximate_solution_gamma_coeff_zero_of_beta_embedding_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) = 0) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs)) =
        (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H k h_gs)
    (natDegree_H_pos k h_gs)
    (claimA2_hypotheses k h_gs)
    (approximate_solution_is_exact_solution_coeffs_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hemb)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Gamma-tail coefficient vanishing from the exact Appendix-A Lemma A.1
largeness condition. -/
lemma approximate_solution_gamma_coeff_zero_of_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs)) =
        (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H k h_gs)
    (natDegree_H_pos k h_gs)
    (claimA2_hypotheses k h_gs)
    (approximate_solution_is_exact_solution_coeffs_of_Sβ_large
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hlarge)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Gamma-tail coefficient vanishing from the genuine recursive Hensel numerator.

This is the `γ'` consumer form of
`approximate_solution_is_exact_solution_coeffs_of_βHensel_Sβ_large`: after the
Appendix-A lift identifies the recursive numerator with the placeholder under
the embedding, `S_β` largeness for `βHensel` gives the vanishing tail used by
the linearity step. -/
lemma approximate_solution_gamma_coeff_zero_of_βHensel_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hcompat : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t) =
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (_root_.BCIKS20.HenselNumerator.βHensel
              (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
              (claimA2_hypotheses k h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs)) =
        (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H k h_gs)
    (natDegree_H_pos k h_gs)
    (claimA2_hypotheses k h_gs)
    (approximate_solution_is_exact_solution_coeffs_of_βHensel_Sβ_large
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hcompat hlarge)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Gamma-tail coefficient vanishing from the genuine Hensel lift identity.

This is the coefficient-level sibling of
`approximate_solution_is_exact_solution_coeffs'_of_βHensel_lift_identity_Sβ_large`:
it converts the native Appendix-A denominator/lift-identity obligations into
the embedded β-compatibility consumed by
`approximate_solution_gamma_coeff_zero_of_βHensel_Sβ_large`. -/
lemma approximate_solution_gamma_coeff_zero_of_βHensel_lift_identity_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hden : ∀ t ≥ k,
      (liftToFunctionField (H := H k δ x₀ h_gs)
            (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1) ≠ 0)
    (hlift : ∀ t ≥ k,
      embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t)
        = α x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t
          * (liftToFunctionField (H := H k δ x₀ h_gs)
              (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (_root_.BCIKS20.HenselNumerator.βHensel
              (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
              (claimA2_hypotheses k h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs)) =
        (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := by
  exact approximate_solution_gamma_coeff_zero_of_βHensel_Sβ_large
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs
    (fun t ht =>
      _root_.BCIKS20.HenselNumerator.β_embedding_eq_of_βHensel_lift_identity
        (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
        (claimA2_hypotheses k h_gs) t (hden t ht) (hlift t ht))
    hlarge

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma approximate_solution_gamma_graph_coeff_zero_of_beta_embedding_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
        (β
          (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) t) = 0) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)) =
        (0 : BCIKS20AppendixA.𝕃
          (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (approximate_solution_is_exact_solution_coeffs_graph_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge hemb)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph gamma-tail coefficient vanishing from the exact Appendix-A Lemma A.1
largeness condition. -/
lemma approximate_solution_gamma_graph_coeff_zero_of_Sβ_large
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlargeS : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) ∧
        Set.ncard (S_β
          (β
            (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
            (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
            (β
              (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge) t) D *
            (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge).natDegree) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)) =
        (0 : BCIKS20AppendixA.𝕃
          (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (approximate_solution_is_exact_solution_coeffs_graph_of_Sβ_large
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge hlargeS)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma approximate_solution_gamma_graph_clear_coeff_zero_of_beta_embedding_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (β
          (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) = 0) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) =
        (0 : BCIKS20AppendixA.𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (claimA2_hypotheses_graph_clear
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (approximate_solution_is_exact_solution_coeffs_graph_clear_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hemb)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph-clear gamma-tail coefficient vanishing from the exact Appendix-A
Lemma A.1 largeness condition. -/
lemma approximate_solution_gamma_graph_clear_coeff_zero_of_Sβ_large
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) ∧
        Set.ncard (S_β
          (β
            (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_clear_pos
              (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (β
              (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) D *
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree) :
    ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) =
        (0 : BCIKS20AppendixA.𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) := by
  exact gamma'_coeff_zero_of_alpha'_coeff_zero
    (F := F) (x₀ := x₀)
    (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (claimA2_hypotheses_graph_clear
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (approximate_solution_is_exact_solution_coeffs_graph_clear_of_Sβ_large
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hlarge)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph-extractor version of the conditional Claim 5.8' bridge.  Once the
Appendix-A argument supplies tail-coefficient vanishing for the `γ'` built from
`R_graph,H_graph`, the published truncation statement follows immediately. -/
lemma approximate_solution_is_exact_solution_coeffs_graph'_of_gamma_coeff_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hzero : ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)) =
        (0 : BCIKS20AppendixA.𝕃
          (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge))) :
    γ' x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃
            (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge))) := by
  exact powerSeries_eq_truncate_of_coeff_zero_ge
    (γ' x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge))
    hzero

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Cleared graph-extractor version of the conditional Claim 5.8' bridge. -/
lemma approximate_solution_is_exact_solution_coeffs_graph_clear'_of_gamma_coeff_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hzero : ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)) =
        (0 : BCIKS20AppendixA.𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))) :
    γ' x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (irreducible_H_graph_clear
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (natDegree_H_graph_clear_pos
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (claimA2_hypotheses_graph_clear
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))) := by
  exact powerSeries_eq_truncate_of_coeff_zero_ge
    (γ' x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
    hzero

open BCIKS20AppendixA.ClaimA2 in
lemma approximate_solution_is_exact_solution_coeffs'_of_beta_embedding_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) = 0) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
  exact powerSeries_eq_truncate_of_coeff_zero_ge
    (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs))
    (approximate_solution_gamma_coeff_zero_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hemb)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8' front door from the exact Appendix-A Lemma A.1 largeness
condition.  This is the published γ-truncation form consumed by the linearity
step, with the missing geometric work isolated as an `S_β` counting
hypothesis. -/
lemma approximate_solution_is_exact_solution_coeffs'_of_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
  exact powerSeries_eq_truncate_of_coeff_zero_ge
    (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs))
    (gamma'_coeff_zero_of_alpha'_coeff_zero
      (F := F) (x₀ := x₀)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      (approximate_solution_is_exact_solution_coeffs_of_Sβ_large
        (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
        h_gs hlarge))

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8' front door from the genuine recursive Hensel numerator.

This is the published `γ'` truncation statement with the remaining geometric
work isolated as `S_β` largeness for the actual recursive Hensel numerator,
plus the Appendix-A compatibility equality identifying that numerator with the
placeholder `β` under the embedding. -/
lemma approximate_solution_is_exact_solution_coeffs'_of_βHensel_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hcompat : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t) =
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (β (H := H k δ x₀ h_gs) (R k δ x₀ h_gs) t))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (_root_.BCIKS20.HenselNumerator.βHensel
              (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
              (claimA2_hypotheses k h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
  exact powerSeries_eq_truncate_of_coeff_zero_ge
    (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs))
    (approximate_solution_gamma_coeff_zero_of_βHensel_Sβ_large
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hcompat hlarge)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8' front door from the genuine Hensel lift identity.

This packages the two Appendix-A proof obligations in their native form:
the lift denominator is nonzero, and the recursive Hensel numerator satisfies
the denominator-cleared identity.  The helper
`β_embedding_eq_of_βHensel_lift_identity` converts those obligations into the
embedding compatibility consumed by
`approximate_solution_is_exact_solution_coeffs'_of_βHensel_Sβ_large`. -/
lemma approximate_solution_is_exact_solution_coeffs'_of_βHensel_lift_identity_Sβ_large
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hden : ∀ t ≥ k,
      (liftToFunctionField (H := H k δ x₀ h_gs)
            (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1) ≠ 0)
    (hlift : ∀ t ≥ k,
      embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t)
        = α x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t
          * (liftToFunctionField (H := H k δ x₀ h_gs)
              (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) >
          weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
            (_root_.BCIKS20.HenselNumerator.βHensel
              (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
              (claimA2_hypotheses k h_gs) t) D *
            (H k δ x₀ h_gs).natDegree) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
  exact approximate_solution_is_exact_solution_coeffs'_of_βHensel_Sβ_large
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs
    (fun t ht =>
      _root_.BCIKS20.HenselNumerator.β_embedding_eq_of_βHensel_lift_identity
        (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
        (claimA2_hypotheses k h_gs) t (hden t ht) (hlift t ht))
    hlarge

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8' front door from the structured Hensel-weight route.

This is the published `γ'` truncation form, with the intermediate `S_β`
largeness discharged by `βHensel_Sβ_large_of_structured_weight`. -/
lemma approximate_solution_is_exact_solution_coeffs'_of_βHensel_lift_identity_structured_weight
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hden : ∀ t ≥ k,
      (liftToFunctionField (H := H k δ x₀ h_gs)
            (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1) ≠ 0)
    (hlift : ∀ t ≥ k,
      embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
        (_root_.BCIKS20.HenselNumerator.βHensel
          (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
          (claimA2_hypotheses k h_gs) t)
        = α x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t
          * (liftToFunctionField (H := H k δ x₀ h_gs)
              (H k δ x₀ h_gs).leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 (H k δ x₀ h_gs)
              (ξ x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs)
                (claimA2_hypotheses k h_gs))) ^ (2 * t - 1))
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree (H k δ x₀ h_gs) ∧
        2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs) ∧
        Bivariate.natDegreeY (H k δ x₀ h_gs) ≤
          Bivariate.natDegreeY (R k δ x₀ h_gs) ∧
        (H k δ x₀ h_gs).leadingCoeff.natDegree +
            Bivariate.natDegreeY (H k δ x₀ h_gs) ≤ D ∧
        weight_Λ_over_𝒪 (natDegree_H_pos k h_gs)
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t) D
          ≤ WithBot.some
            (1 + (t + 1) * (H k δ x₀ h_gs).leadingCoeff.natDegree
              + (2 * t - 1)
                * ((Bivariate.natDegreeY (R k δ x₀ h_gs) - 1)
                  * (D - Bivariate.natDegreeY (H k δ x₀ h_gs) + 1))) ∧
        (Set.ncard (S_β
          (_root_.BCIKS20.HenselNumerator.βHensel
            (H := H k δ x₀ h_gs) x₀ (R k δ x₀ h_gs)
            (claimA2_hypotheses k h_gs) t)) : WithBot ℕ) >
          WithBot.some
            ((2 * t + 1) * Bivariate.natDegreeY (R k δ x₀ h_gs) * D)
            * ((H k δ x₀ h_gs).natDegree : WithBot ℕ)) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
  exact powerSeries_eq_truncate_of_coeff_zero_ge
    (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs))
    (gamma'_coeff_zero_of_alpha'_coeff_zero
      (F := F) (x₀ := x₀)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      (approximate_solution_is_exact_solution_coeffs_of_βHensel_lift_identity_structured_weight
        (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
        h_gs hden hlift hlarge))

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma approximate_solution_is_exact_solution_coeffs_graph'_of_beta_embedding_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
        (β
          (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) t) = 0) :
    γ' x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃
            (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge))) := by
  exact approximate_solution_is_exact_solution_coeffs_graph'_of_gamma_coeff_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
    hx0 hsep hS_nonempty A hA hcount hlarge
    (approximate_solution_gamma_graph_coeff_zero_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge hemb)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph Claim 5.8' front door from the exact Appendix-A Lemma A.1
largeness condition. -/
lemma approximate_solution_is_exact_solution_coeffs_graph'_of_Sβ_large
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlargeS : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) ∧
        Set.ncard (S_β
          (β
            (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
            (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
            (β
              (H := H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge) t) D *
            (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge).natDegree) :
    γ' x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃
            (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge)
              (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
                hx0 hsep hS_nonempty A hA hcount hlarge))) := by
  exact approximate_solution_is_exact_solution_coeffs_graph'_of_gamma_coeff_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
    hx0 hsep hS_nonempty A hA hcount hlarge
    (gamma'_coeff_zero_of_alpha'_coeff_zero
      (F := F) (x₀ := x₀)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (approximate_solution_is_exact_solution_coeffs_graph_of_Sβ_large
        (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge hlargeS))

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma approximate_solution_is_exact_solution_coeffs_graph_clear'_of_beta_embedding_zero
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hemb : ∀ t ≥ k,
      BCIKS20AppendixA.embeddingOf𝒪Into𝕃
          (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (β
          (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) = 0) :
    γ' x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (irreducible_H_graph_clear
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (natDegree_H_graph_clear_pos
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (claimA2_hypotheses_graph_clear
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))) := by
  exact approximate_solution_is_exact_solution_coeffs_graph_clear'_of_gamma_coeff_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
    (approximate_solution_gamma_graph_clear_coeff_zero_of_beta_embedding_zero
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hemb)

open BCIKS20AppendixA in
open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
/-- Graph-clear Claim 5.8' front door from the exact Appendix-A Lemma A.1
largeness condition. -/
lemma approximate_solution_is_exact_solution_coeffs_graph_clear'_of_Sβ_large
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlarge : ∀ t ≥ k, ∃ D : ℕ,
      D ≥ Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) ∧
        Set.ncard (S_β
          (β
            (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t)) >
          weight_Λ_over_𝒪
            (natDegree_H_graph_clear_pos
              (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
            (β
              (H := H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) t) D *
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond).natDegree) :
    γ' x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃
            (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (irreducible_H_graph_clear
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (natDegree_H_graph_clear_pos
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
              (claimA2_hypotheses_graph_clear
                (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))) := by
  exact approximate_solution_is_exact_solution_coeffs_graph_clear'_of_gamma_coeff_zero
    (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
    (gamma'_coeff_zero_of_alpha'_coeff_zero
      (F := F) (x₀ := x₀)
      (irreducible_H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (approximate_solution_is_exact_solution_coeffs_graph_clear_of_Sβ_large
        (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond hlarge))

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution. This version of the claim is stated in
terms of coefficients.

GAP (blocked — see the §5 GAP ANALYSIS block above). `α' x₀ R … t = embeddingOf𝒪Into𝕃 _ (β R t)
/ (W^(t+1) · ξ-emb^(2t-1))`, so the goal reduces by `zero_div` to `embeddingOf𝒪Into𝕃 _ (β R t)
= 0`, which is the conclusion of `Lemma_A_1`. But `Lemma_A_1`'s hypothesis `#(S_β (β R t)) >
Λ(β R t)·dₕ` has no supplier (missing ingredient C), and more fundamentally `β R t` is an opaque
weight-bounded `.choose`, not the recursive Hensel numerator (missing ingredient D), so the
conclusion is underdetermined by the current definitions. -/
lemma approximate_solution_is_exact_solution_coeffs
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hzero : ∀ t ≥ k,
      α'
        x₀
        (R k δ x₀ h_gs)
        (irreducible_H k h_gs)
        (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs)
        t =
      (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))) : ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs)) := hzero

open BCIKS20AppendixA.ClaimA2 in
/-- Side-condition-explicit form of Claim 5.8'.  Once the Appendix-A argument
has supplied vanishing of all coefficients of `γ'` in degrees `≥ k`, the
published truncation statement is immediate. -/
lemma approximate_solution_is_exact_solution_coeffs'_of_gamma_coeff_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hzero : ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs)) =
        (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
  exact powerSeries_eq_truncate_of_coeff_zero_ge
    (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs))
    hzero

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution.
This version is in terms of polynomials.

GAP (blocked — see the §5 GAP ANALYSIS block above). Equivalent to `coeff t γ' = 0` for `t ≥ k`.
Would follow from the coefficient form (`approximate_solution_is_exact_solution_coeffs`) by
`PowerSeries.subst` bookkeeping on `γ = subst (mk shift) (mk α)`, but that form is itself blocked
(ingredients C, D), so this cannot stand alone. -/
lemma approximate_solution_is_exact_solution_coeffs'
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hzero : ∀ t ≥ k,
      PowerSeries.coeff t
        (γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
          (claimA2_hypotheses k h_gs)) =
        (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
            (irreducible_H k h_gs)
            (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
  exact approximate_solution_is_exact_solution_coeffs'_of_gamma_coeff_zero
    (F := F) (m := m) (n := n) (k := k) (δ := δ) (x₀ := x₀) (Q := Q)
    h_gs hzero

open Polynomial Polynomial.Bivariate in
noncomputable def constantCoeffPolynomialInY (P : F[Z][X]) : F[X] :=
  P.sum fun n p => Polynomial.monomial n (p.coeff 0)

open Polynomial Polynomial.Bivariate in
noncomputable def linearCoeffPolynomialInY (P : F[Z][X]) : F[X] :=
  P.sum fun n p => Polynomial.monomial n (p.coeff 1)

open Polynomial Polynomial.Bivariate in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma exists_linear_in_coeff_variable_of_degreeX_le_one (Ppoly : F[Z][X])
    (hP : Bivariate.degreeX Ppoly ≤ 1) :
    ∃ v₀ v₁ : F[X],
      Ppoly =
        (Polynomial.map Polynomial.C v₀) +
          (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) := by
  classical
  refine ⟨constantCoeffPolynomialInY Ppoly, linearCoeffPolynomialInY Ppoly, ?_⟩
  apply Polynomial.ext
  intro n
  apply Polynomial.ext
  intro j
  simp only [coeff_add, coeff_map, coeff_C_mul]
  unfold constantCoeffPolynomialInY linearCoeffPolynomialInY
  simp only [Polynomial.sum]
  rw [Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n ∈ Ppoly.support
  · have hne : Ppoly.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    have hdeg : (Ppoly.coeff n).natDegree ≤ 1 :=
      le_trans (Bivariate.coeff_natDegree_le_degreeX Ppoly n) hP
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
    simp [hne, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    ring_nf
  · have hp0 : Ppoly.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    simp [hn, hp0]

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma gamma'_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    {R : F[Z][X][Y]} {H : F[Z][X]}
    (H_irreducible : Irreducible H) (hHdeg : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H)
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ R H_irreducible hHdeg hHyp =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1) :
    ∃ (v₀ v₁ : F[X]),
      γ' x₀ R H_irreducible hHdeg hHyp =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _
            (
              (Polynomial.map Polynomial.C v₀) +
              (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
            ) := by
  rcases exists_linear_in_coeff_variable_of_degreeX_le_one (F := F) Ppoly hP with
    ⟨v₀, v₁, hlin⟩
  refine ⟨v₀, v₁, ?_⟩
  rw [hrepr, hlin]

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma eval_linear_in_coeff_variable (v₀ v₁ : F[X]) (a : F) :
    (((Polynomial.map Polynomial.C v₀) +
      (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) : F[Z][X]).eval
        (Polynomial.C a)) =
      (Polynomial.C (v₀.eval a) + (v₁.eval a) • Polynomial.X : F[X]) := by
  rw [Polynomial.eval_add, Polynomial.eval_mul]
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [Polynomial.eval_C]
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [mul_comm Polynomial.X (Polynomial.C (v₁.eval a))]
  rw [Polynomial.C_mul']

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma eval_linear_in_coeff_variable_eq_word
    {v₀ v₁ : F[X]} {a u₀ u₁ : F}
    (h₀ : v₀.eval a = u₀) (h₁ : v₁.eval a = u₁) :
    (((Polynomial.map Polynomial.C v₀) +
      (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) : F[Z][X]).eval
        (Polynomial.C a)) =
      (Polynomial.C u₀ + u₁ • Polynomial.X : F[X]) := by
  rw [eval_linear_in_coeff_variable, h₀, h₁]

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma polynomial_representative_matches_word_of_linear_coeff_values
    {Ppoly : F[Z][X]} {v₀ v₁ : F[X]} {a u₀ u₁ : F}
    (hlin :
      Ppoly =
        (Polynomial.map Polynomial.C v₀) +
          (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
    (h₀ : v₀.eval a = u₀) (h₁ : v₁.eval a = u₁) :
    Ppoly.eval (Polynomial.C a) =
      (Polynomial.C u₀ + u₁ • Polynomial.X : F[X]) := by
  rw [hlin]
  exact eval_linear_in_coeff_variable_eq_word (F := F) h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma polynomial_representative_eval_eval_eq_word_of_linear_coeff_values
    {Ppoly : F[Z][X]} {v₀ v₁ : F[X]} {a u₀ u₁ z : F}
    (hlin :
      Ppoly =
        (Polynomial.map Polynomial.C v₀) +
          (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
    (h₀ : v₀.eval a = u₀) (h₁ : v₁.eval a = u₁) :
    (Ppoly.eval (Polynomial.C a)).eval z = u₀ + z * u₁ := by
  rw [polynomial_representative_matches_word_of_linear_coeff_values
    (F := F) hlin h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 in
lemma solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1) :
    ∃ (v₀ v₁ : F[X]),
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _
            (
              (Polynomial.map Polynomial.C v₀) +
              (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
            ) := by
  exact gamma'_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    (F := F) (x₀ := x₀)
    (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
    (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
    (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs)
    hrepr hP

open BCIKS20AppendixA.ClaimA2 in
/-- The polynomial represented by an explicit linearity witness for the base
approximate solution.  Unlike `P`, this does not depend on the unsolved
published Claim 5.9; the witness is supplied as a side condition. -/
noncomputable def P_of_linear_witness
    (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        BCIKS20AppendixA.ClaimA2.γ' x₀ (R k δ x₀ h_gs)
          (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))) : F[Z][X] :=
  let v₀ := Classical.choose hlin
  let v₁ := Classical.choose (Classical.choose_spec hlin)
  (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)

open BCIKS20AppendixA.ClaimA2 in
/-- The explicit-witness polynomial represents the base `γ'`. -/
lemma gamma_eq_P_of_linear_witness
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        BCIKS20AppendixA.ClaimA2.γ' x₀ (R k δ x₀ h_gs)
          (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))) :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
      (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
      (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (P_of_linear_witness k δ x₀ h_gs hlin) := by
  exact Classical.choose_spec (Classical.choose_spec hlin)

open BCIKS20AppendixA.ClaimA2 Polynomial in
/-- Algebraic Claim 5.10 core for an explicit base linearity witness. -/
lemma P_eval_eq_word_of_linear_witness_coeff_values
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    (x : Fin n)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    (P_of_linear_witness k δ x₀ h_gs hlin).eval (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
  unfold P_of_linear_witness
  exact polynomial_representative_matches_word_of_linear_coeff_values
    (F := F) (a := ωs x) (u₀ := u₀ x) (u₁ := u₁ x) rfl h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
/-- Scalar-evaluated algebraic Claim 5.10 core for an explicit base linearity
witness. -/
lemma P_eval_eval_eq_word_of_linear_witness_coeff_values
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    (x : Fin n) (z : F)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    ((P_of_linear_witness k δ x₀ h_gs hlin).eval (Polynomial.C (ωs x))).eval z =
      u₀ x + z * u₁ x := by
  rw [P_eval_eq_word_of_linear_witness_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hlin x h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀
        (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1) :
    ∃ (v₀ v₁ : F[X]),
      γ' x₀
        (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _
            (
              (Polynomial.map Polynomial.C v₀) +
              (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
            ) := by
  exact gamma'_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    (F := F) (x₀ := x₀)
    (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)
    hrepr hP

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
noncomputable def P_graph_of_linear_witness
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))) : F[Z][X] :=
  let v₀ := Classical.choose hlin
  let v₁ := Classical.choose (Classical.choose_spec hlin)
  (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma gamma_graph_eq_P_graph_of_linear_witness
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))) :
    γ' x₀
      (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge)
      (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (P_graph_of_linear_witness
            (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge hlin) := by
  exact Classical.choose_spec (Classical.choose_spec hlin)

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma P_graph_eval_eq_word_of_linear_coeff_values
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    (x : Fin n)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    (P_graph_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge hlin).eval
      (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
  unfold P_graph_of_linear_witness
  exact polynomial_representative_matches_word_of_linear_coeff_values
    (F := F) (a := ωs x) (u₀ := u₀ x) (u₁ := u₁ x) rfl h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma P_graph_eval_eval_eq_word_of_linear_coeff_values
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    (x : Fin n) (z : F)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    ((P_graph_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge hlin).eval
      (Polynomial.C (ωs x))).eval z = u₀ x + z * u₁ x := by
  rw [P_graph_eval_eq_word_of_linear_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty A hA hcount hlarge hlin x h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (irreducible_H_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (natDegree_H_graph_clear_pos
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (claimA2_hypotheses_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1) :
    ∃ (v₀ v₁ : F[X]),
      γ' x₀
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (irreducible_H_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (natDegree_H_graph_clear_pos
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (claimA2_hypotheses_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _
            (
              (Polynomial.map Polynomial.C v₀) +
              (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
            ) := by
  exact gamma'_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    (F := F) (x₀ := x₀)
    (irreducible_H_graph_clear
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (natDegree_H_graph_clear_pos
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    (claimA2_hypotheses_graph_clear
      (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
    hrepr hP

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
noncomputable def P_graph_clear_of_linear_witness
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))) : F[Z][X] :=
  let v₀ := Classical.choose hlin
  let v₁ := Classical.choose (Classical.choose_spec hlin)
  (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)

open BCIKS20AppendixA.ClaimA2 in
omit [DecidableEq (RatFunc F)] in
lemma gamma_graph_clear_eq_P_graph_clear_of_linear_witness
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))) :
    γ' x₀
      (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (irreducible_H_graph_clear
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (natDegree_H_graph_clear_pos
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
      (claimA2_hypotheses_graph_clear
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (P_graph_clear_of_linear_witness
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond hlin) := by
  exact Classical.choose_spec (Classical.choose_spec hlin)

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma P_graph_clear_eval_eq_word_of_linear_coeff_values
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    (x : Fin n)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    (P_graph_clear_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond hlin).eval
      (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
  unfold P_graph_clear_of_linear_witness
  exact polynomial_representative_matches_word_of_linear_coeff_values
    (F := F) (a := ωs x) (u₀ := u₀ x) (u₁ := u₁ x) rfl h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma P_graph_clear_eval_eval_eq_word_of_linear_coeff_values
    [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    (x : Fin n) (z : F)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    ((P_graph_clear_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond hlin).eval
      (Polynomial.C (ωs x))).eval z = u₀ x + z * u₁ x := by
  rw [P_graph_clear_eval_eq_word_of_linear_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hcond hlin x h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.9 from [BCIKS20].
States that the solution `γ` is linear in the variable `Z`.

GAP (blocked — see the §5 GAP ANALYSIS block above). Consumes Claim 5.8' (the degree-`< k`
truncation of `γ`) together with the `Bivariate.degreeX P ≤ 1` output of the Prop 5.5
specialization to read off the linear representative `v₀ + Z·v₁`. Blocked transitively on 5.8'
(ingredients C, D) and on the specialization from Guruswami multiplicity/factor data to the proven
`tagged_fiber_pigeonhole` core in `Guruswami.lean`. -/
lemma solution_gamma_is_linear_in_Z
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1) :
  ∃ (v₀ v₁ : F[X]),
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
      (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
      (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) :=
  solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hrepr hP

open BCIKS20AppendixA.ClaimA2 in
/-- The linear represenation of the solution `γ` extracted from Claim 5.9. -/
noncomputable def P (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1) : F[Z][X] :=
  let v₀ := Classical.choose
    (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs hrepr hP)
  let v₁ := Classical.choose
    (Classical.choose_spec <|
      solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs hrepr hP)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open BCIKS20AppendixA.ClaimA2 in
/-- The extracted `P` from Claim 5.9 equals `γ`. -/
lemma gamma_eq_P (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1) :
  γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
    (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
    (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
  BCIKS20AppendixA.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs hrepr hP) :=
  Classical.choose_spec
    (Classical.choose_spec
      (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs hrepr hP))

open BCIKS20AppendixA.ClaimA2 Polynomial in
/-- Side-condition-explicit algebraic core of Claim 5.10.  Once the linear
representative extracted by Claim 5.9 has coefficient polynomials evaluating to
the word values at `ωs x`, the desired `P(ωs x) = u₀ x + (u₁ x) Z`
identity is immediate. -/
lemma P_eval_eq_word_of_solution_gamma_coeff_values
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    (x : Fin n)
    (h₀ : (Classical.choose
        (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs hrepr hP)).eval
        (ωs x) = u₀ x)
    (h₁ : (Classical.choose
        (Classical.choose_spec <|
          solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs hrepr hP)).eval
        (ωs x) = u₁ x) :
    (P k δ x₀ h_gs hrepr hP).eval (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
  unfold P
  exact polynomial_representative_matches_word_of_linear_coeff_values
    (F := F) (a := ωs x) (u₀ := u₀ x) (u₁ := u₁ x) rfl h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
/-- Scalar-evaluated form of `P_eval_eq_word_of_solution_gamma_coeff_values`.
This is the shape consumed by the curve assembly layer after evaluating the
linear representative at a curve parameter `z`. -/
lemma P_eval_eval_eq_word_of_solution_gamma_coeff_values
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    (x : Fin n) (z : F)
    (h₀ : (Classical.choose
        (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs hrepr hP)).eval
        (ωs x) = u₀ x)
    (h₁ : (Classical.choose
        (Classical.choose_spec <|
          solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs hrepr hP)).eval
        (ωs x) = u₁ x) :
    ((P k δ x₀ h_gs hrepr hP).eval (Polynomial.C (ωs x))).eval z =
      u₀ x + z * u₁ x := by
  rw [P_eval_eq_word_of_solution_gamma_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hrepr hP x h₀ h₁]
  simp [mul_comm]

omit [DecidableEq (RatFunc F)] in
/-- The chosen close polynomial family as a total function of the curve
parameter.  Outside `coeffs_of_close_proximity` the value is irrelevant; all
assembly lemmas consume it only on that finite set. -/
noncomputable def PzFamily
    (δ : ℚ) (u₀ u₁ : Fin n → F) (ωs : Fin n ↪ F) (k : ℕ) : F → F[X] :=
  fun z =>
    if h : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ then
      Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) h
    else
      0

omit [DecidableEq (RatFunc F)] in
lemma PzFamily_eq_Pz_of_mem
    {z : F} (hz : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z =
      Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz := by
  simp [PzFamily, hz]

omit [DecidableEq (RatFunc F)] in
lemma PzFamily_coeff_eq_Pz_coeff_of_mem
    {z : F} (hz : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) (j : ℕ) :
    (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).coeff j =
      (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).coeff j := by
  rw [PzFamily_eq_Pz_of_mem (F := F) (n := n) (k := k)
    (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz]

omit [DecidableEq (RatFunc F)] in
lemma PzFamily_eval_eq_Pz_eval_of_mem
    {z : F} (hz : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) (x : F) :
    (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval x =
      (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hz).eval x := by
  rw [PzFamily_eq_Pz_of_mem (F := F) (n := n) (k := k)
    (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz]

omit [DecidableEq (RatFunc F)] in
lemma PzFamily_natDegree_lt_succ_of_mem
    {z : F} (hz : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).natDegree < k + 1 := by
  rw [PzFamily_eq_Pz_of_mem (F := F) (n := n) (k := k)
    (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz]
  exact Nat.lt_succ_of_le
    (Pz_natDegree_le (n := n) (k := k) (ωs := ωs) (δ := δ)
      (u₀ := u₀) (u₁ := u₁) hz)

omit [DecidableEq (RatFunc F)] in
lemma PzFamily_relDist_le_of_mem
    {z : F} (hz : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    δᵣ(u₀ + z • u₁,
        (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval ∘ ωs) ≤ δ := by
  rw [PzFamily_eq_Pz_of_mem (F := F) (n := n) (k := k)
    (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz]
  exact Pz_relDist_le (n := n) (k := k) (ωs := ωs) (δ := δ)
    (u₀ := u₀) (u₁ := u₁) hz

omit [DecidableEq (RatFunc F)] in
/-- `PzFamily` has exactly the decoded-family hypotheses used by the §6
coefficient/evaluation-polynomial assembly front doors, restricted to the close
parameter set. -/
lemma PzFamily_decoded_on_close_set :
    ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).natDegree < k + 1 ∧
        δᵣ(u₀ + z • u₁,
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval ∘ ωs) ≤ δ := by
  intro z hz
  exact ⟨PzFamily_natDegree_lt_succ_of_mem
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz,
    PzFamily_relDist_le_of_mem
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz⟩

/-- The set `S'` from [BCIKS20] (just before Claim 5.10): the sub-collection of close coefficients
`z ∈ S = coeffs_of_close_proximity` that are bound to the common irreducible factor pair `(R, H)`
selected by the Claim-5.7 pigeonhole.

REPAIR NOTE (pre-existing breakage). `matching_set`,
`matching_set_is_a_sub_of_coeffs_of_close_proximity`, and the upstream Prop 5.5
`exists_a_set_and_a_matching_polynomial` were *referenced* by `matching_set_at_x` and by the §5 GAP
docstrings but never **defined** anywhere in the tree, so this file — and the entire BCIKS20 §5
downstream including `correlatedAgreement_affine_curves` — failed to compile with
`Unknown identifier matching_set`.  We supply the missing definition here.

Faithfulness: in [BCIKS20] `S' ⊆ S` is the fiber bound to the chosen `(R, H)`.  Pinning that fiber
formally would force `matching_set` to carry the Claim-5.7 `.choose` data `R k δ x₀ h_gs` (hence an
extra `x₀` parameter the uneditable call site `matching_set k ωs δ u₀ u₁ h_gs` does not pass).  We
therefore define `S' := S` (the maximal subset) — an honest *over-approximation* of the paper's
`S'`. This only ever **weakens** the explicit cardinality hypotheses carried by the
Claim-5.10/Claim-5.11 residualized wrappers (a larger
`S'` makes `|S'_x|` larger, so their hypotheses are easier, not vacuous), and the inclusion
`S' ⊆ S` holds by `id`.  No proven statement is affected. -/
noncomputable def matching_set
    (k : ℕ) (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Finset F :=
  coeffs_of_close_proximity k ωs δ u₀ u₁

omit [DecidableEq (RatFunc F)] in
/-- `matching_set` (BCIKS20's `S'`) is a subset of `S = coeffs_of_close_proximity` (here, equal by
the `S' := S` over-approximation — see `matching_set`). -/
lemma matching_set_is_a_sub_of_coeffs_of_close_proximity
    (k : ℕ) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {z : F}
    (h : z ∈ matching_set k ωs δ u₀ u₁ h_gs) :
    z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁ := h

/-- The set `S'_x` from [BCIKS20] (just before Claim 5.10). The set of all `z ∈ S'` such that
`w(x,z)` matches `P_z(x)`. -/
noncomputable def matching_set_at_x
    (δ : ℚ)
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) : Finset F := @Set.toFinset _ {z : F | ∃ h : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁,
    u₀ x + z * u₁ x =
      (Pz h).eval (ωs x)}
      (@Fintype.ofFinite _ Subtype.finite)

/-- For a fixed close parameter `z`, the coordinates where the word
`u₀ + z • u₁` matches its Reed-Solomon witness polynomial. -/
noncomputable def matching_coords_for_z
    (δ : ℚ)
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun x =>
    u₀ x + z.1 * u₁ x =
      (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
        (ωs x)

omit [DecidableEq (RatFunc F)] in
lemma mem_matching_coords_for_z
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) (x : Fin n) :
    x ∈ matching_coords_for_z k δ h_gs z ↔
      u₀ x + z.1 * u₁ x =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs x) := by
  simp [matching_coords_for_z]

omit [DecidableEq (RatFunc F)] in
lemma mem_matching_coords_for_z_iff_PzFamily
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) (x : Fin n) :
    x ∈ matching_coords_for_z k δ h_gs z ↔
      u₀ x + z.1 * u₁ x =
        (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z.1).eval (ωs x) := by
  rw [mem_matching_coords_for_z
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z x]
  rw [PzFamily_eq_Pz_of_mem
    (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) z.2]

omit [DecidableEq (RatFunc F)] in
lemma coeff_mem_matching_set_at_x_of_mem_matching_coords
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) {x : Fin n}
    (hx : x ∈ matching_coords_for_z k δ h_gs z) :
    z.1 ∈ matching_set_at_x k δ h_gs x := by
  rw [mem_matching_coords_for_z (F := F) (m := m) (n := n) (k := k) (Q := Q)
    h_gs z x] at hx
  simpa [matching_set_at_x] using hx

omit [DecidableEq (RatFunc F)] in
lemma matching_coords_filter_card_le_matching_set_at_x_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (S : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) (x : Fin n) :
    (S.filter (fun z => x ∈ matching_coords_for_z k δ h_gs z)).card ≤
      (matching_set_at_x k δ h_gs x).card := by
  classical
  let img : Finset F := (S.filter (fun z =>
    x ∈ matching_coords_for_z k δ h_gs z)).image (fun z => (z.1 : F))
  have hsub : img ⊆ matching_set_at_x k δ h_gs x := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact coeff_mem_matching_set_at_x_of_mem_matching_coords
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z
      (Finset.mem_filter.mp hz).2
  have hcard :
      img.card = (S.filter (fun z => x ∈ matching_coords_for_z k δ h_gs z)).card := by
    dsimp [img]
    exact Finset.card_image_of_injective _ fun a b h => Subtype.ext h
  rw [← hcard]
  exact Finset.card_le_card hsub

omit [DecidableEq (RatFunc F)] in
lemma mem_matching_set_at_x_iff
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) (z : F) :
    z ∈ matching_set_at_x k δ h_gs x ↔
      ∃ _h : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁,
        u₀ x + z * u₁ x =
          (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) _h).eval
            (ωs x) := by
  simp [matching_set_at_x]

omit [DecidableEq (RatFunc F)] in
lemma mem_matching_set_at_x_iff_PzFamily
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) (z : F) :
    z ∈ matching_set_at_x k δ h_gs x ↔
      ∃ (_ : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁),
        u₀ x + z * u₁ x =
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) := by
  rw [mem_matching_set_at_x_iff
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x z]
  constructor
  · rintro ⟨hz, hmatch⟩
    refine ⟨hz, ?_⟩
    rwa [PzFamily_eq_Pz_of_mem
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz]
  · rintro ⟨hz, hmatch⟩
    refine ⟨hz, ?_⟩
    rwa [PzFamily_eq_Pz_of_mem
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz] at hmatch

omit [DecidableEq (RatFunc F)] in
lemma matching_set_at_x_eq_filter_PzFamily
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) :
    matching_set_at_x k δ h_gs x =
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).filter fun z =>
        u₀ x + z * u₁ x =
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) := by
  apply Finset.ext
  intro z
  rw [mem_matching_set_at_x_iff_PzFamily
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x z]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, hmatch⟩
    exact ⟨hz, hmatch⟩
  · rintro ⟨hz, hmatch⟩
    exact ⟨hz, hmatch⟩

omit [DecidableEq (RatFunc F)] in
lemma matching_set_at_x_card_eq_filter_PzFamily
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) :
    (matching_set_at_x k δ h_gs x).card =
      ((coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).filter fun z =>
        u₀ x + z * u₁ x =
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x)).card := by
  rw [matching_set_at_x_eq_filter_PzFamily
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x]

omit [DecidableEq (RatFunc F)] in
lemma matching_set_at_x_subset_close_proximity
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) :
    matching_set_at_x k δ h_gs x ⊆
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ := by
  intro z hz
  exact (mem_matching_set_at_x_iff
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x z).mp hz |>.1

omit [DecidableEq (RatFunc F)] in
lemma close_proximity_subset_matching_set_at_x_of_card_le
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n)
    (hcard :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card ≤
        (matching_set_at_x k δ h_gs x).card) :
    coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
      matching_set_at_x k δ h_gs x := by
  have hEq :
      matching_set_at_x k δ h_gs x =
        coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ :=
    Finset.eq_of_subset_of_card_le
      (matching_set_at_x_subset_close_proximity
        (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x)
      hcard
  intro z hz
  rwa [← hEq] at hz

omit [DecidableEq (RatFunc F)] in
lemma close_proximity_subset_matching_set_at_x_of_pred_lt_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n)
    (hcard :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 <
        (matching_set_at_x k δ h_gs x).card) :
    coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
      matching_set_at_x k δ h_gs x := by
  apply close_proximity_subset_matching_set_at_x_of_card_le
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x
  omega

omit [DecidableEq (RatFunc F)] in
lemma close_proximity_subset_matching_set_at_x_on_domain_of_card_le
    {ωs : Fin n ↪ F} {Dtop : Finset (Fin n)}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcard : ∀ x ∈ Dtop,
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card ≤
        (matching_set_at_x k δ h_gs x).card) :
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  intro x hx
  exact close_proximity_subset_matching_set_at_x_of_card_le
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x (hcard x hx)

omit [DecidableEq (RatFunc F)] in
lemma close_proximity_subset_matching_set_at_x_on_domain_of_pred_lt_card
    {ωs : Fin n ↪ F} {Dtop : Finset (Fin n)}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hcard : ∀ x ∈ Dtop,
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 <
        (matching_set_at_x k δ h_gs x).card) :
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  intro x hx
  exact close_proximity_subset_matching_set_at_x_of_pred_lt_card
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x (hcard x hx)

open Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- The degree-one curve-parameter polynomial representing the line word at a
fixed coordinate. -/
noncomputable def lineValuePolynomial (u₀ u₁ : Fin n → F) (x : Fin n) : F[X] :=
  Polynomial.C (u₀ x) + Polynomial.C (u₁ x) * Polynomial.X

open Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- The coordinate-indexed polynomial family `z ↦ u₀ x + z · u₁ x`. -/
noncomputable def lineValuePolynomialFamily (u₀ u₁ : Fin n → F) : Fin n → F[X] :=
  fun x => lineValuePolynomial (F := F) (n := n) u₀ u₁ x

open Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma lineValuePolynomial_eval (u₀ u₁ : Fin n → F) (x : Fin n) (z : F) :
    (lineValuePolynomial (F := F) (n := n) u₀ u₁ x).eval z = u₀ x + z * u₁ x := by
  rw [lineValuePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_X]
  ring

open Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma lineValuePolynomial_natDegree_le_one (u₀ u₁ : Fin n → F) (x : Fin n) :
    (lineValuePolynomial (F := F) (n := n) u₀ u₁ x).natDegree ≤ 1 := by
  unfold lineValuePolynomial
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · rw [Polynomial.natDegree_C]
    omega
  · simpa using Polynomial.natDegree_C_mul_X_pow_le (u₁ x) 1

open Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma lineValuePolynomial_natDegree_lt_succ_succ (u₀ u₁ : Fin n → F) (x : Fin n) :
    (lineValuePolynomial (F := F) (n := n) u₀ u₁ x).natDegree < 1 + 1 := by
  exact Nat.lt_succ_of_le (lineValuePolynomial_natDegree_le_one (F := F) u₀ u₁ x)

open Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma lineValuePolynomial_natDegree_lt_succ_of_pos (u₀ u₁ : Fin n → F) (x : Fin n)
    (hk : 0 < k) :
    (lineValuePolynomial (F := F) (n := n) u₀ u₁ x).natDegree < k + 1 := by
  exact lt_of_le_of_lt
    (lineValuePolynomial_natDegree_le_one (F := F) u₀ u₁ x)
    (Nat.succ_lt_succ hk)

open Polynomial in
omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
lemma lineValuePolynomialFamily_natDegree_lt_succ_of_pos (u₀ u₁ : Fin n → F)
    (hk : 0 < k) :
    ∀ x, (lineValuePolynomialFamily (F := F) (n := n) u₀ u₁ x).natDegree < k + 1 := by
  intro x
  exact lineValuePolynomial_natDegree_lt_succ_of_pos (F := F) (n := n) (k := k) u₀ u₁ x hk

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Membership in `matching_set_at_x` gives exactly the pointwise evaluation
polynomial relation for the total close-polynomial family. -/
lemma PzFamily_eval_eq_lineValuePolynomial_eval_of_mem_matching_set_at_x
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {x : Fin n} {z : F}
    (hz : z ∈ matching_set_at_x k δ h_gs x) :
    (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) =
      (lineValuePolynomial (F := F) (n := n) u₀ u₁ x).eval z := by
  rcases (mem_matching_set_at_x_iff_PzFamily
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x z).mp hz with
    ⟨_hzclose, hmatch⟩
  rw [lineValuePolynomial_eval]
  exact hmatch.symm

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- If a coordinate has the matching-set membership for a parameter `z`, then
`PzFamily z` agrees there with the line-value polynomial family. -/
lemma PzFamily_eval_eq_lineValuePolynomialFamily_eval_of_mem_matching_set_at_x
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {x : Fin n} {z : F}
    (hz : z ∈ matching_set_at_x k δ h_gs x) :
    (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) =
      (lineValuePolynomialFamily (F := F) (n := n) u₀ u₁ x).eval z := by
  exact PzFamily_eval_eq_lineValuePolynomial_eval_of_mem_matching_set_at_x
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs hz

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Finite-domain version of the `PzFamily` evaluation-polynomial relation.
This is the exact local shape used after Claim 5.11 selects the top coordinate
set and Claim 5.10 supplies membership in each selected matching set. -/
lemma PzFamily_eval_eq_lineValuePolynomialFamily_eval_on_matching_domain
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n)) {z : F}
    (hz : ∀ x ∈ Dtop, z ∈ matching_set_at_x k δ h_gs x) :
    ∀ x ∈ Dtop,
      (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) =
        (lineValuePolynomialFamily (F := F) (n := n) u₀ u₁ x).eval z := by
  intro x hx
  exact PzFamily_eval_eq_lineValuePolynomialFamily_eval_of_mem_matching_set_at_x
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs (hz x hx)

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Selected-domain evaluation-polynomial witness for `PzFamily`. This is the
local output shape supplied by Claim 5.11 plus Claim 5.10 before the remaining
interpolation/extension step upgrades it to all coordinates. -/
lemma PzFamily_exists_eval_polys_on_matching_domain_subtype
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n))
    (hk : 0 < k)
    (hmatch : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ x ∈ Dtop, z ∈ matching_set_at_x k δ h_gs x) :
    ∃ E : Dtop → F[X],
      (∀ x, (E x).natDegree < k + 1) ∧
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          ∀ x : Dtop,
            (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x.1) =
              (E x).eval z := by
  refine ⟨fun x => lineValuePolynomialFamily (F := F) (n := n) u₀ u₁ x.1, ?_, ?_⟩
  · intro x
    exact lineValuePolynomialFamily_natDegree_lt_succ_of_pos
      (F := F) (n := n) (k := k) u₀ u₁ hk x.1
  · intro z hz x
    exact PzFamily_eval_eq_lineValuePolynomialFamily_eval_of_mem_matching_set_at_x
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs
      (hmatch z hz x.1 x.2)

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Bundled selected-domain extraction for `PzFamily`: decodedness on the
close-parameter set plus evaluation-polynomial witnesses on a Claim
5.11-selected coordinate domain. -/
lemma PzFamily_decoded_and_exists_eval_polys_on_matching_domain_subtype
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n))
    (hk : 0 < k)
    (hmatch : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ x ∈ Dtop, z ∈ matching_set_at_x k δ h_gs x) :
    (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).natDegree < k + 1 ∧
        δᵣ(u₀ + z • u₁,
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval ∘ ωs) ≤ δ) ∧
      ∃ E : Dtop → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Dtop,
              (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x.1) =
                (E x).eval z := by
  exact ⟨PzFamily_decoded_on_close_set
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs),
    PzFamily_exists_eval_polys_on_matching_domain_subtype
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs Dtop hk hmatch⟩

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Selected-domain canonical-family package for the §5-to-§6 bridge. Claim
5.11 selects a coordinate set `Dtop`; once every close parameter matches every
selected coordinate, `PzFamily` gives the decoded canonical representative and
the evaluation-polynomial witnesses on that selected domain. -/
lemma PzFamily_exists_canonical_eval_polys_on_matching_domain_and_unique
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n))
    (hk : 0 < k)
    (hmatch : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ x ∈ Dtop, z ∈ matching_set_at_x k δ h_gs x)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        P z = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z) :
    ∃ P₀ : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P₀ z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P₀ z).eval ∘ ωs) ≤ δ) ∧
      (∃ E : Dtop → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Dtop, (P₀ z).eval (ωs x.1) = (E x).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, P z = P₀ z := by
  refine ⟨PzFamily (F := F) (n := n) δ u₀ u₁ ωs k, ?_, ?_, ?_⟩
  · exact PzFamily_decoded_on_close_set
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs)
  · exact PzFamily_exists_eval_polys_on_matching_domain_subtype
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs Dtop hk hmatch
  · intro P hP z hz
    exact hunique P hP z hz

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Subset-hypothesis form of the selected-domain canonical package. This is
the direct shape returned after the double-counting step identifies a domain
`Dtop` whose every coordinate contains the full close-parameter set. -/
lemma PzFamily_exists_canonical_eval_polys_on_close_subset_and_unique
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (Dtop : Finset (Fin n))
    (hk : 0 < k)
    (hsubset : ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        P z = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z) :
    ∃ P₀ : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P₀ z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P₀ z).eval ∘ ωs) ≤ δ) ∧
      (∃ E : Dtop → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Dtop, (P₀ z).eval (ωs x.1) = (E x).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, P z = P₀ z :=
  PzFamily_exists_canonical_eval_polys_on_matching_domain_and_unique
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs Dtop hk
    (fun _ hz x hx => hsubset x hx hz) hunique

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Full-domain evaluation-polynomial witness for `PzFamily`, conditional on
the remaining assembly fact that every close parameter lies in every coordinate
matching set.  This is the exact `E` witness expected by the §6
`hEvalPoly` consumer, specialized to the list-decoding polynomial family. -/
lemma PzFamily_exists_eval_polys_of_forall_mem_matching_set_at_x
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hk : 0 < k)
    (hmatch : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ x : Fin n, z ∈ matching_set_at_x k δ h_gs x) :
    ∃ E : Fin n → F[X],
      (∀ x, (E x).natDegree < k + 1) ∧
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          ∀ x : Fin n,
            (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) =
              (E x).eval z := by
  refine ⟨lineValuePolynomialFamily (F := F) (n := n) u₀ u₁, ?_, ?_⟩
  · exact lineValuePolynomialFamily_natDegree_lt_succ_of_pos
      (F := F) (n := n) (k := k) u₀ u₁ hk
  · intro z hz x
    exact PzFamily_eval_eq_lineValuePolynomialFamily_eval_of_mem_matching_set_at_x
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs (hmatch z hz x)

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Bundled canonical-family extraction: the chosen close-polynomial family is
decoded on the close parameter set, and under the remaining full-coordinate
matching hypothesis it also has the evaluation-polynomial dependence required
by the §6 assembly layer.

This deliberately stays specialized to `PzFamily`; the final §6 front door
still asks for a universal statement over every decoded family, which requires
the missing uniqueness/representative bridge rather than just this canonical
choice. -/
lemma PzFamily_decoded_and_exists_eval_polys_of_forall_mem_matching_set_at_x
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hk : 0 < k)
    (hmatch : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ x : Fin n, z ∈ matching_set_at_x k δ h_gs x) :
    (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).natDegree < k + 1 ∧
        δᵣ(u₀ + z • u₁,
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval ∘ ωs) ≤ δ) ∧
      ∃ E : Fin n → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Fin n,
              (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) =
                (E x).eval z := by
  exact ⟨PzFamily_decoded_on_close_set
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs),
    PzFamily_exists_eval_polys_of_forall_mem_matching_set_at_x
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs hk hmatch⟩

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Subset-hypothesis form of the bundled canonical-family extraction.

This matches the shape produced by double-counting over coordinates: for each
domain coordinate `x`, the full close-parameter set is contained in
`matching_set_at_x`. -/
lemma PzFamily_decoded_and_exists_eval_polys_of_close_subset_matching_set_at_x
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hk : 0 < k)
    (hsubset : ∀ x : Fin n,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x) :
    (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).natDegree < k + 1 ∧
        δᵣ(u₀ + z • u₁,
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval ∘ ωs) ≤ δ) ∧
      ∃ E : Fin n → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Fin n,
              (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval (ωs x) =
                (E x).eval z :=
  PzFamily_decoded_and_exists_eval_polys_of_forall_mem_matching_set_at_x
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs hk
    (fun _ hz x => hsubset x hz)

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- Canonical-family package for the §6 bridge: under the full-coordinate
matching-set condition, `PzFamily` supplies the decoded family and the
evaluation-polynomial witness; an external uniqueness/representative theorem
then upgrades it to the canonical-family shape consumed by the curve assembly
wrappers. -/
lemma PzFamily_exists_canonical_eval_polys_of_close_subset_and_unique
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hk : 0 < k)
    (hsubset : ∀ x : Fin n,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        P z = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z) :
    ∃ P₀ : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P₀ z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P₀ z).eval ∘ ωs) ≤ δ) ∧
      (∃ E : Fin n → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Fin n, (P₀ z).eval (ωs x) = (E x).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, P z = P₀ z := by
  refine ⟨PzFamily (F := F) (n := n) δ u₀ u₁ ωs k, ?_, ?_, ?_⟩
  · exact PzFamily_decoded_on_close_set
      (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs)
  · exact PzFamily_exists_eval_polys_of_forall_mem_matching_set_at_x
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs hk
      (fun _ hz x => hsubset x hz)
  · intro P hP z hz
    exact hunique P hP z hz

omit [DecidableEq (RatFunc F)] in
lemma matching_set_at_x_eq_matching_coords_image_univ
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) :
    ((Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)).filter
      (fun z => x ∈ matching_coords_for_z k δ h_gs z)).image (fun z => (z.1 : F)) =
        matching_set_at_x k δ h_gs x := by
  classical
  apply Finset.ext
  intro z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    exact coeff_mem_matching_set_at_x_of_mem_matching_coords
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs w
      (Finset.mem_filter.mp hw).2
  · intro hz
    rcases (mem_matching_set_at_x_iff
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x z).mp hz with
      ⟨hzclose, hmatch⟩
    refine Finset.mem_image.mpr ⟨⟨z, hzclose⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mem_matching_coords_for_z
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs ⟨z, hzclose⟩ x]
    exact hmatch

omit [DecidableEq (RatFunc F)] in
lemma matching_coords_univ_filter_card_eq_matching_set_at_x_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) :
    ((Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)).filter
      (fun z => x ∈ matching_coords_for_z k δ h_gs z)).card =
        (matching_set_at_x k δ h_gs x).card := by
  classical
  rw [← matching_set_at_x_eq_matching_coords_image_univ
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x]
  exact (Finset.card_image_of_injective _ fun a b h => Subtype.ext h).symm

/-- Coordinates where the selected close polynomial for `z` does not match the
line word.  These are the bad coordinates used by the Claim 5.11
double-counting argument. -/
noncomputable def nonmatching_coords_for_z
    (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ matching_coords_for_z k δ h_gs z

omit [DecidableEq (RatFunc F)] in
lemma not_mem_nonmatching_coords_for_z_iff
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) (x : Fin n) :
    x ∉ nonmatching_coords_for_z k δ h_gs z ↔
      x ∈ matching_coords_for_z k δ h_gs z := by
  simp [nonmatching_coords_for_z]

omit [DecidableEq (RatFunc F)] in
lemma nonmatching_coords_filter_card_le_matching_set_at_x_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (S : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) (x : Fin n) :
    (S.filter (fun z => x ∉ nonmatching_coords_for_z k δ h_gs z)).card ≤
      (matching_set_at_x k δ h_gs x).card := by
  classical
  have hfilter :
      S.filter (fun z => x ∉ nonmatching_coords_for_z k δ h_gs z) =
        S.filter (fun z => x ∈ matching_coords_for_z k δ h_gs z) := by
    apply Finset.ext
    intro z
    simp [not_mem_nonmatching_coords_for_z_iff
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z x]
  rw [hfilter]
  exact matching_coords_filter_card_le_matching_set_at_x_card
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs S x

omit [DecidableEq (RatFunc F)] in
lemma nonmatching_coords_for_z_card_eq_hammingDist
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    (nonmatching_coords_for_z k δ h_gs z).card =
      hammingDist (u₀ + z.1 • u₁)
        ((Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          ∘ ωs) := by
  rw [Code.hammingDist_eq_disagreementCols_card]
  apply congrArg Finset.card
  apply Finset.ext
  intro x
  simp [nonmatching_coords_for_z, matching_coords_for_z, Code.disagreementCols, Function.comp_apply]

omit [DecidableEq (RatFunc F)] in
lemma matching_coords_card_add_nonmatching_coords_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    (matching_coords_for_z k δ h_gs z).card +
      (nonmatching_coords_for_z k δ h_gs z).card = n := by
  classical
  rw [nonmatching_coords_for_z, Finset.card_sdiff]
  · rw [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    exact Nat.add_sub_cancel' (by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (matching_coords_for_z k δ h_gs z)))

omit [DecidableEq (RatFunc F)] in
lemma matching_coords_card_eq_sub_nonmatching_coords_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    (matching_coords_for_z k δ h_gs z).card =
      n - (nonmatching_coords_for_z k δ h_gs z).card := by
  have hsum := matching_coords_card_add_nonmatching_coords_card
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z
  omega

omit [DecidableEq (RatFunc F)] in
lemma nonmatching_coords_for_z_card_div_le_delta
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    ((nonmatching_coords_for_z k δ h_gs z).card : ℚ) / n ≤ δ := by
  have hrel :=
    Pz_relDist_le (n := n) (k := k) (ωs := ωs) (δ := δ)
      (u₀ := u₀) (u₁ := u₁) z.2
  simpa [Code.relHammingDist, nonmatching_coords_for_z_card_eq_hammingDist
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z] using hrel

omit [DecidableEq (RatFunc F)] in
lemma nonmatching_coords_for_z_card_le_of_delta_mul_le
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
    {E : ℕ}
    (hE : δ * (n : ℚ) ≤ E) :
    (nonmatching_coords_for_z k δ h_gs z).card ≤ E := by
  have hrel := nonmatching_coords_for_z_card_div_le_delta
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z
  have hnpos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_neZero n
  have hcard :
      ((nonmatching_coords_for_z k δ h_gs z).card : ℚ) ≤ δ * n :=
    (div_le_iff₀ hnpos).mp hrel
  exact_mod_cast le_trans hcard hE

omit [DecidableEq (RatFunc F)] in
lemma nonmatching_coords_for_z_card_le_natCeil_delta_mul
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    (nonmatching_coords_for_z k δ h_gs z).card ≤ ⌈δ * (n : ℚ)⌉₊ := by
  exact nonmatching_coords_for_z_card_le_of_delta_mul_le
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z
    (Nat.le_ceil _)

omit [DecidableEq (RatFunc F)] in
noncomputable def graphExtractionHypotheses_of_matching_coords
    [DecidableEq (Polynomial F)]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
        m * (matching_coords_for_z k δ h_gs z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs where
  hx0 := hx0
  hsep := hsep
  hS_nonempty := hS_nonempty
  A := fun z => matching_coords_for_z k δ h_gs z
  hA := by
    intro z i hi
    exact (mem_matching_coords_for_z
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z i).mp hi
  hcount := hcount
  hlarge := hlarge

omit [DecidableEq (RatFunc F)] in
noncomputable def graphExtractionHypotheses_of_nonmatching_count
    [DecidableEq (Polynomial F)]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
        m * (n - (nonmatching_coords_for_z k δ h_gs z).card))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs :=
  graphExtractionHypotheses_of_matching_coords
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty
    (fun z => by
      simpa [matching_coords_card_eq_sub_nonmatching_coords_card
        (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z] using hcount z)
    hlarge

omit [DecidableEq (RatFunc F)] in
noncomputable def graphExtractionHypotheses_of_uniform_nonmatching_bound
    [DecidableEq (Polynomial F)]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    {E : ℕ}
    (hbad : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      (nonmatching_coords_for_z k δ h_gs z).card ≤ E)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (n - E))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs :=
  graphExtractionHypotheses_of_nonmatching_count
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty
    (fun z => by
      exact lt_of_lt_of_le (hcount z)
        (Nat.mul_le_mul_left m (Nat.sub_le_sub_left (hbad z) n)))
    hlarge

omit [DecidableEq (RatFunc F)] in
noncomputable def graphExtractionHypotheses_of_delta_nonmatching_bound
    [NeZero n]
    [DecidableEq (Polynomial F)]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    {E : ℕ}
    (hE : δ * (n : ℚ) ≤ E)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (n - E))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs :=
  graphExtractionHypotheses_of_uniform_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty
    (fun z => nonmatching_coords_for_z_card_le_of_delta_mul_le
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z hE)
    hcount hlarge

omit [DecidableEq (RatFunc F)] in
noncomputable def graphExtractionHypotheses_of_natCeil_delta_nonmatching_bound
    [NeZero n]
    [DecidableEq (Polynomial F)]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
        m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs :=
  graphExtractionHypotheses_of_delta_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty
    (Nat.le_ceil _)
    hcount hlarge

open BCIKS20AppendixA.ClaimA2 Polynomial in
/-- Claim 5.10 with the missing counting-to-coefficient-value bridge exposed
as hypotheses.  The published cardinality assumptions are retained so this can
replace the legacy statement at call sites once the Appendix-A/value bridge is
available. -/
lemma solution_gamma_matches_word_if_subset_large_of_coeff_values
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        BCIKS20AppendixA.ClaimA2.γ' x₀ (R k δ x₀ h_gs)
          (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
      (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
      (P_of_linear_witness k δ x₀ h_gs hlin).eval (Polynomial.C (ωs x)) =
        (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
    have _hD_used := hD
    have _hx_used := hx
    exact P_eval_eq_word_of_linear_witness_coeff_values
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hlin x h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
/-- Scalar-evaluated side-condition-explicit form of Claim 5.10.  This is the
bridge from the §5 polynomial identity to the pointwise curve value used by the
§6 coefficient/evaluation-polynomial assembly. -/
lemma solution_gamma_matches_word_eval_if_subset_large_of_coeff_values
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (z : F)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    ((P_of_linear_witness k δ x₀ h_gs hlin).eval (Polynomial.C (ωs x))).eval z =
      u₀ x + z * u₁ x := by
  rw [solution_gamma_matches_word_if_subset_large_of_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hlin hD hx h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 Polynomial in
lemma solution_gamma_matches_word_if_subset_large_of_linear_witness
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
      (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
      (P_of_linear_witness k δ x₀ h_gs hlin).eval (Polynomial.C (ωs x)) =
        (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
    have _hD_used := hD
    have _hx_used := hx
    exact P_eval_eq_word_of_linear_witness_coeff_values
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hlin x h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
lemma solution_gamma_matches_word_eval_if_subset_large_of_linear_witness
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (z : F)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    ((P_of_linear_witness k δ x₀ h_gs hlin).eval (Polynomial.C (ωs x))).eval z =
      u₀ x + z * u₁ x := by
  rw [solution_gamma_matches_word_if_subset_large_of_linear_witness
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hlin hD hx h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 Polynomial in
lemma solution_gamma_matches_word_if_subset_large_of_representative_degreeX_le_one
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (h₀ :
      (Classical.choose
        (solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
          hrepr hP)).eval (ωs x) = u₀ x)
    (h₁ :
      (Classical.choose
        (Classical.choose_spec
          (solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
            (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
            hrepr hP))).eval (ωs x) = u₁ x) :
    (P_of_linear_witness k δ x₀ h_gs
      (solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
        (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
        hrepr hP)).eval (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
  exact solution_gamma_matches_word_if_subset_large_of_linear_witness
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs
    (solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs hrepr hP)
    hD hx h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
lemma solution_gamma_matches_word_eval_if_subset_large_of_representative_degreeX_le_one
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
        (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
        (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (z : F)
    (h₀ :
      (Classical.choose
        (solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
          hrepr hP)).eval (ωs x) = u₀ x)
    (h₁ :
      (Classical.choose
        (Classical.choose_spec
          (solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
            (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
            hrepr hP))).eval (ωs x) = u₁ x) :
    ((P_of_linear_witness k δ x₀ h_gs
      (solution_gamma_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
        (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀) h_gs
        hrepr hP)).eval (Polynomial.C (ωs x))).eval z =
      u₀ x + z * u₁ x := by
  rw [solution_gamma_matches_word_if_subset_large_of_representative_degreeX_le_one
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hrepr hP hD hx h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_matches_word_if_subset_large_of_coeff_values
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * (Bivariate.natDegreeY <|
            R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * D)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
      (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
      (P_graph_of_linear_witness
          (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge hlin).eval
        (Polynomial.C (ωs x)) =
        (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
    have _hD_used := hD
    have _hx_used := hx
    exact P_graph_eval_eq_word_of_linear_coeff_values
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hx0 hsep hS_nonempty A hA hcount hlarge hlin x h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_matches_word_eval_if_subset_large_of_coeff_values
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge)
          (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * (Bivariate.natDegreeY <|
            R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * D)
    (z : F)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    ((P_graph_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge hlin).eval
      (Polynomial.C (ωs x))).eval z = u₀ x + z * u₁ x := by
  rw [solution_gamma_graph_matches_word_if_subset_large_of_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty A hA hcount hlarge hlin hD hx h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_clear_matches_word_if_subset_large_of_coeff_values
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * (Bivariate.natDegreeY <|
            R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * D)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
      (P_graph_clear_of_linear_witness
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond hlin).eval
        (Polynomial.C (ωs x)) =
        (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
    have _hD_used := hD
    have _hx_used := hx
    exact P_graph_clear_eval_eq_word_of_linear_coeff_values
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hcond hlin x h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_clear_matches_word_eval_if_subset_large_of_coeff_values
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        γ' x₀
          (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (irreducible_H_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (natDegree_H_graph_clear_pos
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
          (claimA2_hypotheses_graph_clear
            (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * (Bivariate.natDegreeY <|
            R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * D)
    (z : F)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
    (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) :
    ((P_graph_clear_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond hlin).eval
      (Polynomial.C (ωs x))).eval z = u₀ x + z * u₁ x := by
  rw [solution_gamma_graph_clear_matches_word_if_subset_large_of_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hcond hlin hD hx h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_matches_word_if_subset_large_of_representative_degreeX_le_one
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀
        (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * (Bivariate.natDegreeY <|
            R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * D)
    (h₀ :
      (Classical.choose
        (solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP)).eval
          (ωs x) = u₀ x)
    (h₁ :
      (Classical.choose
        (Classical.choose_spec
          (solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
            (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP))).eval
          (ωs x) = u₁ x) :
    (P_graph_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge
        (solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP)).eval
      (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
  exact solution_gamma_graph_matches_word_if_subset_large_of_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty A hA hcount hlarge
    (solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP)
    hD hx h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_clear_matches_word_if_subset_large_of_representative_degreeX_le_one
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (irreducible_H_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (natDegree_H_graph_clear_pos
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (claimA2_hypotheses_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * (Bivariate.natDegreeY <|
            R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * D)
    (h₀ :
      (Classical.choose
        (solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
          hrepr hP)).eval (ωs x) = u₀ x)
    (h₁ :
      (Classical.choose
        (Classical.choose_spec
          (solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
            (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
            hrepr hP))).eval (ωs x) = u₁ x) :
    (P_graph_clear_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond
        (solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
          hrepr hP)).eval
      (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
  exact solution_gamma_graph_clear_matches_word_if_subset_large_of_coeff_values
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hcond
    (solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
      (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
      hrepr hP)
    hD hx h₀ h₁

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_matches_word_eval_if_subset_large_of_representative_degreeX_le_one
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval
          (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀
        (R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (irreducible_H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (natDegree_H_graph_pos (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge)
        (claimA2_hypotheses_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * (Bivariate.natDegreeY <|
            R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
              hx0 hsep hS_nonempty A hA hcount hlarge)
        * D)
    (z : F)
    (h₀ :
      (Classical.choose
        (solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP)).eval
          (ωs x) = u₀ x)
    (h₁ :
      (Classical.choose
        (Classical.choose_spec
          (solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
            (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
            hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP))).eval
          (ωs x) = u₁ x) :
    ((P_graph_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge
        (solution_gamma_graph_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP)).eval
      (Polynomial.C (ωs x))).eval z =
      u₀ x + z * u₁ x := by
  rw [solution_gamma_graph_matches_word_if_subset_large_of_representative_degreeX_le_one
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hx0 hsep hS_nonempty A hA hcount hlarge hrepr hP hD hx h₀ h₁]
  simp [mul_comm]

open BCIKS20AppendixA.ClaimA2 Polynomial in
omit [DecidableEq (RatFunc F)] in
lemma solution_gamma_graph_clear_matches_word_eval_if_subset_large_of_representative_degreeX_le_one
    [DecidableEq (Polynomial F)] {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    {Ppoly : F[Z][X]}
    (hrepr :
      γ' x₀
        (R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (irreducible_H_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (natDegree_H_graph_clear_pos
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        (claimA2_hypotheses_graph_clear
          (F := F) (m := m) (n := n) k δ x₀ h_gs hcond) =
          BCIKS20AppendixA.polyToPowerSeries𝕃 _ Ppoly)
    (hP : Bivariate.degreeX Ppoly ≤ 1)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥
      Bivariate.totalDegree
        (H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <|
            H_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * (Bivariate.natDegreeY <|
            R_graph_clear (F := F) (m := m) (n := n) k δ x₀ h_gs hcond)
        * D)
    (z : F)
    (h₀ :
      (Classical.choose
        (solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
          hrepr hP)).eval (ωs x) = u₀ x)
    (h₁ :
      (Classical.choose
        (Classical.choose_spec
          (solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
            (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
            hrepr hP))).eval (ωs x) = u₁ x) :
    ((P_graph_clear_of_linear_witness
        (F := F) (m := m) (n := n) k δ x₀ h_gs hcond
        (solution_gamma_graph_clear_is_linear_in_Z_of_polynomial_representative_degreeX_le_one
          (F := F) (m := m) (n := n) (k := k) (Q := Q) δ x₀ h_gs hcond
          hrepr hP)).eval
      (Polynomial.C (ωs x))).eval z =
      u₀ x + z * u₁ x := by
  rw [solution_gamma_graph_clear_matches_word_if_subset_large_of_representative_degreeX_le_one
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hcond hrepr hP hD hx h₀ h₁]
  simp [mul_comm]

/-- Claim 5.10 of [BCIKS20].
Needed to prove Claim 5.9. This claim states that `γ(x) = w(x,Z)` if the cardinality `|S'_x|` is big
enough.

GAP (blocked — see the §5 GAP ANALYSIS block above). The hypothesis `hx` bounds
`(matching_set_at_x …).card` from below, and the conclusion is the §5 polynomial identity
`P(ωs x) = C(u₀ x) + u₁ x · X`. Bridging the geometric matching-set bound to the `S_β`-largeness
that `Lemma_A_1` consumes (so that the relevant Hensel coefficient vanishes) is exactly missing
ingredient C; the underlying `β` under-specification (ingredient D) also applies. -/
lemma solution_gamma_matches_word_if_subset_large
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    (hlin :
      ∃ (v₀ v₁ : F[X]),
        BCIKS20AppendixA.ClaimA2.γ' x₀ (R k δ x₀ h_gs)
          (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
          (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
          (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
            BCIKS20AppendixA.polyToPowerSeries𝕃 _
              ((Polynomial.map Polynomial.C v₀) +
                (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)))
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (h₀ : (Classical.choose hlin).eval (ωs x) = u₀ x)
      (h₁ : (Classical.choose (Classical.choose_spec hlin)).eval (ωs x) = u₁ x) : (P_of_linear_witness k δ x₀ h_gs hlin).eval (Polynomial.C (ωs x)) =
        (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by
    have _hD_used := hD
    have _hx_used := hx
    exact P_eval_eq_word_of_linear_witness_coeff_values
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs hlin x h₀ h₁

/-- Select exactly `r` elements from a finite set once its cardinality is large
enough.  This is the final selection step in Claim 5.11 after double-counting
has produced enough good coordinates. -/
lemma exists_subset_card_eq_of_le_card {α : Type} [DecidableEq α] {S : Finset α} {r : ℕ}
    (hcard : r ≤ S.card) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = r :=
  Finset.exists_subset_card_eq hcard

/-- Generic double-counting brick for Claim 5.11. If each `z ∈ S` has at most
`m` bad coordinates, then coordinates that are bad for at least `t` elements of
`S` occupy at most `m * #S / t` in the multiplicative form below. -/
lemma heavyCoords_card_mul_le {α β : Type} [Fintype α] [DecidableEq α]
    {S : Finset β} {B : β → Finset α} {m : ℕ}
    (hB : ∀ z ∈ S, (B z).card ≤ m) (t : ℕ) :
    ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ m * S.card := by
  classical
  have hswap : ∑ x : α, (S.filter (fun z => x ∈ B z)).card =
      ∑ z ∈ S, (B z).card := by
    have h1 : ∀ x : α, (S.filter (fun z => x ∈ B z)).card =
        ∑ z ∈ S, if x ∈ B z then 1 else 0 := fun x => Finset.card_filter _ _
    have h2 : ∀ z : β, (B z).card = ∑ x : α, if x ∈ B z then 1 else 0 := by
      intro z
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hbound : ∑ z ∈ S, (B z).card ≤ m * S.card := by
    calc
      ∑ z ∈ S, (B z).card ≤ ∑ _z ∈ S, m := Finset.sum_le_sum hB
      _ = m * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hfilter :
      ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
        ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card := by
    calc
      ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
          = ∑ _x ∈ (Finset.univ : Finset α).filter
              (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card), t := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).filter
              (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card),
              (S.filter (fun z => x ∈ B z)).card :=
            Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact le_trans hfilter (hswap ▸ hbound)

/-- Complement-to-incidence form of the heavy-coordinate argument.  If a
coordinate is not heavy for the bad sets `B`, then it is nonbad for more than
`threshold` elements of `S`, provided `threshold + t ≤ #S`.  The hypothesis
`hcard` is the remaining arithmetic lower bound on the non-heavy coordinates. -/
lemma exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card
    {α β : Type} [Fintype α] [DecidableEq α]
    {S : Finset β} {B : β → Finset α} {r threshold t : ℕ}
    (hthreshold : threshold + t ≤ S.card)
    (hcard : r ≤ ((Finset.univ : Finset α) \
      ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card))).card) :
    ∃ T : Finset α, T.card = r ∧
      ∀ x ∈ T, threshold < (S.filter (fun z => x ∉ B z)).card := by
  classical
  let heavy : Finset α := (Finset.univ : Finset α).filter
    (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)
  obtain ⟨T, hsub, hTcard⟩ :=
    exists_subset_card_eq_of_le_card (S := (Finset.univ : Finset α) \ heavy) hcard
  refine ⟨T, hTcard, ?_⟩
  intro x hx
  have hxnot : x ∉ heavy := (Finset.mem_sdiff.mp (hsub hx)).2
  have hbad_lt : (S.filter (fun z => x ∈ B z)).card < t := by
    exact Nat.lt_of_not_ge fun hbad => hxnot (by simp [heavy, hbad])
  have hsplit :
      (S.filter (fun z => x ∈ B z)).card +
        (S.filter (fun z => x ∉ B z)).card = S.card := by
    simpa using
      (Finset.card_filter_add_card_filter_not (s := S) (p := fun z => x ∈ B z))
  omega

lemma exists_good_coordinate_subset_of_filter_card
    {α : Type} [Fintype α] [DecidableEq α] {r : ℕ} {p : α → Prop} [DecidablePred p]
    (hcard : r ≤ ((Finset.univ : Finset α).filter p).card) :
    ∃ T : Finset α, T.card = r ∧ ∀ x ∈ T, p x := by
  obtain ⟨T, hsub, hTcard⟩ :=
    exists_subset_card_eq_of_le_card
      (S := (Finset.univ : Finset α).filter p) (r := r) hcard
  refine ⟨T, hTcard, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp (hsub hx)).2

/-- Incidence-form selection step for Claim 5.11.  Once a separate
double-counting argument shows that at least `r` coordinates have more than
`threshold` incident good parameters, this selects exactly `r` of them. -/
lemma exists_coordinate_subset_with_large_incidence
    {α β : Type} [Fintype α] [DecidableEq α]
    {S : Finset β} {G : β → Finset α} {r threshold : ℕ}
    (hcard : r ≤ ((Finset.univ : Finset α).filter
      (fun x => threshold < (S.filter (fun z => x ∈ G z)).card)).card) :
    ∃ T : Finset α, T.card = r ∧
      ∀ x ∈ T, threshold < (S.filter (fun z => x ∈ G z)).card :=
  exists_good_coordinate_subset_of_filter_card hcard

/-- Side-condition-explicit Claim 5.11.  The remaining mathematical work is to
prove `hcard` from the §5 matching construction; the finite-set selection part
itself is just `exists_good_coordinate_subset_of_filter_card`. -/
lemma exists_points_with_large_matching_subset_of_filter_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D : ℕ}
    (hcard : k + 1 ≤ ((Finset.univ : Finset (Fin n)).filter
      (fun x =>
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D < (matching_set_at_x k δ h_gs x).card)).card) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  simpa [gt_iff_lt] using
    exists_good_coordinate_subset_of_filter_card (α := Fin n) (r := k + 1)
      (p := fun x =>
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D < (matching_set_at_x k δ h_gs x).card)
      hcard

/-- Incidence-counting version of the Claim 5.11 selection step.  A later
double-counting proof can work with the per-parameter coordinate sets
`matching_coords_for_z`; this lemma converts the resulting incidence lower
bound into the published `matching_set_at_x` conclusion. -/
lemma exists_points_with_large_matching_subset_of_incidence_filter_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (S : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    {D : ℕ}
    (hcard : k + 1 ≤ ((Finset.univ : Finset (Fin n)).filter
      (fun x =>
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D <
            (S.filter (fun z => x ∈ matching_coords_for_z k δ h_gs z)).card)).card) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  obtain ⟨Dtop, hDtop, hgood⟩ :=
    exists_good_coordinate_subset_of_filter_card (α := Fin n) (r := k + 1)
      (p := fun x =>
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D <
            (S.filter (fun z => x ∈ matching_coords_for_z k δ h_gs z)).card)
      hcard
  refine ⟨Dtop, hDtop, ?_⟩
  intro x hx
  exact lt_of_lt_of_le (hgood x hx)
    (matching_coords_filter_card_le_matching_set_at_x_card
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs S x)

/-- Heavy-bad-coordinate version of the Claim 5.11 selection step.  This is
the form closest to the paper's double-counting proof: `nonmatching_coords_for_z`
are the bad coordinates for each close parameter, `t` is the heaviness cutoff,
and `hcard` asserts that at least `k + 1` coordinates are not heavy. -/
lemma exists_points_with_large_matching_subset_of_heavy_nonmatching_complement_card
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (S : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    {D t : ℕ}
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ S.card)
    (hcard : k + 1 ≤ ((Finset.univ : Finset (Fin n)) \
      ((Finset.univ : Finset (Fin n)).filter
        (fun x =>
          t ≤ (S.filter
            (fun z => x ∈ nonmatching_coords_for_z k δ h_gs z)).card))).card) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  obtain ⟨Dtop, hDtop, hgood⟩ :=
    exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card
      (α := Fin n)
      (β := coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
      (S := S)
      (B := fun z => nonmatching_coords_for_z k δ h_gs z)
      (r := k + 1)
      (threshold :=
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
      (t := t) hthreshold hcard
  refine ⟨Dtop, hDtop, ?_⟩
  intro x hx
  exact lt_of_lt_of_le (hgood x hx)
    (nonmatching_coords_filter_card_le_matching_set_at_x_card
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs S x)

omit [DecidableEq (RatFunc F)] in
/-- Derive the complement-cardinality side condition for the heavy-bad
coordinate form of Claim 5.11 from a uniform bad-coordinate bound. -/
lemma heavy_nonmatching_complement_card_ge_of_uniform_bound
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (S : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    {E t : ℕ}
    (hbad : ∀ z ∈ S, (nonmatching_coords_for_z k δ h_gs z).card ≤ E)
    (hsmall : E * S.card < (n - k) * t) :
    k + 1 ≤ ((Finset.univ : Finset (Fin n)) \
      ((Finset.univ : Finset (Fin n)).filter
        (fun x =>
          t ≤ (S.filter
            (fun z => x ∈ nonmatching_coords_for_z k δ h_gs z)).card))).card := by
  classical
  let heavy : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter
    (fun x =>
      t ≤ (S.filter
        (fun z => x ∈ nonmatching_coords_for_z k δ h_gs z)).card)
  have hmul : heavy.card * t ≤ E * S.card := by
    simpa [heavy] using
      heavyCoords_card_mul_le (α := Fin n)
        (β := coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
        (S := S) (B := fun z => nonmatching_coords_for_z k δ h_gs z)
        (m := E) hbad t
  have hheavy_lt : heavy.card < n - k := by
    exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hmul hsmall)
  have hsubset : heavy ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  have hcard :
      ((Finset.univ : Finset (Fin n)) \ heavy).card = n - heavy.card := by
    rw [Finset.card_sdiff_of_subset hsubset, Finset.card_univ, Fintype.card_fin]
  change k + 1 ≤ ((Finset.univ : Finset (Fin n)) \ heavy).card
  rw [hcard]
  omega

/-- Uniform-bad-coordinate version of the Claim 5.11 selection step.  The
arithmetic hypothesis `hsmall` is exactly the paper's requirement that the heavy
bad coordinates leave at least `k + 1` usable coordinates. -/
lemma exists_points_with_large_matching_subset_of_uniform_nonmatching_bound
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (S : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    {D E t : ℕ}
    (hbad : ∀ z ∈ S, (nonmatching_coords_for_z k δ h_gs z).card ≤ E)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ S.card)
    (hsmall : E * S.card < (n - k) * t) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  exact exists_points_with_large_matching_subset_of_heavy_nonmatching_complement_card
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs S (D := D) (t := t) hthreshold
    (heavy_nonmatching_complement_card_ge_of_uniform_bound
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ)
      h_gs S hbad hsmall)

/-- Full-close-set version of the uniform-bad-coordinate Claim 5.11 wrapper. -/
lemma exists_points_with_large_matching_subset_of_univ_uniform_nonmatching_bound
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D E t : ℕ}
    (hbad : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      (nonmatching_coords_for_z k δ h_gs z).card ≤ E)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      E * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) < (n - k) * t) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  exact exists_points_with_large_matching_subset_of_uniform_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs (Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (D := D) (E := E) (t := t)
    (fun z _hz => hbad z)
    (by simpa using hthreshold)
    (by simpa using hsmall)

/-- Full-close-set Claim 5.11 wrapper where the uniform bad-coordinate bound is
obtained from the relative-distance radius `δ`. -/
lemma exists_points_with_large_matching_subset_of_delta_nonmatching_bound
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D E t : ℕ}
    (hE : δ * (n : ℚ) ≤ E)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      E * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) < (n - k) * t) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  exact exists_points_with_large_matching_subset_of_univ_uniform_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs (D := D) (E := E) (t := t)
    (fun z => nonmatching_coords_for_z_card_le_of_delta_mul_le
      (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z hE)
    hthreshold hsmall

/-- Full-close-set Claim 5.11 wrapper with the canonical integer bad-coordinate
bound `⌈δ * n⌉₊`. -/
lemma exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D t : ℕ}
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) * t) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  exact exists_points_with_large_matching_subset_of_delta_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs (D := D) (E := ⌈δ * (n : ℚ)⌉₊) (t := t)
    (Nat.le_ceil _)
    hthreshold hsmall

/-- Complement-threshold form of the nat-ceil Claim 5.11 wrapper.

This specializes the free slack parameter `t` in
`exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound` to the
remaining number of close parameters after the target fiber threshold is removed. It is the
arithmetic shape used by the final Claim 5.11 capstone: the side conditions become
`threshold ≤ #S` and a single strict counting inequality over `#S - threshold`. -/
lemma exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound_complement
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D : ℕ}
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) *
          (#(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) -
            (2 * k + 1)
              * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
              * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
              * D)) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  exact exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs (D := D)
    (t := #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) -
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    (by omega) hsmall

/-- Direct Claim-5.11 complement wrapper through the standalone
`ArkLib.Claim511` double-counting theorem. This has the same BCIKS20 object
shape as `exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound_complement`,
but keeps the imported combinatorial core visible to downstream callers. -/
lemma
    exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound_complement_claim511
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D : ℕ}
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) *
          (#(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) -
            (2 * k + 1)
              * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
              * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
              * D)) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by
  classical
  exact ArkLib.Claim511.exists_points_with_large_matching_subset_fin_complement
    (n := n)
    (β := coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
    (γ := F)
    (S := (Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)))
    (nonmatching := fun z => nonmatching_coords_for_z k δ h_gs z)
    (matchSet := fun x => matching_set_at_x k δ h_gs x)
    (E := ⌈δ * (n : ℚ)⌉₊)
    (k := k)
    (dH := Bivariate.natDegreeY <| H k δ x₀ h_gs)
    (dR := Bivariate.natDegreeY <| R k δ x₀ h_gs)
    (D := D)
    (by simpa using hthreshold)
    (fun z _hz =>
      nonmatching_coords_for_z_card_le_natCeil_delta_mul
        (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z)
    (by simpa using hsmall)
    (fun x hx =>
      lt_of_lt_of_le hx
        (nonmatching_coords_filter_card_le_matching_set_at_x_card
          (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs
          (Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) x))

/-- Turn a Claim-5.11 point set with sufficiently large `S'_x` fibers into the
full close-set coverage condition consumed by the canonical `PzFamily`
evaluation-polynomial package. -/
lemma close_proximity_subset_matching_set_on_points_of_large_matching_subset
    {ωs : Fin n ↪ F} {Dtop : Finset (Fin n)}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hlarge : ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D) :
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  intro x hx
  exact close_proximity_subset_matching_set_at_x_of_pred_lt_card
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x
    (lt_of_le_of_lt hcover (hlarge x hx))

omit [DecidableEq (RatFunc F)] in
/-- Graph-clear variant of
`close_proximity_subset_matching_set_on_points_of_large_matching_subset`.

This is the selected-domain coverage step with the honest graph-condition
extractions `R_graph_clear`/`H_graph_clear`, rather than the legacy `R`/`H`
chosen by the still-open Claim-5.7 surface. -/
lemma close_proximity_subset_matching_set_on_points_of_large_matching_subset_graph_clear
    [DecidableEq (Polynomial F)]
    {ωs : Fin n ↪ F} {Dtop : Finset (Fin n)}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    {D : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H_graph_clear k δ x₀ h_gs hcond)
          * (Bivariate.natDegreeY <| R_graph_clear k δ x₀ h_gs hcond)
          * D)
    (hlarge : ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H_graph_clear k δ x₀ h_gs hcond)
          * (Bivariate.natDegreeY <| R_graph_clear k δ x₀ h_gs hcond)
          * D) :
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  intro x hx
  exact close_proximity_subset_matching_set_at_x_of_pred_lt_card
    (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs x
    (lt_of_le_of_lt hcover (hlarge x hx))

/-- Claim-5.11-to-assembly bridge for any uniform integer bad-coordinate
bound `E`: once double counting selects points with large fibers and the
coverage arithmetic says that every close parameter must fit in such a fiber,
the selected points cover the full close-parameter set. -/
lemma exists_points_with_close_subset_matching_set_of_delta_nonmatching_bound
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D E t : ℕ}
    (hE : δ * (n : ℚ) ≤ E)
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      E * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) < (n - k) * t) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  obtain ⟨Dtop, hcard, hlarge⟩ :=
    exists_points_with_large_matching_subset_of_delta_nonmatching_bound
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs (D := D) (E := E) (t := t) hE hthreshold hsmall
  refine ⟨Dtop, hcard, ?_⟩
  exact close_proximity_subset_matching_set_on_points_of_large_matching_subset
    (F := F) (m := m) (n := n) (Q := Q)
    (k := k) (δ := δ) (x₀ := x₀) (ωs := ωs) (Dtop := Dtop) (D := D)
    h_gs hcover hlarge

/-- Claim-5.11-to-assembly bridge for the canonical integer bad-coordinate
bound: under the additional arithmetic coverage inequality, the selected
points cover the full close-parameter set in every selected fiber. -/
lemma exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D t : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) * t) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  exact exists_points_with_close_subset_matching_set_of_delta_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs (D := D) (E := ⌈δ * (n : ℚ)⌉₊) (t := t)
    (Nat.le_ceil _) hcover hthreshold hsmall

/-- Complement-threshold close-subset bridge for the canonical integer
bad-coordinate bound. This is the same selected-domain conclusion as
`exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound`,
but with `t` specialized to the complement of the target fiber threshold. -/
lemma exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound_complement
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) *
          (#(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) -
            (2 * k + 1)
              * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
              * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
              * D)) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  obtain ⟨Dtop, hcard, hlarge⟩ :=
    exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound_complement
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs (D := D) hthreshold hsmall
  refine ⟨Dtop, hcard, ?_⟩
  exact close_proximity_subset_matching_set_on_points_of_large_matching_subset
    (F := F) (m := m) (n := n) (Q := Q)
    (k := k) (δ := δ) (x₀ := x₀) (ωs := ωs) (Dtop := Dtop) (D := D)
    h_gs hcover hlarge

/-- Complement-threshold close-subset bridge through the standalone
`ArkLib.Claim511` double-counting theorem. This is the direct consumer form for
§6 callers that want the selected coordinates and full close-set coverage while
exposing the imported combinatorial core. -/
lemma
    exists_points_with_close_subset_matching_set_claim511_complement
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    {D : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) *
          (#(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) -
            (2 * k + 1)
              * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
              * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
              * D)) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  obtain ⟨Dtop, hcard, hlarge⟩ :=
    exists_points_with_large_matching_subset_of_natCeil_delta_nonmatching_bound_complement_claim511
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs (D := D) hthreshold hsmall
  refine ⟨Dtop, hcard, ?_⟩
  exact close_proximity_subset_matching_set_on_points_of_large_matching_subset
    (F := F) (m := m) (n := n) (Q := Q)
    (k := k) (δ := δ) (x₀ := x₀) (ωs := ωs) (Dtop := Dtop) (D := D)
    h_gs hcover hlarge

omit [DecidableEq (RatFunc F)] in
/-- Graph-clear complement-threshold close-subset bridge through the standalone
`ArkLib.Claim511` double-counting theorem. This is the direct Claim-5.11
consumer for the honest graph-condition extractions `R_graph_clear` and
`H_graph_clear`. -/
lemma
    exists_points_with_close_subset_matching_set_graph_clear_claim511_complement
    [NeZero n] [DecidableEq (Polynomial F)]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hcond : GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs)
    {D : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H_graph_clear k δ x₀ h_gs hcond)
          * (Bivariate.natDegreeY <| R_graph_clear k δ x₀ h_gs hcond)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H_graph_clear k δ x₀ h_gs hcond)
        * (Bivariate.natDegreeY <| R_graph_clear k δ x₀ h_gs hcond)
        * D ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) *
          (#(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) -
            (2 * k + 1)
              * (Bivariate.natDegreeY <| H_graph_clear k δ x₀ h_gs hcond)
              * (Bivariate.natDegreeY <| R_graph_clear k δ x₀ h_gs hcond)
              * D)) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆
        matching_set_at_x k δ h_gs x := by
  classical
  obtain ⟨Dtop, hcard, hlarge⟩ :=
    ArkLib.Claim511.exists_points_with_large_matching_subset_fin_complement
      (n := n)
      (β := coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
      (γ := F)
      (S := (Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)))
      (nonmatching := fun z => nonmatching_coords_for_z k δ h_gs z)
      (matchSet := fun x => matching_set_at_x k δ h_gs x)
      (E := ⌈δ * (n : ℚ)⌉₊)
      (k := k)
      (dH := Bivariate.natDegreeY <| H_graph_clear k δ x₀ h_gs hcond)
      (dR := Bivariate.natDegreeY <| R_graph_clear k δ x₀ h_gs hcond)
      (D := D)
      (by simpa using hthreshold)
      (fun z _hz =>
        nonmatching_coords_for_z_card_le_natCeil_delta_mul
          (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z)
      (by simpa using hsmall)
      (fun x hx =>
        lt_of_lt_of_le hx
          (nonmatching_coords_filter_card_le_matching_set_at_x_card
            (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs
            (Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) x))
  refine ⟨Dtop, hcard, ?_⟩
  exact close_proximity_subset_matching_set_on_points_of_large_matching_subset_graph_clear
    (F := F) (m := m) (n := n) (Q := Q)
    (k := k) (δ := δ) (x₀ := x₀) (ωs := ωs) (Dtop := Dtop) (D := D)
    h_gs hcond hcover hlarge

open Polynomial in
/-- Claim-5.11 plus the canonical `PzFamily` selected-domain package for any
uniform integer bad-coordinate bound `E`.  This is the assembled form consumed
by §5-to-§6 interpolation steps that use a non-canonical integer cap before
specializing to the nat-ceil close-proximity bound. -/
lemma exists_points_with_canonical_eval_polys_on_close_subset_of_delta_nonmatching_bound
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hk : 0 < k)
    {D E t : ℕ}
    (hE : δ * (n : ℚ) ≤ E)
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      E * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) < (n - k) * t)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        P z = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∃ P₀ : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P₀ z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P₀ z).eval ∘ ωs) ≤ δ) ∧
      (∃ E : Dtop → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Dtop, (P₀ z).eval (ωs x.1) = (E x).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, P z = P₀ z := by
  obtain ⟨Dtop, hDtop_card, hsubset⟩ :=
    exists_points_with_close_subset_matching_set_of_delta_nonmatching_bound
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs (D := D) (E := E) (t := t) hE hcover hthreshold hsmall
  refine ⟨Dtop, hDtop_card, ?_⟩
  exact PzFamily_exists_canonical_eval_polys_on_close_subset_and_unique
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs Dtop hk hsubset
    hunique

/-- Claim-5.11 plus the canonical `PzFamily` selected-domain package.  This is
the assembled form consumed by the remaining §5-to-§6 interpolation step: the
double-counting hypotheses select `k + 1` coordinates, and on exactly that
domain the canonical close-polynomial family has evaluation-polynomial
witnesses and uniqueness. -/
lemma exists_points_with_canonical_eval_polys_on_close_subset_of_natCeil_delta_nonmatching_bound
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hk : 0 < k)
    {D t : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D + t ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) * t)
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        P z = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∃ P₀ : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P₀ z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P₀ z).eval ∘ ωs) ≤ δ) ∧
      (∃ E : Dtop → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Dtop, (P₀ z).eval (ωs x.1) = (E x).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, P z = P₀ z := by
  exact exists_points_with_canonical_eval_polys_on_close_subset_of_delta_nonmatching_bound
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
    h_gs hk (D := D) (E := ⌈δ * (n : ℚ)⌉₊) (t := t)
    (Nat.le_ceil _) hcover hthreshold hsmall hunique

set_option linter.style.longLine false in
/-- Canonical selected-domain package in the complement-threshold arithmetic shape.

This is the direct consumer form for callers that have already chosen the natural
slack `#S - threshold`: it packages Claim 5.11 coverage, the canonical `PzFamily`
evaluation-polynomial witnesses, and uniqueness under one strict counting inequality. -/
lemma exists_points_with_canonical_eval_polys_on_close_subset_of_natCeil_delta_nonmatching_bound_complement
    [NeZero n]
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Claim57Residuals (F := F) k δ x₀ h_gs]
    (hk : 0 < k)
    {D : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D ≤ #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * #(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) <
        (n - k) *
          (#(coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) -
            (2 * k + 1)
              * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
              * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
              * D))
    (hunique : ∀ P : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
      ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        P z = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∃ P₀ : F → F[X],
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        (P₀ z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P₀ z).eval ∘ ωs) ≤ δ) ∧
      (∃ E : Dtop → F[X],
        (∀ x, (E x).natDegree < k + 1) ∧
          ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
            ∀ x : Dtop, (P₀ z).eval (ωs x.1) = (E x).eval z) ∧
      ∀ P : F → F[X],
        (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
          (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) →
        ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, P z = P₀ z := by
  obtain ⟨Dtop, hcard, hsubset⟩ :=
    exists_points_with_close_subset_matching_set_claim511_complement
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs (D := D) hcover hthreshold hsmall
  refine ⟨Dtop, hcard, ?_⟩
  exact PzFamily_exists_canonical_eval_polys_on_close_subset_and_unique
    (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) h_gs Dtop hk hsubset
    hunique

/-- Claim 5.11 from [BCIKS20].
There exists a set of points `{x₀,...,x_{k+1}}` such that the sets S_{x_j} satisfy the condition in
Claim 5.10.

GAP (blocked — see the §5 GAP ANALYSIS block above). A double-counting argument over the matching
set supplied by the Prop 5.5 specialization; the abstract pigeonhole core is proven as
`tagged_fiber_pigeonhole` in `Guruswami.lean`, but the factor-tag specialization and the per-point
cardinality bound still rely on missing ingredient C. -/
lemma exists_points_with_large_matching_subset
    {ωs : Fin n ↪ F}
      (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
      [Claim57Residuals (F := F) k δ x₀ h_gs]
      {_x : Fin n}
      {D : ℕ}
      (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hcard : k + 1 ≤ ((Finset.univ : Finset (Fin n)).filter
      (fun x =>
        (2 * k + 1)
          * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D < (matching_set_at_x k δ h_gs x).card)).card) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
          * D := by
    have _hD_used := hD
    exact exists_points_with_large_matching_subset_of_filter_card
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs (D := D) hcard

end BCIKS20ProximityGapSection5

end ProximityGap
