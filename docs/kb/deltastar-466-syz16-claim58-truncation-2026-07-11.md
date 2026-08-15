# δ* / #466 — SYZ16: the Claim 5.8 truncation identity `γ = trunc k γ`, attacked at its root

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ16Claim58Truncation.lean`
Status: LANDED, axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`.

## The object

SYZ15's whole T-loaded §5 branch handoff — and its non-vacuity witness
`branch_field_gap_at_monic_quadratic` — takes as an *external hypothesis* the [BCIKS20] **Claim 5.8
truncation identity**

    htrunc : gammaGenuine x₀ R H hHyp = ↑(PowerSeries.trunc k (gammaGenuine …)).

Coefficient-wise this is exactly `αGenuine t = 0` for all `t ≥ k`: the genuine Y-root branch series
is a **polynomial** (its tail vanishes). SYZ16 asks *why* that holds and how far in-tree machinery
carries it.

## The mathematical reason (FOUND)

The mechanism is already present in-tree, in `ToMathlib/BetaTailDegreeVanishing.lean`. The genuine
branch coefficients obey the `(A.1)` Hensel recursion `βHensel_succ`, whose structure constants
`B_{i₁,λ}` are built from the `i₁`-th **lift-`X` Hasse derivative** of `R` (`hasseDerivX i₁`). That
derivative annihilates every `Y`-coefficient of `X`-degree `< i₁`
(`B_coeff_eq_zero_of_natDegree_coeff_lt`). Hence the numerator recursion is **degree-bounded on the
`X`-layer by `deg_X R`** — it is *not* the expansion of an infinite algebraic branch. Concretely
(`βHensel_eq_zero_of_initial_window`): once the branch coefficients vanish on the full initial
segment `[1, T₀]` with `T₀ ≥ deg_X R`, every successor order `> T₀` collapses to an empty-partition
Hasse coefficient of order `> deg_X R`, which vanishes by degree.

**This is the in-tree face of "the fold only sees finitely many coefficients":** the genuine
γ-series is a polynomial because the `(A.1)` numerator recursion is `X`-Hasse-degree bounded. Not
"algebraic of bounded degree in the abstract" — concretely bounded by `deg_X R` through the Hasse
structure of the recursion.

## The honest wall (a genuine finding, not just a residual)

The pure `(A.1)`-recursion degree argument reaches **only the window-collapse regime.** The naive
`[k,T] → T+1` window propagation is **FALSE** (recorded in `BetaTailDegreeVanishing`: a surviving
partition at order `T+1` needs all parts `< k`, which always exist), so tail vanishing forces
nothing unless the *entire* initial segment `[1, T₀]` already vanishes — i.e. the branch is
constant past its window. For a branch with a genuinely nonzero window coefficient the tail datum
is **equivalent** (monic `d_H ≤ 2`, via the `GenuinePpolyConverter` converter both ways) to the
corrected representative `hrepT` itself. So Claim 5.8 in its non-degenerate form cannot be produced
ab initio without the algebraicity / `X`-degree-budget (#138) content. SYZ16 isolates that
irreducible content to a **single minimal Prop** and discharges everything around it.

## What was proven (all axiom-clean, verbatim statements)

Namespace `BCIKS20.CellPencilJohnson.SYZ16`.

1. **`GammaGenuineTailPolynomial`** — the minimal named residual (a `def`, the Claim 5.8
   tail-degree datum):

       def GammaGenuineTailPolynomial (x₀ : F) (R : F[X][X][Y])
           (hHyp : ClaimA2.Hypotheses x₀ R H) (T : ℕ) : Prop :=
         ∀ t, T < t → αGenuine H x₀ R hHyp t = 0

   "the genuine γ-series is a polynomial of degree ≤ T."

2. **`gammaGenuine_eq_trunc_of_graded_disc_tail`** (the reduction — largest honest piece).  The
   truncation identity from finite geometric data + the tail residual, with the F6-unsatisfiable
   ground representative `hrepG` **replaced** by `GammaGenuineTailPolynomial`.  Signature (elided
   graded side-conditions `hD hH hmonic hd2 hdHD hD_Rx0 hR`):

       theorem … (hHyp) {D k T} … (htail : GammaGenuineTailPolynomial x₀ R hHyp T)
         {matchingSet} (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
           ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
         {disc} (hdisc : disc ≠ 0) (hcover : ∀ z, disc.eval z ≠ 0 → z ∈ matchingSet)
         (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree T + disc.natDegree
             < Fintype.card F) :
         gammaGenuine x₀ R H hHyp = ↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp))

   Proof: `claim58prime_genuine_fin_of_monic` fed by `SβLargeAtFin_of_graded_disc` (§6 counting)
   and `htail`.  **No representative — ground or T-loaded — appears.** Every ingredient of Claim
   5.8 except the branch polynomiality is discharged from finite geometric data.

3. **`gammaGenuineTailPolynomial_of_initial_window`** (the ab-initio producer / the mechanism):

       theorem … (hHyp) {T₀} (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
         (hlift : ∀ t, S5Genuine.LiftIdentityAt H x₀ R hHyp t)
         (hwin : ∀ l, 1 ≤ l → l ≤ T₀ → αGenuine H x₀ R hHyp l = 0) :
         GammaGenuineTailPolynomial x₀ R hHyp T₀

   Proof routes `BetaTail.αGenuine_tail_eq_zero_of_window_of_lift`.  **No representative, no
   assumed truncation** — the honest ab-initio face of Claim 5.8, valid in the window-collapse
   regime.

4. **`gammaGenuineTailPolynomial_of_corrected_representative`** (the wall / equivalence direction):
   from the T-loaded representative `hrepT`, the tail datum at `max (deg P₀) (deg P₁)` (via
   `htailDeg_genuine_of_corrected_representative`).  With the converter this makes the residual
   *equivalent* to the representative at monic `d_H ≤ 2`.

5. **`branch_field_gap_of_graded_disc_tail`** (wiring into SYZ15, `htrunc` REMOVED).  Re-derives
   SYZ15's non-vacuity witness with the raw truncation hypothesis discharged: at monic quadratic,
   from finite geometric data + `GammaGenuineTailPolynomial` it produces `htrunc` internally (via
   (2)) then calls `SYZ15.branch_field_gap_at_monic_quadratic`.  Conclusion identical to SYZ15's:
   ground representative field EMPTY (F6) ∧ T-loaded field INHABITED with `[0,k)` support.

## Net effect on the program

SYZ15 conditioned the repaired §5 branch field on a **bare** `htrunc : γ = trunc k γ`.  SYZ16
strips that to its skeleton: `htrunc` is now *derived* from finite §6 geometric counting data plus
the **single minimal Prop `GammaGenuineTailPolynomial`** ("γ is a polynomial"), and that Prop is
(a) produced ab initio in the window-collapse regime, and (b) shown equivalent to the representative
in the non-degenerate regime — pinning the exact open content.

## Honest residual (named, minimal)

- **`GammaGenuineTailPolynomial` non-degenerate** — for a branch with a nonzero window coefficient,
  producing the tail datum needs the algebraicity / **#138 `X`-degree budget** content (equivalent
  to the representative at monic `d_H ≤ 2`).  This is now the *only* Claim 5.8 residual; everything
  else is discharged.  The ab-initio degree route settles the window-collapse (decoded/constant)
  case only, because naive window propagation is false.
- Inherited unchanged: #138 ground `X`-degree budget (`degreeX P₀/P₁` bounds); monic `d_H ≥ 3`
  per-coefficient T-form (span dichotomy) open, non-unit leading coeff false; the SYZ11–13
  T-carrier rename (mechanical).

## Program scoreboard (BCIKS20 §5 branch lane)

- SYZ8: disc-locus reduction of the Johnson residual — LANDED (ground).
- SYZ11–13: C2→C6 interface stack composition — LANDED (ground; terminal `hrepG` F6-empty).
- SYZ14: reduction to the single `HenselBranchSupply` residual — LANDED; flagged F6 vacuity.
- SYZ15: F6 vacuity REPAIRED via the satisfiable T-loaded interface chain; non-vacuity witness
  carried a bare `htrunc` hypothesis.
- **SYZ16 (this note): the `htrunc` hypothesis is REDUCED to its root.** Found the mechanism (the
  `(A.1)` recursion is `X`-Hasse-degree bounded ⇒ the branch is a polynomial), discharged every
  non-tail ingredient from finite geometric data (`gammaGenuine_eq_trunc_of_graded_disc_tail`),
  proved the ab-initio window-collapse case, and pinned the exact open content to the single Prop
  `GammaGenuineTailPolynomial`.  SYZ15's non-vacuity witness re-derived with `htrunc` removed.

The open §5 mathematics is now the single Prop "the genuine γ-series is a polynomial" in the
non-degenerate regime (= the #138 `X`-degree budget in disguise); all surrounding interface and
counting scaffolding is discharged and axiom-clean.
