# SYZ12: BCIKS20 Claim 5.7 program — Chunks C5 (matching-fold) + C6 (heavy-pin) (2026-07-11)

## What landed

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ12BCIKS57Chunks56.lean`
(namespace `BCIKS20.CellPencilJohnson.SYZ12`), axiom-clean.

Continues the SYZ10/SYZ11 chunk program discharging the strictly-smaller Johnson-lane
residual `CellPackageSupplyDiscLocus` (`Frontier/_SYZ8CellPackageSupply.lean`). SYZ11
partitioned `DiscLocusCellData` into five chunk interfaces and proved C3 (§5 grading) + the
composition. This file resolves the two remaining downstream chunks, both taken **after** a
`DiscBudgetSupply` (nonzero disc + base/separability certs + degree budget already exist).

## C6 `HeavyPinSupply` — DISCHARGED (given one named budget inequality)

`heavyPinSupply_of_discBudget` builds the *entire* C6 output from `DiscBudgetSupply` plus one
honest counting hypothesis. No branch mathematics remains in C6.

```
noncomputable def heavyPinSupply_of_discBudget
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)} {R : (F₀[X])[X][Y]}
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (g : GradedYRootSupply domain k δ u R H)
    (db : DiscBudgetSupply domain k δ u R H g)
    (hHeavyBudget :
      max (taylorWCeil g) 1 + db.disc.natDegree < Fintype.card F₀) :
    HeavyPinSupply domain k δ u R H g db
```

Mechanism:
- `S₀ := univ.filter (disc.eval z ≠ 0)` — the disc non-vanishing locus itself ⇒ `hS₀sub`
  definitional (`Finset.mem_filter`).
- `Bw := taylorWCeil g := (taylor (C x₀) w).support.sup (fun t => ((…).coeff t).natDegree)`
  ⇒ `hBw` definitional (support-sup for `t ∈ support`; off-support coeff `= 0`, natDegree `0`).
- `hS₀ : max Bw 1 < |S₀|` is exactly `ArkLib.Match304.card_nonvanishing_gt`
  (`ToMathlib/DiscriminantBadSet.lean`): a nonzero disc vanishes on `≤ natDegree disc` points.

The whole of C6 is thus this one pigeonhole over the locus. The single honest residual is the
counting inequality `max (taylorWCeil g) 1 + natDegree disc < |F₀|`. (Not connected to the
existing `db.hbig = gradedCardBudget … + natDegree disc < |F₀|`: that would require
`max Bw 1 ≤ gradedCardBudget …`, i.e. bounding the `X`-degrees of `w`'s Taylor coefficients by
the graded matching budget — genuine grading work, deliberately left as a named hypothesis, not
claimed.)

## C5 `MatchingFoldSupply` — GENUINE CORE ISOLATED (ξ-weight obligation discharged)

The fold agreement `hfold` (each matching point folds **linearly** through the `Y`-root divisor
`w`: `(w.eval (C(e j)+C x₀)).eval z = u₀ j + z·u₁ j`) is the genuine BCIKS §6 α-series matching.
It cannot be produced from the disc budget: if one took `matchingSet = locus` (to make `hcard`
free like C6), `hfold` would assert linear folding at *every* non-vanishing point, which is
false in general. So the matching sets are genuinely a constrained subset, and their data
(`e, u₀, u₁, matchingSet, hmatchSub, hfold, hcard`) is collected in the minimal named Prop:

```
structure FoldMatchingCore … (g) (db) : Type where
  e : Fin n → F₀
  he : Function.Injective e
  u₀ u₁ : Fin n → F₀
  matchingSet : Fin n → Finset F₀
  hmatchSub : ∀ j, ∀ z ∈ matchingSet j, db.disc.eval z ≠ 0
  hfold : ∀ j, ∀ z ∈ matchingSet j,
    (g.w.eval (C (e j) + C g.x₀)).eval z = u₀ j + z * u₁ j
  hcard : ∀ j, killBudget n g.D H.natDegree (natDegreeY R) (xiWeightCeil g) * H.natDegree
      < (matchingSet j).card
```

Around that core, `matchingFoldSupply_of_foldMatchingCore : FoldMatchingCore … → MatchingFoldSupply …`
**discharges the ξ-weight field** `xw, hξw`. The canonical `xw := xiWeightCeil g :=
(weight_Λ_over_𝒪 … (ξ x₀ R H hHyp) D).unbotD 0` is the ξ-weight's own value; `hξw` holds by a
`WithBot` case split (`⊥ ≤ _` = `bot_le`; `some m ≤ some m` = refl via `unbotD_coe`). So the C5
producer no longer has to exhibit *any* ξ-weight witness — only the α-series fold-matching data
and its count remain. (Note `hcard`'s `killBudget` is stated at this canonical `xw`, which is
the tightest, so the count obligation is if anything easier.)

## Reduced assembly

`discLocusCellData_of_core (p : PlaceCurveSupply) (db) (c : FoldMatchingCore) (hHeavyBudget)
: DiscLocusCellData` — the SYZ11 C3 grading + this C5 core + this C6 discharge assembled. Vs
SYZ11's `discLocusCellData_of_placeCurve`, the whole `HeavyPinSupply` input is gone (C6
discharged to one inequality) and `MatchingFoldSupply` is narrowed to `FoldMatchingCore`.

## Updated remaining-open Props (Claim 5.7 per-cell package)

- **C2 `PlaceCurveSupply`** (+ boundary-shifted C3 branch data): `H` irred monic pos-deg, `x₀`,
  `Hypotheses`, `hd2`, `root`, `Ppoly/hrepG` (γ genuine), `w/hwdeg/hwdvd` (Y-root divisor).
  — genuine open AG. UNCHANGED.
- **C4 `DiscBudgetSupply`**: `disc ≠ 0` with base+separability certs + `hbig`. The nonvanishing
  half is open. UNCHANGED.
- **C5 `FoldMatchingCore`**: the α-series fold-matching data + count. — genuine open §6.
  (Down from `MatchingFoldSupply`: the ξ-weight field is now discharged.)
- **C6**: FULLY discharged to the single counting inequality
  `max (taylorWCeil g) 1 + natDegree disc < |F₀|`. (No structure obligation remains.)

Net: genuine open mathematics of the package = C2 (place-curve/branch), C4 (disc nonvanishing),
C5 fold-matching core, and two honest counting budget inequalities (C6 heavy + C5 fold count).

## Axiom audit

`#print axioms` on `heavyPinSupply_of_discBudget`, `matchingFoldSupply_of_foldMatchingCore`,
`discLocusCellData_of_core`: `[propext, Classical.choice, Quot.sound]` — clean.
