/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PlaceGeometrySupply
import ArkLib.ToMathlib.BetaInputSupply

/-!
# Issue #304 — §6 matching-geometry producers for the keystone assembly
(`KeystoneAssembly.section5DataFin_of_producers` items `mpPoint` / `hcardFin`).

What is proven here (all axiom-clean, no sorry):

* `card_gt_of_compl_subset` — the bad-set counting core: if `matchingSet` contains every
  point outside a `bad` set and `N + #bad < |F|`, then `#matchingSet > N`.
* `hcardConcreteFin_of_badSet` — the finite-range concrete cardinality family
  `∀ t ∈ [k,T], #matchingSet > (2t+1)·d·D·d_H` (in `WithBot ℕ`) from the single top-index
  bad-set bound (monotone collapse + cast).
* `hcardFin_of_badSet` — **the `hcardFin` producer**: chains the bad-set counting through
  the verified L9/L10 weight collapse (`BetaInputSupply.hcardFin_of_concrete`,
  `betaRec_weight_le_concrete`) to produce the exact
  `Section5StrictDataFin.hcardFin` field
  `#matchingSet > weight_Λ_over_𝒪 (betaRec … t) D · d_H` on `[k, T]`,
  from `|F|` large + an excluded bad set + the App-A weight budgets.
* `coeff_coe_eq_zero_of_natDegree_lt` — proximate-root truncation reading: a polynomial of
  `natDegree < k`, viewed as a power series, has vanishing `t`-th coefficient for `t ≥ k`.
* `mpFin_of_henselData_polyProximate` (+ `_dvd` variant) — **the `mpPoint` producer
  upgrade**: the per-`(t,z)` `haP_coeff` field of `BridgeData` is discharged *uniformly*
  when the proximate root at `z` is the §5 decoded polynomial `P_z` of degree `< k`
  (`coeff t P_z = 0` for `t ≥ k` is pure truncation), and the unit readings `w`/`x` are
  taken `t`-uniform (`w = π_z(W)`, `x = π_z(ξ)` do not depend on `t`).  The only remaining
  per-`(t,z)` input is the genuine L12 `α_t`-identity `hαβ`.
* `section5DataFin_of_producers_badSet` — capstone glue: the full
  `Section5StrictDataFin` constructor with the `hcardFin` item replaced by the bad-set
  counting + weight-budget inputs (the honest §6 geometry shape).
* `mpPoint_of_polyProximate_at_T` — the `mpPoint` family in the exact
  `section5DataFin_of_producers` shape (`T := Ppoly.natDegree`).
-/


set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open PowerSeries

namespace ArkLib

namespace Match304

/-! ## Part 1 — the bad-set cardinality producer (mechanical counting) -/

section Counting

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Bad-set counting core.**  If the matching set contains every point of `F` outside a
finite `bad` set, and `N + #bad < |F|`, then `#matchingSet > N`.  This is the §6 geometry
counting shape: the matching set is everything except finitely many excluded (discriminant /
denominator / non-agreement) points. -/
theorem card_gt_of_compl_subset {matchingSet bad : Finset F} {N : ℕ}
    (hcover : ∀ z : F, z ∉ bad → z ∈ matchingSet)
    (hbig : N + bad.card < Fintype.card F) :
    N < matchingSet.card := by
  have hsub : Finset.univ \ bad ⊆ matchingSet := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    exact hcover z hz.2
  have hcard : (Finset.univ \ bad).card = Fintype.card F - bad.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ bad), Finset.card_univ]
  have hle := Finset.card_le_card hsub
  omega

/-- **Finite-range concrete cardinality family from the bad set.**  The single top-index
bound `(2T+1)·d·D·d_H + #bad < |F|` yields the whole finite-range concrete family
`∀ t ∈ [k,T], #matchingSet > (2t+1)·d·D·d_H` in `WithBot ℕ` — exactly the
`hcardConcreteFin` input of `BetaInputSupply.hcardFin_of_concrete` /
`section5DataFin_of_centered_concrete`.  Monotone collapse in `t` + cast. -/
theorem hcardConcreteFin_of_badSet {matchingSet bad : Finset F} {d D dH k T : ℕ}
    (hcover : ∀ z : F, z ∉ bad → z ∈ matchingSet)
    (hbig : (2 * T + 1) * d * D * dH + bad.card < Fintype.card F) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > (((2 * t + 1) * d * D * dH : ℕ) : WithBot ℕ) := by
  intro t _hkt htT
  have hmono : (2 * t + 1) * d * D * dH ≤ (2 * T + 1) * d * D * dH := by
    have h1 : 2 * t + 1 ≤ 2 * T + 1 := by omega
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1))
  have hlt : (2 * t + 1) * d * D * dH < matchingSet.card :=
    lt_of_le_of_lt hmono (card_gt_of_compl_subset hcover hbig)
  exact_mod_cast hlt

end Counting

/-! ## Part 2 — the `hcardFin` producer (bad-set counting × verified weight collapse) -/

section HcardFin

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The `hcardFin` producer from `|F|` large + an excluded bad set.**

Chains the bad-set counting (`hcardConcreteFin_of_badSet`) through the verified
Claim-A.2 weight collapse (`BetaInputSupply.hcardFin_of_concrete`, which consumes
`betaRec_weight_le_concrete ≤ (2t+1)·d·D`) to produce the exact
`Section5StrictDataFin.hcardFin` / `BetaCurveInputFin.hcardFin` field:

```
∀ t ∈ [k, T],  #matchingSet > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D · d_H
```

The genuine isolated inputs are the App-A weight budgets (`hbB`, `hBzero`, `hbξ` — brick
L2b/L4/L5 content) and the two §6 geometry facts: the matching set covers the complement of
the bad set, and `|F|` exceeds `(2T+1)·d·D·d_H + #bad`.  Everything else is in-tree. -/
theorem hcardFin_of_badSet (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D d k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd1 : 1 ≤ d) (hdH_le : H.natDegree ≤ d) (hdH_D : H.natDegree ≤ D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((D - Multiset.card p.parts)
              + (d - betaδ i₁ - Multiset.card p.parts) * (D - H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        d - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D
        ≤ (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    {matchingSet bad : Finset F}
    (hcover : ∀ z : F, z ∉ bad → z ∈ matchingSet)
    (hbig : (2 * T + 1) * d * D * H.natDegree + bad.card < Fintype.card F) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree :=
  BetaInputSupply.hcardFin_of_concrete x₀ R H hHyp Bcoeff hD hH hd1 hdH_le hdH_D
    hbB hBzero hbξ
    (hcardConcreteFin_of_badSet (d := d) (D := D) (dH := H.natDegree) hcover hbig)

end HcardFin

/-! ## Part 3 — the proximate-root truncation reading (mechanical) -/

/-- **Proximate-root truncation.**  A polynomial of `natDegree < k`, viewed as a power
series, reads zero at every coefficient index `t ≥ k`.  This is the `haP_coeff` field of
`MpFinSupply.BridgeData` discharged uniformly: in §5 the proximate root `P_z` is the decoded
codeword polynomial of degree `< k`, so its `(X−x₀)^t` reading vanishes for every tail index
`t` in the counting range `k ≤ t`. -/
theorem coeff_coe_eq_zero_of_natDegree_lt {F : Type} [CommSemiring F]
    {p : Polynomial F} {k t : ℕ} (hdeg : p.natDegree < k) (hkt : k ≤ t) :
    PowerSeries.coeff t (p : PowerSeries F) = 0 := by
  rw [Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hkt)

/-! ## Part 4 — the upgraded `mpPoint` producer: polynomial proximate root -/

section MpPoint

variable {F : Type} [Field F]
variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-- **The `mpFin`/`mpPoint` family with the decoded-polynomial proximate root.**

As `MpFinSupply.mpFin_of_henselData`, but with two of the four per-`(t,z)` `BridgeData`
readings discharged mechanically:

* `haP_coeff` — the proximate root at `z` is the §5 decoded polynomial `Pz z` of
  `natDegree < k`; its `t`-th power-series coefficient vanishes for every `t ≥ k`
  (`coeff_coe_eq_zero_of_natDegree_lt`), uniformly in the counting range;
* `hw`/`hx` — the unit readings are `t`-uniform (`w = π_z(W)`, `x = π_z(ξ)` do not depend
  on the tail index), so they are taken once per `z`.

The remaining genuine per-`(t,z)` input is exactly the L12 `α_t`-identity `hαβ` (the
`betaRec`-numerator identification of L13) plus the per-`z` §5 root geometry — the honest
irreducible frontier. -/
def mpFin_of_henselData_polyProximate {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ a₀ : (z : F) → PowerSeries F)
    (Pz : (z : F) → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_root : ∀ z ∈ matchingSet, (f z).IsRoot ((Pz z : PowerSeries F)))
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet,
      (Pz z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : F → F) (a e : ℕ → F → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet →
      PowerSeries.coeff t (aβ z) =
        (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t) / (w z ^ a t z * x z ^ e t z))
    (hw : ∀ z ∈ matchingSet, w z ≠ 0)
    (hx : ∀ z ∈ matchingSet, x z ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  MpFinSupply.mpFin_of_henselData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp)
    (Bcoeff := Bcoeff) (root := root)
    f aβ (fun z => (Pz z : PowerSeries F)) a₀
    haβ_root haP_root haβ_cong haP_cong hsep
    (fun _ z => w z) (fun _ z => x z) a e
    hαβ
    (fun _ _ _ z hz => hw z hz)
    (fun _ _ _ z hz => hx z hz)
    (fun t hkt _ z hz => coeff_coe_eq_zero_of_natDegree_lt (hPdeg z hz) hkt)

/-- **Divisibility-route variant.**  As `mpFin_of_henselData_polyProximate`, but the
proximate-root membership arrives as the GS matching-factor divisibility
`(Y − P_z) ∣ f_z` (the `MatchingExtractor` / Gap-B output shape), converted to a root inside
`MpFinSupply.mpFin_of_henselData_dvd`. -/
def mpFin_of_henselData_dvd_polyProximate {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ a₀ : (z : F) → PowerSeries F)
    (Pz : (z : F) → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_dvd : ∀ z ∈ matchingSet,
      (Polynomial.X - Polynomial.C ((Pz z : PowerSeries F))) ∣ f z)
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet,
      (Pz z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : F → F) (a e : ℕ → F → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet →
      PowerSeries.coeff t (aβ z) =
        (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t) / (w z ^ a t z * x z ^ e t z))
    (hw : ∀ z ∈ matchingSet, w z ≠ 0)
    (hx : ∀ z ∈ matchingSet, x z ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  MpFinSupply.mpFin_of_henselData_dvd (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp)
    (Bcoeff := Bcoeff) (root := root)
    f aβ (fun z => (Pz z : PowerSeries F)) a₀
    haβ_root haP_dvd haβ_cong haP_cong hsep
    (fun _ z => w z) (fun _ z => x z) a e
    hαβ
    (fun _ _ _ z hz => hw z hz)
    (fun _ _ _ z hz => hx z hz)
    (fun t hkt _ z hz => coeff_coe_eq_zero_of_natDegree_lt (hPdeg z hz) hkt)

end MpPoint

/-! ## Part 5 — capstone glue: the assembly with the bad-set `hcardFin` item -/

section Capstone

open BetaToCurveCoeffPolys Claim59Conditional
open CorrelatedAgreementListDecodingClosed HcardDischarge
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`mpPoint` in the exact `section5DataFin_of_producers` shape** (`T := Ppoly.natDegree`):
the polynomial-proximate-root producer specialised to the truncation index the keystone
assembly fixes.  Pure instantiation of `mpFin_of_henselData_polyProximate`. -/
noncomputable def mpPoint_of_polyProximate_at_T
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}
    {k : ℕ} (Ppoly : F[X][Y]) {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ a₀ : (z : F) → PowerSeries F)
    (Pz : (z : F) → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_root : ∀ z ∈ matchingSet, (f z).IsRoot ((Pz z : PowerSeries F)))
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet,
      (Pz z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : F → F) (a e : ℕ → F → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z, z ∈ matchingSet →
      PowerSeries.coeff t (aβ z) =
        (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t) / (w z ^ a t z * x z ^ e t z))
    (hw : ∀ z ∈ matchingSet, w z ≠ 0)
    (hx : ∀ z ∈ matchingSet, x z ≠ 0) :
    ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  mpFin_of_henselData_polyProximate (k := k) (T := Ppoly.natDegree)
    f aβ a₀ Pz hPdeg haβ_root haP_root haβ_cong haP_cong hsep w x a e hαβ hw hx

/-- **Capstone: the keystone assembly with the bad-set `hcardFin` item.**

`KeystoneAssembly.section5DataFin_of_producers` with the opaque `hcardFin` producer replaced
by its honest §6 geometry sources: the App-A weight budgets (`hbB`/`hBzero`/`hbξ`) plus the
two counting facts (`hcover`: the matching set contains everything outside the bad set;
`hbig`: `|F| > (2·deg(Ppoly)+1)·d_R·D·d_H + #bad`).  The `hcardFin` field is discharged by
`hcardFin_of_badSet`; every other field is delegated verbatim. -/
noncomputable def section5DataFin_of_producers_badSet {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet bad : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (root z))
    -- the App-A weight budgets (`d := b.R.natDegree`):
    (hd1 : 1 ≤ b.R.natDegree) (hdH_le : b.H.natDegree ≤ b.R.natDegree)
    (hdH_D : b.H.natDegree ≤ b.D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 b.hH (Bcoeff i₁ p) b.D
          ≤ (WithBot.some ((b.D - Multiset.card p.parts)
              + (b.R.natDegree - betaδ i₁ - Multiset.card p.parts)
                * (b.D - b.H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        b.R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 b.hH (ξ x₀ b.R b.H b.hHyp) b.D
        ≤ (WithBot.some ((b.R.natDegree - 1) * (b.D - b.H.natDegree + 1)) : WithBot ℕ))
    -- the §6 bad-set counting facts:
    (hcover : ∀ z : F, z ∉ bad → z ∈ matchingSet)
    (hbig : (2 * Ppoly.natDegree + 1) * b.R.natDegree * b.D * b.H.natDegree + bad.card
        < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec x₀ b.R b.H b.hHyp Bcoeff t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  KeystoneAssembly.section5DataFin_of_producers
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    (x₀ := x₀) b Bcoeff matchingSet root Ppoly hrep hdegX mpPoint
    (hcardFin_of_badSet x₀ b.R b.H b.hHyp Bcoeff b.hD b.hH hd1 hdH_le hdH_D
      hbB hBzero hbξ hcover hbig)
    hsubst hβ hHensel hdeg

end Capstone

end Match304

end ArkLib

-- Axiom audit: every declaration must rest only on [propext, Classical.choice, Quot.sound].
#print axioms ArkLib.Match304.card_gt_of_compl_subset
#print axioms ArkLib.Match304.hcardConcreteFin_of_badSet
#print axioms ArkLib.Match304.hcardFin_of_badSet
#print axioms ArkLib.Match304.coeff_coe_eq_zero_of_natDegree_lt
#print axioms ArkLib.Match304.mpFin_of_henselData_polyProximate
#print axioms ArkLib.Match304.mpFin_of_henselData_dvd_polyProximate
#print axioms ArkLib.Match304.mpPoint_of_polyProximate_at_T
#print axioms ArkLib.Match304.section5DataFin_of_producers_badSet
