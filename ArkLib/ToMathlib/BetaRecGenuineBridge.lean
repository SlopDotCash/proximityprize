/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaToCurveCoeffPolysOffcentre
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchRoot
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

/-!
# Issue #304 — the `betaRec ↔ βHensel` bridge and the monic genuine-route identification

## What this file proves

The keystone surfaces (`OffcentreKeystoneAssembly`, `BetaToCurveCoeffPolysOffcentre`, the graded
weight collapse) are built on the abstract recursion capsule `ArkLib.betaRec` with a coefficient
family `Bcoeff`.  The genuine analytic §5 chain (`GammaGenuine`, `S5Genuine`, `S5GenuineMonic`,
the P2 Faà-di-Bruno match) is built on the concrete `(A.1)` recursion
`BCIKS20.HenselNumerator.βHensel` with the canonical coefficients `B_coeff`.  The two recursions
are **identical up to a global sign convention**: `βHensel` carries the leading minus of `(A.1)`
on the successor sum, `betaRec` does not.  Feeding `betaRec` the **sign-flipped canonical family**
`BcoeffSigned := fun i₁ p => -(B_coeff …)` absorbs the minus per-term (each summand is linear in
the `Bcoeff` slot), so the two recursions agree on the nose:

* `betaRec_BcoeffSigned_eq_βHensel` — `betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) t = βHensel … t`
  for every `t` (strong induction; the exclusion filters and the `W`/`ξ` exponents coincide
  definitionally, the partition products match via `partitionProd_eq_prod_count`).

Consequences (the payoff — the keystone surface plugs into the PROVEN genuine chain):

* `alphaFromBeta_BcoeffSigned_eq_coeff_βHenselAssembled` — the off-centre keystone coefficient
  `αFromBeta … (BcoeffSigned …) t` IS the `t`-th coefficient of the assembled `(A.1)` series
  `βHenselAssembled` (the normalizing denominators agree: `henselDenominatorExponent t = 2t − 1`).
* `gammaLocal_BcoeffSigned_eq_βHenselAssembled` — the off-centre local Hensel series at the signed
  canonical coefficients IS `βHenselAssembled`.
* `gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic` — **for monic `H` the off-centre local series
  IS the genuine Hensel-lift root `gammaGenuine`**: the proven monic Faà-di-Bruno match
  (`restrictedFaaDiBrunoMatch_of_monic`) identifies `βHenselAssembled = gammaGenuine`
  (`restrictedFaaDiBrunoMatch_iff_βHenselAssembled_eq_gammaGenuine`), and the bridge transports it.
* `alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic` — coefficient form: for monic `H`,
  `αFromBeta … (BcoeffSigned …) t = αGenuine … t` for every `t`.

## Why this matters for #304

With these identifications, every remaining field of the satisfiable off-centre bundle
`Section5StrictDataOffcentreFin` (at `Bcoeff := BcoeffSigned`, monic `H`) becomes a statement about
the GENUINE Hensel root `gammaGenuine`, where the analytic §5 work is already proven in-tree:
`gammaGenuine_root` (the real `R(X, γ, Z) = 0`), `ζ_ne_zero`/`den_ne_zero` (separability and
denominator nonvanishing), `claim58prime_genuine_of_monic` (γ equals its truncation —
unconditional for monic `H` given the §5 largeness), and `gammaGenuine_Z_linear_of_coeffs_Z_linear`
(Claim 5.9 reduced to per-coefficient Z-linearity).  In particular the `hrep` field
(`polyToPowerSeries𝕃 H Ppoly = gammaLocal …`) becomes literally the genuine Prop-5.5
representative statement for `gammaGenuine`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  Appendix A.4 (recursion (A.1), Claim A.2 normalization `α_t = β_t / (W^{t+1}·ξ^{e_t})`).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace BetaRecGenuineBridge

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The signed canonical coefficient family -/

/-- **The sign-flipped canonical Faà-di-Bruno coefficients.**  `βHensel`'s `(A.1)` successor sum
carries a global minus that `betaRec`'s does not; flipping the sign of the (linear) `Bcoeff` slot
absorbs it per-term. -/
noncomputable def BcoeffSigned (H : F[X][Y]) (x₀ : F) (R : F[X][X][Y]) :
    (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H :=
  fun i₁ {_m} p => -(B_coeff H x₀ R i₁ p)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
@[simp] lemma BcoeffSigned_apply (x₀ : F) (R : F[X][X][Y]) (i₁ : ℕ) {m : ℕ}
    (p : Nat.Partition m) :
    BcoeffSigned H x₀ R i₁ p = -(B_coeff H x₀ R i₁ p) := rfl

/-! ## Definitional alignments between the two recursions -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The `W`-elements of the two developments coincide (both are
`mk (C H.leadingCoeff)` in `𝒪 H`). -/
lemma W_O_eq_W𝒪 : W_𝒪 H = W𝒪 H := rfl

/-- The `W`-exponents coincide: `betaWExp i₁ = i₁ + deltaSave i₁ − 1`
(`betaδ` and `deltaSave` are the same Kronecker delta). -/
lemma betaWExp_eq_deltaSave (i₁ : ℕ) : betaWExp i₁ = i₁ + deltaSave i₁ - 1 := rfl

/-- The `ξ`-exponents coincide: `betaξExp i₁ p = 2·i₁ + Σλ − 2`. -/
lemma betaξExp_eq_sigmaLambda (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m) :
    betaξExp i₁ p = 2 * i₁ + sigmaLambda p - 2 := rfl

/-- The Claim-A.2 normalizing exponent in closed truncated form:
`henselDenominatorExponent t = 2t − 1` (in `ℕ`-truncated subtraction, `2·0 − 1 = 0`). -/
lemma henselDenominatorExponent_eq_two_mul_sub_one (t : ℕ) :
    henselDenominatorExponent t = 2 * t - 1 := by
  cases t with
  | zero => simp [henselDenominatorExponent]
  | succ k => simp [henselDenominatorExponent]

/-- **The exclusion filters coincide.**  For `p ⊢ t+1−i₁`, avoiding the forbidden part `t+1`
(`βHensel`'s filter) is exactly avoiding the trivial pair `(i₁ = 0, λ = [t+1])`
(`betaRec`'s guard). -/
theorem notMem_succ_iff_not_trivPair {t i₁ : ℕ} (p : Nat.Partition (t + 1 - i₁)) :
    (t + 1) ∉ p.parts ↔ ¬(i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) := by
  constructor
  · rintro hnot ⟨_hi0, hparts⟩
    exact hnot (hparts ▸ Multiset.mem_singleton_self _)
  · intro hnexcl hmem
    rcases Nat.eq_zero_or_pos i₁ with hi0 | hpos
    · subst hi0
      refine hnexcl ⟨rfl, ?_⟩
      have hp : p = Nat.Partition.indiscrete (t + 1) :=
        ArkLib.Nat.Partition.eq_indiscrete_of_mem_self (Nat.succ_pos t) hmem
      rw [hp, Nat.Partition.indiscrete_parts (Nat.succ_ne_zero t)]
    · exact partition_notMem_succ_of_pos_i1 t i₁ hpos p hmem

/-! ## The bridge: `betaRec` at the signed canonical family IS `βHensel` -/

/-- **The recursion bridge.**  `betaRec` at the sign-flipped canonical coefficients agrees with
the concrete `(A.1)` recursion `βHensel` at every order.  Strong induction on `t`: the base cases
are both `mk X`; at a successor the global minus of `βHensel` is absorbed by the sign of the
`Bcoeff` slot, the exclusion filters are equivalent (`notMem_succ_iff_not_trivPair`), the `W`/`ξ`
exponents agree definitionally, and the partition products match via
`partitionProd_eq_prod_count` + the inductive hypothesis (every surviving part is `< t+1`,
`recursionStep_lt`). -/
theorem betaRec_BcoeffSigned_eq_βHensel (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) t = βHensel H x₀ R hHyp t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    cases t with
    | zero => rw [betaRec_zero, βHensel_zero]
    | succ k =>
      rw [betaRec_succ, βHensel_succ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i₁ _ => ?_
      rw [← Finset.sum_neg_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hexcl : ¬(i₁ = 0 ∧ p.parts = ({k + 1} : Multiset ℕ))
      · have hnotmem : (k + 1) ∉ p.parts := (notMem_succ_iff_not_trivPair p).mpr hexcl
        rw [dif_pos hexcl, if_pos hnotmem]
        -- align the partition products
        have hprod : (∏ l ∈ p.parts.toFinset.attach,
            betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) l.1 ^ (p.parts.count l.1))
            = partitionProd p
                (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0) := by
          rw [partitionProd_guard_eq H x₀ R hHyp k i₁ p hnotmem]
          rw [partitionProd_eq_prod_count (M := 𝒪 H) p (βHensel H x₀ R hHyp)]
          rw [show (∏ l ∈ p.parts.toFinset.attach,
              betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) l.1 ^ (p.parts.count l.1))
            = ∏ l ∈ p.parts.toFinset,
              betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) l ^ (p.parts.count l) from
            Finset.prod_attach p.parts.toFinset
              (fun l => betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) l ^ p.parts.count l)]
          refine Finset.prod_congr rfl fun l hl => ?_
          rw [ih l (recursionStep_lt p hexcl (Multiset.mem_toFinset.mp hl))]
        rw [hprod, BcoeffSigned_apply, W_O_eq_W𝒪, betaWExp_eq_deltaSave,
          betaξExp_eq_sigmaLambda]
        ring
      · have hmem : ¬((k + 1) ∉ p.parts) :=
          fun hnm => hexcl ((notMem_succ_iff_not_trivPair p).mp hnm)
        rw [dif_neg hexcl, if_neg hmem]

/-! ## Consequences: the off-centre keystone objects ARE the genuine `(A.1)` objects -/

/-- **Coefficient identification with the assembled `(A.1)` series.**  The off-centre keystone
coefficient `αFromBeta` at the signed canonical family equals the `t`-th coefficient of
`βHenselAssembled` (numerators agree by the bridge, denominators by
`henselDenominatorExponent t = 2t − 1`). -/
theorem alphaFromBeta_BcoeffSigned_eq_coeff_βHenselAssembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp (BcoeffSigned H x₀ R) t
      = PowerSeries.coeff t (βHenselAssembled H x₀ R hHyp) := by
  rw [BetaToCurveCoeffPolys.αFromBeta, βHenselAssembled, PowerSeries.coeff_mk,
    betaRec_BcoeffSigned_eq_βHensel, henselDenominatorExponent_eq_two_mul_sub_one]

/-- **The off-centre local Hensel series at the signed canonical family IS the assembled `(A.1)`
series.** -/
theorem gammaLocal_BcoeffSigned_eq_βHenselAssembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) :
    BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp (BcoeffSigned H x₀ R)
      = βHenselAssembled H x₀ R hHyp := by
  ext t
  rw [BetaToCurveCoeffPolys.coeff_gammaLocal,
    alphaFromBeta_BcoeffSigned_eq_coeff_βHenselAssembled]

/-- **THE MONIC GENUINE IDENTIFICATION.**  For monic `H`, the off-centre local Hensel series at
the signed canonical coefficients IS the genuine Hensel-lift root `gammaGenuine`: the proven
monic Faà-di-Bruno match identifies `βHenselAssembled = gammaGenuine`, and the recursion bridge
transports it to the keystone surface.  Every `gammaLocal`-field of the satisfiable off-centre
bundle becomes a statement about the genuine analytic object. -/
theorem gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp (BcoeffSigned H x₀ R)
      = gammaGenuine x₀ R H hHyp := by
  rw [gammaLocal_BcoeffSigned_eq_βHenselAssembled]
  exact (restrictedFaaDiBrunoMatch_iff_βHenselAssembled_eq_gammaGenuine
    (H := H) x₀ R hHyp).mp
    (restrictedFaaDiBrunoMatch_of_monic (H := H) x₀ R hHyp hlc)

/-- **Coefficient form of the monic identification.**  For monic `H`,
`αFromBeta … (BcoeffSigned …) t = αGenuine … t` at every order. -/
theorem alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp (BcoeffSigned H x₀ R) t
      = αGenuine H x₀ R hHyp t := by
  rw [alphaFromBeta_BcoeffSigned_eq_coeff_βHenselAssembled]
  exact (restrictedFaaDiBrunoMatch_iff_coeff_eq_αGenuine (H := H) x₀ R hHyp).mp
    (restrictedFaaDiBrunoMatch_of_monic (H := H) x₀ R hHyp hlc) t

/-- **`hrep` transport (monic).**  A genuine Prop-5.5 representative for `gammaGenuine` is
exactly the `hrep` field of the off-centre bundle at the signed canonical family.  This is the
shape the `Section5StrictDataOffcentreFin` producers consume. -/
theorem hrep_BcoeffSigned_of_genuine_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp) :
    polyToPowerSeries𝕃 H Ppoly
      = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp (BcoeffSigned H x₀ R) := by
  rw [gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic x₀ R hHyp hlc]
  exact hrepG

end BetaRecGenuineBridge

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BetaRecGenuineBridge.BcoeffSigned
#print axioms ArkLib.BetaRecGenuineBridge.notMem_succ_iff_not_trivPair
#print axioms ArkLib.BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel
#print axioms ArkLib.BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_coeff_βHenselAssembled
#print axioms ArkLib.BetaRecGenuineBridge.gammaLocal_BcoeffSigned_eq_βHenselAssembled
#print axioms ArkLib.BetaRecGenuineBridge.gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic
#print axioms ArkLib.BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic
#print axioms ArkLib.BetaRecGenuineBridge.hrep_BcoeffSigned_of_genuine_monic
