/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.CurveCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition
import ArkLib.Research.ProximityGap.Frontier.HigherJetBigrading

/-! # From one translated origin rank to exact agreement on every received line

The partition support bounds both derivative weight and coarse degree.
Translation in the two value coordinates preserves both bounds. Consequently
the rank at the origin suffices simultaneously for all sites, domains, and
received curves. At curve degree one the resulting certificate supplies the
full base-field exact correlated pair outside the canonical exceptional set.
-/
namespace ProximityGap.PartitionOriginCertificate

open ReedSolomon ReedSolomon.HiddenDerivative MvPolynomial PolynomialDifferential Polynomial Finset

noncomputable section

variable {F : Type} [Field F] {D d W m : ℕ} {L : ℝ}

private theorem translate_mem (hD : 0 < D) (c y : F)
    {Q : DifferentialPolynomial F d} (hQ : Q ∈ partitionSupportSpace F D d W L hD) :
    globalPointTranslation c y Q ∈ partitionSupportSpace F D d W L hD := by
  have coarse := globalPointTranslation_mem_weightedSupportSpace hD c y
    (partitionSupportSpace_le_weightedSupportSpace hD hQ)
  have weighted := globalPointTranslation_mem_restrictWeightAtMost (w := jetDerivativeWeight)
    (Nat.zero_le _) (Nat.zero_le _) c y (a := W)
    (mem_restrictWeightAtMost.mpr fun u hu => (mem_partitionSupportSpace_iff.mp hQ u hu).1)
  exact mem_partitionSupportSpace_iff.mpr fun u hu =>
    ⟨mem_restrictWeightAtMost.mp weighted u hu, (mem_weightedSupportSpace_iff.mp coarse u hu).2⟩

/-- A column of the partition-support matrix is the vector of low-contact
coefficients for one permitted monomial. -/
def pointMatrix (m : ℕ) (hD : 0 < D) (c y : F) :
    Matrix (LowContactIndex d m) ↥(partitionSupportExponents D d W L hD) F :=
  Matrix.of fun i j => localConstraintCoordinatesAt m c y ((SourceColumn.ofExponent j.val).polynomial) i

private def pointMap (m : ℕ) (hD : 0 < D) (c y : F) :
    partitionSupportSpace F D d W L hD →ₗ[F] (LowContactIndex d m → F) :=
  (localConstraintCoordinatesAt m c y).domRestrict _

private theorem rank_eq_finrank (m : ℕ) (hD : 0 < D) (c y : F) :
    (pointMatrix (d := d) (W := W) (L := L) m hD c y).rank =
    Module.finrank F (LinearMap.range (pointMap (d := d) (W := W) (L := L) m hD c y)) := by
  let S := partitionSupportExponents D d W L hD
  let b := basisRestrictSupport (R := F) (S : Set (JetVariable d →₀ ℕ))
  have eq : pointMatrix (d := d) (W := W) (L := L) m hD c y =
      Matrix.of fun i j => pointMap (d := d) (W := W) (L := L) m hD c y (b j) i := by
    ext i j
    change localConstraintCoordinatesAt m c y ((SourceColumn.ofExponent j.val).polynomial) i =
      localConstraintCoordinatesAt m c y (b j).val i
    simp only [SourceColumn.polynomial, SourceColumn.exponent_ofExponent]
    rw [show (b j : DifferentialPolynomial F d) = monomial j.val 1 from
      coe_basisRestrictSupport_apply _ j]
  rw [eq]
  exact Matrix.rank_of_basis _ _

/-- Every local matrix has rank at most the rank of the single origin matrix
over the same field. -/
theorem rank_le_origin (m : ℕ) (hD : 0 < D) (c y : F) :
    (pointMatrix (d := d) (W := W) (L := L) m hD c y).rank ≤
      (pointMatrix (d := d) (W := W) (L := L) m hD (0 : F) 0).rank := by
  rw [rank_eq_finrank, rank_eq_finrank]
  let S := partitionSupportExponents D d W L hD
  let b := basisRestrictSupport (R := F) (S : Set (JetVariable d →₀ ℕ))
  let _ : Module.Finite F (partitionSupportSpace F D d W L hD) := Module.Finite.of_basis b
  apply Submodule.finrank_mono
  rintro v ⟨Q, rfl⟩
  refine ⟨⟨globalPointTranslation c y Q.val, translate_mem hD c y Q.property⟩, ?_⟩
  ext i
  simp only [pointMap, localConstraintCoordinatesAt, LinearMap.domRestrict_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [← AlgHom.comp_apply, unscaledLocalSubstitution_comp_globalPointTranslation, add_zero, add_zero]

/-- Bounding the origin over the base field suffices for every symbolic curve.
The total rank is at most the number of sites times the origin rank. -/
theorem certificate_of_origin_rank {n A k ℓ ν r : ℕ} (hD : 0 < D) (hL : L ≤ (m*A : ℕ))
    (hkD : k ≤ D+1) (dom : Fin n ↪ F) (received : Fin n → F[X])
    (hw : ∀ i, (received i).natDegree ≤ ℓ)
    (hν : ∀ u, PartitionSupportEligible D d W L u → totalJetDegree u ≤ ν)
    (hr : (pointMatrix (d := d) (W := W) (L := L) m hD (0 : F) 0).rank ≤ r)
    (hs : n*r < (partitionSupportExponents D d W L hD).card) :
    Nonempty (SymbolicReceivedCurve.Certificate A k ℓ ν d
      (n*r*(ℓ*ν) / ((partitionSupportExponents D d W L hD).card - n*r)) dom received) := by
  classical
  let S := partitionSupportExponents D d W L hD
  let cols (j : S) := SourceColumn.ofExponent j.val
  let φ := algebraMap F[X] (RatFunc F)
  have hi : Function.Injective cols := fun a b eq => Subtype.ext (by
    simpa [cols] using congrArg SourceColumn.exponent eq)
  have hdeg (j : S) : totalJetDegree (cols j).exponent ≤ ν := by
    simpa [cols] using hν j.val (mem_partitionSupportExponents.mp j.property)
  have hy (j : S) : (cols j).y₀ ≤ ν := (by
    rw [SourceColumn.totalJetDegree_exponent]
    omega : (cols j).y₀ ≤ totalJetDegree (cols j).exponent).trans (hdeg j)
  have hband (j : S) : WeightedSupportEligible D d W L (cols j).exponent := by
    simpa [cols] using (mem_partitionSupportExponents.mp j.property).toWeightedSupportEligible
  have hmap : (pointMatrix (d := d) (W := W) (L := L) m hD (0 : F) 0).map (algebraMap F (RatFunc F)) =
      pointMatrix (d := d) (W := W) (L := L) m hD (0 : RatFunc F) 0 := by
    ext row j
    simp only [Matrix.map_apply, pointMatrix, Matrix.of_apply, localConstraintCoordinatesAt,
      lowContactCoefficients, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.pi_apply,
      lcoeff_apply]
    rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
    simp [SourceColumn.polynomial]
  have hr' : (pointMatrix (d := d) (W := W) (L := L) m hD (0 : RatFunc F) 0).rank ≤ r := by
    rw [← hmap]
    exact (Matrix.rank_map_le _ _).trans hr
  have hstack : ((supportedLocalConstraintMatrix m (fun i => Polynomial.C (dom i)) received cols).map φ).rank ≤ n*r := by
    rw [rank_map_supportedLocalConstraintMatrix, localConstraintMatrix_map]
    apply (Matrix.rank_prod_rows_le_sum _).trans
    calc
      _ ≤ ∑ _ : Fin n, r := by
        apply sum_le_sum
        intro i _
        exact (rank_le_origin (d := d) (W := W) (L := L) m hD (φ (Polynomial.C (dom i))) (φ (received i))).trans hr'
      _ = _ := by simp
  simpa [S] using SymbolicReceivedCurve.exists_certificate_of_rank_bound (K := RatFunc F)
    hL hkD dom received hw cols hi hy hdeg hband φ (RatFunc.algebraMap_injective F)
    hstack (by simpa [S] using hs)

open Classical in
/-- A single small origin rank yields exact agreement on every base-field line,
with the canonical exceptional cardinality and an explicitly bounded height. -/
theorem exact_line_of_origin_rank {n A k ν r H : ℕ} {g : ℝ}
    (hD : 0 < D) (hL : L ≤ (m*A : ℕ)) (hkD : k ≤ D + 1)
    (hν : ∀ u, PartitionSupportEligible D d W L u → totalJetDegree u ≤ ν)
    (hr : (pointMatrix (d := d) (W := W) (L := L) m hD (0 : F) 0).rank ≤ r)
    (hs : n*r < (partitionSupportExponents D d W L hD).card)
    (hH : n*r*ν / ((partitionSupportExponents D d W L hD).card - n*r) ≤ H)
    (hHpos : 0 < H) (hk : 0 < k) (hd : d < k) (hkn : k ≤ n) (hAn : A ≤ n)
    (hg : 0 < g) (hgap : (k : ℝ) + g * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (k-1) ν < ringChar F)
    (dom : Fin n ↪ F) (f w : Fin n → F) :
    ∃ E : Finset F, (E.card : ℝ) ≤ polynomialCurveProductAgreementConstant g ν H d * (n : ℝ)^(d+1) ∧
      ∀ z ∉ E, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet dom (fun i => f i + z*w i) P).card →
        HasExactCorrelatedPair dom f w (RingHom.id F) k z P := by
  classical
  let values : Fin 2 → Fin n → F := ![f,w]
  obtain ⟨cert⟩ := certificate_of_origin_rank hD hL hkD dom
    (fun i => powerBatchedCoordinate (ℓ := 1) fun j => values j i)
    (fun _ => powerBatchedCoordinate_natDegree_le _) hν hr hs
  let ι := algebraMap F (AlgebraicClosure F)
  obtain ⟨ex,hcard,hgood⟩ := exists_exceptional_exactPowerAgreement_of_certificate_of_jetCharacteristic
    dom values ι cert hk le_rfl hd hkn hAn hHpos (by simpa using hH) hg hgap hchar
  obtain ⟨E,hE,good⟩ := uniformExactPowerAgreement_of_extension dom values ι k A ex hgood
  refine ⟨E, (Nat.cast_le.mpr hE).trans (by simpa using hcard), ?_⟩
  intro z hz P hP hA
  have hw : powerBatchedWord (ℓ := 1) values z = fun i => f i + z*w i := by
    funext i
    simp [values, powerBatchedWord, Fin.sum_univ_two]
  exact exactCorrelatedPair_of_powerAgreement_one dom ![f,w] (RingHom.id F) z P
    (good z hz P hP (by rwa [hw]))

end
end ProximityGap.PartitionOriginCertificate

#print axioms ProximityGap.PartitionOriginCertificate.certificate_of_origin_rank

#print axioms ProximityGap.PartitionOriginCertificate.exact_line_of_origin_rank
