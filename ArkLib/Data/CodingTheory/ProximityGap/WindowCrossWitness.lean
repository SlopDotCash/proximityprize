/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PencilSplitCount

/-!
# The cross-witness divisibility laws (#371, round 10)

The formal backbone of the window n/w-law assembly.  Every bad scalar's residual
factors as `M_γ = Z_{S_γ}·h_γ` (split part times kernel part, `deg h ≤ j`); for two
bad scalars the elimination identity

  `0 ≡ (h′Z_T − hZ_{T′})·ℓ₁R₀ + (γh′Z_T − γ′hZ_{T′})·ℓ₀R₁  (mod ℓ₀ℓ₁)`

projects to the two **cross-witness laws** (reduced fractions: `IsCoprime ℓᵢ Rᵢ`):

  `ℓ₀ ∣ h·Z_{T′} − h′·Z_T`        and        `ℓ₁ ∣ γ·h′·Z_T − γ′·h·Z_{T′}`.

These confine all witnesses to the `h`-multiplied alignment net
(`span⟨h′Z_T, ℓ₀·P_{≤j}⟩` from the first; the γ-twisted analogue from the second),
which is the structure the n/w-law's stress probes verified
(`probe_nwlaw_stress.py`: nets prune to pencils; `pencil_split_count_le` then counts).

Also here: `vanishing_prod_dvd` — the witness factorization tool (a polynomial
vanishing on an embedded finite set is divisible by the corresponding product of
linear factors).
-/

open Finset Polynomial
open scoped NNReal

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- A nonzero polynomial vanishing on the (injective) image of a finite index set is
divisible by the product of the corresponding linear factors. -/
theorem vanishing_prod_dvd (dom : Fin n ↪ F) {M : F[X]} (hM : M ≠ 0)
    {S : Finset (Fin n)} (hvan : ∀ i ∈ S, M.eval (dom i) = 0) :
    (S.prod fun i => X - C (dom i)) ∣ M := by
  have hprod : (S.prod fun i => X - C (dom i))
      = ((S.val.map dom).map fun a => X - C a).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots hM]
  have hnodup : (S.val.map dom).Nodup := S.nodup.map dom.injective
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : x ∈ S.val.map dom
  · have h1 : (S.val.map dom).count x = 1 :=
      Multiset.count_eq_one_of_mem hnodup hx
    rw [h1]
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    rw [Multiset.one_le_count_iff_mem, mem_roots hM]
    exact hvan i (Finset.mem_val.mp hi)
  · rw [Multiset.count_eq_zero_of_notMem hx]
    omega

section CrossWitness

variable (dom : Fin n ↪ F) {k w : ℕ}
variable {ℓ₀ ℓ₁ R₀ R₁ : F[X]}

open Classical in
/-- **THE CROSS-WITNESS DIVISIBILITY LAWS.**  For two factored bad-scalar residuals
`Z_S·h = ℓ₁R₀ + γ·ℓ₀R₁ − P·ℓ₀ℓ₁` and `Z_{S′}·h′ = ℓ₁R₀ + γ′·ℓ₀R₁ − P′·ℓ₀ℓ₁`
(reduced fractions: `IsCoprime ℓᵢ Rᵢ`, coprime denominators), with
`Z_T := ∏_{i ∉ S}(X − xᵢ)` the missing-set polynomials:

`ℓ₀ ∣ h·Z_{T′} − h′·Z_T`   and   `ℓ₁ ∣ γ·h′·Z_T − γ′·h·Z_{T′}`.

Mechanism: multiplying the identities by `Z_T, Z_{T′}` and cross-eliminating the
full-domain product `Z_D` leaves
`(h′Z_T − hZ_{T′})·ℓ₁R₀ + (γh′Z_T − γ′hZ_{T′})·ℓ₀R₁ ≡ 0 (mod ℓ₀ℓ₁)`;
the two reductions kill one term each. -/
theorem cross_witness_dvd
    (hcop : IsCoprime ℓ₀ ℓ₁) (hcop₀ : IsCoprime ℓ₀ R₀) (hcop₁ : IsCoprime ℓ₁ R₁)
    {S S' : Finset (Fin n)} {h h' P P' : F[X]} {γ γ' : F}
    (hid : (S.prod fun i => X - C (dom i)) * h
      = ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁))
    (hid' : (S'.prod fun i => X - C (dom i)) * h'
      = ℓ₁ * R₀ + C γ' * (ℓ₀ * R₁) - P' * (ℓ₀ * ℓ₁)) :
    ℓ₀ ∣ h * ((Finset.univ \ S').prod fun i => X - C (dom i))
        - h' * ((Finset.univ \ S).prod fun i => X - C (dom i)) ∧
    ℓ₁ ∣ C γ * (h' * ((Finset.univ \ S).prod fun i => X - C (dom i)))
        - C γ' * (h * ((Finset.univ \ S').prod fun i => X - C (dom i))) := by
  set ZS : F[X] := S.prod fun i => X - C (dom i) with hZS
  set ZS' : F[X] := S'.prod fun i => X - C (dom i) with hZS'
  set ZT : F[X] := (Finset.univ \ S).prod fun i => X - C (dom i) with hZT
  set ZT' : F[X] := (Finset.univ \ S').prod fun i => X - C (dom i) with hZT'
  -- the partition identities Z_S · Z_T = Z_D = Z_S' · Z_T'
  have hpart : ZS * ZT = ZS' * ZT' := by
    rw [hZS, hZT, hZS', hZT', mul_comm (S.prod _), mul_comm (S'.prod _),
      Finset.prod_sdiff (Finset.subset_univ S),
      Finset.prod_sdiff (Finset.subset_univ S')]
  -- the elimination identity
  have helim : (h' * ZT - h * ZT') * (ℓ₁ * R₀)
      + (C γ * (h' * ZT) - C γ' * (h * ZT')) * (ℓ₀ * R₁)
      = (P * (h' * ZT) - P' * (h * ZT')) * (ℓ₀ * ℓ₁) := by
    have e1 : ZS * h * (h' * ZT)
        = (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁)) * (h' * ZT) := by
      rw [hid]
    have e2 : ZS' * h' * (h * ZT')
        = (ℓ₁ * R₀ + C γ' * (ℓ₀ * R₁) - P' * (ℓ₀ * ℓ₁)) * (h * ZT') := by
      rw [hid']
    have e3 : ZS * h * (h' * ZT) = ZS' * h' * (h * ZT') := by
      calc ZS * h * (h' * ZT) = (ZS * ZT) * (h * h') := by ring
        _ = (ZS' * ZT') * (h * h') := by rw [hpart]
        _ = ZS' * h' * (h * ZT') := by ring
    have e4 := e1.symm.trans (e3.trans e2)
    linear_combination e4
  constructor
  · -- mod ℓ₀: the ℓ₀R₁- and ℓ₀ℓ₁-terms vanish, leaving ℓ₀ ∣ (h′Z_T − hZ_{T′})·ℓ₁R₀
    have hdvd : ℓ₀ ∣ (h' * ZT - h * ZT') * (ℓ₁ * R₀) := by
      refine ⟨(P * (h' * ZT) - P' * (h * ZT')) * ℓ₁
        - (C γ * (h' * ZT) - C γ' * (h * ZT')) * R₁, ?_⟩
      linear_combination helim
    have h1 : ℓ₀ ∣ h' * ZT - h * ZT' :=
      (hcop.mul_right hcop₀).dvd_of_dvd_mul_right hdvd
    have h2 : ℓ₀ ∣ -(h' * ZT - h * ZT') := dvd_neg.mpr h1
    rwa [neg_sub] at h2
  · -- mod ℓ₁: the ℓ₁R₀- and ℓ₀ℓ₁-terms vanish
    have hdvd : ℓ₁ ∣ (C γ * (h' * ZT) - C γ' * (h * ZT')) * (ℓ₀ * R₁) := by
      refine ⟨(P * (h' * ZT) - P' * (h * ZT')) * ℓ₀
        - (h' * ZT - h * ZT') * R₀, ?_⟩
      linear_combination helim
    have h1 := ((hcop.symm).mul_right hcop₁).dvd_of_dvd_mul_right hdvd
    have heq : C γ * (h' * ZT) - C γ' * (h * ZT')
        = C γ * (h' * ((Finset.univ \ S).prod fun i => X - C (dom i)))
          - C γ' * (h * ((Finset.univ \ S').prod fun i => X - C (dom i))) := by
      rw [hZT, hZT']
    rwa [heq] at h1

open Classical in
/-- **Witness-fraction uniqueness — the Padé property of the window.**  Two factored
residual witnesses for the SAME nonzero scalar represent one fraction:
`h·Z_{T′} = h′·Z_T`, whenever the difference sits below the modulus degree (the
window condition `j < w` makes this automatic: `deg ≤ j + w < 2w`).  Hence the
reduced witness fraction is canonical per scalar — the window is the
rational-reconstruction uniqueness regime. -/
theorem witness_fraction_unique
    (hcop : IsCoprime ℓ₀ ℓ₁) (hcop₀ : IsCoprime ℓ₀ R₀) (hcop₁ : IsCoprime ℓ₁ R₁)
    {S S' : Finset (Fin n)} {h h' P P' : F[X]} {γ : F} (hγ : γ ≠ 0)
    (hid : (S.prod fun i => X - C (dom i)) * h
      = ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁))
    (hid' : (S'.prod fun i => X - C (dom i)) * h'
      = ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P' * (ℓ₀ * ℓ₁))
    (hlt : (h * ((Finset.univ \ S').prod fun i => X - C (dom i))
        - h' * ((Finset.univ \ S).prod fun i => X - C (dom i))).natDegree
        < (ℓ₀ * ℓ₁).natDegree) :
    h * ((Finset.univ \ S').prod fun i => X - C (dom i))
      = h' * ((Finset.univ \ S).prod fun i => X - C (dom i)) := by
  obtain ⟨hd0, hd1⟩ := cross_witness_dvd dom hcop hcop₀ hcop₁ hid hid'
  -- the second law at equal scalars factors through the unit C γ
  have hd1' : ℓ₁ ∣ h * ((Finset.univ \ S').prod fun i => X - C (dom i))
      - h' * ((Finset.univ \ S).prod fun i => X - C (dom i)) := by
    have hfact : C γ * (h' * ((Finset.univ \ S).prod fun i => X - C (dom i)))
        - C γ * (h * ((Finset.univ \ S').prod fun i => X - C (dom i)))
        = C γ * -(h * ((Finset.univ \ S').prod fun i => X - C (dom i))
            - h' * ((Finset.univ \ S).prod fun i => X - C (dom i))) := by
      ring
    rw [hfact] at hd1
    have h2 : ℓ₁ ∣ C γ⁻¹ * (C γ * -(h * ((Finset.univ \ S').prod fun i =>
        X - C (dom i)) - h' * ((Finset.univ \ S).prod fun i => X - C (dom i)))) :=
      Dvd.dvd.mul_left hd1 _
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hγ, C_1, one_mul, dvd_neg] at h2
    exact h2
  have hboth : (ℓ₀ * ℓ₁) ∣ h * ((Finset.univ \ S').prod fun i => X - C (dom i))
      - h' * ((Finset.univ \ S).prod fun i => X - C (dom i)) :=
    hcop.mul_dvd hd0 hd1'
  by_contra hne
  have hne' : h * ((Finset.univ \ S').prod fun i => X - C (dom i))
      - h' * ((Finset.univ \ S).prod fun i => X - C (dom i)) ≠ 0 :=
    sub_ne_zero.mpr hne
  have := Polynomial.natDegree_le_of_dvd hboth hne'
  omega

end CrossWitness

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.vanishing_prod_dvd
#print axioms ProximityGap.WBPencil.cross_witness_dvd
#print axioms ProximityGap.WBPencil.witness_fraction_unique
