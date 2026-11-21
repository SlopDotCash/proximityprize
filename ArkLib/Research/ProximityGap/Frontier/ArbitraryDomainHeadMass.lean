/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ManyHeadLocatorMass
import ArkLib.Research.ProximityGap.Frontier.TranslatedSiteSeparation
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv

/-! # Exact private-head witness counts on arbitrary domains in linear-size fields

Choose the common locator after averaging the projected labels. Its roots
absorb all collisions between an evaluation site and a translated head sum.
The remaining coordinates support every private block of the pencil.
-/

set_option autoImplicit false
namespace ProximityGap.ArbitraryDomainHeadMass
open Finset ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Possible translations from the owner and target head coefficients. -/
def headSums {m : ℕ} (b : Fin m ↪ F) : Finset F :=
  univ.image (fun z : Fin m × Fin m => b z.1+b z.2)

private theorem of_separated {n h d r k : ℕ} [NeZero n] (x : Fin n ↪ F) (δ : ℝ≥0)
    (b : Fin (d+2) ↪ F) (pack : h+(d+1)*r ≤ n) (degree : h+2≤k) (pin : k≤h+r)
    (decode : (1-δ)*(n:ℝ≥0) ≤ ((h+r+1 : ℕ) : ℝ≥0))
    (prepared : ∃ t : F, t≠0 ∧ ∃ S : Finset (Fin n), S.card=h ∧
      ∀ ⦃i j : Fin n⦄, i∉S → j∉S → ∀ ⦃v w : F⦄, v∈headSums b → w∈headSums b →
        x i+t*v=x j+t*w → i=j ∧ v=w) :
    (((d+1)*(n-(h+r)) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ := by
  classical
  obtain ⟨t,_,S,hS,sep⟩ := prepared
  let initial := univ.map (initialPositions pack)
  have hc : initial.card=S.card := by simp [initial,hS]
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_map_finset_eq initial S hc
  let dom := π.toEmbedding.trans x
  rw [ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq
    π dom x (fun _ => rfl)]
  apply mass_of_projectable (L:=(d+1)*(n-(h+r))) dom δ pack degree pin decode le_rfl b
  intro key inj support
  have out {z : Fin n} (hz : z∉initial) : π z∉S := by
    rw [←hπ]
    intro hm
    obtain ⟨v,hv,eq⟩ := mem_map.mp hm
    exact hz (π.injective eq ▸ hv)
  have inside (u v : Fin (d+2)) : b u+b v∈headSums b :=
    mem_image.mpr ⟨(u,v),mem_univ _,rfl⟩
  have inject : Function.Injective (fun i => 1*key i 0+t*key i 1) := by
    intro i j eq
    obtain ⟨z,hz,u,v,k0,k1⟩ := support i
    obtain ⟨y,hy,u',v',l0,l1⟩ := support j
    change 1*key i 0+t*key i 1=1*key j 0+t*key j 1 at eq
    rw [k0,k1,l0,l1] at eq
    change 1 * -x (π z)+t * -(b u+b v) = 1 * -x (π y)+t * -(b u'+b v') at eq
    obtain ⟨site,labels⟩ := sep (out hz) (out hy) (inside u v) (inside u' v') (by linear_combination -eq)
    have pos : z=y := π.injective site
    apply inj
    funext j
    fin_cases j
    · simp [k0,l0,pos]
    · simp [k1,l1,labels]
  refine ⟨1,t,?_⟩
  have full := (@Finset.card_image_of_injective _ _ _ (Classical.decEq F) univ inject)
  simpa only [card_univ,Fintype.card_fin] using full.ge

/-- Every fresh site on every active head gives a distinct bad scalar.
For fixed head count and a positive fraction of common roots, the field
size required by the averaging inequality grows linearly with the length. -/
theorem all_fresh {n h d r k : ℕ} [NeZero n] (x : Fin n ↪ F) (δ : ℝ≥0)
    (b : Fin (d+2) ↪ F) (pack : h+(d+1)*r ≤ n) (degree : h+2≤k) (pin : k≤h+r)
    (decode : (1-δ)*(n:ℝ≥0) ≤ ((h+r+1 : ℕ) : ℝ≥0))
    (room : (univ : Finset (Fin n)).offDiag.card * (headSums b).offDiag.card ≤
      (Fintype.card F-1)*h) :
    (((d+1)*(n-(h+r)) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ := by
  apply of_separated x δ b pack degree pin decode
  exact TranslatedSiteSeparation.exists_separated x (headSums b) h (by rw [Fintype.card_fin];omega) room

/-- Distinct differences suffice in the field-size test.
For fixed head count and a positive fraction of common roots, the field
size required by the averaging inequality grows linearly with the length. -/
theorem all_fresh_of_differences {n h d r k : ℕ} [NeZero n] (x : Fin n ↪ F) (δ : ℝ≥0)
    (b : Fin (d+2) ↪ F) (pack : h+(d+1)*r ≤ n) (degree : h+2≤k) (pin : k≤h+r)
    (decode : (1-δ)*(n:ℝ≥0) ≤ ((h+r+1 : ℕ) : ℝ≥0))
    (R : Finset F) (covers : ∀ ⦃v w : F⦄, v∈headSums b → w∈headSums b → v≠w → w-v∈R)
    (room : (univ : Finset (Fin n)).offDiag.card * R.card ≤ (Fintype.card F-1)*h) :
    (((d+1)*(n-(h+r)) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ := by
  apply of_separated x δ b pack degree pin decode
  exact TranslatedSiteSeparation.exists_separated_of_differences x (headSums b) R h covers
    (by rw [Fintype.card_fin];omega) room

/-- A coefficient-independent field-size condition on any finite field.
At agreement t, each of the m heads contributes n-t+1 distinct labels. -/
theorem grid_mass {n k m t : ℕ} [NeZero n] (x : Fin n ↪ F) (δ : ℝ≥0)
    (hm : 1 ≤ m) (hk : 2≤k) (ht : k<t) (length : t≤n)
    (packing : m*(t-k+1)≤n-k+2) (agreement : (1-δ)*(n:ℝ≥0)≤t)
    (room : n^2*(m+1)^4 ≤ (Fintype.card F-1)*(k-2)) :
    ((m*(n-t+1) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  change (d+1)*(t-k+1)≤n-k+2 at packing
  have pack : k-2+(d+1)*(t-k+1)≤n := by omega
  have rr : 2≤t-k+1 := by omega
  have mm := Nat.mul_le_mul_left (d+1) rr
  have bd : d+2≤n := by omega
  let b := (Fin.castLEEmb bd).trans x
  have sumBound : (headSums b).card ≤ (d+2)*(d+2) := by
    simpa only [headSums,card_univ,Fintype.card_prod,Fintype.card_fin] using
      (card_image_le (s:=univ) (f:=fun z : Fin (d+2) × Fin (d+2) => b z.1+b z.2))
  have nr : (univ : Finset (Fin n)).offDiag.card ≤ n^2 := by simp [offDiag_card,pow_two]
  have br : (headSums b).offDiag.card ≤ (d+2)^4 := by
    rw [offDiag_card]
    exact (Nat.sub_le ..).trans ((Nat.mul_le_mul sumBound sumBound).trans_eq (by ring))
  have agree : k-2+(t-k+1)+1=t := by omega
  have raw := all_fresh (k:=k) (h:=k-2) (r:=t-k+1) x δ b pack (by omega) (by omega)
    (by simpa only [agree] using agreement) ((Nat.mul_le_mul nr br).trans room)
  rwa [show n-(k-2+(t-k+1))=n-t+1 by omega] at raw

end ProximityGap.ArbitraryDomainHeadMass
#print axioms ProximityGap.ArbitraryDomainHeadMass.all_fresh
#print axioms ProximityGap.ArbitraryDomainHeadMass.grid_mass
