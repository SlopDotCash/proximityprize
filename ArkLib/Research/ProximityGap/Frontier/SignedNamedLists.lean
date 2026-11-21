/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientAnchorAllocation
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskPrimeNorms

/-! # Signed two-anchor lists at the two nominated half-rate radii -/

namespace ProximityGap.SignedNamedLists

open Code Finset Polynomial ReservedFiberList TwoAnchorListWitness NamedProductionLists
open QuotientMaskSelections QuotientMaskPositions QuotientMaskBudget QuotientMaskLocator

attribute [local irreducible] selections
set_option maxRecDepth 6000

variable {F : Type} [Field F] [DecidableEq F]

private abbrev fiberSize := 16777216

/-- Apply the joint signature count and the actual anchor palettes to the full cyclic code. -/
theorem signed_failure (g : Fˣ) (hg : orderOf g = fiberSize*64) (z : F)
    (hz : (g : F)^fiberSize=z) (h64 : z^64=1) (h32 : z^32= -1) (valid : Valid z)
    (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) (gain B width : ℕ) (hw : 0<width)
    (hu : ∀ i, 0≤u i ∧ u i≤2) (hv : ∀ i, 0≤v i ∧ v i≤2) (hB : 128*(B:ℤ)<total u v)
    (hP : (∑ i, (u i).toNat)*gain ≤ fiberSize)
    (hN : (∑ i, (v i).toNat)*gain ≤ fiberSize)
    (hSum : (∑ i, (u i).toNat)*gain + (∑ i, (v i).toNat)*gain + (fiberSize-1) ≤ 2*fiberSize) :
    Fails (r:=64) (h:=fiberSize) g hg 32
      (64*fiberSize-(33*fiberSize+(fiberSize-1)+gain)) width B := by
  classical
  let D := cyclicDomain g hg
  let a := cyclicLabels (by decide : 0<fiberSize) g hg
  have label (i : Fin 64) : a i = z^i.val := by
    change (g : F)^(fiberSize*i.val) = _
    rw [pow_mul,hz]
  have evaluate (m : M) (x : F) : (locator a (QuotientMaskPositions.subset m)).eval x = loc z x m := by
    simp [locator,QuotientMaskPositions.subset,eval_prod,loc,label]
  have agree (m n : M) (hm : m∈selections) (hn : n∈selections) (hb : bucket m=bucket n) :=
    anchor_classes z h64 valid m n ((mem_selections m).mp hm) ((mem_selections n).mp hn) hb
  obtain ⟨G,k,P,N,hpop,hp,hn,hG⟩ := QuotientAnchorAllocation.allocate u v bucket
    (loc z 1) (loc z (-1)) B hu hv hB
    (fun m hm n hn hb i => (agree m n hm hn hb i).1)
    (fun m hm n hn hb i => (agree m n hm hn hb i).2)
  let family := G.image QuotientMaskPositions.subset
  have shape (S) (h : S ∈ family) : S.card = 32+1 ∧ 0 ∉ S ∧ 32 ∉ S := by
    obtain ⟨m,hm,rfl⟩ := mem_image.mp h
    exact ⟨(subset_card m).trans ((mem_selections m).mp (hG m hm).1),omits m⟩
  let c := (-1:F)^33*z^(2*k.val)
  have constant (S) (h : S ∈ family) : (locator a S).eval 0 = c := by
    obtain ⟨m,hm,rfl⟩ := mem_image.mp h
    obtain ⟨hwgt,hbucket,hs,_⟩ := hG m hm
    obtain ⟨n,he⟩ := even_exponent m hs
    have hk := congrArg Fin.val hbucket
    change exponentSum m%64/2=k.val at hk
    have hres : exponentSum m%64=2*k.val := by omega
    rw [evaluate,loc]
    simp only [zero_sub, prod_neg, selected_card, (mem_selections m).mp hwgt, prod_pow_eq_pow_sum]
    change (-1:F)^33*z^(exponentSum m) = _
    rw [root_power z h64 (exponentSum m),hres]
  have anchors (S) (h : S ∈ family) : (locator a S).eval (a 0) ∈ P ∨ (locator a S).eval (a 32) ∈ N := by
    obtain ⟨m,hm,rfl⟩ := mem_image.mp h
    rw [evaluate,evaluate,label,label]
    simpa only [Fin.val_zero,pow_zero,show (32 : Fin 64).val=32 from rfl,h32] using (hG m hm).2.2.2
  have hpa := (Nat.mul_le_mul_right gain hp)
  have hna := (Nat.mul_le_mul_right gain hn)
  have lower := locator_list_lower D a (fun i => (Units.ne_zero (g^(fiberSize*i.val))))
    (cyclicDomain_pow (by decide : 0<fiberSize) g hg) 0 32 (by decide) P N family c 32 gain
    (by decide) shape constant anchors (by simpa using hpa.trans hP) (by simpa using hna.trans hN)
    (by simpa using (Nat.add_le_add_right (Nat.add_le_add hpa hna) (fiberSize-1)).trans hSum)
  have hcard : family.card = G.card := card_image_of_injective _ subset_injective
  have pop : (B:ℕ∞) < family.card := by exact_mod_cast hcard.symm ▸ hpop
  let rep (x:F) : Fin width → F := fun _ => x
  have hrep : Function.Injective rep := fun x y he => congrFun he ⟨0,hw⟩
  apply lt_of_lt_of_le _ (Lambda_le_of_injective_comp (e:=rep) hrep
    (C := (ReedSolomon.code D (32*fiberSize) : Set (Fin 64 × Fin fiberSize → F)))
    (D := interleavedCodeSet (κ:=Fin width) (ReedSolomon.code D (32*fiberSize) : Set (Fin 64 × Fin fiberSize → F)))
    (fun _ h _ => h) _)
  simpa only [Fintype.card_prod,Fintype.card_fin] using pop.trans_le lower

namespace First
open ArkLib.ProximityGap.PrizeShapePrimeP30
open QuotientMaskPrimeNorms.First
local instance : Fact P.Prime := ⟨prime_P⟩

/-- The first nominated prime has at least 1,082,868,236 distinct half-rate
codewords in a ball of 500,520,279 errors at every positive interleaving width. -/
theorem list_population (width : ℕ) (hw : 0<width) :
    Fails (r:=64) (h:=fiberSize) NamedProductionLists.First.generator NamedProductionLists.First.order
      32 500520279 width 1082868235 :=
  signed_failure _ _ QuotientMaskPrimeNorms.First.root root_eq order_factors.1 order_factors.2 valid
    ![2,0,1] ![2,1,0,0] 2796202 1082868235 width hw (by decide) (by decide)
    (by rw [first_total]; decide) (by decide) (by decide) (by decide)

theorem over_budget (width : ℕ) (hw : 0<width) :
    Fails (r:=64) (h:=fiberSize) NamedProductionLists.First.generator NamedProductionLists.First.order
      32 500520279 width (P/2^128) :=
  (show ((P/2^128 : ℕ):ℕ∞) ≤ (1082868235:ℕ∞) by decide).trans_lt (list_population width hw)
end First

namespace Second
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open QuotientMaskPrimeNorms.Second
local instance : Fact P.Prime := ⟨prime_P⟩

/-- The second nominated prime has at least 2,183,676,021 distinct half-rate
codewords in a ball of 502,025,926 errors at every positive interleaving width. -/
theorem list_population (width : ℕ) (hw : 0<width) :
    Fails (r:=64) (h:=fiberSize) NamedProductionLists.Second.generator NamedProductionLists.Second.order
      32 502025926 width 2183676020 :=
  signed_failure _ _ QuotientMaskPrimeNorms.Second.root root_eq order_factors.1 order_factors.2 valid
    ![2,2,2] ![2,2,2,1] 1290555 2183676020 width hw (by decide) (by decide)
    (by rw [second_total]; decide) (by decide) (by decide) (by decide)

theorem over_budget (width : ℕ) (hw : 0<width) :
    Fails (r:=64) (h:=fiberSize) NamedProductionLists.Second.generator NamedProductionLists.Second.order
      32 502025926 width (P/2^128) :=
  (show ((P/2^128 : ℕ):ℕ∞) ≤ (2183676020:ℕ∞) by decide).trans_lt (list_population width hw)
end Second

#print axioms First.list_population
#print axioms First.over_budget
#print axioms Second.list_population
#print axioms Second.over_budget
end ProximityGap.SignedNamedLists
