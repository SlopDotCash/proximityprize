/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # Four repeated parabola points at the dimension-one threshold -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.RepetitionFourCenterAttack
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger HalfPredecessorCoreFreshDecode

/-- The integer parameters of the four repeated points on the parabola. -/
private def center : Fin 4 → ℕ := ![1,2,4,8]
private def lo : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
private def hi : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

private abbrev Site (u : ℕ) := (Fin 4 × Fin u) ⊕ Fin (4*u)
private abbrev Edge (u : ℕ) := (Fin 4 × Fin (4*u)) ⊕ Fin 6

private def index (u : ℕ) : Site u ≃ Fin (8*u) :=
  ((finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).trans (finCongr (by omega))

private def parameter {u : ℕ} : Site u → ℕ
  | .inl (c,_) => center c
  | .inr j => 16*(j.val+1)

private def source {u : ℕ} : Edge u → Fin 4
  | .inl (c,_) => c
  | .inr p => lo p

private def tip {u : ℕ} [NeZero u] : Edge u → Site u
  | .inl (_,j) => .inr j
  | .inr p => .inl (hi p,0)

private def sumParam {u : ℕ} [NeZero u] (e : Edge u) :=
  center (source e)+parameter (tip e)

private theorem sums_injective (u : ℕ) [NeZero u] : Function.Injective (@sumParam u _) := by
  intro e f h
  have hsmall : ∀ x : Fin 4, 0<center x ∧ center x≤8 := by decide
  have hs : ∀ p, center (lo p)+center (hi p)<16 := by decide
  have hc : Function.Injective center := by decide
  have hp : Function.Injective (fun p => center (lo p)+center (hi p)) := by decide
  rcases e with ⟨i,j⟩|p <;> rcases f with ⟨i',j'⟩|p'
  · change center i+16*(j.val+1)=center i'+16*(j'.val+1) at h
    have a:=hsmall i; have b:=hsmall i'
    have hj : j=j' := Fin.ext (by omega)
    have he := hc (by omega : center i=center i')
    rw [hj,he]
  · change center i+16*(j.val+1)=center (lo p')+center (hi p') at h
    have := hs p'; omega
  · change center (lo p)+center (hi p)=center i'+16*(j'.val+1) at h
    have := hs p; omega
  · exact congrArg Sum.inr (hp h)

private theorem bounds (u : ℕ) [NeZero u] (e : Edge u) :
    sumParam e≤64*u+8 ∧ center (source e)≠parameter (tip e) := by
  rcases e with ⟨i,j⟩|p
  · have hc : ∀ q : Fin 4, center q≤8 := by decide
    have := hc i
    have := j.isLt
    change center i+16*(j.val+1)≤64*u+8 ∧ center i≠16*(j.val+1)
    omega
  · have hc : ∀ q, center (lo q)+center (hi q)≤12 ∧ center (lo q)≠center (hi q) := by decide
    have := hc p
    have hu := Nat.pos_of_ne_zero (NeZero.ne u)
    change center (lo p)+center (hi p)≤64*u+8 ∧ center (lo p)≠center (hi p)
    omega

private def copies (u : ℕ) (i : Fin 4) : Fin u ↪ Fin (8*u) :=
  ⟨fun x => index u (.inl (i,x)),fun _ _ h => (Prod.mk.inj (Sum.inl.inj ((index u).injective h))).2⟩

variable {F : Type} [Field F] [Fintype F]

/-- Four points of multiplicity `u` and `4u` singleton points on a parabola give
`16u+6` bad labels at `7u−1` errors for every dimension-one evaluation domain. -/
theorem mass {u : ℕ} [NeZero u] (dom : Fin (8*u) ↪ F)
    (hcast : ∀ a b : ℕ, a≤64*u+8 → b≤64*u+8 → (a:F)=(b:F) → a=b)
    (width : ℕ) [NeZero width] :
    ((16*u+6:ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom 1 : Set (Fin (8*u) → F)) ^⋈ (Fin width))
        (((7*u-1:ℕ):ℝ≥0)/(8*u:ℕ)) := by
  classical
  have hu := Nat.pos_of_ne_zero (NeZero.ne u)
  let v (i : Fin (8*u)) : F := parameter ((index u).symm i)
  let rows : WordStack F (Fin 2) (Fin (8*u)) := ![fun i => v i^2,v]
  let label : Edge u ↪ F := ⟨fun e => -(sumParam e:F),fun e f h =>
    sums_injective u (hcast _ _ (bounds u e).1 (bounds u f).1 (neg_injective h))⟩
  have atSite (x : Site u) : v (index u x)=(parameter x:F) := by simp [v]
  have degreeC (x : F) : (C x).degree < (1:ℕ) := by
    exact degree_le_natDegree.trans_lt (by simp)
  have event (e : Edge u) : mcaEvent (ReedSolomon.code dom 1 : Set (Fin (8*u) → F))
      (((7*u-1:ℕ):ℝ≥0)/(8*u:ℕ)) (rows 0) (rows 1) (label e) := by
    let i := source e
    let a : F := center i
    let b : F := parameter (tip e)
    let x := index u (tip e)
    let D := univ.map (copies u i)
    have hD : D.card=u := by simp [D]
    have hx : v x=b := atSite _
    have hcore (y : Fin (8*u)) (hy : y∈D) : v y=a := by
      obtain ⟨j,_,rfl⟩ := mem_map.mp hy
      exact atSite (.inl (i,j))
    have hl : label e=-(a+b) := by simp [label,sumParam,a,b,i]
    have hneq : a≠b := by
      intro he
      have hb := (bounds u e).1
      unfold sumParam at hb
      exact (bounds u e).2 (hcast _ _ (by omega) (by omega) he)
    apply mcaEvent_of_affine_core_fresh dom 1 _ rows (label e) D x (C (a^2)) (C a)
    · intro h
      exact hneq ((hcore x h).symm.trans hx)
    · exact degreeC _
    · exact degreeC _
    · rw [← C_mul,← C_add]
      exact degreeC _
    · omega
    · rw [hD,Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by positivity),← Nat.cast_tsub]
      exact_mod_cast (show 8*u-(7*u-1)≤u+1 by omega)
    · intro y hy
      change (C (a^2)).eval _=v y^2 ∧ (C a).eval _=v y
      simp [hcore y hy]
    · change (C (a^2) + C (label e)*C a).eval _=v x^2+label e*v x
      simp only [eval_add,eval_mul,eval_C,hx,hl]
      ring
    · intro he
      have h : a=v x := by simpa [rows] using congrArg Prod.snd he
      exact hneq (h.trans hx)
  rw [epsMCA_interleaved_eq]
  have hm := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code dom 1 : Set (Fin (8*u) → F)) _ rows (univ.map label) (by
      intro z hz
      obtain ⟨e,_,rfl⟩ := mem_map.mp hz
      exact event e)
  have hc : Fintype.card (Edge u)=16*u+6 := by simp [Edge]; omega
  simpa only [card_map,card_univ,hc] using hm

/-- Over a prime field the construction needs only enough room for the largest
integer pair sum. -/
theorem prime_mass {p u : ℕ} [Fact p.Prime] [NeZero u] (dom : Fin (8*u) ↪ ZMod p)
    (hp : 64*u+8<p) (width : ℕ) [NeZero width] :
    ((16*u+6:ℕ):ℝ≥0∞)/(p:ℝ≥0∞) ≤
      epsMCA (F:=ZMod p) ((ReedSolomon.code dom 1 : Set (Fin (8*u) → ZMod p)) ^⋈ (Fin width))
        (((7*u-1:ℕ):ℝ≥0)/(8*u:ℕ)) := by
  have h := mass dom (by
    intro a b ha hb he
    simpa only [ZMod.val_natCast_of_lt (ha.trans_lt hp),ZMod.val_natCast_of_lt (hb.trans_lt hp)] using
      congrArg (@ZMod.val p) he) width
  simpa only [ZMod.card] using h

local instance : Fact PrizeShapePrimeP30Second.P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- Concrete mass and strict failure at the second production prime, on any
injective domain of production length and at every positive width. -/
theorem second_prime (dom : Fin 1073741824 ↪ SecondPrimeSmoothSeed.F)
    (width : ℕ) [NeZero width] :
    let P := PrizeShapePrimeP30Second.P
    let eps := epsMCA (F:=SecondPrimeSmoothSeed.F)
      ((ReedSolomon.code dom 1 : Set (Fin 1073741824 → SecondPrimeSmoothSeed.F)) ^⋈ (Fin width))
      (939524095/1073741824)
    (2147483654:ℝ≥0∞)/P ≤ eps ∧ 1/(2:ℝ≥0∞)^128<eps := by
  let P := PrizeShapePrimeP30Second.P
  have hh := prime_mass (u:=134217728) dom (by decide) width
  let eps := epsMCA (F:=SecondPrimeSmoothSeed.F)
    ((ReedSolomon.code dom 1 : Set (Fin 1073741824 → SecondPrimeSmoothSeed.F)) ^⋈ (Fin width))
    (939524095/1073741824)
  have hmass : (2147483654:ℝ≥0∞)/P ≤ eps := by
    dsimp only [eps]
    simpa only [P,PrizeShapePrimeP30Second.P,show 16*134217728+6=2147483654 by decide,show 7*134217728-1=939524095 by decide,
      show 8*134217728=1073741824 by decide,Nat.cast_ofNat] using hh
  refine ⟨hmass,lt_of_lt_of_le ?_ hmass⟩
  by_contra! h
  have hd := (BoundarySecurityBudget.count_ratio_le_iff PrizeShapePrimeP30Second.prime_P.pos
    (by decide : 0<2^128)).mp
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h :
        ((2147483654:ℕ):ℝ≥0∞)/P ≤ 1/((2^128:ℕ):ℝ≥0∞))
  exact (by decide : ¬2147483654 ≤ P/2^128) hd

#print axioms mass
#print axioms second_prime
end ArkLib.ProximityGap.Frontier.RepetitionFourCenterAttack
