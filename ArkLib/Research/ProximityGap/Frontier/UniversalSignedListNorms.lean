/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SignedNamedLists

/-! # Half-rate signed list ceilings on every cyclic subgroup of order 2³⁰ -/

namespace ProximityGap.UniversalSignedListNorms
open QuotientMaskLocator QuotientMaskPositions QuotientMaskNorms

variable {F : Type} [Field F]

private def nrm (z : F) (j : ℕ) := (1-z^j)*(1-z^(64-j))

private theorem shifts (z : F) (hz : z^32= -1) (j : ℕ) (hj : j<32) :
    z^(64-j) = -z^(32-j) ∧ z^(64-(32-j))= -z^j := by
  constructor
  · rw [show 64-j=32+(32-j) by omega,pow_add,hz,neg_one_mul]
  · rw [show 64-(32-j)=32+j by omega,pow_add,hz,neg_one_mul]

private theorem doubled (z : F) (hz : z^32= -1) (j : ℕ) (hj : j<32) :
    nrm z (2*j) = nrm z j * nrm z (32-j) := by
  obtain ⟨h₁,h₂⟩ := shifts z hz j hj
  unfold nrm
  rw [show 64-2*j = (32-j)*2 by omega, show 2*j=j*2 by omega,
    pow_mul,pow_mul,h₁,h₂]
  ring

private theorem oriented_norms (z : F) (hz : z^32= -1) (j : ℕ) (hj : 0<j ∧ j<32)
    (b : Bool) :
    posNorm z (Fin.ofNat 64 (if b then 64-j else j)) = nrm z j ∧
    negNorm z (Fin.ofNat 64 (if b then 64-j else j)) = nrm z (32-j) := by
  obtain ⟨hl,hh⟩ := hj
  have h₁ := shifts z hz j hh
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,posNorm,negNorm,nrm,
    Fin.val_ofNat,Nat.mod_eq_of_lt (show j<64 by omega),
    Nat.mod_eq_of_lt (show 64-j<64 by omega),show 64-(64-j)=j by omega,h₁.1,h₁.2] <;>
    constructor <;> first | trivial | ring

/-- The halving tree contains only interior representatives, and every branching
representative has even exponent. -/
private def regular : ℕ → ℕ → Prop
  | 0, j => 0<j ∧ j<32
  | d+1,j => (0<j ∧ j<32) ∧ j%2=0 ∧ regular d (j/2) ∧ regular d ((64-j)/2)

private instance decRegular : (d j : ℕ) → Decidable (regular d j)
  | 0,j => inferInstanceAs (Decidable (0<j ∧ j<32))
  | d+1,j => let _ := decRegular d (j/2); let _ := decRegular d ((64-j)/2)
             inferInstanceAs (Decidable ((0<j ∧ j<32) ∧ j%2=0 ∧ regular d (j/2) ∧ regular d ((64-j)/2)))

private theorem tree (z : F) (hz : z^32= -1) (d j : ℕ) (hr : regular d j) :
    block d (weights z d j)=nrm z j ∧ ∀ p,
    posNorm z (exponent d j p) = nodeValue false d (weights z d j) (nrm z j) p ∧
    negNorm z (exponent d j p) = nodeValue true d (weights z d j) (nrm z (32-j)) p := by
  induction d generalizing j with
  | zero =>
    have hj : 0<j ∧ j<32 := hr
    refine ⟨?_,fun p => oriented_norms z hz j hj p⟩
    change (1-z^(j%64))*(1-z^(64-(j%64))) = _
    rw [Nat.mod_eq_of_lt (show j<64 by omega)]
    rfl
  | succ d ih =>
    obtain ⟨hj,he,hl,hr⟩ := hr
    obtain ⟨hL,il⟩ := ih _ hl
    obtain ⟨hR,ir⟩ := ih _ hr
    have hsub : (64-j)/2=32-j/2 := by omega
    have hsub' : 32-(64-j)/2=j/2 := by omega
    refine ⟨?_,?_⟩
    · change block d (weights z d (j/2)) * block d (weights z d ((64-j)/2)) = _
      rw [hL,hR,hsub,←doubled z hz (j/2) (by omega),show 2*(j/2)=j by omega]
    · rintro (b | (p | p))
      · exact oriented_norms z hz j hj b
      · change _ = nodeValue false d (weights z d (j/2)) (block d (weights z d (j/2))) p ∧
          _ = nodeValue true d (weights z d (j/2)) (block d (weights z d ((64-j)/2))) p
        rw [hL,hR,hsub]
        exact il p
      · change _ = nodeValue false d (weights z d ((64-j)/2)) (block d (weights z d ((64-j)/2))) p ∧
          _ = nodeValue true d (weights z d ((64-j)/2)) (block d (weights z d (j/2))) p
        rw [hL,hR,← hsub']
        exact ir p

/-- Every field root with the prescribed half-turn satisfies the complete signed norm table. -/
theorem valid (z : F) (hz : z^32= -1) : Valid z := by
  obtain ⟨top,h⟩ := tree z hz 4 16 (by decide)
  intro p
  rw [top]
  exact h p

/-- The order premise alone supplies the order-64 quotient and its half-turn. -/
theorem quotient_root (g : Fˣ) (hg : orderOf g=2^30) :
    ((g:F)^16777216)^64=1 ∧ ((g:F)^16777216)^32= -1 := by
  have h64 : ((g:F)^16777216)^64=1 := by
    rw [← pow_mul]
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    exact congrArg Units.val h
  refine ⟨h64,(sq_eq_one_iff.mp ?_).resolve_left ?_⟩
  · rw [← pow_mul]
    exact h64
  · intro h
    have hp : g^(16777216*32)=1 := Units.ext (by
      change (g:F)^(16777216*32)=1
      rwa [pow_mul])
    have small := orderOf_dvd_of_pow_eq_one hp
    rw [hg] at small
    exact (by decide : ¬(2^30 ∣ 16777216*32 : Prop)) small

open QuotientMaskBudget NamedProductionLists Finset

/-- An explicit allocation at the two anchors and the resulting production guarantees. -/
structure Row where
  plus : Fin 3 → ℤ
  minus : Fin 4 → ℤ
  gain : ℕ
  errors : ℕ
  population : ℕ

/-- Rows use from one to fourteen signed anchor values in total. -/
def profile : Fin 14 → Row := ![
  ⟨![1,0,0], ![0,0,0,0], 16777216, 486539265, 190925896⟩,
  ⟨![2,0,0], ![0,0,0,0], 8388608, 494927873, 381851792⟩,
  ⟨![2,0,0], ![1,0,0,0], 5592405, 497724076, 569069736⟩,
  ⟨![2,0,0], ![2,0,0,0], 4194304, 499122177, 756287680⟩,
  ⟨![2,1,0], ![2,0,0,0], 3355443, 499961038, 919784685⟩,
  ⟨![2,2,0], ![2,0,0,0], 2796202, 500520279, 1083281690⟩,
  ⟨![2,2,1], ![2,0,0,0], 2396745, 500919736, 1246778696⟩,
  ⟨![2,2,2], ![2,0,0,0], 2097152, 501219329, 1410275701⟩,
  ⟨![2,2,2], ![2,0,0,1], 1864135, 501452346, 1567784637⟩,
  ⟨![2,2,2], ![2,0,0,2], 1677721, 501638760, 1725293574⟩,
  ⟨![2,2,2], ![2,1,0,2], 1525201, 501791280, 1879266419⟩,
  ⟨![2,2,2], ![2,2,0,2], 1398101, 501918380, 2033239265⟩,
  ⟨![2,2,2], ![2,2,1,2], 1290555, 502025926, 2187212111⟩,
  ⟨![2,2,2], ![2,2,2,2], 1198372, 502118109, 2341184957⟩]

private theorem row_check (i : Fin 14) :
    let r := profile i
    (∀ j, 0≤r.plus j ∧ r.plus j≤2) ∧ (∀ j, 0≤r.minus j ∧ r.minus j≤2) ∧
    128*((r.population-1:ℕ):ℤ)<total r.plus r.minus ∧
    (∑ j,(r.plus j).toNat)*r.gain≤16777216 ∧ (∑ j,(r.minus j).toNat)*r.gain≤16777216 ∧
    (∑ j,(r.plus j).toNat)*r.gain+(∑ j,(r.minus j).toNat)*r.gain+(16777216-1)≤2*16777216 ∧
    64*16777216-(33*16777216+(16777216-1)+r.gain)=r.errors := by
  dsimp only
  rw [total_eq]
  revert i
  decide +kernel

/-- At every positive width and throughout all field characteristics, each table row bounds the
first failing error count for every integer budget strictly below its population. -/
theorem list_bound [DecidableEq F] (g : Fˣ) (hg : orderOf g=2^30) (i : Fin 14)
    (B width : ℕ) (hw : 0<width) (budget : B<(profile i).population) :
    Fails (h:=16777216) (r:=64) g hg 32 (profile i).errors width B := by
  let r := profile i
  obtain ⟨hu,hv,hB,hp,hn,ht,he⟩ := row_check i
  obtain ⟨h64,h32⟩ := quotient_root g hg
  rw [← he]
  apply SignedNamedLists.signed_failure g hg ((g:F)^16777216) rfl h64 h32 (valid _ h32)
      r.plus r.minus r.gain B width hw hu hv _ hp hn ht
  apply lt_of_le_of_lt _ hB
  exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast (show B≤(profile i).population-1 by omega)) (by decide)

#print axioms valid
#print axioms list_bound
end ProximityGap.UniversalSignedListNorms
