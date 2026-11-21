/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ArbitraryDomainHeadMass

/-! # Linear field-size test for prescribed prime-field domains

Use consecutive residues for the heads. Although a site may belong to any
private block, every difference of two head sums lies in one interval of
length 4m+1, independently of the ownership.
-/
set_option autoImplicit false
namespace ProximityGap.PrimeHeadDifferences
open Finset ArbitraryDomainHeadMass
open scoped NNReal ENNReal

/-- The full grid of m(n-t+1) bad scalars on every prime-field embedding,
under an explicit field-size test linear in the number of heads. -/
theorem grid_mass {p n k m t : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (δ : ℝ≥0) (heads : 1 ≤ m) (hk : 2≤k) (ht : k<t) (length : t≤n)
    (packing : m*(t-k+1)≤n-k+2) (agreement : (1-δ)*(n:ℝ≥0)≤t)
    (room : (n*n-n)*(4*m+1)≤(p-1)*(k-2)) :
    ((m*(n-t+1) : ℕ) : ℝ≥0∞)/(p : ℝ≥0∞) ≤
      epsMCA (F:=ZMod p) (ReedSolomon.code x k : Set (Fin n → ZMod p)) δ := by
  classical
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  change (d+1)*(t-k+1)≤n-k+2 at packing
  have pack : k-2+(d+1)*(t-k+1)≤n := by omega
  have rr : 2≤t-k+1 := by omega
  have mm := Nat.mul_le_mul_left (d+1) rr
  have bd : d+2≤n := by omega
  have fieldRoom : n≤p := by simpa using Fintype.card_le_of_injective _ x.injective
  let b : Fin (d+2) ↪ ZMod p := ⟨fun j => (j.val:ZMod p),fun u v eq => by
    apply Fin.ext
    simpa only [ZMod.val_natCast_of_lt (u.isLt.trans_le (bd.trans fieldRoom)),
      ZMod.val_natCast_of_lt (v.isLt.trans_le (bd.trans fieldRoom))] using congrArg ZMod.val eq⟩
  let shift := 2*(d+1)
  let R : Finset (ZMod p) := (range (2*shift+1)).image (fun j : ℕ => (j:ZMod p) - (shift:ZMod p))
  have covers : ∀ ⦃v w : ZMod p⦄, v∈headSums b → w∈headSums b → v≠w → w-v∈R := by
    rintro v w hv hw _
    obtain ⟨⟨a,c⟩,_,rfl⟩ := mem_image.mp hv
    obtain ⟨⟨u,z⟩,_,rfl⟩ := mem_image.mp hw
    have left : a.val+c.val ≤ shift := by dsimp [shift];omega
    have right : u.val+z.val ≤ shift := by dsimp [shift];omega
    refine mem_image.mpr ⟨(u.val+z.val+shift)-(a.val+c.val),mem_range.mpr (by omega),?_⟩
    change (((u.val+z.val+shift-(a.val+c.val):ℕ):ZMod p)-shift) =
      (u.val:ZMod p)+z.val-((a.val:ZMod p)+c.val)
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have supply : (univ : Finset (Fin n)).offDiag.card*R.card≤(Fintype.card (ZMod p)-1)*(k-2) := by
    have rc : R.card≤2*shift+1 := by
      unfold R
      exact (card_image_le (s:=range (2*shift+1)) (f:=fun j : ℕ => (j:ZMod p) - (shift:ZMod p))).trans_eq (card_range _)
    rw [offDiag_card,card_univ,Fintype.card_fin,ZMod.card]
    apply (Nat.mul_le_mul_left _ rc).trans
    simpa only [shift,show 2*(2*(d+1))=4*d.succ by omega] using room
  have agree : k-2+(t-k+1)+1=t := by omega
  have raw := all_fresh_of_differences (k:=k) (h:=k-2) (r:=t-k+1) x δ b pack
    (by omega) (by omega) (by simpa only [agree] using agreement) R covers supply
  simpa only [show n-(k-2+(t-k+1))=n-t+1 by omega,ZMod.card] using raw

end ProximityGap.PrimeHeadDifferences
#print axioms ProximityGap.PrimeHeadDifferences.grid_mass
