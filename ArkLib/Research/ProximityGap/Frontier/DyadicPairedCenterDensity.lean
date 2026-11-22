/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Counting protected antipodal pairs at order 256

A subset of the 128 antipodal classes with no four distinct vertices forming a
parallelogram and with at most one midpoint for proper three-term progressions
has at most eleven elements. The signed Fourier tests at the two named primes
supply the two hypotheses.
-/

namespace ProximityGap.DyadicPairedCenterDensity

abbrev G := ZMod 128

/-- A three-term progression with distinct endpoints. -/
def Progression (s : Finset G) (l c r : G) : Prop :=
  l ∈ s ∧ c ∈ s ∧ r ∈ s ∧ l ≠ r ∧ l+r = c+c

/-- Distinct unordered pairs have distinct sums. Two equal-sum distinct pairs
can only violate this condition when their four vertices are distinct. -/
def WeakSidon (s : Finset G) : Prop :=
  ∀ {a b x y : G}, a ∈ s → b ∈ s → x ∈ s → y ∈ s →
    a ≠ b → x ≠ y → a+b = x+y → (a=x ∧ b=y) ∨ (a=y ∧ b=x)

private theorem one_progression (s : Finset G) (hs : WeakSidon s)
    (hm : ∀ {a b c x y z}, Progression s a b c → Progression s x y z → b=y) :
    ∃ l c r, ∀ {a b d}, Progression s a b d →
      (a=l ∧ b=c ∧ d=r) ∨ (a=r ∧ b=c ∧ d=l) := by
  by_cases h : ∃ l c r, Progression s l c r
  · obtain ⟨l,c,r,hl⟩ := h
    refine ⟨l,c,r,?_⟩
    intro a b d hd
    have eq := hm hd hl
    rcases hd with ⟨ha,_,hd,had,hsum⟩
    rcases hl with ⟨hl,_,hr,hlr,hbase⟩
    rw [eq, ← hbase] at hsum
    rcases hs ha hd hl hr had hlr hsum with ⟨u,v⟩ | ⟨u,v⟩
    · exact .inl ⟨u,eq,v⟩
    · exact .inr ⟨u,eq,v⟩
  · exact ⟨0,0,0,fun {a b d} hd => (h ⟨a,b,d,hd⟩).elim⟩

/-- Give opposite orientations at the self-inverse distance 64 distinct tags. -/
private def tag (x y : G) : G :=
  if x-y = 64 ∧ x.val < y.val then 0 else x-y

private theorem difference_of_tag {x y u v : G} (hxy : x ≠ y) (huv : u ≠ v)
    (h : tag x y = tag u v) : x-y = u-v := by
  unfold tag at h
  split_ifs at h with hx hu hu
  · exact hx.1.trans hu.1.symm
  · exact (sub_ne_zero.mpr huv h.symm).elim
  · exact (sub_ne_zero.mpr hxy h).elim
  · exact h

set_option maxRecDepth 4096 in
private theorem tag_reverse {x y : G} (ne : x ≠ y) : tag x y ≠ tag y x := by
  intro h
  have eq := difference_of_tag ne ne.symm h
  have torsion : ∀ d : G, d+d=0 → d≠0 → d=64 := by decide
  have hx : x-y=64 := torsion _ (by linear_combination eq) (sub_ne_zero.mpr ne)
  have hv : x.val ≠ y.val := fun h => ne (ZMod.val_injective 128 h)
  unfold tag at h
  rw [hx, ← eq, hx] at h
  simp only [true_and] at h
  have nz : (64 : G) ≠ 0 := by decide
  split_ifs at h <;> first | exact nz h | exact nz h.symm | omega

/-- At most eleven antipodal classes satisfy the parallelogram and midpoint
restrictions. This uses every orientation of every pair in the finite set. -/
theorem card_le_eleven (s : Finset G) (hs : WeakSidon s)
    (hm : ∀ {a b c x y z}, Progression s a b c → Progression s x y z → b=y) :
    s.card ≤ 11 := by
  obtain ⟨l,c,r,hap⟩ := one_progression s hs hm
  let bad : Finset (G × G) := {(l,c),(c,l)}
  let good := s.offDiag \ bad
  have facts {x y : G} (h : (x,y) ∈ good) :
      x∈s ∧ y∈s ∧ x≠y ∧ (x,y)≠(l,c) ∧ (x,y)≠(c,l) := by
    obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hx,hy,ne⟩ := Finset.mem_offDiag.mp ht
    simp only [bad,Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    exact ⟨hx,hy,ne,hn⟩
  have hin : Set.InjOn (fun e : G × G => tag e.1 e.2) (good : Set (G × G)) := by
    rintro ⟨x,y⟩ he ⟨u,v⟩ hf hh
    obtain ⟨hx,hy,hxy,he₁,he₂⟩ := facts he
    obtain ⟨hu,hv,huv,hf₁,hf₂⟩ := facts hf
    have diff := difference_of_tag hxy huv hh
    have sum : x+v = y+u := by linear_combination diff
    by_cases hxv : x=v
    · subst v
      by_cases hyu : y=u
      · subst u
        exact (tag_reverse hxy hh).elim
      · rcases hap (show Progression s y x u from ⟨hy,hx,hu,hyu,sum.symm⟩) with h|h
        · exact (he₂ (Prod.ext h.2.1 h.1)).elim
        · exact (hf₁ (Prod.ext h.2.2 h.2.1)).elim
    · by_cases hyu : y=u
      · subst u
        rcases hap (show Progression s x y v from ⟨hx,hy,hv,hxv,sum⟩) with h|h
        · exact (he₁ (Prod.ext h.1 h.2.1)).elim
        · exact (hf₂ (Prod.ext h.2.1 h.2.2)).elim
      · rcases hs hx hv hy hu hxv hyu sum with ⟨u₁,_⟩|⟨u₁,u₂⟩
        · exact (hxy u₁).elim
        · exact Prod.ext u₁ u₂.symm
  have count : good.card ≤ 128 := by
    simpa using Finset.card_le_card_of_injOn (t := Finset.univ)
      (fun e : G × G => tag e.1 e.2) (fun _ _ => Finset.mem_univ _) hin
  have few : bad.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have h := Finset.card_le_card_sdiff_add_card (s := s.offDiag) (t := bad)
  change s.offDiag.card ≤ good.card + bad.card at h
  rw [Finset.offDiag_card] at h
  by_contra! hn
  have lower : 12 * 11 ≤ s.card * (s.card-1) := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.mul_sub_one] at lower
  omega

/-- The two source classes fixed modulo 128 have opposite reflection signs.
Each contributes half its squared projected coordinate to its sector metric. -/
theorem two_fixed_energy {I : Type*} [Fintype I] (u v : I → ℤ) (c d : ℤ) :
    (2 * (∑ i, (u i+v i)^2) + (2*c)^2) + (2 * (∑ i, (u i-v i)^2) + (2*d)^2) =
      4 * ((∑ i, ((u i)^2+(v i)^2)) + c^2+d^2) := by
  have h : (∑ i, (u i+v i)^2) + (∑ i, (u i-v i)^2) =
      2 * ∑ i, ((u i)^2+(v i)^2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

#print axioms card_le_eleven
#print axioms two_fixed_energy
end ProximityGap.DyadicPairedCenterDensity
