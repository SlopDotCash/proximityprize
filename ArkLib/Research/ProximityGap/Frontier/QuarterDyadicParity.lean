/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Heavy edge colours on the even and odd powers of a dyadic root

Each opposite pair is one family of two edge colours. Three centres of a colour in
one exponent parity preserve a ternary signature on the opposite parity. The
signature distinguishes the numerator, denominator and complement of a locator ratio.
-/

namespace ProximityGap.QuarterDyadicParity

abbrev Edge := Fin 3 × Bool

/-- The seven site labels consist of six edge colours and the hole. The two sides of
the next opposite pair have fixed signs. On the remaining pair the centre side
determines which of its two signs is positive. -/
def signature (h : Edge) : Option Edge → Fin 3
  | none => 0
  | some e =>
    if h.1 = e.1 then 0 else
    if (e.1 = h.1+1 ∧ e.2 = false) ∨
       (e.1 ≠ h.1+1 ∧ e.2 ≠ h.2) then 1 else 2

/-- Centres from two different families separate every pair of labels. -/
theorem two_families_separate : ∀ (a b : Edge) (i j : Option Edge), a.1 ≠ b.1 →
    signature a i = signature a j → signature b i = signature b j → i = j := by
  intro a b
  obtain ⟨a,s⟩ := a
  obtain ⟨b,t⟩ := b
  fin_cases a <;> fin_cases b <;> cases s <;> cases t <;> decide

/-- Centres on both sides of one family separate all edges outside that family. -/
theorem one_family_separates_others : ∀ (k : Fin 3) (e : Edge) (j : Option Edge), e.1 ≠ k →
    signature (k,false) (some e) = signature (k,false) j →
    signature (k,true) (some e) = signature (k,true) j → some e = j := by decide

abbrev Counts := Edge → ℕ

private def family (p : Counts) (k : Fin 3) := p (k,false) + p (k,true)
/-- Number of ordinary sites of the six colours, or the sum of their changed counts. -/
def total (p : Counts) := family p 0 + family p 1 + family p 2
private def Rich (p : Counts) := ∃ a b : Edge, a.1 ≠ b.1 ∧ 3 ≤ p a ∧ 3 ≤ p b
private def Concentrated (p : Counts) (k : Fin 3) :=
  ∀ g : Fin 3, g ≠ k → ∀ side, p (g,side) ≤ 2

/-- A changed old edge has an antipodal mate of a different colour which passes
every signature imposed by three or more opposite-parity centres. -/
def CompatibleChanges (centres changes : Counts) : Prop :=
  ∀ e, 0 < changes e → ∃ j : Option Edge, some e ≠ j ∧
    ∀ a : Edge, 3 ≤ centres a → signature a (some e) = signature a j

private theorem rich_kills (p c : Counts) (hp : Rich p) (hc : CompatibleChanges p c) :
    total c = 0 := by
  have hz (e : Edge) : c e = 0 := by
    by_contra! hn
    obtain ⟨j,hj,hs⟩ := hc e (by omega)
    obtain ⟨a,b,hab,ha,hb⟩ := hp
    exact hj (two_families_separate a b (some e) j hab (hs a ha) (hs b hb))
  simp [total, family, hz]

private theorem concentrated_of_not_rich (p : Counts) (hp : ¬ Rich p) :
    ∃ k, Concentrated p k := by
  by_cases h : ∃ a, 3 ≤ p a
  · obtain ⟨a,ha⟩ := h
    refine ⟨a.1, fun g hg s => ?_⟩
    by_contra! hs
    exact hp ⟨a,(g,s),Ne.symm hg,ha,hs⟩
  · push Not at h
    exact ⟨0, fun g _ s => by have := h (g,s); omega⟩

private theorem outside_mass (p : Counts) (k : Fin 3) (hc : Concentrated p k) :
    total p ≤ family p k + 8 := by
  have h (g : Fin 3) (hg : g ≠ k) : family p g ≤ 4 :=
    Nat.add_le_add (hc g hg false) (hc g hg true)
  fin_cases k
  · have := h 1 (by decide); have := h 2 (by decide)
    change family p 0 + family p 1 + family p 2 ≤ family p 0 + 8
    omega
  · have := h 0 (by decide); have := h 2 (by decide)
    change family p 0 + family p 1 + family p 2 ≤ family p 1 + 8
    omega
  · have := h 0 (by decide); have := h 1 (by decide)
    change family p 0 + family p 1 + family p 2 ≤ family p 2 + 8
    omega

private theorem bound_on_changes (p q c : Counts) (k : Fin 3)
    (hf : 3 ≤ p (k,false)) (ht : 3 ≤ p (k,true))
    (hc : CompatibleChanges p c) (hle : ∀ e, c e ≤ q e) :
    total c ≤ family q k := by
  have zero (g : Fin 3) (hg : g ≠ k) : family c g = 0 := by
    have z (s : Bool) : c (g,s) = 0 := by
      by_contra! hn
      obtain ⟨j,hj,hs⟩ := hc (g,s) (by omega)
      exact hj (one_family_separates_others k (g,s) j hg (hs (k,false) hf) (hs (k,true) ht))
    simp only [family,z,Nat.zero_add]
  have hk : family c k ≤ family q k := Nat.add_le_add (hle _) (hle _)
  fin_cases k
  · simpa [total, zero 1 (by decide), zero 2 (by decide)] using hk
  · simpa [total, zero 0 (by decide), zero 2 (by decide)] using hk
  · simpa [total, zero 0 (by decide), zero 1 (by decide)] using hk

private theorem concentrated_bounds (p q c : Counts) {d hp : ℕ} (k : Fin 3)
    (hd : 13 ≤ d) (hholes : hp ≤ 4) (hm : total p + hp = 2*d+2)
    (hcap : ∀ e, p e + q e ≤ d) (hconc : Concentrated p k)
    (hc : CompatibleChanges p c) (hle : ∀ e, c e ≤ q e) :
    total c ≤ family q k ∧ total c ≤ 10 := by
  have hout := outside_mass p k hconc
  have h0 := hcap (k,false)
  have h1 := hcap (k,true)
  unfold family at hout
  have hd0 : 3 ≤ p (k,false) := by omega
  have hd1 : 3 ≤ p (k,true) := by omega
  have h := bound_on_changes p q c k hd0 hd1 hc hle
  refine ⟨h, ?_⟩
  unfold family at h
  omega

/-- On two equal parity classes of size `2d+2`, with four holes overall and
each edge of total size at most `d`, at most ten old double sites can change
under an antipodal pairing which satisfies all the three-centre signatures. -/
theorem at_most_ten (x y u v : Counts) {d hx hy : ℕ} (hd : 13 ≤ d)
    (hh : hx+hy=4) (hmx : total x + hx = 2*d+2) (hmy : total y + hy = 2*d+2)
    (he : ∀ e, x e + y e ≤ d) (hu : ∀ e, u e ≤ x e) (hv : ∀ e, v e ≤ y e)
    (hxv : CompatibleChanges x v) (hyu : CompatibleChanges y u) :
    total u + total v ≤ 10 := by
  have he' (e : Edge) : y e + x e ≤ d := by simpa [Nat.add_comm] using he e
  by_cases xrich : Rich x
  · have vz := rich_kills x v xrich hxv
    by_cases yrich : Rich y
    · rw [vz,rich_kills y u yrich hyu]; decide
    · obtain ⟨j,hj⟩ := concentrated_of_not_rich y yrich
      have h := (concentrated_bounds y x u j hd (by omega) hmy he' hj hyu hu).2
      omega
  · obtain ⟨i,hi⟩ := concentrated_of_not_rich x xrich
    obtain ⟨hvi,vb⟩ := concentrated_bounds x y v i hd (by omega) hmx he hi hxv hv
    by_cases yrich : Rich y
    · rw [rich_kills y u yrich hyu]; omega
    · obtain ⟨j,hj⟩ := concentrated_of_not_rich y yrich
      have huj := (concentrated_bounds y x u j hd (by omega) hmy he' hj hyu hu).1
      by_cases hij : i = j
      · subst j
        have ox := outside_mass x i hi
        have oy := outside_mass y i hj
        have h0 := he (i,false)
        have h1 := he (i,true)
        unfold family at ox oy
        omega
      · have xc := Nat.add_le_add (hi j (Ne.symm hij) false) (hi j (Ne.symm hij) true)
        have yc := Nat.add_le_add (hj i hij false) (hj i hij true)
        unfold family at hvi huj
        omega

#print axioms two_families_separate
#print axioms one_family_separates_others
#print axioms at_most_ten

end ProximityGap.QuarterDyadicParity
