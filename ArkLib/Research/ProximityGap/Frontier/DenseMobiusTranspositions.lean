/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DenseMobiusRigidity
import Mathlib.Data.ZMod.Basic

/-! # A finite-field cap for non-dihedral transpositions on a coset -/

namespace ProximityGap.DenseMobiusTranspositions
open Finset
variable {I F : Type*} [Fintype I] [Field F]

/-- A trace-zero fractional-linear map with more than floor((n+1)/3)
disjoint transpositions on a multiplicative coset is negation or a scaled
reciprocal. All coefficients and sites are in the supplied field. -/
theorem dihedral {n T : ℕ} (D : I ↪ F) (order : Fintype.card I=n) {α : F} (nz : α≠0)
    (roots : ∀ i, (D i)^n=α) (cutoff : n<3*T+2)
    (units : ∀ i : ℕ, 0 < i → i ≤ n+(n-3)/3 → (i:F)≠0)
    (points : Fin (T+1) × Fin 2 ↪ I) (a b c : F) (valid : a^2+b*c≠0)
    (pairs : ∀ i, c*D (points (i,0))*D (points (i,1))-a*(D (points (i,0))+D (points (i,1)))=b) :
    a=0 ∨ c=0 ∧ b=0 := by
  classical
  let H := univ.image D
  let S := univ.image (points.trans D)
  have sub : S⊆H := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    exact mem_image_of_mem D (mem_univ _)
  have countH : H.card=n := by rw [show H=univ.image D from rfl,card_image_of_injective _ D.injective,card_univ,order]
  have countS : S.card=(T+1)*2 := by
    change (univ.image (points.trans D)).card=_
    rw [card_image_of_injective _ (points.trans D).injective,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
  let r := (H\S).card
  have counts : r+(T+1)*2=n := by simpa only [countS,countH] using card_sdiff_add_card_eq_card sub
  have gap : 3*r+2<n := by omega
  have result := DenseMobiusRigidity.rigid (r:=r) gap (fun i pos le => units i pos (by omega)) nz
    (a:=a) (b:=b) (c:=c) (d:=-a) (by intro eq;exact valid (by linear_combination -eq))
    H (H\S) countH le_rfl (fun z hz => by obtain ⟨i,_,rfl⟩ := mem_image.mp hz;exact roots i) (by
      intro z hz on
      have hs : z∈S := by by_contra missing;exact on (mem_sdiff.mpr ⟨hz,missing⟩)
      obtain ⟨⟨i,j⟩,_,rfl⟩ := mem_image.mp hs
      have e₀ : a*D (points (i,0))+b=D (points (i,1))*(c*D (points (i,0))+ -a) :=
        by linear_combination -(pairs i)
      have e₁ : a*D (points (i,1))+b=D (points (i,0))*(c*D (points (i,1))+ -a) :=
        by linear_combination -(pairs i)
      fin_cases j
      · change (a*D (points (i,0))+b)^n=α*(c*D (points (i,0))+ -a)^n
        rw [e₀,mul_pow,roots]
      · change (a*D (points (i,1))+b)^n=α*(c*D (points (i,1))+ -a)^n
        rw [e₁,mul_pow,roots])
  exact result.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.1)

/-- For prime fields the characteristic bound is automatic on every proper
multiplicative coset, since its order is a proper divisor of p−1. -/
theorem prime_coset {p n T : ℕ} [Fact p.Prime] (D : I ↪ ZMod p) (order : Fintype.card I=n)
    {α : ZMod p} (nz : α≠0) (roots : ∀ i, (D i)^n=α) (cutoff : n<3*T+2)
    (proper : n<p-1) (divides : n∣p-1)
    (points : Fin (T+1) × Fin 2 ↪ I) (a b c : ZMod p) (valid : a^2+b*c≠0)
    (pairs : ∀ i, c*D (points (i,0))*D (points (i,1))-a*(D (points (i,0))+D (points (i,1)))=b) :
    a=0 ∨ c=0 ∧ b=0 := by
  apply dihedral D order nz roots cutoff _ points a b c valid pairs
  obtain ⟨d,fac⟩ := divides
  have mult : 2≤d := by
    by_contra! small
    have sd : d=0 ∨ d=1 := by omega
    rcases sd with rfl|rfl <;> simp_all
  have bound : 2*n≤p-1 := by nlinarith
  intro i pos lo zero
  have dvd := (CharP.cast_eq_zero_iff (ZMod p) p i).mp zero
  have more := Nat.le_of_dvd pos dvd
  omega

end ProximityGap.DenseMobiusTranspositions
#print axioms ProximityGap.DenseMobiusTranspositions.dihedral
#print axioms ProximityGap.DenseMobiusTranspositions.prime_coset
