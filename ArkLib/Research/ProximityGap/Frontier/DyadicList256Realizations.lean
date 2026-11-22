/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicList256

/-! # Existence of domains attaining the exact 223/256 list boundary -/

namespace ProximityGap.DyadicList256
open Code GrandChallenges
open scoped NNReal ENNReal

/-- Every dyadic divisor of p−1 has a smooth prime-field evaluation domain,
indexed directly by its exponents. -/
theorem exists_domain {p e : ℕ} [Fact p.Prime] (dvd : 2^e∣p-1) :
    ∃ D : Fin (2^e) ↪ ZMod p, Nonempty (ReedSolomon.Smooth D) := by
  classical
  obtain ⟨g,hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α:=(ZMod p)ˣ)).mp inferInstance
  have order : IsPrimitiveRoot (g:ZMod p) (p-1) := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    rw [orderOf_units,hg,Nat.card_eq_fintype_card,ZMod.card_units]
  let z := (g:ZMod p)^((p-1)/2^e)
  have root : IsPrimitiveRoot z (2^e) := IsPrimitiveRoot.pow (by
    have := (Fact.out : p.Prime).one_lt;omega) order (Nat.div_mul_cancel dvd).symm
  let H := rootsOfUnity (2^e) (ZMod p)
  let _ : Fintype H := Fintype.ofFinite H
  let f (i : Fin (2^e)) : H := root.toRootsOfUnity^i.val
  let D : Fin (2^e) ↪ ZMod p := ⟨fun i => z^i.val,fun i j eq => Fin.ext (root.pow_inj i.isLt j.isLt eq)⟩
  have value (i : Fin (2^e)) : D i=((f i).val:ZMod p) := rfl
  have inj : Function.Injective f := fun _ _ eq => D.injective
    (congrArg (fun u : H => (u.val:ZMod p)) eq)
  have size : Fintype.card H=2^e := Nat.card_eq_fintype_card.symm.trans root.card_rootsOfUnity
  have sur := ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨inj,by rw [Fintype.card_fin,size]⟩).surjective
  refine ⟨D,⟨{ H := H, a := 1, h_card_pow2 := ⟨e,Fintype.card_fin _⟩, h_coset := ?_ }⟩⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(f i).val,(f i).property,by simp [value]⟩
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨i,hi⟩ := sur ⟨g,hg⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by rw [value,hi];simp⟩

/-- Each of the three concrete prime fields has a 256-site domain with
the stated exact bound at every width. -/
def Realized (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ D : Fin 256 ↪ ZMod p, Nonempty (ReedSolomon.Smooth D) ∧ ∀ m : ℕ, 0 < m → ∀ δ : ℝ,
    (Lambda (interleavedCodeSet (κ:=Fin m) (ReedSolomon.code D 32 : Set (Fin 256 → ZMod p))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal)*(Fintype.card (ZMod p):ENNReal) ↔ δ < (223:ℝ)/256

private theorem realized {p : ℕ} [Fact p.Prime] (hp : p=Pallas.baseFieldSize ∨ p=Vesta.baseFieldSize ∨ p=P) :
    Realized p := by
  obtain ⟨band,_,dvd⟩ := named p hp
  obtain ⟨D,⟨sm⟩⟩ := exists_domain (e:=8) dvd
  exact ⟨D,⟨sm⟩,fun m hm δ => threshold band D (Fintype.card_fin _) m hm δ⟩

/-- Both Pasta fields and the 254-bit witness realize the length-256, rate-one-eighth prize endpoint. -/
theorem pasta_and_witness : Realized Pallas.baseFieldSize ∧ Realized Vesta.baseFieldSize ∧ Realized P :=
  ⟨realized (Or.inl rfl),realized (Or.inr (Or.inl rfl)),realized (Or.inr (Or.inr rfl))⟩

end ProximityGap.DyadicList256
#print axioms ProximityGap.DyadicList256.pasta_and_witness
