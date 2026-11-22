/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Combinatorics.Pigeonhole
import ArkLib.Research.ProximityGap.Frontier.DyadicProjectiveDescent
import ArkLib.Research.ProximityGap.Frontier.DyadicCrossRatioParity

/-! # Choosing a parity class containing three of seven projective matches -/

namespace ProximityGap.DyadicSevenCombinatorics
open Finset DyadicParityGalois
variable {K : Type*} [Field K]

/-- The four-site prohibition for an arbitrary ambient characteristic-zero field. -/
def NoQuadrants (z : K) : Prop := ∀ (a b : Fin 4 → ℕ),
  Function.Injective (fun i => z^(a i)) → Function.Injective (fun i => z^(b i)) →
  a 0%2=a 1%2 → a 2%2=a 3%2 → a 0%2≠a 2%2 → b 0%2=b 2%2 → b 1%2=b 3%2 → b 0%2≠b 1%2 →
  (z^(a 0)-z^(a 1))*(z^(a 2)-z^(a 3))*(z^(b 0)-z^(b 2))*(z^(b 1)-z^(b 3))≠
    (z^(a 0)-z^(a 2))*(z^(a 1)-z^(a 3))*(z^(b 0)-z^(b 1))*(z^(b 2)-z^(b 3))

/-- A primitive root in a larger field has the same parity exclusion as in
the cyclotomic field it generates. -/
theorem quadrants [Algebra ℚ K] {m : ℕ} (hm : 0<m) {z : K} (hz : IsPrimitiveRoot z (2^(m+1))) :
    NoQuadrants z := by
  let E := IntermediateField.adjoin ℚ ({z}:Set K)
  let w : E := ⟨z,IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
  let φ : E →+* K := E.subtype
  have wz : φ w=z := rfl
  have root : IsPrimitiveRoot w (2^(m+1)) :=
    (show IsPrimitiveRoot (φ w) (2^(m+1)) from hz).of_map_of_injective φ.injective
  let _ : Algebra ℚ E := E.algebra'
  let _ : IsCyclotomicExtension {2^(m+1)} ℚ E := (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin (2^(m+1)) ℚ K E hz).2 rfl
  intro a b ax bx e₁ e₂ e₃ f₁ f₂ f₃ eq
  have inj (x : Fin 4 → ℕ) (hx : Function.Injective (fun i => z^(x i))) :
      Function.Injective (fun i => w^(x i)) := fun _ _ h => hx (by simpa only [map_pow,wz] using congrArg φ h)
  apply DyadicCrossRatioParity.excludes_quadrants hm root a b (inj a ax) (inj b bx) e₁ e₂ e₃ f₁ f₂ f₃
  apply φ.injective
  simpa only [map_mul,map_sub,map_pow,wz] using eq

/-- Four matched finite pairs on a nonsingular projectivity have equal cross-ratios. -/
theorem cross {a b c d : K} (det : a*d≠b*c) (x y : Fin 4 → K)
    (edges : ∀ i, Graph a b c d (x i) (y i)) :
    (x 0-x 1)*(x 2-x 3)*(y 0-y 2)*(y 1-y 3)=(x 0-x 2)*(x 1-x 3)*(y 0-y 1)*(y 2-y 3) := by
  have den (i : Fin 4) : c*x i+d≠0 := by
    intro zero
    have e := edges i
    dsimp only [Graph] at e
    exact det (by linear_combination a*zero-c*e-c*y i*zero)
  have diff (i j : Fin 4) : y i-y j=(a*d-b*c)*(x i-x j)/((c*x i+d)*(c*x j+d)) := by
    apply (eq_div_iff (mul_ne_zero (den _) (den _))).mpr
    have ei := edges i;have ej := edges j
    dsimp only [Graph] at ei ej
    linear_combination -(c*x j+d)*ei+(c*x i+d)*ej
  rw [diff 0 2,diff 1 3,diff 0 1,diff 2 3]
  field_simp [den]

/-- A finite set of adequate size supplies an injection into its members. -/
theorem select {α : Type*} (S : Finset α) (k : ℕ) (enough : k≤S.card) :
    ∃ e : Fin k ↪ α, ∀ i, e i∈S := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α:=Fin k) (β:=S) (by simpa using enough)
  exact ⟨e.trans (Function.Embedding.subtype _),fun i => (e i).property⟩

/-- After multiplying source and target by at most one copy of the generator,
three of seven matched points have even exponents in both coordinates. -/
theorem majority {z a b c d : K} (blocked : NoQuadrants z) (det : a*d≠b*c)
    (A B : Fin 7 → ℕ) (injA : Function.Injective (fun i => z^(A i)))
    (injB : Function.Injective (fun i => z^(B i))) (edges : ∀ i, Graph a b c d (z^(A i)) (z^(B i))) :
    ∃ r s : ℕ, ∃ pins : Fin 3 ↪ Fin 7, ∀ i, (A (pins i)+r)%2=0 ∧ (B (pins i)+s)%2=0 := by
  classical
  let col (i : Fin 7) : Fin 2 × Fin 2 := (⟨A i%2,by omega⟩,⟨B i%2,by omega⟩)
  have miss : ∃ q, ∀ i, col i≠q := by
    by_contra! onto
    let g : (Fin 2 × Fin 2) ↪ Fin 7 := ⟨fun p => (onto p).choose,fun p q e =>
      (onto p).choose_spec.symm.trans ((congrArg col e).trans (onto q).choose_spec)⟩
    let table : Fin 4 ↪ Fin 2 × Fin 2 := ⟨![(0,0),(0,1),(1,0),(1,1)],by decide⟩
    let f := table.trans g
    have cs (i : Fin 4) : col (f i)=table i := (onto (table i)).choose_spec
    have fst (i : Fin 4) : A (f i)%2=(table i).1.val := congrArg (fun p : Fin 2 × Fin 2 => p.1.val) (cs i)
    have snd (i : Fin 4) : B (f i)%2=(table i).2.val := congrArg (fun p : Fin 2 × Fin 2 => p.2.val) (cs i)
    exact blocked (A ∘ f) (B ∘ f) (injA.comp f.injective) (injB.comp f.injective)
      ((fst 0).trans (fst 1).symm) ((fst 2).trans (fst 3).symm)
      (by change A (f 0)%2≠A (f 2)%2;rw [fst,fst];decide)
      ((snd 0).trans (snd 2).symm) ((snd 1).trans (snd 3).symm)
      (by change B (f 0)%2≠B (f 1)%2;rw [snd,snd];decide)
      (cross det (fun i => z^(A (f i))) (fun i => z^(B (f i))) (fun i => edges _))
  obtain ⟨q,hq⟩ := miss
  obtain ⟨p,_,size⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s:=(univ : Finset (Fin 7))) (t:=univ.erase q) (f:=col) (n:=2)
    (fun i _ => mem_erase.mpr ⟨hq i,mem_univ _⟩) (by simp)
  obtain ⟨pins,inP⟩ := select (univ.filter fun i => col i=p) 3 (by omega)
  refine ⟨p.1,p.2,pins,?_⟩
  intro i
  have hp := (mem_filter.mp (inP i)).2
  have ea : A (pins i)%2=p.1.val := congrArg (fun t : Fin 2 × Fin 2 => t.1.val) hp
  have eb : B (pins i)%2=p.2.val := congrArg (fun t : Fin 2 × Fin 2 => t.2.val) hp
  exact ⟨by omega,by omega⟩

end ProximityGap.DyadicSevenCombinatorics
#print axioms ProximityGap.DyadicSevenCombinatorics.quadrants
#print axioms ProximityGap.DyadicSevenCombinatorics.majority
