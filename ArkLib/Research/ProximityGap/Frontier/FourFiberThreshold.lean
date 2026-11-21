/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourSupportSpectrum

/-! # Sharp four-decoder constructions on four polynomial fibers -/
set_option autoImplicit false
namespace ProximityGap.FourFiberThreshold
open Finset Polynomial
open scoped NNReal
variable {F : Type} [Field F] [DecidableEq F]

private theorem coordinates (i m : Fin 4) (h : m≠i) : m=i+1 ∨ m=i+2 ∨ m=i+3 := by
  fin_cases i <;> fin_cases m <;> first | exact False.elim (h rfl) | decide

private def sites {h : ℕ} (D : (Fin 4 × Fin h) ↪ F) (T : Fin 4 → Finset (Fin h)) :
    (Σ m, ↥(T m)) ↪ F where
  toFun j := D (j.1,j.2.1)
  inj' := by
    rintro ⟨m,j⟩ ⟨m',j'⟩ he
    obtain ⟨eq,ev⟩ := Prod.mk.inj (D.injective he)
    change m=m' at eq
    change j.1=j'.1 at ev
    subst m'
    rw [Subtype.ext ev]

/-- Exact agreement sets for all four decoding polynomials, including the
literal MCA event at the corresponding radii. The extra common sites can be
specified independently in each fiber. -/
def Realizes (h : ℕ) (D : (Fin 4 × Fin h) ↪ F) (γ : Fin 4 → F) (T : Fin 4 → Finset (Fin h)) : Prop :=
    ∃ (u v : F → F) (f : Fin 4 → F[X]), (∀ i, (f i).natDegree < 2*h) ∧
      (∀ i m j, (f i).eval (D (m,j))=u (D (m,j))+γ i*v (D (m,j)) ↔ m≠i ∨ j∈T m) ∧
      ∀ (i : Fin 4) (δ : ℝ≥0), (1-δ)*(4*h : ℕ) ≤ (3*h+(T i).card : ℕ) →
        mcaEvent (F := F) (ReedSolomon.code D (2*h) : Set ((Fin 4 × Fin h) → F)) δ (u ∘ D) (v ∘ D) (γ i)

/-- Four fixed disjoint fibers carry four literal MCA-bad labels with any
prescribed common agreements whose total is less than `h`. -/
theorem construct (h : ℕ) (T : Fin 4 → Finset (Fin h)) (hl : ∑ i, (T i).card<h) (H : F[X]) (hd : H.natDegree=h)
    (D : (Fin 4 × Fin h) ↪ F) (α : Fin 4 → F) (hi : Function.Injective α)
    (hf : ∀ (m : Fin 4) (j : Fin h), H.eval (D (m,j))=α m) :
    Realizes h D α T := by
  classical
  have hh : 0<h := by omega
  let Z := univ.map (sites D T)
  let M := Lagrange.nodal Z id
  have mn : M≠0 := Lagrange.nodal_ne_zero
  have md : M.natDegree=∑ i, (T i).card := by simp [M,Z,Lagrange.natDegree_nodal,Fintype.card_sigma]
  have hn : H≠0 := by rintro rfl; simp at hd; omega
  have zero (m : Fin 4) (j : Fin h) : M.eval (D (m,j))=0 ↔ j∈T m := by
    constructor
    · intro z
      by_contra miss
      have nq : D (m,j) ∉ Z := by
        intro hin
        obtain ⟨⟨a,b⟩,_,he⟩ := mem_map.mp hin
        obtain ⟨e,f⟩ := Prod.mk.inj (D.injective he)
        change a=m at e
        change b.1=j at f
        subst a
        exact miss (f ▸ b.2)
      exact (Lagrange.eval_nodal_not_at_node (s:=Z) (v:=id) (x:=D (m,j)) (fun a ha e => nq (e ▸ ha))) z
    · intro hit
      apply Lagrange.eval_nodal_at_node (s:=Z) (v:=id) (i:=(D (m,j)))
      exact mem_map.mpr ⟨⟨m,⟨j,hit⟩⟩,mem_univ _,rfl⟩
  let s := α 0+α 1+α 2+α 3
  have cyclic (i : Fin 4) : s=α i+α (i+1)+α (i+2)+α (i+3) := by
    fin_cases i <;> norm_num [s] <;> ring
  let t := fun i : Fin 4 => α (i+1)*α (i+2)*α (i+3)
  let b := fun i : Fin 4 => α (i+1)*α (i+2)+α (i+1)*α (i+3)+α (i+2)*α (i+3)
  let f := fun i => M*(C (t i)-C (b i)*H)
  let V := M*H^2
  let u := fun x => M.eval x*((H.eval x)^3-s*(H.eval x)^2)
  let v := fun x => V.eval x
  have fd (i : Fin 4) : (f i).natDegree<2*h := by
    have inner : (C (t i)-C (b i)*H).natDegree≤h := (natDegree_sub_le ..).trans
      (max_le (by simp) ((natDegree_C_mul_le ..).trans hd.le))
    exact (natDegree_mul_le ..).trans_lt (by omega)
  have vd : V.natDegree=(∑ i, (T i).card)+2*h := by rw [show V=M*H^2 by rfl,natDegree_mul mn (pow_ne_zero _ hn),natDegree_pow,md,hd]
  have fit (i m : Fin 4) (j : Fin h) :
      (f i).eval (D (m,j))=u (D (m,j))+α i*v (D (m,j)) ↔ m≠i ∨ j∈T m := by
    have diff : (u (D (m,j))+α i*v (D (m,j)))-(f i).eval (D (m,j)) =
        M.eval (D (m,j))*(α m-α (i+1))*(α m-α (i+2))*(α m-α (i+3)) := by
      simp only [u,v,V,f,eval_mul,eval_pow,eval_sub,eval_C,hf,cyclic i,t,b]
      ring
    rw [eq_comm,← sub_eq_zero,diff]
    simp only [mul_eq_zero,sub_eq_zero,hi.eq_iff,zero]
    constructor
    · intro hem
      by_cases eq : m=i
      · subst m
        have n1 : i≠i+1 := by fin_cases i <;> decide
        have n2 : i≠i+2 := by fin_cases i <;> decide
        have n3 : i≠i+3 := by fin_cases i <;> decide
        tauto
      · exact Or.inl eq
    · rintro (hn|ht)
      · have e := coordinates i m hn
        tauto
      · tauto
  refine ⟨u,v,f,fd,fit,?_⟩
  intro i δ hr
  let S := ((univ.erase i) ×ˢ (univ : Finset (Fin h))) ∪ ({i} ×ˢ T i)
  have sm (m : Fin 4) (j : Fin h) : (m,j) ∈ S ↔ m≠i ∨ j∈T m := by
    by_cases he : m=i
    · simp [S,he]
    · simp [S,he]
  have sc : S.card=3*h+(T i).card := by
    have ds : Disjoint ((univ.erase i) ×ˢ (univ : Finset (Fin h))) ({i} ×ˢ T i) := by
      rw [disjoint_left]
      rintro ⟨m,j⟩ h1 h2
      exact (mem_erase.mp (mem_product.mp h1).1).1 (mem_singleton.mp (mem_product.mp h2).1)
    dsimp [S]
    rw [card_union_of_disjoint ds]
    simp [card_erase_of_mem]
  refine ⟨S,?_,⟨fun j => (f i).eval (D j),ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _ (fd i) (fun _ => rfl),?_⟩,?_⟩
  · simpa [sc,Nat.cast_add,Nat.cast_mul] using hr
  · rintro ⟨m,j⟩ hs
    exact (fit i m j).mpr ((sm m j).mp hs)
  · rintro ⟨_,_,w,hw,hj⟩
    let _ : NeZero (2*h) := ⟨by omega⟩
    obtain ⟨W,wd,ew⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
    have ne : V-W≠0 := by intro hn; have eq := congrArg natDegree (sub_eq_zero.mp hn); omega
    have sub : S.map D ⊆ (V-W).roots.toFinset := by
      intro x hx
      obtain ⟨j,hjS,rfl⟩ := mem_map.mp hx
      rw [Multiset.mem_toFinset,mem_roots ne]
      change (V-W).eval (D j)=0
      rw [eval_sub,ew]
      exact sub_eq_zero.mpr (hj j hjS).2.symm
    have bound := (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))
    rw [card_map,sc] at bound
    have sz := natDegree_sub_le V W
    omega

/-- For four distinct labels on four complete fibers, every genuine realization
has fewer than `h` common sites in total. -/
theorem necessary (h : ℕ) (T : Fin 4 → Finset (Fin h)) (H : F[X]) (hm : H.Monic) (hd : H.natDegree=h)
    (D : (Fin 4 × Fin h) ↪ F) (α γ : Fin 4 → F)
    (hi : Function.Injective α) (hg : Function.Injective γ)
    (hf : ∀ (m : Fin 4) (j : Fin h), H.eval (D (m,j))=α m)
    (real : Realizes h D γ T) : (∑ i, (T i).card)<h ∧ FourSupportSpectrum.ratio γ=FourSupportSpectrum.ratio α := by
  classical
  obtain ⟨u,v,f,fd,fit,event⟩ := real
  let U := fun i : Fin 4 => (univ : Finset (Fin h)).image (fun j => D (i,j))
  let Z := univ.map (sites D T)
  have uc (i : Fin 4) : (U i).card=h := by
    have inj : Function.Injective (fun j : Fin h => D (i,j)) := fun _ _ h => (Prod.mk.inj (D.injective h)).2
    simp [U,card_image_of_injective _ inj]
  have zc : Z.card=∑ i, (T i).card := by simp [Z,Fintype.card_sigma]
  have hh : 0<h := by have := fd 0; omega
  let _ : NeZero h := ⟨by omega⟩
  have nall : ∃ m≠(1 : Fin 4), ∃ j : Fin h, j∉T m := by
    by_contra! all
    obtain ⟨S,_,_,no⟩ := event 0 1 (by simp)
    let E := fun (i : Fin 4) (x : Fin 4 × Fin h) => (f i).eval (D x)
    have word (i : Fin 4) : E i ∈ ReedSolomon.code D (2*h) :=
      ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (f i) (fd i) (fun _ => rfl)
    have global (i : Fin 4) (h1 : i≠1) (x : Fin 4 × Fin h) : E i x=(u ∘ D) x+γ i • (v ∘ D) x := by
      obtain ⟨m,j⟩ := x
      apply (fit i m j).mpr
      by_cases eq : m=i
      · subst m
        exact Or.inr (all i h1 j)
      · exact Or.inl eq
    let C₀ := ReedSolomon.code D (2*h)
    let W := fun i => (u ∘ D)+γ i • (v ∘ D)
    have mw (i : Fin 4) (h1 : i≠1) : W i∈C₀ := by
      have e : E i=W i := funext (global i h1)
      exact e ▸ word i
    have vmem : v ∘ D ∈ C₀ := by
      have mm := C₀.smul_mem (γ 0-γ 2)⁻¹ (C₀.sub_mem (mw 0 (by decide)) (mw 2 (by decide)))
      have he : (γ 0-γ 2)⁻¹ • (W 0-W 2)=v ∘ D := by
        dsimp only [W]
        rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, inv_mul_cancel₀
          (sub_ne_zero.mpr (hg.ne (by decide : (0 : Fin 4)≠2))),one_smul]
      exact he ▸ mm
    have umem : u ∘ D ∈ C₀ := by simpa [W] using C₀.sub_mem (mw 0 (by decide)) (C₀.smul_mem (γ 0) vmem)
    exact no ⟨u ∘ D,umem,v ∘ D,vmem,fun _ _ => ⟨rfl,rfl⟩⟩
  obtain ⟨m,nm,j,hj⟩ := nall
  have fh (i : Fin 4) (x : F) (hx : x∈U i) : H.eval x=α i := by
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact hf i a
  have off (i : Fin 4) (x : F) (hx : x∈U i) (l : Fin 4) (hl : l≠i) : (f l).eval x=u x+γ l*v x := by
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact (fit l i a).mpr (Or.inl hl.symm)
  have miss : ∃ i≠(1 : Fin 4), ∃ x∈U i, (f i).eval x≠u x+γ i*v x := by
    refine ⟨m,nm,D (m,j),mem_image.mpr ⟨j,mem_univ _,rfl⟩,?_⟩
    exact fun he => hj (((fit m m j).mp he).resolve_left (by simp))
  have res := FourSupportSpectrum.four_fits_common_lt h hh H hm hd U α hi uc fh γ hg f fd u v off miss Z (by
    intro x hx l
    obtain ⟨⟨m,j⟩,_,rfl⟩ := mem_map.mp hx
    exact (fit l m j.1).mpr (Or.inr j.2))
  exact ⟨by omega,FourSupportSpectrum.four_fits_fiber_ratio h hh H hm hd U α hi uc fh γ hg f fd u v off miss⟩

/-- The exact four-fiber criterion depends only on the total number of
prescribed common agreements, witnessed by the four fiber values themselves.
The construction and upper bound allow arbitrary fields and embeddings. -/
theorem threshold (h : ℕ) (T : Fin 4 → Finset (Fin h)) (H : F[X]) (hm : H.Monic) (hd : H.natDegree=h)
    (D : (Fin 4 × Fin h) ↪ F) (α : Fin 4 → F) (hi : Function.Injective α)
    (hf : ∀ (m : Fin 4) (j : Fin h), H.eval (D (m,j))=α m) :
    Realizes h D α T ↔ (∑ i, (T i).card)<h :=
  ⟨fun he => (necessary h T H hm hd D α α hi hi hf he).1, fun hl => construct h T hl H hd D α hi hf⟩

#print axioms necessary
#print axioms threshold

#print axioms construct
end ProximityGap.FourFiberThreshold
