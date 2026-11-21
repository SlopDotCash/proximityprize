/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskBudget

/-! # Selecting the actual anchor values from squared locator classes -/

set_option maxRecDepth 6000
namespace ProximityGap.QuotientAnchorAllocation

open Finset QuotientMaskSelections QuotientMaskBudget
open scoped Classical
attribute [local irreducible] picked selections
variable {F : Type} [Field F] [DecidableEq F]

def tiles (r : F) (n : ℤ) (chosen : Bool) : Finset F :=
  if n=2 then {r,-r} else if n=1 then {if chosen then r else -r} else ∅

private theorem card_tiles (r : F) (n : ℤ) (chosen : Bool) :
    (tiles r n chosen).card ≤ n.toNat := by
  by_cases h : n=2
  · subst n
    simpa [tiles] using (card_le_two (a:=r) (b:=-r))
  by_cases h' : n=1
  · subst n; simp [tiles]
  simp [tiles,h,h']

omit [DecidableEq F] in
/-- Equal squared values permit at most two signs for each quotient product
and each permitted leaf signature. -/
theorem representatives {α : Type} (selections : Finset α) (value : α → F) (signature : α → V) (bucket : α → Fin 32)
    (agree : ∀ m ∈ selections, ∀ n ∈ selections, bucket m=bucket n →
      ∀ i, signature m=modes i → signature n=modes i → value m ^ 2 = value n ^ 2) :
    ∃ rep : Fin 32 → Fin 4 → F, ∀ m ∈ selections, ∀ i, signature m=modes i →
       value m=rep (bucket m) i ∨ value m= -rep (bucket m) i := by
  classical
  let choose (g : Fin 32) (i : Fin 4) :=
    if h : ∃ z ∈ selections, bucket z=g ∧ signature z=modes i then value h.choose else 0
  refine ⟨choose,?_⟩
  intro m hm i hi
  have H : ∃ z ∈ selections, bucket z=bucket m ∧ signature z=modes i := ⟨m,hm,rfl,hi⟩
  simp only [choose, dite_eq_left H]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (agree m hm H.choose H.choose_spec.1 H.choose_spec.2.1.symm
    i hi H.choose_spec.2.2)

/-- One Boolean sign per mask labels the actual value for its own mode. -/
noncomputable def sign (value : M → F) (signature : M → V) (bucket : M → Fin 32)
    (rep : Fin 32 → Fin 4 → F) (m : M) : Bool :=
  decide (∃ i, signature m = modes i ∧ value m = rep (bucket m) i)

omit [Field F] in
theorem sign_iff (value : M → F) (signature : M → V) (bucket : M → Fin 32)
    (rep : Fin 32 → Fin 4 → F) (m : M) (i : Fin 4) (hi : signature m = modes i) :
    sign value signature bucket rep m = true ↔ value m=rep (bucket m) i := by
  simp only [sign,decide_eq_true_eq]
  constructor
  · rintro ⟨j,hj,h⟩
    exact mode_injective (hj.symm.trans hi) ▸ h
  · exact fun h => ⟨i,hi,h⟩

private theorem tile_membership (val r : F) (n : ℤ) (chosen actual : Bool)
    (signOK : actual=true ↔ val=r) (possible : val=r ∨ val= -r) (allowed : admissible n chosen actual) :
    val ∈ tiles r n chosen := by
  rcases allowed with hn | ⟨hn,hs⟩
  · subst n
    simpa [tiles] using possible
  · subst n
    subst chosen
    cases actual with
    | true => simp [tiles, signOK.mp rfl]
    | false =>
      have ne : val≠r := fun h => Bool.noConfusion (signOK.mpr h)
      simp [tiles, possible.resolve_left ne]

def palette {ι : Type} [Fintype ι] (ids : ι → Fin 4) (w : ι → ℤ)
    (rep : Fin 32 → Fin 4 → F) (g : Fin 32) (b : Bool) : Finset F :=
  univ.biUnion fun i => tiles (rep g (ids i)) (w i) b

theorem palette_card {ι : Type} [Fintype ι] (ids : ι → Fin 4) (w : ι → ℤ)
    (rep : Fin 32 → Fin 4 → F) (g : Fin 32) (b : Bool) :
    (palette ids w rep g b).card ≤ ∑ i, (w i).toNat :=
  card_biUnion_le.trans (sum_le_sum fun _ _ => card_tiles ..)

theorem eligible_mode {ι : Type} [Fintype ι] [DecidableEq ι] (ids : ι ↪ Fin 4) (w : ι → ℤ)
    (s : V) (chosen actual : Bool) (h : admissible (∑ i, w i * hit s (ids i)) chosen actual) :
    ∃ i, s=modes (ids i) ∧ admissible (w i) chosen actual := by
  by_cases matchable : ∃ i, s=modes (ids i)
  · obtain ⟨i,hi⟩ := matchable
    exact ⟨i,hi,seats_eq ids w s i hi ▸ h⟩
  · push Not at matchable
    rw [seats_zero ids w s matchable] at h
    rcases h with h | ⟨h,_⟩ <;> omega

/-- The two real-valued anchor measurements enter finite palettes of the
requested sizes. Every retained mask has one common product bucket. -/
theorem allocate (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) (bucket : M → Fin 32)
    (plus minus : M → F) (B : ℕ) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 2)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 2) (budget : 128*(B : ℤ)<total u v)
    (hp : ∀ m ∈ selections, ∀ n ∈ selections, bucket m=bucket n →
      ∀ i, (signatures 4 m).1=modes i → (signatures 4 n).1=modes i → plus m ^ 2=plus n ^ 2)
    (hm : ∀ m ∈ selections, ∀ n ∈ selections, bucket m=bucket n →
      ∀ i, (signatures 4 m).2=modes i → (signatures 4 n).2=modes i → minus m ^ 2=minus n ^ 2) :
    ∃ (G : Finset M) (g : Fin 32) (P N : Finset F), B<G.card ∧ P.card≤∑ i, (u i).toNat ∧
      N.card≤∑ i, (v i).toNat ∧ ∀ m∈G, m∈selections ∧ bucket m=g ∧
      ((∃ i, (signatures 4 m).1=modes i) ∨ (∃ i, (signatures 4 m).2=modes i)) ∧
      (plus m ∈ P ∨ minus m ∈ N) := by
  let sp : M → V := fun m => (signatures 4 m).1
  let sn : M → V := fun m => (signatures 4 m).2
  obtain ⟨rp,P⟩ := representatives selections plus sp bucket hp
  obtain ⟨rn,N⟩ := representatives selections minus sn bucket hm
  let ap := sign plus sp bucket rp
  let an := sign minus sn bucket rn
  obtain ⟨cfg,hcfg⟩ := exists_bucket u v bucket ap an B hu hv budget
  refine ⟨picked u v bucket ap an cfg,cfg.2,palette Fin.castSucc u rp cfg.2 cfg.1.1,
    palette id v rn cfg.2 cfg.1.2,hcfg,palette_card ..,palette_card ..,?_⟩
  intro m hPicked
  have hMask := (mem_picked u v bucket ap an cfg m).mp hPicked
  obtain ⟨hmem,hit,hg⟩ := hMask
  refine ⟨hmem,hg,?_⟩
  rcases hit with pos | neg
  · obtain ⟨i,hi,ok⟩ := eligible_mode (Fin.castSuccEmb : Fin 3 ↪ Fin 4) u (sp m) _ _ pos
    refine ⟨.inl ⟨_,hi⟩, .inl (mem_biUnion.mpr ⟨i,mem_univ _,?_⟩)⟩
    rw [← hg]
    exact tile_membership _ _ _ _ _ (sign_iff _ _ _ _ _ _ hi) (P m hmem _ hi) ok
  · obtain ⟨i,hi,ok⟩ := eligible_mode (Function.Embedding.refl (Fin 4)) v (sn m) _ _ neg
    refine ⟨.inr ⟨_,hi⟩, .inr (mem_biUnion.mpr ⟨i,mem_univ _,?_⟩)⟩
    rw [← hg]
    exact tile_membership _ _ _ _ _ (sign_iff _ _ _ _ _ _ hi) (N m hmem _ hi) ok

#print axioms allocate
end ProximityGap.QuotientAnchorAllocation
