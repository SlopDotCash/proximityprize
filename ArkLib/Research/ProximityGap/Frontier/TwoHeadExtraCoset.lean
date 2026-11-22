/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoHeadExtraWitness
import ArkLib.Research.ProximityGap.Frontier.SmoothCosetFourHeadMass
import ArkLib.Research.ProximityGap.Frontier.TerminalDomainSecurity
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence

/-! # Two full secants plus one distinct scalar on smooth rate-sixteenth domains -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped ENNReal NNReal
namespace ArkLib.ProximityGap.Frontier.TwoHeadExtraCoset
open SmoothFourHeadColored SmoothFourHeadFibers TerminalDomainSecurity _root_.ProximityGap.MCAThresholdLedger

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

private def owners : Fin 8 → Fin 3 := ![1, 2, 0, 0, 0, 1, 2, 2]
private def extraClass : Finset (Fin 8) := {0, 1, 3, 6, 7}
private def outerClass : Finset (Fin 8) := {6, 7}

/-- The split cubic and a shared locator realize the two-core witness allocation. -/
theorem colored_mass (dom : I ↪ F) (hnz : ∀ x, dom x ≠ 0) (δ : ℝ≥0)
    (k D G P T : ℕ) (hD : 0 < D) (col : I → Fin 8) (seed : Fin 3 → F[X])
    (hc : ∀ j, (univ.filter (fun x => col x = j)).card = weight D G P T j)
    (hd : ∀ j, (seed j).natDegree ≤ D)
    (heq : ∀ x i j, (seed i).eval (dom x) = (seed j).eval (dom x) ↔ coincide (coarse (col x)) i j)
    (hdeg : G + D + 1 < k) (hcore : k ≤ G + 2 * D + P) (hO : k ≤ P + T) (hT : 0 < T)
    (hs : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((G + 2 * D + P + 1 : ℕ) : ℝ≥0))
    (hq : (1 + 2 * (Fintype.card I - (G + 2 * D + P))).choose 2 < Fintype.card F) :
    ((1 + 2 * (Fintype.card I - (G + 2 * D + P)):ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let select (j : Finset (Fin 8)) := univ.filter fun x => col x ∈ j
  have scard (j : Finset (Fin 8)) : (select j).card = ∑ i ∈ j, weight D G P T i := by
    rw [← sum_card_fiberwise_eq_card_filter univ j col]
    exact sum_congr rfl fun i _ => hc i
  let padding := univ.filter fun x => col x = 3
  let J := Lagrange.nodal padding (fun x => dom x)
  let f (j : Fin 3) := J * seed j
  let b (x : I) := (f (owners (col x))).eval (dom x)
  let core (j : Fin 2) := select (coreClasses j.castSucc)
  let O := univ \ (core 0 ∪ core 1)
  let E := select extraClass
  have hOeq : O = select outerClass := by
    ext x
    simp only [O, core, select, mem_sdiff, mem_filter, mem_univ, true_and, mem_union]
    exact (by decide : ∀ i, ¬(i ∈ coreClasses 0 ∨ i ∈ coreClasses 1) ↔ i ∈ outerClass) _
  have mcore (j : Fin 2) : (core j).card = G + 2 * D + P := by
    change (select _).card = _
    rw [scard]
    fin_cases j <;> simp [coreClasses, weight] <;> omega
  have mO : O.card = P + T := by rw [hOeq, scard]; simp [outerClass, weight]
  have mE : E.card = G + 2 * D + P + T := by
    change (select _).card = _
    rw [scard]; simp [extraClass, weight]; omega
  have Jdeg : J.natDegree = G := (show J.natDegree = padding.card from Lagrange.natDegree_nodal).trans (hc 3)
  have df (j : Fin 3) : (f j).natDegree ≤ G + D :=
    (natDegree_mul_le ..).trans (Nat.add_le_add Jdeg.le (hd j))
  have low (p : F[X]) (h : p.natDegree < k) : p.degree < (k:WithBot ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast h)
  have dx (j : Fin 3) : (Polynomial.X * f j).degree < (k:WithBot ℕ) := by
    apply low
    exact (natDegree_mul_le ..).trans_lt ((Nat.add_le_add natDegree_X_le (df j)).trans_lt (by omega))
  have equal (x : I) (i j : Fin 3) :
      (f i).eval (dom x) = (f j).eval (dom x) ↔ col x = 3 ∨ coincide (coarse (col x)) i j := by
    by_cases hz : col x = 3
    · have vJ : J.eval (dom x) = 0 := Lagrange.eval_nodal_at_node (mem_filter.mpr ⟨mem_univ _, hz⟩)
      simp [f, vJ, hz]
    · have vJ : J.eval (dom x) ≠ 0 := by
        apply Lagrange.eval_nodal_not_at_node
        intro y hy eq
        exact hz (dom.injective eq ▸ (mem_filter.mp hy).2)
      simp only [f, eval_mul, mul_right_inj' vJ, hz, false_or, heq]
  let a : TwoHeadExtraWitness.Arrangement dom k δ := {
    head := fun j => f j.castSucc
    q := f 2
    b := b
    core := core
    extra := E
    nz := hnz
    deg := fun j => low _ ((df j.castSucc).trans_lt (by omega))
    degX := fun j => dx j.castSucc
    degQ := low _ ((df 2).trans_lt (by omega))
    degXQ := dx 2
    pos := by omega
    rank := fun j => (mcore j) ▸ hcore
    size := fun j => (mcore j) ▸ hs
    core_iff := by
      intro x j
      change (f _).eval (dom x) = _ ↔ _ ∈ select _
      rw [equal]
      simp only [select, mem_filter, mem_univ, true_and]
      exact (by decide : ∀ s (j : Fin 2), s = 3 ∨ coincide (coarse s) (owners s) j.castSucc ↔
        s ∈ coreClasses j.castSucc) _ _
    distinct := by
      intro x h
      have ho : x ∈ O := mem_sdiff.mpr ⟨mem_univ _, h⟩
      rw [hOeq] at ho
      intro bad
      exact (by decide : ∀ s ∈ outerClass, ¬(s = 3 ∨ coincide (coarse s) 0 1)) _ (mem_filter.mp ho).2
        ((equal x 0 1).mp bad)
    out_rank := mO ▸ hO
    out_in := by
      intro x hx
      change x ∈ O at hx
      rw [hOeq] at hx
      exact mem_filter.mpr ⟨mem_univ _, (by decide : outerClass ⊆ extraClass) (mem_filter.mp hx).2⟩
    anchor := by
      have hn : 0 < (univ.filter (fun x => col x = 0)).card := by rw [hc]; exact hD
      obtain ⟨x, hx⟩ := card_pos.mp hn
      have hz := (mem_filter.mp hx).2
      refine ⟨x, mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, mem_union_right _ (mem_filter.mpr ⟨mem_univ _, ?_⟩)⟩⟩
      · rw [hz]; decide
      · rw [hz]; decide
    extra_matches := by
      intro x hx
      change (f 2).eval (dom x) = (f _).eval (dom x)
      rw [equal]
      exact (by decide : ∀ s ∈ extraClass, s = 3 ∨ coincide (coarse s) 2 (owners s)) _ (mem_filter.mp hx).2
    extra_size := hs.trans (by rw [mE]; exact_mod_cast (show G + 2 * D + P + 1 ≤ G + 2 * D + P + T by omega)) }
  have count : (1 + ∑ j, (a.core j)ᶜ.card) = 1 + 2 * (Fintype.card I - (G + 2 * D + P)) := by
    change 1 + ∑ j, (core j)ᶜ.card = _
    simp [card_compl, mcore, two_mul]
  obtain ⟨u, A, hcard, hh⟩ := TwoHeadExtraWitness.witnesses a (by rwa [count])
  rw [← count, ← hcard]
  exact MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ δ u A hh

/-- Lift an indexed three-fiber pencil to the two-head construction without enumerating the power coset. -/
theorem coset_mass {s q r : ℕ} [NeZero s] [NeZero q] (hs : 0 < s) (hr : 0 < r) (hqr : q = 16 * r)
    (dom : Fin (s * q) ↪ F) (c g : F) (hc : c ≠ 0) (hg : orderOf g = s * q)
    (hgne : g ≠ 0) (hdom : ∀ i, dom i = c * g ^ i.val)
    (k G P T : ℕ) (δ : ℝ≥0) (hpart : ∀ j, s * (univ.filter (fun i : Fin q => bucket r i.val = j)).card =
      (![3 * s, 3 * s, 3 * s, G + 3 * P + T] : Fin 4 → ℕ) j)
    (hdeg : G + 3 * s + 1 < k) (hcore : k ≤ G + 2 * (3 * s) + P) (hO : k ≤ P + T) (hT : 0 < T)
    (hsz : (1 - δ) * (s * q : ℕ) ≤ ((G + 2 * (3 * s) + P + 1 : ℕ) : ℝ≥0))
    (hq : (1 + 2 * (s * q - (G + 2 * (3 * s) + P))).choose 2 < Fintype.card F) :
    ((1 + 2 * (s * q - (G + 2 * (3 * s) + P)):ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin (s * q) → F)) δ := by
  classical
  let raw (i : Fin (s * q)) := bucket r i.modNat.val
  have count (j : Fin 4) : (univ.filter (fun i => raw i = j)).card =
      (![3 * s, 3 * s, 3 * s, G + 3 * P + T] : Fin 4 → ℕ) j := (count_blocks (fun i : Fin q => bucket r i.val) j).trans (hpart j)
  obtain ⟨col, hcol, hweight⟩ := refine_fibers raw (3 * s) G P T count
  let seed := SmoothCosetCubicSeed.seed s c⁻¹ ((g ^ s) ^ r)
  simpa only [Fintype.card_fin] using colored_mass dom (fun i => hdom i ▸ mul_ne_zero hc (pow_ne_zero _ hgne))
    δ k (3 * s) G P T (by omega) col seed hweight (fun j => SmoothCosetCubicSeed.degree _ _ _ j)
    (fun i j l => by rw [hcol]; exact SmoothCosetCubicSeed.eval_iff hs hr hqr c g hc hg dom hdom i j l)
    hdeg hcore hO hT (by simpa only [Fintype.card_fin] using hsz) (by simpa only [Fintype.card_fin] using hq)

set_option maxRecDepth 40000 in
private theorem count64 (j : Fin 4) :
    (univ.filter (fun i : Fin 64 => bucket 4 i.val = j)).card = (![3, 3, 3, 55] : Fin 4 → ℕ) j := by
  fin_cases j <;> decide

set_option maxRecDepth 10000 in
/-- The literal production construction on an indexed power coset. -/
theorem power_mass (dom : Fin n ↪ F) (c g : F) (hc : c ≠ 0) (hg : orderOf g = n)
    (hdom : ∀ i, dom i = c * g ^ i.val) {e : ℕ} (hl : 654311425 ≤ e) (hu : e ≤ 671088639)
    (hq : (2 * (e + 1) + 1).choose 2 < Fintype.card F) :
    ((2 * (e + 1) + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) ((e : ℝ≥0) / n) := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P + e = 956301313 := ⟨956301313 - e, by omega⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T + 3 * P = 905969666 := ⟨905969666 - 3 * P, by omega⟩
  have gne : g ≠ 0 := by intro h; rw [h, orderOf_zero] at hg; norm_num [n] at hg
  have mtotal : 1 + 2 * (16777216 * 64 - (16777214 + 2 * (3 * 16777216) + P)) = 2 * (e + 1) + 1 := by omega
  rw [← mtotal]
  apply coset_mass (s := 16777216) (q := 64) (r := 4) (by decide) (by decide) (by decide)
    dom c g hc hg gne hdom k 16777214 P T _ _ (by decide) (by dsimp [k]; omega)
    (by dsimp [k]; omega) (by omega) _ (by rwa [mtotal])
  · intro j
    rw [count64]
    fin_cases j <;> dsimp
    omega
  · change (1 - (e : ℝ≥0) / n) * (n : ℝ≥0) ≤ _
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num [n]), ← Nat.cast_tsub]
    exact_mod_cast (show n - e ≤ 16777214 + 2 * (3 * 16777216) + P + 1 by dsimp [n]; omega)

/-- A lower bound on each indexed power coset transfers to every smooth domain
of that cardinality, in every positive interleaving width. -/
theorem smooth_mass_of_power {m : ℕ} [NeZero m] (dom : I ↪ F) [ReedSolomon.Smooth dom]
    (hn : Fintype.card I = m) (dim : ℕ) (δ : ℝ≥0) (bound : ℝ≥0∞)
    (on_power : ∀ (base : Fin m ↪ F) (c g : F), c ≠ 0 → orderOf g = m →
      (∀ i, base i = c * g ^ i.val) →
      bound ≤ epsMCA (F := F) (ReedSolomon.code base dim : Set (Fin m → F)) δ)
    (width : ℕ) [NeZero width] :
    bound ≤ epsMCA (F := F) ((ReedSolomon.code dom dim : Set (I → F)) ^⋈ (Fin width)) δ := by
  classical
  rw [epsMCA_interleaved_eq]
  obtain ⟨sites, hsite⟩ := SmoothDomainMcaEquivalence.coset_equiv dom
  let H := ReedSolomon.Smooth.H dom
  let : Fintype H := Fintype.ofEquiv I sites
  have hcard : Nat.card H = m := by rw [Nat.card_eq_fintype_card, ← Fintype.card_congr sites, hn]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have ho := hg.trans hcard
  let powers : Fin m ≃ H := Equiv.ofBijective (fun i => g ^ i.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j h =>
      Fin.ext ((IsPrimitiveRoot.iff_orderOf.mpr ho).pow_inj i.isLt j.isLt h),
      by rw [← Nat.card_eq_fintype_card (α := H), hcard, Fintype.card_fin]⟩)
  let index := powers.trans sites.symm
  let base := index.toEmbedding.trans dom
  have generator : orderOf ((g.val : Fˣ):F) = m := orderOf_units.trans
    ((orderOf_injective H.subtype Subtype.val_injective g).trans ho)
  have heval (i : Fin m) : base i = (ReedSolomon.Smooth.a dom : F) * (g.val : Fˣ).val ^ i.val := by
    rw [show base i = dom (index i) from rfl, hsite]
    apply congrArg (_ * ·)
    change (↑((sites (sites.symm (powers i))).val):F) = _
    rw [sites.apply_symm_apply]
    rfl
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq index base dom (fun _ => rfl)]
  exact on_power base _ _ (ReedSolomon.Smooth.a dom).ne_zero generator heval

/-- Every smooth coset with arbitrary indexing admits two full heads plus scalar zero. -/
theorem smooth_mass (dom : I ↪ F) [ReedSolomon.Smooth dom] (hn : Fintype.card I = n)
    {e : ℕ} (hl : 654311425 ≤ e) (hu : e ≤ 671088639)
    (hq : (2 * (e + 1) + 1).choose 2 < Fintype.card F) (width : ℕ) [NeZero width] :
    ((2 * (e + 1) + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e : ℝ≥0) / n) := by
  exact smooth_mass_of_power dom hn _ _ _ (fun base c g hc hg hi =>
    power_mass base c g hc hg hi hl hu hq) width

/-- Each even budget in this interval fails at least one Hamming step before the
two-full-head attack alone first exceeds that budget. -/
theorem even_ceiling (dom : I ↪ F) [ReedSolomon.Smooth dom] (hn : Fintype.card I = n) {B : ℕ}
    (hB : Fintype.card F / 2 ^ 128 = B) (even : B % 2 = 0) (hl : 1308622852 ≤ B) (hu : B ≤ 1342177280)
    (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width))
    tolerance < epsMCA (F := F) C (((B / 2 - 1 : ℕ) : ℝ≥0) / n) ∧
      mcaDeltaStar (F := F) C tolerance ≤ (((B / 2 - 1 : ℕ) : ℝ≥0) / n) := by
  dsimp only
  let e := B / 2 - 1
  have he : 654311425 ≤ e := by dsimp [e]; omega
  have he' : e ≤ 671088639 := by dsimp [e]; omega
  have cnt : 2 * (e + 1) + 1 = B + 1 := by dsimp [e]; omega
  have hf : (2 * (e + 1) + 1).choose 2 < Fintype.card F := by
    have mono := Nat.choose_le_choose 2 (show 2 * (e + 1) + 1 ≤ 1342177281 by omega)
    have bnd : (1342177281 : ℕ).choose 2 < 2 ^ 128 := by norm_num [Nat.choose_two_right]
    omega
  have above : tolerance < ((2 * (e + 1) + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
    by_contra! below
    have h := (BoundarySecurityBudget.count_ratio_le_iff (Fintype.card_pos (α := F)) (by decide : 0 < 2 ^ 128)).mp
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using below)
    omega
  have bad := above.trans_le (smooth_mass dom hn he he' hf width)
  exact ⟨bad, mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms smooth_mass
#print axioms even_ceiling
#print axioms colored_mass
end ArkLib.ProximityGap.Frontier.TwoHeadExtraCoset
