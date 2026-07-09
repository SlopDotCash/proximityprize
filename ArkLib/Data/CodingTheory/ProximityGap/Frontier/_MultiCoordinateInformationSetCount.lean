/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RSVanishingDim
import Mathlib.Data.Nat.Choose.Basic

/-!
# Counting information sets in a polynomial subspace

Two reusable pieces of the multi-coordinate rank-reduction argument are isolated here.

* `card_add_finrank_le_of_vanish` is the generalized-MDS zero bound.  If a nonzero
  `r`-dimensional subspace of degree-`< k` polynomials vanishes on `S`, then
  `|S| + r ≤ k`.
* `choose_le_card_layer_of_extension` is the exact abstract basis-count recurrence.  If every
  independent `i`-set has at least `m+d-i` independent one-point extensions, then the number of
  independent `d`-sets is at least `C(m+d,d)`.

For a `d`-dimensional polynomial subspace, the first lemma applied to the annihilator of an
independent `i`-set gives the extension hypothesis of the second: at most `k-d+i` coordinates
are rank-preserving, hence a set of `k+m` coordinates has at least `m+d-i` rank-raising
extensions.  The resulting `C(m+d,d)` count is sharp at the level of these data.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ProximityGap.Frontier.MultiCoordinateInformationSetCount

/-! ## The generalized-MDS common-zero bound -/

variable {F ι : Type*} [Field F] [DecidableEq F]
variable [Fintype ι] [DecidableEq ι]

/-- A positive-dimensional subspace of degree-`< k` polynomials cannot have too many common
zeros.  More precisely, if an `r`-dimensional subspace vanishes on `S`, then `|S|+r ≤ k`.

This is the generalized-Hamming-weight form of the Reed–Solomon MDS property. -/
theorem card_add_finrank_le_of_vanish
    (α : ι ↪ F) (k : ℕ) (S : Finset ι)
    (W : Submodule F (Polynomial.degreeLT F k))
    (hpos : 0 < Module.finrank F W)
    (hvan : W ≤ LinearMap.ker (ArkLib.CS25.evalOnS α k S)) :
    S.card + Module.finrank F W ≤ k := by
  classical
  letI : FiniteDimensional F (Polynomial.degreeLT F k) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F k).toLinearMap
      (Polynomial.degreeLTEquiv F k).injective
  letI : FiniteDimensional F W :=
    FiniteDimensional.of_injective W.subtype W.injective_subtype
  have hSk : S.card ≤ k := by
    by_contra hnot
    have hkS : k < S.card := Nat.lt_of_not_ge hnot
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hkS)
    have hkerT : LinearMap.ker (ArkLib.CS25.evalOnS α k T) = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      rw [ArkLib.CS25.finrank_ker_evalOnS α k T (by omega), hTcard, Nat.sub_self]
    have hWT : W ≤ LinearMap.ker (ArkLib.CS25.evalOnS α k T) := by
      intro p hp
      rw [LinearMap.mem_ker] at ⊢
      ext i
      have hpS := hvan hp
      rw [LinearMap.mem_ker] at hpS
      have := congrFun hpS ⟨(i : ι), hTS i.2⟩
      simpa [ArkLib.CS25.evalOnS] using this
    have hWbot : W = ⊥ := by
      rw [eq_bot_iff, ← hkerT]
      exact hWT
    rw [hWbot, finrank_bot] at hpos
    omega
  have hdimker := ArkLib.CS25.finrank_ker_evalOnS α k S hSk
  have hdimle : Module.finrank F W ≤
      Module.finrank F (LinearMap.ker (ArkLib.CS25.evalOnS α k S)) :=
    Submodule.finrank_mono hvan
  rw [hdimker] at hdimle
  omega

/-! ### Actual polynomial information sets -/

/-- A coordinate set is an information set for `W` when every prescription of values on those
coordinates is attained by a polynomial in `W`.  For sets of size at most `finrank W`, this is
equivalent to independence of the corresponding evaluation rows. -/
def IsPolynomialInformationSet
    (α : ι ↪ F) (k : ℕ) (W : Submodule F (Polynomial.degreeLT F k))
    (I : Finset ι) : Prop :=
  Function.Surjective ((ArkLib.CS25.evalOnS α k I).domRestrict W)

/-- The empty set is an information set. -/
theorem isPolynomialInformationSet_empty
    (α : ι ↪ F) (k : ℕ) (W : Submodule F (Polynomial.degreeLT F k)) :
    IsPolynomialInformationSet α k W ∅ := by
  intro f
  refine ⟨0, ?_⟩
  funext i
  have hex : ∃ x, x ∈ (∅ : Finset ι) ∧ True := ⟨i.1, i.2, trivial⟩
  exact (Finset.exists_mem_empty_iff (fun _ : ι => True)).mp hex |>.elim

/-- If `I` is an information set and a polynomial in `W` vanishes on `I` but not at `x`, then
`insert x I` is again an information set.  This is the constructive one-coordinate rank-raising
step: first lift the prescribed values on `I`, then add a scalar multiple of the kernel
polynomial to fix the value at `x`. -/
theorem isPolynomialInformationSet_insert_of_kernel_nonzero
    (α : ι ↪ F) (k : ℕ) (W : Submodule F (Polynomial.degreeLT F k))
    (I : Finset ι) (x : ι)
    (hI : IsPolynomialInformationSet α k W I)
    (q : W)
    (hqI : ((ArkLib.CS25.evalOnS α k I).domRestrict W) q = 0)
    (hqx : (q.1 : F[X]).eval (α x) ≠ 0) :
    IsPolynomialInformationSet α k W (insert x I) := by
  classical
  intro f
  let fI : I → F := fun i => f ⟨i.1, Finset.mem_insert_of_mem i.2⟩
  obtain ⟨p, hp⟩ := hI fI
  let s : F := (f ⟨x, Finset.mem_insert_self x I⟩ - (p.1 : F[X]).eval (α x)) /
    (q.1 : F[X]).eval (α x)
  refine ⟨p + s • q, ?_⟩
  funext j
  change ((p.1 : F[X]) + s • (q.1 : F[X])).eval (α j.1) = f j
  rw [Polynomial.eval_add, Polynomial.eval_smul]
  by_cases hjx : j.1 = x
  · have hjsub : j = ⟨x, Finset.mem_insert_self x I⟩ := Subtype.ext hjx
    subst j
    dsimp [s]
    field_simp
    ring
  · have hjI : j.1 ∈ I := by
      exact (Finset.mem_insert.mp j.2).resolve_left hjx
    have hqzero : (q.1 : F[X]).eval (α j.1) = 0 := by
      have := congrFun hqI ⟨j.1, hjI⟩
      simpa [ArkLib.CS25.evalOnS, LinearMap.domRestrict_apply] using this
    rw [hqzero, smul_zero, add_zero]
    have := congrFun hp ⟨j.1, hjI⟩
    simpa [fI, ArkLib.CS25.evalOnS, LinearMap.domRestrict_apply] using this

/-! ## An abstract information-set layer count -/

/-- The `i`-th layer of a finite hereditary-style set system.  The theorem below only needs
the explicitly stated one-point extension counts, so it also applies to linear matroids and
other independence systems without importing a matroid API. -/
def layer {E : Type*} (P : Finset E → Prop) (i : ℕ) :=
  {I : Finset E // I.card = i ∧ P I}

/-- Admissible one-point extensions of `I`. -/
def extensions {E : Type*} [DecidableEq E] (P : Finset E → Prop) (I : Finset E) :=
  {x : E // x ∉ I ∧ P (insert x I)}

noncomputable instance layerFintype {E : Type*} [Fintype E]
    (P : Finset E → Prop) (i : ℕ) : Fintype (layer P i) :=
  Fintype.ofInjective (fun I : layer P i => I.1) Subtype.val_injective

noncomputable instance extensionsFintype {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) (I : Finset E) : Fintype (extensions P I) :=
  Fintype.ofInjective (fun x : extensions P I => x.1) Subtype.val_injective

section LayerCount

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Inserting an admissible point sends an `i`-set to an `(i+1)`-set, remembering the inserted
point.  This is the incidence map used in the layer recurrence. -/
noncomputable def insertExtensionMap (P : Finset E → Prop) (i : ℕ) :
    (Σ I : layer P i, extensions P I.1) →
      (Σ J : layer P (i + 1), {x : E // x ∈ J.1}) := by
  classical
  intro z
  refine ⟨⟨insert z.2.1 z.1.1, ?_, z.2.2.2⟩, ⟨z.2.1, mem_insert_self _ _⟩⟩
  rw [card_insert_of_notMem z.2.2.1, z.1.2.1]

/-- The insertion incidence map is injective: the inserted point is remembered, and erasing it
recovers the source set. -/
theorem insertExtensionMap_injective (P : Finset E → Prop) (i : ℕ) :
    Function.Injective (insertExtensionMap P i) := by
  classical
  rintro ⟨I, x⟩ ⟨J, y⟩ h
  have hxy : x.1 = y.1 := by
    exact congrArg (fun z => ((z.2 : {a : E // a ∈ z.1.1}) : E)) h
  have hsets : insert x.1 I.1 = insert y.1 J.1 := by
    exact congrArg (fun z => z.1.1) h
  have hxJ : x.1 ∉ J.1 := by
    simpa [hxy] using y.2.1
  have hIJval : I.1 = J.1 := by
    rw [← hxy] at hsets
    have := congrArg (fun T : Finset E => T.erase x.1) hsets
    simpa [erase_insert, x.2.1, hxJ] using this
  have hIJ : I = J := Subtype.ext hIJval
  cases hIJ
  have hxySub : x = y := Subtype.ext hxy
  subst y
  rfl

/-- **Exact independent-layer recurrence.**  If every admissible `i`-set has at least `L`
admissible one-point extensions, then

`L * #(i-layer) ≤ (i+1) * #((i+1)-layer)`.

The right factor is exact because every `(i+1)`-set has precisely `i+1` marked elements. -/
theorem layer_card_recurrence (P : Finset E → Prop) [DecidablePred P] (i L : ℕ)
    (hext : ∀ I : layer P i, L ≤ Fintype.card (extensions P I.1)) :
    L * Fintype.card (layer P i) ≤ (i + 1) * Fintype.card (layer P (i + 1)) := by
  classical
  let A := Σ I : layer P i, extensions P I.1
  let B := Σ J : layer P (i + 1), {x : E // x ∈ J.1}
  have hA : L * Fintype.card (layer P i) ≤ Fintype.card A := by
    rw [show Fintype.card A = ∑ I : layer P i,
        Fintype.card (extensions P I.1) by
      exact Fintype.card_sigma]
    calc
      L * Fintype.card (layer P i) = ∑ _I : layer P i, L := by
        simp [Nat.mul_comm]
      _ ≤ ∑ I : layer P i, Fintype.card (extensions P I.1) := by
        exact Finset.sum_le_sum (fun I _ => hext I)
  have hAB : Fintype.card A ≤ Fintype.card B := by
    exact Fintype.card_le_of_injective (insertExtensionMap P i)
      (insertExtensionMap_injective P i)
  have hB : Fintype.card B = (i + 1) * Fintype.card (layer P (i + 1)) := by
    rw [show Fintype.card B = ∑ J : layer P (i + 1),
        Fintype.card {x : E // x ∈ J.1} by
      exact Fintype.card_sigma]
    simp only [Fintype.card_coe]
    rw [show (∑ J : layer P (i + 1), J.1.card) =
        ∑ _J : layer P (i + 1), (i + 1) by
      apply Finset.sum_congr rfl
      intro J _
      exact J.2.1]
    simp [Nat.mul_comm]
  exact hA.trans (hAB.trans_eq hB)

/-- **Information-set count from rank-raising extensions.**  Suppose the empty set is admissible
and every admissible `i`-set, for `i<d`, has at least `m+d-i` admissible extensions.  Then there
are at least `C(m+d,d)` admissible `d`-sets.

For polynomial evaluation rows on a `k+m` point set, `card_add_finrank_le_of_vanish` supplies
exactly this extension hypothesis. -/
theorem choose_le_card_layer_of_extension (P : Finset E → Prop) [DecidablePred P] (m d : ℕ)
    (hempty : P ∅)
    (hext : ∀ (i : ℕ), i < d → ∀ I : layer P i,
      m + d - i ≤ Fintype.card (extensions P I.1)) :
    (m + d).choose d ≤ Fintype.card (layer P d) := by
  classical
  have hmain : ∀ i : ℕ, i ≤ d →
      (m + d).choose i ≤ Fintype.card (layer P i) := by
    intro i hi
    induction i with
    | zero =>
        simp only [Nat.choose_zero_right]
        exact Fintype.card_pos_iff.mpr ⟨⟨∅, card_empty, hempty⟩⟩
    | succ i ih =>
        have hid : i < d := Nat.lt_of_succ_le hi
        have hirec := layer_card_recurrence P i (m + d - i) (hext i hid)
        have hmul : (m + d).choose (i + 1) * (i + 1) ≤
            Fintype.card (layer P (i + 1)) * (i + 1) := by
          calc
            (m + d).choose (i + 1) * (i + 1)
                = (m + d).choose i * (m + d - i) :=
                  Nat.choose_succ_right_eq (m + d) i
            _ ≤ Fintype.card (layer P i) * (m + d - i) :=
              Nat.mul_le_mul_right (m + d - i) (ih (Nat.le_of_lt hid))
            _ ≤ Fintype.card (layer P (i + 1)) * (i + 1) := by
              simpa [Nat.mul_comm] using hirec
        exact le_of_mul_le_mul_right hmul (by omega)
  exact hmain d le_rfl

end LayerCount

/-! ## The polynomial-subspace count -/

/-- **Polynomial-subspace information-set count.**

Let `W` be a `d`-dimensional subspace of degree-`<k` polynomials, evaluated on `k+m` distinct
points.  Then at least `C(m+d,d)` coordinate `d`-sets are information sets for `W`.

The proof is the generalized-MDS argument described at the top of the file.  For an information
`i`-set `I`, its vanishing kernel has dimension `d-i`.  The common-zero theorem bounds the
rank-preserving coordinates by `k-d+i`, so at least `m+d-i` coordinates raise the rank.  The
abstract marked-extension recurrence then gives the binomial count. -/
theorem polynomial_information_set_count
    (α : ι ↪ F) (k m d : ℕ)
    (W : Submodule F (Polynomial.degreeLT F k))
    (hcard : Fintype.card ι = k + m)
    (hdim : Module.finrank F W = d) :
    (m + d).choose d ≤
      Fintype.card (layer (IsPolynomialInformationSet α k W) d) := by
  classical
  letI : FiniteDimensional F (Polynomial.degreeLT F k) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F k).toLinearMap
      (Polynomial.degreeLTEquiv F k).injective
  letI : FiniteDimensional F W :=
    FiniteDimensional.of_injective W.subtype W.injective_subtype
  apply choose_le_card_layer_of_extension (IsPolynomialInformationSet α k W) m d
      (isPolynomialInformationSet_empty α k W)
  intro i hid I
  let R : W →ₗ[F] (I.1 → F) :=
    (ArkLib.CS25.evalOnS α k I.1).domRestrict W
  let K : Submodule F W := LinearMap.ker R
  have hrange : Module.finrank F (LinearMap.range R) = I.1.card := by
    rw [LinearMap.range_eq_top.mpr I.2.2, finrank_top, Module.finrank_pi,
      Fintype.card_coe]
  have hKdim : Module.finrank F K = d - i := by
    have hranknull := R.finrank_range_add_finrank_ker
    rw [hrange, hdim, I.2.1] at hranknull
    omega
  let Kamb : Submodule F (Polynomial.degreeLT F k) := K.map W.subtype
  have hKambdim : Module.finrank F Kamb = d - i := by
    dsimp [Kamb]
    rw [Submodule.finrank_map_subtype_eq, hKdim]
  let B : Finset ι := Finset.univ.filter (fun x =>
    ∀ q : K, (q.1.1 : F[X]).eval (α x) = 0)
  have hKambvan : Kamb ≤ LinearMap.ker (ArkLib.CS25.evalOnS α k B) := by
    intro p hp
    rw [LinearMap.mem_ker]
    ext x
    rw [Submodule.mem_map] at hp
    obtain ⟨q, hqK, hqp⟩ := hp
    have hxall : ∀ z : K, (z.1.1 : F[X]).eval (α x.1) = 0 :=
      (Finset.mem_filter.mp x.2).2
    have hqzero := hxall ⟨q, hqK⟩
    simpa [ArkLib.CS25.evalOnS, ← hqp] using hqzero
  have hKambpos : 0 < Module.finrank F Kamb := by
    rw [hKambdim]
    omega
  have hBmaster := card_add_finrank_le_of_vanish α k B Kamb hKambpos hKambvan
  have hBbound : B.card + (d - i) ≤ k := by
    simpa [hKambdim] using hBmaster
  let outsideB := {x : ι // x ∈ (Finset.univ \ B)}
  letI : Fintype outsideB :=
    Fintype.ofInjective (fun x : outsideB => x.1) Subtype.val_injective
  let toExtension : outsideB → extensions (IsPolynomialInformationSet α k W) I.1 := by
    intro x
    have hxnotB : x.1 ∉ B := (Finset.mem_sdiff.mp x.2).2
    have hnotall : ¬ ∀ q : K, (q.1.1 : F[X]).eval (α x.1) = 0 := by
      intro hall
      apply hxnotB
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩
    push_neg at hnotall
    let q : K := Classical.choose hnotall
    have hqx : (q.1.1 : F[X]).eval (α x.1) ≠ 0 := Classical.choose_spec hnotall
    have hqker : R q.1 = 0 := by
      exact LinearMap.mem_ker.mp q.2
    have hxnotI : x.1 ∉ I.1 := by
      intro hxI
      apply hqx
      have := congrFun hqker ⟨x.1, hxI⟩
      simpa [R, ArkLib.CS25.evalOnS, LinearMap.domRestrict_apply] using this
    refine ⟨x.1, hxnotI, ?_⟩
    exact isPolynomialInformationSet_insert_of_kernel_nonzero α k W I.1 x.1 I.2.2 q.1
      (by simpa [R, K] using hqker) hqx
  have htoExtension : Function.Injective toExtension := by
    intro x y hxy
    apply Subtype.ext
    change x.1 = y.1
    simpa [toExtension] using congrArg (fun z => z.1) hxy
  have hcardOutside : Fintype.card outsideB = Fintype.card ι - B.card := by
    rw [show Fintype.card outsideB = (Finset.univ \ B).card by
      exact Fintype.card_coe _]
    simp [Finset.card_sdiff]
  have houtside_le : Fintype.card outsideB ≤
      Fintype.card (extensions (IsPolynomialInformationSet α k W) I.1) :=
    Fintype.card_le_of_injective toExtension htoExtension
  calc
    m + d - i ≤ Fintype.card ι - B.card := by omega
    _ = Fintype.card outsideB := hcardOutside.symm
    _ ≤ Fintype.card (extensions (IsPolynomialInformationSet α k W) I.1) := houtside_le

/-! ## Simultaneous rank-to-two reduction on a shared information set -/

/-- **Injective preimages of an affine line lie on an affine line.**

Let `Φ` be the restriction map to a shared information set.  If the restricted coefficient
vectors `Φ(w_g)` depend affinely on the scalar `γ_g`, then two distinct scalar values lift that
affine dependence uniquely through the injective map `Φ`.  Consequently *all* full coefficient
vectors `w_g` lie on one affine line.

Applied to
`X_g = a + γ_g b + ∑ℓ (w_g)_ℓ c_ℓ`, this is the simultaneous rank-to-`2` reduction:
every column whose witness set contains the same information set belongs to one codeword pencil,
so `DesignMatrixAffineCluster.affineCluster_card_le_length` bounds that fibre by the block length.
-/
theorem injective_preimages_of_affine_line_are_affine
    {V U Γ : Type*} [AddCommGroup V] [Module F V] [AddCommGroup U] [Module F U]
    (Φ : V →ₗ[F] U) (hΦ : Function.Injective Φ)
    (γ : Γ → F) (w : Γ → V) (r₀ r₁ : U)
    (hline : ∀ g : Γ, Φ (w g) = r₀ + γ g • r₁)
    (g₀ g₁ : Γ) (hne : γ g₀ ≠ γ g₁) :
    ∃ v₀ v₁ : V, ∀ g : Γ, w g = v₀ + γ g • v₁ := by
  let Δ : F := γ g₁ - γ g₀
  let v₁ : V := Δ⁻¹ • (w g₁ - w g₀)
  let v₀ : V := w g₀ - γ g₀ • v₁
  have hΔ : Δ ≠ 0 := by
    dsimp [Δ]
    exact sub_ne_zero.mpr hne.symm
  have hΦv₁ : Φ v₁ = r₁ := by
    dsimp [v₁]
    rw [LinearMap.map_smul, LinearMap.map_sub, hline g₁, hline g₀]
    calc
      Δ⁻¹ • ((r₀ + γ g₁ • r₁) - (r₀ + γ g₀ • r₁))
          = Δ⁻¹ • (Δ • r₁) := by
              dsimp [Δ]
              module
      _ = r₁ := by
        rw [smul_smul, inv_mul_cancel₀ hΔ, one_smul]
  have hΦv₀ : Φ v₀ = r₀ := by
    dsimp [v₀]
    rw [LinearMap.map_sub, LinearMap.map_smul, hline g₀, hΦv₁]
    module
  refine ⟨v₀, v₁, fun g => hΦ ?_⟩
  rw [LinearMap.map_add, LinearMap.map_smul, hΦv₀, hΦv₁, hline g]

end ProximityGap.Frontier.MultiCoordinateInformationSetCount

#print axioms ProximityGap.Frontier.MultiCoordinateInformationSetCount.card_add_finrank_le_of_vanish
#print axioms ProximityGap.Frontier.MultiCoordinateInformationSetCount.layer_card_recurrence
#print axioms ProximityGap.Frontier.MultiCoordinateInformationSetCount.choose_le_card_layer_of_extension
#print axioms ProximityGap.Frontier.MultiCoordinateInformationSetCount.injective_preimages_of_affine_line_are_affine
