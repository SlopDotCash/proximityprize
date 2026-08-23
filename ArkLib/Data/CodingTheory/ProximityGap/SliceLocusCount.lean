/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FoldPolynomialSlices

/-!
# The per-locus cardinality (issue #232)

The counting companion to `low_weight_slice_structure`: over a finite field, the
polynomials of degree `< d` vanishing on a prescribed `|Z|`-point locus number EXACTLY
`q^(d − |Z|)` — multiplication by the locator `loc Z` is a bijection from the
unconstrained space one locus-size down (`loc_dvd_iff` supplies surjectivity).

* `polysDegLT` / `mem_polysDegLT` / `card_polysDegLT` — the degree-`< d` space as a
  concrete `Finset` of size `q^d`, enumerated by coefficient tuples;
* `card_polysDegLT_vanishing` — the per-locus count `q^(d − |Z|)`.

With `low_weight_slice_structure` this makes the Conjecture-D counting skeleton
numerically explicit: per locus `Z`, the slice pairs of a degree-`< k` error range in a
space of exactly `q^(de − |Z|)·q^(do − |Z|) = q^(k − 2|Z|)` elements (`de`, `do` the
slice degree budgets), so the open all-words content is precisely the union over loci
against the weight filter. (The `f`-level product count via the slice bijection
`recompose_slices` is the queued capstone.)
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The finset of all polynomials of degree `< d`, enumerated by coefficient tuples. -/
noncomputable def polysDegLT (d : ℕ) : Finset F[X] :=
  (Finset.univ : Finset (Fin d → F)).image
    (fun c => ∑ i : Fin d, C (c i) * X ^ (i : ℕ))

omit [Fintype F] [DecidableEq F] in
theorem coeff_tuple_sum (d : ℕ) (c : Fin d → F) (j : Fin d) :
    (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).coeff j = c j := by
  rw [finset_sum_coeff]
  rw [Finset.sum_congr rfl fun i _ => coeff_C_mul_X_pow (c i) i j]
  simp only [Fin.val_inj]
  rw [Finset.sum_ite_eq Finset.univ j fun i => c i]
  simp

theorem mem_polysDegLT {d : ℕ} {p : F[X]} :
    p ∈ polysDegLT d ↔ p.degree < d := by
  constructor
  · rintro hp
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    apply lt_of_le_of_lt (degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe d)]
    intro i _
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)
  · intro hdeg
    refine Finset.mem_image.mpr ⟨fun i => p.coeff i, Finset.mem_univ _, ?_⟩
    by_cases hp0 : p = 0
    · subst hp0
      simp
    · have hnd : p.natDegree < d := (natDegree_lt_iff_degree_lt hp0).mpr hdeg
      conv_rhs => rw [p.as_sum_range' d hnd]
      rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
      exact Finset.sum_congr rfl fun i _ => C_mul_X_pow_eq_monomial

theorem card_polysDegLT (d : ℕ) :
    (polysDegLT (F := F) d).card = Fintype.card F ^ d := by
  rw [polysDegLT, Finset.card_image_of_injective _ ?inj, Finset.card_univ]
  · rw [Fintype.card_fun, Fintype.card_fin]
  case inj =>
    intro c c' heq
    funext j
    rw [← coeff_tuple_sum d c j, ← coeff_tuple_sum d c' j]
    exact congrArg (fun p : F[X] => p.coeff (j : ℕ)) heq

/-- **The per-locus count**: polynomials of degree `< d` vanishing on a `|Z|`-point set
form exactly `q^(d − |Z|)` elements (for `|Z| ≤ d`) — multiplication by the locator is a
bijection from the unconstrained space one locus-size down. -/
theorem card_polysDegLT_vanishing {d : ℕ} (Z : Finset F) (hZd : Z.card ≤ d) :
    ((polysDegLT (F := F) d).filter (fun p => ∀ z ∈ Z, p.eval z = 0)).card
      = Fintype.card F ^ (d - Z.card) := by
  have hlocne : TopLine.loc Z ≠ 0 := (TopLine.loc_monic Z).ne_zero
  have hlocdeg : (TopLine.loc Z).degree = (Z.card : WithBot ℕ) := by
    rw [degree_eq_natDegree hlocne, TopLine.loc_natDegree]
  rw [← card_polysDegLT (F := F) (d - Z.card)]
  symm
  apply Finset.card_bij (fun h _ => TopLine.loc Z * h)
  · intro h hh
    rw [Finset.mem_filter]
    constructor
    · rw [mem_polysDegLT]
      by_cases h0 : h = 0
      · subst h0
        rw [mul_zero, degree_zero]
        exact WithBot.bot_lt_coe d
      · rw [degree_mul, hlocdeg]
        have hdh : h.degree < ((d - Z.card : ℕ) : WithBot ℕ) := mem_polysDegLT.mp hh
        calc (Z.card : WithBot ℕ) + h.degree
            < (Z.card : WithBot ℕ) + ((d - Z.card : ℕ) : WithBot ℕ) :=
              WithBot.add_lt_add_left (WithBot.coe_ne_bot) hdh
          _ = ((Z.card + (d - Z.card) : ℕ) : WithBot ℕ) := by push_cast; rfl
          _ = (d : WithBot ℕ) := by rw [Nat.add_sub_cancel' hZd]
    · intro z hz
      rw [eval_mul, TopLine.loc_eval_zero hz, zero_mul]
  · intro h1 hh1 h2 hh2 heq
    exact mul_left_cancel₀ hlocne heq
  · intro p hp
    obtain ⟨hpd, hpz⟩ := Finset.mem_filter.mp hp
    obtain ⟨h, rfl⟩ := (loc_dvd_iff Z _).mpr hpz
    refine ⟨h, ?_, rfl⟩
    rw [mem_polysDegLT]
    by_cases h0 : h = 0
    · subst h0
      rw [degree_zero]
      exact WithBot.bot_lt_coe _
    · have hd := mem_polysDegLT.mp hpd
      rw [degree_mul, hlocdeg, degree_eq_natDegree h0] at hd
      rw [degree_eq_natDegree h0]
      have : Z.card + h.natDegree < d := by exact_mod_cast hd
      exact_mod_cast (by omega : h.natDegree < d - Z.card)


/-! ## The f-level capstone: both-slice vanishing counts are exactly `q^(k − 2|Z|)`

Slices are `C`-linear, slices of a built pair recover the pair (`evenSlice_build`/
`oddSlice_build`), and `f ↦ (evenSlice f, oddSlice f)` is a bijection between the
degree-`< k` space and the product of the slice-budget spaces (char ≠ 2). Hence the
degree-`< k` polynomials whose BOTH slices vanish on a prescribed `|Z|`-point locus
number EXACTLY `q^(k − 2|Z|)` (`card_polysDegLT_slices_vanishing`) — the per-locus list
budget of the Conjecture-D skeleton, now an equality. -/

open Polynomial Finset

variable {F : Type*} [Field F]

/-- `expand` composed with `−X` is itself (even polynomials are even). -/
theorem expand_comp_neg_X (h : F[X]) :
    (Polynomial.expand F 2 h).comp (-X) = Polynomial.expand F 2 h := by
  ext n
  rw [coeff_comp_neg_X]
  by_cases hd : 2 ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [Even.neg_one_pow ⟨m, by ring⟩, one_mul]
  · rw [coeff_expand (by norm_num : 0 < 2), if_neg hd, mul_zero]

theorem contract_two_C_mul (a : F) (h : F[X]) :
    Polynomial.contract 2 (C a * h) = C a * Polynomial.contract 2 h := by
  ext n
  rw [coeff_contract (by norm_num : (2:ℕ) ≠ 0), coeff_C_mul, coeff_C_mul,
    coeff_contract (by norm_num : (2:ℕ) ≠ 0)]

theorem comp_neg_X_C_mul (a : F) (h : F[X]) :
    (C a * h).comp (-X) = C a * h.comp (-X) := by
  rw [mul_comp, C_comp]

theorem evenSlice_C_mul (a : F) (h : F[X]) :
    evenSlice (C a * h) = C a * evenSlice h := by
  rw [evenSlice, evenSlice, comp_neg_X_C_mul, ← mul_add, contract_two_C_mul]

theorem divX_C_mul' (a : F) (h : F[X]) :
    Polynomial.divX (C a * h) = C a * Polynomial.divX h := by
  ext n
  rw [coeff_divX, coeff_C_mul, coeff_C_mul, coeff_divX]

theorem oddSlice_C_mul (a : F) (h : F[X]) :
    oddSlice (C a * h) = C a * oddSlice h := by
  rw [oddSlice, oddSlice, comp_neg_X_C_mul, ← mul_sub, divX_C_mul', contract_two_C_mul]

theorem divX_X_mul (h : F[X]) : Polynomial.divX (X * h) = h := by
  ext n
  rw [coeff_divX, mul_comm X h, coeff_mul_X]

/-- Slices of a built pair recover the pair (doubled). -/
theorem evenSlice_build (E O : F[X]) :
    evenSlice (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O) = 2 * E := by
  rw [evenSlice]
  have hcomp : (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O).comp (-X)
      = Polynomial.expand F 2 E - X * Polynomial.expand F 2 O := by
    rw [add_comp, mul_comp, X_comp]
    have he : (Polynomial.expand F 2 E).comp (-X) = Polynomial.expand F 2 E := by
      rw [expand_comp_neg_X]
    have ho : (Polynomial.expand F 2 O).comp (-X) = Polynomial.expand F 2 O := by
      rw [expand_comp_neg_X]
    rw [he, ho]
    ring
  rw [hcomp]
  have : Polynomial.expand F 2 E + X * Polynomial.expand F 2 O
      + (Polynomial.expand F 2 E - X * Polynomial.expand F 2 O)
      = 2 * Polynomial.expand F 2 E := by ring
  rw [this]
  have h2 : (2 : F[X]) * Polynomial.expand F 2 E = Polynomial.expand F 2 (2 * E) := by
    rw [map_mul, map_ofNat]
  rw [h2, contract_expand (p := 2) (by norm_num)]

theorem oddSlice_build (E O : F[X]) :
    oddSlice (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O) = 2 * O := by
  rw [oddSlice]
  have hcomp : (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O).comp (-X)
      = Polynomial.expand F 2 E - X * Polynomial.expand F 2 O := by
    rw [add_comp, mul_comp, X_comp]
    rw [expand_comp_neg_X, expand_comp_neg_X]
    ring
  rw [hcomp]
  have : Polynomial.expand F 2 E + X * Polynomial.expand F 2 O
      - (Polynomial.expand F 2 E - X * Polynomial.expand F 2 O)
      = X * (2 * Polynomial.expand F 2 O) := by ring
  rw [this, divX_X_mul]
  have h2 : (2 : F[X]) * Polynomial.expand F 2 O = Polynomial.expand F 2 (2 * O) := by
    rw [map_mul, map_ofNat]
  rw [h2, contract_expand (p := 2) (by norm_num)]


/-! ## The bijection and the count (restored: dropped from the previous commit by a
merge error — the O96 ledger entry describes this content) -/

theorem C_inv_two_mul_two (h2 : (2 : F) ≠ 0) (p : F[X]) :
    C (2 : F)⁻¹ * (2 * p) = p := by
  have h2C : (2 : F[X]) = C (2 : F) := (map_ofNat (C : F →+* F[X]) 2).symm
  rw [h2C, ← mul_assoc, ← C_mul, inv_mul_cancel₀ h2, C_1, one_mul]

theorem evenSlice_zero : evenSlice (0 : F[X]) = 0 := by
  rw [evenSlice, zero_comp, add_zero]
  ext n
  rw [coeff_contract (by norm_num : (2:ℕ) ≠ 0), coeff_zero, coeff_zero]

theorem oddSlice_zero : oddSlice (0 : F[X]) = 0 := by
  rw [oddSlice, zero_comp, sub_zero, divX_zero]
  ext n
  rw [coeff_contract (by norm_num : (2:ℕ) ≠ 0), coeff_zero, coeff_zero]

theorem natDegree_oddSlice_le' (f : F[X]) :
    (oddSlice f).natDegree ≤ (f.natDegree - 1) / 2 := by
  refine le_trans (natDegree_contract_two_le _) (Nat.div_le_div_right ?_)
  rw [natDegree_divX_eq_natDegree_tsub_one]
  apply Nat.sub_le_sub_right
  refine le_trans (natDegree_sub_le _ _) (max_le le_rfl ?_)
  calc (f.comp (-X)).natDegree ≤ f.natDegree * (-X : F[X]).natDegree := natDegree_comp_le
    _ ≤ f.natDegree := by rw [natDegree_neg, natDegree_X, mul_one]

theorem oddSlice_ne_zero_natDegree_pos {f : F[X]} (h : oddSlice f ≠ 0) :
    1 ≤ f.natDegree := by
  by_contra hlt
  push Not at hlt
  interval_cases hdeg : f.natDegree
  · -- f is a constant: f = C (f.coeff 0)
    have hconst : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    apply h
    rw [hconst, oddSlice]
    have : (C (f.coeff 0) : F[X]).comp (-X) = C (f.coeff 0) := C_comp
    rw [this, sub_self, divX_zero]
    ext n
    rw [coeff_contract (by norm_num : (2:ℕ) ≠ 0), coeff_zero, coeff_zero]


variable [Fintype F] [DecidableEq F]

theorem evenSlice_mem {k : ℕ} {f : F[X]} (hf : f ∈ polysDegLT k) :
    evenSlice f ∈ polysDegLT ((k + 1) / 2) := by
  rw [mem_polysDegLT] at hf ⊢
  by_cases hf0 : f = 0
  · subst hf0
    rw [evenSlice_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hk : f.natDegree < k := (natDegree_lt_iff_degree_lt hf0).mpr hf
    by_cases he0 : evenSlice f = 0
    · rw [he0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [← natDegree_lt_iff_degree_lt he0]
      have := natDegree_evenSlice_le f
      omega
  -- need: natDegree f / 2 < (k+1)/2 given natDegree f < k : omega handles

theorem oddSlice_mem {k : ℕ} {f : F[X]} (hf : f ∈ polysDegLT k) :
    oddSlice f ∈ polysDegLT (k / 2) := by
  rw [mem_polysDegLT] at hf ⊢
  by_cases ho0 : oddSlice f = 0
  · rw [ho0, degree_zero]; exact WithBot.bot_lt_coe _
  · have h1 : 1 ≤ f.natDegree := oddSlice_ne_zero_natDegree_pos ho0
    have hf0 : f ≠ 0 := fun h => by simp [h, oddSlice_zero] at ho0
    have hk : f.natDegree < k := (natDegree_lt_iff_degree_lt hf0).mpr hf
    rw [← natDegree_lt_iff_degree_lt ho0]
    have := natDegree_oddSlice_le' f
    omega

theorem build_mem {k : ℕ} {E O : F[X]}
    (hE : E ∈ polysDegLT ((k + 1) / 2)) (hO : O ∈ polysDegLT (k / 2)) :
    C (2 : F)⁻¹ * (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O)
      ∈ polysDegLT k := by
  rw [mem_polysDegLT] at hE hO ⊢
  set G : F[X] := Polynomial.expand F 2 E + X * Polynomial.expand F 2 O with hG
  by_cases ha : (2:F)⁻¹ = 0
  · rw [ha, map_zero, zero_mul, degree_zero]
    exact WithBot.bot_lt_coe _
  have hdeq : (C (2:F)⁻¹ * G).degree = G.degree := by
    rw [degree_mul, degree_C ha, zero_add]
  rw [hdeq, hG]
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · by_cases hE0 : E = 0
    · subst hE0; rw [map_zero, degree_zero]; exact WithBot.bot_lt_coe _
    · have hEd : E.natDegree < (k + 1) / 2 := (natDegree_lt_iff_degree_lt hE0).mpr hE
      have hexp0 : Polynomial.expand F 2 E ≠ 0 := by
        intro h
        apply hE0
        have hc := congrArg (Polynomial.contract 2) h
        rwa [contract_expand (p := 2) (by norm_num), show Polynomial.contract 2 (0 : F[X]) = 0
          from by ext n; rw [coeff_contract (by norm_num : (2:ℕ) ≠ 0)]; simp] at hc
      rw [← natDegree_lt_iff_degree_lt hexp0, natDegree_expand]
      omega
  · by_cases hO0 : O = 0
    · subst hO0; rw [map_zero, mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
    · have hOd : O.natDegree < k / 2 := (natDegree_lt_iff_degree_lt hO0).mpr hO
      have hexp0 : Polynomial.expand F 2 O ≠ 0 := by
        intro h
        apply hO0
        have hc := congrArg (Polynomial.contract 2) h
        rwa [contract_expand (p := 2) (by norm_num), show Polynomial.contract 2 (0 : F[X]) = 0
          from by ext n; rw [coeff_contract (by norm_num : (2:ℕ) ≠ 0)]; simp] at hc
      have hX0 : (X : F[X]) * Polynomial.expand F 2 O ≠ 0 := mul_ne_zero X_ne_zero hexp0
      rw [← natDegree_lt_iff_degree_lt hX0, natDegree_mul X_ne_zero hexp0,
        natDegree_X, natDegree_expand]
      omega

/-- **The f-level per-locus count**: degree-`< k` polynomials whose BOTH coefficient
slices vanish on a prescribed `|Z|`-point locus number exactly `q^(k − 2|Z|)`. -/
theorem card_polysDegLT_slices_vanishing (h2 : (2 : F) ≠ 0) {k : ℕ} (Z : Finset F)
    (hZ : 2 * Z.card ≤ k) :
    ((polysDegLT (F := F) k).filter (fun f =>
        (∀ z ∈ Z, (evenSlice f).eval z = 0) ∧ (∀ z ∈ Z, (oddSlice f).eval z = 0))).card
      = Fintype.card F ^ (k - 2 * Z.card) := by
  have hsplit : k - 2 * Z.card = ((k + 1) / 2 - Z.card) + (k / 2 - Z.card) := by omega
  rw [hsplit, pow_add,
    ← card_polysDegLT_vanishing (F := F) (d := (k + 1) / 2) Z (by omega),
    ← card_polysDegLT_vanishing (F := F) (d := k / 2) Z (by omega),
    ← Finset.card_product]
  refine Finset.card_bij' (fun f _ => (evenSlice f, oddSlice f))
    (fun p _ => C (2 : F)⁻¹ * (Polynomial.expand F 2 p.1 + X * Polynomial.expand F 2 p.2))
    ?_ ?_ ?_ ?_
  · -- i maps into the product
    intro f hf
    obtain ⟨hfd, hfe, hfo⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨evenSlice_mem hfd, hfe⟩,
       Finset.mem_filter.mpr ⟨oddSlice_mem hfd, hfo⟩⟩
  · -- j maps into the filtered space
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1d, hp1z⟩ := Finset.mem_filter.mp hp1
    obtain ⟨hp2d, hp2z⟩ := Finset.mem_filter.mp hp2
    refine Finset.mem_filter.mpr ⟨build_mem hp1d hp2d, ?_, ?_⟩
    · intro z hz
      rw [evenSlice_C_mul, evenSlice_build, C_inv_two_mul_two h2]
      exact hp1z z hz
    · intro z hz
      rw [oddSlice_C_mul, oddSlice_build, C_inv_two_mul_two h2]
      exact hp2z z hz
  · -- left inverse: j (i f) = f
    intro f _
    show C (2:F)⁻¹ * (Polynomial.expand F 2 (evenSlice f)
      + X * Polynomial.expand F 2 (oddSlice f)) = f
    rw [recompose_slices f, C_inv_two_mul_two h2]
  · -- right inverse: i (j p) = p
    intro p _
    refine Prod.ext ?_ ?_
    · show evenSlice (C (2:F)⁻¹ * _) = p.1
      rw [evenSlice_C_mul, evenSlice_build, C_inv_two_mul_two h2]
    · show oddSlice (C (2:F)⁻¹ * _) = p.2
      rw [oddSlice_C_mul, oddSlice_build, C_inv_two_mul_two h2]


/-! ## The level-1 union bound: the incidence template -/

/-- **The level-1 union bound** (the incidence template): low-evaluation-weight
polynomials are covered by the per-locus spaces over size-`s` loci, so their number is
at most `C(|D²|, s) · q^(k − 2s)` where `s = |D²| − w`. As a pure number this is
classically subsumed (MDS weight distributions are exact); its value is as the
machine-checked template the tower iteration instantiates per level. -/
theorem low_weight_count_le {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D)
    (h0 : (0 : F) ∉ D) (h2 : (2 : F) ≠ 0) {k w s : ℕ}
    (hs : s + w = (D.image (· ^ 2)).card) (h2s : 2 * s ≤ k) :
    ((polysDegLT (F := F) k).filter
        (fun f => (D.filter (fun x => f.eval x ≠ 0)).card ≤ w)).card
      ≤ ((D.image (· ^ 2)).powersetCard s).card * Fintype.card F ^ (k - 2 * s) := by
  -- every low-weight f's slices vanish on some size-s locus
  have hcover : (polysDegLT (F := F) k).filter
        (fun f => (D.filter (fun x => f.eval x ≠ 0)).card ≤ w)
      ⊆ ((D.image (· ^ 2)).powersetCard s).biUnion
          (fun Z => (polysDegLT (F := F) k).filter (fun f =>
            (∀ z ∈ Z, (evenSlice f).eval z = 0) ∧ (∀ z ∈ Z, (oddSlice f).eval z = 0))) := by
    intro f hf
    obtain ⟨hfd, hfw⟩ := Finset.mem_filter.mp hf
    obtain ⟨Zf, hePoly, hoPoly, hZsub, hZcard, heq, hoq, _⟩ :=
      low_weight_slice_structure hneg h0 h2 f
    -- |Zf| ≥ |D²| − w = s
    have hZge : s ≤ Zf.card := by omega
    obtain ⟨Z, hZZf, hZcard'⟩ := Finset.exists_subset_card_eq hZge
    refine Finset.mem_biUnion.mpr ⟨Z, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨hZZf.trans hZsub, hZcard'⟩
    · refine Finset.mem_filter.mpr ⟨hfd, ?_, ?_⟩
      · intro z hz
        have hzZf : z ∈ Zf := hZZf hz
        rw [heq, eval_mul, TopLine.loc_eval_zero hzZf, zero_mul]
      · intro z hz
        have hzZf : z ∈ Zf := hZZf hz
        rw [hoq, eval_mul, TopLine.loc_eval_zero hzZf, zero_mul]
  calc ((polysDegLT (F := F) k).filter
        (fun f => (D.filter (fun x => f.eval x ≠ 0)).card ≤ w)).card
      ≤ (((D.image (· ^ 2)).powersetCard s).biUnion
          (fun Z => (polysDegLT (F := F) k).filter (fun f =>
            (∀ z ∈ Z, (evenSlice f).eval z = 0) ∧ (∀ z ∈ Z, (oddSlice f).eval z = 0)))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ Z ∈ (D.image (· ^ 2)).powersetCard s,
          ((polysDegLT (F := F) k).filter (fun f =>
            (∀ z ∈ Z, (evenSlice f).eval z = 0) ∧ (∀ z ∈ Z, (oddSlice f).eval z = 0))).card :=
        Finset.card_biUnion_le
    _ = ∑ Z ∈ (D.image (· ^ 2)).powersetCard s, Fintype.card F ^ (k - 2 * Z.card) := by
        refine Finset.sum_congr rfl fun Z hZ => ?_
        have hZc : Z.card = s := (Finset.mem_powersetCard.mp hZ).2
        exact card_polysDegLT_slices_vanishing h2 Z (by omega)
    _ = ((D.image (· ^ 2)).powersetCard s).card * Fintype.card F ^ (k - 2 * s) := by
        rw [Finset.sum_congr rfl fun Z hZ => by
          rw [(Finset.mem_powersetCard.mp hZ).2]]
        rw [Finset.sum_const, smul_eq_mul]

end LamLeungTwoPow
