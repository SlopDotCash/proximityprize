/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
  Asymptotic list-bound kernel for explicit Reed-Solomon (an MDS code):
  the MDS / information-set leading-term weight-enumerator bound.

  We work with the Reed-Solomon code RS[F, n, k] = { eval of degree-<k polynomials
  on n distinct points }, an MDS code with minimum distance n-k+1.

  Self-contained: imports ONLY Mathlib. All helper notions restated here.

  Main deliverables (all fully proven, no holes):

  * `rs_codeword_weight_ge`  -- MDS distance: a NONZERO codeword has weight >= n-k+1.
  * `rs_vanish_card_le`      -- INFORMATION-SET COUNT: the number of codewords (as
                                 functions Fin n -> F) that vanish on a FIXED zero-set T
                                 of size m is at most q^(k-m). (Per-support MDS leading
                                 term.)
  * `rs_list_leading_bound`  -- THE LIST BOUND: the number of codewords of weight <= w
                                 is at most  C(n, w) * q^(w-(n-k)),  the MDS
                                 leading-term enumerator bound  A_{<=w} <= C(n,w) q^{w-k}.

  The leading-term bound q^{w-(n-k)} per support is the genuine MDS content; it is the
  honest sharpening past the trivial q^w-per-support bound, and is the leading term of
  the exact MDS weight enumerator A_w = C(n,w) sum_j (-1)^j C(w-1,j)(q^{w-k-j}-1).
-/

open Polynomial Finset

namespace RSAsymptKernel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The (Hamming) weight of a vector indexed by `Fin n`: the number of nonzero coords. -/
def wt {n : ℕ} (c : Fin n → F) : ℕ := #{i : Fin n | c i ≠ 0}

/-- A vector `c : Fin n → F` is an `RS[F,n,k]` codeword iff it is the evaluation of some
    polynomial of degree `< k` at the (fixed, distinct) points `α i`. -/
def IsCodeword (n k : ℕ) (α : Fin n → F) (c : Fin n → F) : Prop :=
  ∃ p : F[X], p.degree < (k : ℕ) ∧ ∀ i, c i = p.eval (α i)

/-! ### MDS minimum distance: a nonzero codeword has weight ≥ n−k+1. -/

/-- **MDS distance.** A nonzero RS codeword has at most `k-1` zero coordinates, hence its
    weight is at least `n - k + 1`.  Equivalently: it has `< k` zeros. -/
theorem rs_zeros_lt {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α)
    {c : Fin n → F} (hc : IsCodeword n k α c) (hne : c ≠ 0) :
    #{i : Fin n | c i = 0} < k := by
  obtain ⟨p, hdeg, hp⟩ := hc
  -- the zero coordinates of `c` are points where `p` vanishes
  by_contra hge
  push_neg at hge
  -- pick a `k`-subset `s` of the zero set
  have hcard : k ≤ #{i : Fin n | c i = 0} := hge
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hcard
  -- `p` vanishes on `α '' s`
  have hpvanish : ∀ x ∈ s.image α, p.eval x = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hci : c i = 0 := by
      have := hs_sub hi
      simpa using this
    rw [← hp]; exact hci
  have himg_card : (s.image α).card = k := by
    rw [Finset.card_image_of_injective _ hα, hs_card]
  -- degree of `p` is `< card (image)`, so `p = 0` by the Lagrange vanishing lemma
  have hdeglt : p.degree < (s.image α).card := by
    rw [himg_card]; exact hdeg
  have hp0 : p = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (s.image α) hdeglt hpvanish
  -- then `c = 0`, contradiction
  apply hne
  funext i
  rw [hp, hp0]; simp

/-- **MDS distance, weight form.** A nonzero RS codeword has weight `≥ n - k + 1`
    (equivalently `n - (k-1)` zeros at most), the Singleton bound met with equality. -/
theorem rs_codeword_weight_ge {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α)
    {c : Fin n → F} (hc : IsCodeword n k α c) (hne : c ≠ 0) :
    n + 1 ≤ wt c + k := by
  -- weight + #zeros = n
  have hsplit : wt c + #{i : Fin n | c i = 0} = n := by
    unfold wt
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => c i ≠ 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    have hBeq : #{a : Fin n | ¬ c a ≠ 0} = #{i : Fin n | c i = 0} := by
      apply Finset.card_nbij' id id <;> intro i hi <;> simp_all
    rw [hBeq] at hsum
    exact hsum
  have hz_lt : #{i : Fin n | c i = 0} < k := rs_zeros_lt hα hc hne
  omega

/-! ### Information-set count of codewords vanishing on a fixed zero-set. -/

/-- Helper: a codeword is determined by its values on any information set of size `k`.
    Concretely, if two codewords agree on a fixed `k`-subset `s` of coordinates, they are
    equal.  (MDS uniqueness / Lagrange interpolation injectivity.) -/
theorem rs_agree_on_kset {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α)
    {c d : Fin n → F} (hc : IsCodeword n k α c) (hd : IsCodeword n k α d)
    {s : Finset (Fin n)} (hs : k ≤ s.card) (hagree : ∀ i ∈ s, c i = d i) :
    c = d := by
  obtain ⟨p, hpdeg, hp⟩ := hc
  obtain ⟨q, hqdeg, hq⟩ := hd
  -- p - q has degree < k and vanishes on `α '' s`, of card ≥ k
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hs
  have himg_card : (t.image α).card = k := by
    rw [Finset.card_image_of_injective _ hα, ht_card]
  have hpq_deg : (p - q).degree < (t.image α).card := by
    rw [himg_card]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hpdeg hqdeg)
  have hpq_vanish : ∀ x ∈ t.image α, (p - q).eval x = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi_s : i ∈ s := ht_sub hi
    rw [Polynomial.eval_sub, ← hp, ← hq, hagree i hi_s, sub_self]
  have hpq0 : p - q = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (t.image α) hpq_deg hpq_vanish
  have hpeqq : p = q := by linear_combination (norm := ring_nf) hpq0
  funext i
  rw [hp, hq, hpeqq]

/-! ### Information-set count: codewords with a fixed zero-set of size `m`. -/

/-- The finite set of `RS[F,n,k]` codewords that VANISH on a fixed coordinate set `T`
    (i.e. `c i = 0` for every `i ∈ T`).  Decidability is supplied classically. -/
noncomputable def vanishCodewords (n k : ℕ) (α : Fin n → F) (T : Finset (Fin n)) :
    Finset (Fin n → F) := by
  classical
  exact (Finset.univ : Finset (Fin n → F)).filter
    (fun c => IsCodeword n k α c ∧ ∀ i ∈ T, c i = 0)

/-- **Information-set count (per-support MDS leading term).**
    The number of `RS[F,n,k]` codewords that vanish on a FIXED zero-set `T` of size `m`
    (with `m ≤ k ≤ n`) is at most `|F|^(k-m)`.

    This is the heart of the MDS weight enumerator: the codewords supported off `T` form a
    coset structure of dimension `k - m`, so there are at most `q^{k-m}` of them. -/
theorem rs_vanish_card_le {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α)
    {T : Finset (Fin n)} (hkn : k ≤ n) (hmk : T.card ≤ k) :
    (vanishCodewords n k α T).card ≤ (Fintype.card F) ^ (k - T.card) := by
  classical
  -- choose an information set `U ⊆ Tᶜ` of size `k - m`, disjoint from `T`
  set m := T.card with hm
  have hTc_card : Tᶜ.card = n - m := by
    rw [Finset.card_compl]; simp [hm, Fintype.card_fin]
  have hUexists : k - m ≤ Tᶜ.card := by rw [hTc_card]; omega
  obtain ⟨U, hU_sub, hU_card⟩ := Finset.exists_subset_card_eq hUexists
  -- restriction map: a codeword to its values on `U` (as a function on the subtype `↥U`)
  let restr : (Fin n → F) → (↥U → F) := fun c u => c u.1
  -- target Fintype has card |F|^(k-m)
  have hcardU : Fintype.card (↥U → F) = (Fintype.card F) ^ (k - m) := by
    rw [Fintype.card_fun]
    congr 1
    rw [Fintype.card_coe, hU_card]
  -- the restriction is injective on `vanishCodewords`
  have hinj : Set.InjOn restr (vanishCodewords n k α T : Set (Fin n → F)) := by
    intro c hc d hd hcd
    simp only [Finset.coe_filter, Set.mem_setOf_eq, vanishCodewords,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
    obtain ⟨hc_cw, hc_van⟩ := hc
    obtain ⟨hd_cw, hd_van⟩ := hd
    -- c and d agree on `T ∪ U`, of card `m + (k-m) = k`
    apply rs_agree_on_kset hα hc_cw hd_cw (s := T ∪ U)
    · -- |T ∪ U| ≥ k since T, U disjoint
      have hdisj : Disjoint T U := by
        apply Finset.disjoint_left.mpr
        intro a haT haU
        have : a ∈ Tᶜ := hU_sub haU
        simp [Finset.mem_compl] at this
        exact this haT
      rw [Finset.card_union_of_disjoint hdisj, hU_card]
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with hiT | hiU
      · rw [hc_van i hiT, hd_van i hiT]
      · -- on U, the restrictions agree
        have := congrFun hcd ⟨i, hiU⟩
        simpa [restr] using this
  -- conclude by card_le_card_of_injOn into univ
  calc (vanishCodewords n k α T).card
      ≤ (Finset.univ : Finset (↥U → F)).card :=
        Finset.card_le_card_of_injOn restr (fun _ _ => Finset.mem_univ _) hinj
    _ = Fintype.card (↥U → F) := by rw [Finset.card_univ]
    _ = (Fintype.card F) ^ (k - m) := hcardU

/-! ### The MDS leading-term list bound. -/

/-- The finite set ("list") of `RS[F,n,k]` codewords of weight at most `w`. -/
noncomputable def listAt (n k : ℕ) (α : Fin n → F) (w : ℕ) : Finset (Fin n → F) := by
  classical
  exact (Finset.univ : Finset (Fin n → F)).filter
    (fun c => IsCodeword n k α c ∧ wt c ≤ w)

/-- Every weight-`≤ w` codeword vanishes on SOME `(n-w)`-subset of coordinates:
    the list is contained in the union of `vanishCodewords T` over all `T` with
    `|T| = n - w`. -/
theorem listAt_subset_biUnion {n k : ℕ} {α : Fin n → F} {w : ℕ} (hw : w ≤ n) :
    listAt n k α w ⊆
      (Finset.powersetCard (n - w) (Finset.univ : Finset (Fin n))).biUnion
        (fun T => vanishCodewords n k α T) := by
  classical
  intro c hc
  simp only [listAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  obtain ⟨hc_cw, hc_wt⟩ := hc
  -- the zero-set of `c` has size `n - wt c ≥ n - w`
  have hzero_card : #{i : Fin n | c i = 0} = n - wt c := by
    have hsum : wt c + #{i : Fin n | c i = 0} = n := by
      unfold wt
      have hsum := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun i => c i ≠ 0)
      simp only [Finset.card_univ, Fintype.card_fin] at hsum
      have hBeq : #{a : Fin n | ¬ c a ≠ 0} = #{i : Fin n | c i = 0} := by
        apply Finset.card_nbij' id id <;> intro i hi <;> simp_all
      rw [hBeq] at hsum
      exact hsum
    omega
  -- so there is an `(n-w)`-subset `T` of the zero-set
  have hge : n - w ≤ #{i : Fin n | c i = 0} := by rw [hzero_card]; omega
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hge
  rw [Finset.mem_biUnion]
  refine ⟨T, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hT_card⟩
  · simp only [vanishCodewords, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hc_cw, ?_⟩
    intro i hiT
    have := hT_sub hiT
    simpa using this

/-- **THE MDS LEADING-TERM LIST BOUND.**
    For an RS code `RS[F,n,k]` (`k ≤ n`) and radius `w` with `n - k ≤ w ≤ n`, the number of
    codewords of weight at most `w` is bounded by

        |list(w)|  ≤  C(n, n-w) · q^(w-(n-k))   =   C(n, w) · q^(w-(n-k)),

    where `q = |F|` and `n-k` is one less than the minimum distance `d = n-k+1`.
    This is the leading-term / information-set upper bound on the cumulative MDS weight
    enumerator, valid all the way to the Singleton capacity. -/
theorem rs_list_leading_bound {n k : ℕ} {α : Fin n → F} (hα : Function.Injective α)
    {w : ℕ} (hkn : k ≤ n) (hw_hi : w ≤ n) (hw_lo : n - k ≤ w) :
    (listAt n k α w).card ≤ Nat.choose n (n - w) * (Fintype.card F) ^ (w - (n - k)) := by
  classical
  -- 1. list ⊆ biUnion of vanishCodewords over (n-w)-subsets
  have hsub := listAt_subset_biUnion (n := n) (k := k) (α := α) (w := w) hw_hi
  -- 2. card of biUnion ≤ sum of cards
  calc (listAt n k α w).card
      ≤ ((Finset.powersetCard (n - w) (Finset.univ : Finset (Fin n))).biUnion
          (fun T => vanishCodewords n k α T)).card := Finset.card_le_card hsub
    _ ≤ ∑ T ∈ Finset.powersetCard (n - w) (Finset.univ : Finset (Fin n)),
          (vanishCodewords n k α T).card := Finset.card_biUnion_le
    _ ≤ ∑ T ∈ Finset.powersetCard (n - w) (Finset.univ : Finset (Fin n)),
          (Fintype.card F) ^ (w - (n - k)) := by
        apply Finset.sum_le_sum
        intro T hT
        rw [Finset.mem_powersetCard] at hT
        obtain ⟨_, hTcard⟩ := hT
        -- per-support bound: each summand ≤ q^(k - |T|) = q^(k-(n-w)) = q^(w-(n-k))
        have hmk : T.card ≤ k := by rw [hTcard]; omega
        have hbound := rs_vanish_card_le hα (T := T) hkn hmk
        rw [hTcard] at hbound
        -- exponent: k - (n - w) = w - (n - k) since n-k ≤ w ≤ n and k ≤ n
        have hexp : k - (n - w) = w - (n - k) := by omega
        rw [hexp] at hbound
        exact hbound
    _ = Nat.choose n (n - w) * (Fintype.card F) ^ (w - (n - k)) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]

/-! ### Concrete, NON-VACUOUS instance over `ZMod 7`.

  We instantiate `RS[ZMod 7, n = 5, k = 2]` with evaluation points `α i = (i : ZMod 7)`
  (injective on `Fin 5`).  We exhibit a genuine NONZERO codeword `c i = (i : ZMod 7)`
  (the evaluation of the degree-1 polynomial `X`), so every hypothesis is satisfiable and
  none of the results is vacuously about an empty object.
-/

section Concrete

/-- `7` is prime, supplying the `Field (ZMod 7)` instance. -/
instance primeFact_RSMDSListBound_1 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Evaluation points for the concrete `RS[ZMod 7, 5, 2]`: the first five field elements. -/
def α₀ : Fin 5 → ZMod 7 := fun i => (i.val : ZMod 7)

/-- `α₀` is injective: distinct indices in `Fin 5` give distinct elements of `ZMod 7`. -/
theorem α₀_injective : Function.Injective α₀ := by
  intro i j h
  simp only [α₀] at h
  -- the natural representatives are < 5 < 7, so equality in ZMod 7 forces equality of vals
  have hi : (i.val : ZMod 7).val = i.val := by
    rw [ZMod.val_natCast]; omega
  have hj : (j.val : ZMod 7).val = j.val := by
    rw [ZMod.val_natCast]; omega
  have : i.val = j.val := by rw [← hi, ← hj, h]
  exact Fin.ext this

/-- The concrete NONZERO codeword `c₀ i = (i : ZMod 7)`, evaluation of `X` (degree `1 < 2`). -/
def c₀ : Fin 5 → ZMod 7 := fun i => (i.val : ZMod 7)

/-- `c₀` is a genuine `RS[ZMod 7, 5, 2]` codeword (witnessing satisfiability of `IsCodeword`). -/
theorem c₀_isCodeword : IsCodeword 5 2 α₀ c₀ := by
  refine ⟨Polynomial.X, ?_, ?_⟩
  · rw [Polynomial.degree_X]
    norm_num
  · intro i; simp [c₀, α₀]

/-- `c₀` is NONZERO (e.g. its value at index `1` is `1 ≠ 0`), so the MDS-distance result
    `rs_codeword_weight_ge` applies non-vacuously. -/
theorem c₀_ne_zero : c₀ ≠ 0 := by
  intro h
  have : c₀ 1 = 0 := by rw [h]; rfl
  simp only [c₀] at this
  revert this; decide

/-- Non-vacuity of the MDS-distance theorem: applied to the concrete nonzero codeword `c₀`,
    `rs_codeword_weight_ge` yields the genuine Singleton bound `5 + 1 ≤ wt c₀ + 2`,
    i.e. `wt c₀ ≥ 4 = n - k + 1`. -/
theorem c₀_mds_distance : 5 + 1 ≤ wt c₀ + 2 :=
  rs_codeword_weight_ge α₀_injective c₀_isCodeword c₀_ne_zero

/-- Non-vacuity of the list: the weight-`≤ 5` list for `RS[ZMod 7, 5, 2]` is NONEMPTY
    (it contains the nonzero codeword `c₀`, whose weight is `4 ≤ 5`). Hence the list-bound
    theorem `rs_list_leading_bound` is a statement about a genuinely inhabited finite set. -/
theorem listAt_nonempty : (listAt 5 2 α₀ 5).Nonempty := by
  classical
  refine ⟨c₀, ?_⟩
  simp only [listAt, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨c₀_isCodeword, ?_⟩
  -- weight of c₀ is 4 ≤ 5
  have hwt : wt c₀ + 2 ≥ 6 := c₀_mds_distance
  have hle : wt c₀ ≤ 5 := by
    unfold wt
    have := Finset.card_le_univ (Finset.univ.filter (fun i : Fin 5 => c₀ i ≠ 0))
    simpa using this
  exact hle

/-- Non-vacuity / sanity of the leading-term list bound on the concrete instance:
    `|list(5)| ≤ C(5,0) · 7^(5-3) = 1 · 49 = 49`.  (Here `n=5, k=2, w=5`, so `n-k=3`,
    `n-w=0`, `w-(n-k)=2`.)  The list is nonempty, so this is a real, non-vacuous bound. -/
theorem c₀_list_bound : (listAt 5 2 α₀ 5).card ≤ Nat.choose 5 0 * (Fintype.card (ZMod 7)) ^ 2 := by
  have h := rs_list_leading_bound (n := 5) (k := 2) (α := α₀) (w := 5)
    α₀_injective (by omega) (by omega) (by omega)
  -- normalise the exponents/choose computed by the theorem to the displayed form
  simpa using h

end Concrete

end RSAsymptKernel

-- Axiom audit of the main MDS leading-term list bound and the concrete instance.
#print axioms RSAsymptKernel.rs_list_leading_bound
#print axioms RSAsymptKernel.rs_codeword_weight_ge
#print axioms RSAsymptKernel.rs_vanish_card_le
#print axioms RSAsymptKernel.c₀_list_bound
#print axioms RSAsymptKernel.listAt_nonempty
