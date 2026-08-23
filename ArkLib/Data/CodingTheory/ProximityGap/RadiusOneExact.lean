/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.RadiusOne

/-!
# The EXACT radius-one MCA error `ε_mca(RS, 1)` and the decided §1 MCA prize

`GrandChallengeRadiusOne.lean` proves the upper bound
`ε_mca(RS, 1) ≤ C(n, k+1) / |F|` (`epsMCA_one_le_choose_div`). This file proves the
**matching lower bound** in the large-field regime, yielding the *exact* value

  `ε_mca(RS, 1) = C(n, k+1) / |F|`  (`epsMCA_one_eq_choose_div`)

whenever `k + 1 ≤ n` and `|F| > C(C(n, k+1), 2)`, and uses it to **decide** the formal §1
Grand MCA Challenge for Reed–Solomon by the single inequality `C(n, k+1)/|F| ≤ ε*`
(`grandMCAChallenge_iff_choose_le`).

## Strategy for the lower bound

Fix the *deep-hole* second word `u₁ i := (domain i) ^ k` (evaluations of `Xᵏ`). For every
`(k+1)`-subset `T` of `ι`, the unique degree-`≤ k` interpolant of `u₁` through `T` is `Xᵏ`
itself, which has degree exactly `k`, so `u₁` is **non-extendable** on `T`.

The `Xᵏ`-coefficient functional `c_T(u) := (Lagrange.interpolate T domain u).coeff k` is
`F`-linear, satisfies `c_T(u₁) = 1`, and a word `u` is extendable on `T` iff `c_T(u) = 0`.
For a first word `u₀`, the line `u₀ + γ • u₁` is extendable on `T` iff `γ = -c_T(u₀) =: γ_T`,
so each `γ_T` realises `mcaEvent` with witness `T`. The functionals `c_T` are pairwise
distinct (separated by an indicator word), so the `c_T(u₀)` — hence the `γ_T` — can be made
pairwise distinct by avoiding the `C(C(n, k+1), 2)` hyperplanes `{c_T = c_{T'}}`, a union
of `q^{n-1}`-sized kernels that does not cover `(ι → F)` once `q > C(C(n,k+1), 2)`. The bad
`γ`-set then contains the `C(n, k+1)` distinct `γ_T`, giving `Pr_γ ≥ C(n,k+1)/q`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Polynomial ReedSolomon
open scoped ProbabilityTheory BigOperators

section Exact

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The `Xᵏ`-coefficient functional of the Lagrange interpolant through a node set `T`.
For `T` of size `k + 1` this is `c_T(u) = ∑ i ∈ T, u i / ∏ j ∈ T \ {i}, (domain i - domain j)`,
the leading coefficient of the interpolant; it is `F`-linear in `u`. -/
noncomputable def cT (domain : ι ↪ F) (k : ℕ) (T : Finset ι) : (ι → F) →ₗ[F] F :=
  (Polynomial.lcoeff F k).comp (Lagrange.interpolate T (fun i => domain i))

lemma cT_apply (domain : ι ↪ F) (k : ℕ) (T : Finset ι) (u : ι → F) :
    cT domain k T u = (Lagrange.interpolate T (fun i => domain i) u).coeff k := rfl

/-- The deep-hole word: evaluations of `Xᵏ`. -/
noncomputable def deepHole (domain : ι ↪ F) (k : ℕ) : ι → F := fun i => (domain i) ^ k

/-- **Key identity `c_T(u₁) = 1`.** For a `(k+1)`-subset `T`, the interpolant of the deep-hole
word `deepHole = (Xᵏ ∘ domain)` through `T` is `Xᵏ` itself, whose `k`-th coefficient is `1`. -/
lemma cT_deepHole (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1) :
    cT domain k T (deepHole domain k) = 1 := by
  have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  -- interpolant of (fun i => (X^k).eval (domain i)) through T is X^k since deg X^k = k < #T
  have hdeg : (X ^ k : F[X]).degree < (T.card : WithBot ℕ) := by
    rw [hT]
    calc (X ^ k : F[X]).degree ≤ (k : WithBot ℕ) := degree_X_pow_le k
      _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
  have hpoly : Lagrange.interpolate T (fun i => domain i)
      (fun i => (X ^ k : F[X]).eval (domain i)) = X ^ k :=
    (Lagrange.eq_interpolate hinj hdeg).symm
  have hval : (deepHole domain k) = (fun i => (X ^ k : F[X]).eval (domain i)) := by
    funext i; simp [deepHole, eval_pow, eval_X]
  rw [cT_apply, hval, hpoly]
  rw [coeff_X_pow, if_pos rfl]

/-- **Extendability ⟺ `c_T = 0`.** For a `(k+1)`-subset `T`, a word `u` agrees on `T` with some
RS codeword iff its interpolant has vanishing `k`-th coefficient, i.e. `c_T(u) = 0`. -/
lemma extendable_iff_cT_eq_zero (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1)
    (u : ι → F) :
    (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ T, w i = u i) ↔
      cT domain k T u = 0 := by
  have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  set p : F[X] := Lagrange.interpolate T (fun i => domain i) u with hp
  have hpdeg : p.degree < (T.card : WithBot ℕ) := Lagrange.degree_interpolate_lt _ hinj
  have hpeval : ∀ i ∈ T, p.eval (domain i) = u i := fun i hi =>
    Lagrange.eval_interpolate_at_node u hinj hi
  constructor
  · -- extendable ⇒ the extending codeword's poly equals p, has degree < k ⇒ coeff k = 0
    rintro ⟨w, hw, hwagree⟩
    rw [SetLike.mem_coe, mem_code_iff_exists_polynomial] at hw
    obtain ⟨q, hqdeg, hq⟩ := hw
    -- q and p agree on T (size k+1) and both degree < k+1, so q = p
    have hqeval : ∀ i ∈ T, q.eval (domain i) = u i := by
      intro i hi
      have : w i = q.eval (domain i) := congrFun hq i
      rw [← this, hwagree i hi]
    have hqdeg' : q.degree < (T.card : WithBot ℕ) := by
      rw [hT]
      calc q.degree < (k : WithBot ℕ) := hqdeg
        _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
    have hqp : q = p := by
      refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := T) (v := fun i => domain i)
        hinj hqdeg' hpdeg ?_
      intro i hi
      rw [hqeval i hi, ← hpeval i hi]
    -- coeff k of p = coeff k of q = 0 since deg q < k
    rw [cT_apply, ← hp, ← hqp]
    exact Polynomial.coeff_eq_zero_of_degree_lt hqdeg
  · -- c_T u = 0 ⇒ p has degree < k ⇒ p is a deg<k poly extending u on T
    intro hc
    rw [cT_apply, ← hp] at hc
    have hpdeg_k : p.degree < (k : WithBot ℕ) := by
      -- p.degree ≤ k (since < k+1) and coeff k = 0 ⇒ degree < k
      have hle : p.degree ≤ (k : WithBot ℕ) := by
        rw [hT] at hpdeg
        exact Order.le_of_lt_succ (by exact_mod_cast hpdeg)
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · -- degree = k but coeff k = 0 is impossible unless... use leadingCoeff
        exfalso
        have hk : p.natDegree = k := natDegree_eq_of_degree_eq_some h
        have : p.coeff k ≠ 0 := by
          rw [← hk]
          exact Polynomial.leadingCoeff_ne_zero.mpr (by
            intro h0; rw [h0, degree_zero] at h; exact absurd h.symm (by simp))
        exact this hc
    refine ⟨evalOnPoints domain p, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_code_iff_exists_polynomial]
      exact ⟨p, hpdeg_k, rfl⟩
    · intro i hi
      change p.eval (domain i) = u i
      exact hpeval i hi

/-- The deep-hole word `u₁ = (Xᵏ ∘ domain)` is non-extendable on every `(k+1)`-subset. -/
lemma nonExtendable_deepHole (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1) :
    NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) T (deepHole domain k) := by
  rw [NonExtendableOn, extendable_iff_cT_eq_zero domain hT, cT_deepHole domain hT]
  exact one_ne_zero

/-- **`γ_T := -c_T(u₀)` makes the line extendable on `T`.** For any first word `u₀`, the line
`u₀ + γ • u₁` is extendable on a `(k+1)`-subset `T` iff `γ = -c_T(u₀)`. -/
lemma line_extendable_iff (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1)
    (u₀ : ι → F) (γ : F) :
    (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ T, w i = u₀ i + γ • (deepHole domain k) i)
      ↔ γ = -cT domain k T u₀ := by
  rw [extendable_iff_cT_eq_zero domain hT]
  -- the function `fun i => u₀ i + γ • deepHole i` is `u₀ + γ • deepHole` as a `Pi`
  have hfun : (fun i => u₀ i + γ • (deepHole domain k) i)
      = u₀ + γ • deepHole domain k := rfl
  rw [hfun]
  -- c_T (u₀ + γ • u₁) = c_T u₀ + γ • c_T u₁ = c_T u₀ + γ
  have hlin : cT domain k T (u₀ + γ • deepHole domain k)
      = cT domain k T u₀ + γ * cT domain k T (deepHole domain k) := by
    rw [map_add, map_smul, smul_eq_mul]
  rw [hlin, cT_deepHole domain hT, mul_one]
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; ring

/-- **Each `γ_T` realises `mcaEvent`.** With the deep-hole second word, for any first word `u₀`
and any `(k+1)`-subset `T`, the scalar `γ := -c_T(u₀)` satisfies `mcaEvent (RS) 1 u₀ u₁ γ`
with witness set `T`. -/
lemma mcaEvent_at_gammaT (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1)
    (u₀ : ι → F) :
    mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ (deepHole domain k)
      (-cT domain k T u₀) := by
  refine ⟨T, ?_, ?_, ?_⟩
  · -- size clause vacuous at δ = 1: (1 - 1) * n = 0 ≤ card
    simp
  · -- line extendable on T at γ = -c_T(u₀)
    exact (line_extendable_iff domain hT u₀ _).mpr rfl
  · -- no joint pair: u₁ non-extendable on T
    rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    exact nonExtendable_deepHole domain hT ⟨v₁, hv₁, fun i hi => (hagree i hi).2⟩

/-- **Separation of distinct functionals.** For two distinct `(k+1)`-subsets `T ≠ T'`, the
linear functional `c_T - c_{T'}` is nonzero: pick `i₀ ∈ T \ T'` and evaluate at the indicator
word `e_{i₀}`, where `c_T(e_{i₀}) ≠ 0 = c_{T'}(e_{i₀})`. -/
lemma cT_sub_ne_zero (domain : ι ↪ F) {k : ℕ} {T T' : Finset ι}
    (hT : T.card = k + 1) (hT' : T'.card = k + 1) (hne : T ≠ T') :
    cT domain k T - cT domain k T' ≠ 0 := by
  classical
  -- pick i₀ ∈ T \ T'  (cards equal, sets distinct ⇒ some element of T not in T')
  have hexists : ∃ i₀ ∈ T, i₀ ∉ T' := by
    by_contra h
    push Not at h
    -- T ⊆ T' and equal cards ⇒ T = T'
    exact hne (Finset.eq_of_subset_of_card_le h (le_of_eq (hT'.trans hT.symm)))
  obtain ⟨i₀, hi₀T, hi₀T'⟩ := hexists
  -- indicator word e_{i₀}
  set e : ι → F := fun i => if i = i₀ then 1 else 0 with he
  intro hcontra
  -- c_{T'}(e) = 0: e restricted to T' is the zero word (i₀ ∉ T'), interpolant is 0
  have hcT'e : cT domain k T' e = 0 := by
    have hzero : (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ T', w i = e i) := by
      refine ⟨0, (ReedSolomon.code domain k).zero_mem, ?_⟩
      intro i hi
      have : i ≠ i₀ := fun h => hi₀T' (h ▸ hi)
      simp [he, this]
    exact (extendable_iff_cT_eq_zero domain hT' e).mp hzero
  -- c_T(e) ≠ 0: e is NOT extendable on T, since e|T has a single 1 at i₀ — the interpolant
  -- is a nonzero Lagrange basis polynomial of degree k.
  have hcTe : cT domain k T e ≠ 0 := by
    rw [cT_apply]
    -- interpolant of e through T = (Lagrange.basis T domain i₀), a degree-k poly, coeff k ≠ 0
    have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) :=
      fun _ _ _ _ h => domain.injective h
    have hbasis : Lagrange.interpolate T (fun i => domain i) e = Lagrange.basis T (fun i => domain i) i₀ := by
      rw [Lagrange.interpolate_apply]
      rw [← Finset.add_sum_erase _ _ hi₀T]
      have h1 : C (e i₀) * Lagrange.basis T (fun i => domain i) i₀
          = Lagrange.basis T (fun i => domain i) i₀ := by
        simp [he]
      rw [h1]
      have h0 : ∑ i ∈ T.erase i₀, C (e i) * Lagrange.basis T (fun i => domain i) i = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have : i ≠ i₀ := (Finset.mem_erase.mp hi).1
        simp [he, this]
      rw [h0, add_zero]
    rw [hbasis]
    -- coeff k of basis = leadingCoeff (since natDegree basis = #T - 1 = k) ≠ 0
    have hnatdeg : (Lagrange.basis T (fun i => domain i) i₀).natDegree = k := by
      rw [Lagrange.natDegree_basis hinj hi₀T, hT]; omega
    rw [← hnatdeg, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr (Lagrange.basis_ne_zero hinj hi₀T)
  -- contradiction: applying the zero functional to e gives c_T e - c_{T'} e = 0
  have := congrFun (congrArg (DFunLike.coe) hcontra) e
  simp only [LinearMap.sub_apply, LinearMap.zero_apply, hcT'e, sub_zero] at this
  exact hcTe this

/-- **Kernel cardinality of a nonzero functional.** A nonzero linear functional
`φ : (ι → F) →ₗ[F] F` has kernel of `F`-dimension `n - 1`, hence the set of its zeros has
cardinality `q^{n-1}`. -/
lemma card_ker_eq (φ : (ι → F) →ₗ[F] F) (hφ : φ ≠ 0) :
    Nat.card (LinearMap.ker φ) = Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  have : Fintype (LinearMap.ker φ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  -- finrank of kernel = n - 1 by rank-nullity + surjectivity (range = ⊤, finrank 1)
  have hsurj : Function.Surjective φ := by
    -- pick u₀ with φ u₀ ≠ 0, then a = φ ((a / φ u₀) • u₀)
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, φ u₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    intro a
    refine ⟨(a / φ u₀) • u₀, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hu₀]
  have hrange : Module.finrank F (LinearMap.range φ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, Module.finrank_pi (R := F) (ι := ι)] at hrn
  have hker : Module.finrank F (LinearMap.ker φ) = Fintype.card ι - 1 := by omega
  rw [Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker φ), hker]

/-- **Bad-set cardinality bound.** For each pair of distinct subsets, the set of words on which
the two functionals agree has cardinality `q^{n-1}`. Translating to the filter `Finset`. -/
lemma card_agree_le (domain : ι ↪ F) {k : ℕ} {T T' : Finset ι}
    (hT : T.card = k + 1) (hT' : T'.card = k + 1) (hne : T ≠ T') :
    (Finset.univ.filter (fun u : ι → F => cT domain k T u = cT domain k T' u)).card
      = Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  set φ : (ι → F) →ₗ[F] F := cT domain k T - cT domain k T' with hφdef
  have hφ : φ ≠ 0 := cT_sub_ne_zero domain hT hT' hne
  have hFin : Fintype (LinearMap.ker φ) := Fintype.ofFinite _
  -- the filter predicate coincides with membership in `ker φ`
  have hpred : ∀ u : ι → F, (cT domain k T u = cT domain k T' u) ↔ (φ u = 0) := by
    intro u
    rw [hφdef]
    simp only [LinearMap.sub_apply]
    constructor
    · intro h; rw [h]; ring
    · intro h; exact sub_eq_zero.mp h
  -- rewrite filter card via the subtype card of the kernel
  rw [Finset.filter_congr (q := fun u : ι → F => φ u = 0) (fun u _ => hpred u)]
  rw [show (Finset.univ.filter (fun u : ι → F => φ u = 0)).card
        = Fintype.card { u : ι → F // φ u = 0 } from
      (Fintype.card_subtype (fun u : ι → F => φ u = 0)).symm]
  rw [show Fintype.card { u : ι → F // φ u = 0 } = Nat.card (LinearMap.ker φ) from ?_]
  · exact card_ker_eq φ hφ
  · rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun u => by rw [LinearMap.mem_ker]))

/-- **Hyperplane avoidance.** If `q > C(C(n, k+1), 2)`, there is a first word `u₀` for which the
functionals `c_T` (over `(k+1)`-subsets `T`) take pairwise distinct values: the union of the
`C(C(n,k+1),2)` "agreement hyperplanes" `{u | c_T u = c_{T'} u}` (each of size `q^{n-1}`) does
not cover all `q^n` words. -/
lemma exists_u0_injOn_cT (domain : ι ↪ F) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (hq : (Nat.choose (Fintype.card ι) (k + 1)).choose 2 < Fintype.card F) :
    ∃ u₀ : ι → F, ∀ T ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
      ∀ T' ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
        cT domain k T u₀ = cT domain k T' u₀ → T = T' := by
  classical
  set n := Fintype.card ι with hn
  set Subs := (Finset.univ : Finset ι).powersetCard (k + 1) with hSubs
  -- the set of "bad" first words (some pair of distinct subsets gives equal functionals)
  set bad : Finset (ι → F) := Finset.univ.filter
    (fun u => ∃ T ∈ Subs, ∃ T' ∈ Subs, T ≠ T' ∧ cT domain k T u = cT domain k T' u) with hbad
  -- it suffices to find u₀ ∉ bad
  suffices hsuff : ∃ u₀, u₀ ∉ bad by
    obtain ⟨u₀, hu₀⟩ := hsuff
    refine ⟨u₀, fun T hT T' hT' heq => ?_⟩
    by_contra hTne
    exact hu₀ (by rw [hbad, Finset.mem_filter]; exact ⟨Finset.mem_univ _, T, hT, T', hT', hTne, heq⟩)
  -- bound: card bad < card univ = q^n  ⇒  bad ≠ univ  ⇒  ∃ u₀ ∉ bad
  have hcard_univ : (Finset.univ : Finset (ι → F)).card = Fintype.card F ^ n := by
    rw [Finset.card_univ, Fintype.card_pi]; simp [hn]
  -- bad ⊆ ⋃ over the 2-subsets of Subs of the agreement filters
  set Pairs := Subs.powersetCard 2 with hPairs
  have hbad_sub : bad ⊆ Pairs.biUnion (fun P =>
      Finset.univ.filter (fun u : ι → F =>
        ∃ T ∈ P, ∃ T' ∈ P, T ≠ T' ∧ cT domain k T u = cT domain k T' u)) := by
    intro u hu
    rw [hbad, Finset.mem_filter] at hu
    obtain ⟨_, T, hT, T', hT', hTne, heq⟩ := hu
    rw [Finset.mem_biUnion]
    refine ⟨{T, T'}, ?_, ?_⟩
    · rw [hPairs, Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hT
        · exact (Finset.mem_singleton.mp h) ▸ hT'
      · rw [Finset.card_insert_of_notMem (by simp [hTne]), Finset.card_singleton]
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, T, Finset.mem_insert_self _ _, T',
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hTne, heq⟩
  -- each agreement filter (over a 2-element pair) has card ≤ q^(n-1)
  have heach : ∀ P ∈ Pairs,
      (Finset.univ.filter (fun u : ι → F =>
        ∃ T ∈ P, ∃ T' ∈ P, T ≠ T' ∧ cT domain k T u = cT domain k T' u)).card
        ≤ Fintype.card F ^ (n - 1) := by
    intro P hP
    rw [hPairs, Finset.mem_powersetCard] at hP
    obtain ⟨hPsub, hPcard⟩ := hP
    -- P = {T, T'} with T ≠ T', both (k+1)-subsets
    obtain ⟨T, T', hTne, hPeq⟩ := Finset.card_eq_two.mp hPcard
    have hTmem : T ∈ Subs := hPsub (hPeq ▸ Finset.mem_insert_self _ _)
    have hT'mem : T' ∈ Subs := hPsub (hPeq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hSubs, Finset.mem_powersetCard] at hTmem hT'mem
    -- the filter is contained in the single agreement filter for (T, T')
    have hsub : (Finset.univ.filter (fun u : ι → F =>
        ∃ S ∈ P, ∃ S' ∈ P, S ≠ S' ∧ cT domain k S u = cT domain k S' u))
        ⊆ Finset.univ.filter (fun u : ι → F => cT domain k T u = cT domain k T' u) := by
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨S, hS, S', hS', hSne, hSeq⟩ := hu.2
      -- S, S' ∈ {T, T'}, distinct ⇒ {S,S'} = {T,T'}; so c_T u = c_{T'} u
      rw [hPeq, Finset.mem_insert, Finset.mem_singleton] at hS hS'
      rcases hS with hSa | hSa <;> rcases hS' with hSb | hSb
      · exact absurd (hSa.trans hSb.symm) hSne
      · exact (congrArg (fun (R : Finset ι) => cT domain k R u) hSa).symm.trans
          (hSeq.trans (congrArg (fun (R : Finset ι) => cT domain k R u) hSb))
      · exact (congrArg (fun (R : Finset ι) => cT domain k R u) hSb).symm.trans
          (hSeq.symm.trans (congrArg (fun (R : Finset ι) => cT domain k R u) hSa))
      · exact absurd (hSa.trans hSb.symm) hSne
    calc _ ≤ (Finset.univ.filter (fun u : ι → F =>
            cT domain k T u = cT domain k T' u)).card := Finset.card_le_card hsub
      _ = Fintype.card F ^ (n - 1) := card_agree_le domain hTmem.2 hT'mem.2 hTne
  -- assemble the union bound
  have hbad_card : bad.card ≤ ((Nat.choose n (k + 1)).choose 2) * Fintype.card F ^ (n - 1) := by
    calc bad.card ≤ (Pairs.biUnion _).card := Finset.card_le_card hbad_sub
      _ ≤ ∑ P ∈ Pairs, (Finset.univ.filter (fun u : ι → F =>
            ∃ T ∈ P, ∃ T' ∈ P, T ≠ T' ∧ cT domain k T u = cT domain k T' u)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ Pairs, Fintype.card F ^ (n - 1) := Finset.sum_le_sum heach
      _ = Pairs.card * Fintype.card F ^ (n - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ = ((Nat.choose n (k + 1)).choose 2) * Fintype.card F ^ (n - 1) := by
          rw [hPairs, Finset.card_powersetCard, hSubs, Finset.card_powersetCard, Finset.card_univ,
            ← hn]
  -- q^(n-1) * q = q^n, and #pairs < q, so card bad < q^n
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hn1 : n - 1 + 1 = n := by omega
  have hstrict : bad.card < Fintype.card F ^ n := by
    calc bad.card ≤ ((Nat.choose n (k + 1)).choose 2) * Fintype.card F ^ (n - 1) := hbad_card
      _ < Fintype.card F * Fintype.card F ^ (n - 1) := by
          have hpp : 0 < Fintype.card F ^ (n - 1) := pow_pos hpos _
          exact Nat.mul_lt_mul_of_pos_right hq hpp
      _ = Fintype.card F ^ n := by rw [← pow_succ', hn1]
  -- card bad < card univ ⇒ ∃ u₀ ∉ bad
  by_contra hcon
  push Not at hcon
  have hbeq : bad = Finset.univ := Finset.eq_univ_of_forall hcon
  rw [hbeq, hcard_univ] at hstrict
  exact lt_irrefl _ hstrict

/-- **Lower-bound counting.** With the deep-hole second word and a first word `u₀` separating all
the `c_T`, the bad `γ`-set contains the `C(n,k+1)` distinct values `γ_T = -c_T(u₀)`, so
`Pr_γ[mcaEvent] ≥ C(n,k+1)/q`. -/
lemma mcaEvent_prob_ge (domain : ι ↪ F) {k : ℕ} {u₀ : ι → F}
    (hu₀ : ∀ T ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
      ∀ T' ∈ (Finset.univ : Finset ι).powersetCard (k + 1),
        cT domain k T u₀ = cT domain k T' u₀ → T = T') :
    (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) ≤
      Pr_{ let γ ←$ᵖ F }[ mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀
        (deepHole domain k) γ ] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  set Subs := (Finset.univ : Finset ι).powersetCard (k + 1) with hSubs
  set Bad := Finset.univ.filter
    (fun γ : F => mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ (deepHole domain k) γ)
    with hBad
  -- the map T ↦ -c_T(u₀) injects Subs into Bad
  set g : Finset ι → F := fun T => -cT domain k T u₀ with hg
  have hmaps : ∀ T ∈ Subs, g T ∈ Bad := by
    intro T hT
    rw [hSubs, Finset.mem_powersetCard] at hT
    rw [hBad, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mcaEvent_at_gammaT domain hT.2 u₀⟩
  have hinj : Set.InjOn g (↑Subs) := by
    intro T hT T' hT' hgeq
    rw [Finset.mem_coe] at hT hT'
    apply hu₀ T hT T' hT'
    have : cT domain k T u₀ = cT domain k T' u₀ := by
      have := hgeq; rw [hg] at this; simpa using neg_injective this
    exact this
  -- therefore #Subs ≤ #Bad
  have hcard_le : Subs.card ≤ Bad.card :=
    Finset.card_le_card_of_injOn g hmaps hinj
  rw [hSubs, Finset.card_powersetCard, Finset.card_univ] at hcard_le
  -- push to ENNReal division
  have hnum : (↑(Nat.choose (Fintype.card ι) (k + 1)) : ENNReal) ≤ (↑(↑Bad.card : ℝ≥0) : ENNReal) := by
    exact_mod_cast hcard_le
  have hden : (↑(↑(Fintype.card F) : ℝ≥0) : ENNReal) = (↑(Fintype.card F) : ENNReal) := by
    push_cast; rfl
  rw [hden]
  gcongr

/-- **Lower bound on the radius-one MCA error.** For `C := RS[F, domain, k]` with `k + 1 ≤ n`
and `q > C(C(n, k+1), 2)`: `ε_mca(C, 1) ≥ C(n, k+1) / q`. -/
theorem epsMCA_one_ge_choose_div (domain : ι ↪ F) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (hq : (Nat.choose (Fintype.card ι) (k + 1)).choose 2 < Fintype.card F) :
    (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  obtain ⟨u₀, hu₀⟩ := exists_u0_injOn_cT domain hk hq
  have hpr := mcaEvent_prob_ge domain hu₀
  refine le_trans hpr ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 (u 0) (u 1) γ ])
    (Code.finMapTwoWords u₀ (deepHole domain k))

/-- **EXACT radius-one MCA value.** For `C := RS[F, domain, k]` with injective `domain`,
`n := |ι|`, `k + 1 ≤ n`, and `q := |F| > C(C(n, k+1), 2)`:

  `ε_mca(C, 1) = C(n, k+1) / |F|`. -/
theorem epsMCA_one_eq_choose_div (domain : ι ↪ F) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (hq : (Nat.choose (Fintype.card ι) (k + 1)).choose 2 < Fintype.card F) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 =
      (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) :=
  le_antisymm (epsMCA_one_le_choose_div domain k) (epsMCA_one_ge_choose_div domain hk hq)

/-- **The formal §1 Grand MCA Challenge for Reed–Solomon is decided by a single inequality.**
Under `k + 1 ≤ n` and `q > C(C(n, k+1), 2)`, the Grand MCA Challenge holds for `RS[F, domain, k]`
at threshold `ε*` iff `C(n, k+1) / |F| ≤ ε*`. -/
theorem grandMCAChallenge_iff_choose_le (domain : ι ↪ F) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (hq : (Nat.choose (Fintype.card ι) (k + 1)).choose 2 < Fintype.card F) (ε_star : ℝ≥0) :
    grandMCAChallenge (ReedSolomon.code domain k) ε_star ↔
      (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal)
        ≤ (ε_star : ENNReal) := by
  rw [grandMCAChallenge_iff_epsMCA_one, epsMCA_one_eq_choose_div domain hk hq]

/-- **Per-window γ-uniqueness (reducible half of the radius-`1/n` J1 bad-scalar cap, issue #65).**

Fix a window `S` on which `u₁` is non-extendable for the degree-`<k` Reed–Solomon code.  Then at
most one scalar `γ` makes the line word `u₀ + γ • u₁` locally extendable on every `(k+1)`-subset
of `S` — i.e. satisfies `∀ T ⊆ S, T.card = k+1 → cT T (u₀ + γ • u₁) = 0`.

So each non-extendable window pins the J1 ratio scalar uniquely: the J1 bad-scalar set
(`GrandChallengesLattice.j1RatioConstraintBadScalars`) injects into the set of non-extendable
windows via `γ ↦ S`.  The remaining (genuinely harder) core of the `card ≤ 2` cap is bounding the
number of *contributing* windows among `univ` and the `n` one-point-deleted windows
`univ.erase i`.

Proof: from non-extendability extract a `(k+1)`-subset `T ⊆ S` with `u₁` non-extendable on `T`
(`exists_card_eq_subset_nonExtendable`); `cT T (u₀ + γ • u₁) = 0` then yields, via
`extendable_iff_cT_eq_zero`, an RS codeword agreeing with the line on `T`, and
`unique_gamma_of_nonExtendable` pins `γ`. -/
theorem j1_unique_gamma_of_nonExtendableOn
    (domain : ι ↪ F) {k : ℕ} {S : Finset ι} {u₀ u₁ : ι → F}
    (hne : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁)
    {γ γ' : F}
    (hγ : ∀ T : Finset ι, T ⊆ S → T.card = k + 1 → cT domain k T (u₀ + γ • u₁) = 0)
    (hγ' : ∀ T : Finset ι, T ⊆ S → T.card = k + 1 → cT domain k T (u₀ + γ' • u₁) = 0) :
    γ = γ' := by
  obtain ⟨T, hTS, hTcard, hneT⟩ := exists_card_eq_subset_nonExtendable domain hne
  obtain ⟨w₁, hw₁mem, hw₁⟩ :=
    (extendable_iff_cT_eq_zero domain hTcard (u₀ + γ • u₁)).mpr (hγ T hTS hTcard)
  obtain ⟨w₂, hw₂mem, hw₂⟩ :=
    (extendable_iff_cT_eq_zero domain hTcard (u₀ + γ' • u₁)).mpr (hγ' T hTS hTcard)
  have h₁' : ∀ i ∈ T, w₁ i = u₀ i + γ • u₁ i := by
    intro i hi; simpa using hw₁ i hi
  have h₂' : ∀ i ∈ T, w₂ i = u₀ i + γ' • u₁ i := by
    intro i hi; simpa using hw₂ i hi
  exact unique_gamma_of_nonExtendable domain hneT hw₁mem hw₂mem h₁' h₂'

end Exact

end ProximityGap
