/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import ArkLib.Research.ProximityGap.Frontier.LinearPencilFreshLabels
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import ArkLib.Research.ProximityGap.Support.BinaryPower
import ArkLib.Research.ProximityGap.RankJohnsonComparison
import ArkLib.Research.ProximityGap.KKH26RegimeSplit

/-! # Domain-independent `2n + 2` barrier at the quarter-rate Johnson sign pivot

For every quarter-rate parameter `d ≥ 3` (`k = d + 1`, `n = 4(d + 1)`, `t = 2d + 1`,
`e = 2d + 3 = n/2 + 1`), the error fraction `e/n` sits strictly below the finite-length
Johnson radius `1 - √(d/n)` because `(n - e)^2 = (2d + 1)^2 = n · d + 1 > n · d`, while
the next Hamming step `e + 1` crosses strictly above it.

Whenever a finite field `F` contains a primitive `(d - 1)`-th root of unity `ω` and two
nonzero elements `u₀, v₀` with `1, u₀^(d-1), v₀^(d-1)` pairwise distinct and
`Choose(8d + 10, 2) ≤ |F|`, an explicit 4-head pencil with zero search produces
`8d + 10 = 2n + 2` distinct fresh MCA bad scalars on any `n`-element evaluation domain
containing the three cosets `⟨ω⟩, u₀⟨ω⟩, v₀⟨ω⟩`:

- `g₁₂(X) = X^(d-1) - 1`, `g₁₃(X) = λ(X^(d-1) - r₀)` with `λ = (s₀ - 1)/(s₀ - r₀)`;
- Head 0: `(0, 0, 0)` with core `B₁₂ ∪ B₁₃ ∪ E₁` (size `2d`);
- Head 1: `(0, X·g₁₂, g₁₂)` with core `B₁₂ ∪ B₂₃ ∪ E₂` (size `2d`);
- Head 2: `(0, X·g₁₃, g₁₃)` with core `B₁₃ ∪ B₂₃ ∪ E₃` (size `2d`);
- Head 3: `(g₁₂, λ·X·g₁₂, λ·g₁₂)` with core `B₁₂ ∪ B_rem` (size `2d`).

Because `g₁₃ - λ·g₁₂ = λ(1 - r₀)` is a nonzero constant, every fresh denominator is
automatically nonzero anywhere outside `B₁₂ ∪ B₁₃ ∪ B₂₃`, and every event satisfies
`key_1 = -x`, making `key` injective across all `8d + 10 = 2n + 2` fresh events.

## Main unconditional results (100% kernel-checked)

1. `quarter_pivot_failure_of_domain`: Any domain `dom : Fin (4(d+1)) ↪ F` containing the
   three cosets achieves `(2n + 2) / |F| ≤ epsMCA (RS(dom, d+1)^⋈ width) ((2d+3)/(4(d+1)))`.
2. `universal_quarter_pivot_failure`: Whenever `Choose(8d+10, 2) ≤ |F|` and such
   `ω, u₀, v₀` exist, there exists `dom : Fin (4(d+1)) ↪ F` realizing `(2n + 2) / |F|`.
3. `production_quarter_pivot_domain_independent_barrier`: At production scale
   `n = 2^30`, `k = 2^28`, `e = 536,870,913`, over the Lucas-certified 159-bit prime
   `Q = 730750818869487914369817427303088068110372044801` (matching `Q / 2^128 = 2^31 = 2n`
   and `2^30 ∣ Q - 1`), there exists `dom : Fin (2^30) ↪ ZMod Q` where for every positive
   interleaving width, `1/2^128 < epsMCA` at `536,870,913 / 2^30` and `mcaDeltaStar` lies
   strictly below the finite-length Johnson radius. Thus any safety proof at the second-prime
   quarter-rate Johnson pivot `536,870,913` must use arithmetic structure of the smooth
   evaluation subgroup `μ_{2^30}` rather than domain-independent counting.
4. `smooth_mu16_f1009_quarter_pivot_failure`: At `d = 3, n = 16, k = 4, e = 9` in
   `ZMod 1009`, the construction lands directly on the literal smooth subgroup `μ₁₆` with
   `34 / 1009 ≤ epsMCA` (`34 > 32 = 2n`) strictly below the finite Johnson radius.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open Finset Polynomial Code
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open ProximityPrize.RankJohnsonComparison
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.QuarterPivotDomainIndependentBarrier

/-! ## Part 1: Combinatorial partition and universal `2n + 2` construction -/

/-- The 7-part partition of a quarter-rate evaluation domain of length `4 * (d + 1)`. -/
inductive Site (d : ℕ) where
  | b12 (j : Fin (d - 1))
  | b13 (j : Fin (d - 1))
  | b23 (j : Fin (d - 1))
  | e1 (j : Fin 2)
  | e2 (j : Fin 2)
  | e3 (j : Fin 2)
  | brem (j : Fin (d + 1))
  deriving DecidableEq

/-- Sum-type equivalence for `Site d`. -/
def siteSumEquiv (d : ℕ) :
    Site d ≃
      Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 ⊕ Fin 2 ⊕ Fin 2 ⊕ Fin (d + 1) where
  toFun
    | .b12 j => .inl j
    | .b13 j => .inr (.inl j)
    | .b23 j => .inr (.inr (.inl j))
    | .e1 j => .inr (.inr (.inr (.inl j)))
    | .e2 j => .inr (.inr (.inr (.inr (.inl j))))
    | .e3 j => .inr (.inr (.inr (.inr (.inr (.inl j)))))
    | .brem j => .inr (.inr (.inr (.inr (.inr (.inr j)))))
  invFun
    | .inl j => .b12 j
    | .inr (.inl j) => .b13 j
    | .inr (.inr (.inl j)) => .b23 j
    | .inr (.inr (.inr (.inl j))) => .e1 j
    | .inr (.inr (.inr (.inr (.inl j)))) => .e2 j
    | .inr (.inr (.inr (.inr (.inr (.inl j))))) => .e3 j
    | .inr (.inr (.inr (.inr (.inr (.inr j))))) => .brem j
  left_inv s := by cases s <;> rfl
  right_inv x := by
    rcases x with j | j | j | j | j | j | j <;> rfl

instance instFintypeSite (d : ℕ) : Fintype (Site d) :=
  Fintype.ofEquiv _ (siteSumEquiv d).symm

theorem card_site (d : ℕ) (hd : 1 ≤ d) : Fintype.card (Site d) = 4 * (d + 1) := by
  rw [Fintype.card_congr (siteSumEquiv d)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Fresh-event multiplicity at each site of the 7-part partition. -/
abbrev mult (d : ℕ) : Site d → ℕ
  | .b12 _ => 1
  | .b13 _ => 2
  | .b23 _ => 2
  | .e1 _ => 2
  | .e2 _ => 2
  | .e3 _ => 2
  | .brem _ => 3

/-- Index type of the `8d + 10 = 2n + 2` fresh MCA events. -/
abbrev Event (d : ℕ) := (s : Site d) × Fin (mult d s)

theorem card_event (d : ℕ) (hd : 1 ≤ d) : Fintype.card (Event d) = 8 * d + 10 := by
  rw [Fintype.card_sigma]
  have hsum :
      (∑ s : Site d, Fintype.card (Fin (mult d s))) =
      ∑ x : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 ⊕ Fin 2 ⊕ Fin 2 ⊕ Fin (d + 1),
        mult d ((siteSumEquiv d).symm x) := by
    refine Fintype.sum_equiv (siteSumEquiv d) _ _ ?_
    intro s
    rw [Fintype.card_fin, (siteSumEquiv d).symm_apply_apply s]
  rw [hsum]
  simp only [Fintype.sum_sum_type, siteSumEquiv, Equiv.coe_fn_symm_mk, mult,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- Which of the 4 heads owns the received word at a given site. -/
private def owner (d : ℕ) : Site d → Fin 4
  | .b12 _ => 0
  | .b13 _ => 0
  | .b23 _ => 1
  | .e1 _ => 0
  | .e2 _ => 1
  | .e3 _ => 2
  | .brem _ => 3

/-- Membership indicator of each head's size-`2d` core. -/
private def inCore (d : ℕ) (h : Fin 4) (s : Site d) : Bool :=
  match h.val, s with
  | 0, .b12 _ => true
  | 0, .b13 _ => true
  | 0, .e1 _ => true
  | 1, .b12 _ => true
  | 1, .b23 _ => true
  | 1, .e2 _ => true
  | 2, .b13 _ => true
  | 2, .b23 _ => true
  | 2, .e3 _ => true
  | 3, .b12 _ => true
  | 3, .brem _ => true
  | _, _ => false

/-- The fresh head assigned to each event. -/
private def eventHead (d : ℕ) : Event d → Fin 4
  | ⟨.b12 _, _⟩ => 2
  | ⟨.b13 _, t⟩ => if t.val = 0 then 1 else 3
  | ⟨.b23 _, t⟩ => if t.val = 0 then 0 else 3
  | ⟨.e1 _, t⟩ => if t.val = 0 then 1 else 3
  | ⟨.e2 _, t⟩ => if t.val = 0 then 0 else 3
  | ⟨.e3 _, t⟩ => if t.val = 0 then 0 else 3
  | ⟨.brem _, t⟩ => if t.val = 0 then 0 else if t.val = 1 then 1 else 2

private theorem card_core_site (d : ℕ) (hd : 1 ≤ d) (h : Fin 4) :
    (univ.filter (fun s : Site d => inCore d h s = true)).card = 2 * d := by
  rw [Finset.card_filter]
  have hsum :
      (∑ s : Site d, if inCore d h s = true then 1 else 0) =
      ∑ x : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 ⊕ Fin 2 ⊕ Fin 2 ⊕ Fin (d + 1),
        if inCore d h ((siteSumEquiv d).symm x) = true then 1 else 0 := by
    refine Fintype.sum_equiv (siteSumEquiv d) _ _ ?_
    intro s
    rw [(siteSumEquiv d).symm_apply_apply s]
  rw [hsum]
  fin_cases h <;>
    simp [Fintype.sum_sum_type, siteSumEquiv, inCore] <;>
    omega

/-- In a field, if `ω` has exact order `m > 0` and `c ≠ 0`, then the coset `c · ⟨ω⟩` is
precisely the root set of `X^m - c^m`. -/
private theorem mem_coset_iff_pow_eq {F : Type} [Field F] [DecidableEq F]
    {m : ℕ} (hm : 0 < m) {ω c : F} (hω : orderOf ω = m) (hc : c ≠ 0) (x : F) :
    (∃ j : Fin m, c * ω ^ j.val = x) ↔ x ^ m = c ^ m := by
  have hωm : ω ^ m = 1 := by rw [← hω, pow_orderOf_eq_one]
  constructor
  · rintro ⟨j, rfl⟩
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, hωm, one_pow, mul_one]
  · intro hxm
    let f : Fin m → F := fun j => c * ω ^ j.val
    have hfinj : Function.Injective f := by
      intro i j hij
      have hpow : ω ^ i.val = ω ^ j.val := mul_left_cancel₀ hc hij
      have hi : i.val ∈ Set.Iio (orderOf ω) := by rw [hω]; exact i.isLt
      have hj : j.val ∈ Set.Iio (orderOf ω) := by rw [hω]; exact j.isLt
      exact Fin.ext (pow_injOn_Iio_orderOf hi hj hpow)
    let S : Finset F := univ.image f
    have hScard : S.card = m := by
      rw [card_image_of_injective _ hfinj, card_univ, Fintype.card_fin]
    let P : F[X] := (Polynomial.X : F[X]) ^ m - C (c ^ m)
    have hlt : (C (c ^ m) : F[X]).degree < ((Polynomial.X : F[X]) ^ m).degree := by
      calc (C (c ^ m) : F[X]).degree ≤ 0 := degree_C_le
        _ < (m : WithBot ℕ) := by exact_mod_cast hm
        _ = ((Polynomial.X : F[X]) ^ m).degree := (degree_X_pow m).symm
    have hPdeg : P.degree = (m : WithBot ℕ) := by
      dsimp [P]
      rw [degree_sub_eq_left_of_degree_lt hlt, degree_X_pow]
    have hPne : P ≠ 0 := by
      intro h0
      rw [h0, degree_zero] at hPdeg
      exact absurd hPdeg (by simp)
    have hPndeg : P.natDegree = m := natDegree_eq_of_degree_eq_some hPdeg
    have hsub : S ⊆ P.roots.toFinset := by
      intro y hy
      rcases mem_image.mp hy with ⟨j, _, rfl⟩
      rw [Multiset.mem_toFinset, mem_roots hPne, IsRoot]
      simp only [P, eval_sub, eval_pow, eval_X, eval_C, f]
      rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, hωm, one_pow, mul_one, sub_self]
    have hrcard : P.roots.toFinset.card ≤ S.card := by
      calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := card_roots' P
        _ = S.card := by rw [hPndeg, hScard]
    have heq : S = P.roots.toFinset := Finset.eq_of_subset_of_card_le hsub hrcard
    have hxmem : x ∈ S := by
      rw [heq, Multiset.mem_toFinset, mem_roots hPne, IsRoot]
      simp [P, hxm]
    rcases mem_image.mp hxmem with ⟨j, _, hj⟩
    exact ⟨j, hj⟩

/-- **Core quarter-rate pivot failure on any domain containing the three cosets.**
Given `d ≥ 3`, a primitive `(d - 1)`-th root `ω`, nonzero coset representatives `u₀, v₀`
with `1, u₀^(d-1), v₀^(d-1)` pairwise distinct, and ANY evaluation domain
`dom : Fin (4*(d+1)) ↪ F` partitioned by `e : Fin (4*(d+1)) ≃ Site d` whose `b12, b13, b23`
parts coincide with `⟨ω⟩, u₀⟨ω⟩, v₀⟨ω⟩`, the interleaved Reed–Solomon code of dimension
`d + 1` has at least `8d + 10 = 2n + 2` bad scalars at error count `2d + 3 = n/2 + 1`. -/
theorem quarter_pivot_failure_of_domain
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (hd : 3 ≤ d)
    (ω u₀ v₀ : F) (hω : orderOf ω = d - 1) (hu₀ : u₀ ≠ 0) (hv₀ : v₀ ≠ 0)
    (hr1 : u₀ ^ (d - 1) ≠ 1) (hs1 : v₀ ^ (d - 1) ≠ 1) (hrs : u₀ ^ (d - 1) ≠ v₀ ^ (d - 1))
    (dom : Fin (4 * (d + 1)) ↪ F) (e : Fin (4 * (d + 1)) ≃ Site d)
    (hb12 : ∀ j : Fin (d - 1), dom (e.symm (.b12 j)) = ω ^ j.val)
    (hb13 : ∀ j : Fin (d - 1), dom (e.symm (.b13 j)) = u₀ * ω ^ j.val)
    (hb23 : ∀ j : Fin (d - 1), dom (e.symm (.b23 j)) = v₀ * ω ^ j.val)
    (hfield : (8 * d + 10).choose 2 ≤ Fintype.card F)
    (width : ℕ) [NeZero width] :
    ((8 * d + 10 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F)
        ((ReedSolomon.code dom (d + 1) : Set (Fin (4 * (d + 1)) → F)) ^⋈ (Fin width))
        (((2 * d + 3 : ℕ) : ℝ≥0) / ((4 * (d + 1) : ℕ) : ℝ≥0)) := by
  have hm_pos : 0 < d - 1 := by omega
  have hd1 : 1 ≤ d := by omega
  let r₀ : F := u₀ ^ (d - 1)
  let s₀ : F := v₀ ^ (d - 1)
  have hsr : s₀ - r₀ ≠ 0 := sub_ne_zero.mpr hrs.symm
  have hs1' : s₀ - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hr1' : r₀ - 1 ≠ 0 := sub_ne_zero.mpr hr1
  let lam : F := (s₀ - 1) / (s₀ - r₀)
  have hlam0 : lam ≠ 0 := div_ne_zero hs1' hsr
  have hlam_sub : lam - 1 = (r₀ - 1) / (s₀ - r₀) := by
    dsimp [lam]; field_simp [hsr]; ring
  have hlam1 : lam ≠ 1 := by
    intro h
    have h0 : lam - 1 = 0 := sub_eq_zero.mpr h
    rw [hlam_sub] at h0
    exact div_ne_zero hr1' hsr h0
  have hlam1' : lam - 1 ≠ 0 := sub_ne_zero.mpr hlam1
  have h1r : 1 - r₀ ≠ 0 := sub_ne_zero.mpr hr1.symm
  let g12 : F[X] := (Polynomial.X : F[X]) ^ (d - 1) - 1
  let g13 : F[X] := C lam * ((Polynomial.X : F[X]) ^ (d - 1) - C r₀)
  have hg12_eval (x : F) : g12.eval x = x ^ (d - 1) - 1 := by simp [g12]
  have hg13_eval (x : F) : g13.eval x = lam * (x ^ (d - 1) - r₀) := by simp [g13]
  have hg13_sub_g12 (x : F) : g13.eval x - g12.eval x = (lam - 1) * (x ^ (d - 1) - s₀) := by
    rw [hg13_eval, hg12_eval, hlam_sub]
    dsimp [lam]
    field_simp [hsr]
    ring
  have hg13_sub_lam_g12 (x : F) : g13.eval x - lam * g12.eval x = lam * (1 - r₀) := by
    rw [hg13_eval, hg12_eval]; ring
  -- Zero characterizations on `dom`
  have hb12_iff (x : Fin (4 * (d + 1))) : g12.eval (dom x) = 0 ↔ ∃ j, e x = .b12 j := by
    rw [hg12_eval, sub_eq_zero]
    have h1 : (1 : F) ^ (d - 1) = 1 := one_pow _
    rw [← h1, ← mem_coset_iff_pow_eq hm_pos hω one_ne_zero]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hdom : dom (e.symm (.b12 j)) = dom x := by
        rw [hb12 j]; simpa using hj
      have hx : e.symm (.b12 j) = x := dom.injective hdom
      rw [← hx, e.apply_symm_apply]
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hx : x = e.symm (.b12 j) := by rw [← hj, e.symm_apply_apply]
      rw [hx, hb12 j, one_mul]
  have hb13_iff (x : Fin (4 * (d + 1))) : g13.eval (dom x) = 0 ↔ ∃ j, e x = .b13 j := by
    rw [hg13_eval, mul_eq_zero, or_iff_right hlam0, sub_eq_zero]
    rw [← mem_coset_iff_pow_eq hm_pos hω hu₀]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hdom : dom (e.symm (.b13 j)) = dom x := by rw [hb13 j]; exact hj
      have hx : e.symm (.b13 j) = x := dom.injective hdom
      rw [← hx, e.apply_symm_apply]
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hx : x = e.symm (.b13 j) := by rw [← hj, e.symm_apply_apply]
      rw [hx, hb13 j]
  have hb23_iff (x : Fin (4 * (d + 1))) :
      g13.eval (dom x) = g12.eval (dom x) ↔ ∃ j, e x = .b23 j := by
    rw [← sub_eq_zero, hg13_sub_g12, mul_eq_zero, or_iff_right hlam1', sub_eq_zero]
    rw [← mem_coset_iff_pow_eq hm_pos hω hv₀]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hdom : dom (e.symm (.b23 j)) = dom x := by rw [hb23 j]; exact hj
      have hx : e.symm (.b23 j) = x := dom.injective hdom
      rw [← hx, e.apply_symm_apply]
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hx : x = e.symm (.b23 j) := by rw [← hj, e.symm_apply_apply]
      rw [hx, hb23 j]
  -- Head polynomials `(headP, headQ, headR)`
  let headP : Fin 4 → F[X] := fun h => match h.val with | 3 => g12 | _ => 0
  let headR : Fin 4 → F[X] := fun h =>
    match h.val with | 0 => 0 | 1 => g12 | 2 => g13 | _ => C lam * g12
  let headQ : Fin 4 → F[X] := fun h => Polynomial.X * headR h
  have headP0 : headP 0 = 0 := rfl
  have headP1 : headP 1 = 0 := rfl
  have headP2 : headP 2 = 0 := rfl
  have headP3 : headP 3 = g12 := rfl
  have headR0 : headR 0 = 0 := rfl
  have headR1 : headR 1 = g12 := rfl
  have headR2 : headR 2 = g13 := rfl
  have headR3 : headR 3 = C lam * g12 := rfl
  have hQ_eq (h : Fin 4) (y : F) : (headQ h).eval y = y * (headR h).eval y := by
    simp [headQ]
  -- Degree bounds `< d + 1`
  have deg_C_mul_lt {n : ℕ} (c : F) (f : F[X]) (hf : f.degree < (n : WithBot ℕ)) :
      (C c * f).degree < (n : WithBot ℕ) := by
    by_cases hz : c = 0
    · simp [hz]
    · simpa [degree_C_mul hz] using hf
  have hg12_deg : g12.degree < (d : WithBot ℕ) := by
    have h1 : g12.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
      dsimp [g12]
      refine (degree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [degree_X_pow]
      · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le (d - 1))
    exact h1.trans_lt (by exact_mod_cast (by omega : d - 1 < d))
  have hg13_deg : g13.degree < (d : WithBot ℕ) := by
    have h1 : ((Polynomial.X : F[X]) ^ (d - 1) - C r₀).degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
      refine (degree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [degree_X_pow]
      · exact degree_C_le.trans (by exact_mod_cast Nat.zero_le (d - 1))
    exact deg_C_mul_lt lam _ (h1.trans_lt (by exact_mod_cast (by omega : d - 1 < d)))
  have hlt_succ : (d : WithBot ℕ) < ((d + 1 : ℕ) : WithBot ℕ) := by
    exact_mod_cast Nat.lt_succ_self d
  have hX_mul_deg {f : F[X]} (hf : f.degree < (d : WithBot ℕ)) :
      (Polynomial.X * f).degree < ((d + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_mul_le Polynomial.X f).trans_lt ?_
    rw [degree_X]
    have h1 : (1 : WithBot ℕ) + f.degree < (1 : WithBot ℕ) + (d : WithBot ℕ) :=
      WithBot.add_lt_add_left (by simp) hf
    convert h1 using 1
    exact_mod_cast Nat.add_comm d 1
  have hR_deg_d (h : Fin 4) : (headR h).degree < (d : WithBot ℕ) := by
    fin_cases h
    · simp [headR]
    · exact hg12_deg
    · exact hg13_deg
    · exact deg_C_mul_lt lam g12 hg12_deg
  have hP_deg (h : Fin 4) : (headP h).degree < ((d + 1 : ℕ) : WithBot ℕ) := by
    fin_cases h
    · simp [headP]
    · simp [headP]
    · simp [headP]
    · exact hg12_deg.trans hlt_succ
  have hR_deg (h : Fin 4) : (headR h).degree < ((d + 1 : ℕ) : WithBot ℕ) :=
    (hR_deg_d h).trans hlt_succ
  have hQ_deg (h : Fin 4) : (headQ h).degree < ((d + 1 : ℕ) : WithBot ℕ) :=
    hX_mul_deg (hR_deg_d h)
  -- Received words `(u, v, w)`
  let u : Fin (4 * (d + 1)) → F := fun x => (headP (owner d (e x))).eval (dom x)
  let v : Fin (4 * (d + 1)) → F := fun x => (headQ (owner d (e x))).eval (dom x)
  let w : Fin (4 * (d + 1)) → F := fun x => (headR (owner d (e x))).eval (dom x)
  have hv_eq (x : Fin (4 * (d + 1))) : v x = dom x * w x := hQ_eq (owner d (e x)) (dom x)
  -- Head cores
  let headCore : Fin 4 → Finset (Fin (4 * (d + 1))) :=
    fun h => univ.filter (fun x => inCore d h (e x) = true)
  have hcore_card (h : Fin 4) : (headCore h).card = 2 * d := by
    have hbij : (headCore h).card = (univ.filter (fun s : Site d => inCore d h s = true)).card := by
      refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
      · intro x hx
        simp only [headCore, mem_filter, mem_univ, true_and] at hx ⊢
        exact hx
      · intro x₁ _ x₂ _ h12; exact e.injective h12
      · intro s hs
        refine ⟨e.symm s, ?_, e.apply_symm_apply s⟩
        simp only [headCore, mem_filter, mem_univ, true_and, e.apply_symm_apply] at hs ⊢
        exact hs
    rw [hbij, card_core_site d hd1 h]
  have hcore_agree (h : Fin 4) (x : Fin (4 * (d + 1))) (hx : x ∈ headCore h) :
      (headP h).eval (dom x) = u x ∧ (headQ h).eval (dom x) = v x ∧
        (headR h).eval (dom x) = w x := by
    simp only [headCore, mem_filter, mem_univ, true_and] at hx
    fin_cases h <;> cases hs : e x <;> simp [inCore, hs] at hx
    · -- h = 0, b12
      simp [u, v, w, owner, hs]
    · -- h = 0, b13
      simp [u, v, w, owner, hs]
    · -- h = 0, e1
      simp [u, v, w, owner, hs]
    · -- h = 1, b12
      have hg : g12.eval (dom x) = 0 := (hb12_iff x).mpr ⟨_, hs⟩
      simp [u, v, w, owner, hs, headP, headQ, headR, hg]
    · -- h = 1, b23
      simp [u, v, w, owner, hs]
    · -- h = 1, e2
      simp [u, v, w, owner, hs]
    · -- h = 2, b13
      have hg : g13.eval (dom x) = 0 := (hb13_iff x).mpr ⟨_, hs⟩
      simp [u, v, w, owner, hs, headP, headQ, headR, hg]
    · -- h = 2, b23
      have hg : g13.eval (dom x) = g12.eval (dom x) := (hb23_iff x).mpr ⟨_, hs⟩
      simp [u, v, w, owner, hs, headP, headQ, headR, hg]
    · -- h = 2, e3
      simp [u, v, w, owner, hs]
    · -- h = 3, b12
      have hg : g12.eval (dom x) = 0 := (hb12_iff x).mpr ⟨_, hs⟩
      simp [u, v, w, owner, hs, headP, headQ, headR, hg]
    · -- h = 3, brem
      simp [u, v, w, owner, hs]
  -- Event indexing
  let site : Event d → Fin (4 * (d + 1)) := fun ev => e.symm ev.1
  let core : Event d → Finset (Fin (4 * (d + 1))) := fun ev => headCore (eventHead d ev)
  let p : Event d → F[X] := fun ev => headP (eventHead d ev)
  let q : Event d → F[X] := fun ev => headQ (eventHead d ev)
  let r : Event d → F[X] := fun ev => headR (eventHead d ev)
  -- Non-vanishing of `r_ev - w` at every fresh event
  have hmis (ev : Event d) : (r ev).eval (dom (site ev)) ≠ w (site ev) := by
    rcases ev with ⟨s, t⟩
    have hes : e (site ⟨s, t⟩) = s := e.apply_symm_apply s
    have hnot12 (hns : ∀ j, s ≠ .b12 j) : g12.eval (dom (site ⟨s, t⟩)) ≠ 0 := by
      intro h0
      rcases (hb12_iff _).mp h0 with ⟨j, hj⟩
      rw [hes] at hj
      exact hns j hj
    have hnot13 (hns : ∀ j, s ≠ .b13 j) : g13.eval (dom (site ⟨s, t⟩)) ≠ 0 := by
      intro h0
      rcases (hb13_iff _).mp h0 with ⟨j, hj⟩
      rw [hes] at hj
      exact hns j hj
    have hnot23 (hns : ∀ j, s ≠ .b23 j) :
        g13.eval (dom (site ⟨s, t⟩)) ≠ g12.eval (dom (site ⟨s, t⟩)) := by
      intro h0
      rcases (hb23_iff _).mp h0 with ⟨j, hj⟩
      rw [hes] at hj
      exact hns j hj
    cases s with
    | b12 j =>
      rcases t with ⟨t, ht⟩; interval_cases t
      simp only [r, w, eventHead, owner, hes, headR2, headR0, eval_zero]
      exact hnot13 (by intro _ h; cases h)
    | b13 j =>
      rcases t with ⟨t, ht⟩; interval_cases t
      · simp only [r, w, eventHead, owner, hes, ite_true, headR1, headR0, eval_zero]
        exact hnot12 (by intro _ h; cases h)
      · simp only [r, w, eventHead, owner, hes, one_ne_zero, ite_false, headR3, headR0,
          eval_mul, eval_C, eval_zero]
        exact mul_ne_zero hlam0 (hnot12 (by intro _ h; cases h))
    | b23 j =>
      rcases t with ⟨t, ht⟩; interval_cases t
      · simp only [r, w, eventHead, owner, hes, ite_true, headR0, headR1, eval_zero]
        exact (hnot12 (by intro _ h; cases h)).symm
      · simp only [r, w, eventHead, owner, hes, one_ne_zero, ite_false, headR3, headR1,
          eval_mul, eval_C]
        intro hEq
        have h0 : (lam - 1) * g12.eval (dom (site ⟨.b23 j, ⟨1, ht⟩⟩)) = 0 := by
          linear_combination hEq
        exact mul_ne_zero hlam1' (hnot12 (by intro _ h; cases h)) h0
    | e1 j =>
      rcases t with ⟨t, ht⟩; interval_cases t
      · simp only [r, w, eventHead, owner, hes, ite_true, headR1, headR0, eval_zero]
        exact hnot12 (by intro _ h; cases h)
      · simp only [r, w, eventHead, owner, hes, one_ne_zero, ite_false, headR3, headR0,
          eval_mul, eval_C, eval_zero]
        exact mul_ne_zero hlam0 (hnot12 (by intro _ h; cases h))
    | e2 j =>
      rcases t with ⟨t, ht⟩; interval_cases t
      · simp only [r, w, eventHead, owner, hes, ite_true, headR0, headR1, eval_zero]
        exact (hnot12 (by intro _ h; cases h)).symm
      · simp only [r, w, eventHead, owner, hes, one_ne_zero, ite_false, headR3, headR1,
          eval_mul, eval_C]
        intro hEq
        have h0 : (lam - 1) * g12.eval (dom (site ⟨.e2 j, ⟨1, ht⟩⟩)) = 0 := by
          linear_combination hEq
        exact mul_ne_zero hlam1' (hnot12 (by intro _ h; cases h)) h0
    | e3 j =>
      rcases t with ⟨t, ht⟩; interval_cases t
      · simp only [r, w, eventHead, owner, hes, ite_true, headR0, headR2, eval_zero]
        exact (hnot13 (by intro _ h; cases h)).symm
      · simp only [r, w, eventHead, owner, hes, one_ne_zero, ite_false, headR3, headR2,
          eval_mul, eval_C]
        intro hEq
        have h0 : g13.eval (dom (site ⟨.e3 j, ⟨1, ht⟩⟩)) - lam * g12.eval (dom (site ⟨.e3 j, ⟨1, ht⟩⟩)) = 0 :=
          sub_eq_zero.mpr hEq.symm
        rw [hg13_sub_lam_g12] at h0
        exact mul_ne_zero hlam0 h1r h0
    | brem j =>
      rcases t with ⟨t, ht⟩; interval_cases t
      · simp only [r, w, eventHead, owner, hes, ite_true, headR0, headR3, eval_zero, eval_mul,
          eval_C]
        exact (mul_ne_zero hlam0 (hnot12 (by intro _ h; cases h))).symm
      · simp only [r, w, eventHead, owner, hes, one_ne_zero, ite_false, ite_true, headR1, headR3,
          eval_mul, eval_C]
        intro hEq
        have h0 : (lam - 1) * g12.eval (dom (site ⟨.brem j, ⟨1, ht⟩⟩)) = 0 := by
          linear_combination -hEq
        exact mul_ne_zero hlam1' (hnot12 (by intro _ h; cases h)) h0
      · simp only [r, w, eventHead, owner, hes,
          show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false, headR2, headR3,
          eval_mul, eval_C]
        intro hEq
        have h0 : g13.eval (dom (site ⟨.brem j, ⟨2, ht⟩⟩)) - lam * g12.eval (dom (site ⟨.brem j, ⟨2, ht⟩⟩)) = 0 :=
          sub_eq_zero.mpr hEq
        rw [hg13_sub_lam_g12] at h0
        exact mul_ne_zero hlam0 h1r h0
  -- Key functional: `key ev 1 = -dom (site ev)` uniformly
  let key : Event d → Fin 2 → F := fun ev =>
    ![(u (site ev) - (p ev).eval (dom (site ev))) / ((r ev).eval (dom (site ev)) - w (site ev)),
      -dom (site ev)]
  have hkey (ev : Event d) :
      key ev 0 * ((r ev).eval (dom (site ev)) - w (site ev)) =
        u (site ev) - (p ev).eval (dom (site ev)) ∧
      key ev 1 * ((r ev).eval (dom (site ev)) - w (site ev)) =
        v (site ev) - (q ev).eval (dom (site ev)) := by
    constructor
    · exact div_mul_cancel₀ _ (sub_ne_zero.mpr (hmis ev))
    · change -dom (site ev) * ((headR (eventHead d ev)).eval (dom (site ev)) - w (site ev)) =
        v (site ev) - (headQ (eventHead d ev)).eval (dom (site ev))
      rw [hv_eq (site ev), hQ_eq (eventHead d ev) (dom (site ev))]
      ring
  -- Key injectivity: coordinate 1 pins `site`, coordinate 0 separates heads at that site
  have hinj : Function.Injective key := by
    rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ hEq
    have h1 : -dom (e.symm s₁) = -dom (e.symm s₂) := congrFun hEq 1
    have hs : s₁ = s₂ := e.symm.injective (dom.injective (neg_injective h1))
    subst hs
    congr 1
    have h0 : key ⟨s₁, t₁⟩ 0 = key ⟨s₁, t₂⟩ 0 := congrFun hEq 0
    have hes : e (e.symm s₁) = s₁ := e.apply_symm_apply s₁
    have hnot12 (hns : ∀ j, s₁ ≠ .b12 j) : g12.eval (dom (e.symm s₁)) ≠ 0 := by
      intro hz
      rcases (hb12_iff _).mp hz with ⟨j, hj⟩
      rw [hes] at hj
      exact hns j hj
    have hnot13 (hns : ∀ j, s₁ ≠ .b13 j) : g13.eval (dom (e.symm s₁)) ≠ 0 := by
      intro hz
      rcases (hb13_iff _).mp hz with ⟨j, hj⟩
      rw [hes] at hj
      exact hns j hj
    have hnot23 (hns : ∀ j, s₁ ≠ .b23 j) :
        g13.eval (dom (e.symm s₁)) ≠ g12.eval (dom (e.symm s₁)) := by
      intro hz
      rcases (hb23_iff _).mp hz with ⟨j, hj⟩
      rw [hes] at hj
      exact hns j hj
    -- Helper for all five `mult = 2` cases: `key 0 = 0` at `t = 0` and `≠ 0` at `t = 1`
    have hsep2 (hm2 : mult d s₁ = 2)
        (hz0 : key ⟨s₁, ⟨0, by omega⟩⟩ 0 = 0)
        (hnz1 : key ⟨s₁, ⟨1, by omega⟩⟩ 0 ≠ 0) : t₁ = t₂ := by
      rcases t₁ with ⟨a₁, ha₁⟩
      rcases t₂ with ⟨a₂, ha₂⟩
      have ha₁' : a₁ < 2 := hm2 ▸ ha₁
      have ha₂' : a₂ < 2 := hm2 ▸ ha₂
      interval_cases a₁ <;> interval_cases a₂
      · rfl
      · exfalso; exact hnz1 (h0.symm.trans hz0)
      · exfalso; exact hnz1 (h0.trans hz0)
      · rfl
    cases s₁ with
    | b12 j => exact Subsingleton.elim t₁ t₂
    | b13 j =>
      refine hsep2 rfl (by simp [key, u, p, site, eventHead, owner, headP]) ?_
      refine div_ne_zero ?_ (sub_ne_zero.mpr (hmis ⟨.b13 j, 1⟩))
      simp only [u, p, site, eventHead, owner, hes, one_ne_zero, ite_false, headP0, headP3,
        eval_zero, zero_sub, neg_ne_zero]
      exact hnot12 (by intro _ h; cases h)
    | b23 j =>
      refine hsep2 rfl (by simp [key, u, p, site, eventHead, owner, headP]) ?_
      refine div_ne_zero ?_ (sub_ne_zero.mpr (hmis ⟨.b23 j, 1⟩))
      simp only [u, p, site, eventHead, owner, hes, one_ne_zero, ite_false, headP1, headP3,
        eval_zero, zero_sub, neg_ne_zero]
      exact hnot12 (by intro _ h; cases h)
    | e1 j =>
      refine hsep2 rfl (by simp [key, u, p, site, eventHead, owner, headP]) ?_
      refine div_ne_zero ?_ (sub_ne_zero.mpr (hmis ⟨.e1 j, 1⟩))
      simp only [u, p, site, eventHead, owner, hes, one_ne_zero, ite_false, headP0, headP3,
        eval_zero, zero_sub, neg_ne_zero]
      exact hnot12 (by intro _ h; cases h)
    | e2 j =>
      refine hsep2 rfl (by simp [key, u, p, site, eventHead, owner, headP]) ?_
      refine div_ne_zero ?_ (sub_ne_zero.mpr (hmis ⟨.e2 j, 1⟩))
      simp only [u, p, site, eventHead, owner, hes, one_ne_zero, ite_false, headP1, headP3,
        eval_zero, zero_sub, neg_ne_zero]
      exact hnot12 (by intro _ h; cases h)
    | e3 j =>
      refine hsep2 rfl (by simp [key, u, p, site, eventHead, owner, headP]) ?_
      refine div_ne_zero ?_ (sub_ne_zero.mpr (hmis ⟨.e3 j, 1⟩))
      simp only [u, p, site, eventHead, owner, hes, one_ne_zero, ite_false, headP2, headP3,
        eval_zero, zero_sub, neg_ne_zero]
      exact hnot12 (by intro _ h; cases h)
    | brem j =>
      -- All three fresh heads have `p = 0`, `u = g12 ≠ 0`, so equal keys force equal `r_h`
      have hden1 : (r ⟨.brem j, t₁⟩).eval (dom (e.symm (.brem j))) - w (e.symm (.brem j)) ≠ 0 :=
        sub_ne_zero.mpr (hmis ⟨.brem j, t₁⟩)
      have hden2 : (r ⟨.brem j, t₂⟩).eval (dom (e.symm (.brem j))) - w (e.symm (.brem j)) ≠ 0 :=
        sub_ne_zero.mpr (hmis ⟨.brem j, t₂⟩)
      have hg12ne : g12.eval (dom (e.symm (.brem j))) ≠ 0 := hnot12 (by intro _ h; cases h)
      have hp0 (t : Fin 3) : (p ⟨.brem j, t⟩).eval (dom (e.symm (.brem j))) = 0 := by
        rcases t with ⟨a, ha⟩; interval_cases a <;> simp [p, eventHead, headP]
      have hu_brem : u (e.symm (.brem j)) = g12.eval (dom (e.symm (.brem j))) := by
        simp [u, owner, hes, headP]
      have hr_eq :
          (r ⟨.brem j, t₁⟩).eval (dom (e.symm (.brem j))) =
          (r ⟨.brem j, t₂⟩).eval (dom (e.symm (.brem j))) := by
        simp only [key, Matrix.cons_val_zero, site, hu_brem, hp0, sub_zero] at h0
        have hcross :
            g12.eval (dom (e.symm (.brem j))) *
              ((r ⟨.brem j, t₂⟩).eval (dom (e.symm (.brem j))) - w (e.symm (.brem j))) =
            g12.eval (dom (e.symm (.brem j))) *
              ((r ⟨.brem j, t₁⟩).eval (dom (e.symm (.brem j))) - w (e.symm (.brem j))) :=
          (div_eq_div_iff hden1 hden2).mp h0
        have hsub := mul_left_cancel₀ hg12ne hcross
        exact sub_left_inj.mp hsub.symm
      rcases t₁ with ⟨a₁, ha₁⟩
      rcases t₂ with ⟨a₂, ha₂⟩
      interval_cases a₁ <;> interval_cases a₂
      · rfl
      · exfalso
        simp only [r, eventHead, ite_true, one_ne_zero, ite_false, headR0, headR1,
          eval_zero] at hr_eq
        exact hg12ne hr_eq.symm
      · exfalso
        simp only [r, eventHead, ite_true,
          show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false,
          headR0, headR2, eval_zero] at hr_eq
        exact hnot13 (by intro _ h; cases h) hr_eq.symm
      · exfalso
        simp only [r, eventHead, ite_true, one_ne_zero, ite_false, headR0, headR1,
          eval_zero] at hr_eq
        exact hg12ne hr_eq
      · rfl
      · exfalso
        simp only [r, eventHead, one_ne_zero, ite_true,
          show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false,
          headR1, headR2] at hr_eq
        exact hnot23 (by intro _ h; cases h) hr_eq.symm
      · exfalso
        simp only [r, eventHead, ite_true,
          show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false,
          headR0, headR2, eval_zero] at hr_eq
        exact hnot13 (by intro _ h; cases h) hr_eq
      · exfalso
        simp only [r, eventHead, one_ne_zero, ite_true,
          show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false,
          headR1, headR2] at hr_eq
        exact hnot23 (by intro _ h; cases h) hr_eq
      · rfl
  -- Apply `LinearPencilFreshLabels.mass_of_distinct_fresh_labels`
  rw [epsMCA_interleaved_eq]
  have hm := LinearPencilFreshLabels.mass_of_distinct_fresh_labels
    dom (d + 1) (((2 * d + 3 : ℕ) : ℝ≥0) / ((4 * (d + 1) : ℕ) : ℝ≥0))
    core site p q r u v w key
    (fun ev => hP_deg (eventHead d ev))
    (fun ev => hQ_deg (eventHead d ev))
    (fun ev => hR_deg (eventHead d ev))
    (fun ev x hx => hcore_agree (eventHead d ev) x hx)
    (fun ev => by rw [show (core ev).card = 2 * d from hcore_card (eventHead d ev)]; omega)
    (fun ev => by
      rw [Fintype.card_fin, show (core ev).card = 2 * d from hcore_card (eventHead d ev)]
      have hnpos : (0 : ℝ≥0) < ((4 * (d + 1) : ℕ) : ℝ≥0) := by exact_mod_cast (by omega : 0 < 4 * (d + 1))
      have hne : ((4 * (d + 1) : ℕ) : ℝ≥0) ≠ 0 := hnpos.ne'
      rw [tsub_mul, one_mul, div_mul_cancel₀ _ hne]
      rw [tsub_le_iff_right]
      exact_mod_cast (by omega : 4 * (d + 1) ≤ (2 * d + 1) + (2 * d + 3)))
    hmis hkey hinj
    (by rw [card_event d hd1, Nat.card_eq_fintype_card]; exact hfield)
  rwa [card_event d hd1] at hm

/-- **Universal quarter-rate Johnson-pivot domain-independent barrier.**
For ANY `d ≥ 3` and ANY finite field `F` containing a primitive `(d - 1)`-th root `ω` and
nonzero `u₀, v₀` with `1, u₀^(d-1), v₀^(d-1)` pairwise distinct and
`Choose(8d + 10, 2) ≤ |F|`, there exists an evaluation domain `dom : Fin (4*(d+1)) ↪ F`
achieving `(8d + 10) / |F| = (2n + 2) / |F| ≤ epsMCA` at the exact finite-Johnson pivot
`e = 2d + 3 = n/2 + 1` (strictly below `1 - √(d/n)`), for every positive interleaving width. -/
theorem universal_quarter_pivot_failure
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (hd : 3 ≤ d)
    (ω u₀ v₀ : F) (hω : orderOf ω = d - 1) (hu₀ : u₀ ≠ 0) (hv₀ : v₀ ≠ 0)
    (hr1 : u₀ ^ (d - 1) ≠ 1) (hs1 : v₀ ^ (d - 1) ≠ 1) (hrs : u₀ ^ (d - 1) ≠ v₀ ^ (d - 1))
    (hfield : (8 * d + 10).choose 2 ≤ Fintype.card F) :
    ∃ dom : Fin (4 * (d + 1)) ↪ F,
      (((2 * d + 3 : ℕ) : ℝ) / ((4 * (d + 1) : ℕ) : ℝ)) <
        1 - Real.sqrt ((d : ℝ) / ((4 * (d + 1) : ℕ) : ℝ)) ∧
      ∀ (width : ℕ) [NeZero width],
        ((8 * d + 10 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
          epsMCA (F := F)
            ((ReedSolomon.code dom (d + 1) : Set (Fin (4 * (d + 1)) → F)) ^⋈ (Fin width))
            (((2 * d + 3 : ℕ) : ℝ≥0) / ((4 * (d + 1) : ℕ) : ℝ≥0)) := by
  have hd1 : 1 ≤ d := by omega
  have hm_pos : 0 < d - 1 := by omega
  let B12 : Finset F := univ.image (fun j : Fin (d - 1) => ω ^ j.val)
  let B13 : Finset F := univ.image (fun j : Fin (d - 1) => u₀ * ω ^ j.val)
  let B23 : Finset F := univ.image (fun j : Fin (d - 1) => v₀ * ω ^ j.val)
  have hcoset_inj (c : F) (hc : c ≠ 0) :
      Function.Injective (fun j : Fin (d - 1) => c * ω ^ j.val) := by
    intro i j hij
    have hpow : ω ^ i.val = ω ^ j.val := mul_left_cancel₀ hc hij
    have hi : i.val ∈ Set.Iio (orderOf ω) := by rw [hω]; exact i.isLt
    have hj : j.val ∈ Set.Iio (orderOf ω) := by rw [hω]; exact j.isLt
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj hpow)
  have hB12_card : B12.card = d - 1 := by
    have hinj : Function.Injective (fun j : Fin (d - 1) => ω ^ j.val) := by
      intro i j hij
      exact hcoset_inj 1 one_ne_zero (by simpa using hij)
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hB13_card : B13.card = d - 1 := by
    rw [card_image_of_injective _ (hcoset_inj u₀ hu₀), card_univ, Fintype.card_fin]
  have hB23_card : B23.card = d - 1 := by
    rw [card_image_of_injective _ (hcoset_inj v₀ hv₀), card_univ, Fintype.card_fin]
  have hωd : ω ^ (d - 1) = 1 := by rw [← hω, pow_orderOf_eq_one]
  have hpow_B12 : ∀ x ∈ B12, x ^ (d - 1) = 1 := by
    intro x hx
    rcases mem_image.mp hx with ⟨j, _, rfl⟩
    rw [← pow_mul, Nat.mul_comm, pow_mul, hωd, one_pow]
  have hpow_B13 : ∀ x ∈ B13, x ^ (d - 1) = u₀ ^ (d - 1) := by
    intro x hx
    rcases mem_image.mp hx with ⟨j, _, rfl⟩
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, hωd, one_pow, mul_one]
  have hpow_B23 : ∀ x ∈ B23, x ^ (d - 1) = v₀ ^ (d - 1) := by
    intro x hx
    rcases mem_image.mp hx with ⟨j, _, rfl⟩
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, hωd, one_pow, mul_one]
  have hU_card : (B12 ∪ B13 ∪ B23).card ≤ 3 * (d - 1) := by
    calc (B12 ∪ B13 ∪ B23).card
        ≤ (B12 ∪ B13).card + B23.card := card_union_le _ _
      _ ≤ B12.card + B13.card + B23.card := Nat.add_le_add_right (card_union_le _ _) _
      _ = 3 * (d - 1) := by rw [hB12_card, hB13_card, hB23_card]; omega
  have h4d_le : 4 * d + 4 ≤ Fintype.card F := by
    have hch : 4 * d + 4 ≤ (8 * d + 10).choose 2 := by
      rw [Nat.choose_two_right, show 8 * d + 10 - 1 = 8 * d + 9 by omega]
      have h1 : 2 * (4 * d + 4) ≤ (8 * d + 10) * (8 * d + 9) := by nlinarith
      omega
    exact hch.trans hfield
  have hcompl_card : d + 7 ≤ (B12 ∪ B13 ∪ B23)ᶜ.card := by
    rw [card_compl]
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hcompl_card
  let eR : Fin (d + 7) ≃ R := (Fintype.equivFinOfCardEq (by simp [hRcard])).symm
  let rem (i : Fin (d + 7)) : F := (eR i).1
  have hrem_inj : Function.Injective rem := fun i j hij => eR.injective (Subtype.ext hij)
  have hrem_not_U (i : Fin (d + 7)) : rem i ∉ B12 ∪ B13 ∪ B23 := by
    have hmem : rem i ∈ (B12 ∪ B13 ∪ B23)ᶜ := hRsub (eR i).2
    exact mem_compl.mp hmem
  -- Map `Site d → F` directly
  let domSite : Site d → F
    | .b12 j => ω ^ j.val
    | .b13 j => u₀ * ω ^ j.val
    | .b23 j => v₀ * ω ^ j.val
    | .e1 j => rem ⟨j.val, by omega⟩
    | .e2 j => rem ⟨2 + j.val, by omega⟩
    | .e3 j => rem ⟨4 + j.val, by omega⟩
    | .brem j => rem ⟨6 + j.val, by omega⟩
  have hdomSite_inj : Function.Injective domSite := by
    have hmem12 (j : Fin (d - 1)) : domSite (.b12 j) ∈ B12 :=
      mem_image.mpr ⟨j, mem_univ _, rfl⟩
    have hmem13 (j : Fin (d - 1)) : domSite (.b13 j) ∈ B13 :=
      mem_image.mpr ⟨j, mem_univ _, rfl⟩
    have hmem23 (j : Fin (d - 1)) : domSite (.b23 j) ∈ B23 :=
      mem_image.mpr ⟨j, mem_univ _, rfl⟩
    have h12_13 (i j : Fin (d - 1)) (h : domSite (.b12 i) = domSite (.b13 j)) : False := by
      have hp := congrArg (fun y : F => y ^ (d - 1)) h
      rw [hpow_B12 _ (hmem12 i), hpow_B13 _ (hmem13 j)] at hp
      exact hr1 hp.symm
    have h12_23 (i j : Fin (d - 1)) (h : domSite (.b12 i) = domSite (.b23 j)) : False := by
      have hp := congrArg (fun y : F => y ^ (d - 1)) h
      rw [hpow_B12 _ (hmem12 i), hpow_B23 _ (hmem23 j)] at hp
      exact hs1 hp.symm
    have h13_23 (i j : Fin (d - 1)) (h : domSite (.b13 i) = domSite (.b23 j)) : False := by
      have hp := congrArg (fun y : F => y ^ (d - 1)) h
      rw [hpow_B13 _ (hmem13 i), hpow_B23 _ (hmem23 j)] at hp
      exact hrs hp
    have hU_rem (y : F) (hy : y ∈ B12 ∪ B13 ∪ B23) (k : Fin (d + 7)) (h : y = rem k) : False :=
      hrem_not_U k (h ▸ hy)
    intro s₁ s₂ hEq
    cases s₁ <;> cases s₂
    · congr 1; exact hcoset_inj 1 one_ne_zero (by simpa [domSite] using hEq)
    · exact False.elim (h12_13 _ _ hEq)
    · exact False.elim (h12_23 _ _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq)
    · exact False.elim (h12_13 _ _ hEq.symm)
    · congr 1; exact hcoset_inj u₀ hu₀ hEq
    · exact False.elim (h13_23 _ _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq)
    · exact False.elim (h12_23 _ _ hEq.symm)
    · exact False.elim (h13_23 _ _ hEq.symm)
    · congr 1; exact hcoset_inj v₀ hv₀ hEq
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq.symm)
    · have hk := congrArg Fin.val (hrem_inj hEq); congr 1; exact Fin.ext (by omega)
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq.symm)
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk
      congr 1; exact Fin.ext (by omega)
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq.symm)
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk
      congr 1; exact Fin.ext (by omega)
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_left _ (hmem12 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_left _ (mem_union_right _ (hmem13 _))) _ hEq.symm)
    · exact False.elim (hU_rem _ (mem_union_right _ (hmem23 _)) _ hEq.symm)
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · exfalso; have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk; omega
    · have hk := congrArg Fin.val (hrem_inj hEq); dsimp at hk
      congr 1; exact Fin.ext (by omega)
  let e : Fin (4 * (d + 1)) ≃ Site d := (Fintype.equivFinOfCardEq (card_site d hd1)).symm
  let dom : Fin (4 * (d + 1)) ↪ F :=
    ⟨fun x => domSite (e x), fun _ _ h => e.injective (hdomSite_inj h)⟩
  refine ⟨dom, ?_, ?_⟩
  · -- Strict finite-Johnson comparison: `(4(d+1)) * d < (4(d+1) - (2d+3))^2 = (2d+1)^2`
    have hlt : 2 * d + 3 < 4 * (d + 1) + 1 := by omega
    have hsq : (4 * (d + 1)) * d < (4 * (d + 1) - (2 * d + 3)) ^ 2 := by
      have hsub : 4 * (d + 1) - (2 * d + 3) = 2 * d + 1 := by omega
      rw [hsub]
      nlinarith
    exact (below_iff (n := 4 * (d + 1)) (by omega) d (some ⟨2 * d + 3, hlt⟩)).mpr hsq
  · intro width _
    exact quarter_pivot_failure_of_domain d hd ω u₀ v₀ hω hu₀ hv₀ hr1 hs1 hrs dom e
      (fun j => by change domSite (e (e.symm (.b12 j))) = _; rw [e.apply_symm_apply])
      (fun j => by change domSite (e (e.symm (.b13 j))) = _; rw [e.apply_symm_apply])
      (fun j => by change domSite (e (e.symm (.b23 j))) = _; rw [e.apply_symm_apply])
      hfield width

/-! ## Part 2: Production-scale `n = 2^30`, `e = 536,870,913` domain-independent barrier -/

/-- A 159-bit smooth prize-shaped prime `Q` with `Q / 2^128 = 2^31 = 2n`,
`2^30 ∣ (Q - 1)`, and `(2^28 - 2) ∣ (Q - 1)`. Every prime factor of `Q - 1` is `≤ 357,283`. -/
abbrev Q : ℕ := 730750818869487914369817427303088068110372044801

theorem Q_sub_one_factorization :
    Q - 1 = 2 ^ 92 * 5 ^ 2 * 7 * 13 * 17 * 73 * 557 * 262657 * 357283 := by norm_num

private theorem Q_cert_main : (3 : ZMod Q) ^ (Q - 1) = 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q2 : (3 : ZMod Q) ^ ((Q - 1) / 2) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q5 : (3 : ZMod Q) ^ ((Q - 1) / 5) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q7 : (3 : ZMod Q) ^ ((Q - 1) / 7) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q13 : (3 : ZMod Q) ^ ((Q - 1) / 13) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q17 : (3 : ZMod Q) ^ ((Q - 1) / 17) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q73 : (3 : ZMod Q) ^ ((Q - 1) / 73) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q557 : (3 : ZMod Q) ^ ((Q - 1) / 557) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q262657 : (3 : ZMod Q) ^ ((Q - 1) / 262657) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide
private theorem Q_cert_q357283 : (3 : ZMod Q) ^ ((Q - 1) / 357283) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide

private theorem Q_cert_all (q : ℕ) (hq : Nat.Prime q) (hdvd : q ∣ Q - 1) :
    (3 : ZMod Q) ^ ((Q - 1) / q) ≠ 1 := by
  rw [show Q - 1 = 2 ^ 92 * (5 ^ 2 * (7 * (13 * (17 * (73 * (557 * (262657 * 357283)))))))
      by norm_num] at hdvd
  rcases hq.dvd_mul.mp hdvd with h2 | hr
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
    subst q; exact Q_cert_q2
  · rcases hq.dvd_mul.mp hr with h5 | hr
    · have hq5 : q = 5 :=
        (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h5)
      subst q; exact Q_cert_q5
    · rcases hq.dvd_mul.mp hr with h7 | hr
      · have hq7 : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7
        subst q; exact Q_cert_q7
      · rcases hq.dvd_mul.mp hr with h13 | hr
        · have hq13 : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h13
          subst q; exact Q_cert_q13
        · rcases hq.dvd_mul.mp hr with h17 | hr
          · have hq17 : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h17
            subst q; exact Q_cert_q17
          · rcases hq.dvd_mul.mp hr with h73 | hr
            · have hq73 : q = 73 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h73
              subst q; exact Q_cert_q73
            · rcases hq.dvd_mul.mp hr with h557 | hr
              · have hq557 : q = 557 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h557
                subst q; exact Q_cert_q557
              · rcases hq.dvd_mul.mp hr with h262657 | h357283
                · have hq262657 : q = 262657 :=
                    (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h262657
                  subst q; exact Q_cert_q262657
                · have hq357283 : q = 357283 :=
                    (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h357283
                  subst q; exact Q_cert_q357283

/-- Lucas primality certificate for the 159-bit modulus `Q`. -/
theorem prime_Q : Nat.Prime Q :=
  lucas_primality Q 3 Q_cert_main Q_cert_all

/-- `Q` matches the exact second-prime 128-bit security budget `B₂ = 2^31 = 2n`. -/
theorem Q_div_two_pow_128 : Q / 2 ^ 128 = 2 ^ 31 := by norm_num

/-- `Q` also supports a smooth multiplicative subgroup of order `2^30`. -/
theorem Q_modEq_one_two_pow_30 : Q ≡ 1 [MOD 2 ^ 30] := by norm_num [Nat.ModEq]

local instance fact_prime_Q : Fact Q.Prime := ⟨prime_Q⟩

private theorem orderOf_three_Q : orderOf (3 : ZMod Q) = Q - 1 := by
  have hdvd : orderOf (3 : ZMod Q) ∣ Q - 1 := orderOf_dvd_of_pow_eq_one Q_cert_main
  have hpos : 0 < orderOf (3 : ZMod Q) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨Q - 1, by decide, Q_cert_main⟩)
  by_contra hne
  have hlt : orderOf (3 : ZMod Q) < Q - 1 :=
    lt_of_le_of_ne (Nat.le_of_dvd (by decide) hdvd) hne
  rcases hdvd with ⟨k, hk⟩
  have hk1 : 1 < k := by
    by_contra hle
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> omega
  obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  have hqQ : q ∣ Q - 1 := dvd_trans hqk ⟨orderOf (3 : ZMod Q), by rw [hk, mul_comm]⟩
  have hord_dvd : orderOf (3 : ZMod Q) ∣ (Q - 1) / q := by
    rcases hqk with ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    have hmul : (Q - 1) / q = orderOf (3 : ZMod Q) * m := by
      rw [hk, show orderOf (3 : ZMod Q) * (q * m) = q * (orderOf (3 : ZMod Q) * m) by ring]
      exact Nat.mul_div_right _ hq.pos
    exact hmul
  exact Q_cert_all q hq hqQ (orderOf_dvd_iff_pow_eq_one.mp hord_dvd)

private abbrev dProd : ℕ := 2 ^ 28 - 1

private theorem omegaQ_order :
    orderOf ((3 : ZMod Q) ^ ((Q - 1) / (dProd - 1))) = dProd - 1 := by
  let c : ℕ := (Q - 1) / (dProd - 1)
  have hcm : c * (dProd - 1) = Q - 1 := by decide
  have hc_pos : 0 < c := by decide
  have hdvd1 : orderOf ((3 : ZMod Q) ^ c) ∣ dProd - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, hcm]
    exact Q_cert_main
  have hdvd2 : dProd - 1 ∣ orderOf ((3 : ZMod Q) ^ c) := by
    have hpow : (3 : ZMod Q) ^ (c * orderOf ((3 : ZMod Q) ^ c)) = 1 := by
      rw [pow_mul, pow_orderOf_eq_one]
    have hQ : Q - 1 ∣ c * orderOf ((3 : ZMod Q) ^ c) := by
      rw [← orderOf_three_Q]
      exact orderOf_dvd_of_pow_eq_one hpow
    rw [← hcm] at hQ
    exact (Nat.mul_dvd_mul_iff_left hc_pos).mp hQ
  exact Nat.dvd_antisymm hdvd1 hdvd2

private theorem two_pow_dProd_ne_one : (2 : ZMod Q) ^ (dProd - 1) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide

private theorem three_pow_dProd_ne_one : (3 : ZMod Q) ^ (dProd - 1) ≠ 1 := by
  rw [← binaryPow_eq_pow]; decide

private theorem two_pow_ne_three_pow_dProd :
    (2 : ZMod Q) ^ (dProd - 1) ≠ (3 : ZMod Q) ^ (dProd - 1) := by
  rw [← binaryPow_eq_pow, ← binaryPow_eq_pow]; decide

/-- **Production-scale domain-independent barrier at the quarter-rate Johnson pivot.**
In the certified smooth 159-bit prime field `ZMod Q` (`Q / 2^128 = 2^31`, `2^30 ∣ Q - 1`),
there exists an injective domain `dom : Fin (2^30) ↪ ZMod Q` on which, at every positive
interleaving width, the quarter-rate RS code (`k = 2^28`, `n = 2^30`) fails 128-bit MCA
security at the exact Johnson sign pivot `e = 536,870,913` (`epsMCA ≥ 2,147,483,650 / Q > 2^-128`),
forcing `mcaDeltaStar ≤ 536,870,913 / 2^30 < 1 - √((2^28 - 1) / 2^30)` strictly below the
finite-length Johnson radius. -/
theorem production_quarter_pivot_domain_independent_barrier :
    ∃ dom : Fin (2 ^ 30) ↪ ZMod Q,
      ∀ (width : ℕ) [NeZero width],
        let code := ((ReedSolomon.code dom (2 ^ 28) : Set (Fin (2 ^ 30) → ZMod Q)) ^⋈ (Fin width))
        let tol : ℝ≥0∞ := 1 / (2 : ℝ≥0∞) ^ 128
        (2147483650 : ℝ≥0∞) / (Q : ℝ≥0∞) ≤ epsMCA (F := ZMod Q) code (536870913 / 1073741824) ∧
        tol < epsMCA (F := ZMod Q) code (536870913 / 1073741824) ∧
        mcaDeltaStar (F := ZMod Q) code tol ≤ 536870913 / 1073741824 ∧
        (mcaDeltaStar (F := ZMod Q) code tol : ℝ) <
          1 - Real.sqrt (((2 ^ 28 - 1 : ℕ) : ℝ) / ((2 ^ 30 : ℕ) : ℝ)) := by
  have huniv := universal_quarter_pivot_failure (F := ZMod Q) dProd (by decide)
    ((3 : ZMod Q) ^ ((Q - 1) / (dProd - 1))) 2 3 omegaQ_order
    (by decide) (by decide)
    two_pow_dProd_ne_one three_pow_dProd_ne_one two_pow_ne_three_pow_dProd
    (by rw [ZMod.card, Nat.choose_two_right]; decide)
  rcases huniv with ⟨dom, hJ, hmass⟩
  refine ⟨dom, fun width _ => ?_⟩
  dsimp only
  have hm := hmass width
  rw [ZMod.card] at hm
  have hm' : (2147483650 : ℝ≥0∞) / (Q : ℝ≥0∞) ≤
      epsMCA (F := ZMod Q)
        ((ReedSolomon.code dom (2 ^ 28) : Set (Fin (2 ^ 30) → ZMod Q)) ^⋈ (Fin width))
        (536870913 / 1073741824) := by
    convert hm using 2
  have hb : 1 / (2 : ℝ≥0∞) ^ 128 < (2147483650 : ℝ≥0∞) / (Q : ℝ≥0∞) := by
    by_contra! h
    have hh := (BoundarySecurityBudget.count_ratio_le_iff prime_Q.pos
      (by decide : 0 < 2 ^ 128)).mp
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h :
        ((2147483650 : ℕ) : ℝ≥0∞) / Q ≤ 1 / ((2 ^ 128 : ℕ) : ℝ≥0∞))
    exact (by decide : ¬ 2147483650 ≤ Q / 2 ^ 128) hh
  have hbad := hb.trans_le hm'
  have hle := mcaDeltaStar_le_of_bad _ _ hbad
  have hbelow :
      (mcaDeltaStar (F := ZMod Q)
        ((ReedSolomon.code dom (2 ^ 28) : Set (Fin (2 ^ 30) → ZMod Q)) ^⋈ (Fin width))
        (1 / (2 : ℝ≥0∞) ^ 128) : ℝ) <
      1 - Real.sqrt (((2 ^ 28 - 1 : ℕ) : ℝ) / ((2 ^ 30 : ℕ) : ℝ)) := by
    have hleR :
        (mcaDeltaStar (F := ZMod Q)
          ((ReedSolomon.code dom (2 ^ 28) : Set (Fin (2 ^ 30) → ZMod Q)) ^⋈ (Fin width))
          (1 / (2 : ℝ≥0∞) ^ 128) : ℝ) ≤ (536870913 : ℝ) / (1073741824 : ℝ) := by
      exact_mod_cast hle
    have hJ' : (536870913 : ℝ) / (1073741824 : ℝ) <
        1 - Real.sqrt (((2 ^ 28 - 1 : ℕ) : ℝ) / ((2 ^ 30 : ℕ) : ℝ)) := by
      convert hJ using 2
    exact hleR.trans_lt hJ'
  exact ⟨hm', hbad, hle, hbelow⟩

/-! ## Part 3: Concrete smooth-subgroup instantiation `H = μ₁₆ < F₁₀₀₉` (`d = 3, n = 16, e = 9`) -/

private theorem prime_1009 : Nat.Prime 1009 := by norm_num

local instance fact_prime_1009 : Fact (Nat.Prime 1009) := ⟨prime_1009⟩

/-- An explicit primitive 16th root of unity in `ZMod 1009`. -/
def zeta16 : ZMod 1009 := (11 : ZMod 1009) ^ 63

theorem orderOf_zeta16 : orderOf zeta16 = 16 := by
  have h := orderOf_eq_prime_pow (x := zeta16) (p := 2) (n := 3) (by decide) (by decide)
  norm_num at h ⊢
  exact h

/-- The literal smooth multiplicative subgroup `μ₁₆` inside `ZMod 1009`. -/
def domMu16 : Fin 16 ↪ ZMod 1009 :=
  KKH26RegimeSplit.powDomain zeta16 orderOf_zeta16 (by decide)

private def equivMu16ToSite (x : Fin 16) : Site 3 :=
  match x.val with
  | 0 => .b12 0
  | 1 => .b13 0
  | 2 => .b23 0
  | 3 => .e1 0
  | 4 => .e1 1
  | 5 => .e2 0
  | 6 => .e2 1
  | 7 => .e3 0
  | 8 => .b12 1
  | 9 => .b13 1
  | 10 => .b23 1
  | 11 => .e3 1
  | 12 => .brem 0
  | 13 => .brem 1
  | 14 => .brem 2
  | _ => .brem 3

private def equivSiteToMu16 : Site 3 → Fin 16
  | .b12 ⟨0, _⟩ => 0
  | .b12 ⟨1, _⟩ => 8
  | .b13 ⟨0, _⟩ => 1
  | .b13 ⟨1, _⟩ => 9
  | .b23 ⟨0, _⟩ => 2
  | .b23 ⟨1, _⟩ => 10
  | .e1 ⟨0, _⟩ => 3
  | .e1 ⟨1, _⟩ => 4
  | .e2 ⟨0, _⟩ => 5
  | .e2 ⟨1, _⟩ => 6
  | .e3 ⟨0, _⟩ => 7
  | .e3 ⟨1, _⟩ => 11
  | .brem ⟨0, _⟩ => 12
  | .brem ⟨1, _⟩ => 13
  | .brem ⟨2, _⟩ => 14
  | .brem ⟨3, _⟩ => 15

private def equivMu16 : Fin 16 ≃ Site 3 where
  toFun := equivMu16ToSite
  invFun := equivSiteToMu16
  left_inv x := by fin_cases x <;> rfl
  right_inv s := by
    cases s with
    | b12 j => fin_cases j <;> rfl
    | b13 j => fin_cases j <;> rfl
    | b23 j => fin_cases j <;> rfl
    | e1 j => fin_cases j <;> rfl
    | e2 j => fin_cases j <;> rfl
    | e3 j => fin_cases j <;> rfl
    | brem j => fin_cases j <;> rfl

/-- **Concrete smooth-subgroup corollary (`n = 16, k = 4, e = 9` on `μ₁₆ ⊂ F₁₀₀₉`).**
Because `(d - 1) = 2 ∣ 16`, the 3-coset construction lands directly inside the literal smooth
subgroup `μ₁₆` and certifies `34 / 1009 ≤ epsMCA` (`34 > 32 = 2n`) strictly below the finite
Johnson radius `1 - √(3/16)`, for every positive interleaving width. -/
theorem smooth_mu16_f1009_quarter_pivot_failure (width : ℕ) [NeZero width] :
    ((9 : ℝ) / 16 < 1 - Real.sqrt ((3 : ℝ) / 16)) ∧
    ((34 : ℝ≥0∞) / 1009 ≤
      epsMCA (F := ZMod 1009)
        ((ReedSolomon.code domMu16 4 : Set (Fin 16 → ZMod 1009)) ^⋈ (Fin width))
        (9 / 16)) := by
  have hω2 : orderOf (zeta16 ^ 8) = 2 := by
    have h := orderOf_eq_prime_pow (x := zeta16 ^ 8) (p := 2) (n := 0) (by decide) (by decide)
    norm_num at h ⊢
    exact h
  constructor
  · exact (below_iff (n := 16) (by decide) 3 (some ⟨9, by decide⟩)).mpr (by decide)
  · have hm := quarter_pivot_failure_of_domain (F := ZMod 1009) 3 (by decide)
      (zeta16 ^ 8) zeta16 (zeta16 ^ 2) hω2
      (by decide) (by decide) (by decide) (by decide) (by decide)
      domMu16 equivMu16
      (fun j => by fin_cases j <;> decide)
      (fun j => by fin_cases j <;> decide)
      (fun j => by fin_cases j <;> decide)
      (by rw [ZMod.card]; decide)
      width
    rw [ZMod.card] at hm
    convert hm using 2

#print axioms quarter_pivot_failure_of_domain
#print axioms universal_quarter_pivot_failure
#print axioms prime_Q
#print axioms Q_div_two_pow_128
#print axioms Q_modEq_one_two_pow_30
#print axioms production_quarter_pivot_domain_independent_barrier
#print axioms smooth_mu16_f1009_quarter_pivot_failure

end ArkLib.ProximityGap.Frontier.QuarterPivotDomainIndependentBarrier
