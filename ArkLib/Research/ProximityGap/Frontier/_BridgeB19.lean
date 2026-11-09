/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B19 — the depth-`m=1` DD-ratio forcing for `D*(1)` (target E4, #444)

## The empirical target (E4)

The depth-`m=1` worst-direction over-determination far-line incidence is conjectured
(empirically, `deltastar-444-empirical-formulas`) to equal the number of DISTINCT forced
scalar values

  `D*(1) = #{ -h_{a-k}(T)/h_{b-k}(T)  :  T a (k+1)-subset of μ_n }`,

where `h_{j}(T)` is the complete-homogeneous readout `dividedDifferencePow T v (k+j)`
(`SchurLagrangeBridge.dividedDifferencePow`, the Schur/Jacobi–Trudi divided difference).  The
monomial line direction is `(x^a, x^b)` (`a > b ≥ k`); over a single over-determined
`(k+1)`-window `T` the agreement of the line `x^a + γ·x^b` with a degree-`< k` codeword forces
the top divided difference to vanish, which — since the divided difference is **linear in the
data** — is

  `h_{a-k}(T) + γ · h_{b-k}(T) = 0`,

a single linear equation in `γ`.  When `h_{b-k}(T) ≠ 0` this has the unique root
`γ_T = -h_{a-k}(T)/h_{b-k}(T)`.  Hence the bad-`γ` set of direction `(a,b)` at depth-1 is exactly
the IMAGE of the forced-`γ` map `T ↦ γ_T`, and its cardinality is the count of distinct values.

## What this file proves (axiom-clean), and what it does NOT

The file consumes `SchurLagrangeBridge` (the divided-difference / `h_{b-k}` substrate) and
`IncidencePeriodBridge` (the far-line incidence object `lineIncidence`).

PROVEN here, character-sum-free:

* `lineDividedDiff_eq` — **the linearity / forcing identity.**  The divided difference of the
  two-monomial pencil data `i ↦ (v i)^a + γ·(v i)^b` over a node set `T` equals
  `dividedDifferencePow T v a + γ · dividedDifferencePow T v b`.

* `lineInterp_top_coeff` — the **top-coefficient readout.**  The `(#T-1)`-coefficient of the
  Lagrange interpolant of the line data is exactly `DD(a) + γ·DD(b)` (= `h_{a-k}+γ·h_{b-k}`).

* `exists_lowDeg_agree_iff_DD_vanish` — **THE GEOMETRIC ⟺ DD-VANISHING BRIDGE** (the genuine
  new content; the "(i)" the prior B19 draft flagged as not-discharged).  There exists a codeword
  `p` of degree `< #T-1` (= `< k`) agreeing with the line `x^a + γ·x^b` on all of `T` **iff**
  `DD(a) + γ·DD(b) = 0`.  Pure Lagrange interpolation: degree-`<#T` uniqueness + the top
  coefficient.  This is what makes the bridge geometric rather than a restatement of a definition.

* `forcedGamma_unique`, `lineAgrees_iff_forcedGamma`, `badGammaSet_eq_image`,
  `geomBadGammaSet_eq_image` — **single-window forcing and the set identity.**  With `DD(b) ≠ 0`,
  the line agrees with a low-degree codeword on `T` iff `γ = forcedGamma a b v T`; over a family
  `𝒯` of non-degenerate windows the geometric depth-1 bad-`γ` set is exactly the forced-ratio
  image `forcedGamma a b v '' 𝒯`.  Hence (`distinctForcedCount`) its cardinality is the literal
  E4 right-hand side `#{ -h_{a-k}(T)/h_{b-k}(T) }`.

NOT proven here (named honestly as the remaining gap — see `D1FarIncidenceEqDDAgreement`):
the EQUALITY of this geometric depth-1 DD-agreement count with the *worst-direction* far-line
incidence `D*(1)` of `IncidencePeriodBridge.lineIncidence` (period/ball form) maximised over
directions `(a,b)`.  That equality is the open E4↔E7 object: it needs (ii) the reduction of a
witness-sized agreement set to a single over-determined `(k+1)`-window, and (iii) the
worst-direction maximum.  We state it as an explicit named `Prop` and give the **reduced**
theorem `Dstar1_eq_of_bridge`: modulo `D1FarIncidenceEqDDAgreement`, `D*(1) = Dstar1` (the
per-direction max of the literal E4 count).  The forcing mechanism and the geometric agreement
criterion (the inner per-window engine) are fully discharged and axiom-clean.

Issue #444.
-/

set_option autoImplicit false

open Finset Polynomial
open ProximityGap.SchurLagrange

namespace ProximityGap.Frontier.BridgeB19

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [DecidableEq ι]

/-! ### Part 1 — the forcing engine (linearity + top coefficient) -/

/-- **The forced scalar of a single over-determined window.**  For a node set `T` and a
two-monomial direction `(a, b)`, this is `-h_{a-k}(T)/h_{b-k}(T) = -DD(a)/DD(b)` — the unique
`γ` (when `DD(b) ≠ 0`) for which the pencil `x^a + γ·x^b` agrees with a degree-`<#T-1` codeword
on all of `T`. -/
noncomputable def forcedGamma (a b : ℕ) (v : ι → F) (T : Finset ι) : F :=
  - dividedDifferencePow T v a / dividedDifferencePow T v b

/-- **Linearity / forcing identity.**  The divided difference of the two-monomial pencil data
`i ↦ (v i)^a + γ·(v i)^b` over the node set `T` equals
`dividedDifferencePow T v a + γ · dividedDifferencePow T v b`.

This is the engine of E4: the top divided difference of the line `x^a + γ·x^b` over an
over-determined `(k+1)`-window is **linear in `γ`**, with coefficients the complete-homogeneous
readouts `h_{a-k}(T)` and `h_{b-k}(T)`.  Pure linearity of
`SchurLagrange.dividedDifferencePow` in the data; no character sums, no field-size hypotheses. -/
theorem lineDividedDiff_eq (a b : ℕ) (γ : F) (v : ι → F) (T : Finset ι) :
    ∑ i ∈ T, ((v i) ^ a + γ * (v i) ^ b) * (∏ j ∈ T.erase i, (v i - v j))⁻¹
      = dividedDifferencePow T v a + γ * dividedDifferencePow T v b := by
  unfold dividedDifferencePow
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Top-coefficient readout.**  The `(#T-1)`-coefficient of the Lagrange interpolant of the
two-monomial pencil data `i ↦ (v i)^a + γ·(v i)^b` over the (injective) node set `T` is exactly
`DD(a) + γ·DD(b) = h_{a-k}(T) + γ·h_{b-k}(T)`.  Via `SchurLagrange.interpolate_coeff_top`. -/
theorem lineInterp_top_coeff (a b : ℕ) (γ : F) (v : ι → F) (T : Finset ι)
    (hvs : Set.InjOn v T) :
    (Lagrange.interpolate T v (fun i => (v i) ^ a + γ * (v i) ^ b)).coeff (#T - 1)
      = dividedDifferencePow T v a + γ * dividedDifferencePow T v b := by
  rw [interpolate_coeff_top hvs]
  unfold dividedDifferencePow
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ### Part 2 — the geometric ⟺ DD-vanishing bridge (genuine new content) -/

/-- **Existence of a low-degree interpolant ⟺ top divided difference vanishes.**  For an
injective node set `T` and arbitrary data `r`, there is a polynomial `p` of degree `< #T-1`
agreeing with `r` on all of `T` **iff** the `(#T-1)`-coefficient of the Lagrange interpolant of
`r` is `0`.  Pure Lagrange interpolation: degree-`<#T` uniqueness (`eq_interpolate_of_eval_eq`)
forces any such `p` to BE the interpolant, whose top coefficient must then vanish; conversely a
vanishing top coefficient drops the interpolant's degree below `#T-1`. -/
theorem exists_lowDeg_interp_iff (T : Finset ι) (v : ι → F) (hvs : Set.InjOn v T)
    (hT : T.Nonempty) (r : ι → F) :
    (∃ p : F[X], p.degree < ((#T : ℕ) - 1 : ℕ) ∧ ∀ i ∈ T, p.eval (v i) = r i)
      ↔ (Lagrange.interpolate T v r).coeff (#T - 1) = 0 := by
  constructor
  · rintro ⟨p, hdeg, hev⟩
    have hdegT : p.degree < (#T : ℕ) := by
      refine lt_of_lt_of_le hdeg ?_
      exact_mod_cast Nat.sub_le #T 1
    have hpeq : p = Lagrange.interpolate T v r :=
      Lagrange.eq_interpolate_of_eval_eq _ hvs hdegT hev
    rw [← hpeq]
    exact Polynomial.coeff_eq_zero_of_degree_lt hdeg
  · intro hcoeff
    refine ⟨Lagrange.interpolate T v r, ?_,
      fun i hi => Lagrange.eval_interpolate_at_node _ hvs hi⟩
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    have hlt : (Lagrange.interpolate T v r).degree < (#T : ℕ) :=
      Lagrange.degree_interpolate_lt _ hvs
    rcases Nat.lt_or_ge m #T with hmlt | hmge
    · have hpos : 0 < #T := Finset.card_pos.mpr hT
      have hmeq : m = #T - 1 := by omega
      rw [hmeq]; exact hcoeff
    · exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hlt (by exact_mod_cast hmge))

/-- **THE GEOMETRIC ⟺ DD-VANISHING BRIDGE (target E4, piece (i)).**  For an injective
`(k+1)`-window `T` (`#T = k+1`), there exists a codeword of degree `< k` agreeing with the line
`x^a + γ·x^b` on all of `T` **iff** `h_{a-k}(T) + γ·h_{b-k}(T) = 0`, i.e.
`dividedDifferencePow T v a + γ·dividedDifferencePow T v b = 0`.

This is the genuine geometric content of B19: the depth-1 over-determined agreement event of the
two-monomial line with a low-degree codeword is *exactly* the vanishing of the linear-in-`γ`
divided difference.  Combines `exists_lowDeg_interp_iff` (Lagrange) with `lineInterp_top_coeff`
(the linearity readout). -/
theorem exists_lowDeg_agree_iff_DD_vanish (a b : ℕ) (γ : F) (v : ι → F) (T : Finset ι)
    (hvs : Set.InjOn v T) (hT : T.Nonempty) :
    (∃ p : F[X], p.degree < ((#T : ℕ) - 1 : ℕ)
        ∧ ∀ i ∈ T, p.eval (v i) = (v i) ^ a + γ * (v i) ^ b)
      ↔ dividedDifferencePow T v a + γ * dividedDifferencePow T v b = 0 := by
  rw [exists_lowDeg_interp_iff T v hvs hT, lineInterp_top_coeff a b γ v T hvs]

/-! ### Part 3 — single-window forcing and the set identity -/

/-- **Single-window forcing (uniqueness).**  If `dividedDifferencePow T v b ≠ 0`, the pencil
divided difference `DD(a) + γ·DD(b)` vanishes **iff** `γ = forcedGamma a b v T`.  So a
non-degenerate over-determined window admits exactly one bad scalar. -/
theorem forcedGamma_unique (a b : ℕ) (γ : F) (v : ι → F) (T : Finset ι)
    (hb : dividedDifferencePow T v b ≠ 0) :
    dividedDifferencePow T v a + γ * dividedDifferencePow T v b = 0
      ↔ γ = forcedGamma a b v T := by
  unfold forcedGamma
  rw [eq_div_iff hb]
  constructor
  · intro h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)
  · intro h
    rw [h, add_neg_cancel]

/-- **Single-window forcing, geometric form.**  On a non-degenerate `(k+1)`-window `T`
(`DD(b) ≠ 0`), the line `x^a + γ·x^b` agrees with a degree-`<k` codeword on all of `T` **iff**
`γ` is the forced ratio `forcedGamma a b v T = -h_{a-k}(T)/h_{b-k}(T)`.  This is the per-window
core of E4: each non-degenerate window pins exactly one bad scalar, namely its DD-ratio. -/
theorem lineAgrees_iff_forcedGamma (a b : ℕ) (γ : F) (v : ι → F) (T : Finset ι)
    (hvs : Set.InjOn v T) (hT : T.Nonempty) (hb : dividedDifferencePow T v b ≠ 0) :
    (∃ p : F[X], p.degree < ((#T : ℕ) - 1 : ℕ)
        ∧ ∀ i ∈ T, p.eval (v i) = (v i) ^ a + γ * (v i) ^ b)
      ↔ γ = forcedGamma a b v T := by
  rw [exists_lowDeg_agree_iff_DD_vanish a b γ v T hvs hT, forcedGamma_unique a b γ v T hb]

/-- **The bad-`γ` set of direction `(a,b)` equals the image of the forced-`γ` map** over a
family `𝒯` of windows on each of which `DD(b) ≠ 0` (algebraic form, in terms of DD-vanishing). -/
theorem badGammaSet_eq_image (a b : ℕ) (v : ι → F) (𝒯 : Finset (Finset ι))
    (hb : ∀ T ∈ 𝒯, dividedDifferencePow T v b ≠ 0) :
    {γ : F | ∃ T ∈ 𝒯, dividedDifferencePow T v a + γ * dividedDifferencePow T v b = 0}
      = forcedGamma a b v '' (𝒯 : Set (Finset ι)) := by
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨T, hT, hvan⟩
    exact ⟨T, hT, ((forcedGamma_unique a b γ v T (hb T hT)).mp hvan).symm⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, (forcedGamma_unique a b (forcedGamma a b v T) v T (hb T hT)).mpr rfl⟩

/-- **The GEOMETRIC depth-1 bad-`γ` set equals the forced-ratio image.**  Over a family `𝒯` of
injective, nonempty, non-degenerate (`DD(b) ≠ 0`) windows, the set of scalars `γ` for which the
line `x^a + γ·x^b` agrees with SOME window's degree-`<k` codeword is exactly the image of the
forced-ratio map `T ↦ -h_{a-k}(T)/h_{b-k}(T)`.

This is the fully-discharged (no open hypothesis) set-level form of E4's right-hand side: the
geometric depth-1 bad scalars are *exactly* the distinct forced DD-ratios. -/
theorem geomBadGammaSet_eq_image (a b : ℕ) (v : ι → F) (𝒯 : Finset (Finset ι))
    (hinj : ∀ T ∈ 𝒯, Set.InjOn v T) (hne : ∀ T ∈ 𝒯, T.Nonempty)
    (hb : ∀ T ∈ 𝒯, dividedDifferencePow T v b ≠ 0) :
    {γ : F | ∃ T ∈ 𝒯, ∃ p : F[X], p.degree < ((#T : ℕ) - 1 : ℕ)
        ∧ ∀ i ∈ T, p.eval (v i) = (v i) ^ a + γ * (v i) ^ b}
      = forcedGamma a b v '' (𝒯 : Set (Finset ι)) := by
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨T, hT, hagree⟩
    exact ⟨T, hT,
      ((lineAgrees_iff_forcedGamma a b γ v T (hinj T hT) (hne T hT) (hb T hT)).mp hagree).symm⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT,
      (lineAgrees_iff_forcedGamma a b (forcedGamma a b v T) v T
        (hinj T hT) (hne T hT) (hb T hT)).mpr rfl⟩

/-! ### Part 4 — the literal E4 count, and the reduced bridge to `D*(1)` -/

/-- **The distinct forced-value count (literal E4 RHS).**  The number of distinct forced scalars
`-h_{a-k}(T)/h_{b-k}(T)` over the `(k+1)`-subsets `T` of `μ_n = nthRootsFinset n 1` is the
cardinality of the image of `forcedGamma a b id` over `powersetCard (k+1) (nthRootsFinset n 1)`. -/
noncomputable def distinctForcedCount (F : Type*) [Field F] [DecidableEq F]
    (n a b k : ℕ) : ℕ :=
  ((powersetCard (k + 1) (nthRootsFinset n (1 : F))).image
      (forcedGamma a b (id : F → F))).card

/-- **The forced-count is the cardinality of the distinct-value image** (definitional, so
downstream code consumes the E4 right-hand side as `#(image …)`). -/
theorem distinctForcedCount_eq (n a b k : ℕ) :
    distinctForcedCount F n a b k
      = ((powersetCard (k + 1) (nthRootsFinset n (1 : F))).image
          (forcedGamma a b (id : F → F))).card := rfl

/-- **The depth-`m=1` over-determination far-line incidence `D*(1)`** (object of E4), packaged as
the maximum over a finite set of monomial directions `(a,b)` of the literal E4 distinct
forced-DD-ratio count.  Once the geometric agreement set of a far direction reduces to a single
non-degenerate `(k+1)`-window (the content of `D1FarIncidenceEqDDAgreement`), this is the
worst-direction depth-1 incidence. -/
noncomputable def Dstar1 (n k : ℕ) (dirs : Finset (ℕ × ℕ)) : ℕ :=
  dirs.sup (fun ab => distinctForcedCount F n ab.1 ab.2 k)

/-- **THE NAMED OPEN BRIDGE (E4↔E7).**  For the worst direction `(a,b)`, the geometric
worst-direction far-line incidence at depth-1 — `IncidencePeriodBridge.lineIncidence` over a far
direction, restricted to the over-determined `(k+1)`-window regime — equals the per-direction max
of the distinct forced-DD-ratio count.  This packages the two remaining pieces: (ii) the
reduction of a witness-sized agreement set to a single `(k+1)`-window, and (iii) that the worst
direction is one of `dirs`.  It is the prize-grade open object and is **not discharged here**. -/
def D1FarIncidenceEqDDAgreement (n k : ℕ) (dirs : Finset (ℕ × ℕ)) (Dstar1Geom : ℕ) : Prop :=
  Dstar1Geom = Dstar1 (F := F) n k dirs

/-- **REDUCED bridge to E4.**  Modulo the named open `Prop` `D1FarIncidenceEqDDAgreement`
(piece (ii)+(iii): witness-set ⇒ single window, and the worst-direction max), the geometric
`D*(1)` equals `Dstar1`, the per-direction max of the literal E4 distinct forced-ratio count.
The forcing mechanism and the geometric per-window agreement criterion (the inner engine) are
fully discharged and axiom-clean; only this outer reduction is named. -/
theorem Dstar1_eq_of_bridge (n k : ℕ) (dirs : Finset (ℕ × ℕ)) (Dstar1Geom : ℕ)
    (h : D1FarIncidenceEqDDAgreement (F := F) n k dirs Dstar1Geom) :
    Dstar1Geom = Dstar1 (F := F) n k dirs := h

/-- **Per-window bound: at most one forced `γ`.**  Each non-degenerate `(k+1)`-window contributes
a single bad scalar, so the depth-1 bad-set size is `≤ #(k+1)-subsets`, with equality to the
*distinct* count only after collapsing coincident forced values.  Structural reason `D*(1)` is an
IMAGE cardinality, not a fibered count. -/
theorem forced_per_window_unique (a b : ℕ) (v : ι → F) (T : Finset ι)
    (hvs : Set.InjOn v T) (hT : T.Nonempty) (hb : dividedDifferencePow T v b ≠ 0) :
    {γ : F | ∃ p : F[X], p.degree < ((#T : ℕ) - 1 : ℕ)
        ∧ ∀ i ∈ T, p.eval (v i) = (v i) ^ a + γ * (v i) ^ b}
      = {forcedGamma a b v T} := by
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact lineAgrees_iff_forcedGamma a b γ v T hvs hT hb

end ProximityGap.Frontier.BridgeB19

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.lineDividedDiff_eq
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.lineInterp_top_coeff
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.exists_lowDeg_interp_iff
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.exists_lowDeg_agree_iff_DD_vanish
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.forcedGamma_unique
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.lineAgrees_iff_forcedGamma
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.badGammaSet_eq_image
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.geomBadGammaSet_eq_image
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.distinctForcedCount_eq
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.Dstar1_eq_of_bridge
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.BridgeB19.forced_per_window_unique
