/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Issue #232 — the codimension-excess-2 core-elimination bound (ePrint 2026/858, Thm 38)

The FRI-relevant codimension excess for the list-size landscape past Johnson is `c = 2`
(rate 1/2, `w = n/2 − 2`). ePrint 2026/858 §7.5 proves the only known `p`-independent
worst-case bound there, via the **Möbius structure on `(w−1)`-cores** (their Lemma 37) and
degree-2 elimination (their Theorem 38): on any syndrome line `s(γ) = s₁ + γ·s₂`,

    `M_compat(s₁, s₂) ≤ min(p, 2·C(n, w−1))`.

This file machine-checks the elimination engine and the count, and **surfaces an honest
proviso the paper's `min` packaging hides**: when a core's elimination quadratic vanishes
identically, only the trivial `|F|` bound survives — the `2·C(n, w−1)` component requires
a nondegeneracy hypothesis. We give the *sharp minimal* such hypothesis: every error
support `E` has at least one core whose quadratic is nonzero. The degeneracy lemma
(`coreQuad_eq_zero_of_degenerate`) shows this is exactly the right granularity: a support
whose syndrome constraints degenerate (all four window functionals vanish, so *every*
`γ ∈ F` is compatible) forces *all* of its cores' quadratics to vanish identically.

Contents (all axiom-clean, any field `F`):

* `synd`/`syndr` — the coefficient-window syndrome functional `⟨X^r·Λ_E, s⟩` of the
  error-locator polynomial `Λ_E = ∏_{a ∈ E} (X − a)`.
* `syndr_insert` — the **shift identity** (the engine of their Lemma 37):
  `⟨X^r·Λ_{C∪{x}}, s⟩ = ⟨X^{r+1}·Λ_C, s⟩ − α_x·⟨X^r·Λ_C, s⟩` — the compatibility system
  is *bilinear* in `(α_x, γ)`.
* `coreQuad` — the degree-`≤ 2` elimination resultant of the two bilinear equations.
* `coreQuad_eval_eq_zero` — any compatible extension point of a core is a root of its
  quadratic (their Theorem 38's elimination step).
* `coreQuad_eq_zero_of_degenerate` — a degenerate support kills the quadratic of every
  one of its cores (the honest-proviso lemma; not stated in the paper).
* `gamma_unique` — at a core with nonzero quadratic, each extension point admits at most
  one compatible `γ` (the Möbius-image well-definedness, char-free, division-free).
* `c2_core_bound` — the count: under the minimal nondegeneracy hypothesis,
  `#{γ : ∃ E, compatible} ≤ 2·C(n, w−1)`.
* `c2_card_bound` / `c2_min_bound` — the trivial `|F|` bound and the honest `min` form.

The bound complements the in-tree ladder: `c ≥ w` unique decoding, the Fisher/incidence
cap (round 11 = their phase diagram's incidence regime), the GS walls at Johnson, and
their Conjecture 41 (`c ≥ 3` rank lemma) ≈ the prize's open core, which starts exactly
one codimension above this theorem.
-/

namespace C2CoreBound

open Polynomial Finset

variable {F : Type*} [Field F]

/-- The coefficient-window syndrome pairing: `⟨P, s⟩ = ∑_{j < N} P_j · s_j`. -/
def synd (s : ℕ → F) (N : ℕ) (P : F[X]) : F := ∑ j ∈ Finset.range N, P.coeff j * s j

/-- The error-locator polynomial of a support `E ⊆ F`. -/
noncomputable def loc (E : Finset F) : F[X] := ∏ a ∈ E, (X - C a)

/-- The `r`-shifted syndrome functional of a support. -/
noncomputable def syndr (s : ℕ → F) (N r : ℕ) (E : Finset F) : F :=
  synd s N (X ^ r * loc E)

/-- The codimension-2 compatibility system for support `E` at line parameter `γ`:
both error-locator normals `Λ_E` and `X·Λ_E` annihilate `s₁ + γ·s₂` on the window. -/
def Compat (s₁ s₂ : ℕ → F) (N : ℕ) (E : Finset F) (γ : F) : Prop :=
  syndr s₁ N 0 E + γ * syndr s₂ N 0 E = 0 ∧
  syndr s₁ N 1 E + γ * syndr s₂ N 1 E = 0

/-- Linearity of the window pairing under the locator factorization — the **shift
identity** behind the Möbius structure on cores (2026/858 Lemma 37): adjoining the
point `a` to a core acts linearly in `a` on every shifted syndrome functional. -/
lemma syndr_insert [DecidableEq F] (s : ℕ → F) (N r : ℕ) {Cs : Finset F} {a : F}
    (ha : a ∉ Cs) :
    syndr s N r (insert a Cs)
      = syndr s N (r + 1) Cs - a * syndr s N r Cs := by
  have hloc : loc (insert a Cs) = (X - C a) * loc Cs := by
    rw [loc, Finset.prod_insert ha]
    rfl
  have harg : (X : F[X]) ^ r * ((X - C a) * loc Cs)
      = X ^ (r + 1) * loc Cs - C a * (X ^ r * loc Cs) := by ring
  rw [syndr, hloc, harg]
  simp only [synd, coeff_sub, coeff_C_mul, sub_mul, Finset.sum_sub_distrib]
  rw [syndr, syndr, synd, synd, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The core elimination quadratic: eliminating `γ` between the two bilinear
compatibility equations of the core `Cs` leaves this degree-`≤ 2` polynomial in the
extension point. -/
noncomputable def coreQuad (s₁ s₂ : ℕ → F) (N : ℕ) (Cs : Finset F) : F[X] :=
  C (syndr s₁ N 1 Cs * syndr s₂ N 2 Cs - syndr s₁ N 2 Cs * syndr s₂ N 1 Cs)
  + C (syndr s₁ N 2 Cs * syndr s₂ N 0 Cs - syndr s₁ N 0 Cs * syndr s₂ N 2 Cs) * X
  + C (syndr s₁ N 0 Cs * syndr s₂ N 1 Cs - syndr s₁ N 1 Cs * syndr s₂ N 0 Cs) * X ^ 2

lemma coreQuad_natDegree_le (s₁ s₂ : ℕ → F) (N : ℕ) (Cs : Finset F) :
    (coreQuad s₁ s₂ N Cs).natDegree ≤ 2 := by
  unfold coreQuad
  refine le_trans (natDegree_add_le _ _) ?_
  rw [max_le_iff]
  constructor
  · refine le_trans (natDegree_add_le _ _) ?_
    rw [max_le_iff]
    refine ⟨(natDegree_C _).le.trans (by norm_num), ?_⟩
    exact le_trans (natDegree_C_mul_le _ _) (by simp [natDegree_X])
  · exact le_trans (natDegree_C_mul_le _ _) (by simp)

/-- **The elimination step** (2026/858 Theorem 38): if the support `Cs ∪ {a}` is
compatible at some `γ`, then `a` is a root of the core quadratic of `Cs`. -/
lemma coreQuad_eval_eq_zero [DecidableEq F] {s₁ s₂ : ℕ → F} {N : ℕ} {Cs : Finset F} {a γ : F}
    (ha : a ∉ Cs) (h : Compat s₁ s₂ N (insert a Cs) γ) :
    (coreQuad s₁ s₂ N Cs).eval a = 0 := by
  obtain ⟨h₀, h₁⟩ := h
  rw [syndr_insert s₁ N 0 ha, syndr_insert s₂ N 0 ha] at h₀
  rw [syndr_insert s₁ N 1 ha, syndr_insert s₂ N 1 ha] at h₁
  simp only [coreQuad, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination (syndr s₂ N 2 Cs - a * syndr s₂ N 1 Cs) * h₀
    - (syndr s₂ N 1 Cs - a * syndr s₂ N 0 Cs) * h₁

/-- **The honest-proviso lemma** (not stated in 2026/858): a *degenerate* support —
one where all four window functionals vanish, so every `γ ∈ F` is compatible — forces
the core quadratic of **every** one of its cores to vanish identically. Hence the
nondegeneracy hypothesis of `c2_core_bound` below is exactly what excludes the
`M_compat = |F|` blow-up, and the paper's `min(p, 2·C(n,w−1))` needs it for its second
component. -/
lemma coreQuad_eq_zero_of_degenerate [DecidableEq F] {s₁ s₂ : ℕ → F} {N : ℕ}
    {Cs : Finset F} {a : F}
    (ha : a ∉ Cs)
    (hA₀ : syndr s₁ N 0 (insert a Cs) = 0) (hB₀ : syndr s₂ N 0 (insert a Cs) = 0)
    (hA₁ : syndr s₁ N 1 (insert a Cs) = 0) (hB₁ : syndr s₂ N 1 (insert a Cs) = 0) :
    coreQuad s₁ s₂ N Cs = 0 := by
  rw [syndr_insert s₁ N 0 ha] at hA₀
  rw [syndr_insert s₂ N 0 ha] at hB₀
  rw [syndr_insert s₁ N 1 ha] at hA₁
  rw [syndr_insert s₂ N 1 ha] at hB₁
  have hc₂ : syndr s₁ N 0 Cs * syndr s₂ N 1 Cs - syndr s₁ N 1 Cs * syndr s₂ N 0 Cs = 0 := by
    linear_combination syndr s₁ N 0 Cs * hB₀ - syndr s₂ N 0 Cs * hA₀
  have hc₁ : syndr s₁ N 2 Cs * syndr s₂ N 0 Cs - syndr s₁ N 0 Cs * syndr s₂ N 2 Cs = 0 := by
    linear_combination syndr s₂ N 0 Cs * hA₁ - syndr s₁ N 0 Cs * hB₁
      + (a * syndr s₂ N 0 Cs) * hA₀ - (a * syndr s₁ N 0 Cs) * hB₀
  have hc₀ : syndr s₁ N 1 Cs * syndr s₂ N 2 Cs - syndr s₁ N 2 Cs * syndr s₂ N 1 Cs = 0 := by
    linear_combination syndr s₂ N 2 Cs * hA₀ - syndr s₁ N 2 Cs * hB₀ - a * hc₁
  rw [coreQuad, hc₀, hc₁, hc₂]
  simp

/-- **Möbius-image well-definedness** (division-free form of 2026/858 Lemma 37): at a
core whose quadratic is nonzero, each extension point admits at most one compatible
line parameter `γ`. -/
lemma gamma_unique [DecidableEq F] {s₁ s₂ : ℕ → F} {N : ℕ} {Cs : Finset F} {a γ γ' : F}
    (ha : a ∉ Cs) (hq : coreQuad s₁ s₂ N Cs ≠ 0)
    (h : Compat s₁ s₂ N (insert a Cs) γ) (h' : Compat s₁ s₂ N (insert a Cs) γ') :
    γ = γ' := by
  by_contra hne
  have hsub : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
  have hB₀ : syndr s₂ N 0 (insert a Cs) = 0 := by
    have hzero : (γ - γ') * syndr s₂ N 0 (insert a Cs) = 0 := by
      linear_combination h.1 - h'.1
    exact (mul_eq_zero.mp hzero).resolve_left hsub
  have hB₁ : syndr s₂ N 1 (insert a Cs) = 0 := by
    have hzero : (γ - γ') * syndr s₂ N 1 (insert a Cs) = 0 := by
      linear_combination h.2 - h'.2
    exact (mul_eq_zero.mp hzero).resolve_left hsub
  have hA₀ : syndr s₁ N 0 (insert a Cs) = 0 := by
    have h1 := h.1
    rw [hB₀] at h1
    simpa using h1
  have hA₁ : syndr s₁ N 1 (insert a Cs) = 0 := by
    have h1 := h.2
    rw [hB₁] at h1
    simpa using h1
  exact hq (coreQuad_eq_zero_of_degenerate ha hA₀ hB₀ hA₁ hB₁)

section Count

variable [Fintype F] [DecidableEq F]

open Classical in
/-- The set of line parameters charged to the core `Cs`: those `γ` compatible with some
extension of a *nondegenerate* core inside the domain. -/
private noncomputable def chargeSet (s₁ s₂ : ℕ → F) (N : ℕ) (D₀ Cs : Finset F) : Finset F :=
  Finset.univ.filter
    (fun γ => coreQuad s₁ s₂ N Cs ≠ 0 ∧ ∃ a ∈ D₀ \ Cs, Compat s₁ s₂ N (insert a Cs) γ)

private lemma mem_chargeSet {s₁ s₂ : ℕ → F} {N : ℕ} {D₀ Cs : Finset F} {γ : F} :
    γ ∈ chargeSet s₁ s₂ N D₀ Cs ↔
      coreQuad s₁ s₂ N Cs ≠ 0 ∧ ∃ a ∈ D₀ \ Cs, Compat s₁ s₂ N (insert a Cs) γ := by
  simp [chargeSet]

open Classical in
/-- **The c = 2 core-elimination bound** (the `p`-independent half of 2026/858
Theorem 38, with the honest minimal proviso): if every weight-`w` support over the
domain `D₀` has at least one core with nonzero elimination quadratic, then the number
of line parameters `γ` compatible with *some* support is at most `2·C(|D₀|, w−1)`.

Counting structure: each compatible `γ` is charged to a nondegenerate core `C` of its
witness support together with the extension point `a` (a root of `coreQuad C`, of which
there are ≤ 2); `γ`-uniqueness per `(C, a)` makes the charge injective. -/
theorem c2_core_bound {s₁ s₂ : ℕ → F} {N : ℕ} {D₀ : Finset F} {w : ℕ}
    (hq : ∀ E ∈ D₀.powersetCard w, ∃ a ∈ E,
      coreQuad s₁ s₂ N (E.erase a) ≠ 0) :
    (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, Compat s₁ s₂ N E γ).card
      ≤ 2 * D₀.card.choose (w - 1) := by
  classical
  -- every compatible γ is charged to a nondegenerate core of its witness support
  have hsub : (Finset.univ.filter fun γ : F =>
      ∃ E ∈ D₀.powersetCard w, Compat s₁ s₂ N E γ)
        ⊆ (D₀.powersetCard (w - 1)).biUnion (chargeSet s₁ s₂ N D₀) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨-, E, hE, hcomp⟩ := hγ
    obtain ⟨a, haE, hqa⟩ := hq E hE
    rw [Finset.mem_powersetCard] at hE
    refine Finset.mem_biUnion.mpr ⟨E.erase a, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨(Finset.erase_subset _ _).trans hE.1,
        by rw [Finset.card_erase_of_mem haE, hE.2]⟩
    · rw [mem_chargeSet]
      refine ⟨hqa, a, ?_, ?_⟩
      · rw [Finset.mem_sdiff]
        exact ⟨hE.1 haE, Finset.notMem_erase _ _⟩
      · rwa [Finset.insert_erase haE]
  -- each core charges at most 2 parameters
  have hbound : ∀ Cs ∈ D₀.powersetCard (w - 1), (chargeSet s₁ s₂ N D₀ Cs).card ≤ 2 := by
    intro Cs _
    by_cases hq0 : coreQuad s₁ s₂ N Cs = 0
    · have hempty : chargeSet s₁ s₂ N D₀ Cs = ∅ := by
        ext γ
        rw [mem_chargeSet]
        simp [hq0]
      simp [hempty]
    · -- inject into the ≤ 2 roots of the core quadratic inside D₀
      have hXC : (D₀.filter fun a => (coreQuad s₁ s₂ N Cs).eval a = 0).card ≤ 2 := by
        calc (D₀.filter fun a => (coreQuad s₁ s₂ N Cs).eval a = 0).card
            ≤ (coreQuad s₁ s₂ N Cs).roots.toFinset.card := by
              apply Finset.card_le_card
              intro a haX
              rw [Finset.mem_filter] at haX
              rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
              exact haX.2
          _ ≤ Multiset.card (coreQuad s₁ s₂ N Cs).roots := Multiset.toFinset_card_le _
          _ ≤ (coreQuad s₁ s₂ N Cs).natDegree := Polynomial.card_roots' _
          _ ≤ 2 := coreQuad_natDegree_le s₁ s₂ N Cs
      refine le_trans (Finset.card_le_card_of_injOn
        (fun γ => if h : ∃ a ∈ D₀ \ Cs, Compat s₁ s₂ N (insert a Cs) γ
          then h.choose else 0) ?_ ?_) hXC
      · intro γ hγ
        obtain ⟨-, hex⟩ := mem_chargeSet.mp hγ
        simp only [dif_pos hex, Finset.mem_coe, Finset.mem_filter]
        obtain ⟨haD, hcomp⟩ := hex.choose_spec
        rw [Finset.mem_sdiff] at haD
        exact ⟨haD.1, coreQuad_eval_eq_zero haD.2 hcomp⟩
      · intro γ hγ γ' hγ' heq
        obtain ⟨-, hex⟩ := mem_chargeSet.mp (Finset.mem_coe.mp hγ)
        obtain ⟨-, hex'⟩ := mem_chargeSet.mp (Finset.mem_coe.mp hγ')
        simp only [] at heq
        rw [dif_pos hex, dif_pos hex'] at heq
        obtain ⟨haD, hcomp⟩ := hex.choose_spec
        obtain ⟨haD', hcomp'⟩ := hex'.choose_spec
        rw [heq] at hcomp
        exact gamma_unique (Finset.mem_sdiff.mp haD').2 hq0 hcomp hcomp'
  calc (Finset.univ.filter fun γ : F =>
      ∃ E ∈ D₀.powersetCard w, Compat s₁ s₂ N E γ).card
      ≤ ((D₀.powersetCard (w - 1)).biUnion (chargeSet s₁ s₂ N D₀)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ Cs ∈ D₀.powersetCard (w - 1), (chargeSet s₁ s₂ N D₀ Cs).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _Cs ∈ D₀.powersetCard (w - 1), 2 := Finset.sum_le_sum hbound
    _ = 2 * D₀.card.choose (w - 1) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]
        ring

omit [DecidableEq F] in
open Classical in
/-- The trivial field-size bound (the only bound surviving degenerate cores). -/
theorem c2_card_bound (s₁ s₂ : ℕ → F) (N : ℕ) (D₀ : Finset F) (w : ℕ) :
    (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, Compat s₁ s₂ N E γ).card
      ≤ Fintype.card F :=
  le_trans (Finset.card_filter_le _ _) Finset.card_univ.le

open Classical in
/-- The honest `min` form of 2026/858 Theorem 38: BOTH components hold **given** the
nondegeneracy proviso; without it only `c2_card_bound` survives. -/
theorem c2_min_bound {s₁ s₂ : ℕ → F} {N : ℕ} {D₀ : Finset F} {w : ℕ}
    (hq : ∀ E ∈ D₀.powersetCard w, ∃ a ∈ E,
      coreQuad s₁ s₂ N (E.erase a) ≠ 0) :
    (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, Compat s₁ s₂ N E γ).card
      ≤ min (Fintype.card F) (2 * D₀.card.choose (w - 1)) :=
  le_min (c2_card_bound s₁ s₂ N D₀ w) (c2_core_bound hq)

end Count

/-! ## Refutation of the literal Theorem 38 packaging: degenerate lines exist

The proviso above is not vacuous caution — the unproviso'd `min(p, 2·C(n,w−1))` claim is
**false** for adversarial lines, by the paper's own Remark-31 device upgraded to a line:
take the line spanned by two *evaluation syndromes* `s_α, s_β` with `{α, β} ⊆ E`. Both
window functionals of `Λ_E` and `X·Λ_E` are then `x^r·Λ_E(x)` evaluated at a root of
`Λ_E`, so they vanish on both endpoints of the line — every `γ ∈ F` is compatible, the
compatible-`γ` set is all of `F`, and the `2·C(n,w−1)` component fails whenever
`|F| > 2·C(n,w−1)`. (For their `M_true` the same supports contribute nothing — the
Vandermonde solution is supported on `{α, β}` only — so the refutation targets exactly
the `M_compat ≤ min(...)` claim as printed.) -/

section DegenerateLine

/-- The evaluation syndrome at `x`: `s_j = x^j`. -/
def evalSynd (x : F) : ℕ → F := fun j => x ^ j

/-- On a window past the degree, the syndrome pairing against an evaluation syndrome is
plain evaluation. -/
lemma synd_evalSynd {P : F[X]} {N : ℕ} (hdeg : P.natDegree < N) (x : F) :
    synd (evalSynd x) N P = P.eval x :=
  (Polynomial.eval_eq_sum_range' hdeg x).symm

lemma loc_natDegree_le (E : Finset F) : (loc E).natDegree ≤ E.card := by
  rw [loc]
  refine le_trans (Polynomial.natDegree_prod_le _ _) (le_of_eq ?_)
  simp

lemma loc_eval_eq_zero {E : Finset F} {x : F} (hx : x ∈ E) : (loc E).eval x = 0 := by
  rw [loc, eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

/-- **The degeneracy construction**: a support containing both endpoints of the
evaluation-syndrome line is compatible at *every* line parameter `γ`. -/
theorem compat_evalSynd_line {E : Finset F} {α β : F} {N : ℕ}
    (hα : α ∈ E) (hβ : β ∈ E) (hN : E.card + 1 < N) (γ : F) :
    Compat (evalSynd α) (evalSynd β) N E γ := by
  have hdeg : ∀ r : ℕ, r ≤ 1 → ((X : F[X]) ^ r * loc E).natDegree < N := by
    intro r hr
    have h1 : ((X : F[X]) ^ r * loc E).natDegree ≤ r + E.card := by
      refine le_trans natDegree_mul_le ?_
      have := loc_natDegree_le E
      have hx : ((X : F[X]) ^ r).natDegree ≤ r := natDegree_X_pow_le r
      omega
    omega
  have hzero : ∀ (x : F), x ∈ E → ∀ r : ℕ, r ≤ 1 →
      syndr (evalSynd x) N r E = 0 := by
    intro x hx r hr
    rw [syndr, synd_evalSynd (hdeg r hr)]
    simp [loc_eval_eq_zero hx]
  exact ⟨by rw [hzero α hα 0 (by norm_num), hzero β hβ 0 (by norm_num)]; ring,
         by rw [hzero α hα 1 le_rfl, hzero β hβ 1 le_rfl]; ring⟩

variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
open Classical in
/-- On the evaluation-syndrome line through two points of a common support, **every**
`γ ∈ F` is compatible: the compatible-parameter set is the whole field. -/
theorem degenerate_line_full {D₀ : Finset F} {w N : ℕ} {α β : F}
    (hE : ∃ E ∈ D₀.powersetCard w, α ∈ E ∧ β ∈ E) (hN : w + 1 < N) :
    (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, Compat (evalSynd α) (evalSynd β) N E γ)
      = Finset.univ := by
  obtain ⟨E, hEmem, hα, hβ⟩ := hE
  have hcard : E.card = w := (Finset.mem_powersetCard.mp hEmem).2
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact ⟨E, hEmem, compat_evalSynd_line hα hβ (by omega) γ⟩

omit [DecidableEq F] in
open Classical in
/-- **Refutation of the literal 2026/858 Theorem 38 packaging**: without the
nondegeneracy proviso, the claimed bound `M_compat ≤ min(p, 2·C(n, w−1))` FAILS on the
evaluation-syndrome line as soon as `|F| > 2·C(n, w−1)`. -/
theorem thm38_min_bound_fails {D₀ : Finset F} {w N : ℕ} {α β : F}
    (hE : ∃ E ∈ D₀.powersetCard w, α ∈ E ∧ β ∈ E) (hN : w + 1 < N)
    (hbig : 2 * D₀.card.choose (w - 1) < Fintype.card F) :
    ¬ ((Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, Compat (evalSynd α) (evalSynd β) N E γ).card
      ≤ min (Fintype.card F) (2 * D₀.card.choose (w - 1))) := by
  rw [degenerate_line_full hE hN, Finset.card_univ]
  omega

instance primeFact_C2CoreEliminationBound_1 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

open Classical in
/-- Concrete witness over `ZMod 11`: domain `{0,1,2}`, `w = 2`, support `{0,1}`,
window `N = 4` — the compatible-`γ` count is `11 > 6 = min(11, 2·C(3,1))`. -/
theorem thm38_refutation_instance :
    ¬ ((Finset.univ.filter fun γ : ZMod 11 =>
        ∃ E ∈ ({0, 1, 2} : Finset (ZMod 11)).powersetCard 2,
          Compat (evalSynd 0) (evalSynd 1) 4 E γ).card
      ≤ min (Fintype.card (ZMod 11))
          (2 * ({0, 1, 2} : Finset (ZMod 11)).card.choose (2 - 1))) := by
  have hwit : ({0, 1} : Finset (ZMod 11)) ∈
      ({0, 1, 2} : Finset (ZMod 11)).powersetCard 2 := by decide
  have h := thm38_min_bound_fails (F := ZMod 11) (D₀ := {0, 1, 2}) (w := 2) (N := 4)
    (α := 0) (β := 1)
    ⟨{0, 1}, hwit, by decide, by decide⟩ (by norm_num)
    (by rw [ZMod.card]; decide)
  convert h using 2
  congr 1
  ext γ
  simp only [Finset.mem_filter]

end DegenerateLine


end C2CoreBound
