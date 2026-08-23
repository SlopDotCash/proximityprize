/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionGlobalLift

/-!
# Hypothesis K1 — fiber-section coherence is free (interpolation rigidity of surface branches)

`SectionGlobalLift.section_dvd_global_of_fibers` consumes a COHERENT family of fiber sections:
`(T − C (w.eval (C y))) ∣ evalX (C y) R` for one global `w` at every centre `y ∈ S`.  The K1
question: is coherence implied rather than assumed, when the per-centre data is only a root
family `v : F → F[X]` of the fibers?

**Resolution (this file)**:

* **The naive reading is FALSE** (`coherence_from_separability_alone_false`): per-fiber
  separability ("disc ≠ 0 on S", root-separation of branches) plus agreement with a global `w`
  beyond the lifting budget does NOT force `v y = w.eval (C y)` on all of `S` — the family can
  jump to a different global branch off the agreement set.  Verified counterexample:
  `R = Y′(Y′ − 1)`, `v = 𝟙{y ≠ 0}`, `w = 0` over `ℚ`.
* **The honest large-subset versions are PROVED**:
  - `section_dvd_global_of_agreement` — agreement beyond the budget alone already fires the
    lift (the global factor `(Y′ − C w) ∣ R` exists);
  - `exists_global_section_of_local_coherence` — interpolation rigidity: if every
    `(k+1)`-subset of the family lies on SOME polynomial of `natDegree < k`, the whole family
    lies on ONE global `w` (so coherence on ALL of `S` is free given local coherence);
  - `section_dvd_global_of_local_coherence` — the rigidity composed with the lifting budget:
    local coherence + per-centre roots + `DX + deg_Y R · (k−1) < |S|` produce the global factor;
  - `exists_heavy_branch` / `section_dvd_global_of_branch_cover` — pigeonhole over the
    branches: if the root family is covered pointwise by a finite branch set `W`, some branch
    agrees with `v` on a subset of size `> |S| / |W|`; with the uniform budget
    `|W| · B < |S|` that subset beats the budget and the lift fires for that branch;
  - `section_dvd_global_offDiscriminant` — the same, packaged off the non-vanishing locus of a
    discriminant via `Match304.card_nonvanishing_gt`: `|W| · B + deg disc < |F|` suffices;
  - `coherence_of_fiber_unique_root` / `coherence_of_agreement_beyond_budget` — the doc-K1
    statement made honest: FULL coherence on `S` does hold once per-fiber root-separation is
    strengthened to per-fiber UNIQUENESS of degree-`< k` roots (the unique-decoding regime),
    and then agreement beyond the budget gives both the global factor and `v y = w.eval (C y)`
    at every `y ∈ S`;
  - `global_facts_of_local_coherence` — the full production: local coherence also delivers the
    `(hsplit, on-branch, hbr)` package at the in-tree factorization, mirroring
    `SectionGlobalLift.global_facts_of_fiber_sections` with the coherence DERIVED, not assumed.

**Build note (olean-thrash workaround)**: the ArkLib oleans are mid-rebuild this session, so
this scratch does NOT import `ArkLib.*`.  The consumed prerequisites are inlined VERBATIM
(statements and proofs unchanged, same fully-qualified names) from:
  - `ArkLib/ToMathlib/SectionGlobalLift.lean` (`eval_section_evalX`, `centre_section_dvd`,
    `section_dvd_global_of_fibers`, `eval_section_natDegree_le`,
    `branch_ne_zero_of_separable`, `exists_split_branch_of_factorization`);
  - `ArkLib/ToMathlib/MatchingGeometryProducers.lean` (`card_gt_of_compl_subset`);
  - `ArkLib/ToMathlib/DiscriminantBadSet.lean` (`Match304.card_nonvanishing_gt`).
`Bivariate.evalX` / `evalX_eq_map` come from the stable CompPoly package import.  When the
tree heals, delete the inlined Part 0 and restore
`import ArkLib.ToMathlib.SectionGlobalLift` + `import ArkLib.ToMathlib.DiscriminantBadSet`
(that variant verified green earlier as the original draft).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate
open scoped BigOperators

namespace ArkLib

/-! ## Part 0 — inlined prerequisites (verbatim from the in-tree files, see build note) -/


namespace FiberSectionCoherence

variable {F : Type} [Field F]

/-! ## Part 1 — branch separation and uniqueness of low-degree sections -/

/-- **Branch separation**: two distinct global sections agree at no more than
`natDegree (w₁ − w₂)` centres — the centre images `C y` of an agreement set are roots of the
nonzero difference `w₁ − w₂ ∈ F[X][Y]` over the integral domain `F[X]`. -/
theorem agree_card_le_of_ne {w₁ w₂ : F[X][Y]} (hne : w₁ ≠ w₂) {S : Finset F}
    (hagree : ∀ y ∈ S, w₁.eval (Polynomial.C y) = w₂.eval (Polynomial.C y)) :
    S.card ≤ (w₁ - w₂).natDegree := by
  classical
  have hd : w₁ - w₂ ≠ 0 := sub_ne_zero.mpr hne
  have hroot : ∀ y ∈ S, (Polynomial.C y : F[X]) ∈ (w₁ - w₂).roots.toFinset := by
    intro y hy
    refine Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hd, ?_⟩)
    show (w₁ - w₂).eval (Polynomial.C y) = 0
    rw [Polynomial.eval_sub, hagree y hy, sub_self]
  have hsub : S.image (fun y : F => (Polynomial.C y : F[X])) ⊆ (w₁ - w₂).roots.toFinset :=
    Finset.image_subset_iff.mpr hroot
  have h1 : S.card = (S.image (fun y : F => (Polynomial.C y : F[X]))).card :=
    (Finset.card_image_of_injOn (fun a _ b _ h => Polynomial.C_injective h)).symm
  have h2 := Finset.card_le_card hsub
  have h3 := Multiset.toFinset_card_le (w₁ - w₂).roots
  have h4 := Polynomial.card_roots' (w₁ - w₂)
  omega

/-- **Uniqueness of degree-`< k` sections through `k` centres**: two polynomials of
`natDegree < k` agreeing at `k` distinct centres coincide. -/
theorem section_eq_of_agree {k : ℕ} {w₁ w₂ : F[X][Y]}
    (h₁ : w₁.natDegree < k) (h₂ : w₂.natDegree < k) {T : Finset F} (hcard : k ≤ T.card)
    (hagree : ∀ y ∈ T, w₁.eval (Polynomial.C y) = w₂.eval (Polynomial.C y)) :
    w₁ = w₂ := by
  by_contra hne
  have hle := agree_card_le_of_ne hne hagree
  have hmax : (w₁ - w₂).natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt h₁ h₂)
  omega

/-! ## Part 2 — agreement beyond the budget fires the lift -/

/-- **Agreement beyond the budget fires the lifting lemma**: a per-centre root family that
agrees with a single `w` at more centres than `(R.eval w).natDegree` already produces the
global factor — coherence is needed only ON the agreement set. -/
theorem section_dvd_global_of_agreement {R : F[X][X][Y]} {w : F[X][Y]} {v : F → F[X]}
    {A : Finset F}
    (hfibv : ∀ y ∈ A, (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R)
    (hagree : ∀ y ∈ A, v y = w.eval (Polynomial.C y))
    (hbig : (R.eval w).natDegree < A.card) :
    (Polynomial.X - Polynomial.C w) ∣ R := by
  refine SectionGlobalLift.section_dvd_global_of_fibers (S := A) ?_ hbig
  intro y hy
  rw [← hagree y hy]
  exact hfibv y hy

/-! ## Part 3 — interpolation rigidity: local coherence glues to one global section -/

/-- **Interpolation rigidity (coherence is free given local coherence)**: if every
`(k+1)`-subset of the family `{(y, v y) : y ∈ S}` lies on SOME polynomial of `natDegree < k`,
then the WHOLE family lies on ONE global `w` of `natDegree < k`.  Proof: fix a base
`(k+1)`-subset with witness `w`; any further centre joins a `(k+1)`-subset sharing `k` base
centres with it, and uniqueness through `k` centres (`section_eq_of_agree`) identifies the two
witnesses. -/
theorem exists_global_section_of_local_coherence {k : ℕ} {S : Finset F} {v : F → F[X]}
    (hcard : k + 1 ≤ S.card)
    (hcoh : ∀ T ⊆ S, T.card = k + 1 →
      ∃ wT : F[X][Y], wT.natDegree < k ∧ ∀ y ∈ T, v y = wT.eval (Polynomial.C y)) :
    ∃ w : F[X][Y], w.natDegree < k ∧ ∀ y ∈ S, v y = w.eval (Polynomial.C y) := by
  classical
  obtain ⟨T₀, hT₀S, hT₀card⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨w, hwdeg, hwagree⟩ := hcoh T₀ hT₀S hT₀card
  refine ⟨w, hwdeg, ?_⟩
  intro y hy
  by_cases hyT : y ∈ T₀
  · exact hwagree y hyT
  · have hT₀ne : T₀.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨t, ht⟩ := hT₀ne
    have herase : (T₀.erase t).card = k := by
      rw [Finset.card_erase_of_mem ht, hT₀card]
      omega
    have hynot : y ∉ T₀.erase t := fun hc => hyT (Finset.mem_of_mem_erase hc)
    have hT'S : insert y (T₀.erase t) ⊆ S := by
      intro a ha
      rcases Finset.mem_insert.mp ha with h | h
      · exact h ▸ hy
      · exact hT₀S (Finset.mem_of_mem_erase h)
    have hT'card : (insert y (T₀.erase t)).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hynot, herase]
    obtain ⟨w', hw'deg, hw'agree⟩ := hcoh _ hT'S hT'card
    have hagree2 : ∀ y' ∈ T₀.erase t,
        w.eval (Polynomial.C y') = w'.eval (Polynomial.C y') := by
      intro y' hy'
      rw [← hwagree y' (Finset.mem_of_mem_erase hy')]
      exact hw'agree y' (Finset.mem_insert_of_mem hy')
    have hww' : w = w' := section_eq_of_agree hwdeg hw'deg herase.ge hagree2
    rw [hww']
    exact hw'agree y (Finset.mem_insert_self y _)

/-- **HEADLINE A — the lift fires from local coherence**: a per-centre root family whose
`(k+1)`-subsets are each degree-`< k` coherent, on a set beating the uniform budget
`DX + natDegree_Y R · (k − 1)`, produces one global `w` with FULL coherence on `S` AND the
global surface factor `(Y′ − C w) ∣ R`. -/
theorem section_dvd_global_of_local_coherence {R : F[X][X][Y]} {k : ℕ} {S : Finset F}
    {v : F → F[X]}
    (hfibv : ∀ y ∈ S, (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R)
    (hcard : k + 1 ≤ S.card)
    (hcoh : ∀ T ⊆ S, T.card = k + 1 →
      ∃ wT : F[X][Y], wT.natDegree < k ∧ ∀ y ∈ T, v y = wT.eval (Polynomial.C y))
    {DX : ℕ} (hcoeff : ∀ j, (R.coeff j).natDegree ≤ DX)
    (hbig : DX + R.natDegree * (k - 1) < S.card) :
    ∃ w : F[X][Y], w.natDegree < k ∧ (∀ y ∈ S, v y = w.eval (Polynomial.C y)) ∧
      (Polynomial.X - Polynomial.C w) ∣ R := by
  obtain ⟨w, hwdeg, hwagree⟩ := exists_global_section_of_local_coherence hcard hcoh
  refine ⟨w, hwdeg, hwagree, section_dvd_global_of_agreement hfibv hwagree ?_⟩
  have h1 := SectionGlobalLift.eval_section_natDegree_le (R := R) (w := w) hcoeff
  have h2 : R.natDegree * w.natDegree ≤ R.natDegree * (k - 1) :=
    Nat.mul_le_mul le_rfl (by omega)
  omega

/-! ## Part 4 — pigeonhole over the branches: the large-subset version -/

/-- **The heavy branch (pigeonhole)**: a root family covered pointwise by a finite branch set
`W` agrees with SOME single branch on a subset `A` with `|S| ≤ |W| · |A|`. -/
theorem exists_heavy_branch {S : Finset F} (hS : S.Nonempty) {v : F → F[X]}
    {W : Finset (F[X][Y])}
    (hcover : ∀ y ∈ S, ∃ w ∈ W, v y = w.eval (Polynomial.C y)) :
    ∃ w ∈ W, ∃ A ⊆ S, (∀ y ∈ A, v y = w.eval (Polynomial.C y)) ∧
      S.card ≤ W.card * A.card := by
  classical
  have hWne : W.Nonempty := by
    obtain ⟨y, hy⟩ := hS
    obtain ⟨w, hw, -⟩ := hcover y hy
    exact ⟨w, hw⟩
  obtain ⟨w, hwW, hmax⟩ := Finset.exists_max_image W
    (fun w' => (S.filter (fun y => v y = w'.eval (Polynomial.C y))).card) hWne
  refine ⟨w, hwW, S.filter (fun y => v y = w.eval (Polynomial.C y)),
    Finset.filter_subset _ _, fun y hy => (Finset.mem_filter.mp hy).2, ?_⟩
  have hsub : S ⊆ W.biUnion
      (fun w' => S.filter (fun y => v y = w'.eval (Polynomial.C y))) := by
    intro y hy
    obtain ⟨w', hw', hvw'⟩ := hcover y hy
    exact Finset.mem_biUnion.mpr ⟨w', hw', Finset.mem_filter.mpr ⟨hy, hvw'⟩⟩
  calc S.card
      ≤ (W.biUnion (fun w' => S.filter (fun y => v y = w'.eval (Polynomial.C y)))).card :=
        Finset.card_le_card hsub
    _ ≤ W.card * (S.filter (fun y => v y = w.eval (Polynomial.C y))).card :=
        Finset.card_biUnion_le_card_mul W _ _ (fun w' hw' => hmax w' hw')

/-- **HEADLINE B — the large-subset coherence, pigeonhole form**: a per-centre root family
covered by `≤ |W|` branches, with the uniform budget `|W| · B < |S|`
(`B ≥ (R.eval w).natDegree` over the branches), agrees with SOME branch `w` on a subset `A`
beyond the budget — and the lift fires there: `(Y′ − C w) ∣ R`.  This is the honest
"coherence on a large subset" of K1: full coherence on `S` is FALSE
(`coherence_from_separability_alone_false` below), but a `1/|W|` fraction is free. -/
theorem section_dvd_global_of_branch_cover {R : F[X][X][Y]} {S : Finset F}
    {v : F → F[X]} {W : Finset (F[X][Y])} {B : ℕ}
    (hfibv : ∀ y ∈ S, (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R)
    (hcover : ∀ y ∈ S, ∃ w ∈ W, v y = w.eval (Polynomial.C y))
    (hbudget : ∀ w ∈ W, (R.eval w).natDegree ≤ B)
    (hbig : W.card * B < S.card) :
    ∃ w ∈ W, ∃ A ⊆ S, (∀ y ∈ A, v y = w.eval (Polynomial.C y)) ∧ B < A.card ∧
      (Polynomial.X - Polynomial.C w) ∣ R := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w, hwW, A, hAS, hAagree, hcount⟩ := exists_heavy_branch hS hcover
  have hBA : B < A.card := by
    by_contra hle
    have hle' : A.card ≤ B := Nat.le_of_not_lt hle
    have hmul : W.card * A.card ≤ W.card * B := Nat.mul_le_mul le_rfl hle'
    omega
  exact ⟨w, hwW, A, hAS, hAagree, hBA,
    section_dvd_global_of_agreement (fun y hy => hfibv y (hAS hy)) hAagree
      (lt_of_le_of_lt (hbudget w hwW) hBA)⟩

/-- **HEADLINE C — off the discriminant locus**: the pigeonhole headline packaged with
`Match304.card_nonvanishing_gt`: per-centre roots and a branch cover off the vanishing locus
of a nonzero `disc : F[X]`, with the numeric budget `|W| · B + deg disc < |F|`, produce a
branch `w` carrying a beyond-budget coherent subset and the global factor. -/
theorem section_dvd_global_offDiscriminant [Fintype F] [DecidableEq F]
    {R : F[X][X][Y]} {v : F → F[X]} {disc : F[X]} (hdisc : disc ≠ 0)
    (hfibv : ∀ y : F, disc.eval y ≠ 0 →
      (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R)
    {W : Finset (F[X][Y])}
    (hcover : ∀ y : F, disc.eval y ≠ 0 → ∃ w ∈ W, v y = w.eval (Polynomial.C y))
    {B : ℕ} (hbudget : ∀ w ∈ W, (R.eval w).natDegree ≤ B)
    (hbig : W.card * B + disc.natDegree < Fintype.card F) :
    ∃ w ∈ W, ∃ A : Finset F, (∀ y ∈ A, disc.eval y ≠ 0) ∧
      (∀ y ∈ A, v y = w.eval (Polynomial.C y)) ∧ B < A.card ∧
      (Polynomial.X - Polynomial.C w) ∣ R := by
  have hcardS : W.card * B < (Finset.univ.filter (fun z : F => disc.eval z ≠ 0)).card :=
    Match304.card_nonvanishing_gt hdisc hbig
  obtain ⟨w, hwW, A, hAS, hAagree, hBA, hdvd⟩ := section_dvd_global_of_branch_cover
    (S := Finset.univ.filter (fun z : F => disc.eval z ≠ 0))
    (fun y hy => hfibv y (Finset.mem_filter.mp hy).2)
    (fun y hy => hcover y (Finset.mem_filter.mp hy).2)
    hbudget hcardS
  exact ⟨w, hwW, A, fun y hy => (Finset.mem_filter.mp (hAS hy)).2, hAagree, hBA, hdvd⟩

/-! ## Part 5 — the doc-K1 statement made honest: full coherence from per-fiber uniqueness -/

/-- **Coherence from per-fiber LOW-DEGREE-ROOT UNIQUENESS** (the honest strengthening of
"disc ≠ 0 on S"): once the global factor exists, the section reading `w.eval (C y)` is a root
of every fiber; if at each `y ∈ S` the fiber has at most one degree-`< k` root (the
unique-decoding regime — strictly stronger than separability, see the refutation below), the
family must coincide with the global section at EVERY centre of `S`. -/
theorem coherence_of_fiber_unique_root {R : F[X][X][Y]} {S : Finset F} {v : F → F[X]}
    {w : F[X][Y]} {k : ℕ}
    (hfibv : ∀ y ∈ S, (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R)
    (hvdeg : ∀ y ∈ S, (v y).natDegree < k)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ R)
    (hwdeg : ∀ y ∈ S, (w.eval (Polynomial.C y)).natDegree < k)
    (huniq : ∀ y ∈ S, ∀ r₁ r₂ : F[X], r₁.natDegree < k → r₂.natDegree < k →
      (Polynomial.X - Polynomial.C r₁) ∣ Bivariate.evalX (Polynomial.C y) R →
      (Polynomial.X - Polynomial.C r₂) ∣ Bivariate.evalX (Polynomial.C y) R → r₁ = r₂) :
    ∀ y ∈ S, v y = w.eval (Polynomial.C y) := by
  intro y hy
  exact huniq y hy _ _ (hvdeg y hy) (hwdeg y hy) (hfibv y hy)
    (SectionGlobalLift.centre_section_dvd y hdvdR)

/-- **The doc-K1 hypothesis, honest form**: agreement with `w` beyond the lifting budget plus
per-fiber degree-`< k` root uniqueness give BOTH the global factor and full coherence
`v y = w.eval (C y)` at every `y ∈ S`. -/
theorem coherence_of_agreement_beyond_budget {R : F[X][X][Y]} {S A : Finset F}
    {v : F → F[X]} {w : F[X][Y]} {k : ℕ} (hAS : A ⊆ S)
    (hfibv : ∀ y ∈ S, (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R)
    (hagree : ∀ y ∈ A, v y = w.eval (Polynomial.C y))
    (hbig : (R.eval w).natDegree < A.card)
    (hvdeg : ∀ y ∈ S, (v y).natDegree < k)
    (hwdeg : ∀ y ∈ S, (w.eval (Polynomial.C y)).natDegree < k)
    (huniq : ∀ y ∈ S, ∀ r₁ r₂ : F[X], r₁.natDegree < k → r₂.natDegree < k →
      (Polynomial.X - Polynomial.C r₁) ∣ Bivariate.evalX (Polynomial.C y) R →
      (Polynomial.X - Polynomial.C r₂) ∣ Bivariate.evalX (Polynomial.C y) R → r₁ = r₂) :
    (Polynomial.X - Polynomial.C w) ∣ R ∧ ∀ y ∈ S, v y = w.eval (Polynomial.C y) := by
  have hdvdR := section_dvd_global_of_agreement (fun y hy => hfibv y (hAS hy)) hagree hbig
  exact ⟨hdvdR, coherence_of_fiber_unique_root hfibv hvdeg hdvdR hwdeg huniq⟩

/-! ## Part 6 — the full production from local coherence -/

/-- **The full production from local coherence**: the rigidity headline composed with
`SectionGlobalLift.exists_split_branch_of_factorization` — local `(k+1)`-coherence of the root
family plus the budget produce the global `w`, the global factor, AND the assembler's
`(hsplit, on-branch, hbr)` package at some factor of the in-tree factorization.  Mirrors
`SectionGlobalLift.global_facts_of_fiber_sections` with the coherence DERIVED. -/
theorem global_facts_of_local_coherence {ι' : Type*} [DecidableEq ι'] {x₀ : F}
    {R : F[X][X][Y]} {s : Finset ι'} {Hf : ι' → F[X][Y]} {k : ℕ} {S : Finset F} {v : F → F[X]}
    (hQ : Bivariate.evalX (Polynomial.C x₀) R = ∏ i ∈ s, Hf i)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hfibv : ∀ y ∈ S, (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R)
    (hcard : k + 1 ≤ S.card)
    (hcoh : ∀ T ⊆ S, T.card = k + 1 →
      ∃ wT : F[X][Y], wT.natDegree < k ∧ ∀ y ∈ T, v y = wT.eval (Polynomial.C y))
    {DX : ℕ} (hcoeff : ∀ j, (R.coeff j).natDegree ≤ DX)
    (hbig : DX + R.natDegree * (k - 1) < S.card) :
    ∃ w : F[X][Y], w.natDegree < k ∧ (∀ y ∈ S, v y = w.eval (Polynomial.C y)) ∧
      (Polynomial.X - Polynomial.C w) ∣ R ∧
      ∃ i ∈ s,
        Bivariate.evalX (Polynomial.C x₀) R = Hf i * ∏ j ∈ s.erase i, Hf j ∧
        (Hf i).eval (w.eval (Polynomial.C x₀)) = 0 ∧
        (∏ j ∈ s.erase i, Hf j).eval (w.eval (Polynomial.C x₀)) ≠ 0 := by
  obtain ⟨w, hwdeg, hwagree, hdvdR⟩ :=
    section_dvd_global_of_local_coherence hfibv hcard hcoh hcoeff hbig
  exact ⟨w, hwdeg, hwagree, hdvdR,
    SectionGlobalLift.exists_split_branch_of_factorization hQ hsep hdvdR⟩

/-! ## Part 7 — the refutation of the naive reading -/

/-- **The naive K1 reading is FALSE**: per-fiber SEPARABILITY (root-separation of branches,
"disc ≠ 0 on S") plus agreement with `w` beyond the budget plus all the degree bounds do NOT
force coherence on all of `S` — the family may sit on a different global branch off the
agreement set.  Counterexample: `R = Y′(Y′ − 1)` over `ℚ` (all fibers `T(T − 1)`, separable),
`v = 𝟙{y ≠ 0}` (each value a fiber root), `w = 0`, `S = {0, 1}`, `A = {0}`,
`(R.eval 0).natDegree = 0 < 1 = |A|`, yet `v 1 = 1 ≠ 0 = w.eval (C 1)`.  This is why the
honest coherence statements above are the large-subset/pigeonhole ones, and full coherence
needs the strictly stronger per-fiber low-degree-root UNIQUENESS. -/
theorem coherence_from_separability_alone_false :
    ¬ (∀ (k : ℕ) (R : ℚ[X][X][Y]) (S A : Finset ℚ) (v : ℚ → ℚ[X]) (w : ℚ[X][Y]),
        A ⊆ S →
        (∀ y ∈ S, (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) R) →
        (∀ y ∈ S, (Bivariate.evalX (Polynomial.C y) R).Separable) →
        (∀ y ∈ S, (v y).natDegree < k) →
        w.natDegree < k →
        (∀ y ∈ A, v y = w.eval (Polynomial.C y)) →
        (R.eval w).natDegree < A.card →
        ∀ y ∈ S, v y = w.eval (Polynomial.C y)) := by
  intro h
  -- the surface `Y′(Y′ − 1)` and the branch-jumping family
  set R : ℚ[X][X][Y] := Polynomial.X * (Polynomial.X - 1) with hRdef
  set v : ℚ → ℚ[X] := fun y => if y = 0 then 0 else 1 with hvdef
  -- every fiber is `T(T − 1)`
  have hRy : ∀ y : ℚ, Bivariate.evalX (Polynomial.C y) R
      = Polynomial.X * (Polynomial.X - 1) := by
    intro y
    rw [hRdef, Bivariate.evalX_eq_map]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
  -- membership in S = {0, 1}
  have hmem : ∀ y : ℚ, y ∈ ({0, 1} : Finset ℚ) → y = 0 ∨ y = 1 := by
    intro y hy
    simpa using hy
  have h1 := h 1 R {0, 1} {0} v 0
    (by simp)
    (by
      intro y hy
      rcases hmem y hy with rfl | rfl
      · have hv0 : v 0 = 0 := by simp [hvdef]
        rw [hRy, hv0, Polynomial.C_0, sub_zero]
        exact dvd_mul_right _ _
      · have hv1 : v 1 = 1 := by simp [hvdef]
        rw [hRy, hv1, Polynomial.C_1]
        exact dvd_mul_left _ _)
    (by
      intro y hy
      rw [hRy]
      exact Polynomial.separable_X.mul
        (by simpa using Polynomial.separable_X_sub_C (x := (1 : ℚ[X])))
        ⟨1, -1, by ring⟩)
    (by
      intro y hy
      rcases hmem y hy with rfl | rfl
      · simp [hvdef]
      · simp [hvdef])
    (by simp)
    (by
      intro y hy
      have hy0 : y = 0 := by simpa using hy
      subst hy0
      simp [hvdef])
    (by
      rw [hRdef]
      simp)
    1 (by simp)
  -- the conclusion at the off-agreement centre `y = 1` is false
  have hv1 : v 1 = 1 := by simp [hvdef]
  rw [hv1, Polynomial.eval_zero] at h1
  exact one_ne_zero h1

end FiberSectionCoherence

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionGlobalLift.eval_section_evalX
#print axioms ArkLib.SectionGlobalLift.centre_section_dvd
#print axioms ArkLib.SectionGlobalLift.section_dvd_global_of_fibers
#print axioms ArkLib.SectionGlobalLift.eval_section_natDegree_le
#print axioms ArkLib.SectionGlobalLift.branch_ne_zero_of_separable
#print axioms ArkLib.SectionGlobalLift.exists_split_branch_of_factorization
#print axioms ArkLib.Match304.card_gt_of_compl_subset
#print axioms ArkLib.Match304.card_nonvanishing_gt
#print axioms ArkLib.FiberSectionCoherence.agree_card_le_of_ne
#print axioms ArkLib.FiberSectionCoherence.section_eq_of_agree
#print axioms ArkLib.FiberSectionCoherence.section_dvd_global_of_agreement
#print axioms ArkLib.FiberSectionCoherence.exists_global_section_of_local_coherence
#print axioms ArkLib.FiberSectionCoherence.section_dvd_global_of_local_coherence
#print axioms ArkLib.FiberSectionCoherence.exists_heavy_branch
#print axioms ArkLib.FiberSectionCoherence.section_dvd_global_of_branch_cover
#print axioms ArkLib.FiberSectionCoherence.section_dvd_global_offDiscriminant
#print axioms ArkLib.FiberSectionCoherence.coherence_of_fiber_unique_root
#print axioms ArkLib.FiberSectionCoherence.coherence_of_agreement_beyond_budget
#print axioms ArkLib.FiberSectionCoherence.global_facts_of_local_coherence
#print axioms ArkLib.FiberSectionCoherence.coherence_from_separability_alone_false
