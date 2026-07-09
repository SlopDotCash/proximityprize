/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._LambdaQSpectralMoment

/-!
# LANE (#466): THE NON-BACKTRACKING / IHARA–BASS RELABELING NO-GO (axiom-clean)

This brick converts the probe-only kill `[466-r1-nonbacktracking-relabeling]` (DISPROOF_LOG,
2026-07-01) into an in-tree machine-checked theorem: on the `n`-regular generalized Paley graph
`Cay(F_p, μ_n)` the non-backtracking (Hashimoto) spectral radius is a **deterministic,
strictly-monotone relabeling** of the adjacency spectral radius `M = max_{b≠0} |η_b|`, hence
carries **zero new information** beyond the `E_r` / spectral-moment wall.

## The set-up (matches `_LambdaQSpectralMoment.lean`)
The adjacency operator of `Cay(F_p, μ_n)` is a real symmetric circulant whose eigenvalue family is
exactly the character sums `η_b = Σ_{x∈μ_n} e_p(b·x)` (there `η : ι → ℝ`, `ι = F_p`); the prize
floor is `M = ‖η‖_{∞,non-principal} = max_{b≠0} |η_b|`.

## Ihara–Bass on a `d`-regular graph
For a `d`-regular graph the non-trivial spectrum of the non-backtracking operator `B` is, by the
Ihara–Bass determinant identity, the multiset of roots of the per-eigenvalue quadratics
`x² − η_b·x + (d−1)`, one quadratic for each adjacency eigenvalue `η_b`, together with the trivial
`±1` band. Writing `d₀ = d − 1 = n − 1`, the dominant-modulus root of `x² − η·x + d₀` at an
adjacency eigenvalue with `|η| > 2√d₀` (the non-Ramanujan / expander-relevant range) is
`nbLambda d₀ η = (η + √(η² − 4·d₀)) / 2` on the `η ≥ 0` branch.

## What is proven here (all axiom-clean)
* `nbLambda_is_root` : `(nbLambda d₀ η)² − η·(nbLambda d₀ η) + d₀ = 0` when `4·d₀ ≤ η²`
  (the Ihara–Bass factorization content: `nbLambda` really is a root of the per-eigenvalue
  quadratic).
* `nbLambda_prod` : `(nbLambda d₀ η) · (η − nbLambda d₀ η) = d₀` (Vieta product of the two roots).
* `nbLambda_ge_minor` : on `2√d₀ ≤ η` the `+` root `nbLambda d₀ η` dominates its Vieta partner —
  certifying in-code that `nbLambda` selects the DOMINANT root (so its use as the NB spectral-radius
  ingredient is justified, not just asserted).
* `nbLambda_strictMonoOn` : `nbLambda d₀` is STRICTLY INCREASING in `η` on `{η | 2·√d₀ ≤ η}`
  (for `0 < d₀`). Hence the map `η ↦ nbLambda d₀ η` is injective and order-preserving there.
* `nbLambdaMod d₀ η := nbLambda d₀ |η|` : the MODULUS of the dominant NB root, valid for `η` of
  EITHER sign (for `η < 0` the dominant root is `(η − √(η²−4d₀))/2`, modulus `nbLambda d₀ |η|`).
  `nbLambdaMod_is_root` / `nbLambdaMod_le_iff` port the root and strict-monotonicity facts to `|η|`.
  This is the correction to the naive positive-branch reading: the Paley adjacency spectrum has
  `∑ η_b = 0`, so `M = max_b |η_b|` may be attained at a NEGATIVE eigenvalue.
* `nb_argmax_eq_adj_argmax` : over any finite family `η : ι → ℝ`, all in the non-Ramanujan range
  `2·√d₀ ≤ |η b|`, the index maximizing `nbLambdaMod d₀ (η b)` is exactly the index maximizing
  `|η b|`. (A convenience form under the all-non-Ramanujan hypothesis.)
* `nbRootMod d₀ η := max (nbLambda d₀ |η|) √d₀` : the TRUE piecewise NB dominant-root modulus,
  correct in BOTH bands (`√d₀` in the Ramanujan band, the real dominant root above threshold).
  `nbRootMod_mono` : monotone in `|η|` on ALL of `ℝ` with NO range hypothesis.
* `nb_specRadius_relabel_general` : **the applicable no-go.** For an ARBITRARY family (any number
  of sub-threshold frequencies allowed), assuming only that the worst frequency `i` is above
  threshold `2√d₀ ≤ |η i|`, the index `i` also maximizes the true NB modulus `nbRootMod d₀ (η b)`,
  and the NB spectral radius equals `nbLambda d₀ M` with `M = max_b |η b| = |η i|`. The
  non-backtracking spectral radius is thus the fixed strictly-monotone relabel `nbLambda d₀` of the
  prize floor `M` — no new information — for the real Paley spectrum (sub-threshold eigenvalues and
  either sign of the worst frequency included).

## The no-go conclusion (informal, honest)
Because `nbLambda d₀` is a fixed strictly-increasing function on the expander range, ANY upper
bound `nbLambda d₀ M ≤ W'` the non-backtracking route could certify is EQUIVALENT (by applying the
inverse relabeling) to a bound `M ≤ nbLambda d₀ ⁻¹ W'` on the adjacency spectral radius — i.e. on
the exact prize object `M` governed by the spectral-moment / `E_r` wall of
`_LambdaQSpectralMoment.lean`. The non-backtracking / Ihara–Bass preprocessing carries no new
information and cannot beat `√q`. This does NOT touch the wall; it closes the "spectral
preprocessing" branch as a genuine, machine-checked no-go. Issue #466. Axiom-clean
(`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Real

namespace ArkLib.ProximityGap.Frontier.NonBacktrackingRelabelingNoGo

/-- The dominant-modulus non-backtracking (Ihara–Bass) eigenvalue attached to an adjacency
eigenvalue `η` on an `n`-regular graph, with `d₀ = n − 1`.

**Scope (important).** This closed form equals the larger real root of `x² − η·x + d₀` ONLY on the
non-Ramanujan / expander branch `η ≥ 0`, `4·d₀ ≤ η²` (equivalently `2√d₀ ≤ η`). In the Ramanujan
band `|η| < 2√d₀` the two NB roots are a complex-conjugate pair of modulus `√d₀`, and this
formula does NOT compute that modulus (`Real.sqrt` of the negative discriminant clamps to `0`, so
it returns `η/2`). Every lemma and no-go below carries an explicit `4·d₀ ≤ η²` / `2√d₀ ≤ |η|`
hypothesis, so `nbLambda` is only ever consumed on the branch where it is the genuine dominant
root — which is exactly the regime the prize lives in (the worst frequency `M = max_b |η_b|` of a
non-trivial family is `> 2√d₀`; sub-threshold frequencies never attain the spectral radius). -/
noncomputable def nbLambda (d₀ η : ℝ) : ℝ := (η + Real.sqrt (η ^ 2 - 4 * d₀)) / 2

/-- **Ihara–Bass factorization content.** For `4·d₀ ≤ η²`, `nbLambda d₀ η` is a genuine root of the
per-eigenvalue quadratic `x² − η·x + d₀`. This is the exact algebraic statement of the
non-backtracking spectrum being `{roots of x² − η_b·x + (n−1)}` on a regular graph. -/
theorem nbLambda_is_root {d₀ η : ℝ} (h : 4 * d₀ ≤ η ^ 2) :
    (nbLambda d₀ η) ^ 2 - η * (nbLambda d₀ η) + d₀ = 0 := by
  have hnn : (0 : ℝ) ≤ η ^ 2 - 4 * d₀ := by linarith
  have hsq : Real.sqrt (η ^ 2 - 4 * d₀) ^ 2 = η ^ 2 - 4 * d₀ := Real.sq_sqrt hnn
  unfold nbLambda
  field_simp
  nlinarith [hsq]

/-- **Vieta product.** The two roots `nbLambda d₀ η` and `η − nbLambda d₀ η` of the quadratic
`x² − η·x + d₀` multiply to `d₀` (`= n − 1`). In particular their product is fixed independent of
`η`, so a single dominant root determines the pair — the Chebyshev normal form
`λ₊ = √d₀·(cosh θ + sinh θ)`, `η = 2√d₀·cosh θ`. -/
theorem nbLambda_prod {d₀ η : ℝ} (h : 4 * d₀ ≤ η ^ 2) :
    (nbLambda d₀ η) * (η - nbLambda d₀ η) = d₀ := by
  have := nbLambda_is_root h
  nlinarith [this]

/-- **`nbLambda` is the DOMINANT root on the non-Ramanujan branch.** For `0 ≤ d₀` and `2√d₀ ≤ η`
(so `4·d₀ ≤ η²`), `nbLambda d₀ η` (the `+` root) is `≥` its Vieta partner `η − nbLambda d₀ η` (the
`−` root). This certifies in-code the docstring claim that `nbLambda` picks the dominant real root
(and hence, via `nbLambda_prod`, the one of larger modulus since both roots are `≥ 0` here). -/
theorem nbLambda_ge_minor {d₀ η : ℝ} (hd : 0 ≤ d₀) (h : 2 * Real.sqrt d₀ ≤ η) :
    η - nbLambda d₀ η ≤ nbLambda d₀ η := by
  have hdisc : (0 : ℝ) ≤ η ^ 2 - 4 * d₀ := by
    have hsd : (0 : ℝ) ≤ Real.sqrt d₀ := Real.sqrt_nonneg d₀
    have hsdsq : Real.sqrt d₀ ^ 2 = d₀ := Real.sq_sqrt hd
    nlinarith [h, hsd, hsdsq]
  have hpos : (0 : ℝ) ≤ Real.sqrt (η ^ 2 - 4 * d₀) := Real.sqrt_nonneg _
  unfold nbLambda
  linarith

/-- **Strict monotonicity on the expander range.** For `0 < d₀`, the dominant non-backtracking
eigenvalue `nbLambda d₀` is strictly increasing in the adjacency eigenvalue `η` on
`{η | 2·√d₀ ≤ η}`. This is the heart of the relabeling no-go: `η ↦ nbLambda d₀ η` is injective and
order-preserving on the range where the graph is non-Ramanujan. -/
theorem nbLambda_strictMonoOn {d₀ : ℝ} (hd : 0 < d₀) :
    StrictMonoOn (nbLambda d₀) {η : ℝ | 2 * Real.sqrt d₀ ≤ η} := by
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  -- `2√d₀ ≤ a` gives `4 d₀ ≤ a²`; likewise for `b`.
  have hsd : (0 : ℝ) ≤ Real.sqrt d₀ := Real.sqrt_nonneg d₀
  have hsdsq : Real.sqrt d₀ ^ 2 = d₀ := Real.sq_sqrt hd.le
  have ha4 : 4 * d₀ ≤ a ^ 2 := by nlinarith [ha, hsd, hsdsq]
  have hb4 : 4 * d₀ ≤ b ^ 2 := by nlinarith [hb, hsd, hsdsq]
  have hann : (0 : ℝ) ≤ a ^ 2 - 4 * d₀ := by linarith
  have hbnn : (0 : ℝ) ≤ b ^ 2 - 4 * d₀ := by linarith
  -- both `a, b > 0`
  have hapos : 0 < a := by nlinarith [ha, hsd]
  -- The square-root term is monotone: `a < b ⟹ a² < b² ⟹ a²-4d₀ < b²-4d₀`.
  have hab2 : a ^ 2 - 4 * d₀ < b ^ 2 - 4 * d₀ := by nlinarith [hab, hapos]
  have hsqrt : Real.sqrt (a ^ 2 - 4 * d₀) < Real.sqrt (b ^ 2 - 4 * d₀) :=
    Real.sqrt_lt_sqrt hann hab2
  unfold nbLambda
  have : a + Real.sqrt (a ^ 2 - 4 * d₀) < b + Real.sqrt (b ^ 2 - 4 * d₀) := by linarith
  linarith

/-- Monotone-image auxiliary: on the expander range, `η a ≤ η b ↔ nbLambda d₀ (η a) ≤
nbLambda d₀ (η b)`. Directly packages the strict-mono relabeling for the argmax argument. -/
theorem nbLambda_le_iff {d₀ : ℝ} (hd : 0 < d₀) {x y : ℝ}
    (hx : 2 * Real.sqrt d₀ ≤ x) (hy : 2 * Real.sqrt d₀ ≤ y) :
    nbLambda d₀ x ≤ nbLambda d₀ y ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have := nbLambda_strictMonoOn hd (Set.mem_setOf_eq ▸ hy) (Set.mem_setOf_eq ▸ hx) hlt
    linarith
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact (nbLambda_strictMonoOn hd (Set.mem_setOf_eq ▸ hx) (Set.mem_setOf_eq ▸ hy) hlt).le
    · rw [heq]

/-- **The dominant NB eigenvalue MODULUS** on the non-Ramanujan branch, valid for adjacency
eigenvalues of EITHER sign. For `η < 0` (with `4·d₀ ≤ η²`) the dominant root of `x² − η·x + d₀` is
`(η − √(η²−4d₀))/2`, whose modulus is `(|η| + √(η²−4d₀))/2 = nbLambda d₀ |η|`. So on the
non-Ramanujan range `2√d₀ ≤ |η|` the modulus of the dominant NB root is always `nbLambda d₀ |η|`.

**Scope (important).** Like `nbLambda`, this equals the true dominant-root modulus ONLY for
`2√d₀ ≤ |η|`; in the Ramanujan band `|η| < 2√d₀` the roots are complex with modulus `√d₀` and
this formula returns `|η|/2 ≠ √d₀`. Every consumer (`nbLambdaMod_le_iff`, the two no-go theorems)
carries `2√d₀ ≤ |η b|` on the whole family, so `nbLambdaMod` is only used where it IS the true
modulus. This is the object the SPECTRAL RADIUS (a max of moduli, attained at the worst frequency
`> 2√d₀`) is built from — correcting the naive positive-branch-only reading: the Paley adjacency
spectrum has `∑ η_b = 0`, so the worst frequency `M = max_b |η_b|` can be a NEGATIVE eigenvalue. -/
noncomputable def nbLambdaMod (d₀ η : ℝ) : ℝ := nbLambda d₀ |η|

/-- The NB modulus is a genuine root modulus: `nbLambdaMod d₀ η = nbLambda d₀ |η|`, and it is a root
of `x² − |η|·x + d₀` (the quadratic attached to the eigenvalue-modulus). Since `x² − η x + d₀` and
`x² + η x + d₀` have root sets negatives of each other, the DOMINANT-MODULUS root of the
`η`-quadratic has modulus `nbLambda d₀ |η|` for both signs of `η`. -/
theorem nbLambdaMod_is_root {d₀ η : ℝ} (h : 4 * d₀ ≤ η ^ 2) :
    (nbLambdaMod d₀ η) ^ 2 - |η| * (nbLambdaMod d₀ η) + d₀ = 0 := by
  have habs : |η| ^ 2 = η ^ 2 := sq_abs η
  have h' : 4 * d₀ ≤ |η| ^ 2 := by rw [habs]; exact h
  simpa only [nbLambdaMod] using nbLambda_is_root h'

/-- **Modulus strict monotonicity.** `nbLambdaMod d₀` is strictly increasing in `|η|` on the
non-Ramanujan range `2√d₀ ≤ |η|`. This is the sign-robust form of `nbLambda_strictMonoOn`: the NB
dominant-root modulus is a strictly increasing function of the adjacency-eigenvalue modulus. -/
theorem nbLambdaMod_le_iff {d₀ : ℝ} (hd : 0 < d₀) {x y : ℝ}
    (hx : 2 * Real.sqrt d₀ ≤ |x|) (hy : 2 * Real.sqrt d₀ ≤ |y|) :
    nbLambdaMod d₀ x ≤ nbLambdaMod d₀ y ↔ |x| ≤ |y| := by
  simpa only [nbLambdaMod] using nbLambda_le_iff hd hx hy

/-- **The TRUE non-backtracking dominant-root modulus, piecewise over both bands.** This is the
genuine modulus of the dominant Ihara–Bass root for `x² − η·x + d₀`, correct EVERYWHERE:
* non-Ramanujan `|η| ≥ 2√d₀` : two real roots, dominant modulus `nbLambda d₀ |η| ≥ √d₀`;
* Ramanujan `|η| < 2√d₀`     : complex-conjugate roots of modulus `√d₀` (and there
  `nbLambda d₀ |η| = |η|/2 < √d₀`).
Taking the `max` with `√d₀` yields the correct value in BOTH bands with a single closed form,
removing the `nbLambdaMod` scope caveat. This is the object the NB SPECTRAL RADIUS is a max of. -/
noncomputable def nbRootMod (d₀ η : ℝ) : ℝ := max (nbLambda d₀ |η|) (Real.sqrt d₀)

/-- On the non-Ramanujan branch `2√d₀ ≤ |η|`, the piecewise modulus agrees with the real dominant
root: `nbRootMod d₀ η = nbLambda d₀ |η|` (because there `nbLambda d₀ |η| ≥ √d₀`). -/
theorem nbRootMod_eq_of_ge {d₀ η : ℝ} (hd : 0 ≤ d₀) (h : 2 * Real.sqrt d₀ ≤ |η|) :
    nbRootMod d₀ η = nbLambda d₀ |η| := by
  have hsd : (0 : ℝ) ≤ Real.sqrt d₀ := Real.sqrt_nonneg d₀
  have hsdsq : Real.sqrt d₀ ^ 2 = d₀ := Real.sq_sqrt hd
  have hdisc : (0 : ℝ) ≤ |η| ^ 2 - 4 * d₀ := by nlinarith [h, hsd, hsdsq]
  have hge : Real.sqrt d₀ ≤ nbLambda d₀ |η| := by
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (|η| ^ 2 - 4 * d₀) := Real.sqrt_nonneg _
    unfold nbLambda
    -- 2√d₀ ≤ |η| ≤ |η| + √(η²-4d₀), so √d₀ ≤ (|η| + √…)/2
    linarith
  simp only [nbRootMod, max_eq_left hge]

/-- **`nbRootMod` is monotone in `|η|` on ALL of `ℝ` (both bands).** As a `max` of the nondecreasing
`|η| ↦ nbLambda d₀ |η|` (nondecreasing because `√` is monotone) and the constant `√d₀`, the true NB
modulus is monotone nondecreasing in the adjacency modulus everywhere. No range hypothesis. -/
theorem nbRootMod_mono {d₀ : ℝ} {x y : ℝ} (h : |x| ≤ |y|) :
    nbRootMod d₀ x ≤ nbRootMod d₀ y := by
  have hnb : nbLambda d₀ |x| ≤ nbLambda d₀ |y| := by
    unfold nbLambda
    have hsq : Real.sqrt (|x| ^ 2 - 4 * d₀) ≤ Real.sqrt (|y| ^ 2 - 4 * d₀) := by
      apply Real.sqrt_le_sqrt
      have : |x| ^ 2 ≤ |y| ^ 2 := by nlinarith [abs_nonneg x, abs_nonneg y, h]
      linarith
    linarith
  exact max_le_max hnb le_rfl

variable {ι : Type*}

/-- **The relabeling no-go (spectral-radius form, GENERAL family — no per-frequency range needed).**
This is the fully honest, applicable form demanded by Codex-review: the family `η : ι → ℝ` is
ARBITRARY — it may contain any number of sub-threshold (Ramanujan-band) eigenvalues. We use the
true piecewise NB modulus `nbRootMod`. The only hypothesis is the natural one: the worst
frequency `i` (`|η i|` maximal) is itself above threshold, `2√d₀ ≤ |η i|` — which holds in the
prize / non-Ramanujan regime where the graph is a non-trivial expander.

Conclusion: (1) `i` also maximizes the NB dominant-root modulus `nbRootMod d₀ (η b)` over the whole
family; and (2) that NB spectral radius equals `nbLambda d₀ M`, `M = |η i| = max_b |η b|`. So the
NB spectral radius is the fixed strictly-monotone relabel `nbLambda d₀` of the prize floor `M`,
carrying no information beyond `M` — no matter how many sub-threshold frequencies the spectrum has,
and whatever the sign of the worst frequency. Closes the `nonbacktracking-relabeling` branch. -/
theorem nb_specRadius_relabel_general {d₀ : ℝ} (hd : 0 < d₀)
    (η : ι → ℝ) (i : ι) (hi : 2 * Real.sqrt d₀ ≤ |η i|)
    (hM : ∀ b, |η b| ≤ |η i|) :
    ((∀ b, nbRootMod d₀ (η b) ≤ nbRootMod d₀ (η i))
      ∧ nbRootMod d₀ (η i) = nbLambda d₀ (|η i|)) := by
  refine ⟨fun b => nbRootMod_mono (hM b), ?_⟩
  exact nbRootMod_eq_of_ge hd.le hi

/-- **The relabeling no-go (argmax form, modulus-correct).** For an adjacency eigenvalue family
`η : ι → ℝ` whose every frequency is in the non-Ramanujan range `2·√d₀ ≤ |η b|`, the index
maximizing the non-backtracking eigenvalue MODULUS `nbLambdaMod d₀ (η b)` is exactly the index
maximizing the adjacency eigenvalue modulus `|η b|`.

This is the honest form Codex-review demanded: it works with `|η_b|` (moduli), so it does not
assume the maximal modulus lies on the positive branch — the worst frequency of the Paley spectrum
(`∑ η_b = 0`) may be a negative eigenvalue. The non-backtracking / Ihara–Bass preprocessing
produces no new extremal index and no new information: any bound it certifies on the NB spectral
radius is equivalent (via the fixed order-isomorphism `nbLambdaMod d₀ = nbLambda d₀ ∘ |·|`) to the
same bound on `M = max_b |η b|`, i.e. on the `E_r` / spectral-moment wall. -/
theorem nb_argmax_eq_adj_argmax {d₀ : ℝ} (hd : 0 < d₀)
    (η : ι → ℝ) (hrange : ∀ b, 2 * Real.sqrt d₀ ≤ |η b|) (i : ι) :
    (∀ b, nbLambdaMod d₀ (η b) ≤ nbLambdaMod d₀ (η i)) ↔ (∀ b, |η b| ≤ |η i|) := by
  constructor
  · intro h b
    exact (nbLambdaMod_le_iff hd (hrange b) (hrange i)).1 (h b)
  · intro h b
    exact (nbLambdaMod_le_iff hd (hrange b) (hrange i)).2 (h b)

/-- **The relabeling no-go (spectral-radius form, modulus-correct).** Let `M = |η i|` be the
adjacency spectral radius (`|η i|` maximal on the non-Ramanujan-ranged family). Then
`nbLambdaMod d₀ (η i) = nbLambda d₀ M` is the non-backtracking spectral radius, and it is maximal
among `nbLambdaMod d₀ (η b)`. The non-backtracking spectral radius is thus exactly the strictly-
monotone relabel `nbLambda d₀` of the prize floor `M = max_b |η b|` — a deterministic order-
isomorphism image, carrying no information beyond `M`, whatever the sign of the worst frequency. -/
theorem nb_specRadius_eq_relabel_of_M {d₀ : ℝ} (hd : 0 < d₀)
    (η : ι → ℝ) (hrange : ∀ b, 2 * Real.sqrt d₀ ≤ |η b|) (i : ι)
    (hM : ∀ b, |η b| ≤ |η i|) :
    ((∀ b, nbLambdaMod d₀ (η b) ≤ nbLambdaMod d₀ (η i))
      ∧ nbLambdaMod d₀ (η i) = nbLambda d₀ (|η i|)) := by
  refine ⟨fun b => (nbLambdaMod_le_iff hd (hrange b) (hrange i)).2 (hM b), ?_⟩
  rfl

end ArkLib.ProximityGap.Frontier.NonBacktrackingRelabelingNoGo
