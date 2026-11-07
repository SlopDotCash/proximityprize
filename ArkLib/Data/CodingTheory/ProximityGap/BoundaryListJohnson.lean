/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound

/-!
# B9 — the boundary regime `(1 − √ρ − η, 1 − √ρ]` admits a linear (`≤ n`) Johnson list

**Brick B9 (probe, value 8).** *Does the δ* boundary regime
`1 − √ρ − η < δ ≤ 1 − √ρ` at small gap `η ≤ √ρ − ρ` admit a deterministic
smooth-domain RS code with a poly-size list below capacity, or must all such codes have
list size growing super-polynomially in `q` at fixed rate `ρ`?*

**What the Johnson bound gives.**  The whole window sits at or below the Johnson radius
`J = 1 − √ρ`, so the classical second-moment (Johnson) list bound applies.  With agreement
`a = ⌈(1 − δ)·n⌉` and pairwise codeword agreement `≤ b = k − 1`, the Johnson cap is
`|L| ≤ n² / (a² − n·b)`.  Inside the window the denominator is only guaranteed to be `≥ n`:
`a ≥ √ρ·n` gives `a² ≥ ρ·n² = k·n`, so `a² − n·b ≥ n`, and this is attained at the right
endpoint (e.g. `n = 100`, `k = 25`, `ρ = 1/4`, `δ = 1/2 = J`, `a = 50`, `b = 24`:
`a² − n·b = 100 = n`).  Hence throughout the window the list is at most **linear**, `|L| ≤ n`,
which is polynomial (and independent of `q = |F|`).

**Correction.**  An earlier version of this docstring claimed a uniform `O(1)` cap
`1/(2√ρ·η + η²)` over the whole window.  That used the denominator bound
`a² − n·b ≥ (2√ρ·η + η²)·n²`, which holds for `δ ≤ J − η` — the opposite side of the window —
not for `J − η < δ ≤ J`.  At the endpoint above that bound would demand `a² − n·b ≥ 1100`, but
the actual value is `100`.  An `η`-dependent constant cap is available only at a fixed positive
gap *below* the window (`δ ≤ J − η`); inside the window only the linear endpoint bound is derived.

This file formalizes the load-bearing arithmetic in the exact form consumed by the
Johnson substrate (`ArkLib.JohnsonList.johnson_list_bound`), entirely over `ℕ`:

* `boundary_list_bounded_by_qindep_witness` — **the capstone (conditional).** A list `L` whose
  words each agree with `f` on `≥ a` coordinates and whose distinct words pairwise agree on
  `≤ b`, given a positive gap `a² > n·b` and a *supplied numeric witness* `M` with
  `n² ≤ M·(a² − n·b)`, has `L.card ≤ M`.  The theorem derives no particular `M`; a caller with a
  fixed relative gap `δ ≤ J − η` below the window may supply `M = ⌈1/(2√ρη + η²)⌉`.

* `boundary_list_le_linear` — the linear cap `|L| ≤ n` (set `M = n`) from an explicit margin
  `n ≤ a² − n·b`; by the computation above this margin holds throughout the window (with
  `b = k − 1` and `a ≥ √ρ·n`), including the endpoint `δ = 1 − √ρ`.

* `boundary_no_superpoly` — packages the capstone as `∃ bound, L.card ≤ bound`.  This existential
  is automatically true for every finite list (take `bound = L.card`) and by itself expresses no
  uniform or asymptotic quantifier; the content is the specific bound `M` supplied by the caller.

The deep open core of the prize lives *above* Johnson — `δ ∈ (1 − √ρ, 1 − ρ)` — where the
second-moment denominator `a² − n·b` goes negative and this argument is unavailable.  The B9
window does not reach that regime; that is why B9 is decidable on the poly side while the
(Johnson, capacity) gap remains genuinely open.
-/

open Finset

namespace ArkLib.ProximityGap.B9

/-- **B9 capstone (conditional on a supplied witness).**
A decoding list `L` is bounded by any supplied numeric witness `M` for the Johnson denominator.

Hypotheses:
* every word of `L` agrees with the received word `f` on at least `a` of the `n` coordinates;
* distinct words of `L` agree pairwise on at most `b` coordinates (`b = k − 1` for an RS code,
  by the singleton/minimum-distance bound — distinct codewords share `≤ k − 1` points);
* `hgap : n·b < a²` — the strict Johnson gap (`δ < 1 − √ρ`, or the integer-rounded endpoint);
* `hwit : n² ≤ M · (a² − n·b)` — a numeric witness `M` whose product with the gap dominates
  `n²`.  For a fixed relative gap *below* the Johnson radius (`δ ≤ 1 − √ρ − η`) one may take
  `M = ⌈1/(2√ρ·η + η²)⌉`; inside the window `(1 − √ρ − η, 1 − √ρ]` the gap is only guaranteed
  to be `≥ n`, so the generally available witness there is `M = n` (`boundary_list_le_linear`).

Conclusion: `L.card ≤ M`.  The Johnson second-moment inequality `L.card·(a² − n·b) ≤ n²` does all
the work; the witness converts it to the explicit cap.  Any `q`-independence or `O(1)` claim is
carried entirely by the caller's choice of `M`, not derived here. -/
theorem boundary_list_bounded_by_qindep_witness
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (f : ι → F) (L : Finset (ι → F)) (a b M : ℕ)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hagree : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      (Finset.univ.filter (fun x => c x = c' x)).card ≤ b)
    (hgap : Fintype.card ι * b < a ^ 2)
    (hwit : (Fintype.card ι) ^ 2 ≤ M * (a ^ 2 - Fintype.card ι * b)) :
    L.card ≤ M := by
  classical
  -- Johnson second-moment cap, divided form: L.card ≤ n² / (a² − n·b).
  have hdiv := ArkLib.JohnsonList.johnson_list_bound_div f L a b hclose hagree hgap
  -- The witness `n² ≤ M·(a² − n·b)` gives `n²/(a² − n·b) ≤ M`: divide both sides by the
  -- (positive) denominator and cancel.  `Nat.div_le_of_le_mul` does exactly this.
  have hMle : (Fintype.card ι) ^ 2 / (a ^ 2 - Fintype.card ι * b) ≤ M :=
    Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hwit)
  exact le_trans hdiv hMle

/-- **Linear cap across the window, including the endpoint `δ = 1 − √ρ`.**
Inside the window the second-moment denominator can be as small as `n` (attained at the endpoint,
e.g. `n = 100`, `k = 25`, `a = 50`, `b = 24`), so the cap is `n²/n = n` — linear, hence
polynomial.  This instantiates the capstone with `M = n` from a margin
`hmargin : n ≤ a² − n·b`; with `b = k − 1` and `a ≥ √ρ·n` (any `δ ≤ 1 − √ρ`) one has
`a² ≥ k·n`, so the margin holds. -/
theorem boundary_list_le_linear
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (f : ι → F) (L : Finset (ι → F)) (a b : ℕ)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hagree : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      (Finset.univ.filter (fun x => c x = c' x)).card ≤ b)
    (hgap : Fintype.card ι * b < a ^ 2)
    (hmargin : Fintype.card ι ≤ a ^ 2 - Fintype.card ι * b) :
    L.card ≤ Fintype.card ι := by
  classical
  refine boundary_list_bounded_by_qindep_witness f L a b (Fintype.card ι) hclose hagree hgap ?_
  -- n² = n·n ≤ n·(a² − n·b) = M·(gap) with M = n.
  calc (Fintype.card ι) ^ 2
      = Fintype.card ι * Fintype.card ι := by ring
    _ ≤ Fintype.card ι * (a ^ 2 - Fintype.card ι * b) := by
        exact Nat.mul_le_mul_left _ hmargin

/-- **B9 packaging as an existential.**  Under the Johnson gap and the supplied witness `M`,
`L.card ≤ M`, repackaged as `∃ bound, L.card ≤ bound`.  Caution: this existential is trivially
true for every finite list (`bound = L.card`) and does not by itself express a uniform-in-`q` or
asymptotic bound; it is not a refutation of super-polynomial growth.  The meaningful statement is
the capstone with a caller-supplied `M` (e.g. `M = n` from `boundary_list_le_linear`). -/
theorem boundary_no_superpoly
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (f : ι → F) (L : Finset (ι → F)) (a b M : ℕ)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hagree : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      (Finset.univ.filter (fun x => c x = c' x)).card ≤ b)
    (hgap : Fintype.card ι * b < a ^ 2)
    (hwit : (Fintype.card ι) ^ 2 ≤ M * (a ^ 2 - Fintype.card ι * b)) :
    ∃ bound : ℕ, L.card ≤ bound :=
  ⟨M, boundary_list_bounded_by_qindep_witness f L a b M hclose hagree hgap hwit⟩

end ArkLib.ProximityGap.B9

-- Axiom audit.
#print axioms ArkLib.ProximityGap.B9.boundary_list_bounded_by_qindep_witness
#print axioms ArkLib.ProximityGap.B9.boundary_list_le_linear
#print axioms ArkLib.ProximityGap.B9.boundary_no_superpoly
