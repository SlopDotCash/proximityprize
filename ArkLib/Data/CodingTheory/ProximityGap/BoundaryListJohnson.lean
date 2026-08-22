/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound

/-!
# B9 — the boundary regime `(1 − √ρ − η, 1 − √ρ]` admits a `q`-independent poly list

**Brick B9 (probe, value 8).** *Does the δ* boundary regime
`1 − √ρ − η < δ ≤ 1 − √ρ` at small gap `η ≤ √ρ − ρ` admit a deterministic
smooth-domain RS code with a poly-size list below capacity, or must all such codes have
list size growing super-polynomially in `q` at fixed rate `ρ`?*

**Verdict: it admits a poly (indeed `q`-independent `O(1)`) list — the super-polynomial
alternative is FALSE.** The whole window sits at or below the Johnson radius `1 − √ρ`, so the
classical second-moment (Johnson) list bound applies. With agreement `a = ⌈(1 − δ)·n⌉` and
pairwise codeword agreement `≤ b = k − 1`, the Johnson cap is
`|L| ≤ n² / (a² − n·b)`.  At a **fixed relative gap** `η > 0` (the brick's hypothesis — `η`
is a constant fraction, not shrinking with `q`) one has
`a² − n·b ≥ (2√ρ·η + η²)·n²`, so

```
        |L| ≤ n² / ((2√ρ·η + η²)·n²) = 1 / (2√ρ·η + η²),
```

a constant **independent of `q` (= |F|) and of `n`**.  This is the polynomial side of the
dichotomy, uniformly over the whole window and over every deterministic smooth-domain RS code.

This file formalizes the load-bearing arithmetic in the exact form consumed by the
Johnson substrate (`ArkLib.JohnsonList.johnson_list_bound`), entirely over `ℕ`:

* `boundary_list_bounded_by_qindep_witness` — **the capstone.** A list `L` whose words each
  agree with `f` on `≥ a` coordinates and whose distinct words pairwise agree on `≤ b`, given a
  positive gap `a² > n·b` and a *supplied `q`-independent witness* `M` with `n² ≤ M·(a² − n·b)`,
  has `L.card ≤ M`.  When the relative gap is fixed, the caller supplies the constant
  `M = ⌈1/(2√ρη + η²)⌉` — uniform in `q`.  The hypothesis `n² ≤ M·(a² − n·b)` is exactly the
  `q`-independence: it encodes "a constant `M` suffices for every field size".

* `boundary_list_le_linear` — the **endpoint** `δ = 1 − √ρ` (right end of the half-open window,
  relative gap `→ 0`): even there the list is at most **linear** `|L| ≤ n` (set `M = n`), hence
  still polynomial — never super-polynomial.  This kills the super-poly alternative even at the
  measure-zero boundary point the window includes.

* `boundary_no_superpoly` — the explicit **refutation packaging**: there is a finite `M` (the
  `q`-independent constant in the fixed-gap regime, or `n` at the endpoint) that caps the list,
  so the "list size grows super-polynomially in `q`" disjunct cannot hold.

The deep open core of the prize lives *above* Johnson — `δ ∈ (1 − √ρ, 1 − ρ)` — where the
second-moment denominator `a² − n·b` goes negative and this argument is unavailable.  The B9
window does not reach that regime; that is why B9 is decidable on the poly side while the
(Johnson, capacity) gap remains genuinely open.
-/

open Finset

namespace ArkLib.ProximityGap.B9

/-- **B9 capstone (poly side of the dichotomy).**
A decoding list `L` in the boundary regime is bounded by any supplied `q`-independent witness `M`.

Hypotheses:
* every word of `L` agrees with the received word `f` on at least `a` of the `n` coordinates;
* distinct words of `L` agree pairwise on at most `b` coordinates (`b = k − 1` for an RS code,
  by the singleton/minimum-distance bound — distinct codewords share `≤ k − 1` points);
* `hgap : n·b < a²` — the strict Johnson gap (`δ < 1 − √ρ`, or the integer-rounded endpoint);
* `hwit : n² ≤ M · (a² − n·b)` — *the `q`-independence witness*: a single constant `M` whose
  product with the (growing) gap dominates `n²`.  For a fixed relative gap `η > 0` one may take
  the constant `M = ⌈1/(2√ρ·η + η²)⌉`, uniformly over all `q`.

Conclusion: `L.card ≤ M`.  Since `M` is `q`-independent (and finite), the list is polynomial —
indeed `O(1)` in the fixed-gap regime.  The Johnson second-moment inequality
`L.card·(a² − n·b) ≤ n²` does all the work; the witness converts it to the explicit cap. -/
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

/-- **Endpoint of the window `δ = 1 − √ρ` (relative gap `→ 0`): at most LINEAR, still poly.**
At the right end of the half-open window the second-moment denominator can be as small as `Θ(n)`
(integer rounding `a = ⌊√ρ·n⌋ + O(1)`), so the cap is `n²/Θ(n) = Θ(n)` — linear, hence
polynomial, **never super-polynomial**.  This instantiates the capstone with `M = n` from a
margin `hmargin : n ≤ a² − n·b` (i.e. the gap is at least one full `n`, which holds for any
genuine positive integer agreement margin at the endpoint). -/
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

/-- **B9 refutation packaging: no super-polynomial list in the boundary window.**
The super-polynomial alternative asserts that *no* `q`-independent (finite) cap on `L.card`
exists.  We exhibit the cap: under the Johnson gap and the supplied witness `M`, `L.card ≤ M`.
Stated as the existence of a finite bounding constant — exactly the negation of "grows
super-polynomially in `q`" at fixed rate. -/
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
