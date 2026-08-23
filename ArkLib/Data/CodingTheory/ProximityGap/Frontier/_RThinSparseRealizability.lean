/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RaggedRootBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RingHomBadScalarMono

/-!
# R-thin via sparsity-realizability: the agreement polynomial is `(k+2)`-sparse (#407 — B1)

The B1 lever ("R-thin / realizability"): the far-line agreement set is realized by **one**
degree-`<k` codeword, a constraint the circulant-of-counts discards. Two facts about it are already
in-tree:

* `_RaggedRootBound.ragged_excess_le_degree` — the degree-governed backbone: the agreement set `S`
  has `|S| ≤ deg P` (the realizability *root* bound).
* `_RThinSqrtNKRefuted` — the naive raw form `|S| ≤ √(nk)` is **false** over a general field.
* `_RingHomBadScalarMono` — `N(char-p) ≤ N(char-0)` (so a char-0 bound transfers).

The genuine missing link (issue comment "the correct (isolated-point) quantity is char-free and
`n`-independent ≤ k+1, Schlickewei–Evertse / Beukers–Smyth"): the agreement polynomial is not just
degree-`b`, it is **`(k+2)`-sparse** — supported on `{0,…,k−1} ∪ {a,b}`. *Sparsity*, not degree, is
the quantity the vanishing-sums-of-roots-of-unity theory (Mann / Conway–Jones / Beukers–Smyth)
bounds. This file proves that sparsity exactly, isolates it as the entry point for the realizability
lever, and names the one open inequality that would close the additive `Θ(s)` gap.

* `agreementPoly a b γ c = X^a + γ·X^b − c` — the agreement polynomial of the monomial line
  `X^a + γ X^b` against a codeword `c` (`deg c < k`).
* `agreementPoly_support_subset` / `agreementPoly_support_card_le` — its support is
  `⊆ {a,b} ∪ range k`, hence it has at most `k + 2` nonzero terms (the sparsity).
* `SparseRaggedExcessBound` — the **named open lever**: the ragged (non-`μ_g`-coset) part of a
  `t`-sparse agreement polynomial's root set is bounded by a function of the *term count* `t` (not
  the degree). Proving it with the prize-tight constant closes R-thin; it replaces the refuted
  `√(nk)` form with the surviving char-free sparsity form.
* `rThin_charP_of_charZero` — the transfer: any char-0 ragged-excess budget on the agreement set
  transfers to char-`p` via the landed merge-only monotonicity. So the lever only needs the *char-0*
  sparse bound.

Provable content (sparsity + transfer) is axiom-clean; the sparse-excess constant is the open core,
left as an explicit `Prop` (honesty contract: named, never asserted). Issue #407.
-/

open Polynomial Finset

namespace ProximityGap.Frontier.RThinSparseRealizability

variable {F : Type*} [Field F]

/-- **The agreement polynomial** of the monomial line `X^a + γ·X^b` against a codeword `c`:
its `μ_n`-roots are exactly the points where the line agrees with `c`. For a degree-`<k` codeword
this is a `(k+2)`-sparse polynomial — the realizability constraint in algebraic form. -/
noncomputable def agreementPoly (a b : ℕ) (γ : F) (c : F[X]) : F[X] :=
  X ^ a + C γ * X ^ b - c

/-- **Sparsity (support).** The agreement polynomial is supported on `{a, b} ∪ {0,…,k−1}` whenever
the codeword has degree `< k`: every coefficient outside that set is `1 - γ·0 - 0 = 0`. -/
theorem agreementPoly_support_subset (a b k : ℕ) (γ : F) {c : F[X]} (hc : c.natDegree < k) :
    (agreementPoly a b γ c).support ⊆ insert a (insert b (Finset.range k)) := by
  intro j hj
  rw [Polynomial.mem_support_iff] at hj
  by_contra hcon
  apply hj
  simp only [Finset.mem_insert, Finset.mem_range, not_or] at hcon
  obtain ⟨hja, hjb, hjk⟩ := hcon
  have hca : (X ^ a : F[X]).coeff j = 0 := by rw [Polynomial.coeff_X_pow]; exact if_neg hja
  have hcb : (C γ * X ^ b : F[X]).coeff j = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hjb, mul_zero]
  have hcc : c.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp [agreementPoly, Polynomial.coeff_sub, Polynomial.coeff_add, hca, hcb, hcc]

/-- **Sparsity (term count).** The agreement polynomial of a degree-`<k` codeword has at most
`k + 2` nonzero terms. This is the `(k+2)`-sparsity that routes R-thin to the vanishing-sums /
Beukers–Smyth lever (a *term-count*, characteristic-free, `n`-independent quantity) — not the degree
`b`, which can be `Θ(n)`. -/
theorem agreementPoly_support_card_le (a b k : ℕ) (γ : F) {c : F[X]} (hc : c.natDegree < k) :
    (agreementPoly a b γ c).support.card ≤ k + 2 := by
  have hsub := agreementPoly_support_subset a b k γ hc
  have h1 : (agreementPoly a b γ c).support.card ≤ (insert a (insert b (Finset.range k))).card :=
    Finset.card_le_card hsub
  have h2 : (insert a (insert b (Finset.range k))).card ≤ (insert b (Finset.range k)).card + 1 :=
    Finset.card_insert_le _ _
  have h3 : (insert b (Finset.range k)).card ≤ (Finset.range k).card + 1 := Finset.card_insert_le _ _
  rw [Finset.card_range] at h3
  omega

/-! ### The open realizability lever, stated over the sparsity -/

/-- **The open R-thin lever (sparse form).** `SparseRaggedExcessBound bound` asserts that the ragged
(non-`μ_g`-coset) excess of the agreement set `S` of *any* `t`-sparse agreement polynomial is at most
`bound t` — a function of the **term count** `t`, replacing the refuted `√(nk)` (raw size) and the
provable-but-loose `deg P` (degree). The prize needs `bound (k+2) ≤` the additive-`Θ(s)` budget at
the Kambiré worst direction; this is the Hankel/realizability structure the circulant-of-counts
discards. Stated as a `Prop` — the genuine open core of B1, never asserted here. -/
def SparseRaggedExcessBound (bound : ℕ → ℕ) : Prop :=
  ∀ (a b k : ℕ) (γ : F) (c : F[X]) (S : Finset F) (cosetCore : ℕ),
    c.natDegree < k →
    (∀ x ∈ S, (agreementPoly a b γ c).IsRoot x) →
    cosetCore ≤ S.card →
    S.card - cosetCore ≤ bound ((agreementPoly a b γ c).support.card)

/-- **The provable backbone is monotone in the bound shape.** The in-tree degree bound
(`ragged_excess_le_degree`: `|S| − core ≤ deg P − core`) shows R-thin holds with `bound = deg`-shaped
data; the open lever asks to replace it by the *sparsity*-shaped `bound t`. Concretely: the agreement
set's ragged excess is bounded by `deg P − core`, and the sparse lever would sharpen this to
`bound (support.card)`. Here we record the degree backbone in the `SparseRaggedExcessBound` frame to
make the gap explicit: it holds for `bound _ = deg P`, the open part is making `bound` depend only on
the (small) term count. -/
theorem ragged_excess_realizable {a b k : ℕ} {γ : F} {c : F[X]} {S : Finset F} {cosetCore : ℕ}
    (hroots : ∀ x ∈ S, (agreementPoly a b γ c).IsRoot x) (hcore : cosetCore ≤ S.card)
    (hP : agreementPoly a b γ c ≠ 0) :
    S.card - cosetCore ≤ (agreementPoly a b γ c).natDegree - cosetCore :=
  ProximityGap.Frontier.RaggedRootBound.ragged_excess_le_degree hP hroots cosetCore hcore

/-! ### Char-`p` transfer (the landed monotonicity, in R-thin shape) -/

/-- **Char-`p` R-thin from char-0 R-thin.** Any char-0 bound on the *distinct bad-scalar count*
transfers verbatim to char-`p`, by the landed merge-only monotonicity
(`_RingHomBadScalarMono.badScalar_charP_card_le_budget`): reduction `ℤ[ζ_n] → 𝔽_q` only merges
char-0 bad scalars, never creates them. So the R-thin lever only needs to be proved in characteristic
`0` (where the vanishing-sums / sparse structure is rigid). -/
theorem rThin_charP_of_charZero {ι K S : Type*} [DecidableEq K] [DecidableEq S]
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig]
    (charZero : ι → K) (charP : ι → S) (red : K → S) {B : ℕ}
    (hfactor : ∀ t ∈ T, elig t → charP t = red (charZero t))
    (hcharZero : (T.image charZero).card ≤ B) :
    ((T.filter elig).image charP).card ≤ B :=
  ProximityGap.Frontier.RingHomBadScalarMono.badScalar_charP_card_le_budget
    T elig charZero charP red hfactor hcharZero

end ProximityGap.Frontier.RThinSparseRealizability

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.RThinSparseRealizability.agreementPoly_support_subset
#print axioms ProximityGap.Frontier.RThinSparseRealizability.agreementPoly_support_card_le
#print axioms ProximityGap.Frontier.RThinSparseRealizability.ragged_excess_realizable
#print axioms ProximityGap.Frontier.RThinSparseRealizability.rThin_charP_of_charZero
