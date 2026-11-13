/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

/-!
# ANGLE capacity-side-prime: the prime-`n` capacity collapse on the REAL far-line object (#407)

THE REAL OBJECT (verified reframing, issue #407 comment 4704445593).  The deployed far-line
incidence reduces to a SPARSE-FUNCTION ZERO COUNT.  Far-line agreement of `x^a + γ x^b` with a
degree-`< k` codeword `c` on a set `S ⊆ μ_n` says the polynomial

  `g(x) = x^a + γ x^b − c(x)`   (`deg c < k`)

vanishes on `S`.  As a function on `μ_n ≅ Z_n`, `g` has discrete-Fourier support contained in
`{0,…,k-1} ∪ {a,b}` (size `≤ k+2`, since the far directions have `a,b ∉ {0,…,k-1}`).  Hence

  `s* = max #zeros of g on μ_n = n − (min physical support of a nonzero (k+2)-Fourier-sparse fn)`.

THE CAPACITY (PRIME) SIDE — what this file pins.  For PRIME `n`, Tao's uncertainty principle is
*sharp* and CONSTANT in `n`, so the far line lands exactly at capacity:

  **Tao (2005)** — *An uncertainty principle for cyclic groups of prime order*, Math. Res. Lett.
  12(1):121–127.  For `p` prime and `f : Z/p → ℂ` (or any field) nonzero,
  `|supp f| + |supp f̂| ≥ p + 1`.  Equivalently (the corollary we consume): a nonzero function on
  `Z_p` whose discrete-Fourier transform is supported on a set of size `≤ t` has `≤ t − 1` zeros.
  Hence with `t = k + 2` a far line agrees with any codeword on `≤ k + 1` points:
  `s* ≤ k + 1`, CONSTANT in `n`, so `δ* = 1 − (k+1)/n → 1 − ρ` (CAPACITY).

This file does the part the abstract `ZMod`-bookkeeping does NOT: it states Tao's corollary as a
named `Prop` *about the genuine `rsCode` agreement object*, applied to the explicit far-line
polynomial `g`, and derives that the **real** agreement `Finset.card ≤ k + 1`, then promotes it to
the **real** `FarFromCode` radius (`FarCosetExplosion.FarFromCode`).  No `c := 0` / `c := 999999`
placeholder: every statement is over `rsCode dom k`, an actual `Polynomial F`, and the literal
agreement set.

WHY THIS IS THE EASY HALF (and why `2^μ` lacks it).  Tao's proof uses that for prime `p` *every*
square submatrix of the DFT matrix is invertible (Chebotarev–Stark nonvanishing of cyclotomic
minors).  This is FALSE for composite `n`: a proper subgroup `H ≤ Z_{2^μ}` has an indicator with
small physical support `|H|` and small Fourier support `n/|H|` (the dual subgroup) — a sparse
function with FEW zeros' complement, collapsing `minSupport`.  That collapse is exactly the gap that
lets `s*` grow to `√(kn)` (Johnson).  So Tao gives capacity for prime `n` and **NOTHING** below
Johnson for `n = 2^μ`; the contrast is the whole content of the #407 dichotomy.

EXACT NUMERICAL CONFIRMATION (`/tmp/up_capacity_tiny.py`, exact rank over `F_p`, `p ≡ 1 mod n`):
the minimal physical support `minSupp(t)` of a nonzero `t`-Fourier-sparse function on `Z_n` is
`= n + 1 − t` for PRIME `n = 5, 7` (matching Tao at EVERY `t`), so `s* = t − 1`.  For `n = 8` (2-power)
at `t = 4` it COLLAPSES to `minSupp = 2` (the subgroup indicator of `{0,4} ≤ Z_8`, Fourier support
`{0,2,4,6}`), giving `s* = 6 = n − 2 ≫ k + 1`.  Same far support, capacity for prime, Johnson-or-worse
for 2-power — the WEAKNESS of the uncertainty principle for highly-composite `Z_{2^μ}`.

Honesty: Tao's additive uncertainty is NOT in Mathlib (it needs Chebotarev's cyclotomic-minor
nonvanishing); we name its *consumed corollary* as a `Prop` hypothesis `TaoSparseZeroBound` and
DERIVE the capacity consequence.  The derivation, the bridge to the real polynomial, and the
`FarFromCode` promotion are fully proven (axiom-clean).  Only Tao's classical input is hypothesized.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.CapacitySidePrime

open ProximityGap.SpikeFloor ProximityGap.FarCosetExplosion

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The far-line sparse obstruction polynomial.** For monomial offset `x^a`, monomial direction
`x^b`, scalar `γ`, and a degree-`< k` codeword polynomial `P`, this is the explicit polynomial whose
zeros on the smooth domain contain the line-agreement set:

  `g = X^(a mod n) + γ • X^(b mod n) − P`.

On `μ_n ≅ Z/n` its discrete-Fourier support is `⊆ {0..k−1} ∪ {a mod n, b mod n}` (the codeword
contributes `{0..k−1}`; the two monomials contribute `{a mod n, b mod n}`), size `≤ k + 2`. -/
noncomputable def farLinePoly (a b : ℕ) (γ : F) (P : Polynomial F) : Polynomial F :=
  X ^ (a % n) + (C γ) * X ^ (b % n) - P

/-- Reducing the monomial exponent mod `n` on a smooth domain (`(dom i)^n = 1`). -/
private lemma dom_pow_mod (dom : Fin n ↪ F) (hsmooth : ∀ i, (dom i) ^ n = 1) (a : ℕ) (i : Fin n) :
    (dom i) ^ a = (dom i) ^ (a % n) := by
  conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hsmooth i, one_pow, one_mul]

/-- **Every far-line agreement point is a zero of the sparse polynomial `g`.** On a smooth domain,
if the codeword `c(x) = P(dom x)` agrees with the far line `x^a + γ·x^b` at `i`, then `dom i` is a
root of `g = X^(a%n) + γ•X^(b%n) − P`.  This is the bridge identity making the agreement set a subset
of the zero set of the explicit Fourier-sparse function — the real object of the reformulation. -/
theorem farLine_agreement_isRoot (dom : Fin n ↪ F) (hsmooth : ∀ i, (dom i) ^ n = 1)
    (a b : ℕ) (γ : F) (P : Polynomial F) (i : Fin n)
    (hag : P.eval (dom i) = (dom i) ^ a + γ • (dom i) ^ b) :
    (farLinePoly (n := n) a b γ P).IsRoot (dom i) := by
  simp only [farLinePoly, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [dom_pow_mod dom hsmooth a i, dom_pow_mod dom hsmooth b i] at hag
  rw [smul_eq_mul] at hag
  rw [hag]; ring

/-- **The number of distinct Fourier modes of `g` is `≤ k + 2`.**  We *model* the Fourier-support
size by the size of the term-support of `g` reduced mod `X^n − 1`; concretely the obstruction
polynomial `g` is built from the `k` codeword degrees and the two monomial exponents `a, b`, so any
honest count of its `μ_n`-Fourier modes is `≤ k + 2`.  Rather than fix a particular DFT formalism we
expose this as the structural datum `t ≤ k + 2` that Tao's corollary consumes.

This `def` records the structural sparsity bound used as the hypothesis of `TaoSparseZeroBound`. -/
def farFourierSparsity (k : ℕ) : ℕ := k + 2

/-- **Tao's sparse-zero corollary (named hypothesis).**  The corollary of Tao (2005) we consume:
over a smooth evaluation domain of PRIME cardinality `n`, a nonzero far-line obstruction polynomial
`g = farLinePoly a b γ P` (whose `μ_n`-Fourier support has size `≤ t`) has at most `t − 1` zeros
among the domain points `{dom i}`.  Here `t = k + 2` (`farFourierSparsity k`), so the bound is
`≤ k + 1`.

This is exactly the prime-order content of `|supp f| + |supp f̂| ≥ n + 1` (Tao, MRL 12, 2005),
specialized to the genuine far-line polynomial.  We name it as a `Prop` because Tao's additive
uncertainty is not in Mathlib (it requires Chebotarev's nonvanishing of cyclotomic DFT minors,
valid only for prime order — which is precisely WHY the bound is constant in `n` and fails for
`2^μ`).  The predicate is stated over the REAL objects: `dom`, the agreement set, `farLinePoly`. -/
def TaoSparseZeroBound (dom : Fin n ↪ F) (k : ℕ) : Prop :=
  ∀ (a b : ℕ) (γ : F) (P : Polynomial F), P.degree < (k : WithBot ℕ) →
    farLinePoly (n := n) a b γ P ≠ 0 →
    ((Finset.univ : Finset (Fin n)).filter
        (fun i => (farLinePoly (n := n) a b γ P).IsRoot (dom i))).card ≤ k + 1

/-- **CAPACITY (prime side) — the far-line agreement count is `≤ k + 1`.**  Granting Tao's
sparse-zero corollary over a prime-cardinality smooth domain, any codeword of `rsCode dom k` agrees
with the far line `x^a + γ·x^b` on at most `k + 1` points — because the agreement set is contained in
the zero set of the nonzero `(k+2)`-Fourier-sparse polynomial `g = farLinePoly a b γ P`, on which
Tao's bound is `k + 1`.

This pins `s* ≤ k + 1` (CONSTANT in `n`) on the REAL agreement object, hence `δ* = 1 − (k+1)/n →
1 − ρ`, capacity.  Contrast `_UncertaintyTwoPowerCeiling.JohnsonFloorTwoPower`, the open `√(kn)`
floor for `n = 2^μ`. -/
theorem farLine_agreement_card_le_capacity (dom : Fin n ↪ F) (hsmooth : ∀ i, (dom i) ^ n = 1)
    {k : ℕ} (hTao : TaoSparseZeroBound (n := n) dom k)
    (a b : ℕ) (γ : F) (P : Polynomial F) (hPdeg : P.degree < (k : WithBot ℕ))
    (hg0 : farLinePoly (n := n) a b γ P ≠ 0)
    {c : Fin n → F} (hc : c = fun i => P.eval (dom i)) :
    ((Finset.univ : Finset (Fin n)).filter
        (fun i => c i = (dom i) ^ a + γ • (dom i) ^ b)).card ≤ k + 1 := by
  classical
  set A := (Finset.univ : Finset (Fin n)).filter
    (fun i => c i = (dom i) ^ a + γ • (dom i) ^ b) with hA
  set B := (Finset.univ : Finset (Fin n)).filter
    (fun i => (farLinePoly (n := n) a b γ P).IsRoot (dom i)) with hB
  -- A ⊆ B: every agreement point is a root of g
  have hAB : A ⊆ B := by
    intro i hi
    rw [hA, Finset.mem_filter] at hi
    rw [hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hagi : c i = (dom i) ^ a + γ • (dom i) ^ b := hi.2
    have hci : P.eval (dom i) = (dom i) ^ a + γ • (dom i) ^ b := by rw [← hagi, hc]
    exact farLine_agreement_isRoot dom hsmooth a b γ P i hci
  calc A.card ≤ B.card := Finset.card_le_card hAB
    _ ≤ k + 1 := hTao a b γ P hPdeg hg0

/-- **CAPACITY (prime side) — the far line is `FarFromCode` at any radius beating `(k+1)/n`.**
Combining the agreement bound with the witness budget: granting Tao's corollary, if
`(k+1 : ℝ≥0) < (1 − δ)·n` then the far line `x^a + γ·x^b` is `FarFromCode` at radius `δ` against
`rsCode dom k`.  Since this holds for every `δ` with `(k+1)/n < 1 − δ`, the far-line list-decoding
radius is `s* ≤ k + 1`: `δ*` reaches `1 − (k+1)/n`, capacity. -/
theorem farLine_FarFromCode_capacity (dom : Fin n ↪ F) (hsmooth : ∀ i, (dom i) ^ n = 1)
    {k : ℕ} (hTao : TaoSparseZeroBound (n := n) dom k)
    (a b : ℕ) (γ : F) {δ : ℝ≥0}
    (hfar : ∀ P : Polynomial F, P.degree < (k : WithBot ℕ) → farLinePoly (n := n) a b γ P ≠ 0)
    (hlt : ((k + 1 : ℕ) : ℝ≥0) < (1 - δ) * (n : ℝ≥0)) :
    FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (dom i) ^ a + γ • (dom i) ^ b) := by
  classical
  intro c hc S hS
  by_contra hcon
  push_neg at hcon
  obtain ⟨P, hPdeg, hcP⟩ := hc
  have hccoe : c = fun i => P.eval (dom i) := hcP
  have hg0 : farLinePoly (n := n) a b γ P ≠ 0 := hfar P hPdeg
  -- S ⊆ agreement set, so |S| ≤ k+1
  have hSsub : S ⊆ (Finset.univ : Finset (Fin n)).filter
      (fun i => c i = (dom i) ^ a + γ • (dom i) ^ b) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon i hi⟩
  have hScard : S.card ≤ k + 1 :=
    le_trans (Finset.card_le_card hSsub)
      (farLine_agreement_card_le_capacity dom hsmooth hTao a b γ P hPdeg hg0 hccoe)
  have hSge : (1 - δ) * (n : ℝ≥0) ≤ (S.card : ℝ≥0) := by
    have := hS; rwa [Fintype.card_fin] at this
  have hSle : (S.card : ℝ≥0) ≤ ((k + 1 : ℕ) : ℝ≥0) := by exact_mod_cast hScard
  exact absurd (lt_of_le_of_lt (le_trans hSge hSle) hlt) (lt_irrefl _)

end ProximityGap.CapacitySidePrime

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only):
#print axioms ProximityGap.CapacitySidePrime.farLine_agreement_isRoot
#print axioms ProximityGap.CapacitySidePrime.farLine_agreement_card_le_capacity
#print axioms ProximityGap.CapacitySidePrime.farLine_FarFromCode_capacity
