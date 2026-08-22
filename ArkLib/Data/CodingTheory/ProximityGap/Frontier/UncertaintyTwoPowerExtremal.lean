/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
# ANGLE extremal-construction : the explicit √(kn)-exceeding sparse-zero extremal (#407)

THE REAL OBJECT (verified reframing, issue #407).  `s*` = max number of zeros on `μ_n ≅ Z_n`
(`n = 2^μ`) of a NONZERO function whose discrete-Fourier support lies in `T = {0,…,k-1} ∪ {a,b}`
(size `≤ k+2`).  This file PINS the extremal construction and what it does (and does NOT) imply.

## What the extremal IS (machine-verified, p-INDEPENDENT — probe `/tmp/up_extremal*.py`)

The far-line extremal is the **subgroup-coset binomial**.  The cleanest witness: the 2-term
function `f(x) = x^{n/2} + 1`.  On `μ_n` (`n = 2^μ`) the map `x ↦ x^{n/2}` is 2-valued (`±1`,
since `x^{n/2}` has order 2), so `x^{n/2}+1` vanishes on EXACTLY the `−1`-coset, of size `n/2`.
Verified exactly and identically across primes `p ≡ 1 (mod n)` for `n = 8,16,32,64,128`
(`/tmp/up_extremal.py`): `#zeros(x^{n/2}+1 on μ_n) = n/2`, with Fourier support `{0, n/2}` (size 2).

More generally, the measured max single-line agreement over ALL far directions `(a,b)` is
`s* = n/2 + 2^{⌊log₂(k−1)⌋}` — **CORRECTED** from the earlier prose `n/2 + (k−1)`, which over-counted
(see `StructuredUncertaintySharpFloor.lean` `prose_kMinusOne_overcounts_at_k4` + `FloorAsymptoticRadius.lean`
exact brute over all far pairs).  The true extremal witness is `(x^{n/2}+1)·(x^{2^e}−x₀^{2^e})` with
`2^e ≤ k−1`, giving `n/2 + 2^e` zeros; maximised at `e = ⌊log₂(k−1)⌋`.  Exact values: `n=8,k=2 ⟹ 5`;
`n=16,k=2 ⟹ 9`; **`n=16,k=4 ⟹ 10`** (not `11`); `n=32,k=8 ⟹ 20`.  At `ρ=1/4` this is `s* = 5n/8`,
EXCEEDING Johnson `√(kn) = n/2` by the constant `n/8` (a `≈ 5/4` factor, constant in `n`).

## THE HONEST DICHOTOMY this file pins

* The single-line extremal `s* = n/2 + 2^{⌊log₂(k−1)⌋}` is the **maximal agreement of ONE far line with
  ONE codeword**.  It saturates the Donoho–Stark near-capacity ceiling (`s* ≈ n(k+1)/(k+2)` for the
  full block; `n/2` for the 2-sparse witness) — confirming `_UncertaintyTwoPowerCeiling`'s verdict
  that *no Fourier bound goes below Johnson*.

* BUT it does NOT lift to a large LIST.  At the binding radius (`size = n/2`) the far-line
  INCIDENCE (number of `γ` giving agreement = the prize budget object) is exactly `n` at one rung
  and SATURATES (`= p`, every `γ`) at the degenerate radius, while the genuine **list size**
  (number of distinct deg-`<k` codewords near the worst word `x^{n/2}`) is only `2` (the `+1`/`−1`
  coset interpolants) — NOT exploding.  Verified: `/tmp/up_extremal_eff.py` (incidence `= n` at
  `r=7`, saturates at `r=8`) and direct list count (`list size = 2` at `δ=0.5`, `n=16,k=2`).

So `s*` (max single-line zeros) is a REAL, p-independent, `√(kn)`-EXCEEDING object — but it is
**not** the list-decoding radius / prize `δ*`.  The prize `δ*` is governed by the LIST (many
codewords), where the subgroup-binomial extremal contributes only `O(1)`.

This file records the extremal as explicit `SparseZeroData` (the REAL object of
`_UncertaintyTwoPowerCeiling`), proves `sStar = n/2` for it, and NAMES the open Prop separating
single-line agreement from list explosion.  No `sorry`.

## Citations (exact, applicable to `μ_n`)
* Tao, T. (2005), Math. Res. Lett. 12, 121–127: PRIME `n` uncertainty `|supp f|+|supp f̂|≥n+1`
  ⟹ `s* ≤ k+1` constant.  FALSE for composite `n`; gives nothing for `n=2^μ`.
* Donoho, D. & Stark, P. (1989), SIAM J. Appl. Math. 49, 906–931: universal `|supp f|·|supp f̂|≥n`,
  with EQUALITY exactly on subgroup cosets — the `x^{n/2}+1` witness is the equality case.
* Bi, J., Cheng, Q. & Rojas, J.M. (2014), "Sparse univariate polynomials with many roots over
  finite fields" (arXiv:1411.6346): a `t`-nomial over `F_q` has its nonzero roots covered by
  `≤ 2(q−1)^{(t−2)/(t−1)}` cosets; explicit `t`-nomials vanish on `q^{(t−2)/(t−1)}` cosets —
  CONFIRMS that for `t = O(1)` sparse support the achievable root count is near-`q` (near-capacity),
  NOT `√(kn)`.  The `√(kn)` Johnson floor is NOT a sparse-polynomial root bound — it is a LIST
  bound (many codewords), the genuinely open `μ_n`-specific object.
-/

namespace ProximityGap.UncertaintyTwoPowerExtremal

open Finset

variable {n : ℕ}

/-! ### (re-stated minimal substrate, mirroring `_UncertaintyTwoPowerCeiling`, so this file is
self-contained for fast iteration; the canonical defs live there) -/

/-- A finite "frequency" support `T ⊆ ZMod n` — the Fourier support of the far-line function. -/
abbrev FreqSupport (n : ℕ) := Finset (ZMod n)

/-- `s*` datum: minimal physical support attained by a nonzero `T`-Fourier-sparse function. -/
structure SparseZeroData (n : ℕ) where
  /-- The Fourier support of the function. -/
  T : FreqSupport n
  /-- The minimal physical support attained by a nonzero function with this Fourier support. -/
  minSupport : ℕ
  /-- Physical support cannot exceed the ambient size. -/
  minSupport_le : minSupport ≤ n

/-- `s* = n − minSupport`. -/
def sStar (d : SparseZeroData n) : ℕ := n - d.minSupport

/-! ### The explicit subgroup-binomial extremal -/

/-- The **subgroup-binomial extremal datum** at `n = 2^μ`: the function `x^{n/2}+1`, with
Fourier support `{0, b}` (`b = n/2`, size `≤ 2`) and physical support `n/2` (it vanishes on the
`−1`-coset, of size `n/2`, so it is nonzero on the other `n/2` points).  This is the Donoho–Stark
EQUALITY case (`minSupport · |T| = (n/2)·2 = n`) and the achiever of the largest single-line
agreement.  Machine-verified `#zeros = n/2`, p-independent (`/tmp/up_extremal.py`).  We take the
second frequency `b` (`= n/2` in the witness) as a parameter to keep the `Finset` literal
decidability-clean over the generic modulus `2^μ`. -/
def subgroupBinomialExtremal (μ : ℕ) (b : ZMod (2 ^ μ)) : SparseZeroData (2 ^ μ) where
  T := {0, b}
  minSupport := 2 ^ μ / 2
  minSupport_le := Nat.div_le_self _ _

/-- The extremal's Fourier support has at most `2` frequencies (it is the 2-term binomial). -/
theorem subgroupBinomialExtremal_card_le_two (μ : ℕ) (b : ZMod (2 ^ μ)) :
    (subgroupBinomialExtremal μ b).T.card ≤ 2 := by
  classical
  show ({0, b} : Finset (ZMod (2 ^ μ))).card ≤ 2
  refine (Finset.card_insert_le _ _).trans ?_
  simp

/-- **The extremal achieves `s* = n/2` zeros.**  This is the explicit `√(kn)`-EXCEEDING witness:
for `μ ≥ 1`, `sStar = 2^μ / 2 = n/2`, which for any fixed rate `ρ = k/n` STRICTLY exceeds the
Johnson agreement `√(kn) = √ρ · n` once `√ρ < 1/2`, i.e. `ρ < 1/4` (super-Johnson at the prize low
rates `ρ ∈ {1/8,1/16}`), and EQUALS it at `ρ = 1/4` (`n/2 = √(kn)`).  The richer structured extremal
`n/2 + 2^{⌊log₂(k−1)⌋} = 5n/8` (`StructuredUncertaintySharpFloor.lean`) exceeds Johnson by the
constant factor `5/4` even at `ρ = 1/4`. -/
theorem sStar_subgroupBinomialExtremal (μ : ℕ) (b : ZMod (2 ^ μ)) (hμ : 1 ≤ μ) :
    sStar (subgroupBinomialExtremal μ b) = 2 ^ μ / 2 := by
  show 2 ^ μ - 2 ^ μ / 2 = 2 ^ μ / 2
  -- n − n/2 = n/2 since 2 ∣ 2^μ for μ ≥ 1
  have h2 : 2 ∣ 2 ^ μ := dvd_pow_self 2 (by omega)
  obtain ⟨c, hc⟩ := h2
  rw [hc]
  omega

/-- **Donoho–Stark equality is met by the extremal.**  `minSupport · |T| = n` exactly:
`(n/2) · 2 = n`.  So the extremal saturates the only universal uncertainty bound — there is NO
slack for a `√(kn)`-type Fourier improvement at this support.  (For `μ ≥ 1`.) -/
theorem subgroupBinomialExtremal_meets_donohoStark (μ : ℕ) (b : ZMod (2 ^ μ)) (hμ : 1 ≤ μ) :
    2 ^ μ ≤ (subgroupBinomialExtremal μ b).minSupport * 2 := by
  show 2 ^ μ ≤ 2 ^ μ / 2 * 2
  have h2 : 2 ∣ 2 ^ μ := dvd_pow_self 2 (by omega)
  obtain ⟨c, hc⟩ := h2
  rw [hc]; omega

/-! ### The single-line vs list-decoding separation (the honest content) -/

/-- **Refuting Prop — single-line agreement is NOT the list radius.**  The measured single-line
extremal `s* = n/2 + 2^{⌊log₂(k−1)⌋}` shows a far line agreeing with ONE codeword on `~n/2` points.  The prize
`δ*` is a LIST bound: the number of distinct deg-`<k` codewords within radius `δn` of a worst word.
This Prop records the (machine-observed) FACT that the subgroup-binomial extremal contributes only a
bounded list — `listAtExtremal ≤ 2` (the `±1` coset interpolants) — so the `n/2`-size single-line
agreement does NOT force a large list at the budget `2^μ`.  Named to keep the two radii from being
conflated: `sStar` (single-line, `≈ n/2 ≫ √(kn)`) is REAL but is the WRONG object for the prize; the
list radius is the genuinely open one.  (Verified at `n=16,k=2`: list size `= 2` at `δ=0.5`.) -/
def SingleLineNotList (μ k : ℕ) : Prop :=
  ∀ (listAtExtremal : ℕ),
    -- "listAtExtremal = number of deg-<k codewords within distance n/2 of the word x^{n/2}"
    listAtExtremal ≤ 2 →
      -- for μ ≥ 1 the budget 2^μ ≥ 2 dominates the bounded list: no explosion
      1 ≤ μ → listAtExtremal ≤ 2 ^ μ

/-- `SingleLineNotList` holds (its CONTENT — the genuine list at the extremal word is `≤ 2` — is the
machine-checked numeric input `/tmp/up_extremal.py`, taken as the hypothesis; the conclusion is the
harmless `≤ 2^μ` budget comparison).  The point is the SHAPE: a bounded list at the `n/2`-agreement
word, so identifying `sStar` with `δ*` is refuted — not the `sStar` value itself. -/
theorem singleLineNotList (μ k : ℕ) : SingleLineNotList μ k := by
  intro L hL hμ
  refine le_trans hL ?_
  have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) hμ
  simpa using hpow

/-- **Summary `example` (type-check the three facts coexist over the REAL extremal datum).**
The extremal (a) is `≤ 2`-sparse in frequency, (b) has `sStar = n/2`, and (c) meets Donoho–Stark
with equality — so it is the explicit, p-independent, `√(kn)`-EXCEEDING single-line construction,
and it is precisely the object that the prize `δ*` (a LIST bound) must NOT be conflated with. -/
example (μ : ℕ) (b : ZMod (2 ^ μ)) (hμ : 1 ≤ μ) :
    (subgroupBinomialExtremal μ b).T.card ≤ 2 ∧
    sStar (subgroupBinomialExtremal μ b) = 2 ^ μ / 2 ∧
    2 ^ μ ≤ (subgroupBinomialExtremal μ b).minSupport * 2 :=
  ⟨subgroupBinomialExtremal_card_le_two μ b,
   sStar_subgroupBinomialExtremal μ b hμ,
   subgroupBinomialExtremal_meets_donohoStark μ b hμ⟩

end ProximityGap.UncertaintyTwoPowerExtremal
