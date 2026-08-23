/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.GHSZ02Foundations
import ArkLib.Data.CodingTheory.ListDecoding.Bounds
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds

/-!
# GHSZ02 Corollary 20 — Reed-Solomon list-size lower bound over prime fields

This file builds the *genuine combinatorial content* of GHSZ02 Corollary 20 (the source of
ABF26 Theorem 3.13, `CodingTheory.rs_lambda_large_prime_ghsz02`) maximally in-tree, and pins
the single remaining `for large enough p` asymptotic input as a precisely named residual.

## What GHSZ02 Corollary 20 actually says

Guruswami–Håstad–Sudan–Zuckerman, *Combinatorial bounds for list decoding*, IEEE Trans.
Inform. Theory 48 (2002), §III-F.

> **Lemma 19.** For any MDS `[n, k]_q` code `C` and `a ≥ k`,
> `(1/e)·C(n,a)·q^{k-a} ≤ E_x[|B(x, n-a) ∩ C|] ≤ C(n,a)·q^{k-a}`.
>
> **Corollary 20.** Use an MDS `[n, k]_q` code with `n = q` and `k = n^ε` (e.g. Reed-Solomon).
> Then `C(n,a)·q^{k-a} ≥ (n/a)^a·q^{k-a} = n^k/a^a`. Letting `a = (1-γ)n^ε/ε`, for large
> enough `n` we have `a^a ≤ n^{(1-γ/2)n^ε}`, and the expected number of codewords in a ball of
> radius `n-a` is `Ω(n^{(γ/2)n^ε})`.

**Important.** Corollary 20 is a *pure averaging argument* — there is **no** multiplicative
character / `p`-th power residue / BCH subfield-subcode input. (Those appear in the *other*
GHSZ02 result, Theorem 13 for binary concatenated codes via Lemmas 17/18, which is a different
construction and is not what ABF26 T3.13 cites.) Consequently **no character-sum residual is
needed**: GHSZ02 Cor 20 is elementary, and Mathlib's `GaussSum`/`MulChar` API is not on the
critical path here.

## Parameter dictionary (GHSZ02 ↔ ABF26 T3.13)

`q = p`, `n = p`, `ε ↔ α`, `γ ↔ β`, `k = ⌊p^α⌋`, agreement `a = n − ⌊δ·n⌋`,
`δ = 1 − ((1−β)/α)·p^{α−1}` so `a ≈ ((1−β)/α)·p^α`, list size `Ω(p^{p^α·β/2})`.

## Layering

* `GHSZ02Cor20.averaging_real` — **proven brick**. The Lemma-19 averaging bound, real-valued:
  `q^k · (C(n,r)·(q−1)^r) / q^n ≤ |Λ(RS[domain,k], δ, w)|` for some `w`. Wraps the already
  proven `GHSZ02RS.ghsz02_rs_averaging_core` (no new admits).
* `GHSZ02Cor20.choose_real_ge_pow_div` — **proven brick**. The elementary binomial bound
  `(n+1−r)^r / r! ≤ C(n,r)` real-valued (from Mathlib `Nat.pow_le_choose`).
* `GHSZ02LargeN` — **named residual**. The single `for large enough p` asymptotic estimate that
  GHSZ02 Cor 20 proves (`a^a ≤ p^{(1−γ/2)p^ε}` plus the `(1−1/p)^{n−a} ≥ 1/e` constant absorbed
  into the exponent slack), stated as the one real inequality
  `q^n · p^{p^α·β/2} ≤ q^k · (C(n,r)·(q−1)^r)`. See its docstring for the exact constant tracking.
* `CodingTheory.hcount_of_largeN` — **proven reduction**. Bricks + residual ⟹ the exact `hcount`
  hypothesis of `CodingTheory.rs_lambda_large_prime_ghsz02_of_residuals`.
* `CodingTheory.omega_listsize_of_largeN` — **proven end-to-end front door**. Residual ⟹ the full
  ABF26 T3.13 per-instance Ω list-size bound `|Λ| > c · p^{p^α·β/2}` (`c = 1/2`).

The residual surface is thereby shrunk from "construct the GHSZ02 bad word + count its close
codewords" to "the explicit real inequality `p^n·p^{p^α·β/2} ≤ p^k·C(n,r)·(p−1)^r`", with the
*existence of the word* (the averaging) and all `ncard`/Ω bookkeeping discharged in-tree.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped BigOperators
open CodingTheory ListDecodable

namespace GHSZ02Cor20

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Proven brick (GHSZ02 Lemma 19, averaging, real form).**

There is a word `w` whose relative-distance close-codeword list for `RS[domain, k]` satisfies
`q^k · (C(n,r)·(q−1)^r) / q^n ≤ |Λ(C, δ, w)|`, where `q = |F|`, `n = |ι|`, `r = ⌊δ·n⌋`.

This is a clean real-valued repackaging of `GHSZ02RS.ghsz02_rs_averaging_core` (which itself is
fully proven, `sorry`-free): we move the `q^n` factor to the denominator. No new admit. -/
theorem averaging_real
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hk : k ≤ Fintype.card ι) :
    ∃ w : ι → F,
      ((Fintype.card F : ℝ) ^ k
          * ((Nat.choose (Fintype.card ι) ⌊δ * Fintype.card ι⌋₊ : ℝ)
              * ((Fintype.card F : ℝ) - 1) ^ ⌊δ * Fintype.card ι⌋₊))
            / (Fintype.card F : ℝ) ^ (Fintype.card ι)
        ≤ ((closeCodewordsRel
              ((ReedSolomon.code domain k : Submodule F (ι → F)) : Set (ι → F))
              w δ).ncard : ℝ) := by
  classical
  obtain ⟨w, hw⟩ := GHSZ02RS.ghsz02_rs_averaging_core domain k δ hδ_pos hδ_lt hk
  refine ⟨w, ?_⟩
  -- `q` is positive (a finite field has at least 2 elements; in any case `card F ≥ 1`).
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hqn_pos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (Fintype.card ι) := pow_pos hqpos _
  -- Cast the integer averaging inequality to ℝ.  Name the ℕ quantities first so the
  -- subtraction `card F - 1` is unambiguously ℕ-subtraction (not `Int.subNatNat`).
  set Lnat : ℕ := (Fintype.card F) ^ k
      * (Nat.choose (Fintype.card ι) ⌊δ * Fintype.card ι⌋₊
          * (Fintype.card F - 1) ^ ⌊δ * Fintype.card ι⌋₊) with hLnat
  set Rnat : ℕ := (Fintype.card F) ^ (Fintype.card ι)
      * (closeCodewordsRel ((ReedSolomon.code domain k : Submodule F (ι → F)) :
            Set (ι → F)) w δ).ncard with hRnat
  have hw' : (Lnat : ℝ) ≤ (Rnat : ℝ) := by exact_mod_cast hw
  -- The ℕ-subtraction `(card F - 1)` casts to the ℝ-subtraction since `card F ≥ 1`.
  have hcard_ge_one : 1 ≤ Fintype.card F := Fintype.card_pos
  have hsub_cast : ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Nat.cast_sub hcard_ge_one]; norm_num
  -- Rearrange: divide both sides by `q^n`.
  rw [div_le_iff₀ hqn_pos]
  -- Match the LHS shape (casts of the ℕ-product) to `(Lnat : ℝ)`.
  have hLHS :
      ((Fintype.card F : ℝ) ^ k
          * ((Nat.choose (Fintype.card ι) ⌊δ * Fintype.card ι⌋₊ : ℝ)
              * ((Fintype.card F : ℝ) - 1) ^ ⌊δ * Fintype.card ι⌋₊))
        = (Lnat : ℝ) := by
    rw [hLnat]; push_cast [hsub_cast]; ring
  rw [hLHS]
  -- And the RHS shape.
  have hRHS :
      ((closeCodewordsRel ((ReedSolomon.code domain k : Submodule F (ι → F)) : Set (ι → F))
            w δ).ncard : ℝ) * (Fintype.card F : ℝ) ^ (Fintype.card ι)
        = (Rnat : ℝ) := by
    rw [hRnat]; push_cast; ring
  rw [hRHS]
  exact hw'

/-- **Proven brick (elementary binomial bound, real form).**

`(n + 1 − r)^r / r! ≤ C(n,r)` over `ℝ`. This is Mathlib's `Nat.pow_le_choose` specialised to
`ℝ`; it is the real engine of GHSZ02 Cor 20's `C(n,a) ≥ (n/a)^a` step. -/
theorem choose_real_ge_pow_div (r n : ℕ) :
    (((n + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ) ≤ (Nat.choose n r : ℝ) :=
  Nat.pow_le_choose r n

end GHSZ02Cor20

namespace CodingTheory

open GHSZ02Cor20

/-- **GHSZ02 Corollary 20 — named asymptotic residual.**

The single `for large enough p` analytic estimate that GHSZ02 Cor 20 establishes, isolated as
one explicit real inequality between *closed-form* quantities (no codes, no `ncard`, no
existentials over words):

  `p^n · p^{p^α·β/2}  ≤  p^k · (C(n,r)·(p−1)^r)`

(with `q = n = p`, `k = ⌊p^α⌋`, `r = ⌊δ·p⌋`).

**Why this is exactly GHSZ02 Cor 20's content, with the constants tracked honestly.**
Set the agreement `a = n − r`. Dividing the target by `p^n` and using
`(p−1)^r / p^n = (1 − 1/p)^{n−a} · p^{−a}` gives the equivalent form

  `p^{p^α·β/2}  ≤  C(n,a)·p^{k−a} · (1 − 1/p)^{n−a}`.

GHSZ02's chain bounds the *codeword-count* factor `C(n,a)·p^{k−a} ≥ (n/a)^a·p^{k−a} = n^k/a^a`,
then uses `a^a ≤ n^{(1−γ/2)n^ε}` (the `for large enough n` step, `ε ↔ α`, `γ ↔ β`) to get
`C(n,a)·p^{k−a} ≥ n^{(γ/2)n^ε} = p^{p^α·β/2}`. The remaining `(1−1/p)^{n−a} ≥ 1/e`
factor (`GHSZ02Core.one_sub_inv_pow_ge_inv_e`) costs a constant, which GHSZ02 absorbs into
the `Ω`/exponent slack: the corollary states `Ω(n^{(γ/2)n^ε})`, and the `γ/2` exponent has
genuine room below the achievable `~γ`, so the constant `1/e` is swallowed by taking `n` large
enough. The displayed no-constant inequality is therefore the precise closed form that, fed
through the averaging core, yields the `hcount` hypothesis used in
`rs_lambda_large_prime_ghsz02_of_residuals`.

Everything *around* this estimate is proven in-tree: the Lemma-19 averaging *existence* of the
word, the `q^n` division, the `ncard` cardinality arithmetic, and the Ω-constant `c = 1/2`
strict-inequality bookkeeping (`GHSZ02Cor20.averaging_real`,
`rs_lambda_large_prime_ghsz02_of_residuals`).

We keep this a residual because it carries the genuine `for large enough p` quantifier content
of GHSZ02 Cor 20 (`a^a ≤ n^{(1−β/2)n^ε}` only for `n` above a threshold, plus the constant
absorption above), an asymptotic estimate not derivable in-tree from the unhypothesised
statement. **It is *not* a character-sum residual** — GHSZ02 Cor 20 uses no multiplicative
characters (see the module header), so no Mathlib `GaussSum`/`MulChar` input is required. -/
def GHSZ02LargeN
    (α β : ℝ) (p : ℕ) (δ : ℝ) : Prop :=
    (p : ℝ) ^ p * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2)
      ≤ (p : ℝ) ^ (Nat.floor ((p : ℝ) ^ α))
          * ((Nat.choose p ⌊δ * (p : ℝ)⌋₊ : ℝ) * ((p : ℝ) - 1) ^ ⌊δ * (p : ℝ)⌋₊)

/-- **GHSZ02 Corollary 20 — proven reduction (residual ⟹ `hcount`).**

Given the named asymptotic residual `GHSZ02LargeN` for the prime-field RS parameters, together
with `n = |ι| = p` and `q = |F| = p`, the GHSZ02 averaging core produces a word `w` whose
close-codeword count meets the `hcount` hypothesis of `rs_lambda_large_prime_ghsz02_of_residuals`:

  `p^{p^α·β/2} ≤ |Λ(RS[domain, ⌊p^α⌋], δ, w)|`.

All steps here are proven, `sorry`-free: the residual supplies the closed-form inequality, the
averaging brick supplies the word and `q^k·(…)/q^n ≤ |Λ|`, and we divide. -/
theorem hcount_of_largeN
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (α β : ℝ) (p : ℕ) (hp2 : 2 ≤ p)
    (hcardF : Fintype.card F = p) (hcardι : Fintype.card ι = p)
    (domain : ι ↪ F) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hk : Nat.floor ((p : ℝ) ^ α) ≤ p)
    (hlargeN : GHSZ02LargeN α β p δ) :
    ∃ w : ι → F,
      (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) ≤
        ((closeCodewordsRel
            ((ReedSolomon.code domain (Nat.floor ((p : ℝ) ^ α)) : Submodule F (ι → F)) :
              Set (ι → F)) w δ).ncard : ℝ) := by
  classical
  set k : ℕ := Nat.floor ((p : ℝ) ^ α) with hk_def
  have hk' : k ≤ Fintype.card ι := by rw [hcardι]; exact hk
  obtain ⟨w, hw⟩ := averaging_real domain k δ hδ_pos hδ_lt hk'
  refine ⟨w, ?_⟩
  -- Specialise the averaging brick under `card F = card ι = p`.
  rw [hcardF, hcardι] at hw
  -- `q^p > 0`.
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hqn_pos : (0 : ℝ) < (p : ℝ) ^ p := pow_pos hp_pos p
  -- From the residual: `p^{p^α·β/2} ≤ (p^k · (…)) / p^p`.
  have hresid := hlargeN
  -- Divide the residual by `p^p`.
  have hdiv :
      (p : ℝ) ^ ((p : ℝ) ^ α * β / 2)
        ≤ ((p : ℝ) ^ k
            * ((Nat.choose p ⌊δ * (p : ℝ)⌋₊ : ℝ) * ((p : ℝ) - 1) ^ ⌊δ * (p : ℝ)⌋₊))
              / (p : ℝ) ^ p := by
    rw [le_div_iff₀ hqn_pos]
    -- `hresid : p^p * p^{…} ≤ p^k * (…)`.
    calc (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) * (p : ℝ) ^ p
        = (p : ℝ) ^ p * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) := by ring
      _ ≤ _ := hresid
  -- Chain through the averaging brick.
  exact le_trans hdiv hw

/-- **GHSZ02 Corollary 20 — end-to-end front door (residual ⟹ Ω list-size bound).**

The full per-instance ABF26 T3.13 conclusion, derived from the single named asymptotic residual
`GHSZ02LargeN`. There exists a word `w` and an Ω-constant `c > 0` (witnessed by `c = 1/2`) with

  `|Λ(RS[domain, ⌊p^α⌋], δ, w)| > c · p^{p^α·β/2}`.

This chains `hcount_of_largeN` (averaging core + residual ⟹ `hcount`) into the in-tree, fully
proven `rs_lambda_large_prime_ghsz02_of_residuals` (Ω-constant + strict-inequality bookkeeping).
The only ingredient that is *not* discharged in-tree is `GHSZ02LargeN`, the GHSZ02 Cor-20
`for large enough p` real inequality. -/
theorem omega_listsize_of_largeN
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (α β : ℝ) (p : ℕ) (hp2 : 2 ≤ p)
    (hcardF : Fintype.card F = p) (hcardι : Fintype.card ι = p)
    (domain : ι ↪ F) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hk : Nat.floor ((p : ℝ) ^ α) ≤ p)
    (hlargeN : GHSZ02LargeN α β p δ) :
    ∃ (w : ι → F) (c : ℝ), 0 < c ∧
      ((closeCodewordsRel
          ((ReedSolomon.code domain (Nat.floor ((p : ℝ) ^ α)) : Set (ι → F))) w δ).ncard : ℝ) >
        c * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) := by
  obtain ⟨w, hcount⟩ :=
    hcount_of_largeN α β p hp2 hcardF hcardι domain δ hδ_pos hδ_lt hk hlargeN
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  obtain ⟨c, hc_pos, hc⟩ :=
    rs_lambda_large_prime_ghsz02_of_residuals α β p hp1 domain w δ hcount
  exact ⟨w, c, hc_pos, hc⟩

end CodingTheory
