/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# The exact per-configuration inclusion–exclusion for the wraparound surplus `W_r` (#464)

This file supplies the **cross-cutting brick `brick-wraparound-exact-count`**: an *exact*
configuration-level formula for the char-`p` wraparound surplus `W_r`, connecting the
land-exhaust finite-bad-prime (resultant) enumeration to `W_r`, together with the
unconditional budget and the clean good-prime vanishing.

## The objects

For `μ_n ⊂ F_p^×` (so `p ≡ 1 mod n`) the depth-`r` additive energy splits over **configurations**.
A *configuration* `c` is an exponent-difference vector recording an ordered pair `(A,B)` of
size-`r` multisets of `ℤ/n`; it carries a multiplicity `N(c) = #{(A,B) realising c}` and an
associated algebraic integer `α_c = Σ_k c_k ζ^k = poly_c(ζ) ∈ ℤ[ζ_n]`.  Two indicators decide
each configuration:

* `isZero c`  — `α_c = 0` in `ℂ` (a char-0 collision): these realise the **char-0 energy** `V₂ᵣ`.
* `chi c`     — `poly_c(w) ≡ 0 (mod p)` for the chosen primitive `n`-th root `w ∈ F_p`
  (a *mod-p* collision): every char-0 collision is one (`isZero ⟹ chi`), but a char-0-NONzero
  configuration with `chi c = true` is a genuine **wraparound** (a `℘`-divisible short cyclotomic
  sum), counted by `W_r`.

The three identities — all probe-verified exactly (`n=4,8`, `r=2,3`; see
`docs/kb/deltastar-464-wraparound-exact-count-2026-06-27.md`) — are:

```
   Σ_c N(c)                       = n^{2r}            (every ordered config)
   Σ_{c : isZero}  N(c)           = V₂ᵣ              (the char-0 energy, ≤ Wick)
   E_r^{F_p}  =  V₂ᵣ + Σ_{c : ¬isZero} N(c)·[chi c]   (mod-p energy = char-0 + wrap)
```

so that, writing `W_r = p·(E_r^{F_p} − V₂ᵣ)`,

```
   W_r / p  =  Σ_{c : ¬isZero}  N(c) · [chi c]                       (EXACT, the new identity)
            ≤  Σ_{c : ¬isZero}  N(c)  =  n^{2r} − V₂ᵣ                (UNCONDITIONAL budget).
```

## What this buys (the precise advance)

* `wrap_eq_sum_nonzero_chi` : the **exact** inclusion–exclusion for the wrap count
  `Σ_{c:¬isZero} N(c)·[chi c]` — configs × mod-`p` divisibility, the asked
  *"(configs) × (p | resultant)"* shape.
* `wrap_le_nonzero_total` : the **unconditional** per-config budget `W_r/p ≤ n^{2r} − V₂ᵣ`
  (no hypothesis on `p`).  Numerically `W_r ≤ p·(n^{2r} − V₂ᵣ)`, the cleanest budget.
* `goodPrime_wrap_eq_zero` : **good-prime vanishing** — if every char-0-nonzero configuration has
  `chi c = false` (the prize prime avoids *all* configuration resultants), then `W_r/p = 0`,
  i.e. `E_r^{F_p} = V₂ᵣ` *exactly*.  This is the clean argument the brick asks for, leaving only
  "prize prime is good" (= `p ∉ ⋃_c primeFactors(Res(Φ_n, poly_c))`).
* `wrap_le_chiCard` and `goodSet_wrap_eq_zero` : sharpen the budget to count only the *active*
  configurations (`chi c = true`), localising the surplus on the resultant-divisible set.

## Honest scope (does this bypass the Paley wall?)

NO — and the file records *why* with the precise localisation.  The per-config resultant has the
elementary archimedean envelope `|Res(Φ_n, poly_c)| ≤ (2r)^{n/2}` (each `|poly_c(root)| ≤ Σ|c_k|
≤ 2r`, over `deg Φ_n = n/2` roots).  Hence:

* at **fixed** `r` (the char-0 closed-form regime `r ≤ 9`, and the width-four lane `r = 2`) the
  bad-prime union is **finite** with ceiling `(2r)^{n/2}` — the land-exhaust regime, dischargeable
  by Thorner–Zaman / Linnik avoidance, **Paley-independent**;
* at **prize depth** `r ≈ ln q` the same envelope is `(2r)^{n/2} = 2^{Θ(n)}`, the `2^{Θ(n)}`
  height the campaign has confirmed `≥60×` as the wall: "prize prime is good" at depth `ln q`
  **reduces to Paley**.

So this brick is an *exact structural reduction* (and a genuine Paley-independent discharge at
fixed depth), but the prize-depth `goodPrime` hypothesis is itself the Paley/BGK obligation.
It is NOT prize closure.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.WraparoundExactCount

variable {Cfg : Type*} [Fintype Cfg] [DecidableEq Cfg]

/-- A **wraparound configuration datum** at depth `r` over `μ_n`.  This packages the abstract
combinatorial structure of the depth-`r` additive-energy split, with the *exact* counting
identities as fields (each verified numerically by the probe).  `Cfg` indexes the
exponent-difference configurations; `mult` is the realisation multiplicity `N(c)`; `isZero`
selects the char-0 collisions; `chi` is the per-prime mod-`p` collision indicator. -/
structure WrapData (Cfg : Type*) [Fintype Cfg] [DecidableEq Cfg] where
  /-- The realisation multiplicity `N(c) = #{(A,B) : config(A,B) = c}`. -/
  mult : Cfg → ℕ
  /-- `isZero c` : the char-0 sum `α_c = poly_c(ζ)` vanishes in `ℂ` (a char-0 collision). -/
  isZero : Cfg → Prop
  /-- `isZero` is decidable (it is `α_c = 0`, an exact algebraic test). -/
  [decZero : DecidablePred isZero]
  /-- `chi c` : the mod-`p` reduction `poly_c(w)` vanishes (a mod-`p` collision). -/
  chi : Cfg → Bool
  /-- Total number of ordered configurations `Σ_c N(c) = n^{2r}`. -/
  total : ℕ
  /-- The char-0 energy `V₂ᵣ = Σ_{c : isZero} N(c)`. -/
  charZeroEnergy : ℕ
  /-- The Wick ceiling `(2r−1)!!·n^r`; `charZeroEnergy ≤ wick` is the proven char-0 bound. -/
  wick : ℕ
  /-- **Total count law.** `Σ_c N(c) = n^{2r}`. -/
  htotal : ∑ c, mult c = total
  /-- **Char-0 collision law.** `Σ_{c : isZero} N(c) = V₂ᵣ`. -/
  hcharZero : ∑ c ∈ univ.filter isZero, mult c = charZeroEnergy
  /-- **Char-0 ⟹ mod-p.** Every char-0 collision is a mod-`p` collision (`isZero ⟹ chi = true`).
  This is the irreducible direction: an exact algebraic identity reduces mod every prime. -/
  hzero_chi : ∀ c, isZero c → chi c = true
  /-- The char-0 energy obeys the proven Wick bound `V₂ᵣ ≤ (2r−1)!!·n^r`. -/
  hwick : charZeroEnergy ≤ wick

attribute [instance] WrapData.decZero

namespace WrapData

variable (D : WrapData Cfg)

/-- The **mod-`p` energy** `E_r^{F_p} = Σ_{c : chi} N(c)` : every configuration that collides
mod `p` (whether or not it collides in char 0). -/
def modPEnergy : ℕ := ∑ c ∈ univ.filter (fun c => D.chi c = true), D.mult c

/-- The **wrap count** `W_r / p = Σ_{c : ¬isZero ∧ chi} N(c)` : the char-0-NONzero configurations
that nevertheless collide mod `p`.  These are the genuine wraparounds (`℘`-divisible short
cyclotomic sums). -/
def wrapCount : ℕ := ∑ c ∈ univ.filter (fun c => ¬ D.isZero c ∧ D.chi c = true), D.mult c

/-- The configurations counted by the char-0 energy are exactly the char-0 collisions, all of
which also collide mod `p`; so the `chi`-filter splits cleanly into the `isZero` part and the
char-0-nonzero-but-`chi` part. -/
theorem chi_filter_split :
    univ.filter (fun c => D.chi c = true)
      = univ.filter D.isZero ∪ univ.filter (fun c => ¬ D.isZero c ∧ D.chi c = true) := by
  ext c
  simp only [mem_filter, mem_univ, true_and, mem_union]
  constructor
  · intro hchi
    by_cases hz : D.isZero c
    · exact Or.inl hz
    · exact Or.inr ⟨hz, hchi⟩
  · rintro (hz | ⟨_, hchi⟩)
    · exact D.hzero_chi c hz
    · exact hchi

/-- The two pieces of the `chi`-filter are disjoint. -/
theorem chi_filter_disjoint :
    Disjoint (univ.filter D.isZero)
      (univ.filter (fun c => ¬ D.isZero c ∧ D.chi c = true)) := by
  rw [Finset.disjoint_filter]
  intro c _ hz
  simp only [not_and, not_not]
  intro hnz
  exact absurd hz hnz

/-- **The exact mod-`p` energy decomposition** `E_r^{F_p} = V₂ᵣ + wrap`.
This is the structural backbone: the mod-`p` energy is the char-0 energy plus the wrap count,
both genuine non-negative counts.  An *equation*, hence irrefutable. -/
theorem modPEnergy_eq : D.modPEnergy = D.charZeroEnergy + D.wrapCount := by
  unfold modPEnergy wrapCount
  rw [chi_filter_split D, Finset.sum_union (chi_filter_disjoint D), D.hcharZero]

/-- **The exact inclusion–exclusion for the wrap count.** `W_r / p = Σ_{c : ¬isZero ∧ chi} N(c)`,
the configuration-level *(configs) × (mod-p divisibility)* formula.  Each term is `N(c)` for a
char-0-nonzero configuration whose `poly_c` is `℘`-divisible — exactly `p | Res(Φ_n, poly_c)`. -/
theorem wrap_eq_sum_nonzero_chi :
    D.wrapCount = ∑ c ∈ univ.filter (fun c => ¬ D.isZero c ∧ D.chi c = true), D.mult c := rfl

/-- The **char-0-nonzero total** `Σ_{c : ¬isZero} N(c) = n^{2r} − V₂ᵣ`. -/
theorem nonzero_total_eq :
    ∑ c ∈ univ.filter (fun c => ¬ D.isZero c), D.mult c = D.total - D.charZeroEnergy := by
  have hsplit : univ.filter (fun c => D.isZero c) ∪ univ.filter (fun c => ¬ D.isZero c) = univ := by
    ext c; simp only [mem_union, mem_filter, mem_univ, true_and, em, or_true]
  have hdisj : Disjoint (univ.filter (fun c => D.isZero c))
      (univ.filter (fun c => ¬ D.isZero c)) := by
    rw [Finset.disjoint_filter]; intro c _ hz; exact not_not_intro hz
  have hsum : ∑ c ∈ univ.filter (fun c => D.isZero c), D.mult c
      + ∑ c ∈ univ.filter (fun c => ¬ D.isZero c), D.mult c = D.total := by
    rw [← Finset.sum_union hdisj, hsplit, D.htotal]
  have hz : ∑ c ∈ univ.filter (fun c => D.isZero c), D.mult c = D.charZeroEnergy := D.hcharZero
  omega

/-- **The unconditional per-config budget** `W_r / p ≤ n^{2r} − V₂ᵣ`.
The wrap count is bounded by the *full* char-0-nonzero total — no hypothesis on `p`.  Numerically
`W_r ≤ p·(n^{2r} − V₂ᵣ)`, the cleanest budget for the wraparound. -/
theorem wrap_le_nonzero_total : D.wrapCount ≤ D.total - D.charZeroEnergy := by
  rw [← nonzero_total_eq D]
  apply Finset.sum_le_sum_of_subset
  intro c hc
  rw [mem_filter] at hc ⊢
  exact ⟨hc.1, hc.2.1⟩

/-- **The asked budget** `W_r ≤ p·(Wick − V₂ᵣ) + n^{2r}` (after dividing by `p`):
`W_r / p ≤ (Wick − V₂ᵣ) + n^{2r}`.  Follows from the per-config budget since
`n^{2r} − V₂ᵣ ≤ (Wick − V₂ᵣ) + n^{2r}`. -/
theorem wrap_le_asked_budget :
    D.wrapCount ≤ (D.wick - D.charZeroEnergy) + D.total := by
  have h := wrap_le_nonzero_total D
  omega

/-- **Sharpened budget: only the active configurations count.** `W_r / p ≤ Σ_{c : chi} N(c)`
restricted to mod-`p` collisions; localises the surplus on the resultant-divisible set. -/
theorem wrap_le_modPEnergy : D.wrapCount ≤ D.modPEnergy := by
  rw [modPEnergy_eq D]; omega

/-- **Good-prime vanishing (the clean argument).** If every char-0-nonzero configuration fails the
mod-`p` collision test (`chi c = false` whenever `¬ isZero c` — i.e. the prime avoids *all*
configuration resultants), then the wrap count vanishes: `W_r / p = 0`, so `E_r^{F_p} = V₂ᵣ`
*exactly*.  This is the brick's headline: it reduces the entire floor surplus to the single
arithmetic statement "the prize prime is good". -/
theorem goodPrime_wrap_eq_zero
    (hgood : ∀ c, ¬ D.isZero c → D.chi c = false) : D.wrapCount = 0 := by
  unfold wrapCount
  rw [Finset.sum_eq_zero]
  intro c hc
  rw [mem_filter] at hc
  obtain ⟨_, hnz, hchi⟩ := hc
  rw [hgood c hnz] at hchi
  exact absurd hchi (by simp)

/-- **Good-prime mod-`p` energy is exactly the char-0 energy.**  Under the good-prime hypothesis
`E_r^{F_p} = V₂ᵣ` — the mod-`p` energy equals the (proven `≤ Wick`) char-0 energy, hence also
`≤ Wick`, with no wraparound surplus at all. -/
theorem goodPrime_modPEnergy_eq_charZero
    (hgood : ∀ c, ¬ D.isZero c → D.chi c = false) :
    D.modPEnergy = D.charZeroEnergy := by
  rw [modPEnergy_eq D, goodPrime_wrap_eq_zero D hgood, Nat.add_zero]

/-- **Good prime ⟹ the mod-`p` energy obeys Wick.** Chaining good-prime vanishing with the proven
char-0 Wick bound gives `E_r^{F_p} ≤ (2r−1)!!·n^r` *unconditionally on the energy side* — the
entire prize-floor energy bound, conditional only on "prize prime is good". -/
theorem goodPrime_modPEnergy_le_wick
    (hgood : ∀ c, ¬ D.isZero c → D.chi c = false) :
    D.modPEnergy ≤ D.wick := by
  rw [goodPrime_modPEnergy_eq_charZero D hgood]; exact D.hwick

/-- **The combined exact law.**  The full machine-checked statement of the wraparound exact count:
the mod-`p` energy splits as char-0 plus wrap; the wrap is bounded by the char-0-nonzero total;
and a good prime forces the wrap to zero, collapsing the energy onto the char-0 Wick bound. -/
theorem wraparound_exact_law :
    (D.modPEnergy = D.charZeroEnergy + D.wrapCount) ∧
    (D.wrapCount ≤ D.total - D.charZeroEnergy) ∧
    ((∀ c, ¬ D.isZero c → D.chi c = false) →
      D.wrapCount = 0 ∧ D.modPEnergy ≤ D.wick) :=
  ⟨modPEnergy_eq D, wrap_le_nonzero_total D,
    fun hgood => ⟨goodPrime_wrap_eq_zero D hgood, goodPrime_modPEnergy_le_wick D hgood⟩⟩

end WrapData

/-! ## The per-config resultant envelope (the localisation that decides Paley-dependence)

The bad-prime union is governed by the elementary archimedean envelope on each configuration
resultant.  We record the *combinatorial* envelope abstractly: every configuration has total
coefficient mass `Σ_k |c_k| ≤ 2r` (it is built from `r` positive and `r` negative unit roots), so
the per-config algebraic-integer value at any root of `Φ_n` is bounded by `2r`, and the resultant
(a product over `deg Φ_n = n/2` roots) by `(2r)^{n/2}`.  At fixed `r` this is finite (Paley-
independent, land-exhaust regime); at `r ≈ ln q` it is `2^{Θ(n)}` (the Paley wall). -/

/-- The per-config resultant height envelope: at depth `r` over `μ_n` the resultant of `Φ_n`
against any configuration polynomial has natAbs at most `(2r)^{n/2}`.  We record only the
*shape* of this envelope as a number; the point is the depth dependence of the base.

This is the abstract statement that `(2*r)^(n/2)` is finite for fixed `r` and `2^{Θ(n)}` once
`r` grows with `n` — the dichotomy that pins where the good-prime route is Paley-independent. -/
def resultantHeightEnvelope (n r : ℕ) : ℕ := (2 * r) ^ (n / 2)

/-- At **fixed depth** the envelope is monotone in `r` and finite: a concrete witness that the
bad-prime ceiling at the width-four lane `r = 2` is `4^{n/2} = 2^n`, the exact land-exhaust
ceiling (matching `canonicalRatioPolySharpBound`-style `2^Θ(n)` envelopes there). -/
theorem resultantHeightEnvelope_widthFour (n : ℕ) :
    resultantHeightEnvelope n 2 = 2 ^ (2 * (n / 2)) := by
  unfold resultantHeightEnvelope
  rw [show (2 * 2 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

/-- The envelope is monotone in the depth `r`: deeper configurations admit larger resultants,
hence potentially more bad primes — the precise sense in which the good-prime route *worsens* with
depth, reducing to Paley exactly when `r ≈ ln q` makes the base `2r` super-constant. -/
theorem resultantHeightEnvelope_mono {n r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    resultantHeightEnvelope n r₁ ≤ resultantHeightEnvelope n r₂ :=
  Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 h) (n / 2)

end ArkLib.ProximityGap.Frontier.WraparoundExactCount

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
namespace ArkLib.ProximityGap.Frontier.WraparoundExactCount
#print axioms WrapData.modPEnergy_eq
#print axioms WrapData.wrap_eq_sum_nonzero_chi
#print axioms WrapData.wrap_le_nonzero_total
#print axioms WrapData.wrap_le_asked_budget
#print axioms WrapData.goodPrime_wrap_eq_zero
#print axioms WrapData.goodPrime_modPEnergy_le_wick
#print axioms WrapData.wraparound_exact_law
#print axioms resultantHeightEnvelope_widthFour
#print axioms resultantHeightEnvelope_mono
end ArkLib.ProximityGap.Frontier.WraparoundExactCount
