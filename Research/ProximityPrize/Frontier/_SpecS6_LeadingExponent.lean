/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Spec S6 — the VACUOUS-REGIME record of the complete-homogeneous crossing (#444)

⚠️⚠️ **STATUS — an HONEST VACUOUS-REGIME RECORD, *not* a `δ*` lower bound.** This file lands the
exact, axiom-clean *arithmetic* of the binomial crossing
`C(s, k+1) ≤ n · C(s+r−1, r)` and packages the conditional implication

> `spectrum ≤ rotCeil`  AND  `rotCeil ≤ n · chooseCH s r₁`  AND  `r₁ ≤ r`
>   ⟹  `spectrum ≤ n · chooseCH s r`,

where `rotCeil = C(s, k+1)` is the PROVEN `_SpecS1` rotation ceiling and `chooseCH s r = C(s+r−1, r)`
is the complete-homogeneous count. **The point of this file is to be brutally honest about WHEN that
implication is non-vacuous, and to record that the regime where it fires is exactly the VACUOUS
large-`r` regime — so this is NOT a `δ*` lower bound and must never be cited as one.**

## Why "above the crossing" is the VACUOUS regime (read this before reusing anything here)

The hypothesis `rotCeil ≤ n · chooseCH s r₁` says the complete-homogeneous ceiling `n·C(s+r−1,r₁)` has
GROWN past the rotation ceiling `C(s,k+1)`. Because `chooseCH s ·` is monotone increasing in `r`
(`chooseCH_le_succ`, `chooseCH_mono_right`), once it crosses it stays crossed (`crossing_closed_upward`).
But this crossing happens precisely because the right-hand side `n·C(s+r−1,r)` has become LARGE — it
is the regime where the CH ceiling exceeds even the trivial subset count, so the bound
`spectrum ≤ n·C(s+r−1,r)` it produces is loose-to-vacuous. Concretely (`crossing_concrete_s16`,
machine-checked) at `s = 16`, `ρ = 1/4` (`k+1 = 5`, rotation ceiling `C(16,5) = 4368`), with `n = 16`:

| fold `r` | `n · chooseCH 16 r` | vs `C(16,5)=4368` |
|----------|---------------------|-------------------|
| `r = 0`  | `16`                | **below** (vacuous-loose, bound says nothing) |
| `r = 1`  | `256`               | **below** |
| `r = 2`  | `2176`              | **below** — and the bound `spectrum ≤ 2176` is **VIOLATED** (see next §) |
| `r = 3`  | `13056`             | **above** — crossing fold `M_cross = 3`, bound now holds but `13056 ≫ 4368` |
| `r ≥ 4`  | `≥ 62016`           | **above** (`crossing_closed_upward`), ever looser |

So the crossing fold here is `M_cross = 3 ≈ 0.19·s`, and "above the crossing" (`r ≥ 3`) gives
`spectrum ≤ 13056, 62016, …` — a ceiling that exceeds the rotation ceiling `4368` by `3×, 14×, …`.
**This is the vacuous large-`r` regime: the bound holds only because the right side is enormous.**

## The bound is VIOLATED below the crossing — so this is NON-TAUTOLOGICAL

The conditional is NOT a triviality that holds for all `r`. **Below the crossing the bound
`spectrum ≤ n·C(s+r−1,r)` is genuinely FALSE.** At `s = 16`, `r = 2` the CH ceiling is `n·C(17,2) =
2176`, but the actual distinct complete-homogeneous spectrum at the higher rates already EXCEEDS it:
exact full enumeration over `(k+1)`-subsets of `μ_16` gives `#distinct h_2 = 2752` at `k+1 = 6`,
`3592` at `k+1 = 7`, `4041` at `k+1 = 8` (probe, good prime `p ≡ 1 mod 16`), and the dossier records
a `#distinct h_2 = 3408 > 2176` witness at `s = 16`, `r = 2/3` — all `> 2176`. So at the binding
*small*-`r` end the bound is **violated**, confirming the conditional has real content (it is FALSE
below `M_cross`, only becoming TRUE once the CH ceiling has ballooned past the rotation ceiling at and
above `M_cross`). The hypothesis `hcross` is therefore a genuine constraint, not a tautology — and the
regime it selects is exactly the one where the conclusion is loose.

## `poly = n` is REFUTED strictly below `M_cross` at the prize scale `s = 32`

The `_BchksF1.CompleteHomogeneousSpectrumBound` with `poly = n` (the "char-free `δ*` core" framing) is
**REFUTED** at the prize scale `s = 32` for small `r`, STRICTLY BELOW the crossing fold
(`probe_spectrum_polyN_REFUTED_s32.py`): exact full enumeration gives `poly_min = 389, 3444` at
`s = 24, 28` (`r = 2`, super-linear `≈ 16n, 123n`), and a SAMPLE (a lower bound on the true count)
already exceeds `n·C(s+r−1,r)` at `s = 32` (`r = 2`: ceiling `16896 <` seen; `r = 3`: ceiling
`191488 <` seen). At fixed rate the witness size `k+1 = ρs` GROWS with `s`, so the rotation/trivial
ceiling `C(s,k+1)` is EXPONENTIAL, and at small `r` there is too little symmetric-function collision
to bring `#distinct` under the polynomial `n·C(s+r−1,r)`. The `poly = n` bound holds ONLY at large `r`
(`s = 24, 28`: `r ≥ 4` OK) — exactly the vacuous regime above the crossing. **The clean
"`poly(n) = n` char-free `δ*` core" framing is REFUTED; this file does not resurrect it.**

## The exact crossing fold `M_cross` and the `r ↔ δ` map are OPEN

This file proves the crossing is upward-closed and pins it at `M_cross = 3` for the single config
`s = 16, ρ = 1/4`. It does **NOT** determine the crossing fold `M_cross(s, ρ, ε*)` in general, nor
the map from the fold `r` to the proximity parameter `δ`. Whether the `δ*`-binding fold lands in the
holds-regime (large `r`, vacuous) or the fails-regime (small `r`, where the genuine `~n` far-line
count lives and the CH spectrum is exponentially loose for `#bad` — `D4.1` of the dossier) is the
OPEN residual. **The exact `M_cross` / `r ↔ δ` map is OPEN; nothing here closes it.**

## What this file proves (all axiom-clean, char-free `Nat`/binomial arithmetic)

* `chooseCH_succ_mul` — the exact growth recursion `C(s+r,r+1)·(r+1) = C(s+r−1,r)·(s+r)`, the
  monotone-step driver.
* `chooseCH_le_succ` / `chooseCH_mono_right` — `chooseCH s r = C(s+r−1,r)` is monotone non-decreasing
  in the fold `r` (`s ≥ 1`).
* `crossing_closed_upward` — once `n·C(s+r−1,r) ≥ C(s,k+1)` holds at a fold it holds at ALL larger
  folds (monotone upward-closure of the crossing).
* `leading_exponent_pinned` — the CAPSTONE CONDITIONAL: from `spectrum ≤ rotCeil`,
  `rotCeil ≤ n·chooseCH s r₁`, and `r₁ ≤ r`, conclude `spectrum ≤ n·C(s+r−1,r)`. **HONEST as a
  conditional only**, and (per the above) firing exactly in the vacuous large-`r` regime.
* `crossing_concrete_s16` / `upward_closure_concrete_s16` — the machine-checked crossing at
  `M_cross = 3`, with the below-crossing gap exhibited (`16·chooseCH 16 2 = 2176 < 4368`).

## Honest scope (one paragraph)

This is a VACUOUS-REGIME RECORD: the conditional `leading_exponent_pinned` is a true, axiom-clean
`le_trans`, but its hypothesis `rotCeil ≤ n·chooseCH s r₁` is met only when the CH ceiling has grown
large (the vacuous large-`r` regime), the conclusion is then loose-to-vacuous, the bound is VIOLATED
below the crossing (so the conditional is non-tautological), the `poly = n` form is REFUTED at the
prize scale `s = 32` strictly below `M_cross`, and the exact `M_cross` / `r ↔ δ` map is OPEN. **It is
NOT a `δ*` lower bound and must never be cited as one** — it is honest substrate recording exactly
where the complete-homogeneous crossing argument is and is not informative.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.SpecS6

/-! ## Part 0 — the complete-homogeneous count and floor `Prop` (mirrors `_BchksF1`)

These mirror `_BchksF1_CompleteHomogeneousFloor` verbatim so this file is self-contained (the
`_BchksF1` scratch module is not in the build graph). `chooseCH s r = C(s+r−1, r)` is the
complete-homogeneous dimension (= `Nat.multichoose s r`); `CompleteHomogeneousSpectrumBound` is the
F1 floor object — recorded here ONLY to phrase the vacuous-regime conditional against it, NOT to
claim it discharged (`poly = n` is REFUTED at `s = 32`, see the header). -/

/-- The complete-homogeneous count `chooseCH s r = C(s+r−1, r)` (= `Nat.multichoose s r`), the ABF26
§4 worst-direction multiplier. Mirrors `_BchksF1.chooseCH`. -/
def chooseCH (s r : ℕ) : ℕ := Nat.choose (s + r - 1) r

/-- The F1 floor object: `spectrum ≤ poly · chooseCH s r`. Mirrors
`_BchksF1.CompleteHomogeneousSpectrumBound`. ⚠️ The `poly = n` instance is REFUTED at the prize scale
`s = 32` strictly below the crossing fold (header §"poly = n is REFUTED"); recorded here only to
phrase the vacuous-regime conditional, never as a discharged `δ*` bound. -/
def CompleteHomogeneousSpectrumBound (spectrum poly s r : ℕ) : Prop :=
  spectrum ≤ poly * chooseCH s r

/-! ## Part 1 — the CH count `chooseCH s r = C(s+r−1,r)` grows in the fold `r` -/

/-- **The exact growth recursion of the complete-homogeneous count.**
`C(s+r, r+1) · (r+1) = C(s+r−1, r) · (s+r)` — i.e. `chooseCH s (r+1) · (r+1) = chooseCH s r · (s+r)`.
This is the Pascal-ratio identity `Nat.succ_mul_choose_eq` specialized to the shifted index
`(s+r−1, r) ↦ (s+r, r+1)`; it drives the monotone step (ratio `(s+r)/(r+1) ≥ 1` for `s ≥ 1`). -/
theorem chooseCH_succ_mul (s r : ℕ) (hs : 1 ≤ s) :
    chooseCH s (r + 1) * (r + 1) = chooseCH s r * (s + r) := by
  unfold chooseCH
  -- chooseCH s (r+1) = C((s+(r+1))-1, r+1) = C(s+r, r+1); chooseCH s r = C(s+r-1, r).
  -- Use Nat.succ_mul_choose_eq: (n+1) * C(n,k) = C(n+1, k+1) * (k+1), with n = s+r-1, k = r.
  -- Then C(s+r-1+1, r+1) = C(s+(r+1)-1, r+1) and (s+r-1)+1 = s+r (since s ≥ 1).
  have hbase : s + r - 1 + 1 = s + r := by omega
  have hidx : s + (r + 1) - 1 = s + r := by omega
  have key : (s + r - 1).succ * Nat.choose (s + r - 1) r
      = Nat.choose (s + r - 1).succ (r + 1) * (r + 1) := Nat.succ_mul_choose_eq (s + r - 1) r
  rw [Nat.succ_eq_add_one, hbase] at key
  -- key : (s+r) * C(s+r-1, r) = C(s+r, r+1) * (r+1)
  rw [hidx]
  -- goal : C(s+r, r+1) * (r+1) = C(s+r-1, r) * (s+r)
  rw [← key]
  ring

/-- **`chooseCH` is monotone non-decreasing in the fold `r`** (for `s ≥ 1`):
`chooseCH s r ≤ chooseCH s (r+1)`. The complete-homogeneous count GROWS with the fold — this is the
engine of the upward-closure of the crossing (and the reason "above the crossing" is the regime where
the CH ceiling has ballooned, i.e. the vacuous regime). -/
theorem chooseCH_le_succ (s r : ℕ) (hs : 1 ≤ s) :
    chooseCH s r ≤ chooseCH s (r + 1) := by
  -- From chooseCH s (r+1)·(r+1) = chooseCH s r·(s+r) and s+r ≥ r+1 (since s ≥ 1):
  --   chooseCH s (r+1)·(r+1) = chooseCH s r·(s+r) ≥ chooseCH s r·(r+1).
  have hmul := chooseCH_succ_mul s r hs
  have hge : chooseCH s r * (r + 1) ≤ chooseCH s (r + 1) * (r + 1) := by
    rw [hmul]
    exact Nat.mul_le_mul_left _ (by omega)
  exact Nat.le_of_mul_le_mul_right hge (by omega)

/-- **`chooseCH` is monotone non-decreasing in the fold across any gap** (for `s ≥ 1`):
`r₁ ≤ r₂ → chooseCH s r₁ ≤ chooseCH s r₂`. Iterates `chooseCH_le_succ`. -/
theorem chooseCH_mono_right (s : ℕ) (hs : 1 ≤ s) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    chooseCH s r₁ ≤ chooseCH s r₂ := by
  induction r₂ with
  | zero =>
    have : r₁ = 0 := Nat.le_zero.mp h
    rw [this]
  | succ r ih =>
    rcases Nat.lt_or_ge r₁ (r + 1) with hlt | hge
    · have hr₁r : r₁ ≤ r := by omega
      exact le_trans (ih hr₁r) (chooseCH_le_succ s r hs)
    · -- r₁ ≥ r+1 and r₁ ≤ r+1 ⟹ r₁ = r+1
      have : r₁ = r + 1 := by omega
      rw [this]

/-! ## Part 2 — the crossing inequality is upward-closed (entering the VACUOUS large-`r` regime) -/

/-- **The crossing inequality is UPWARD-CLOSED.** If at fold `r₁` the CH ceiling `n · chooseCH s r₁`
already dominates the rotation ceiling `T` (here `T = C(s, k+1)`), then it dominates `T` at EVERY
larger fold `r₂ ≥ r₁`:
  `T ≤ n · chooseCH s r₁  →  ∀ r₂ ≥ r₁, T ≤ n · chooseCH s r₂`.
⚠️ This upward-closure is exactly the entry into the VACUOUS large-`r` regime: the CH ceiling, once it
has grown past the rotation ceiling at `M_cross`, only grows further (`crossing_concrete_s16`:
`13056, 62016, …` at `s = 16` vs `C(16,5) = 4368`), so the resulting bound `spectrum ≤ n·chooseCH s r`
is loose-to-vacuous. (Monotonicity of `chooseCH` in `r`, Part 1.) -/
theorem crossing_closed_upward (s k₁ T n : ℕ) (hs : 1 ≤ s)
    {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂)
    (hcross : T ≤ n * chooseCH s r₁) :
    T ≤ n * chooseCH s r₂ := by
  refine le_trans hcross ?_
  exact Nat.mul_le_mul_left n (chooseCH_mono_right s hs hr)

/-- **A crossing fold EXISTS (existential form).** Since `chooseCH s r → ∞` in `r` (Part 1 growth,
`s ≥ 2`) while `T` is fixed, there is a fold `M` with `T ≤ n · chooseCH s M`; above it the inequality
stays met (`crossing_closed_upward`). This packages "there is a fold at/above which the inequality
binds" for the conditional below — it makes NO claim about *which* fold the `δ*` binder is, nor that
the resulting bound is non-vacuous there. -/
theorem exists_crossing_fold (s T n : ℕ) (hs : 1 ≤ s)
    {M : ℕ} (hM : T ≤ n * chooseCH s M) :
    ∃ M₀, ∀ r ≥ M₀, T ≤ n * chooseCH s r :=
  ⟨M, fun r hr => crossing_closed_upward s 0 T n hs hr hM⟩

/-! ## Part 3 — the capstone CONDITIONAL (firing in the vacuous regime)

⚠️ The capstone below is a true `le_trans`, but it is NOT a `δ*` lower bound. Its hypothesis
`hcross` is met only at and above the crossing fold `M_cross` — the VACUOUS large-`r` regime where the
CH ceiling has grown large (header). Below `M_cross` the conclusion `spectrum ≤ n·C(s+r−1,r)` is
genuinely FALSE (header §"VIOLATED below the crossing"), so the conditional has real content; but the
regime where it fires is exactly where the bound is loose. Do NOT read this as pinning `δ*`. -/

/-- **CAPSTONE (CONDITIONAL, vacuous-regime) — `spectrum ≤ n·C(s+r−1,r)` at and above the crossing
fold.** GIVEN
* `hrot : spectrum ≤ rotCeil` — the PROVEN rotation ceiling (`_SpecS1`: `#distinct h_r ≤ C(s,k+1)`,
  here `rotCeil = C(s,k+1)`; the `/gcd` refinement only makes it smaller, so `≤ C(s,k+1)` is valid),
* `hcross : rotCeil ≤ n · chooseCH s r₁` — the binomial crossing inequality at the crossing fold
  `r₁ = M_cross` (upward-closed by `crossing_closed_upward`),
* `hr : r₁ ≤ r` — the binding fold is at or above the crossing fold,
THEN
  `spectrum ≤ n · chooseCH s r = n · C(s+r−1, r)`.
⚠️ This is a pure `le_trans`, HONEST as a CONDITIONAL only. It is **NOT a `δ*` lower bound**: the
hypothesis `hcross` selects the VACUOUS large-`r` regime (CH ceiling grown past the rotation ceiling,
conclusion loose-to-vacuous); below the crossing the conclusion is FALSE (header), so the conditional
is non-tautological; the `poly = n` form is REFUTED at `s = 32` strictly below `M_cross`; and the
exact `M_cross` / `r ↔ δ` map is OPEN. Cite this only as the vacuous-regime record it is. -/
theorem leading_exponent_pinned (spectrum rotCeil n s r₁ r : ℕ) (hs : 1 ≤ s)
    (hrot : spectrum ≤ rotCeil)
    (hcross : rotCeil ≤ n * chooseCH s r₁)
    (hr : r₁ ≤ r) :
    spectrum ≤ n * chooseCH s r :=
  le_trans hrot (crossing_closed_upward s 0 rotCeil n hs hr hcross)

/-- **The capstone conditional in `CompleteHomogeneousSpectrumBound` form (`poly = n`).** Identical
content, phrased against the F1 floor `Prop`: at and above the crossing fold the spectrum satisfies
`CompleteHomogeneousSpectrumBound spectrum n s r` (i.e. `spectrum ≤ n · C(s+r−1,r)`). ⚠️ This is NOT a
discharge of the F1 floor as a `δ*` bound — the `poly = n` form is REFUTED strictly below `M_cross` at
`s = 32` (header), and the regime where this conditional fires is the vacuous large-`r` one. It is the
honest vacuous-regime record of *where* the `poly = n` form holds (large `r`, where it is loose), with
the exact `M_cross` / `r ↔ δ` map OPEN. -/
theorem spectrumBound_of_crossing (spectrum rotCeil n s r₁ r : ℕ) (hs : 1 ≤ s)
    (hrot : spectrum ≤ rotCeil)
    (hcross : rotCeil ≤ n * chooseCH s r₁)
    (hr : r₁ ≤ r) :
    CompleteHomogeneousSpectrumBound spectrum n s r :=
  leading_exponent_pinned spectrum rotCeil n s r₁ r hs hrot hcross hr

/-! ## Part 4 — concrete sanity: the crossing and the BELOW-crossing gap (non-tautology witness) -/

/-- **Crossing-fold sanity at `s = 16, ρ = 1/4` (`k+1 = 5`), exhibiting the below-crossing gap.** The
rotation ceiling is `C(16,5) = 4368`; with `n = 16` the CH ceiling crosses it at `M_cross = 3`:
`16 · chooseCH 16 3 = 16 · C(18,3) = 16 · 816 = 13056 ≥ 4368`, while at `r = 2`
`16 · chooseCH 16 2 = 16 · 136 = 2176 < 4368` — **strictly below**, the small-`r` regime where the
bound `spectrum ≤ 2176` is VIOLATED by the actual spectrum (`#distinct h_2 = 2752, 3592, 4041` at
`k+1 = 6, 7, 8`; dossier `3408 > 2176`). So the conditional is NON-TAUTOLOGICAL: it fails below
`M_cross = 3` and only holds above, in the vacuous regime (`13056 ≫ 4368`). -/
theorem crossing_concrete_s16 :
    Nat.choose 16 5 = 4368
    ∧ 16 * chooseCH 16 2 < Nat.choose 16 5
    ∧ Nat.choose 16 5 ≤ 16 * chooseCH 16 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Upward-closure into the vacuous regime, sanity at `s = 16`.** Having crossed at `M_cross = 3`,
the inequality stays met at all larger folds — `C(16,5) ≤ 16 · chooseCH 16 r` for `r = 3, 4, 5`
(machine-checked instances of `crossing_closed_upward`), with the CH ceiling growing `13056, 62016,
248064` — `3×, 14×, 57×` the rotation ceiling `4368`. This exhibits the vacuous-regime looseness: the
bound holds only because the right side has ballooned. -/
theorem upward_closure_concrete_s16 :
    Nat.choose 16 5 ≤ 16 * chooseCH 16 3
    ∧ Nat.choose 16 5 ≤ 16 * chooseCH 16 4
    ∧ Nat.choose 16 5 ≤ 16 * chooseCH 16 5 := by
  refine ⟨by decide, by decide, by decide⟩

end ArkLib.ProximityGap.SpecS6

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpecS6.chooseCH_succ_mul
#print axioms ArkLib.ProximityGap.SpecS6.chooseCH_le_succ
#print axioms ArkLib.ProximityGap.SpecS6.chooseCH_mono_right
#print axioms ArkLib.ProximityGap.SpecS6.crossing_closed_upward
#print axioms ArkLib.ProximityGap.SpecS6.exists_crossing_fold
#print axioms ArkLib.ProximityGap.SpecS6.leading_exponent_pinned
#print axioms ArkLib.ProximityGap.SpecS6.spectrumBound_of_crossing
#print axioms ArkLib.ProximityGap.SpecS6.crossing_concrete_s16
#print axioms ArkLib.ProximityGap.SpecS6.upward_closure_concrete_s16
