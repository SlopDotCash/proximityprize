/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Bchks F1 — the char-free Sumset-Extremality floor, QUANTITATIVELY encoded (#444)

The genuine open core of the `δ*` floor: bound the worst far-line bad-scalar count by the
**complete-homogeneous** count, char-free. The F3/F6 verify correctly flagged that the earlier
`SumsetExtremality` Prop, with free binders, COLLAPSES to "the cascade binds at fold M_cross" — the
quantitative `C(s+r−1,r)` content was not encoded. This file fixes that: it defines the SPECIFIC
multiplier `chooseCH s r = C(s+r−1, r)` and states the floor against it, so `M_cross` becomes the
genuine complete-homogeneous crossing — and isolates the ONE open distinct-value count.

## The structure (ABF26 §4 + in-tree SchurLagrangeBridge)

At the minimal witness `|R| = k+1`, the unique parity-check is the divided-difference functional, and
the forced bad scalar of the far pencil `(x^a, x^b)` over the `(k+1)`-subset `R ⊆ μ_s` is
  `γ_R = − h_{a−k}(R) / h_{b−k}(R)`,
where `h_d` is the COMPLETE-HOMOGENEOUS symmetric polynomial of degree `d` in the nodes `R`
(`SchurLagrangeBridge.dividedDifferencePow_eq_schurH`). The distinct bad count `#bad` (the worst
monomial direction's `D*(1)`) is therefore `≤ #{distinct h_{a−k}(R) : R ∈ binom(μ_s, k+1)}` — the
**complete-homogeneous spectrum size**. ABF26: this spectrum is bounded by `C(s+r−1, r)` (the
dimension of the degree-`r` complete-homogeneous space), STRICTLY larger than the subset-sum
`C(s, r)` (whence the refuted-Kambiré gap).

## What this file proves (char-free)

* `chooseCH` arithmetic: `chooseCH s r = C(s+r−1, r)`, monotone, `chooseCH s r ≥ C(s, r)` (the
  complete-homogeneous DOMINATES the subset-sum — the precise sense in which Kambiré's ceiling is not
  tight), all axiom-clean.
* `bad_le_chooseCH_of_spectrum` — the floor REDUCED to the ONE open input
  `CompleteHomogeneousSpectrumBound`: `#{distinct h_d-values over (k+1)-subsets} ≤ chooseCH s r`.
  This is the genuine char-free open core; everything else is discharged.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF1

/-- **The complete-homogeneous count** `chooseCH s r = C(s+r−1, r)` — the number of degree-`r`
monomials in `s` variables (= dim of the degree-`r` complete-homogeneous space = #multisets of size
`r` from `s` elements). This is the ABF26 §4 worst-direction multiplier (NOT the subset-sum
`C(s,r)`). -/
def chooseCH (s r : ℕ) : ℕ := Nat.choose (s + r - 1) r

@[simp] theorem chooseCH_zero (s : ℕ) : chooseCH s 0 = 1 := by
  simp [chooseCH]

theorem chooseCH_one {s : ℕ} (hs : 1 ≤ s) : chooseCH s 1 = s := by
  simp only [chooseCH]
  rw [show s + 1 - 1 = s from by omega, Nat.choose_one_right]

/-- **The complete-homogeneous count DOMINATES the subset-sum count:** `C(s, r) ≤ chooseCH s r`.
This is the exact sense in which the Kambiré subset-sum ceiling is NOT tight — the
complete-homogeneous worst direction realizes at least as many bad scalars. -/
theorem subsetSum_le_chooseCH (s r : ℕ) : Nat.choose s r ≤ chooseCH s r := by
  unfold chooseCH
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; rw [Nat.choose_eq_zero_of_lt hr]; exact Nat.zero_le _
    · exact Nat.choose_le_choose r (by omega)

/-! ## The F1 floor, reduced to the ONE open distinct-value count -/

/-- **The complete-homogeneous spectrum bound — a conditional REDUCTION target, with the `poly`
factor left as a free binder.** The number of distinct degree-`r` complete-homogeneous values
`h_r(R)` over the `(k+1)`-subsets `R ⊆ μ_s` is at most `poly · chooseCH s r` (the ABF26 §4
sumset-extremality content). This is a `Prop` parameterized by `poly`; the theorem below uses it
purely as a hypothesis (`le_trans`), so it is HONEST as a conditional regardless of what `poly` is.

⚠️ **`poly = 1` is FALSE** (`#distinct h_2(μ_16)=1848 > C(17,2)=136`,
`probe_completehomog_spectrum.py`). ⚠️⚠️ **`poly(n) = n` is ALSO FALSE at the prize scale
[REFUTED, `probe_spectrum_polyN_REFUTED_s32.py`].** The earlier "poly=n SUFFICES" claim was tested
ONLY at `s = 8, 16`; extending to the next power of two `s = 32` (the prize is `s = 2^μ`) the bound
FAILS at small `r`: exact full-enumeration gives `poly_min = 389, 3444` at `s = 24, 28` (`r = 2`,
super-linear `≈16n, 123n`), and a SAMPLE (which only lower-bounds the true count) already exceeds
`n·C(s+r−1,r)` at `s = 32` (`r = 2`: ceil `16896` < seen; `r = 3`: ceil `191488` < seen). At fixed
rate the witness size `k+1 = ρs` GROWS, so the trivial ceiling `C(s,k+1)` is EXPONENTIAL, and at
small `r` there is too little symmetric-function collision to bring it under the polynomial
`n·C(s+r−1,r)`. The bound DOES hold at LARGE `r` (`s = 24, 28`: `r ≥ 4` OK) — it is a small-`r`
phenomenon. **The honest open question is whether the δ*-binding fold `r = M_cross` lies in the
holds-regime (large `r`) or the fails-regime (small `r`); the clean "poly(n)=n char-free core"
framing is REFUTED.** The genuinely PROVABLE bound is the rotation/trivial one
`#distinct ≤ C(s,k+1)/gcd(s,r)` (exponential — see `_SpecS1_RotationEquivariance`). -/
def CompleteHomogeneousSpectrumBound (spectrum poly s r : ℕ) : Prop :=
  spectrum ≤ poly * chooseCH s r

/-- **F1 — the char-free floor, REDUCED to the (free-`poly`) spectrum bound.** GIVEN (a)
`hbad : bad ≤ spectrum` (SchurLagrangeBridge forced-γ = `−h_{a−k}/h_{b−k}`: distinct γ ≤ distinct
`h`-values), and (b) `CompleteHomogeneousSpectrumBound spectrum poly s r`, the bad count obeys
`bad ≤ poly · chooseCH s r` with the SPECIFIC multiplier `chooseCH = C(s+r−1,r)`. This is a pure
`le_trans` — HONEST as a conditional for ANY `poly`. ⚠️ It does NOT assert `poly = n`: that is
REFUTED at `s = 32` (see `CompleteHomogeneousSpectrumBound` docstring + `probe_spectrum_polyN_REFUTED_s32.py`).
The quantitative content of (b) — what `poly` actually is at the binding fold, hence whether this
yields a poly(n) δ* correction — is OPEN, not discharged. -/
theorem bad_le_chooseCH_of_spectrum (bad spectrum poly s r : ℕ)
    (hbad : bad ≤ spectrum)
    (hspec : CompleteHomogeneousSpectrumBound spectrum poly s r) :
    bad ≤ poly * chooseCH s r :=
  le_trans hbad hspec

/-- **Sanity (the multiplier is the SPECIFIC complete-homogeneous count, not a free binder).** At
`s = 8, r = 3` the ceiling is `chooseCH 8 3 = C(10,3) = 120`, strictly above the subset-sum
`C(8,3) = 56` — the quantitative Kambiré-not-tight gap, machine-checked. -/
theorem chooseCH_concrete : chooseCH 8 3 = 120 ∧ Nat.choose 8 3 = 56 ∧ Nat.choose 8 3 < chooseCH 8 3 := by
  refine ⟨by decide, by decide, by decide⟩

end ArkLib.ProximityGap.BchksF1

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BchksF1.subsetSum_le_chooseCH
#print axioms ArkLib.ProximityGap.BchksF1.bad_le_chooseCH_of_spectrum
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_concrete
