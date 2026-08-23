/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Fold transport of the KKH26 bad line (#357 R2): the trichotomy

The KKH26 near-capacity bad family for smooth-domain RS codes
(`KKH26BadLineConstruction.lean`) is the monomial stack `(u₀, u₁) = (X^{rm}, X^{(r−1)m})` on
`H = ⟨g⟩`, `|H| = s·m`, `s = 2^μ`, with bad scalars `λ_S = −∑_{a∈S} a` over `r`-subsets `S` of
the inner group `G = ⟨g^m⟩`. The FRI fold maps words on `H` to words on `H² = ⟨g²⟩` via
`f ↦ f_e + β·f_o` (even/odd split, folding challenge `β`). **R2 of the #357 campaign asked
whether the family is fold-covariant.** The answer, probe-verified at p = 97 and proven here,
is a sharp trichotomy:

1. **`m` even (m-tower steps): exact covariance, `β`-free.**
   `fold_β(X^{rm}) = Y^{r(m/2)}` and `fold_β(X^{(r−1)m}) = Y^{(r−1)(m/2)}`
   (`kkh26_fold_m_even`) — the folded stack *is* the KKH26 stack at `(s, m/2, r)`; and the
   inner group is *literally unchanged*: `(g²)^{m/2} = g^m` (`sq_pow_half`), so the
   bad-scalar census is the same set of field elements. The fold does **not** shrink the
   census along m-steps; the census-extremality direction survives (the mutually-falsifying
   pairing of the campaign dossier).

2. **`m = 1`, `r` even (s-steps): structural halving.**
   `fold_β(X^r, X^{r−1}) = (Z^{r/2}, β·Z^{r/2−1})` (`kkh26_fold_s_step_r_even`) — a β-scaled
   KKH26 stack at `(s/2, 1, r/2)` (the scaling is census-neutral by
   `MCAEquivariance.prob_mcaEvent_smul_right`). The construction-class supply drops
   `2^r·C(s/2,r) → 2^{r/2}·C(s/4,r/2)` per s-step.

3. **`m = 1`, `r` odd (s-steps): total collapse.**
   Both rows fold to multiples of *one* monomial, and the whole folded line is the pencil
   `(β + λ)·Z^{(r−1)/2}` (`kkh26_fold_line_collapse`): the census collapses to a single
   scalar (probe: 40 → 1 at every β).

**Consequence.** The KKH26 ceiling is μ-uniform along the m-half of the smooth tower with an
*identical* census, and the entire decay of this construction class concentrates at the
s-steps (exact halving for even `r`, instant death for odd `r`). Any fold-based protocol
argument crossing one s-step strictly escapes the KKH26 construction class.

The fold is formalized pointwise: `foldAt f β x` is the value of the folded word at `y = x²`,
defined for `x ≠ 0` over any field of characteristic `≠ 2` (both hypotheses explicit).

Everything is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- [KKH26] ePrint 2026/782 (the bad-line construction; `KKH26BadLineConstruction.lean`).
- Issue #357 (R2 in the campaign dossier); probe `p = 97` data in the R2 verdict comment.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.KKH26FoldTransport

variable {F : Type*} [Field F]

/-- The FRI fold of a word `f`, evaluated at the point lying over `y = x²`: the even part
plus `β` times the odd part, `f_e(x²) + β·f_o(x²)`. -/
noncomputable def foldAt (f : F → F) (β x : F) : F :=
  (f x + f (-x)) / 2 + β * ((f x - f (-x)) / (2 * x))

/-- The fold is additive in the word. -/
theorem foldAt_add (f g : F → F) (β x : F) :
    foldAt (fun t => f t + g t) β x = foldAt f β x + foldAt g β x := by
  unfold foldAt
  ring

/-- The fold is homogeneous in the word. -/
theorem foldAt_smul (c : F) (f : F → F) (β x : F) :
    foldAt (fun t => c * f t) β x = c * foldAt f β x := by
  unfold foldAt
  ring

/-- **Even monomials fold β-freely:** `fold_β(X^d) = Y^{d/2}` at `y = x²` for `2 ∣ d`. -/
theorem foldAt_monomial_even {d : ℕ} (hd : 2 ∣ d) (h2 : (2 : F) ≠ 0) (β : F) {x : F}
    (hx : x ≠ 0) : foldAt (fun t => t ^ d) β x = (x ^ 2) ^ (d / 2) := by
  obtain ⟨e, rfl⟩ := hd
  have hneg : (-x) ^ (2 * e) = (x ^ 2) ^ e := by
    rw [pow_mul, neg_sq]
  have hpos : x ^ (2 * e) = (x ^ 2) ^ e := by
    rw [pow_mul]
  have hdiv : 2 * e / 2 = e := Nat.mul_div_cancel_left e (by norm_num)
  simp only [foldAt]
  rw [hneg, hpos, hdiv]
  field_simp
  ring

/-- **Odd monomials fold to β times the half monomial:** `fold_β(X^d) = β·Y^{d/2}` at
`y = x²` for odd `d` (`d/2 = (d−1)/2` in ℕ). -/
theorem foldAt_monomial_odd {d : ℕ} (hd : ¬ 2 ∣ d) (h2 : (2 : F) ≠ 0) (β : F) {x : F}
    (hx : x ≠ 0) : foldAt (fun t => t ^ d) β x = β * (x ^ 2) ^ (d / 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e + 1 := ⟨d / 2, by omega⟩
  have hneg : (-x) ^ (2 * e + 1) = -((x ^ 2) ^ e * x) := by
    rw [pow_succ, pow_mul, neg_sq, neg_mul_eq_mul_neg]
  have hpos : x ^ (2 * e + 1) = (x ^ 2) ^ e * x := by
    rw [pow_succ, pow_mul]
  have hdiv : (2 * e + 1) / 2 = e := by omega
  simp only [foldAt]
  rw [hneg, hpos, hdiv]
  field_simp
  ring

/-! ## Regime 1 — `m` even: exact covariance, identical census -/

/-- **The m-step covariance (word level).** For even `m`, the KKH26 stack folds, at every
challenge `β`, to *exactly* the KKH26 stack of the next tower level `(s, m/2, r)`:
`fold_β(X^{rm}) = Y^{r·(m/2)}` and `fold_β(X^{(r−1)m}) = Y^{(r−1)·(m/2)}`. -/
theorem kkh26_fold_m_even {r m : ℕ} (hm : 2 ∣ m) (h2 : (2 : F) ≠ 0) (β : F) {x : F}
    (hx : x ≠ 0) :
    foldAt (fun t => t ^ (r * m)) β x = (x ^ 2) ^ (r * (m / 2)) ∧
      foldAt (fun t => t ^ ((r - 1) * m)) β x = (x ^ 2) ^ ((r - 1) * (m / 2)) := by
  obtain ⟨e, rfl⟩ := hm
  constructor
  · rw [foldAt_monomial_even ⟨r * e, by ring⟩ h2 β hx]
    congr 1
    rw [show r * (2 * e) = 2 * (r * e) by ring,
      Nat.mul_div_cancel_left (r * e) (by norm_num : 0 < 2),
      Nat.mul_div_cancel_left e (by norm_num : 0 < 2)]
  · rw [foldAt_monomial_even ⟨(r - 1) * e, by ring⟩ h2 β hx]
    congr 1
    rw [show (r - 1) * (2 * e) = 2 * ((r - 1) * e) by ring,
      Nat.mul_div_cancel_left ((r - 1) * e) (by norm_num : 0 < 2),
      Nat.mul_div_cancel_left e (by norm_num : 0 < 2)]

/-- **The m-step census invariance (group level).** The inner group generator is literally
unchanged by the fold: `(g²)^{m/2} = g^m` for even `m`. Hence `G = ⟨g^m⟩` — and with it the
entire KKH26 bad-scalar supply `{−∑_{a∈S} a : S ⊆ G, |S| = r}` — is the *same set of field
elements* at the folded level `(⟨g²⟩, m/2)` as at `(⟨g⟩, m)`. -/
theorem sq_pow_half {M : Type*} [Monoid M] (g : M) {m : ℕ} (hm : 2 ∣ m) :
    (g ^ 2) ^ (m / 2) = g ^ m := by
  rw [← pow_mul, Nat.mul_div_cancel' hm]

/-- The census-supply transport, in the explicit `Finset` form used by
`kkh26_badline_closePoints`: the inner-group enumeration at the folded level coincides
verbatim. -/
theorem kkh26_inner_group_fold_invariant [DecidableEq F] {s m : ℕ} (g : F) (hm : 2 ∣ m) :
    (Finset.range s).image (fun i => ((g ^ 2) ^ (m / 2)) ^ i)
      = (Finset.range s).image (fun i => (g ^ m) ^ i) := by
  rw [sq_pow_half g hm]

/-! ## Regime 2 — `m = 1`, `r` even: structural halving -/

/-- **The s-step halving (word level).** At the bottom of the m-tower (`m = 1`) with even
`r`, the KKH26 stack folds to the **β-scaled** KKH26 stack of `(s/2, 1, r/2)`:
`fold_β(X^r) = Z^{r/2}` and `fold_β(X^{r−1}) = β·Z^{r/2−1}`. (The β-scaling of the direction
row is census-neutral by `MCAEquivariance.prob_mcaEvent_smul_right`.) -/
theorem kkh26_fold_s_step_r_even {r : ℕ} (hr : 2 ∣ r) (hr2 : 2 ≤ r) (h2 : (2 : F) ≠ 0)
    (β : F) {x : F} (hx : x ≠ 0) :
    foldAt (fun t => t ^ r) β x = (x ^ 2) ^ (r / 2) ∧
      foldAt (fun t => t ^ (r - 1)) β x = β * (x ^ 2) ^ (r / 2 - 1) := by
  constructor
  · exact foldAt_monomial_even hr h2 β hx
  · rw [foldAt_monomial_odd (by omega) h2 β hx]
    congr 2
    omega

/-! ## Regime 3 — `m = 1`, `r` odd: total collapse -/

/-- **The s-step collapse (word level).** At `m = 1` with odd `r`, both rows fold to
multiples of the *same* monomial: `fold_β(X^r) = β·Z^{(r−1)/2}` and
`fold_β(X^{r−1}) = Z^{(r−1)/2}`. -/
theorem kkh26_fold_s_step_r_odd {r : ℕ} (hr : ¬ 2 ∣ r) (hr1 : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (β : F) {x : F} (hx : x ≠ 0) :
    foldAt (fun t => t ^ r) β x = β * (x ^ 2) ^ (r / 2) ∧
      foldAt (fun t => t ^ (r - 1)) β x = (x ^ 2) ^ (r / 2) := by
  constructor
  · exact foldAt_monomial_odd hr h2 β hx
  · rw [foldAt_monomial_even (by omega) h2 β hx]
    congr 1
    omega

/-- **The pencil collapse.** At `m = 1`, odd `r`, the *entire folded KKH26 line* degenerates
to the one-monomial pencil: `fold_β(X^r + λ·X^{r−1}) = (β + λ)·Z^{(r−1)/2}` — so at most one
folded line point (namely `λ = −β`, the zero word) can be better than the single monomial
allows, and the bad-scalar census collapses (probe: 40 → 1 at every β). -/
theorem kkh26_fold_line_collapse {r : ℕ} (hr : ¬ 2 ∣ r) (hr1 : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (β lam : F) {x : F} (hx : x ≠ 0) :
    foldAt (fun t => t ^ r + lam * t ^ (r - 1)) β x = (β + lam) * (x ^ 2) ^ (r / 2) := by
  rw [foldAt_add (fun t => t ^ r) (fun t => lam * t ^ (r - 1)) β x,
    foldAt_smul lam (fun t => t ^ (r - 1)) β x,
    (kkh26_fold_s_step_r_odd hr hr1 h2 β hx).1,
    (kkh26_fold_s_step_r_odd hr hr1 h2 β hx).2]
  ring

/-- The fold of the full KKH26 line commutes with the line structure: folding
`u₀ + λ·u₁` equals `fold(u₀) + λ·fold(u₁)` — the bad-scalar parameter survives the fold
untouched in *every* regime (linearity; the regime trichotomy then identifies the shape). -/
theorem foldAt_line (u₀ u₁ : F → F) (lam β x : F) :
    foldAt (fun t => u₀ t + lam * u₁ t) β x = foldAt u₀ β x + lam * foldAt u₁ β x := by
  rw [foldAt_add u₀ (fun t => lam * u₁ t) β x, foldAt_smul lam u₁ β x]

/-! ## Source audit -/

#print axioms foldAt_add
#print axioms foldAt_smul
#print axioms foldAt_monomial_even
#print axioms foldAt_monomial_odd
#print axioms kkh26_fold_m_even
#print axioms sq_pow_half
#print axioms kkh26_inner_group_fold_invariant
#print axioms kkh26_fold_s_step_r_even
#print axioms kkh26_fold_s_step_r_odd
#print axioms kkh26_fold_line_collapse
#print axioms foldAt_line

end ProximityGap.KKH26FoldTransport
