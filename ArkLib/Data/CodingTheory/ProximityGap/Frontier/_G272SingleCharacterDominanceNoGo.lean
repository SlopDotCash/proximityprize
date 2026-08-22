/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G272: the single order-2 character does not dominate the adjacent-rank CORE covariance sign (#466)

The canonical #466 CORE model (identical to G269/G271, computation of record) is
`W_G(x) = #{(y,z) ∈ G² : 2y − z = x}` (double-shift sponsor), `R_r = dp_r ⋆ dp_{r-1}` (adjacent-rank
subset correlation), `SW = n²`, `SR = C(n,r)·C(n,r-1)`, and
`A_r = p·∑_x W_G(x) R_r(x) − SW·SR`.

G271 proved that the centered coordinate mass `P(x) = (p·W_G(x) − SW)·(p·R_r(x) − SR)` is **constant
on the multiplicative `G`-cosets** of `𝔽_p^*`. Consequently the sponsor gate factors exactly through
the cyclic quotient `Z_m = 𝔽_p^*/G`, `m = (p−1)/n`, as a Plancherel sum over `Ẑ_m`:

```text
p · A_r  =  P(0)  +  n · ∑_{j ∈ Z_m} Porbit(j)          (orbit reconstruction, exact)
         =  P(0)  +  ∑_{χ ∈ Ẑ_m} What(χ)·conj(Rhat_r(χ)).
```

The G270 referee census (Fable, 2026-07-13) established the coarse even/odd *families* cancel
(magnitudes `10⁴–10⁵ × |A_r|`, opposite sign). This leaves the **single-character dominance test**
rank-1 open question flagged by both the referee and the G271 formalizer handoff:

> Does the single order-2 (quadratic / Legendre-type) character term track `sign(A_r)` where the
> coarse families fail? If yes, the target factors through one Jacobi-sum-shaped covariance
> (classically estimable). If no, the frontier is irreducibly multi-character.

**Empirical resolution (this file's motivation).** The exact integer probe
`scripts/probes/g272_single_character_dominance_probe.py` computes, over the balanced `n=16, r=5`
census at every even-`m` prime `p < 2600`, the exact single order-2 Plancherel term as the product
of the two SEPARATE real transforms of the centered quotient profiles `w`, `r`:

```text
term := What(χ₂) · Rhat(χ₂) = (∑_j w(j)(−1)^j) · (∑_j r(j)(−1)^j)     (exact integer)
```

and finds `sign(term) = sign(A_r)` in only **7/22** cells (below chance), realizing **all four sign
combinations** of `(sign A, sign term)`:

* `p = 929`: `A = +136655344 > 0` but `term = 3716 · (−7746931) = −28787595596 < 0`;
* `p = 97`:  `A = −6285008 < 0` but `term = 194 · 244828 = +47496632 > 0`;
* `p = 257`: `A = −1051408 < 0` and `term = (−257) · 650210 = −167103970 < 0` (same sign);
* `p = 641`: `A = +28460944 > 0` and `term = 1282 · 2709507 = +3473587974 > 0` (same sign).

Many cells even have `term = 0` (the χ₂ factor vanishes). So the single order-2 Plancherel term is
not sign-faithful in either polarity. Single-character dominance is **DEAD**; the frontier is
irreducibly multi-character.

## What this file proves (axiom-clean, `decide`-level)

Abstractly over the signed orbit-mass vector `Q : Fin m → ℤ` (with `Q(j) = n · Porbit(j)` already
carrying the `n` coset copies) and a DC term `P0 : ℤ`, with the reconstructed gate
`gate P0 Q := P0 + ∑ Q`:

* `charTwo` and `evenFamily`/`oddFamily` are defined; `family_split` gives the exact partition
  `evenFamily Q + oddFamily Q = ∑ Q` and `charTwo Q = evenFamily Q − oddFamily Q`.
* `evenFamily_consumes_gate` : the *even-family lower bound* at its complementary threshold is
  **algebraically equivalent** to the gate `gate > 0`, hence target-consuming, NOT a weaker route
  (formalizes Fable's one-line consumer equivalence for coarse families).
* `charTwoTerm w r := charTwo w * charTwo r` : the **correct** single order-2 Plancherel term. Since
  `χ₂(j) = (−1)^j` is a REAL character, `What(χ₂) = charTwo w` and `Rhat(χ₂) = charTwo r` are exact
  integers, and the single order-2 term `(n/m)·What(χ₂)·Rhat(χ₂)` has the sign of the integer
  product `charTwo w * charTwo r`. NOTE this is the product of the *separate* transforms, NOT
  `charTwo` of the pointwise product `P = w·r` (which convolves all pairs `χ·χ' = χ₂`, a different
  object).
* `term_sign_decouples_pos` / `term_sign_decouples_neg` : concrete recorded witnesses in which the
  order-2 term `wchi2 * rchi2` and `gate` have **opposite** strict sign, in both directions.
* `term_sign_agrees_neg` / `term_sign_agrees_pos` : same-sign witnesses, needed so the
  *anti-correlation* law is also refuted, not just the same-polarity law.
* `not_term_certifies_gate_sign` / `no_fixed_order2_sign_law_either_polarity` : packaged no-go.
  No fixed sign relation of **either** polarity (`0 < gate ↔ 0 < term`, or `0 < gate ↔ term < 0`)
  holds across the recorded census.

The Lean statements are exact integer identities/inequalities on the recorded scalars; the
computation of record (the subset-DP orbit sums producing `A`, `wchi2 = charTwo w`,
`rchi2 = charTwo r`, `P0`) is the float-free probe, matching the G214/G220/G266/G269 convention. It
certifies the decomposition bookkeeping and the two-sided sign-decoupling of the CORRECT single
order-2 Plancherel term, not an in-Lean re-derivation of the orbit sums.
-/

namespace ArkLib.ProximityGap.Frontier.G272SingleCharacterDominanceNoGo

open scoped BigOperators

/-- The signed order-2 (quadratic / Legendre-on-quotient) character functional of a quotient profile
`f : Fin m → ℤ`: `∑_j f j · (−1)^j`. Applied to the centered quotient profile `w` (resp. `r`) it is
exactly the real transform `What(χ₂)` (resp. `Rhat(χ₂)`), an exact integer. -/
def charTwo {m : ℕ} (f : Fin m → ℤ) : ℤ :=
  ∑ j : Fin m, f j * (if (j : ℕ) % 2 = 0 then 1 else -1)

/-- The **single order-2 Plancherel term** `What(χ₂) · Rhat(χ₂)` as an exact integer: the product of
the two SEPARATE order-2 character functionals of the centered quotient profiles `w` and `r`. Its
sign equals that of the true (real) single order-2 term `(n/m)·What(χ₂)·Rhat(χ₂)` since `n/m > 0`.
This is the object the single-character-dominance question is actually about; it is NOT `charTwo` of
the pointwise product `w·r` (which convolves all character pairs `χ·χ' = χ₂`). -/
def charTwoTerm {m : ℕ} (w r : Fin m → ℤ) : ℤ :=
  charTwo w * charTwo r

/-- The sign of the single order-2 Plancherel term is the product of the signs of the two separate
character functionals: it is negative exactly when `What(χ₂)` and `Rhat(χ₂)` have opposite strict
sign. This is why the term can freely decouple from the gate sign: it is a product of two
independent real transforms, not a quantity tied to the covariance sign. -/
theorem charTwoTerm_neg_iff_opposite_sign {m : ℕ} (w r : Fin m → ℤ) :
    charTwoTerm w r < 0 ↔ (0 < charTwo w ∧ charTwo r < 0) ∨ (charTwo w < 0 ∧ 0 < charTwo r) := by
  unfold charTwoTerm
  constructor
  · intro h
    rcases lt_trichotomy (charTwo w) 0 with hw | hw | hw
    · rcases lt_trichotomy (charTwo r) 0 with hr | hr | hr
      · exact absurd h (not_lt.mpr (le_of_lt (mul_pos_of_neg_of_neg hw hr)))
      · simp [hr] at h
      · exact Or.inr ⟨hw, hr⟩
    · simp [hw] at h
    · rcases lt_trichotomy (charTwo r) 0 with hr | hr | hr
      · exact Or.inl ⟨hw, hr⟩
      · simp [hr] at h
      · exact absurd h (not_lt.mpr (le_of_lt (mul_pos hw hr)))
  · rintro (⟨hw, hr⟩ | ⟨hw, hr⟩)
    · exact mul_neg_of_pos_of_neg hw hr
    · exact mul_neg_of_neg_of_pos hw hr

/-- The coarse even-index family aggregate `∑_{j even} Q j` (Fable G270 `Q_even`). -/
def evenFamily {m : ℕ} (Q : Fin m → ℤ) : ℤ :=
  ∑ j : Fin m, if (j : ℕ) % 2 = 0 then Q j else 0

/-- The coarse odd-index family aggregate `∑_{j odd} Q j`. -/
def oddFamily {m : ℕ} (Q : Fin m → ℤ) : ℤ :=
  ∑ j : Fin m, if (j : ℕ) % 2 = 0 then 0 else Q j

/-- The reconstructed sponsor gate scalar `p · A = P0 + ∑ Q` (G271 orbit reconstruction). Here `Q`
is the **signed orbit-mass vector** `Q(j) = n · Porbit(j)`, which already carries the `n` copies of
each coset representative, so the total is `P0 + ∑ Q` with no further factor. Its sign equals
`sign (p · A) = sign A` since `p > 0`. -/
def gate {m : ℕ} (P0 : ℤ) (Q : Fin m → ℤ) : ℤ :=
  P0 + ∑ j : Fin m, Q j

/-- Exact partition: the even and odd families sum to the total orbit mass. -/
theorem family_split {m : ℕ} (Q : Fin m → ℤ) :
    evenFamily Q + oddFamily Q = ∑ j : Fin m, Q j := by
  unfold evenFamily oddFamily
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases h : (j : ℕ) % 2 = 0 <;> simp [h]

/-- The order-2 character functional is the *signed* difference of the two families. -/
theorem charTwo_eq_even_sub_odd {m : ℕ} (Q : Fin m → ℤ) :
    charTwo Q = evenFamily Q - oddFamily Q := by
  unfold charTwo evenFamily oddFamily
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases h : (j : ℕ) % 2 = 0 <;> simp [h]

/-- **Coarse family lower bound is target-consuming.** With `Q` the signed orbit-mass vector, a
lower bound on the even family at its complementary threshold, `evenFamily Q > −(P0 + oddFamily Q)`,
is *algebraically equivalent* to the gate being positive `gate P0 Q > 0`. This formalizes Fable's
one-line consumer equivalence: subtracting the odd part changes bookkeeping, not information, so no
coarse family lower bound is a route strictly weaker than the live gate. -/
theorem evenFamily_consumes_gate {m : ℕ} (P0 : ℤ) (Q : Fin m → ℤ) :
    (evenFamily Q > -(P0 + oddFamily Q)) ↔ gate P0 Q > 0 := by
  unfold gate
  have hsplit : ∑ j : Fin m, Q j = evenFamily Q + oddFamily Q := (family_split Q).symm
  rw [hsplit]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## Recorded single order-2 Plancherel term witnesses (all four sign combinations)

Exact scalars from the float-free census probe (`n = 16`, `r = 5`, canonical CORE model). For each
witness we record the gate scalar `A` (the integer `A_r`, whose sign equals that of `p·A` since
`p > 0`) and the two exact-integer order-2 character values `wchi2 = What(χ₂) = charTwo w` and
`rchi2 = Rhat(χ₂) = charTwo r`. The single order-2 Plancherel term is `term = wchi2 · rchi2`; its
sign equals that of the true `(n/m)·What(χ₂)·Rhat(χ₂)`. The four recorded cells realize all four
sign combinations of `(sign A, sign term)`, so no fixed sign law of either polarity survives. The
quotient profiles producing these are the computation of record (the probe). -/

/-- Witness `p = 929`: gate `A = +136655344 > 0`, `wchi2 = 3716`, `rchi2 = -7746931`, so
`term = wchi2·rchi2 = -28787595596 < 0` (positive gate, negative order-2 term). -/
def A_929 : ℤ := 136655344
/-- `What(χ₂)` at `p = 929`. -/
def wchi2_929 : ℤ := 3716
/-- `Rhat(χ₂)` at `p = 929`. -/
def rchi2_929 : ℤ := -7746931

/-- Witness `p = 97`: gate `A = -6285008 < 0`, `wchi2 = 194`, `rchi2 = 244828`, so
`term = +47496632 > 0` (negative gate, positive order-2 term). -/
def A_97 : ℤ := -6285008
/-- `What(χ₂)` at `p = 97`. -/
def wchi2_97 : ℤ := 194
/-- `Rhat(χ₂)` at `p = 97`. -/
def rchi2_97 : ℤ := 244828

/-- Witness `p = 257`: gate `A = -1051408 < 0`, `wchi2 = -257`, `rchi2 = 650210`, so
`term = -167103970 < 0` (both negative: a same-sign cell). -/
def A_257 : ℤ := -1051408
/-- `What(χ₂)` at `p = 257`. -/
def wchi2_257 : ℤ := -257
/-- `Rhat(χ₂)` at `p = 257`. -/
def rchi2_257 : ℤ := 650210

/-- Witness `p = 641`: gate `A = +28460944 > 0`, `wchi2 = 1282`, `rchi2 = 2709507`, so
`term = +3473587974 > 0` (both positive: a same-sign cell). -/
def A_641 : ℤ := 28460944
/-- `What(χ₂)` at `p = 641`. -/
def wchi2_641 : ℤ := 1282
/-- `Rhat(χ₂)` at `p = 641`. -/
def rchi2_641 : ℤ := 2709507

/-- **Positive-gate decoupling.** A recorded cell (`p = 929`) where the gate is strictly positive
yet the single order-2 Plancherel term `wchi2 · rchi2` is strictly negative. -/
theorem term_sign_decouples_pos : 0 < A_929 ∧ wchi2_929 * rchi2_929 < 0 := by
  unfold A_929 wchi2_929 rchi2_929; decide

/-- **Negative-gate decoupling.** A recorded cell (`p = 97`) where the gate is strictly negative yet
the single order-2 Plancherel term is strictly positive. -/
theorem term_sign_decouples_neg : A_97 < 0 ∧ 0 < wchi2_97 * rchi2_97 := by
  unfold A_97 wchi2_97 rchi2_97; decide

/-- **Same-sign witness (both negative).** A recorded cell (`p = 257`) where gate and order-2 term
agree in sign, both negative. Together with `term_sign_decouples_*` this kills the anti-correlation
law as well as the same-polarity law. -/
theorem term_sign_agrees_neg : A_257 < 0 ∧ wchi2_257 * rchi2_257 < 0 := by
  unfold A_257 wchi2_257 rchi2_257; decide

/-- **Same-sign witness (both positive).** A recorded cell (`p = 641`) where gate and order-2 term
agree in sign, both positive. -/
theorem term_sign_agrees_pos : 0 < A_641 ∧ 0 < wchi2_641 * rchi2_641 := by
  unfold A_641 wchi2_641 rchi2_641; decide

/-- **Packaged single-character no-go.** The recorded census realizes all four sign combinations of
`(sign gate, sign (order-2 term))`: `(+, -)` at `p = 929`, `(-, +)` at `p = 97`, `(-, -)` at
`p = 257`, `(+, +)` at `p = 641`. Hence the single order-2 Plancherel term `What(χ₂)·Rhat(χ₂)` does
not certify the sponsor-gate sign in either polarity, and the surviving object is the full
character-weighted quotient covariance. -/
theorem not_term_certifies_gate_sign :
    (0 < A_929 ∧ wchi2_929 * rchi2_929 < 0) ∧
    (A_97 < 0 ∧ 0 < wchi2_97 * rchi2_97) ∧
    (A_257 < 0 ∧ wchi2_257 * rchi2_257 < 0) ∧
    (0 < A_641 ∧ 0 < wchi2_641 * rchi2_641) := by
  exact ⟨term_sign_decouples_pos, term_sign_decouples_neg,
         term_sign_agrees_neg, term_sign_agrees_pos⟩

/-- A candidate "order-2 sign law" is a fixed polarity `b : Bool` asserting that, on a cell with a
gate `A` and order-2 term `t`, the gate is positive iff the term is positive (`b = true`, same)
or iff the term is negative (`b = false`, anti-polarity). `SignLawHolds b` says this candidate law
holds on ALL FOUR recorded cells at once (the genuine, cellwise, non-vacuous claim: it ranges only
over the recorded `(A, term)` pairs, not over arbitrary integers). -/
def SignLawHolds (b : Bool) : Prop :=
  ∀ At ∈ [ (A_929, wchi2_929 * rchi2_929),
           (A_97,  wchi2_97  * rchi2_97),
           (A_257, wchi2_257 * rchi2_257),
           (A_641, wchi2_641 * rchi2_641) ],
    (0 < At.1) ↔ (if b then 0 < At.2 else At.2 < 0)

/-- Consequence: **no fixed order-2 sign law of either polarity** holds across the recorded cells.
The same-polarity law (`b = true`) is killed by `p = 929` (`0 < A_929` but its term is `< 0`); the
anti-polarity law (`b = false`) is killed by `p = 257` (`A_257 < 0` yet its term is `< 0`, which the
anti-law would force to `0 < A_257`). So no single order-2 Plancherel term predicts the gate sign on
the recorded census, in either polarity. -/
theorem no_fixed_order2_sign_law_either_polarity (b : Bool) : ¬ SignLawHolds b := by
  intro h
  unfold SignLawHolds at h
  cases b with
  | true =>
    -- same-polarity: p = 929 has 0 < A but term < 0
    have hc := h (A_929, wchi2_929 * rchi2_929) (by simp)
    have h1 := hc.mp term_sign_decouples_pos.1        -- 0 < term
    exact absurd h1 (not_lt.mpr term_sign_decouples_pos.2.le)
  | false =>
    -- anti-polarity: p = 257 has A < 0 but term < 0 ⇒ anti-law forces 0 < A
    have hc := h (A_257, wchi2_257 * rchi2_257) (by simp)
    have h1 := hc.mpr term_sign_agrees_neg.2          -- 0 < A_257
    exact absurd h1 (not_lt.mpr term_sign_agrees_neg.1.le)

end ArkLib.ProximityGap.Frontier.G272SingleCharacterDominanceNoGo
