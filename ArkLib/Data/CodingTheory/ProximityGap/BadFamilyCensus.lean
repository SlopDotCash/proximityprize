/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Level1RungPin

/-!
# The bad-family census: the pencil ladder (general rung), the doublet bottom rung, and
# the complete-envelope conjecture at the first exhaustively-censused instance (#371)

Round 7 (`Level1RungPin.lean`) discovered the antipodal pencil `(X^h, X^{h+1})` and proved
the level-`j` staircase is **not** the complete bad-family envelope.  The candidate answer
to the δ* question became "the envelope over the *complete* bad-family catalogue" — with
the catalogue itself not known to be complete.  This file lands the round-8 census results
(probe: `scripts/probes/probe_bad_family_census.py`).

## The probe (what was actually measured)

A scalar `γ` is bad for the stack `(u₀, u₁)` at agreement threshold `t` **iff** the point
`s₀ + γ·s₁` of an affine line in syndrome space `F_p^{n-k}` lies in the syndrome image of
the weight-`≤ n−t` ball, via an error support that does not explain the direction `s₁`.
So the census over ALL stacks is the census over ALL affine lines — finite, and at
`p = 17, n = 8` (domain `⟨2⟩ ⊆ F₁₇ˣ`) genuinely exhaustible (quotienting directions by the
rotation action, which is a code automorphism acting linearly on syndromes).  The probe
exhausts every threshold cell `t ∈ {5, 6, 7}` for `d ∈ {1, 2, 3}` and `t = 4` for `d = 2`,
cross-validating three independent badness checkers byte-exactly.

## The catalogue (the conjectured complete bad-family list, char-0 layer)

| family | stack | threshold `T` | count |
|---|---|---|---|
| level-`j` staircase | `(X^{r'_j 2^j m}, X^{(r'_j−1) 2^j m})` | `r'_j 2^j m` | `N(μ−j, r'_j)` |
| pencil rung `s` | `(X^a, X^{a+s})`, `gcd(a,n) ≥ d+1` | `gcd(a,n) + gcd(s,n)` | `n/gcd(s,n)` |
| simplex `e` | line of words on an `(e+1)`-set, `d ≤ n−e−2` | `n − e` | `e + 1` |
| bisimplex `e` | `((X·q₀)|_{S₁}, q₀|_{S₁})`, `n−2e−1 ≤ d ≤ n−e−2` | `n − e` | `2e + 2` |
| doublet (= simplex `1`) | `(e_x, e_y − e_x)` | `n − 1` | `2` |
| single | `(c − γ₀u₁, u₁)`, `u₁ ∉ C` | `n` | `1` |
| explosion (`t = d+2` band) | support-compact stacks | `d + 2` | `Θ(p)` |

This file proves the **general pencil-rung law** (`pencil_rung_epsMCA_lower_bound`: the
`s ∣ h` ladder `(X^h, X^{h+s})` carries `n/s` bad scalars at radius `1 − (h+s)/n`,
generalizing the landed `s = 1` antipodal pencil), the **doublet bottom rung**
(`two_deviation_epsMCA_lower_bound`), the **simplex ladder**
(`simplex_epsMCA_lower_bound`: `e + 1` bad scalars at radius `e/n` for every
`d ≤ n−e−2` — discovered by the census at the `(d, t) = (1, 6)` cell), and the
**BISIMPLEX** (`bisimplex_epsMCA_lower_bound`, THE ROUND-8 DISCOVERY: two disjoint
simplices on one affine line, `2e + 2` bad scalars at radius `e/n` in the window
`n−2e−1 ≤ d ≤ n−e−2` — strictly above every previously known family at its cells), plus
the concrete δ*-envelope extensions at `p = 12289` (`δ* ≤ 3/8` at `ε* < 8/p` for `d = 2`;
`δ* ≤ 3/8` at the WIDER band `ε* < 14/p` for `d = 4` via the bisimplex; `δ* ≤ 1/4` at
`ε* < 4/p`) and at the censused instance `p = 17`.

## The census verdict (probe, exact: every affine line, side condition exact)

At `(p, n, g) = (17, 8, 2)` the exhaustive exact maxima `W_t = p·ε_mca` per threshold
(round-8 corrected predictor + structural extremal classification):

* `d = 2`: `W_4 = 17 = p` (explosion band, `t = d+2`) · `W_5 = 11` (mod-17 surplus
  `8 + 3`: the extremal = two OVERLAPPING `e = 3` simplices `{0,2,4,7}`, `{3,5,6,7}`
  plus a 3-scalar sunflower; the char-0 layer `8` is the pencil/bisimplex value)
  · `W_6 = 4` = **the `s = 2` pencil, catalogue-EXACT** · `W_7 = 2` = **the
  doublet/simplex, catalogue-EXACT** · `W_8 = 1`.
* `d = 1`: `W_5 = 8` = the pencil tied with the disjoint BISIMPLEX (the extremal's
  structure is `simplex{0,1,3,6} + simplex{2,4,5,7}`), catalogue-EXACT · `W_6 = 3` =
  **the `e = 2` simplex, catalogue-EXACT** (the cell that exposed the predictor's
  simplex omission: the "triangle" extremal IS the simplex) · `W_7 = 2`.
* `d = 3` (the boundary `d = h − 1`): `W_5 = 17` (explosion) · `W_6 = 7` = **the
  BISIMPLEX `6` plus exactly one mod-17 extra** (the extremal decomposes as
  `simplex{0,2,6} + simplex{1,3,5}` + one weight-2 support on the complement pair
  `{4,7}`) · `W_7 = 2`.

Two-layer law: the char-0 layer of every censused cell is a catalogue family
(staircase / pencil / simplex / BISIMPLEX / explosion); the small-field surpluses
(`+3` at `(d,t) = (2,5)`, `+1` at `(3,6)`) are mod-17-specific: the `(3,6)` shoulder
cell re-censused EXHAUSTIVELY at `p = 97` gives `W_6 = 6` — the bisimplex EXACTLY,
extremal = two clean simplex triangles, runner-up `5` — and the `(2,5)` surplus does
not recur in the `p = 97` heuristic novelty searches.  The conjecture that the
catalogue good sides are exact at the instance is the named Prop
`CompleteEnvelopeF17`, with its unconditionally-proven bad sides and the conditional
full-curve theorem `completeEnvelopeF17_curve`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26 Code
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.OwnershipCensus
open ArkLib.ProximityGap.KKH26DimGeneral
open ArkLib.ProximityGap.Level1Rung

namespace ArkLib.ProximityGap.BadFamilyCensus

/-! ## The general pencil-rung law: the ladder `(X^h, X^{h+s})`, `s ∣ h`

The round-7 antipodal pencil is the rung `s = 1`.  For any `s ∣ h` with `s ≤ d`, the same
mechanism fires one level deeper: `x^h = ±1` splits the domain into two antipodal
half-cosets; on the half-coset of sign opposite to the cross points, the line
`u₀ + γu₁ = x^h(1 + γx^s)` *is* the degree-`s` codeword `±(1 + γX^s)`, and the `s`
solutions of `x^s = −1/γ` (one coset of the order-`s` subgroup, all of one parity since
`n/s` is even) are joint zeros of both — an `(h+s)`-point witness on which the direction
`x^{h+s} = ±x^s` is sign-flipped at the cross points, hence unfit.  Every
`γ ∈ −1/⟨g^s⟩` is bad: `n/s` scalars at radius `1 − (h+s)/n`. -/

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy of the `private` helper
of the sibling files). -/
private lemma pow_inj_below_order''' {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-- `(−1)^a` depends only on the parity of `a` (local copy). -/
private lemma neg_one_pow_congr' {R : Type*} [Monoid R] [HasDistribNeg R] {a b : ℕ}
    (hab : a % 2 = b % 2) : ((-1 : R)) ^ a = (-1) ^ b := by
  rcases Nat.even_or_odd a with ha | ha
  · have hb : Even b := by
      rw [Nat.even_iff] at ha ⊢
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]
  · have hb : Odd b := by
      rw [Nat.odd_iff] at ha ⊢
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]

open Classical in
/-- **The pencil-rung lower bound** (the general `s ∣ h` ladder; `s = 1` recovers the
round-7 `antipodal_pencil_epsMCA_lower_bound`).  On the smooth domain `⟨g⟩` of even order
`n = 2h`, for every `s ∣ h` with `1 ≤ s ≤ d` and `d + 1 ≤ h`, the stack
`(X^h, X^{h+s})` has at least `n/s` bad scalars — the orbit `−1/⟨g^s⟩` — at radius
`1 − (h+s)/n` against the degree-`d` code.  Probe-exact at the censused instances
(`4 = 8/2` at `(p,n,d) = (17,8,2)`, `t = 6`; `8 = 16/2` and `4 = 16/4` at `n = 16`,
`p ∈ {97, 12289}`). -/
theorem pencil_rung_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {h d s : ℕ}
    (hh : 1 ≤ h) (hn : n = 2 * h) {g : ZMod p} (hg : orderOf g = n)
    (hs1 : 1 ≤ s) (hsh : s ∣ h) (hsd : s ≤ d) (hdh : d + 1 ≤ h) :
    ((n / s : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((h + s : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  classical
  subst hn
  -- arithmetic bookkeeping for the rung: `q := 2h/s`, division-free
  have hsh' : s ≤ h := Nat.le_of_dvd (by omega) hsh
  obtain ⟨q', hq'⟩ : ∃ c, h = s * c := hsh
  set q : ℕ := 2 * q' with hq_def
  have hqs : q * s = 2 * h := by rw [hq_def, hq']; ring
  have hq'_pos : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with h0 | h1
    · rw [h0, mul_zero] at hq'
      omega
    · exact h1
  have hq_pos : 1 ≤ q := by omega
  have hdivq : 2 * h / s = q := by
    rw [← hqs, Nat.mul_div_cancel _ (by omega : 0 < s)]
  rw [hdivq]
  -- field bookkeeping: `g ≠ 0`, index injectivity, `g^h = −1`
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (2 * h) = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega : 2 * h ≠ 0)] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin (2 * h), g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    exact Fin.ext (pow_inj_below_order''' hg0 hg _ i.isLt _ j.isLt hij)
  have hgn : g ^ (2 * h) = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hne1 : g ^ h ≠ 1 := by
    intro hcon
    have hdvd : 2 * h ∣ h := hg ▸ orderOf_dvd_of_pow_eq_one hcon
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hgh : g ^ h = -1 := by
    have hfac : (g ^ h - 1) * (g ^ h + 1) = 0 := by
      have hsq : g ^ h * g ^ h = 1 := by
        rw [← pow_add]
        have : h + h = 2 * h := by omega
        rw [this, hgn]
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact absurd (by linear_combination hc) hne1
    · linear_combination hc
  have hm1 : (-1 : ZMod p) ≠ 1 := hgh ▸ hne1
  -- the antipodal values of the stack words
  have hu0v : ∀ i : Fin (2 * h), (g ^ (i : ℕ)) ^ h = (-1 : ZMod p) ^ (i : ℕ) := by
    intro i
    rw [← pow_mul, mul_comm (i : ℕ) h, pow_mul, hgh]
  have hu1v : ∀ i : Fin (2 * h),
      (g ^ (i : ℕ)) ^ (h + s) = (-1 : ZMod p) ^ (i : ℕ) * (g ^ (i : ℕ)) ^ s := by
    intro i
    rw [pow_add, hu0v i]
  -- the stack and the bad-scalar orbit `−1/⟨g^s⟩`
  set u : WordStack (ZMod p) (Fin 2) (Fin (2 * h)) :=
    ![fun i => (g ^ (i : ℕ)) ^ h, fun i => (g ^ (i : ℕ)) ^ (h + s)] with hu
  set Λ : Finset (ZMod p) :=
    Finset.univ.image (fun i : Fin q => -((g ^ ((i : ℕ) * s))⁻¹)) with hΛ
  have hΛcard : Λ.card = q := by
    have hinj : Function.Injective (fun i : Fin q => -((g ^ ((i : ℕ) * s))⁻¹)) := by
      intro i j hij
      simp only at hij
      have heq : g ^ ((i : ℕ) * s) = g ^ ((j : ℕ) * s) :=
        inv_injective (neg_injective hij)
      have hi : (i : ℕ) * s < 2 * h := by
        calc (i : ℕ) * s < q * s :=
          mul_lt_mul_of_pos_right i.isLt (by omega : 0 < s)
        _ = 2 * h := hqs
      have hj : (j : ℕ) * s < 2 * h := by
        calc (j : ℕ) * s < q * s :=
          mul_lt_mul_of_pos_right j.isLt (by omega : 0 < s)
        _ = 2 * h := hqs
      have := pow_inj_below_order''' hg0 hg _ hi _ hj heq
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) this)
    rw [hΛ, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  -- every orbit scalar is bad with the half-coset-plus-`s`-zeros witness
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g (2 * h) d)
      (1 - ((h + s : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro γ hγ
    obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.mp hγ
    set a₀ : ℕ := (i₀ : ℕ) with ha₀_def
    set γ := -((g ^ (a₀ * s))⁻¹) with hγdef
    have hγx : 1 + γ * g ^ (a₀ * s) = 0 := by
      rw [hγdef, neg_mul, inv_mul_cancel₀ (pow_ne_zero _ hg0)]
      ring
    -- the bulk: the half-coset of parity opposite to `a₀`
    set r : ℕ := 1 - a₀ % 2 with hr_def
    have hflt : ∀ k : Fin h, 2 * (k : ℕ) + r < 2 * h := fun k => by
      have := k.isLt
      omega
    set f : Fin h → Fin (2 * h) := fun k => ⟨2 * (k : ℕ) + r, hflt k⟩ with hf
    set Sbulk : Finset (Fin (2 * h)) := Finset.univ.image f with hSb
    have hbulk_par : ∀ i ∈ Sbulk, (i : ℕ) % 2 = r := by
      intro i hib
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hib
      subst hk
      show (2 * (k : ℕ) + r) % 2 = r
      omega
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 := congrArg Fin.val hab
      simp only [hf] at h1
      exact Fin.ext (by omega)
    have hSbulk_card : Sbulk.card = h := by
      rw [hSb, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
        Fintype.card_fin]
    -- the cross points: the coset `g^{a₀}·⟨g^q⟩`, all of parity `a₀`
    have hzlt : ∀ k : Fin s, (a₀ + (k : ℕ) * q) % (2 * h) < 2 * h :=
      fun _ => Nat.mod_lt _ (by omega)
    set z : Fin s → Fin (2 * h) := fun k => ⟨(a₀ + (k : ℕ) * q) % (2 * h), hzlt k⟩
      with hz
    have hz_par : ∀ k : Fin s, ((z k : Fin (2 * h)) : ℕ) % 2 = a₀ % 2 := by
      intro k
      show ((a₀ + (k : ℕ) * q) % (2 * h)) % 2 = a₀ % 2
      have hkq : (k : ℕ) * q = 2 * ((k : ℕ) * q') := by
        rw [hq_def]; ring
      rw [hkq]
      obtain ⟨c, hc⟩ : ∃ c, (a₀ + 2 * ((k : ℕ) * q')) % (2 * h) + 2 * h * c
          = a₀ + 2 * ((k : ℕ) * q') := ⟨_, Nat.mod_add_div _ _⟩
      have hassoc : 2 * h * c = 2 * (h * c) := mul_assoc 2 h c
      rw [hassoc] at hc
      omega
    have hz_pow : ∀ k : Fin s, (g ^ ((z k : Fin (2 * h)) : ℕ)) ^ s = g ^ (a₀ * s) := by
      intro k
      have h1 : g ^ ((a₀ + (k : ℕ) * q) % (2 * h)) = g ^ (a₀ + (k : ℕ) * q) := by
        conv_lhs => rw [← hg]
        exact pow_mod_orderOf _ _
      show (g ^ ((a₀ + (k : ℕ) * q) % (2 * h))) ^ s = g ^ (a₀ * s)
      have hexp : (a₀ + (k : ℕ) * q) * s = a₀ * s + 2 * h * (k : ℕ) := by
        rw [add_mul, mul_assoc, hqs, mul_comm ((k : ℕ)) (2 * h)]
      rw [h1, ← pow_mul, hexp, pow_add, pow_mul g (2 * h), hgn, one_pow, mul_one]
    have hz_zero : ∀ k : Fin s, 1 + γ * (g ^ ((z k : Fin (2 * h)) : ℕ)) ^ s = 0 := by
      intro k
      rw [hz_pow k]
      exact hγx
    set Z : Finset (Fin (2 * h)) := Finset.univ.image z with hZ
    have hzinj : Function.Injective z := by
      intro k k' hkk
      have h1 : (a₀ + (k : ℕ) * q) % (2 * h) = (a₀ + (k' : ℕ) * q) % (2 * h) :=
        congrArg Fin.val hkk
      rcases le_total (k : ℕ) (k' : ℕ) with hle | hle
      · have hmod : (a₀ + (k : ℕ) * q) ≡ (a₀ + (k' : ℕ) * q) [MOD 2 * h] := h1
        have hle' : a₀ + (k : ℕ) * q ≤ a₀ + (k' : ℕ) * q := by
          have := Nat.mul_le_mul hle (le_refl q)
          omega
        have hdvd : 2 * h ∣ (a₀ + (k' : ℕ) * q) - (a₀ + (k : ℕ) * q) :=
          (Nat.modEq_iff_dvd' hle').mp hmod
        have hsub : (a₀ + (k' : ℕ) * q) - (a₀ + (k : ℕ) * q)
            = ((k' : ℕ) - (k : ℕ)) * q := by
          rw [Nat.add_sub_add_left, Nat.sub_mul]
        rw [hsub] at hdvd
        have hks : ((k' : ℕ) - (k : ℕ)) < s := by
          have := k'.isLt
          omega
        have hlt : ((k' : ℕ) - (k : ℕ)) * q < 2 * h := by
          calc ((k' : ℕ) - (k : ℕ)) * q < s * q :=
            mul_lt_mul_of_pos_right hks (by omega : 0 < q)
          _ = 2 * h := by rw [mul_comm]; exact hqs
        have := Nat.eq_zero_of_dvd_of_lt hdvd hlt
        have hk0 : (k' : ℕ) - (k : ℕ) = 0 := by
          rcases Nat.mul_eq_zero.mp this with h0 | h0
          · exact h0
          · omega
        exact Fin.ext (by omega)
      · -- symmetric case
        have hmod : (a₀ + (k' : ℕ) * q) ≡ (a₀ + (k : ℕ) * q) [MOD 2 * h] := h1.symm
        have hle' : a₀ + (k' : ℕ) * q ≤ a₀ + (k : ℕ) * q := by
          have := Nat.mul_le_mul hle (le_refl q)
          omega
        have hdvd : 2 * h ∣ (a₀ + (k : ℕ) * q) - (a₀ + (k' : ℕ) * q) :=
          (Nat.modEq_iff_dvd' hle').mp hmod
        have hsub : (a₀ + (k : ℕ) * q) - (a₀ + (k' : ℕ) * q)
            = ((k : ℕ) - (k' : ℕ)) * q := by
          rw [Nat.add_sub_add_left, Nat.sub_mul]
        rw [hsub] at hdvd
        have hks : ((k : ℕ) - (k' : ℕ)) < s := by
          have := k.isLt
          omega
        have hlt : ((k : ℕ) - (k' : ℕ)) * q < 2 * h := by
          calc ((k : ℕ) - (k' : ℕ)) * q < s * q :=
            mul_lt_mul_of_pos_right hks (by omega : 0 < q)
          _ = 2 * h := by rw [mul_comm]; exact hqs
        have := Nat.eq_zero_of_dvd_of_lt hdvd hlt
        have hk0 : (k : ℕ) - (k' : ℕ) = 0 := by
          rcases Nat.mul_eq_zero.mp this with h0 | h0
          · exact h0
          · omega
        exact Fin.ext (by omega)
    have hZcard : Z.card = s := by
      rw [hZ, Finset.card_image_of_injective _ hzinj, Finset.card_univ,
        Fintype.card_fin]
    have hZdisj : Disjoint Sbulk Z := by
      rw [Finset.disjoint_right]
      intro i hiZ hiB
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hiZ
      have h1 := hbulk_par i hiB
      have h2 : (i : ℕ) % 2 = a₀ % 2 := hk ▸ hz_par k
      omega
    set S : Finset (Fin (2 * h)) := Sbulk ∪ Z with hS
    have hScard : S.card = h + s := by
      rw [hS, Finset.card_union_of_disjoint hZdisj, hSbulk_card, hZcard]
    -- the sign of the bulk coset, and the degree-`s` codeword
    set sg : ZMod p := (-1 : ZMod p) ^ (a₀ + 1) with hsg_def
    have hpar : ∀ i ∈ Sbulk, (-1 : ZMod p) ^ (i : ℕ) = sg := by
      intro i hib
      have h1 := hbulk_par i hib
      exact neg_one_pow_congr' (by omega)
    have hzsign : ∀ k : Fin s, (-1 : ZMod p) ^ ((z k : Fin (2 * h)) : ℕ)
        = (-1 : ZMod p) ^ a₀ := by
      intro k
      exact neg_one_pow_congr' (hz_par k)
    set qpoly : Polynomial (ZMod p) :=
      Polynomial.C sg * (1 + Polynomial.C γ * Polynomial.X ^ s) with hqpoly_def
    have hqdeg : qpoly.natDegree ≤ d := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      refine max_le (by simp) ?_
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      simpa [Polynomial.natDegree_X_pow] using hsd
    have hq_eval : ∀ x : ZMod p, qpoly.eval x = sg * (1 + γ * x ^ s) := by
      intro x
      rw [hqpoly_def]
      simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    refine ⟨S, ?_, ⟨fun i => qpoly.eval (g ^ (i : ℕ)),
      polyEval_mem_evalCode qpoly hqdeg, ?_⟩, ?_⟩
    · -- size: |S| = h + s = (1 − δ)·n
      have hcardF : ((Fintype.card (Fin (2 * h)) : ℕ) : ℝ≥0) = ((2 * h : ℕ) : ℝ≥0) := by
        rw [Fintype.card_fin]
      have hn0 : ((2 * h : ℕ) : ℝ≥0) ≠ 0 := by
        have hpos : (0 : ℕ) < 2 * h := by omega
        exact_mod_cast hpos.ne'
      have hle1 : ((h + s : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0) ≤ 1 := by
        rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0))]
        exact_mod_cast (by omega : h + s ≤ 2 * h)
      have h1δ : (1 : ℝ≥0) - (1 - ((h + s : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0))
          = ((h + s : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0) := tsub_tsub_cancel_of_le hle1
      rw [hScard, hcardF, h1δ, div_mul_cancel₀ _ hn0]
    · -- agreement of the line with the degree-`s` codeword on the witness
      intro i hi
      rw [hu]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
      rw [hq_eval, hu0v i, hu1v i]
      rcases Finset.mem_union.mp hi with hib | hiZ
      · rw [hpar i hib]
        ring
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hiZ
        have hzz := hz_zero k
        linear_combination (sg - (-1 : ZMod p) ^ ((z k : Fin (2 * h)) : ℕ)) * hzz
    · -- no joint pair: the direction is sign-flipped at the cross points
      rintro ⟨v₀, -, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hsX : (Polynomial.C sg * Polynomial.X ^ s : Polynomial (ZMod p)).natDegree
          ≤ d := by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        simpa [Polynomial.natDegree_X_pow] using hsd
      have hqq : q₁ = Polynomial.C sg * Polynomial.X ^ s := by
        refine fit_unique hginj (B := Sbulk) (by rw [hSbulk_card]; exact hdh)
          hq₁deg hsX fun i hib => ?_
        have h1 : v₁ i = u 1 i :=
          (hpair i (Finset.mem_union_left _ hib)).2
        have h2 : v₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i
        have h3 : u 1 i = sg * (g ^ (i : ℕ)) ^ s := by
          rw [hu]
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [hu1v i, hpar i hib]
        rw [← h2, h1, h3]
        simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_pow]
      -- contradiction at the cross point `z 0`
      have hs_pos : 0 < s := hs1
      set k₀ : Fin s := ⟨0, hs_pos⟩ with hk₀
      have hz₀mem : z k₀ ∈ S :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k₀, Finset.mem_univ _, rfl⟩)
      have h4 : v₁ (z k₀) = u 1 (z k₀) := (hpair (z k₀) hz₀mem).2
      have h5 : v₁ (z k₀) = q₁.eval (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) := hq₁ (z k₀)
      have h6 : u 1 (z k₀) = (-1 : ZMod p) ^ a₀
          * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s := by
        rw [hu]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hu1v (z k₀), hzsign k₀]
      have h7 : q₁.eval (g ^ ((z k₀ : Fin (2 * h)) : ℕ))
          = sg * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s := by
        rw [hqq]
        simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_pow]
      have hkey : (-1 : ZMod p) ^ a₀ * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s
          = -((-1 : ZMod p) ^ a₀ * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s) := by
        calc (-1 : ZMod p) ^ a₀ * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s
            = u 1 (z k₀) := h6.symm
        _ = q₁.eval (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) := by rw [← h4, h5]
        _ = sg * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s := h7
        _ = -((-1 : ZMod p) ^ a₀ * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s) := by
            rw [hsg_def, pow_succ]
            ring
      have hx0 : (-1 : ZMod p) ^ a₀ * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
          (pow_ne_zero _ (pow_ne_zero _ hg0))
      have h2x : (2 : ZMod p)
          * ((-1 : ZMod p) ^ a₀ * (g ^ ((z k₀ : Fin (2 * h)) : ℕ)) ^ s) = 0 := by
        linear_combination hkey
      rcases mul_eq_zero.mp h2x with h20 | hx
      · exact hm1 (by linear_combination -h20)
      · exact hx0 hx
  -- feed the orbit into the in-tree lower-bound engine
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g (2 * h) d)
    (1 - ((h + s : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  refine ENNReal.div_le_div_right ?_ _
  rw [hΛcard]

/-- **The pencil-rung `δ*` upper bound**: at every budget `ε* < (n/s)/p`, the threshold of
the degree-`d` code is at most `1 − (h+s)/n`.  The rungs `s = 1, 2, 4, …` extend the
round-7 envelope strictly downward in radius as the budget shrinks. -/
theorem mcaDeltaStar_le_pencil_rung {p n : ℕ} [Fact p.Prime] [NeZero n] {h d s : ℕ}
    (hh : 1 ≤ h) (hn : n = 2 * h) {g : ZMod p} (hg : orderOf g = n)
    (hs1 : 1 ≤ s) (hsh : s ∣ h) (hsd : s ≤ d) (hdh : d + 1 ≤ h) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((n / s : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar
      ≤ 1 - ((h + s : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) :=
  mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (pencil_rung_epsMCA_lower_bound hh hn hg hs1 hsh hsd hdh))

/-! ## The doublet: the universal bottom rung of every envelope

The smallest nontrivial bad family: `u₀ = e_x`, `u₁ = e_y − e_x` (two deviation points).
At `γ = 0` the line is `e_x` — within one error of the zero codeword, with the direction
unfit on the complement of `x`; at `γ = 1` it is `e_y`, symmetrically.  Two bad scalars at
radius `1 − (n−1)/n`, for every degree `d ≤ n − 3`: the census shows this is EXACTLY the
worst stack at threshold `n − 1` (probe `W_7 = 2` at all censused instances). -/

open Classical in
/-- **The doublet lower bound** — the bottom rung: `2` bad scalars at radius `1 − (n−1)/n`
for every smooth-domain evaluation code with `d + 3 ≤ n`. -/
theorem two_deviation_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {d : ℕ}
    {g : ZMod p} (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    (hd : d + 3 ≤ n) :
    (2 : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((n - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  classical
  have hn3 : 3 ≤ n := by omega
  set ix : Fin n := ⟨0, by omega⟩ with hix
  set iy : Fin n := ⟨1, by omega⟩ with hiy
  have hxy : ix ≠ iy := by
    intro hcon
    have := congrArg Fin.val hcon
    simp [hix, hiy] at this
  set u : WordStack (ZMod p) (Fin 2) (Fin n) :=
    ![fun i => if i = ix then 1 else 0,
      fun i => (if i = iy then 1 else 0) - (if i = ix then 1 else 0)] with hu
  -- the witness machinery, symmetric in the deleted point
  have hsize : ∀ j : Fin n, (((Finset.univ.erase j).card : ℕ) : ℝ≥0)
      ≥ (1 - (1 - ((n - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)))
        * (Fintype.card (Fin n) : ℝ≥0) := by
    intro j
    have hn0 : ((n : ℕ) : ℝ≥0) ≠ 0 := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this.ne'
    have hle1 : ((n - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) ≤ 1 := by
      rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0))]
      exact_mod_cast (by omega : n - 1 ≤ n)
    have h1δ : (1 : ℝ≥0) - (1 - ((n - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0))
        = ((n - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := tsub_tsub_cancel_of_le hle1
    rw [h1δ, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin, div_mul_cancel₀ _ hn0]
  -- unfitness of the direction on `univ.erase j ∋ the other deviation point`
  have hunfit : ∀ j w : Fin n, w ≠ j → w ∈ Finset.univ.erase j →
      (∀ i ∈ Finset.univ.erase j, i ≠ w → u 1 i = 0) → u 1 w ≠ 0 →
      ¬ pairJointAgreesOn (evalCode g n d) (Finset.univ.erase j) (u 0) (u 1) := by
    intro j w hwj hwmem hzero hwnz
    rintro ⟨v₀, -, v₁, hv₁, hpair⟩
    obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
    have hzero' : q₁ = 0 := by
      refine fit_unique hginj (B := (Finset.univ.erase j).erase w) ?_ hq₁deg
        (by simp) fun i hib => ?_
      · rw [Finset.card_erase_of_mem hwmem, Finset.card_erase_of_mem
          (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
        omega
      · have hiw : i ≠ w := (Finset.mem_erase.mp hib).1
        have hij : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hib).2
        have h1 : v₁ i = u 1 i := (hpair i hij).2
        have h2 : v₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i
        rw [← h2, h1, hzero i hij hiw]
        simp
    have h4 : v₁ w = u 1 w := (hpair w hwmem).2
    have h5 : v₁ w = q₁.eval (g ^ (w : ℕ)) := hq₁ w
    rw [hzero'] at h5
    simp only [Polynomial.eval_zero] at h5
    exact hwnz (by rw [← h4, h5])
  set Λ : Finset (ZMod p) := {0, 1} with hΛ
  have hΛcard : Λ.card = 2 := by
    rw [hΛ]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g n d)
      (1 - ((n - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro γ hγ
    have hγ01 : γ = 0 ∨ γ = 1 := by
      rcases Finset.mem_insert.mp hγ with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Finset.mem_singleton.mp h1)
    rcases hγ01 with rfl | rfl
    · -- γ = 0: the line is `e_x`; witness erases `x`, direction deviates at `y`
      refine ⟨Finset.univ.erase ix, hsize ix,
        ⟨fun i => (0 : Polynomial (ZMod p)).eval (g ^ (i : ℕ)),
         polyEval_mem_evalCode 0 (by simp), ?_⟩, ?_⟩
      · intro i hi
        have hix' : i ≠ ix := (Finset.mem_erase.mp hi).1
        rw [hu]
        simp [hix']
      · refine hunfit ix iy hxy.symm (Finset.mem_erase.mpr ⟨hxy.symm,
          Finset.mem_univ _⟩) (fun i hi hiy' => ?_) ?_
        · have hix' : i ≠ ix := (Finset.mem_erase.mp hi).1
          rw [hu]
          simp [hiy', hix']
        · rw [hu]
          simp [hxy.symm]
    · -- γ = 1: the line is `e_y`; witness erases `y`, direction deviates at `x`
      refine ⟨Finset.univ.erase iy, hsize iy,
        ⟨fun i => (0 : Polynomial (ZMod p)).eval (g ^ (i : ℕ)),
         polyEval_mem_evalCode 0 (by simp), ?_⟩, ?_⟩
      · intro i hi
        have hiy' : i ≠ iy := (Finset.mem_erase.mp hi).1
        rw [hu]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
          Polynomial.eval_zero, one_mul]
        rcases ne_or_eq i ix with hne | rfl
        · simp [hne, hiy']
        · simp [hiy']
      · refine hunfit iy ix hxy (Finset.mem_erase.mpr ⟨hxy,
          Finset.mem_univ _⟩) (fun i hi hix' => ?_) ?_
        · have hiy'' : i ≠ iy := (Finset.mem_erase.mp hi).1
          rw [hu]
          simp [hix', hiy'']
        · rw [hu]
          simp [hxy]
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g n d)
    (1 - ((n - 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  rw [hΛcard]
  simp

/-! ## The simplex ladder: the doublet generalized to every radius `e/n`

THE CENSUS DISCOVERY at `(p, n, d) = (17, 8, 1)`, threshold `6`: the exact worst count is
`3`, attained by stacks whose three bad scalars carry weight-2 error patterns on the
support triangle `{a,b}, {a,c}, {b,c}` — an affine line of words through three weight-2
patterns.  The general mechanism: fix an `(e+1)`-point set `X`; the line
`u₀ + γu₁` of words supported on `X` passes through `e + 1` *weight-`e`* words (one per
point of `X`, at the scalar killing that coordinate).  Each such scalar is bad at
agreement `n − e` with the ZERO codeword, and the direction (supported on `X`, nonzero at
the surviving point) is unfit.  Count `e + 1` at radius `e/n` — the doublet is `e = 1`.
The census certifies the simplex value is EXACT at `(d, t) = (1, 6)` (`W_6 = 3`,
char-0 layer) — the first cell where the simplex strictly beats every other family. -/

open Classical in
/-- **The simplex-ladder lower bound**: `e + 1` bad scalars at radius `1 − (n−e)/n`, for
every `1 ≤ e ≤ n − d − 2`.  At `e = 1` this is the doublet bound; the families fill every
threshold between the pencil rungs. -/
theorem simplex_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {d e : ℕ}
    {g : ZMod p} (hg : orderOf g = n) (he1 : 1 ≤ e) (hed : e + d + 2 ≤ n) :
    ((e + 1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  classical
  have hn0 : 0 < n := by omega
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ n = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega : n ≠ 0)] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    exact Fin.ext (pow_inj_below_order''' hg0 hg _ i.isLt _ j.isLt hij)
  -- the domain order divides `p − 1`, so `n < p`: small casts are injective
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdvd : n ∣ p - 1 := by
    have hpow : g ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hg0
    exact hg ▸ orderOf_dvd_of_pow_eq_one hpow
  have hnp : n < p := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hcast : ∀ a b : ℕ, a < p → b < p → ((a : ZMod p) = (b : ZMod p)) → a = b := by
    intro a b ha hb hab
    have hmod := (ZMod.natCast_eq_natCast_iff a b p).mp hab
    have h1 : a % p = b % p := hmod
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
    exact h1
  -- the stack: a line of words supported on the simplex `X = {0, …, e}`
  set u : WordStack (ZMod p) (Fin 2) (Fin n) :=
    ![fun j => if (j : ℕ) ≤ e then (((j : ℕ) : ℕ) : ZMod p) else 0,
      fun j => if (j : ℕ) ≤ e then 1 else 0] with hu
  set Λ : Finset (ZMod p) :=
    Finset.univ.image (fun i : Fin (e + 1) => -(((i : ℕ) : ZMod p))) with hΛ
  have hΛcard : Λ.card = e + 1 := by
    have hinj : Function.Injective (fun i : Fin (e + 1) => -(((i : ℕ) : ZMod p))) := by
      intro i j hij
      simp only at hij
      have h1 : (((i : ℕ) : ℕ) : ZMod p) = (((j : ℕ) : ℕ) : ZMod p) :=
        neg_injective hij
      exact Fin.ext (hcast _ _ (by have := i.isLt; omega) (by have := j.isLt; omega) h1)
    rw [hΛ, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  -- the witness injection: the surviving simplex point plus everything above `e`
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g n d)
      (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro γ hγ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
    have hie : (i : ℕ) ≤ e := by have := i.isLt; omega
    set xi : Fin n := ⟨(i : ℕ), by omega⟩ with hxi
    have hflt : ∀ k : Fin (n - e - 1), (k : ℕ) + e + 1 < n := fun k => by
      have := k.isLt
      omega
    set f : Fin (n - e - 1) → Fin n := fun k => ⟨(k : ℕ) + e + 1, hflt k⟩ with hf
    set Stail : Finset (Fin n) := Finset.univ.image f with hSt
    have htail_gt : ∀ j ∈ Stail, e < (j : ℕ) := by
      intro j hjt
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hjt
      subst hk
      show e < (k : ℕ) + e + 1
      omega
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 := congrArg Fin.val hab
      simp only [hf] at h1
      exact Fin.ext (by omega)
    have hStail_card : Stail.card = n - e - 1 := by
      rw [hSt, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
        Fintype.card_fin]
    have hxi_notin : xi ∉ Stail := by
      intro hmem
      have := htail_gt xi hmem
      simp only [hxi] at this
      omega
    set S : Finset (Fin n) := insert xi Stail with hS
    have hScard : S.card = n - e := by
      rw [hS, Finset.card_insert_of_notMem hxi_notin, hStail_card]
      omega
    refine ⟨S, ?_, ⟨fun j => (0 : Polynomial (ZMod p)).eval (g ^ (j : ℕ)),
      polyEval_mem_evalCode 0 (by simp), ?_⟩, ?_⟩
    · -- size: |S| = n − e = (1 − δ)·n
      have hn0' : ((n : ℕ) : ℝ≥0) ≠ 0 := by
        exact_mod_cast hn0.ne'
      have hle1 : ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) ≤ 1 := by
        rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0'))]
        exact_mod_cast (by omega : n - e ≤ n)
      have h1δ : (1 : ℝ≥0) - (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0))
          = ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := tsub_tsub_cancel_of_le hle1
      rw [hScard, h1δ, Fintype.card_fin, div_mul_cancel₀ _ hn0']
    · -- agreement with the zero codeword on the witness
      intro j hj
      rw [hu]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
        Polynomial.eval_zero]
      rcases Finset.mem_insert.mp hj with rfl | hjt
      · simp only [hxi, hie, if_pos]
        ring
      · have hgt := htail_gt j hjt
        have hnle : ¬ (j : ℕ) ≤ e := by omega
        simp [hnle]
    · -- the direction is unfit: it vanishes on the tail but not at the simplex point
      rintro ⟨v₀, -, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hq₁zero : q₁ = 0 := by
        refine fit_unique hginj (B := Stail) ?_ hq₁deg (by simp) fun j hjt => ?_
        · rw [hStail_card]
          omega
        · have hgt := htail_gt j hjt
          have hnle : ¬ (j : ℕ) ≤ e := by omega
          have h1 : v₁ j = u 1 j := (hpair j (Finset.mem_insert_of_mem hjt)).2
          have h2 : v₁ j = q₁.eval (g ^ (j : ℕ)) := hq₁ j
          rw [← h2, h1, hu]
          simp [hnle]
      have h4 : v₁ xi = u 1 xi := (hpair xi (Finset.mem_insert_self _ _)).2
      have h5 : v₁ xi = q₁.eval (g ^ ((xi : Fin n) : ℕ)) := hq₁ xi
      rw [hq₁zero] at h5
      simp only [Polynomial.eval_zero] at h5
      have h6 : u 1 xi = 1 := by
        rw [hu]
        simp [hxi, hie]
      rw [← h4, h5] at h6
      exact zero_ne_one h6
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g n d)
    (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  rw [hΛcard]

/-- **The simplex `δ*` upper bound**: at every budget `ε* < (e+1)/p`, the threshold is at
most `1 − (n−e)/n = e/n`.  The ladder `e = 1, 2, …` is the fine-grained floor of the
whole envelope: between pencil rungs, the count decreases by exactly `1` per radius step. -/
theorem mcaDeltaStar_le_simplex {p n : ℕ} [Fact p.Prime] [NeZero n] {d e : ℕ}
    {g : ZMod p} (hg : orderOf g = n) (he1 : 1 ≤ e) (hed : e + d + 2 ≤ n)
    (εstar : ℝ≥0∞) (hεstar : εstar < ((e + 1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar
      ≤ 1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) :=
  mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (simplex_epsMCA_lower_bound hg he1 hed))

/-! ## The bisimplex: two disjoint simplices on one line — THE ROUND-8 DISCOVERY

The census surplus cells decompose: at `(p, n, d) = (17, 8, 3)`, threshold `6`, the exact
worst count is `7`, and the extremal's per-scalar error supports are the THREE 2-subsets
of `{0,2,6}` **plus** the three 2-subsets of `{1,3,5}` **plus** one extra pair — two
complete simplices riding the SAME affine line, plus a mod-17 coincidence.  The compound
is a genuine char-0 family the catalogue missed:

Take disjoint `(e+1)`-sets `S₁ = {0,…,e}`, `S₂ = {e+1,…,2e+1}`, complement `Z`, and the
vanishing polynomial `q₀ = ∏_{z ∈ Z} (X − z)` (degree `n − 2e − 2`).  Stack:
`u₁ = q₀|_{S₁}` and `u₀ = (X·q₀)|_{S₁}`.  Then `γ = −x` is bad for **every**
`x ∈ S₁ ∪ S₂` — `2e + 2` scalars:

* `x ∈ S₁`: the line word is `((X−x)q₀)|_{S₁}` — weight `≤ e` (it vanishes at `x`),
  within `e` of the ZERO codeword, and the direction is unfit on the witness (it
  vanishes on the `n−e−1` points off `S₁` but not at `x`);
* `x ∈ S₂`: the line word is `(X−x)q₀ − ((X−x)q₀)|_{S₂∪Z}` — the degree-`≤ d` codeword
  `(X−x)q₀` minus a weight-`≤ e` word supported on `S₂ ∖ {x}` (`q₀` kills `Z`), and the
  direction agrees with `q₀` off `S₂` but vanishes at `x` where `q₀` does not.

Count `2e + 2` at radius `e/n`, valid for `n − 2e − 1 ≤ d ≤ n − e − 2` — strictly above
both the simplex (`e+1`) and, at the censused `(d, t) = (3, 6)` cell, the pencil (`4`).
The probe confirms the count word-level at `p ∈ {17, 97}`, and the exhaustive `p = 97`
shoulder-cell census pins the cell value at exactly `6` = the bisimplex (runner-up `5`):
the family is char-0 real, not a small-field artifact. -/

open Classical in
/-- **The bisimplex lower bound**: `2e + 2` bad scalars at radius `1 − (n−e)/n`, for
every `1 ≤ e` with `2e + 2 ≤ n` and `n − 2e − 1 ≤ d ≤ n − e − 2`.  Two disjoint
simplices share one affine line of words; each point of `S₁ ∪ S₂` contributes the scalar
`−x` killing its coordinate of the corresponding residual. -/
theorem bisimplex_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {d e : ℕ}
    {g : ZMod p} (hg : orderOf g = n) (he1 : 1 ≤ e) (hed : e + d + 2 ≤ n)
    (hlow : n ≤ d + 2 * e + 1) (h2e : 2 * e + 2 ≤ n) :
    ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  classical
  have hn0 : 0 < n := by omega
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ n = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega : n ≠ 0)] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    exact Fin.ext (pow_inj_below_order''' hg0 hg _ i.isLt _ j.isLt hij)
  -- the vanishing polynomial of the complement `Z = {2e+2, …, n−1}`
  set Zc : ℕ := n - (2 * e + 2) with hZc
  set q0 : Polynomial (ZMod p) :=
    ∏ j ∈ Finset.range Zc, (Polynomial.X - Polynomial.C (g ^ (2 * e + 2 + j)))
    with hq0
  have hq0deg : q0.natDegree = Zc := by
    rw [hq0, Polynomial.natDegree_prod_of_monic _ _
      (fun j _ => Polynomial.monic_X_sub_C _)]
    rw [Finset.sum_congr rfl
      (fun j _ => Polynomial.natDegree_X_sub_C (g ^ (2 * e + 2 + j)))]
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range]
  have hq0eval : ∀ x : ZMod p,
      q0.eval x = ∏ j ∈ Finset.range Zc, (x - g ^ (2 * e + 2 + j)) := by
    intro x
    rw [hq0]
    simp [Polynomial.eval_prod]
  have hq0_ne : ∀ a : ℕ, a < 2 * e + 2 → q0.eval (g ^ a) ≠ 0 := by
    intro a ha
    rw [hq0eval]
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [Finset.mem_range] at hj
    intro hzero
    have heq : g ^ a = g ^ (2 * e + 2 + j) := sub_eq_zero.mp hzero
    have h1 : (⟨a, by omega⟩ : Fin n) = ⟨2 * e + 2 + j, by omega⟩ :=
      hginj _ _ heq
    have h2 := congrArg Fin.val h1
    simp only at h2
    omega
  have hq0_zero : ∀ a : ℕ, 2 * e + 2 ≤ a → a < n → q0.eval (g ^ a) = 0 := by
    intro a ha han
    rw [hq0eval]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr
      (show a - (2 * e + 2) < Zc by omega)) ?_
    have h1 : 2 * e + 2 + (a - (2 * e + 2)) = a := by omega
    rw [h1, sub_self]
  -- the stack: the line `(X·q₀)|_{S₁} + γ·q₀|_{S₁}`
  set u : WordStack (ZMod p) (Fin 2) (Fin n) :=
    ![fun j => if (j : ℕ) ≤ e then g ^ (j : ℕ) * q0.eval (g ^ (j : ℕ)) else 0,
      fun j => if (j : ℕ) ≤ e then q0.eval (g ^ (j : ℕ)) else 0] with hu
  set Λ : Finset (ZMod p) :=
    Finset.univ.image (fun i : Fin (2 * e + 2) => -(g ^ (i : ℕ))) with hΛ
  have hΛcard : Λ.card = 2 * e + 2 := by
    have hinj : Function.Injective (fun i : Fin (2 * e + 2) => -(g ^ (i : ℕ))) := by
      intro i j hij
      simp only at hij
      have heq : g ^ (i : ℕ) = g ^ (j : ℕ) := neg_injective hij
      exact Fin.ext (pow_inj_below_order''' hg0 hg _
        (lt_of_lt_of_le i.isLt h2e) _ (lt_of_lt_of_le j.isLt h2e) heq)
    rw [hΛ, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  -- shared witness-size arithmetic
  have hsizeS : ∀ S : Finset (Fin n), S.card = n - e →
      ((S.card : ℕ) : ℝ≥0) ≥ (1 - (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)))
        * (Fintype.card (Fin n) : ℝ≥0) := by
    intro S hS
    have hn0' : ((n : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hn0.ne'
    have hle1 : ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) ≤ 1 := by
      rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0'))]
      exact_mod_cast (by omega : n - e ≤ n)
    have h1δ : (1 : ℝ≥0) - (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0))
        = ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := tsub_tsub_cancel_of_le hle1
    rw [hS, h1δ, Fintype.card_fin, div_mul_cancel₀ _ hn0']
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g n d)
      (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro γ hγ
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hγ
    set a₀ : ℕ := (a : ℕ) with ha₀_def
    have ha₀lt : a₀ < 2 * e + 2 := a.isLt
    have ha₀n : a₀ < n := by omega
    set xa : Fin n := ⟨a₀, ha₀n⟩ with hxa
    rcases Nat.lt_or_ge a₀ (e + 1) with hae1 | hae1
    · -- `x ∈ S₁`: the simplex case against the ZERO codeword
      have hae : a₀ ≤ e := by omega
      have hflt : ∀ k : Fin (n - e - 1), (k : ℕ) + e + 1 < n := fun k => by
        have := k.isLt
        omega
      set f : Fin (n - e - 1) → Fin n := fun k => ⟨(k : ℕ) + e + 1, hflt k⟩ with hf
      set Stail : Finset (Fin n) := Finset.univ.image f with hSt
      have htail_gt : ∀ j ∈ Stail, e < (j : ℕ) := by
        intro j hjt
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hjt
        subst hk
        show e < (k : ℕ) + e + 1
        omega
      have hfinj : Function.Injective f := by
        intro a b hab
        have h1 := congrArg Fin.val hab
        simp only [hf] at h1
        exact Fin.ext (by omega)
      have hStail_card : Stail.card = n - e - 1 := by
        rw [hSt, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
          Fintype.card_fin]
      have hxa_notin : xa ∉ Stail := by
        intro hmem
        have := htail_gt xa hmem
        simp only [hxa] at this
        omega
      set S : Finset (Fin n) := insert xa Stail with hS
      have hScard : S.card = n - e := by
        rw [hS, Finset.card_insert_of_notMem hxa_notin, hStail_card]
        omega
      refine ⟨S, hsizeS S hScard, ⟨fun j => (0 : Polynomial (ZMod p)).eval
        (g ^ (j : ℕ)), polyEval_mem_evalCode 0 (by simp), ?_⟩, ?_⟩
      · -- agreement with the zero codeword
        intro j hj
        rw [hu]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
          Polynomial.eval_zero]
        rcases Finset.mem_insert.mp hj with rfl | hjt
        · simp only [hxa, hae, if_pos]
          ring
        · have hgt := htail_gt j hjt
          have hnle : ¬ (j : ℕ) ≤ e := by omega
          simp [hnle]
      · -- the direction vanishes on the tail but not at `xa`
        rintro ⟨v₀, -, v₁, hv₁, hpair⟩
        obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
        have hq₁zero : q₁ = 0 := by
          refine fit_unique hginj (B := Stail) ?_ hq₁deg (by simp) fun j hjt => ?_
          · rw [hStail_card]
            omega
          · have hgt := htail_gt j hjt
            have hnle : ¬ (j : ℕ) ≤ e := by omega
            have h1 : v₁ j = u 1 j := (hpair j (Finset.mem_insert_of_mem hjt)).2
            have h2 : v₁ j = q₁.eval (g ^ (j : ℕ)) := hq₁ j
            rw [← h2, h1, hu]
            simp [hnle]
        have h4 : v₁ xa = u 1 xa := (hpair xa (Finset.mem_insert_self _ _)).2
        have h5 : v₁ xa = q₁.eval (g ^ ((xa : Fin n) : ℕ)) := hq₁ xa
        rw [hq₁zero] at h5
        simp only [Polynomial.eval_zero] at h5
        have h6 : u 1 xa = q0.eval (g ^ a₀) := by
          rw [hu]
          simp [hxa, hae]
        rw [← h4, h5] at h6
        exact hq0_ne a₀ ha₀lt h6.symm
    · -- `x ∈ S₂`: the line word is the codeword `(X − g^{a₀})·q₀` minus a weight-`≤ e`
      -- word supported on `S₂ ∖ {x}`
      have ha₀2 : e + 1 ≤ a₀ := hae1
      set P : Polynomial (ZMod p) :=
        (Polynomial.X - Polynomial.C (g ^ a₀)) * q0 with hP
      have hPdeg : P.natDegree ≤ d := by
        refine le_trans (Polynomial.natDegree_mul_le) ?_
        rw [Polynomial.natDegree_X_sub_C, hq0deg]
        omega
      have hPeval : ∀ x : ZMod p, P.eval x = (x - g ^ a₀) * q0.eval x := by
        intro x
        rw [hP]
        simp [Polynomial.eval_mul, Polynomial.eval_sub]
      -- the witness: `S₁`, the complement `Z`, and `xa`
      have hhflt : ∀ k : Fin (e + 1), (k : ℕ) < n := fun k => by
        have := k.isLt
        omega
      set fh : Fin (e + 1) → Fin n := fun k => ⟨(k : ℕ), hhflt k⟩ with hfh
      set Shead : Finset (Fin n) := Finset.univ.image fh with hSh
      have hhead_le : ∀ j ∈ Shead, (j : ℕ) ≤ e := by
        intro j hjh
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hjh
        subst hk
        show (k : ℕ) ≤ e
        have := k.isLt
        omega
      have hfhinj : Function.Injective fh := by
        intro a b hab
        have h1 := congrArg Fin.val hab
        simp only [hfh] at h1
        exact Fin.ext h1
      have hShead_card : Shead.card = e + 1 := by
        rw [hSh, Finset.card_image_of_injective _ hfhinj, Finset.card_univ,
          Fintype.card_fin]
      have hzflt : ∀ k : Fin Zc, 2 * e + 2 + (k : ℕ) < n := fun k => by
        have := k.isLt
        omega
      set fz : Fin Zc → Fin n := fun k => ⟨2 * e + 2 + (k : ℕ), hzflt k⟩ with hfz
      set Sz : Finset (Fin n) := Finset.univ.image fz with hSz
      have hz_ge : ∀ j ∈ Sz, 2 * e + 2 ≤ (j : ℕ) := by
        intro j hjz
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hjz
        subst hk
        show 2 * e + 2 ≤ 2 * e + 2 + (k : ℕ)
        omega
      have hfzinj : Function.Injective fz := by
        intro a b hab
        have h1 := congrArg Fin.val hab
        simp only [hfz] at h1
        exact Fin.ext (by omega)
      have hSz_card : Sz.card = Zc := by
        rw [hSz, Finset.card_image_of_injective _ hfzinj, Finset.card_univ,
          Fintype.card_fin]
      have hdisj : Disjoint Shead Sz := by
        rw [Finset.disjoint_right]
        intro j hjz hjh
        have h1 := hhead_le j hjh
        have h2 := hz_ge j hjz
        omega
      set B : Finset (Fin n) := Shead ∪ Sz with hB
      have hBcard : B.card = n - e - 1 := by
        rw [hB, Finset.card_union_of_disjoint hdisj, hShead_card, hSz_card]
        omega
      have hxa_notinB : xa ∉ B := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hh | hz
        · have := hhead_le xa hh
          simp only [hxa] at this
          omega
        · have := hz_ge xa hz
          simp only [hxa] at this
          omega
      set S : Finset (Fin n) := insert xa B with hS
      have hScard : S.card = n - e := by
        rw [hS, Finset.card_insert_of_notMem hxa_notinB, hBcard]
        omega
      refine ⟨S, hsizeS S hScard, ⟨fun j => P.eval (g ^ (j : ℕ)),
        polyEval_mem_evalCode P hPdeg, ?_⟩, ?_⟩
      · -- agreement with the codeword `(X − g^{a₀})·q₀` on the witness
        intro j hj
        rw [hu]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
        rw [hPeval]
        rcases Finset.mem_insert.mp hj with rfl | hjB
        · have hnle : ¬ (xa : ℕ) ≤ e := by
            simp only [hxa]
            omega
          simp only [hnle, if_neg, not_false_iff]
          simp only [hxa]
          ring_nf
        · rcases Finset.mem_union.mp hjB with hjh | hjz
          · have hle := hhead_le j hjh
            simp only [hle, if_pos]
            ring
          · have hge := hz_ge j hjz
            have hnle : ¬ (j : ℕ) ≤ e := by omega
            simp only [hnle, if_neg, not_false_iff]
            rw [hq0_zero (j : ℕ) hge j.isLt]
            ring
      · -- the direction agrees with `q₀` on `B` but vanishes at `xa` where `q₀` does not
        rintro ⟨v₀, -, v₁, hv₁, hpair⟩
        obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
        have hq₁q0 : q₁ = q0 := by
          refine fit_unique hginj (B := B) ?_ hq₁deg
            (by rw [hq0deg]; omega) fun j hjB => ?_
          · rw [hBcard]
            omega
          · have h1 : v₁ j = u 1 j := (hpair j (Finset.mem_insert_of_mem hjB)).2
            have h2 : v₁ j = q₁.eval (g ^ (j : ℕ)) := hq₁ j
            rcases Finset.mem_union.mp hjB with hjh | hjz
            · have hle := hhead_le j hjh
              rw [← h2, h1, hu]
              simp [hle]
            · have hge := hz_ge j hjz
              have hnle : ¬ (j : ℕ) ≤ e := by omega
              rw [← h2, h1, hu, hq0_zero (j : ℕ) hge j.isLt]
              simp [hnle]
        have h4 : v₁ xa = u 1 xa := (hpair xa (Finset.mem_insert_self _ _)).2
        have h5 : v₁ xa = q₁.eval (g ^ ((xa : Fin n) : ℕ)) := hq₁ xa
        rw [hq₁q0] at h5
        have h6 : u 1 xa = 0 := by
          have hnle : ¬ (xa : ℕ) ≤ e := by
            simp only [hxa]
            omega
          rw [hu]
          simp [hnle]
        have h7 : q0.eval (g ^ a₀) = 0 := by
          have hxv : ((xa : Fin n) : ℕ) = a₀ := rfl
          rw [← hxv, ← h5, h4, h6]
        exact hq0_ne a₀ ha₀lt h7
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g n d)
    (1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  rw [hΛcard]

/-- **The bisimplex `δ*` upper bound**: at every budget `ε* < (2e+2)/p`, the threshold is
at most `e/n`.  In its validity window `n − 2e − 1 ≤ d ≤ n − e − 2` the bisimplex
strictly dominates the simplex (`2e+2 > e+1`) and widens every envelope band it
touches. -/
theorem mcaDeltaStar_le_bisimplex {p n : ℕ} [Fact p.Prime] [NeZero n] {d e : ℕ}
    {g : ZMod p} (hg : orderOf g = n) (he1 : 1 ≤ e) (hed : e + d + 2 ≤ n)
    (hlow : n ≤ d + 2 * e + 1) (h2e : 2 * e + 2 ≤ n)
    (εstar : ℝ≥0∞) (hεstar : εstar < ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar
      ≤ 1 - ((n - e : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) :=
  mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (bisimplex_epsMCA_lower_bound hg he1 hed hlow h2e))

/-! ## The pencil ladder at the first biting instance (`p = 12289`, `n = 16`)

Round 7 trapped the `d = 2` level-1 rung band to `[16/p, 32/p)` via the `s = 1` pencil.
The deeper rungs now extend the proven upper envelope strictly below `7/16`: the `s = 2`
pencil (`8` bad scalars at `3/8`) and, against the `d = 4` code, the `s = 4` pencil
(`4` bad scalars at `1/4`). -/

section Concrete12289

local instance fact_prime_12289''' : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- The `s = 2` pencil at the `d = 2` instance: eight bad scalars at radius `3/8`. -/
theorem pencil2_epsMCA_F12289_d2 :
    (8 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) (3 / 8 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := pencil_rung_epsMCA_lower_bound (p := 12289) (n := 16) (h := 8) (d := 2)
    (s := 2) (by norm_num) (by norm_num) (g := (4134 : ZMod 12289)) orderOf_4134
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 : ((16 / 2 : ℕ) : ℝ≥0∞) = (8 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((8 + 2 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 3 / 8 := by
    have hd : ((8 + 2 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 5 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- **The deepened envelope at the `d = 2` instance**: every budget `ε* < 8/p` forces
`δ* ≤ 3/8` — strictly below the round-7 antipodal value `7/16` (which held on the wider
band `ε* < 16/p`).  The pencil ladder continues the upper staircase downward. -/
theorem deltaStar_le_pencil2_F12289_d2 (εstar : ℝ≥0∞)
    (hεstar : εstar < (8 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 2) εstar ≤ 3 / 8 :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hεstar pencil2_epsMCA_F12289_d2)

/-- The `s = 4` pencil at the `d = 4` instance (rate `5/16`): four bad scalars at radius
`1/4`. -/
theorem pencil4_epsMCA_F12289_d4 :
    (4 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 4) (1 / 4 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := pencil_rung_epsMCA_lower_bound (p := 12289) (n := 16) (h := 8) (d := 4)
    (s := 4) (by norm_num) (by norm_num) (g := (4134 : ZMod 12289)) orderOf_4134
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 : ((16 / 4 : ℕ) : ℝ≥0∞) = (4 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((8 + 4 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 1 / 4 := by
    have hd : ((8 + 4 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 3 / 4 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The `d = 4` envelope continues to `δ* ≤ 1/4` at every `ε* < 4/p` (below the round-7
refutation value `7/16`, which needed `ε* < 16/p`). -/
theorem deltaStar_le_pencil4_F12289_d4 (εstar : ℝ≥0∞)
    (hεstar : εstar < (4 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 4) εstar ≤ 1 / 4 :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hεstar pencil4_epsMCA_F12289_d4)

/-- The bisimplex (`e = 6`) at the `d = 4` instance: FOURTEEN bad scalars at radius
`3/8` — strictly above the `s = 2` pencil's `8` at the same radius.  The widest
bad family known at this `(rate, radius)` point. -/
theorem bisimplex_epsMCA_F12289_d4 :
    (14 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 4) (3 / 8 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := bisimplex_epsMCA_lower_bound (p := 12289) (n := 16) (d := 4) (e := 6)
    (g := (4134 : ZMod 12289)) orderOf_4134 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : ((2 * 6 + 2 : ℕ) : ℝ≥0∞) = (14 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((16 - 6 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 3 / 8 := by
    have hd : ((16 - 6 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 5 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The `d = 4` budget band `ε* < 14/p` forces `δ* ≤ 3/8` — the bisimplex widens the
band of the `3/8` rung from the pencil's `ε* < 8/p` to `ε* < 14/p`. -/
theorem deltaStar_le_bisimplex_F12289_d4 (εstar : ℝ≥0∞)
    (hεstar : εstar < (14 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 4) εstar ≤ 3 / 8 :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hεstar bisimplex_epsMCA_F12289_d4)

end Concrete12289

/-! ## The censused instance: `p = 17`, `n = 8`, `g = 2`, `d = 2` (rate `3/8`)

The probe's exhaustive cells (`W_t` = exact max bad count over ALL stacks at threshold
`t`, certified by the all-lines syndrome census with the exact side condition):

  `W_4 = 17 = p` (explosion band, support-compact stacks) · `W_5 = 11` (mod-17 surplus
  `8 + 3`: the extremal is an OVERLAPPING bisimplex — two `e = 3` simplices
  `{0,2,4,7}`, `{3,5,6,7}` sharing one point — plus a 3-scalar sunflower at a second
  point; the char-0 layer `8` is the pencil/bisimplex value) · `W_6 = 4` (the `s = 2`
  pencil, catalogue-EXACT) · `W_7 = 2` (the doublet/simplex, catalogue-EXACT) ·
  `W_8 = 1`.

The bad sides provable from the general family theorems are below; the matching good
sides — true by exhaustion — are the named census conjecture. -/

section CensusF17

local instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `2` generates the `8`-element smooth domain in `F₁₇ˣ`. -/
theorem orderOf_two_F17 : orderOf (2 : ZMod 17) = 8 := by
  have h4 : ¬ (2 : ZMod 17) ^ (2 : ℕ) ^ 2 = 1 := by decide
  have h8 : (2 : ZMod 17) ^ (2 : ℕ) ^ 3 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (2 : ZMod 17)) h4 h8
  norm_num at h
  exact h

/-- The `s = 1` (antipodal) pencil at the censused instance: eight bad scalars at radius
`3/8` — the char-0 layer of the censused `W_5`. -/
theorem pencil1_epsMCA_F17 :
    (8 : ℝ≥0∞) / (17 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) (3 / 8 : ℝ≥0) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := pencil_rung_epsMCA_lower_bound (p := 17) (n := 8) (h := 4) (d := 2)
    (s := 1) (by norm_num) (by norm_num) (g := (2 : ZMod 17)) orderOf_two_F17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 : ((8 / 1 : ℕ) : ℝ≥0∞) = (8 : ℝ≥0∞) := by norm_num
  have e2 : ((17 : ℕ) : ℝ≥0∞) = (17 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((4 + 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 3 / 8 := by
    have hd : ((4 + 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 5 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The `s = 2` pencil at the censused instance: four bad scalars at radius `1/4` — the
census certifies `W_6 = 4` is EXACTLY this family. -/
theorem pencil2_epsMCA_F17 :
    (4 : ℝ≥0∞) / (17 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) (1 / 4 : ℝ≥0) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := pencil_rung_epsMCA_lower_bound (p := 17) (n := 8) (h := 4) (d := 2)
    (s := 2) (by norm_num) (by norm_num) (g := (2 : ZMod 17)) orderOf_two_F17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 : ((8 / 2 : ℕ) : ℝ≥0∞) = (4 : ℝ≥0∞) := by norm_num
  have e2 : ((17 : ℕ) : ℝ≥0∞) = (17 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((4 + 2 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 1 / 4 := by
    have hd : ((4 + 2 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 3 / 4 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The simplex (`e = 1`, the doublet) at the censused instance: two bad scalars at
radius `1/8` — the census certifies `W_7 = 2` is EXACTLY this family. -/
theorem simplex1_epsMCA_F17 :
    (2 : ℝ≥0∞) / (17 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) (1 / 8 : ℝ≥0) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := simplex_epsMCA_lower_bound (p := 17) (n := 8) (d := 2) (e := 1)
    (g := (2 : ZMod 17)) orderOf_two_F17 (by norm_num) (by norm_num)
  have e1 : ((1 + 1 : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) := by norm_num
  have e2 : ((17 : ℕ) : ℝ≥0∞) = (17 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((8 - 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 1 / 8 := by
    have hd : ((8 - 1 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 7 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The bisimplex at the censused boundary instance `d = 3` (the `(d, t) = (3, 6)`
cell): SIX bad scalars at radius `1/4` — the char-0 layer of the censused `W_6 = 7`
(`7 = 6 + 1`: the probe's extremal decomposes into the two simplex triangles
`{0,2,6}`, `{1,3,5}` plus one mod-17 extra pair on the complement `{4,7}`). -/
theorem bisimplex_epsMCA_F17_d3 :
    (6 : ℝ≥0∞) / (17 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 3) (1 / 4 : ℝ≥0) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := bisimplex_epsMCA_lower_bound (p := 17) (n := 8) (d := 3) (e := 2)
    (g := (2 : ZMod 17)) orderOf_two_F17 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : ((2 * 2 + 2 : ℕ) : ℝ≥0∞) = (6 : ℝ≥0∞) := by norm_num
  have e2 : ((17 : ℕ) : ℝ≥0∞) = (17 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((8 - 2 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 1 / 4 := by
    have hd : ((8 - 2 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 3 / 4 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- **The unconditional upper staircase at the censused instance** — the provable bad
sides of the catalogue, in one statement. -/
theorem deltaStar_upper_staircase_F17 (εstar : ℝ≥0∞) :
    (εstar < (8 : ℝ≥0∞) / (17 : ℝ≥0∞) →
      mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar ≤ 3 / 8) ∧
    (εstar < (4 : ℝ≥0∞) / (17 : ℝ≥0∞) →
      mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar ≤ 1 / 4) ∧
    (εstar < (2 : ℝ≥0∞) / (17 : ℝ≥0∞) →
      mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar ≤ 1 / 8) :=
  ⟨fun h => mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le h pencil1_epsMCA_F17),
   fun h => mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le h pencil2_epsMCA_F17),
   fun h => mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le h simplex1_epsMCA_F17)⟩

/-- **THE COMPLETE-ENVELOPE CONJECTURE at the censused instance** — the good sides.  The
exhaustive census measured the exact worst-stack counts `W_8 = 1, W_7 = 2, W_6 = 4,
W_5 = 11` over EVERY stack (every affine line in syndrome space, side condition exact):
this Prop asserts the matching `ε_mca` upper bounds — i.e. that `ε_mca` equals the
censused envelope on every band.  It is TRUE by the (Python) exhaustion recorded in
`scripts/probes/probe_bad_family_census.py`; what is missing is only a kernel-checkable
certificate, so it stays a named obligation in the round-7 convention
(`SubCeilingInteriorCeiling` etc.). -/
def CompleteEnvelopeF17 : Prop :=
  (∀ δ : ℝ≥0, δ < 1 / 8 →
    epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) δ ≤ (1 : ℝ≥0∞) / (17 : ℝ≥0∞)) ∧
  (∀ δ : ℝ≥0, δ < 1 / 4 →
    epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) δ ≤ (2 : ℝ≥0∞) / (17 : ℝ≥0∞)) ∧
  (∀ δ : ℝ≥0, δ < 3 / 8 →
    epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) δ ≤ (4 : ℝ≥0∞) / (17 : ℝ≥0∞)) ∧
  (∀ δ : ℝ≥0, δ < 1 / 2 →
    epsMCA (F := ZMod 17) (evalCode (2 : ZMod 17) 8 2) δ ≤ (11 : ℝ≥0∞) / (17 : ℝ≥0∞))

/-- **The conditional full curve at the censused instance**: granting the census-true
good sides, the δ* curve of `RS[F₁₇, ⟨2⟩, deg ≤ 2]` is pinned EXACTLY on three
consecutive budget bands, with the fourth band bounded from below —

  `δ*(ε*) = 1/8` on `[1/17, 2/17)` · `= 1/4` on `[2/17, 4/17)` · `= 3/8` on
  `[4/17, 8/17)` · `≥ 1/2` on `[11/17, ∞)`.

(The census says `δ* = 3/8` in fact persists through `[8/17, 11/17)` — the bad side
there is the 11-scalar overlapping-bisimplex-plus-sunflower compound, whose char-0
layer `8` is in-tree (`pencil1_epsMCA_F17`) while the mod-17 `+3` has no in-tree
construction yet — and `= 1/2` on `[11/17, 1)`, whose bad side is the explosion
stack.)  This is the first instance whose whole budget curve is reduced to one
census-verified hypothesis: the three pinned band values are attained by catalogue
families, and the census checked every stack. -/
theorem completeEnvelopeF17_curve (hint : CompleteEnvelopeF17) :
    (∀ εstar : ℝ≥0∞, (1 : ℝ≥0∞) / (17 : ℝ≥0∞) ≤ εstar →
      εstar < (2 : ℝ≥0∞) / (17 : ℝ≥0∞) →
      mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar = 1 / 8) ∧
    (∀ εstar : ℝ≥0∞, (2 : ℝ≥0∞) / (17 : ℝ≥0∞) ≤ εstar →
      εstar < (4 : ℝ≥0∞) / (17 : ℝ≥0∞) →
      mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar = 1 / 4) ∧
    (∀ εstar : ℝ≥0∞, (4 : ℝ≥0∞) / (17 : ℝ≥0∞) ≤ εstar →
      εstar < (8 : ℝ≥0∞) / (17 : ℝ≥0∞) →
      mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar = 3 / 8) ∧
    (∀ εstar : ℝ≥0∞, (11 : ℝ≥0∞) / (17 : ℝ≥0∞) ≤ εstar →
      (1 / 2 : ℝ≥0) ≤ mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar) := by
  obtain ⟨h18, h14, h38, h12⟩ := hint
  refine ⟨fun εstar hlo hhi => ?_, fun εstar hlo hhi => ?_,
    fun εstar hlo hhi => ?_, fun εstar hlo => ?_⟩
  · refine mcaDeltaStar_eq_of_good_below_of_bad_above _ εstar
      (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]; norm_num)
      (fun δ hδ => le_trans (h18 δ hδ) hlo)
      (fun δ hδ => lt_of_lt_of_le hhi ?_)
    exact le_trans simplex1_epsMCA_F17
      (epsMCA_mono (F := ZMod 17) (A := ZMod 17) _ hδ)
  · refine mcaDeltaStar_eq_of_good_below_of_bad_above _ εstar
      (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]; norm_num)
      (fun δ hδ => le_trans (h14 δ hδ) hlo)
      (fun δ hδ => lt_of_lt_of_le hhi ?_)
    exact le_trans pencil2_epsMCA_F17
      (epsMCA_mono (F := ZMod 17) (A := ZMod 17) _ hδ)
  · refine mcaDeltaStar_eq_of_good_below_of_bad_above _ εstar
      (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]; norm_num)
      (fun δ hδ => le_trans (h38 δ hδ) hlo)
      (fun δ hδ => lt_of_lt_of_le hhi ?_)
    exact le_trans pencil1_epsMCA_F17
      (epsMCA_mono (F := ZMod 17) (A := ZMod 17) _ hδ)
  · -- the fourth band: every `δ < 1/2` is good, so `δ* ≥ 1/2`
    by_contra hnot
    rw [not_le] at hnot
    obtain ⟨δ, hδlo, hδhi⟩ := exists_between hnot
    have hgood : δ ≤ mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (evalCode (2 : ZMod 17) 8 2) εstar :=
      le_mcaDeltaStar_of_good _ _
        (le_of_lt (lt_of_lt_of_le hδhi
          (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 2)]; norm_num)))
        (le_trans (h12 δ hδhi) hlo)
    exact absurd hgood (not_le_of_gt hδlo)

end CensusF17

end ArkLib.ProximityGap.BadFamilyCensus

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.BadFamilyCensus.pencil_rung_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.BadFamilyCensus.mcaDeltaStar_le_pencil_rung
#print axioms ArkLib.ProximityGap.BadFamilyCensus.two_deviation_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.BadFamilyCensus.simplex_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.BadFamilyCensus.mcaDeltaStar_le_simplex
#print axioms ArkLib.ProximityGap.BadFamilyCensus.bisimplex_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.BadFamilyCensus.mcaDeltaStar_le_bisimplex
#print axioms ArkLib.ProximityGap.BadFamilyCensus.bisimplex_epsMCA_F12289_d4
#print axioms ArkLib.ProximityGap.BadFamilyCensus.deltaStar_le_bisimplex_F12289_d4
#print axioms ArkLib.ProximityGap.BadFamilyCensus.bisimplex_epsMCA_F17_d3
#print axioms ArkLib.ProximityGap.BadFamilyCensus.pencil2_epsMCA_F12289_d2
#print axioms ArkLib.ProximityGap.BadFamilyCensus.deltaStar_le_pencil2_F12289_d2
#print axioms ArkLib.ProximityGap.BadFamilyCensus.pencil4_epsMCA_F12289_d4
#print axioms ArkLib.ProximityGap.BadFamilyCensus.deltaStar_le_pencil4_F12289_d4
#print axioms ArkLib.ProximityGap.BadFamilyCensus.orderOf_two_F17
#print axioms ArkLib.ProximityGap.BadFamilyCensus.pencil1_epsMCA_F17
#print axioms ArkLib.ProximityGap.BadFamilyCensus.pencil2_epsMCA_F17
#print axioms ArkLib.ProximityGap.BadFamilyCensus.simplex1_epsMCA_F17
#print axioms ArkLib.ProximityGap.BadFamilyCensus.deltaStar_upper_staircase_F17
#print axioms ArkLib.ProximityGap.BadFamilyCensus.completeEnvelopeF17_curve
