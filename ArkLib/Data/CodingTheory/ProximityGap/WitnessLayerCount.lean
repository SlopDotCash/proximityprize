/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPow

/-!
# Issue #334 — The witness-layer count: balanced configs number `C(s/2 − 1, s/4)`

The combinatorial core of O130's general rung law (the per-level descent instance at every
2-power scale `s = 2^j`, `n = 2s`, `H = μ_n`, `w = X^(s+2) − z*·X^s`, `z* = ζ_n^(s/2)`,
code = RS degree `< s`; see `scripts/probes/genlaw/RESULTS-GENERAL-LAW.md`).

The agree-`(s+2)` ("witness") layer reduces, through the consistency equation
`e₂ − e₁² = λ + e₁(B)` at fiber pattern `r = 0`, to the **antipodal balance** of the
`μ_s`-multiset `S_z ⊎ {−z*}` where `S_z` is the set of `s/2 + 1` fibers used by the
agreement set.  Balance (= vanishing in `ℤ[ζ_s]`, by the in-tree criterion
`LamLeungTwoPow.vanishing_iff_antipodal_coeffs`) forces the `z*`-fiber (exponent `s/4`)
IN, the `−z*`-fiber (exponent `3s/4`) OUT, and every other axis fully antipodal, leaving
`s/4` free antipodal pairs on the remaining `s/2 − 1` axes:

  **`#{balanced witness configs} = C(s/2 − 1, s/4)`.**

Rungs: `3` (s = 8, C19), `35` (s = 16, O87), `6435 = C(15,8)` (s = 32, the blind n = 64
forecast that survived independent enumeration), `300540195 = C(31,16)` (s = 64).

Contents:

* `balanced_iff` — the balance-forcing structure: `S ⊎ {q+h}` is antipodally balanced iff
  `q ∈ S`, `q + h ∉ S`, and every other axis is fully in or fully out.
* `balanced_card` — the count, abstract form: for any `q < h` and any `k`, the number of
  `(2k+1)`-subsets of `range (2h)` whose layer multiset is balanced is `C(h − 1, k)`,
  via the explicit bijection with `k`-subsets of the `h − 1` non-`q` axes.
* `layer_vanishing_iff` / `witness_layer_card` — the composition with the in-tree
  field criterion at scale `s = 2^(m+2)`: the vanishing-sum configs number
  `C(2^(m+1) − 1, 2^m)`.
* `witness_e1_card` — the same count in `e₁`-form: `#{S : |S| = s/2+1, Σ_{e∈S} ζ^e = z*}`.
* `sum_ne_zero_of_support_lower_half` / `sum_ne_zero_of_no_antipodal_pair` — the even-`r`
  death lemma: a nonzero-coefficient (in particular `±1`) combination supported on
  exponents below `2^m` — equivalently a set of roots with no antipodal pair — cannot
  vanish (free power basis; direct corollary of `nonvanishing_of_unpaired`).

What this does NOT contain (honest scope): the reduction from RS-codeword agreement sets
to the balance equation (the `e₂ − e₁²` consistency-equation derivation and the
agreement-`> s+2` impossibility); those remain charted in the probe docs.
-/

namespace WitnessLayer

open Finset

/-! ## The layer multiset and its balance condition (pure combinatorics) -/

/-- The multiplicity function of the witness-layer multiset `S ⊎ {t}` on exponents:
the indicator of `S` plus an extra unit mass at the slot `t` (the `−z*` exponent). -/
def layerMult (S : Finset ℕ) (t e : ℕ) : ℕ :=
  (if e ∈ S then 1 else 0) + (if e = t then 1 else 0)

/-- Antipodal balance of the layer multiset at half-period `h`: the multiplicity at `e`
equals the multiplicity at the antipode `e + h`, for every `e < h`. -/
def Balanced (h t : ℕ) (S : Finset ℕ) : Prop :=
  ∀ e < h, layerMult S t e = layerMult S t (e + h)

instance decidableBalanced (h t : ℕ) : DecidablePred (Balanced h t) := fun S =>
  inferInstanceAs (Decidable (∀ e < h, layerMult S t e = layerMult S t (e + h)))

/-- **The balance-forcing structure**: for `q < h`, the layer multiset `S ⊎ {q + h}` is
antipodally balanced iff the `q`-fiber is IN, the `(q+h)`-fiber is OUT, and every other
axis `e` is fully antipodal (`e ∈ S ↔ e + h ∈ S`).  This is the "fiber `s/4` in, fiber
`3s/4` out, free antipodal pairs elsewhere" step of the rung law. -/
theorem balanced_iff {h q : ℕ} (hq : q < h) {S : Finset ℕ} :
    Balanced h (q + h) S ↔
      q ∈ S ∧ q + h ∉ S ∧ ∀ e, e < h → e ≠ q → (e ∈ S ↔ e + h ∈ S) := by
  constructor
  · intro hb
    have h1 : (if q ∈ S then 1 else 0) + (if q = q + h then 1 else 0)
        = (if q + h ∈ S then 1 else 0) + (if q + h = q + h then 1 else 0) := hb q hq
    rw [if_neg (by omega : ¬ q = q + h), if_pos rfl] at h1
    have hqS : q ∈ S ∧ q + h ∉ S := by
      by_cases hA : q ∈ S <;> by_cases hB : q + h ∈ S
      · rw [if_pos hA, if_pos hB] at h1; omega
      · exact ⟨hA, hB⟩
      · rw [if_neg hA, if_pos hB] at h1; omega
      · rw [if_neg hA, if_neg hB] at h1; omega
    refine ⟨hqS.1, hqS.2, fun e he hne => ?_⟩
    have h2 : (if e ∈ S then 1 else 0) + (if e = q + h then 1 else 0)
        = (if e + h ∈ S then 1 else 0) + (if e + h = q + h then 1 else 0) := hb e he
    rw [if_neg (by omega : ¬ e = q + h), if_neg (by omega : ¬ e + h = q + h)] at h2
    constructor <;> intro hmem
    · by_contra hno
      rw [if_pos hmem, if_neg hno] at h2; omega
    · by_contra hno
      rw [if_neg hno, if_pos hmem] at h2; omega
  · rintro ⟨hqIn, hqOut, hax⟩ e he
    show (if e ∈ S then 1 else 0) + (if e = q + h then 1 else 0)
        = (if e + h ∈ S then 1 else 0) + (if e + h = q + h then 1 else 0)
    rw [if_neg (by omega : ¬ e = q + h)]
    by_cases heq : e = q
    · subst heq
      rw [if_pos hqIn, if_neg hqOut, if_pos rfl]
    · rw [if_neg (by omega : ¬ e + h = q + h)]
      by_cases hmem : e ∈ S
      · rw [if_pos hmem, if_pos ((hax e he heq).mp hmem)]
      · rw [if_neg hmem, if_neg fun hc => hmem ((hax e he heq).mpr hc)]

/-! ## The bijection with `k`-subsets of the non-`q` axes -/

private lemma mem_axes {h q : ℕ} {T : Finset ℕ} (hT : T ⊆ (range h).erase q) :
    ∀ x ∈ T, x < h ∧ x ≠ q := fun x hx => by
  have hx' := hT hx
  rw [mem_erase, mem_range] at hx'
  exact ⟨hx'.2, hx'.1⟩

/-- A balanced config decomposes as: the slot `q`, plus the free pairs over the lower
representatives `T = (S.filter (· < h)).erase q`. -/
private lemma decomp {h q : ℕ} {S : Finset ℕ}
    (hSsub : S ⊆ range (2 * h)) (hqIn : q ∈ S) (hqOut : q + h ∉ S)
    (hax : ∀ e, e < h → e ≠ q → (e ∈ S ↔ e + h ∈ S)) :
    S = insert q (((S.filter (· < h)).erase q) ∪
      ((S.filter (· < h)).erase q).image (· + h)) := by
  ext x
  simp only [mem_insert, mem_union, mem_image, mem_erase, mem_filter]
  constructor
  · intro hx
    by_cases hxh : x < h
    · by_cases hxq : x = q
      · exact Or.inl hxq
      · exact Or.inr (Or.inl ⟨hxq, hx, hxh⟩)
    · have hx2h : x < 2 * h := mem_range.mp (hSsub hx)
      have hlt : x - h < h := by omega
      have hne : x - h ≠ q := by
        intro hc
        have hx' : q + h = x := by omega
        rw [hx'] at hqOut
        exact hqOut hx
      have hmem : x - h ∈ S := (hax (x - h) hlt hne).mpr (by
        have hx' : x - h + h = x := by omega
        rwa [hx'])
      exact Or.inr (Or.inr ⟨x - h, ⟨hne, hmem, hlt⟩, by omega⟩)
  · rintro (rfl | ⟨hxq, hxS, hxh⟩ | ⟨y, ⟨hyq, hyS, hyh⟩, rfl⟩)
    · exact hqIn
    · exact hxS
    · exact (hax y hyh hyq).mp hyS

private lemma card_decomp {h q : ℕ} (hq : q < h) {T : Finset ℕ}
    (hT : T ⊆ (range h).erase q) :
    (insert q (T ∪ T.image (· + h))).card = 2 * T.card + 1 := by
  have hdisj : Disjoint T (T.image (· + h)) := by
    rw [Finset.disjoint_left]
    intro a haT haI
    obtain ⟨b, hb, hba⟩ := mem_image.mp haI
    have hba' : b + h = a := hba
    have h1 := mem_axes hT a haT
    omega
  have hnotin : q ∉ T ∪ T.image (· + h) := by
    rw [mem_union]
    rintro (hqT | hqI)
    · exact (mem_axes hT q hqT).2 rfl
    · obtain ⟨b, hb, hba⟩ := mem_image.mp hqI
      have hba' : b + h = q := hba
      have h1 := mem_axes hT b hb
      omega
  have hinj : Function.Injective (· + h) := fun a b hab => by
    have hab' : a + h = b + h := hab
    omega
  rw [card_insert_of_notMem hnotin, card_union_of_disjoint hdisj,
    card_image_of_injective T hinj]
  omega

/-- Forward leg: a balanced `(2k+1)`-config yields a `k`-subset of the non-`q` axes. -/
private lemma psi_mem {h q k : ℕ} (hq : q < h) {S : Finset ℕ}
    (hS : S ∈ ((range (2 * h)).powersetCard (2 * k + 1)).filter (Balanced h (q + h))) :
    (S.filter (· < h)).erase q ∈ ((range h).erase q).powersetCard k := by
  rw [mem_filter, mem_powersetCard] at hS
  obtain ⟨⟨hSsub, hScard⟩, hbal⟩ := hS
  rw [balanced_iff hq] at hbal
  obtain ⟨hqIn, hqOut, hax⟩ := hbal
  have hsub : (S.filter (· < h)).erase q ⊆ (range h).erase q := by
    intro x hx
    rw [mem_erase, mem_filter] at hx
    rw [mem_erase, mem_range]
    exact ⟨hx.1, hx.2.2⟩
  rw [mem_powersetCard]
  refine ⟨hsub, ?_⟩
  have hcd := card_decomp hq hsub
  rw [← decomp hSsub hqIn hqOut hax] at hcd
  omega

/-- Backward leg: a `k`-subset of the non-`q` axes yields a balanced `(2k+1)`-config. -/
private lemma phi_mem {h q k : ℕ} (hq : q < h) {T : Finset ℕ}
    (hT : T ∈ ((range h).erase q).powersetCard k) :
    insert q (T ∪ T.image (· + h)) ∈
      ((range (2 * h)).powersetCard (2 * k + 1)).filter (Balanced h (q + h)) := by
  rw [mem_powersetCard] at hT
  obtain ⟨hTsub, hTcard⟩ := hT
  rw [mem_filter, mem_powersetCard]
  refine ⟨⟨?_, by rw [card_decomp hq hTsub, hTcard]⟩, ?_⟩
  · intro x hx
    simp only [mem_insert, mem_union, mem_image] at hx
    rw [mem_range]
    rcases hx with rfl | hx | ⟨b, hb, rfl⟩
    · omega
    · have h1 := mem_axes hTsub x hx; omega
    · have h1 := mem_axes hTsub b hb; omega
  · rw [balanced_iff hq]
    refine ⟨mem_insert_self q _, ?_, ?_⟩
    · intro hc
      simp only [mem_insert, mem_union, mem_image] at hc
      rcases hc with hc | hc | ⟨b, hb, hc⟩
      · omega
      · exact absurd (mem_axes hTsub _ hc).1 (by omega)
      · have h1 := mem_axes hTsub b hb; omega
    · intro e he hne
      simp only [mem_insert, mem_union, mem_image]
      constructor
      · rintro (rfl | hT' | ⟨b, hb, hc⟩)
        · exact absurd rfl hne
        · exact Or.inr (Or.inr ⟨e, hT', rfl⟩)
        · omega
      · rintro (hc | hc | ⟨b, hb, hc⟩)
        · omega
        · exact absurd (mem_axes hTsub _ hc).1 (by omega)
        · have hbe : b = e := by omega
          subst hbe
          exact Or.inr (Or.inl hb)

private lemma phi_psi {h q : ℕ} {T : Finset ℕ} (hTsub : T ⊆ (range h).erase q) :
    ((insert q (T ∪ T.image (· + h))).filter (· < h)).erase q = T := by
  ext x
  simp only [mem_erase, mem_filter, mem_insert, mem_union, mem_image]
  constructor
  · rintro ⟨hxq, (rfl | hxT | ⟨b, hb, rfl⟩), hxh⟩
    · exact absurd rfl hxq
    · exact hxT
    · omega
  · intro hxT
    have h1 := mem_axes hTsub x hxT
    exact ⟨h1.2, Or.inr (Or.inl hxT), h1.1⟩

/-- **The witness-layer count, abstract form**: for `q < h`, the number of `(2k+1)`-element
subsets `S ⊆ {0, …, 2h−1}` whose layer multiset `S ⊎ {q+h}` is antipodally balanced equals
`C(h − 1, k)` — the balanced configs are exactly `{q}` plus `k` free antipodal pairs on the
`h − 1` non-`q` axes.  Witness layer: `h = s/2`, `q = k = s/4`, count `C(s/2 − 1, s/4)`. -/
theorem balanced_card (h q k : ℕ) (hq : q < h) :
    (((range (2 * h)).powersetCard (2 * k + 1)).filter (Balanced h (q + h))).card
      = (h - 1).choose k := by
  have hkey : (((range h).erase q).powersetCard k).card = (h - 1).choose k := by
    rw [card_powersetCard, card_erase_of_mem (mem_range.mpr hq), card_range]
  rw [← hkey]
  refine Finset.card_bij' (fun S _ => (S.filter (· < h)).erase q)
    (fun T _ => insert q (T ∪ T.image (· + h))) ?_ ?_ ?_ ?_
  · exact fun S hS => psi_mem hq hS
  · exact fun T hT => phi_mem hq hT
  · intro S hS
    rw [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSsub, _⟩, hbal⟩ := hS
    rw [balanced_iff hq] at hbal
    exact (decomp hSsub hbal.1 hbal.2.1 hbal.2.2).symm
  · exact fun T hT => phi_psi (mem_powersetCard.mp hT).1

/-- Kernel-checked calibration at `s = 8` (C19's level 1): exactly `3 = C(3, 2)` balanced
witness configs among the `C(8, 5) = 56` candidate 5-subsets (`h = 4`, `q = 2`, `t = 6`). -/
example : (((range 8).powersetCard 5).filter (Balanced 4 6)).card = 3 := by decide

/-- The `s = 16` rung from the theorem (O87's 35; direct kernel enumeration of the
`C(16, 9) = 11440` candidates is too heavy for `decide`): `h = 8`, `q = k = 4`. -/
example : (((range (2 * 8)).powersetCard (2 * 4 + 1)).filter (Balanced 8 (4 + 8))).card
    = 35 := (balanced_card 8 4 4 (by norm_num)).trans (by decide)

/-- The `s = 32` rung from the theorem (the blind n = 64 forecast value): `6435 = C(15, 8)`. -/
example : (((range (2 * 16)).powersetCard (2 * 8 + 1)).filter (Balanced 16 (8 + 16))).card
    = 6435 := (balanced_card 16 8 8 (by norm_num)).trans (by decide)

/-- The `s = 64` rung from the theorem: `C(31, 16) = 300540195`. -/
example : (((range (2 * 32)).powersetCard (2 * 16 + 1)).filter (Balanced 32 (16 + 32))).card
    = Nat.choose 31 16 := (balanced_card 32 16 16 (by norm_num)).trans (by norm_num)

/-! ## Composition with the in-tree field criterion -/

variable {F : Type*} [Field F] [CharZero F]

/-- **Vanishing ⟺ balance for the witness layer** at scale `s = 2^(m+2)`: the layer sum
`Σ_e mult(e)·ζ^e` (with the `−z*` slot at exponent `3·2^m = 3s/4`) vanishes iff the layer
multiset is antipodally balanced.  Direct composition with
`LamLeungTwoPow.vanishing_iff_antipodal_coeffs`.  (`S` is an arbitrary `Finset ℕ`:
exponents `≥ 2^(m+2)` are invisible to both sides, so no range hypothesis is needed.) -/
theorem layer_vanishing_iff {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 2)))
    (S : Finset ℕ) :
    (∑ e ∈ range (2 ^ (m + 2)), (layerMult S (3 * 2 ^ m) e : F) * ζ ^ e = 0) ↔
      Balanced (2 ^ (m + 1)) (3 * 2 ^ m) S := by
  have hcrit := LamLeungTwoPow.vanishing_iff_antipodal_coeffs (m := m + 1) hζ
    (fun e => ((layerMult S (3 * 2 ^ m) e : ℚ)))
  simp only [Rat.cast_natCast] at hcrit
  rw [show (2 : ℕ) ^ (m + 2) = 2 ^ (m + 1 + 1) from rfl, hcrit]
  constructor
  · intro hb e he
    exact_mod_cast hb e he
  · intro hb e he
    exact_mod_cast hb e he

open scoped Classical in
/-- **The witness-layer count** (O130's layer dichotomy, counting half), composed with the
field criterion: at scale `s = 2^(m+2)`, the number of `(s/2 + 1)`-element exponent sets
`S ⊆ {0, …, s−1}` whose layer sum vanishes is exactly `C(s/2 − 1, s/4)`.
Rungs: 3 (s = 8), 35 (s = 16), 6435 (s = 32), 300540195 (s = 64).
(This counts solutions of the balance equation — the combinatorial core of the layer
law; the reduction from RS agree-`(s+2)` list elements to this equation is the
not-yet-formalized analytic half.) -/
theorem witness_layer_card {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 2))) :
    (((range (2 ^ (m + 2))).powersetCard (2 ^ (m + 1) + 1)).filter
        (fun S => ∑ e ∈ range (2 ^ (m + 2)), (layerMult S (3 * 2 ^ m) e : F) * ζ ^ e = 0)).card
      = (2 ^ (m + 1) - 1).choose (2 ^ m) := by
  rw [Finset.filter_congr (fun S _ => layer_vanishing_iff hζ S)]
  have h1 : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
  have h2 : (2 : ℕ) ^ (m + 1) + 1 = 2 * 2 ^ m + 1 := by ring
  have h3 : 3 * 2 ^ m = 2 ^ m + 2 ^ (m + 1) := by ring
  rw [h1, h2, h3]
  exact balanced_card (2 ^ (m + 1)) (2 ^ m) (2 ^ m)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))

omit [CharZero F] in
/-- The layer sum in closed form: `Σ_e mult(e)·ζ^e = (Σ_{e ∈ S} ζ^e) + ζ^t`. -/
lemma layer_sum_eq {m : ℕ} {ζ : F} {S : Finset ℕ} (hS : S ⊆ range (2 ^ (m + 2)))
    {t : ℕ} (ht : t < 2 ^ (m + 2)) :
    ∑ e ∈ range (2 ^ (m + 2)), (layerMult S t e : F) * ζ ^ e
      = (∑ e ∈ S, ζ ^ e) + ζ ^ t := by
  have hsplit : ∀ e, ((layerMult S t e : ℕ) : F) * ζ ^ e
      = (if e ∈ S then ζ ^ e else 0) + (if e = t then ζ ^ e else 0) := by
    intro e
    simp only [layerMult]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl fun e _ => hsplit e, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_subset hS (fun x _ hx => if_neg hx)]
    exact Finset.sum_congr rfl fun e he => if_pos he
  · rw [Finset.sum_ite_eq' (range (2 ^ (m + 2))) t (fun e => ζ ^ e),
      if_pos (mem_range.mpr ht)]

open scoped Classical in
/-- **The witness-layer count, `e₁`-form**: at scale `s = 2^(m+2)` the number of
`(s/2 + 1)`-element exponent sets `S` with `Σ_{e ∈ S} ζ^e = ζ^(s/4) = z*` is exactly
`C(s/2 − 1, s/4)` — the count of `r = 0` solutions of the consistency equation. -/
theorem witness_e1_card {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 2))) :
    (((range (2 ^ (m + 2))).powersetCard (2 ^ (m + 1) + 1)).filter
        (fun S => ∑ e ∈ S, ζ ^ e = ζ ^ 2 ^ m)).card
      = (2 ^ (m + 1) - 1).choose (2 ^ m) := by
  have hhalf : ζ ^ 2 ^ (m + 1) = -1 :=
    LamLeungTwoPow.pow_half_eq_neg_one (m := m + 1) hζ
  have h3 : ζ ^ (3 * 2 ^ m) = -ζ ^ 2 ^ m := by
    rw [show 3 * 2 ^ m = 2 ^ m + 2 ^ (m + 1) from by ring, pow_add, hhalf, mul_neg_one]
  have h3lt : 3 * 2 ^ m < 2 ^ (m + 2) := by
    have h4 : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by ring
    have h5 : 0 < 2 ^ m := Nat.two_pow_pos m
    omega
  have hcong : ∀ S ∈ (range (2 ^ (m + 2))).powersetCard (2 ^ (m + 1) + 1),
      ((∑ e ∈ S, ζ ^ e = ζ ^ 2 ^ m) ↔
        (∑ e ∈ range (2 ^ (m + 2)), (layerMult S (3 * 2 ^ m) e : F) * ζ ^ e = 0)) := by
    intro S hS
    rw [layer_sum_eq (mem_powersetCard.mp hS).1 h3lt, h3, add_neg_eq_zero]
  rw [Finset.filter_congr hcong]
  exact witness_layer_card hζ

/-! ## The even-`r` death lemma (free power basis below `2^m`) -/

/-- **Even-`r` death, power-basis form**: a combination of `2^(m+1)`-th roots of unity with
nonzero (e.g. `±1`) rational coefficients supported on distinct exponents **below `2^m`**
cannot vanish — the lower half of the exponent range is a free basis.  This is why even
fiber patterns with `e₁ = 0` die a priori in every rung of the law.  Direct corollary of
`LamLeungTwoPow.nonvanishing_of_unpaired`. -/
theorem sum_ne_zero_of_support_lower_half {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) {T : Finset ℕ} (hT : T.Nonempty)
    (hTlt : ∀ e ∈ T, e < 2 ^ m) {ε : ℕ → ℚ} (hε : ∀ e ∈ T, ε e ≠ 0) :
    ∑ e ∈ T, (ε e : F) * ζ ^ e ≠ 0 := by
  intro h0
  obtain ⟨e₀, he₀⟩ := hT
  have hsub : T ⊆ range (2 ^ (m + 1)) := fun e he => mem_range.mpr
    ((hTlt e he).trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have hagree : ∑ e ∈ range (2 ^ (m + 1)),
      (((if e ∈ T then ε e else 0 : ℚ)) : F) * ζ ^ e = ∑ e ∈ T, (ε e : F) * ζ ^ e := by
    rw [← Finset.sum_subset hsub (fun x _ hx => by rw [if_neg hx]; simp)]
    exact Finset.sum_congr rfl fun e he => by rw [if_pos he]
  have hout : e₀ + 2 ^ m ∉ T := fun hmem => by
    have h1 := hTlt _ hmem; omega
  have hne : (if e₀ ∈ T then ε e₀ else 0) ≠
      (if e₀ + 2 ^ m ∈ T then ε (e₀ + 2 ^ m) else 0) := by
    rw [if_pos he₀, if_neg hout]
    exact hε e₀ he₀
  exact LamLeungTwoPow.nonvanishing_of_unpaired hζ (fun e => if e ∈ T then ε e else 0)
    (hTlt e₀ he₀) hne (hagree.trans h0)

/-- **Even-`r` death, geometric form**: a nonempty set of `2^(m+1)`-th roots of unity
containing **no antipodal pair** has nonvanishing sum.  (`e₁ = 0` for an even fiber
pattern would need an antipodal pair across distinct fibers.)  Mathematically the
contrapositive of `LamLeungUnconditionalGeneral.antipodal_unconditional`, restated in
exponent coordinates so it composes with the counting theorems in this file. -/
theorem sum_ne_zero_of_no_antipodal_pair {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) {T : Finset ℕ} (hT : T.Nonempty)
    (hTlt : ∀ e ∈ T, e < 2 ^ (m + 1))
    (hfree : ∀ e, ¬(e ∈ T ∧ e + 2 ^ m ∈ T)) :
    ∑ e ∈ T, ζ ^ e ≠ 0 := by
  intro h0
  obtain ⟨e₀, he₀⟩ := hT
  have hsub : T ⊆ range (2 ^ (m + 1)) := fun e he => mem_range.mpr (hTlt e he)
  have hagree : ∑ e ∈ range (2 ^ (m + 1)),
      (((if e ∈ T then 1 else 0 : ℚ)) : F) * ζ ^ e = ∑ e ∈ T, ζ ^ e := by
    rw [← Finset.sum_subset hsub (fun x _ hx => by rw [if_neg hx]; simp)]
    exact Finset.sum_congr rfl fun e he => by rw [if_pos he]; simp
  have hsplit : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
  by_cases hlow : e₀ < 2 ^ m
  · have hout : e₀ + 2 ^ m ∉ T := fun hmem => hfree e₀ ⟨he₀, hmem⟩
    have hne : (if e₀ ∈ T then (1 : ℚ) else 0) ≠
        (if e₀ + 2 ^ m ∈ T then 1 else 0) := by
      rw [if_pos he₀, if_neg hout]; norm_num
    exact LamLeungTwoPow.nonvanishing_of_unpaired hζ
      (fun e => if e ∈ T then (1 : ℚ) else 0) hlow hne (hagree.trans h0)
  · have he₀lt := hTlt e₀ he₀
    have he' : e₀ - 2 ^ m < 2 ^ m := by omega
    have heq : e₀ - 2 ^ m + 2 ^ m = e₀ := by omega
    have hin : e₀ - 2 ^ m + 2 ^ m ∈ T := by rwa [heq]
    have hout : e₀ - 2 ^ m ∉ T := fun hmem => hfree _ ⟨hmem, hin⟩
    have hne : (if e₀ - 2 ^ m ∈ T then (1 : ℚ) else 0) ≠
        (if e₀ - 2 ^ m + 2 ^ m ∈ T then 1 else 0) := by
      rw [if_neg hout, if_pos hin]; norm_num
    exact LamLeungTwoPow.nonvanishing_of_unpaired hζ
      (fun e => if e ∈ T then (1 : ℚ) else 0) he' hne (hagree.trans h0)

/-! ## Rung values (numeric sanity, kernel-checked) -/

example : (2 ^ (1 + 1) - 1).choose (2 ^ 1) = 3 := by decide      -- s = 8   (C19)
example : (2 ^ (2 + 1) - 1).choose (2 ^ 2) = 35 := by decide     -- s = 16  (O87)
example : (2 ^ (3 + 1) - 1).choose (2 ^ 3) = 6435 := by decide   -- s = 32  (the n = 64 hit)

end WitnessLayer

#print axioms WitnessLayer.balanced_iff
#print axioms WitnessLayer.balanced_card
#print axioms WitnessLayer.layer_vanishing_iff
#print axioms WitnessLayer.witness_layer_card
#print axioms WitnessLayer.witness_e1_card
#print axioms WitnessLayer.sum_ne_zero_of_support_lower_half
#print axioms WitnessLayer.sum_ne_zero_of_no_antipodal_pair
