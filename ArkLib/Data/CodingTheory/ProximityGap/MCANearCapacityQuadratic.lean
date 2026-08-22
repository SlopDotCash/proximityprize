/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCANearCapacityGeneralRate

/-!
# A quadratic near-capacity MCA lower bound on the arithmetic domain (Proximity Prize, #232)

`MCANearCapacityGeneralRate.lean` proved, for every Reed–Solomon rate `ρ = k/n`, the **linear**
near-capacity lower bound
`ε_mca(C, 1-(k+1)/n) ≥ (n-k)/|F|`
via the sunflower family of `(k+1)`-windows `{0,…,k-1, k+j}` (only one node varies, so the window
sums are trivially distinct). Its docstring flags the next concrete step: on a *structured* node set
the spread `|𝒮|` — the number of `(k+1)`-windows with **distinct** node-sums — can be pushed from
linear to **quadratic** `Θ(k(n-k))`, because an arithmetic node set has that many distinct
`(k+1)`-subset sums. This file realizes that quadratic spread explicitly and kernel-checks it.

## The construction (two-parameter staircase)

Take the arithmetic domain `domain i = (i : ZMod p)` (an embedding once `n ≤ p`). For parameters
`0 ≤ q < n-2k` and `0 ≤ r ≤ k`, the window

`W(q,r) = {q, q+1, …, q+k-1} ∪ {q+k+r}`

is a `(k+1)`-subset of `{0,…,n-1}` (the bound `q+k+r ≤ n-1` holds on the grid), with integer node-sum

`Σ(q,r) = (∑_{i<k}(q+i)) + (q+k+r) = (k+1)·q + (G + k) + r`,  `G = ∑_{i<k} i`.

The leading block `{q,…,q+k-1}` slides (the `(k+1)·q` term) and the single tail node `q+k+r` adds a
fine offset `r ∈ {0,…,k}`. Since `r ≤ k < k+1`, the map `(q,r) ↦ (k+1)·q + r` is **injective** by
uniqueness of Euclidean division, so all `(n-2k)·(k+1)` window-sums are distinct integers; as they are
all `< n² ≤ p` they stay distinct in `ZMod p`. Feeding this family to
`MCANearCapacityGK.epsMCA_ge_of_window_family` gives

`ε_mca(C, 1-(k+1)/n) ≥ (n-2k)·(k+1) / |F|`,

a **quadratic** `Θ(k(n-k))` lower bound at `δ = capacity − 1/n`, strictly inside the Johnson→capacity
gap — quadratically stronger than the sunflower's linear `n-k`.

## What this does and does not do (candidate analysis for #232)

* It is the docstring-flagged quadratic strengthening of the realized witness spread: a genuine
  `Θ(k(n-k))/|F|` lower bound, kernel-checked, for every rate with `n ≥ 2k+1` (`ρ < 1/2`).
* It remains `poly(n)/|F|`, hence `< ε* = 2⁻¹²⁸` for the prize's large fields, so it does **not** pin
  the prize threshold `δ*` (that needs an *exponential* spread). It sharpens, but does not close, the
  open core delineated in `MCANearCapacityGeneralRate.lean`: a single algebraic monomial line still
  caps `δ` at `capacity − 1/n`; reaching the gap interior needs multiplicity (Guruswami–Sudan).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

open Polynomial BigOperators
open scoped NNReal ENNReal

namespace ProximityGap.MCANearCapacityQuadratic

open ProximityGap Code ProximityGap.MCANearCapacityGK

variable {p : ℕ} [Fact p.Prime] {n k : ℕ} [NeZero n]

/-- A total `ℕ → Fin n` that is the identity on `{0,…,n-1}` (and wraps elsewhere). Used to build
window finsets by `image` with no per-element bound obligation; on the staircase grid every node is
`< n`, so this acts as the genuine inclusion. -/
def node : ℕ → Fin n := fun m => ⟨m % n, Nat.mod_lt m (NeZero.pos n)⟩

@[simp] theorem node_val_of_lt {m : ℕ} (h : m < n) : ((node m : Fin n) : ℕ) = m := by
  simp only [node]; exact Nat.mod_eq_of_lt h

/-- The integer window `{q, q+1, …, q+k-1} ∪ {q+k+r}`. -/
def Wnat (k q r : ℕ) : Finset ℕ := (Finset.range k).image (fun i => q + i) ∪ {q + k + r}

/-- The window as a `Finset (Fin n)`. -/
def Wfin (n k q r : ℕ) [NeZero n] : Finset (Fin n) := (Wnat k q r).image node

/-- The arithmetic evaluation domain `i ↦ (i : ZMod p)`, an embedding once `n ≤ p`. -/
def dom (hnp : n ≤ p) : Fin n ↪ ZMod p where
  toFun i := ((i : ℕ) : ZMod p)
  inj' i j h := by
    have hi : (i : ℕ) < p := lt_of_lt_of_le i.isLt hnp
    have hj : (j : ℕ) < p := lt_of_lt_of_le j.isLt hnp
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact Fin.ext this

/-! ## Integer combinatorics of the staircase windows -/

omit [NeZero n] in
/-- Every node of a grid window is `< n`. -/
theorem Wnat_lt {q r : ℕ} (hq : q < n - 2 * k) (hr : r ≤ k) :
    ∀ m ∈ Wnat k q r, m < n := by
  intro m hm
  have hqkr : q + k + r < n := by omega
  rw [Wnat, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hm
  rcases hm with ⟨i, hi, rfl⟩ | rfl
  · rw [Finset.mem_range] at hi; omega
  · exact hqkr

/-- The integer sum of a window: `(k+1)·q + (G + k) + r` with `G = ∑_{i<k} i`. -/
theorem Wnat_sum (k q r : ℕ) :
    (∑ m ∈ Wnat k q r, m) = (k + 1) * q + ((∑ i ∈ Finset.range k, i) + k) + r := by
  have hdisj : Disjoint ((Finset.range k).image (fun i => q + i)) ({q + k + r} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨i, hi, hcontra⟩
    rw [Finset.mem_range] at hi; omega
  rw [Wnat, Finset.sum_union hdisj, Finset.sum_singleton,
    Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]
  have : (∑ i ∈ Finset.range k, (q + i)) = k * q + ∑ i ∈ Finset.range k, i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  rw [this]; ring

omit [NeZero n] in
/-- A grid window has `k+1` integer nodes. -/
theorem Wnat_card {q r : ℕ} : (Wnat k q r).card = k + 1 := by
  have hdisj : Disjoint ((Finset.range k).image (fun i => q + i)) ({q + k + r} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨i, hi, hcontra⟩
    rw [Finset.mem_range] at hi; omega
  rw [Wnat, Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
    Finset.card_image_of_injective _ (by intro a b h; simp only at h; omega), Finset.card_range]

/-! ## Transport to `Fin n` and `ZMod p` -/

/-- On the grid, the `Fin n` window has `k+1` elements (`node` is injective on nodes `< n`). -/
theorem Wfin_card {q r : ℕ} (hq : q < n - 2 * k) (hr : r ≤ k) :
    (Wfin n k q r).card = k + 1 := by
  rw [Wfin, Finset.card_image_of_injOn, Wnat_card]
  intro a ha b hb hab
  have := Wnat_lt hq hr
  have hva : ((node a : Fin n) : ℕ) = a := node_val_of_lt (this a ha)
  have hvb : ((node b : Fin n) : ℕ) = b := node_val_of_lt (this b hb)
  rw [← hva, ← hvb, hab]

/-- The `ZMod p` node-sum of a grid window equals the integer sum, cast. -/
theorem dom_sum (hnp : n ≤ p) {q r : ℕ} (hq : q < n - 2 * k) (hr : r ≤ k) :
    (∑ i ∈ Wfin n k q r, dom (p := p) hnp i) = (((∑ m ∈ Wnat k q r, m) : ℕ) : ZMod p) := by
  have hlt := Wnat_lt hq hr
  rw [Wfin, Finset.sum_image (by
    intro a ha b hb hab
    have hva : ((node a : Fin n) : ℕ) = a := node_val_of_lt (hlt a ha)
    have hvb : ((node b : Fin n) : ℕ) = b := node_val_of_lt (hlt b hb)
    rw [← hva, ← hvb, hab])]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  show (((node m : Fin n) : ℕ) : ZMod p) = ((m : ℕ) : ZMod p)
  rw [node_val_of_lt (hlt m hm)]

/-- Uniqueness of Euclidean division: the "digits" `(q, r)` with `r < K` are determined by
`K·q + r`. This is what makes the staircase sums injective. -/
theorem euclid_uniq {K q r q' r' : ℕ} (hK : 0 < K) (hr : r < K) (hr' : r' < K)
    (h : K * q + r = K * q' + r') : q = q' ∧ r = r' := by
  have hrr : r = r' := by
    have hmod : (K * q + r) % K = (K * q' + r') % K := by rw [h]
    rwa [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at hmod
  subst hrr
  exact ⟨Nat.eq_of_mul_eq_mul_left hK (by omega), rfl⟩

omit [Fact p.Prime] in
/-- Every grid window sum is `< p`, so distinct integer sums stay distinct in `ZMod p`. -/
theorem Wnat_sum_lt (hp : n * n ≤ p) {q r : ℕ}
    (hq : q < n - 2 * k) (hr : r ≤ k) : (∑ m ∈ Wnat k q r, m) < p := by
  have hcard := Wnat_card (k := k) (q := q) (r := r)
  have hle : (∑ m ∈ Wnat k q r, m) ≤ (k + 1) * (n - 1) := by
    calc (∑ m ∈ Wnat k q r, m) ≤ (Wnat k q r).card • (n - 1) :=
          Finset.sum_le_card_nsmul _ _ _ (fun m hm => by have := Wnat_lt hq hr m hm; omega)
      _ = (k + 1) * (n - 1) := by rw [hcard, smul_eq_mul]
  have hk1n : k + 1 ≤ n := by omega
  have hnpos : 0 < n := NeZero.pos n
  have hstep : (k + 1) * (n - 1) < n * n :=
    calc (k + 1) * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ hk1n
      _ < n * n := mul_lt_mul_of_pos_left (by omega) hnpos
  omega

/-! ## The quadratic lower bound -/

/-- The staircase window family `{ W(q,r) : 0 ≤ q < n-2k, 0 ≤ r ≤ k }` as a `Finset` of windows. -/
noncomputable def family (n k : ℕ) [NeZero n] : Finset (Finset (Fin n)) :=
  ((Finset.range (n - 2 * k)) ×ˢ (Finset.range (k + 1))).image (fun qr => Wfin n k qr.1 qr.2)

/-- **The staircase sums are injective on the grid** — the heart of the quadratic count. -/
theorem sumval_injOn (hp : n * n ≤ p) :
    Set.InjOn (fun qr : ℕ × ℕ => (((∑ m ∈ Wnat k qr.1 qr.2, m) : ℕ) : ZMod p))
      (((Finset.range (n - 2 * k)) ×ˢ (Finset.range (k + 1)) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro qr hqr qr' hqr' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hqr hqr'
  obtain ⟨hq, hr⟩ := hqr
  obtain ⟨hq', hr'⟩ := hqr'
  have hb1 := Wnat_sum_lt hp (q := qr.1) (r := qr.2) hq (by omega)
  have hb2 := Wnat_sum_lt hp (q := qr'.1) (r := qr'.2) hq' (by omega)
  have heq : (∑ m ∈ Wnat k qr.1 qr.2, m) = (∑ m ∈ Wnat k qr'.1 qr'.2, m) := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
    rwa [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at this
  rw [Wnat_sum, Wnat_sum] at heq
  have hKeq : (k + 1) * qr.1 + qr.2 = (k + 1) * qr'.1 + qr'.2 := by omega
  obtain ⟨hh1, hh2⟩ := euclid_uniq (Nat.succ_pos k) (by omega) (by omega) hKeq
  exact Prod.ext hh1 hh2

/-- **Quadratic near-capacity MCA lower bound on the arithmetic domain.**
For the Reed–Solomon code of dimension `k` on the arithmetic domain `i ↦ (i : ZMod p)` over a prime
field with `n² ≤ p`, with `n ≥ 2k+1` (`ρ < 1/2`) and `k ≥ 1`, at radius `δ = 1-(k+1)/n` (capacity
minus `1/n`):
`ε_mca(C, δ) ≥ (n-2k)·(k+1) / |F|`.
The `(n-2k)·(k+1)` staircase windows `{q,…,q+k-1}∪{q+k+r}` have distinct node-sums
`(k+1)·q + (G+k) + r` (injective by Euclidean division), realizing a **quadratic** `Θ(k(n-k))` witness
spread — quadratically stronger than the sunflower family's linear `n-k`
(`MCANearCapacityGK.epsMCA_ge_of_prefix_sunflower`). -/
theorem epsMCA_quadratic_ge (hp : n * n ≤ p) (hk : 1 ≤ k) (hn : 2 * k + 1 ≤ n) :
    (((n - 2 * k) * (k + 1) : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (A := ZMod p)
          (ReedSolomon.code
              (domain := dom (p := p) (n := n) (by have := NeZero.pos n; nlinarith [hp])) k : Set (Fin n → ZMod p))
          (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)) := by
  have hnp : n ≤ p := by have := NeZero.pos n; nlinarith [hp]
  set grid : Finset (ℕ × ℕ) :=
    (Finset.range (n - 2 * k)) ×ˢ (Finset.range (k + 1)) with hgrid
  set win : ℕ × ℕ → Finset (Fin n) := fun qr => Wfin n k qr.1 qr.2 with hwin
  -- the sum-value of a window equals the cast integer sum, on the grid
  have hval : ∀ qr ∈ grid, (∑ i ∈ win qr, dom (p := p) hnp i)
      = (((∑ m ∈ Wnat k qr.1 qr.2, m) : ℕ) : ZMod p) := by
    intro qr hqr
    rw [hgrid, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqr
    exact dom_sum hnp hqr.1 (by omega)
  -- windows are injective on the grid (their sums already are)
  have hwinInj : Set.InjOn win (grid : Set (ℕ × ℕ)) := by
    intro qr hqr qr' hqr' hww
    refine sumval_injOn (p := p) hp hqr hqr' ?_
    have e1 := hval qr (by simpa using hqr)
    have e2 := hval qr' (by simpa using hqr')
    simp only at e1 e2 ⊢
    rw [← e1, ← e2, hww]
  -- |family| = (n-2k)·(k+1)
  have hfamcard : (family n k).card = (n - 2 * k) * (k + 1) := by
    rw [family, ← hgrid, ← hwin, Finset.card_image_of_injOn hwinInj, hgrid,
      Finset.card_product, Finset.card_range, Finset.card_range]
  -- each window has card k+1
  have hcard : ∀ S ∈ family n k, S.card = k + 1 := by
    intro S hS
    rw [family, Finset.mem_image] at hS
    obtain ⟨qr, hqr, rfl⟩ := hS
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqr
    exact Wfin_card hqr.1 (by omega)
  -- the bad-scalar map is injective on the family
  have hinj : Set.InjOn (fun S => -(∑ i ∈ S, dom (p := p) hnp i)) (family n k : Set (Finset (Fin n))) := by
    intro S hS S' hS' hSS'
    rw [Finset.mem_coe, family, Finset.mem_image] at hS hS'
    obtain ⟨qr, hqr, rfl⟩ := hS
    obtain ⟨qr', hqr', rfl⟩ := hS'
    have e1 := hval qr hqr
    have e2 := hval qr' hqr'
    simp only at hSS' e1 e2
    have hcast : (((∑ m ∈ Wnat k qr.1 qr.2, m) : ℕ) : ZMod p)
        = (((∑ m ∈ Wnat k qr'.1 qr'.2, m) : ℕ) : ZMod p) := by
      rw [← e1, ← e2]; exact neg_injective hSS'
    have hpair := sumval_injOn (p := p) hp (by simpa using hqr) (by simpa using hqr')
      (by simpa using hcast)
    rw [hpair]
  have hbound := epsMCA_ge_of_window_family (F := ZMod p) (dom (p := p) hnp) k hk
    (family n k) hcard hinj
  rwa [hfamcard] at hbound

#print axioms epsMCA_quadratic_ge

end ProximityGap.MCANearCapacityQuadratic
