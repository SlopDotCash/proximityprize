/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWindowedLaw

/-!
# Issue #232 — THE TWO-GENERATOR PACKING CAPACITY LAW: the first sufficiency
# rung of the 0/1 packing surface (O116's named next (a))

O116 proved the two-sided span law necessary and refuted its sufficiency via
the CRT obstruction (coprime-step cosets always intersect).  This file proves
the EXACT criterion for the two-generator case — when can `a` rotated
`μ_d`-cosets and `b` rotated `μ_{d'}`-cosets be chosen pairwise disjoint in
`[0, n)`?  With `s = n/d`, `s' = n/d'`, `G = gcd(s, s')`, `m = s/G`,
`m' = s'/G`:

* `cosetOf_disjoint_same` / `cosetOf_disjoint_cross` / `cosetOf_not_disjoint_cross`
  — the intersection trichotomy: same-type cosets are disjoint iff their bases
  differ; cross-type cosets are disjoint IFF their bases differ mod `G`
  (the CRT direction via `Nat.chineseRemainder'`).
* `two_generator_capacity` — **the law**:
  `Packable n d d' a b  ↔  ⌈a/m⌉ + ⌈b/m'⌉ ≤ G`
  (ℕ-form `(a + m − 1)/m + (b + m' − 1)/m' ≤ G`).  Each residue class mod `G`
  holds exactly `m` bases of type `d` (`m'` of type `d'`), classes are
  exclusive across types, and within a class same-type cosets never collide —
  so packing is exactly a class-allocation problem.
* `two_gen_mass_realizable` — the window-fiber consumer: when `d, d' ∣ n`
  exceed `t` and the capacity condition holds, the mass `a·d + b·d'` is
  realized by a window-`t`-vanishing 0/1 set (an `IsWindowCosetUnion`).

The O116 CRT refutation instance is the degenerate reading: at `n = 36`,
`d = 9`, `d' = 4`: `s = 4`, `s' = 9`, `G = 1` — `⌈1/4⌉ + ⌈1/9⌉ = 2 > 1`, so
one `μ_9`- and one `μ_4`-coset NEVER pack (mass 13 dead), while `d = 6,
d' = 9` with `a = 3, b = 2` packs (`G = 2`: `⌈3/3⌉ + ⌈2/2⌉ = 2 ≤ 2`) — a full
mixed tiling of `[0, 36)`.

Probe-verified before formalization (`scripts/probes/probe_two_gen_capacity.py`,
exhaustive over n ∈ {12, 18, 24, 30, 36}, ALL ordered divisor pairs, ALL
`(a, b)` up to the base counts, raw backtracking ground truth).
-/

namespace TwoGenPackingCapacity

open Finset DeBruijnWindowedLaw

/-! ## The intersection trichotomy -/

/-- Membership in a canonical coset, characterized by bound and residue. -/
lemma mem_cosetOf_iff {n d r e : ℕ} (hdn : d ∣ n) (hr : r < n / d) :
    e ∈ cosetOf n d r ↔ e < n ∧ e % (n / d) = r := by
  have hsd : (n / d) * d = n := Nat.div_mul_cancel hdn
  have hs : 0 < n / d := by omega
  constructor
  · intro he
    refine ⟨?_, mod_of_mem_cosetOf hr he⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_range] at hj
    calc r + j * (n / d) < n / d + j * (n / d) := Nat.add_lt_add_right hr _
      _ = (j + 1) * (n / d) := by ring
      _ ≤ d * (n / d) := Nat.mul_le_mul_right _ (by omega)
      _ = n := by rw [mul_comm]; exact hsd
  · rintro ⟨hlt, hmod⟩
    refine Finset.mem_image.mpr ⟨e / (n / d), Finset.mem_range.mpr ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hs]
      calc e < n := hlt
        _ = d * (n / d) := by rw [mul_comm]; exact hsd.symm
    · rw [mul_comm, ← hmod]
      exact Nat.mod_add_div e (n / d)

/-- Same-type canonical cosets with distinct bases are disjoint. -/
lemma cosetOf_disjoint_same {n d r r' : ℕ} (hr : r < n / d) (hr' : r' < n / d)
    (hne : r ≠ r') : Disjoint (cosetOf n d r) (cosetOf n d r') :=
  Finset.disjoint_left.mpr fun _ he he' =>
    hne ((mod_of_mem_cosetOf hr he).symm.trans (mod_of_mem_cosetOf hr' he'))

/-- Cross-type canonical cosets whose bases differ modulo `G = gcd(s, s')` are
disjoint. -/
lemma cosetOf_disjoint_cross {n d d' r r' : ℕ} (hr : r < n / d) (hr' : r' < n / d')
    (hne : r % Nat.gcd (n / d) (n / d') ≠ r' % Nat.gcd (n / d) (n / d')) :
    Disjoint (cosetOf n d r) (cosetOf n d' r') := by
  refine Finset.disjoint_left.mpr fun e he he' => hne ?_
  rw [← mod_of_mem_cosetOf hr he, ← mod_of_mem_cosetOf hr' he',
    Nat.mod_mod_of_dvd e (Nat.gcd_dvd_left _ _),
    Nat.mod_mod_of_dvd e (Nat.gcd_dvd_right _ _)]

/-- **The CRT direction**: cross-type canonical cosets whose bases AGREE
modulo `G = gcd(s, s')` always intersect — `Nat.chineseRemainder'` produces a
common element below `lcm(s, s') ∣ n`. -/
lemma cosetOf_not_disjoint_cross {n d d' r r' : ℕ} (hn : 0 < n)
    (hdn : d ∣ n) (hd'n : d' ∣ n)
    (hr : r < n / d) (hr' : r' < n / d')
    (heq : r % Nat.gcd (n / d) (n / d') = r' % Nat.gcd (n / d) (n / d')) :
    ¬ Disjoint (cosetOf n d r) (cosetOf n d' r') := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' (n := n / d) (m := n / d') heq
  have hlcm : Nat.lcm (n / d) (n / d') ∣ n :=
    Nat.lcm_dvd (Nat.div_dvd_of_dvd hdn) (Nat.div_dvd_of_dvd hd'n)
  have hxlt : k % Nat.lcm (n / d) (n / d') < n :=
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_dvd_of_pos hlcm hn))
      (Nat.le_of_dvd hn hlcm)
  have hx1 : k % Nat.lcm (n / d) (n / d') % (n / d) = r := by
    rw [Nat.mod_mod_of_dvd k (Nat.dvd_lcm_left _ _)]
    rw [Nat.ModEq] at hk1
    rw [hk1, Nat.mod_eq_of_lt hr]
  have hx2 : k % Nat.lcm (n / d) (n / d') % (n / d') = r' := by
    rw [Nat.mod_mod_of_dvd k (Nat.dvd_lcm_right _ _)]
    rw [Nat.ModEq] at hk2
    rw [hk2, Nat.mod_eq_of_lt hr']
  intro hdisj
  exact Finset.disjoint_left.mp hdisj
    ((mem_cosetOf_iff hdn hr).mpr ⟨hxlt, hx1⟩)
    ((mem_cosetOf_iff hd'n hr').mpr ⟨hxlt, hx2⟩)

/-! ## Packability -/

/-- `a` canonical `μ_d`-cosets and `b` canonical `μ_{d'}`-cosets fit pairwise
disjointly in `[0, n)`: base sets of the right sizes exist whose total coset
union has FULL cardinality `a·d + b·d'` (full cardinality forces all the
disjointness). -/
def Packable (n d d' a b : ℕ) : Prop :=
  ∃ A B : Finset ℕ, A ⊆ Finset.range (n / d) ∧ B ⊆ Finset.range (n / d') ∧
    A.card = a ∧ B.card = b ∧
    (A.biUnion (cosetOf n d) ∪ B.biUnion (cosetOf n d')).card = a * d + b * d'

/-- Ceiling division transfer: `⌈a/m⌉ ≤ c ↔ a ≤ c·m` (`m > 0`). -/
private lemma ceil_le_iff {a m c : ℕ} (hm : 0 < m) :
    (a + m - 1) / m ≤ c ↔ a ≤ c * m := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hm]
  have hexp : Nat.succ c * m = c * m + m := Nat.succ_mul c m
  rw [hexp]
  omega

/-- The cardinality of a canonical coset. -/
private lemma cosetOf_card {n d r : ℕ} (hs : 0 < n / d) (hr : r < n / d) :
    (cosetOf n d r).card = d :=
  DeBruijnTwoPrimeAssembly.IsPacket.card_eq hs ⟨r, hr, rfl⟩

/-- The biUnion of cosets over a base set inside `range (n/d)` has cardinality
at most `|A| · d`, with equality unnecessary here — the budget bound. -/
private lemma biUnion_card_le {n d a : ℕ} (hs : 0 < n / d)
    {A : Finset ℕ} (hAs : A ⊆ Finset.range (n / d)) (hcA : A.card = a) :
    (A.biUnion (cosetOf n d)).card ≤ a * d := by
  calc (A.biUnion (cosetOf n d)).card
      ≤ ∑ r ∈ A, (cosetOf n d r).card := Finset.card_biUnion_le
    _ = ∑ r ∈ A, d := Finset.sum_congr rfl fun r hr =>
        cosetOf_card hs (Finset.mem_range.mp (hAs hr))
    _ = a * d := by rw [Finset.sum_const, hcA, smul_eq_mul]

/-- **Full cardinality forces cross-disjointness**: in a packing achieving the
total budget `a·d + b·d'`, every `A`-coset is disjoint from every `B`-coset. -/
private lemma cross_disjoint_of_card {n d d' a b : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hd' : 0 < d') (hdn : d ∣ n) (hd'n : d' ∣ n)
    {A B : Finset ℕ} (hAs : A ⊆ Finset.range (n / d))
    (hBs : B ⊆ Finset.range (n / d'))
    (hcA : A.card = a) (hcB : B.card = b)
    (hcard : (A.biUnion (cosetOf n d) ∪ B.biUnion (cosetOf n d')).card
      = a * d + b * d') :
    ∀ α ∈ A, ∀ β ∈ B, Disjoint (cosetOf n d α) (cosetOf n d' β) := by
  intro α hα β hβ
  have hs : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
  have hs' : 0 < n / d' := Nat.div_pos (Nat.le_of_dvd hn hd'n) hd'
  have hXle := biUnion_card_le hs hAs hcA
  have hYle := biUnion_card_le hs' hBs hcB
  have hsum := Finset.card_union_add_card_inter
    (A.biUnion (cosetOf n d)) (B.biUnion (cosetOf n d'))
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  have hint : 0 < ((A.biUnion (cosetOf n d)) ∩ (B.biUnion (cosetOf n d'))).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨α, hα, he⟩, Finset.mem_biUnion.mpr ⟨β, hβ, he'⟩⟩⟩
  obtain ⟨P, hP⟩ : ∃ P, a * d = P := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, b * d' = Q := ⟨_, rfl⟩
  rw [hP] at hXle hcard
  rw [hQ] at hYle hcard
  omega

/-! ## Necessity: packing forces the class-capacity bound -/

/-- Bases below `s` in a fixed residue class mod `G` (`G ∣ s`) number at most
`s / G`. -/
private lemma fiber_card_le {s G γ : ℕ} (hG : 0 < G) (hGs : G ∣ s)
    {A : Finset ℕ} (hA : A ⊆ Finset.range s) :
    ((A.filter (· % G = γ))).card ≤ s / G := by
  classical
  calc ((A.filter (· % G = γ))).card ≤ (Finset.range (s / G)).card := by
        refine Finset.card_le_card_of_injOn (fun x => x / G) ?_ ?_
        · intro x hx
          obtain ⟨hxA, _⟩ := Finset.mem_filter.mp hx
          have hxs : x < s := Finset.mem_range.mp (hA hxA)
          refine Finset.mem_range.mpr ?_
          rw [Nat.div_lt_iff_lt_mul hG]
          calc x < s := hxs
            _ = s / G * G := (Nat.div_mul_cancel hGs).symm
        · intro x hx y hy hxy
          obtain ⟨_, hxγ⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
          obtain ⟨_, hyγ⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
          have hxy' : x / G = y / G := hxy
          have hx' := Nat.div_add_mod x G
          have hy' := Nat.div_add_mod y G
          have hmul : G * (x / G) = G * (y / G) := by rw [hxy']
          omega
    _ = s / G := Finset.card_range _

/-- **Necessity over abstract block data**: a full-cardinality packing forces
`⌈a/m⌉ + ⌈b/m'⌉ ≤ G`, stated with the derived quantities as free variables to
keep every arithmetic step linear. -/
private lemma capacity_of_packable_aux {n d d' a b s s' G : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hd' : 0 < d') (hdn : d ∣ n) (hd'n : d' ∣ n)
    (hsdef : s = n / d) (hs'def : s' = n / d') (hGdef : G = Nat.gcd s s')
    (h : Packable n d d' a b) :
    (a + s / G - 1) / (s / G) + (b + s' / G - 1) / (s' / G) ≤ G := by
  classical
  obtain ⟨A, B, hAs, hBs, hcA, hcB, hcard⟩ := h
  rw [← hsdef] at hAs
  rw [← hs'def] at hBs
  have hs : 0 < s := hsdef ▸ Nat.div_pos (Nat.le_of_dvd hn hdn) hd
  have hs' : 0 < s' := hs'def ▸ Nat.div_pos (Nat.le_of_dvd hn hd'n) hd'
  have hG : 0 < G := hGdef ▸ Nat.gcd_pos_of_pos_left _ hs
  have hGs : G ∣ s := hGdef ▸ Nat.gcd_dvd_left _ _
  have hGs' : G ∣ s' := hGdef ▸ Nat.gcd_dvd_right _ _
  have hm : 0 < s / G := Nat.div_pos (Nat.le_of_dvd hs hGs) hG
  have hm' : 0 < s' / G := Nat.div_pos (Nat.le_of_dvd hs' hGs') hG
  -- cross pairs occupy distinct classes mod G
  have hcrossdisj := cross_disjoint_of_card hn hd hd' hdn hd'n
    (hsdef ▸ hAs) (hs'def ▸ hBs) hcA hcB hcard
  have hcross : ∀ α ∈ A, ∀ β ∈ B, α % G ≠ β % G := by
    intro α hα β hβ heq
    refine cosetOf_not_disjoint_cross hn hdn hd'n
      (hsdef ▸ Finset.mem_range.mp (hAs hα))
      (hs'def ▸ Finset.mem_range.mp (hBs hβ)) ?_ (hcrossdisj α hα β hβ)
    rw [← hsdef, ← hs'def, ← hGdef]
    exact heq
  -- class counting
  have hCdisj : Disjoint (A.image (· % G)) (B.image (· % G)) := by
    refine Finset.disjoint_left.mpr fun γ hγA hγB => ?_
    obtain ⟨α, hα, hαγ⟩ := Finset.mem_image.mp hγA
    obtain ⟨β, hβ, hβγ⟩ := Finset.mem_image.mp hγB
    exact hcross α hα β hβ (hαγ.trans hβγ.symm)
  have hCsub : (A.image (· % G)) ∪ (B.image (· % G)) ⊆ Finset.range G := by
    intro γ hγ
    rcases Finset.mem_union.mp hγ with h | h <;>
      obtain ⟨α, _, hαγ⟩ := Finset.mem_image.mp h <;>
      exact Finset.mem_range.mpr (hαγ ▸ Nat.mod_lt _ hG)
  have hCsum : (A.image (· % G)).card + (B.image (· % G)).card ≤ G := by
    calc (A.image (· % G)).card + (B.image (· % G)).card
        = ((A.image (· % G)) ∪ (B.image (· % G))).card :=
          (Finset.card_union_of_disjoint hCdisj).symm
      _ ≤ (Finset.range G).card := Finset.card_le_card hCsub
      _ = G := Finset.card_range G
  -- per-class fibers bound the base counts
  have hAfib : a ≤ (A.image (· % G)).card * (s / G) := by
    calc a = A.card := hcA.symm
      _ = ∑ γ ∈ A.image (· % G), (A.filter (· % G = γ)).card :=
          Finset.card_eq_sum_card_fiberwise fun x hx =>
            Finset.mem_image_of_mem _ hx
      _ ≤ ∑ _γ ∈ A.image (· % G), s / G :=
          Finset.sum_le_sum fun γ _ => fiber_card_le hG hGs hAs
      _ = (A.image (· % G)).card * (s / G) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hBfib : b ≤ (B.image (· % G)).card * (s' / G) := by
    calc b = B.card := hcB.symm
      _ = ∑ γ ∈ B.image (· % G), (B.filter (· % G = γ)).card :=
          Finset.card_eq_sum_card_fiberwise fun x hx =>
            Finset.mem_image_of_mem _ hx
      _ ≤ ∑ _γ ∈ B.image (· % G), s' / G :=
          Finset.sum_le_sum fun γ _ => fiber_card_le hG hGs' hBs
      _ = (B.image (· % G)).card * (s' / G) := by
          rw [Finset.sum_const, smul_eq_mul]
  calc (a + s / G - 1) / (s / G) + (b + s' / G - 1) / (s' / G)
      ≤ (A.image (· % G)).card + (B.image (· % G)).card :=
        Nat.add_le_add ((ceil_le_iff hm).mpr hAfib) ((ceil_le_iff hm').mpr hBfib)
    _ ≤ G := hCsum

/-- **Necessity**, in the concrete form. -/
theorem capacity_of_packable {n d d' a b : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hd' : 0 < d') (hdn : d ∣ n) (hd'n : d' ∣ n)
    (h : Packable n d d' a b) :
    (a + (n / d) / Nat.gcd (n / d) (n / d') - 1) / ((n / d) / Nat.gcd (n / d) (n / d'))
      + (b + (n / d') / Nat.gcd (n / d) (n / d') - 1) / ((n / d') / Nat.gcd (n / d) (n / d'))
      ≤ Nat.gcd (n / d) (n / d') :=
  capacity_of_packable_aux hn hd hd' hdn hd'n rfl rfl rfl h

/-! ## Sufficiency: the explicit class-block construction -/

/-- **Sufficiency over abstract block data**: given `a ≤ k·m`, `b ≤ k'·m'`,
`k + k' ≤ G`, `m·G = s`, `m'·G = s'`, the explicit enumeration — base `j` of
type `d` is `(j % k) + G·(j / k)`, of type `d'` is `(k + j % k') + G·(j / k')`
— is a full-cardinality packing.  The `d`-bases live in classes `0..k−1`
mod `G`, the `d'`-bases in classes `k..k+k'−1`. -/
private lemma packable_of_blocks {n d d' a b s s' G m m' k k' : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hd' : 0 < d') (hdn : d ∣ n) (hd'n : d' ∣ n)
    (hsdef : s = n / d) (hs'def : s' = n / d') (hGdef : G = Nat.gcd s s')
    (hG : 0 < G) (hmG : m * G = s) (hm'G : m' * G = s')
    (ham : a ≤ k * m) (hbm : b ≤ k' * m') (hkk' : k + k' ≤ G) :
    Packable n d d' a b := by
  classical
  have hk0 : ∀ j, j < a → 0 < k := by
    intro j hj
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, zero_mul] at ham
      omega
    · exact h
  have hk'0 : ∀ j, j < b → 0 < k' := by
    intro j hj
    rcases Nat.eq_zero_or_pos k' with h0 | h
    · rw [h0, zero_mul] at hbm
      omega
    · exact h
  -- the type-d enumeration
  have hfclass : ∀ j, j < a → (j % k + G * (j / k)) % G = j % k := by
    intro j hj
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (hk0 j hj)) (by omega))
  have hfrange : ∀ j, j < a → j % k + G * (j / k) < s := by
    intro j hj
    have hk := hk0 j hj
    have hjk : j / k + 1 ≤ m := by
      have : j / k < m := by
        rw [Nat.div_lt_iff_lt_mul hk, mul_comm]
        exact lt_of_lt_of_le hj ham
      omega
    calc j % k + G * (j / k) < G + G * (j / k) :=
          Nat.add_lt_add_right (lt_of_lt_of_le (Nat.mod_lt _ hk) (by omega)) _
      _ = G * (j / k + 1) := by ring
      _ ≤ G * m := Nat.mul_le_mul_left _ hjk
      _ = m * G := mul_comm _ _
      _ = s := hmG
  have hfinj : ∀ j₁, j₁ < a → ∀ j₂, j₂ < a →
      j₁ % k + G * (j₁ / k) = j₂ % k + G * (j₂ / k) → j₁ = j₂ := by
    intro j₁ h₁ j₂ h₂ heq
    have hclass : j₁ % k = j₂ % k := by
      rw [← hfclass j₁ h₁, ← hfclass j₂ h₂, heq]
    rw [hclass] at heq
    have hdiv : j₁ / k = j₂ / k :=
      Nat.eq_of_mul_eq_mul_left hG (Nat.add_left_cancel heq)
    calc j₁ = k * (j₁ / k) + j₁ % k := (Nat.div_add_mod j₁ k).symm
      _ = k * (j₂ / k) + j₂ % k := by rw [hdiv, hclass]
      _ = j₂ := Nat.div_add_mod j₂ k
  -- the type-d' enumeration
  have hgclass : ∀ j, j < b → ((k + j % k') + G * (j / k')) % G = k + j % k' := by
    intro j hj
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt
      (lt_of_lt_of_le (Nat.add_lt_add_left (Nat.mod_lt _ (hk'0 j hj)) k) hkk')
  have hgrange : ∀ j, j < b → (k + j % k') + G * (j / k') < s' := by
    intro j hj
    have hk' := hk'0 j hj
    have hjk : j / k' + 1 ≤ m' := by
      have : j / k' < m' := by
        rw [Nat.div_lt_iff_lt_mul hk', mul_comm]
        exact lt_of_lt_of_le hj hbm
      omega
    calc (k + j % k') + G * (j / k') < G + G * (j / k') :=
          Nat.add_lt_add_right
            (lt_of_lt_of_le (Nat.add_lt_add_left (Nat.mod_lt _ hk') k) hkk') _
      _ = G * (j / k' + 1) := by ring
      _ ≤ G * m' := Nat.mul_le_mul_left _ hjk
      _ = m' * G := mul_comm _ _
      _ = s' := hm'G
  have hginj : ∀ j₁, j₁ < b → ∀ j₂, j₂ < b →
      (k + j₁ % k') + G * (j₁ / k') = (k + j₂ % k') + G * (j₂ / k') → j₁ = j₂ := by
    intro j₁ h₁ j₂ h₂ heq
    have hclass : j₁ % k' = j₂ % k' := by
      have h := hgclass j₁ h₁
      have h' := hgclass j₂ h₂
      have : k + j₁ % k' = k + j₂ % k' := by rw [← h, ← h', heq]
      omega
    rw [hclass] at heq
    have hdiv : j₁ / k' = j₂ / k' :=
      Nat.eq_of_mul_eq_mul_left hG (Nat.add_left_cancel heq)
    calc j₁ = k' * (j₁ / k') + j₁ % k' := (Nat.div_add_mod j₁ k').symm
      _ = k' * (j₂ / k') + j₂ % k' := by rw [hdiv, hclass]
      _ = j₂ := Nat.div_add_mod j₂ k'
  -- assemble
  refine ⟨(Finset.range a).image (fun j => j % k + G * (j / k)),
    (Finset.range b).image (fun j => (k + j % k') + G * (j / k')), ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hα
    exact Finset.mem_range.mpr (hsdef ▸ hfrange j (Finset.mem_range.mp hj))
  · intro β hβ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hβ
    exact Finset.mem_range.mpr (hs'def ▸ hgrange j (Finset.mem_range.mp hj))
  · rw [Finset.card_image_of_injOn fun j₁ h₁ j₂ h₂ heq =>
      hfinj j₁ (Finset.mem_range.mp h₁) j₂ (Finset.mem_range.mp h₂) heq]
    exact Finset.card_range a
  · rw [Finset.card_image_of_injOn fun j₁ h₁ j₂ h₂ heq =>
      hginj j₁ (Finset.mem_range.mp h₁) j₂ (Finset.mem_range.mp h₂) heq]
    exact Finset.card_range b
  · -- the union has full cardinality
    have hsd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    have hsd' : 0 < n / d' := Nat.div_pos (Nat.le_of_dvd hn hd'n) hd'
    have hXcard : (((Finset.range a).image (fun j => j % k + G * (j / k))).biUnion
        (cosetOf n d)).card = a * d := by
      rw [Finset.card_biUnion]
      · calc ∑ r ∈ (Finset.range a).image (fun j => j % k + G * (j / k)),
              (cosetOf n d r).card
            = ∑ r ∈ (Finset.range a).image (fun j => j % k + G * (j / k)), d := by
              refine Finset.sum_congr rfl fun r hr => ?_
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
              exact cosetOf_card hsd
                (hsdef ▸ hfrange j (Finset.mem_range.mp hj))
          _ = a * d := by
              rw [Finset.sum_const, smul_eq_mul,
                Finset.card_image_of_injOn fun j₁ h₁ j₂ h₂ heq =>
                  hfinj j₁ (Finset.mem_range.mp h₁) j₂ (Finset.mem_range.mp h₂) heq,
                Finset.card_range]
      · intro r₁ h₁ r₂ h₂ hne
        obtain ⟨j₁, hj₁, rfl⟩ := Finset.mem_image.mp h₁
        obtain ⟨j₂, hj₂, rfl⟩ := Finset.mem_image.mp h₂
        exact cosetOf_disjoint_same
          (hsdef ▸ hfrange j₁ (Finset.mem_range.mp hj₁))
          (hsdef ▸ hfrange j₂ (Finset.mem_range.mp hj₂)) hne
    have hYcard : (((Finset.range b).image (fun j => (k + j % k') + G * (j / k'))).biUnion
        (cosetOf n d')).card = b * d' := by
      rw [Finset.card_biUnion]
      · calc ∑ r ∈ (Finset.range b).image (fun j => (k + j % k') + G * (j / k')),
              (cosetOf n d' r).card
            = ∑ r ∈ (Finset.range b).image (fun j => (k + j % k') + G * (j / k')), d' := by
              refine Finset.sum_congr rfl fun r hr => ?_
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
              exact cosetOf_card hsd'
                (hs'def ▸ hgrange j (Finset.mem_range.mp hj))
          _ = b * d' := by
              rw [Finset.sum_const, smul_eq_mul,
                Finset.card_image_of_injOn fun j₁ h₁ j₂ h₂ heq =>
                  hginj j₁ (Finset.mem_range.mp h₁) j₂ (Finset.mem_range.mp h₂) heq,
                Finset.card_range]
      · intro r₁ h₁ r₂ h₂ hne
        obtain ⟨j₁, hj₁, rfl⟩ := Finset.mem_image.mp h₁
        obtain ⟨j₂, hj₂, rfl⟩ := Finset.mem_image.mp h₂
        exact cosetOf_disjoint_same
          (hs'def ▸ hgrange j₁ (Finset.mem_range.mp hj₁))
          (hs'def ▸ hgrange j₂ (Finset.mem_range.mp hj₂)) hne
    have hXY : Disjoint
        (((Finset.range a).image (fun j => j % k + G * (j / k))).biUnion (cosetOf n d))
        (((Finset.range b).image (fun j => (k + j % k') + G * (j / k'))).biUnion
          (cosetOf n d')) := by
      rw [Finset.disjoint_biUnion_left]
      intro α hα
      rw [Finset.disjoint_biUnion_right]
      intro β hβ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hα
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hβ
      have hja := Finset.mem_range.mp hj
      have hib := Finset.mem_range.mp hi
      refine cosetOf_disjoint_cross (hsdef ▸ hfrange j hja)
        (hs'def ▸ hgrange i hib) ?_
      rw [← hsdef, ← hs'def, ← hGdef, hfclass j hja, hgclass i hib]
      exact Nat.ne_of_lt
        (lt_of_lt_of_le (Nat.mod_lt _ (hk0 j hja)) (Nat.le_add_right k _))
    rw [Finset.card_union_of_disjoint hXY, hXcard, hYcard]

/-- **Sufficiency**, in the concrete form. -/
theorem packable_of_capacity {n d d' a b : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hd' : 0 < d') (hdn : d ∣ n) (hd'n : d' ∣ n)
    (hcap : (a + (n / d) / Nat.gcd (n / d) (n / d') - 1) / ((n / d) / Nat.gcd (n / d) (n / d'))
      + (b + (n / d') / Nat.gcd (n / d) (n / d') - 1) / ((n / d') / Nat.gcd (n / d) (n / d'))
      ≤ Nat.gcd (n / d) (n / d')) :
    Packable n d d' a b := by
  have hs : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
  have hs' : 0 < n / d' := Nat.div_pos (Nat.le_of_dvd hn hd'n) hd'
  have hG : 0 < Nat.gcd (n / d) (n / d') := Nat.gcd_pos_of_pos_left _ hs
  have hGs : Nat.gcd (n / d) (n / d') ∣ n / d := Nat.gcd_dvd_left _ _
  have hGs' : Nat.gcd (n / d) (n / d') ∣ n / d' := Nat.gcd_dvd_right _ _
  have hm : 0 < (n / d) / Nat.gcd (n / d) (n / d') :=
    Nat.div_pos (Nat.le_of_dvd hs hGs) hG
  have hm' : 0 < (n / d') / Nat.gcd (n / d) (n / d') :=
    Nat.div_pos (Nat.le_of_dvd hs' hGs') hG
  exact packable_of_blocks hn hd hd' hdn hd'n rfl rfl rfl hG
    (Nat.div_mul_cancel hGs) (Nat.div_mul_cancel hGs')
    ((ceil_le_iff hm).mp le_rfl) ((ceil_le_iff hm').mp le_rfl)
    hcap

/-- **THE TWO-GENERATOR PACKING CAPACITY LAW**: `a` canonical `μ_d`-cosets and
`b` canonical `μ_{d'}`-cosets fit pairwise disjointly in `[0, n)` IFF
`⌈a/m⌉ + ⌈b/m'⌉ ≤ G`, where `s = n/d`, `s' = n/d'`, `G = gcd(s, s')`,
`m = s/G`, `m' = s'/G`.  The O116 CRT obstruction is the instance `G = 1`,
`a = b = 1`. -/
theorem two_generator_capacity {n d d' a b : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hd' : 0 < d') (hdn : d ∣ n) (hd'n : d' ∣ n) :
    Packable n d d' a b ↔
      (a + (n / d) / Nat.gcd (n / d) (n / d') - 1) / ((n / d) / Nat.gcd (n / d) (n / d'))
        + (b + (n / d') / Nat.gcd (n / d) (n / d') - 1) / ((n / d') / Nat.gcd (n / d) (n / d'))
        ≤ Nat.gcd (n / d) (n / d') :=
  ⟨capacity_of_packable hn hd hd' hdn hd'n,
    packable_of_capacity hn hd hd' hdn hd'n⟩

/-! ## The window-fiber consumer -/

/-- A packing whose generators exceed `t` realizes its mass in the window
fiber: the union is an `IsWindowCosetUnion n t`, hence (O106 ⟸ direction)
kills the whole window `1 ≤ j ≤ t` — the mass `a·d + b·d'` is realizable. -/
theorem two_gen_mass_realizable {n d d' a b t : ℕ} (hn : 0 < n)
    (hd : 0 < d) (hd' : 0 < d') (hdn : d ∣ n) (hd'n : d' ∣ n)
    (htd : t < d) (htd' : t < d')
    (hcap : (a + (n / d) / Nat.gcd (n / d) (n / d') - 1) / ((n / d) / Nat.gcd (n / d) (n / d'))
      + (b + (n / d') / Nat.gcd (n / d) (n / d') - 1) / ((n / d') / Nat.gcd (n / d) (n / d'))
      ≤ Nat.gcd (n / d) (n / d')) :
    ∃ S : Finset ℕ, IsWindowCosetUnion n t S ∧ S.card = a * d + b * d' := by
  classical
  obtain ⟨A, B, hAs, hBs, hcA, hcB, hcard⟩ :=
    packable_of_capacity hn hd hd' hdn hd'n hcap
  have hcross := cross_disjoint_of_card hn hd hd' hdn hd'n hAs hBs hcA hcB hcard
  refine ⟨A.biUnion (cosetOf n d) ∪ B.biUnion (cosetOf n d'), ?_, hcard⟩
  refine ⟨A.image (cosetOf n d) ∪ B.image (cosetOf n d'), ?_, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with h | h
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h
      exact ⟨d, hdn, htd, r, Finset.mem_range.mp (hAs hr), rfl⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h
      exact ⟨d', hd'n, htd', r, Finset.mem_range.mp (hBs hr), rfl⟩
  · intro P hP Q hQ hne
    show Disjoint P Q
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hP) with hPm | hPm <;>
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hQ) with hQm | hQm
    · obtain ⟨r₁, h₁, rfl⟩ := Finset.mem_image.mp hPm
      obtain ⟨r₂, h₂, rfl⟩ := Finset.mem_image.mp hQm
      exact cosetOf_disjoint_same (Finset.mem_range.mp (hAs h₁))
        (Finset.mem_range.mp (hAs h₂)) (fun hcon => hne (by rw [hcon]))
    · obtain ⟨r₁, h₁, rfl⟩ := Finset.mem_image.mp hPm
      obtain ⟨r₂, h₂, rfl⟩ := Finset.mem_image.mp hQm
      exact hcross r₁ h₁ r₂ h₂
    · obtain ⟨r₁, h₁, rfl⟩ := Finset.mem_image.mp hPm
      obtain ⟨r₂, h₂, rfl⟩ := Finset.mem_image.mp hQm
      exact (hcross r₂ h₂ r₁ h₁).symm
    · obtain ⟨r₁, h₁, rfl⟩ := Finset.mem_image.mp hPm
      obtain ⟨r₂, h₂, rfl⟩ := Finset.mem_image.mp hQm
      exact cosetOf_disjoint_same (Finset.mem_range.mp (hBs h₁))
        (Finset.mem_range.mp (hBs h₂)) (fun hcon => hne (by rw [hcon]))
  · ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, id_eq]
    constructor
    · rintro (⟨r, hr, hx⟩ | ⟨r, hr, hx⟩)
      · exact ⟨cosetOf n d r, Or.inl ⟨r, hr, rfl⟩, hx⟩
      · exact ⟨cosetOf n d' r, Or.inr ⟨r, hr, rfl⟩, hx⟩
    · rintro ⟨P, (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩), hx⟩
      · exact Or.inl ⟨r, hr, hx⟩
      · exact Or.inr ⟨r, hr, hx⟩

/-! ## Teeth -/

/-- The O116 refutation through the general law: one `μ_9`- and one
`μ_4`-coset at `n = 36` can NEVER be disjoint (`G = gcd(4, 9) = 1`,
`⌈1/4⌉ + ⌈1/9⌉ = 2 > 1`). -/
example : ¬ Packable 36 9 4 1 1 := by
  intro h
  have := capacity_of_packable (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h
  exact absurd this (by decide)

/-- A positive instance: three `μ_6`-cosets and two `μ_9`-cosets pack in
`[0, 36)` (`s = 6, s' = 4, G = 2, m = 3, m' = 2`: `⌈3/3⌉ + ⌈2/2⌉ = 2 ≤ 2`),
realizing mass `3·6 + 2·9 = 36` — a full tiling mixing generators. -/
example : Packable 36 6 9 3 2 :=
  packable_of_capacity (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide)

end TwoGenPackingCapacity

#print axioms TwoGenPackingCapacity.mem_cosetOf_iff
#print axioms TwoGenPackingCapacity.cosetOf_disjoint_same
#print axioms TwoGenPackingCapacity.cosetOf_disjoint_cross
#print axioms TwoGenPackingCapacity.cosetOf_not_disjoint_cross
#print axioms TwoGenPackingCapacity.capacity_of_packable
#print axioms TwoGenPackingCapacity.packable_of_capacity
#print axioms TwoGenPackingCapacity.two_generator_capacity
#print axioms TwoGenPackingCapacity.two_gen_mass_realizable
