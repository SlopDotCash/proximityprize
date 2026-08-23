/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnTwoPrimeAssembly
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnPrimePower

/-!
# Issue #232 — THE WINDOWED TWO-PRIME LAW: the full t-general window-fiber
# classification (O70's exhaustively-verified law as a theorem, O105)

The O70 numeric lane verified exhaustively (86/86 `(n,t)` fibers at
`n = 12, 18, 24, 36`, full mask spaces) the **mixed-radix tower law**: for every
window length `t`, the window fiber `{S ⊆ μ_n : p₁(S) = ⋯ = p_t(S) = 0}` (vanishing
power sums `p_j(S) = Σ_{z∈S} z^j` for `1 ≤ j ≤ t`) EQUALS the family of disjoint
unions of rotated `μ_d`-cosets with `d ∣ n`, `d > t` — the *pure size-kill law*
(`μ_d` dies iff `d ≤ t`, plateaus between consecutive divisors).  This file proves
that law for two-prime-smooth `n = p^a·q^b` in exponent form:

* `windowed_two_prime` — **the headline iff**: for `ζ` a primitive `n`-th root of
  unity in a characteristic-zero field and `S ⊆ [0, n)`,
  `(∀ j, 1 ≤ j ≤ t → Σ_{e∈S} ζ^{je} = 0)  ↔  S` is a disjoint union of canonical
  rotated `μ_d`-cosets (`d ∣ n`, `d > t`).

The induction is **multiplicity-free** and needs no weighted de Bruijn machinery:

* base `t = 0`: every subset is a disjoint union of singletons = `μ_1`-cosets;
* step `t → t+1`: the inherited decomposition has cosets `d ≥ t+1`; if
  `(t+1) ∤ n` there is nothing to kill; otherwise the `j = t+1` power sum
  annihilates every `d > t+1` coset (`isPacket_pow_sum_eq_zero`) and extracts
  `(t+1) · Σ_{bases r} (ζ^{t+1})^r = 0` over the **distinct** bases of the
  `d = t+1` cosets (the base of a canonical coset is `e % (n/(t+1))` for ANY of
  its elements, so disjoint cosets have distinct bases — no multiplicities ever
  appear); de Bruijn at level `n/(t+1)` (`LevelDecomposes`, discharged by O94's
  two-prime theorem and O92's prime-power theorem at every divisor level) breaks
  the bases into prime `d'`-packets; and the **merge lemma** (`isPacket_merge`)
  reassembles each base packet's fattened cosets into ONE canonical
  `μ_{(t+1)·d'}`-coset, with `(t+1)·d' > t+1`.

The level classifier is abstracted as `LevelDecomposes`, so `windowed_law` (the
induction wrapper) is modulus-agnostic: a future level classification at
three-prime moduli instantly yields the windowed law there.

This subsumes the `t = 1` case — `debruijn_two_prime` restated with `d > 1`
cosets — and is the dense-window complement of `TwoPrimeWindowLaw.lean`'s sparse
`q`-power-window rung (O97).
-/

namespace DeBruijnWindowedLaw

open Finset DeBruijnTwoPrimeAssembly

/-! ## Canonical cosets and their power sums -/

/-- The canonical rotated `μ_τ`-coset over base `r` at level `n`: the arithmetic
progression `{r + s·(n/τ) : s < τ}`.  For `r < n/τ` this is exactly
`IsPacket n τ` shape. -/
def cosetOf (n τ r : ℕ) : Finset ℕ :=
  (Finset.range τ).image fun s => r + s * (n / τ)

/-- `IsPacket` is definitionally "is a canonical coset over a small base". -/
lemma isPacket_iff_cosetOf {n d : ℕ} {P : Finset ℕ} :
    IsPacket n d P ↔ ∃ r < n / d, P = cosetOf n d r := Iff.rfl

/-- The base of a canonical coset is recovered from any element by reduction
mod the step. -/
lemma mod_of_mem_cosetOf {n τ r e : ℕ} (hr : r < n / τ)
    (he : e ∈ cosetOf n τ r) : e % (n / τ) = r := by
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The base lies in its own coset (witness `s = 0`). -/
lemma base_mem_cosetOf {n τ r : ℕ} (hτ : 0 < τ) : r ∈ cosetOf n τ r :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hτ, by ring⟩

/-- **Coset power-sum kill**: a canonical `μ_d`-coset (as an `IsPacket`)
annihilates the `j`-th power sum whenever `d ∤ j`. -/
lemma isPacket_pow_sum_eq_zero {L : Type*} [Field L] {n d j : ℕ} (hn : 0 < n)
    (hdn : d ∣ n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {P : Finset ℕ} (hP : IsPacket n d P) (hj : ¬ d ∣ j) :
    ∑ e ∈ P, ζ ^ (j * e) = 0 := by
  obtain ⟨r, _, rfl⟩ := hP
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · obtain ⟨c, hc⟩ := hdn
      omega
    · exact h
  have hk : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
  rw [Finset.sum_image (fun s₁ _ s₂ _ heq =>
    Nat.eq_of_mul_eq_mul_right hk (by omega))]
  have hsplit : ∀ s ∈ Finset.range d,
      ζ ^ (j * (r + s * (n / d))) = ζ ^ (j * r) * (ζ ^ (j * (n / d))) ^ s := by
    intro s _
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  have hx1 : ζ ^ (j * (n / d)) ≠ 1 := by
    intro h1
    rw [hζ.pow_eq_one_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    refine hj ⟨c, Nat.eq_of_mul_eq_mul_right hk ?_⟩
    calc j * (n / d) = n * c := hc
      _ = d * (n / d) * c := by rw [Nat.mul_div_cancel' hdn]
      _ = d * c * (n / d) := by ring
  have hxd : (ζ ^ (j * (n / d))) ^ d = 1 := by
    rw [← pow_mul]
    refine (hζ.pow_eq_one_iff_dvd _).mpr ⟨j, ?_⟩
    calc j * (n / d) * d = j * (d * (n / d)) := by ring
      _ = n * j := by rw [Nat.mul_div_cancel' hdn]; ring
  have hgeom : ∑ s ∈ Finset.range d, (ζ ^ (j * (n / d))) ^ s = 0 := by
    rw [geom_sum_eq hx1, hxd, sub_self, zero_div]
  rw [hgeom, mul_zero]

/-- **Coset power-sum saturation**: at the resonant exponent (`τ` itself, for a
`τ`-coset with `τ·(n/τ) = n`), each element contributes `ζ^{τ·r}` — the sum is
`τ · (ζ^τ)^r`. -/
lemma cosetOf_pow_sum {L : Type*} [Field L] {n τ r : ℕ}
    (hmpos : 0 < n / τ) (hτm : τ * (n / τ) = n) {ζ : L} (hζn : ζ ^ n = 1) :
    ∑ e ∈ cosetOf n τ r, ζ ^ (τ * e) = ((τ : ℕ) : L) * (ζ ^ τ) ^ r := by
  rw [cosetOf, Finset.sum_image (fun s₁ _ s₂ _ heq =>
    Nat.eq_of_mul_eq_mul_right hmpos (by omega))]
  have hterm : ∀ s ∈ Finset.range τ, ζ ^ (τ * (r + s * (n / τ))) = ζ ^ (τ * r) := by
    intro s _
    have hexp : τ * (r + s * (n / τ)) = τ * r + n * s := by
      calc τ * (r + s * (n / τ)) = τ * r + (τ * (n / τ)) * s := by ring
        _ = τ * r + n * s := by rw [hτm]
    have hns : ζ ^ (n * s) = 1 := by rw [pow_mul, hζn, one_pow]
    rw [hexp, pow_add, hns, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, pow_mul]

/-! ## The merge lemma: a base packet fattened by its cosets is one bigger coset -/

/-- **The merge step**: a canonical `d`-packet of bases at level `n/τ`, with each
base fattened to its full `μ_τ`-coset at level `n`, is ONE canonical
`(τ·d)`-coset at level `n`. -/
lemma isPacket_merge {n τ d : ℕ} (hτ : 0 < τ) (hd : 0 < d) (htd : τ * d ∣ n)
    {B : Finset ℕ} (hB : IsPacket (n / τ) d B) :
    IsPacket n (τ * d) (B.biUnion (cosetOf n τ)) := by
  obtain ⟨c, rfl⟩ := htd
  have hnt : τ * d * c / τ = d * c := by
    rw [mul_assoc]
    exact Nat.mul_div_cancel_left _ hτ
  have hntd : τ * d * c / (τ * d) = c := Nat.mul_div_cancel_left _ (Nat.mul_pos hτ hd)
  obtain ⟨r₀, hr₀, hBeq⟩ := hB
  rw [hnt, Nat.mul_div_cancel_left _ hd] at hr₀ hBeq
  subst hBeq
  refine ⟨r₀, by rw [hntd]; exact hr₀, ?_⟩
  ext x
  simp only [cosetOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, hnt, hntd]
  constructor
  · rintro ⟨r, ⟨s', hs', rfl⟩, s, hs, rfl⟩
    refine ⟨s' + s * d, ?_, by ring⟩
    calc s' + s * d < d + s * d := by omega
      _ = (s + 1) * d := by ring
      _ ≤ τ * d := Nat.mul_le_mul_right d hs
  · rintro ⟨u, hu, rfl⟩
    refine ⟨r₀ + (u % d) * c, ⟨u % d, Nat.mod_lt _ hd, rfl⟩,
      u / d, (Nat.div_lt_iff_lt_mul hd).mpr hu, ?_⟩
    have hsplit : u % d + u / d * d = u := Nat.mod_add_div' u d
    calc r₀ + u % d * c + u / d * (d * c)
        = r₀ + (u % d + u / d * d) * c := by ring
      _ = r₀ + u * c := by rw [hsplit]

/-! ## The window-coset predicate and the easy direction -/

/-- `S ⊆ [0,n)` is a **disjoint union of canonical rotated `μ_d`-cosets with
`d ∣ n`, `d > t`** — the divisor-coset prediction of the windowed law. -/
def IsWindowCosetUnion (n t : ℕ) (S : Finset ℕ) : Prop :=
  ∃ Ps : Finset (Finset ℕ),
    (∀ P ∈ Ps, ∃ d, d ∣ n ∧ t < d ∧ IsPacket n d P) ∧
    (↑Ps : Set (Finset ℕ)).PairwiseDisjoint id ∧ S = Ps.biUnion id

/-- **⟸ of the windowed law**: a window coset union kills every power sum in the
window `1 ≤ j ≤ t` (each coset has `d > t ≥ j ≥ 1`, so `d ∤ j`). -/
theorem window_vanishes_of_isWindowCosetUnion {L : Type*} [Field L] {n t : ℕ}
    (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n) {S : Finset ℕ}
    (h : IsWindowCosetUnion n t S) :
    ∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0 := by
  intro j hj1 hjt
  obtain ⟨Ps, hpk, hdisj, rfl⟩ := h
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun P hP => ?_
  obtain ⟨d, hdn, htd, hPd⟩ := hpk P hP
  refine isPacket_pow_sum_eq_zero hn hdn hζ hPd fun hdj => ?_
  have := Nat.le_of_dvd (by omega) hdj
  omega

/-- Base case `t = 0`: every subset of `[0, n)` is a disjoint union of
singletons, i.e. canonical `μ_1`-cosets. -/
lemma isWindowCosetUnion_zero {n : ℕ} {S : Finset ℕ} (hS : ∀ e ∈ S, e < n) :
    IsWindowCosetUnion n 0 S := by
  classical
  refine ⟨S.image (fun e => ({e} : Finset ℕ)), ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨1, one_dvd n, one_pos, e, by simpa using hS e he, ?_⟩
    simp
  · intro P₁ h₁ P₂ h₂ hne
    obtain ⟨e₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₁)
    obtain ⟨e₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₂)
    have he : e₁ ≠ e₂ := fun h => hne (by rw [h])
    simp only [Function.onFun, id_eq]
    rwa [Finset.disjoint_singleton]
  · ext x
    simp

/-! ## The level-classification interface

A modulus `m` *level-decomposes* over `L` if every vanishing subset sum of
`m`-th roots of unity (exponent form) is a disjoint union of canonical prime
packets.  Two-prime-smooth divisors level-decompose (O92 + O94, below); a future
three-prime classifier plugs in here and inherits the whole windowed law. -/

/-- Vanishing subset sums at level `m` decompose into canonical prime packets. -/
def LevelDecomposes (L : Type*) [Field L] (m : ℕ) : Prop :=
  ∀ ξ : L, IsPrimitiveRoot ξ m → ∀ B : Finset ℕ, (∀ r ∈ B, r < m) →
    (∑ r ∈ B, ξ ^ r = 0) →
    ∃ Qs : Finset (Finset ℕ),
      (∀ Q ∈ Qs, ∃ d, d.Prime ∧ d ∣ m ∧ IsPacket m d Q) ∧
      (↑Qs : Set (Finset ℕ)).PairwiseDisjoint id ∧ B = Qs.biUnion id

/-! ## The induction step -/

/-- **One upgrade step**: a `t`-window decomposition plus the `(t+1)`-st power sum
upgrades to a `(t+1)`-window decomposition, given level decomposition at
`n/(t+1)`.  The `(t+1)`-st power sum kills every `d > t+1` coset and extracts a
vanishing multiplicity-free base sum at level `n/(t+1)`; the level classifier
breaks the bases into prime packets; the merge lemma reassembles. -/
private lemma window_step {L : Type*} [Field L] [CharZero L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) {t : ℕ} (htn : t + 1 < n) (hdvd : t + 1 ∣ n)
    (hLD : LevelDecomposes L (n / (t + 1)))
    {S : Finset ℕ} (hprev : IsWindowCosetUnion n t S)
    (hsum : ∑ e ∈ S, ζ ^ ((t + 1) * e) = 0) :
    IsWindowCosetUnion n (t + 1) S := by
  classical
  obtain ⟨Ps, hpk, hdisj, hSuni⟩ := hprev
  have hnpos : 0 < n := by omega
  have hτm : (t + 1) * (n / (t + 1)) = n := Nat.mul_div_cancel' hdvd
  have hmpos : 0 < n / (t + 1) :=
    Nat.div_pos (Nat.le_of_dvd hnpos hdvd) (Nat.succ_pos t)
  -- the resonant cosets carry exactly `IsPacket n (t+1)` structure
  have hsmallPacket : ∀ P ∈ Ps.filter (fun P => P.card = t + 1),
      ∃ r < n / (t + 1), P = cosetOf n (t + 1) r := by
    intro P hP
    obtain ⟨hPs, hcard⟩ := Finset.mem_filter.mp hP
    obtain ⟨d, hdn, htd, hPd⟩ := hpk P hPs
    have hd0 : 0 < d := by omega
    have hcd : P.card = d :=
      hPd.card_eq (Nat.div_pos (Nat.le_of_dvd hnpos hdn) hd0)
    have hdτ : d = t + 1 := by omega
    exact hdτ ▸ hPd
  have hbig : ∀ P ∈ Ps.filter (fun P => ¬ P.card = t + 1),
      ∃ d, d ∣ n ∧ t + 1 < d ∧ IsPacket n d P := by
    intro P hP
    obtain ⟨hPs, hcard⟩ := Finset.mem_filter.mp hP
    obtain ⟨d, hdn, htd, hPd⟩ := hpk P hPs
    have hd0 : 0 < d := by omega
    have hcd : P.card = d :=
      hPd.card_eq (Nat.div_pos (Nat.le_of_dvd hnpos hdn) hd0)
    exact ⟨d, hdn, by omega, hPd⟩
  -- every element of a resonant coset recovers the base by mod-reduction
  have hbaseEq : ∀ P ∈ Ps.filter (fun P => P.card = t + 1), ∀ e ∈ P,
      P = cosetOf n (t + 1) (e % (n / (t + 1))) := by
    intro P hP e heP
    obtain ⟨r, hr, rfl⟩ := hsmallPacket P hP
    rw [mod_of_mem_cosetOf hr heP]
  -- the canonical re-imaging of the resonant cosets through their base set
  have hPsmall_eq : Ps.filter (fun P => P.card = t + 1)
      = (((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
          (· % (n / (t + 1)))).image (cosetOf n (t + 1)) := by
    ext P
    constructor
    · intro hP
      obtain ⟨r, hr, hPeq⟩ := hsmallPacket P hP
      have hne : P.Nonempty := by
        rw [hPeq]
        exact ⟨r, base_mem_cosetOf (Nat.succ_pos t)⟩
      obtain ⟨e, heP⟩ := hne
      exact Finset.mem_image.mpr ⟨e % (n / (t + 1)),
        Finset.mem_image.mpr ⟨e, Finset.mem_biUnion.mpr ⟨P, hP, heP⟩, rfl⟩,
        (hbaseEq P hP e heP).symm⟩
    · intro hP
      obtain ⟨r, hrB, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨e, heU, rfl⟩ := Finset.mem_image.mp hrB
      obtain ⟨P', hP', heP'⟩ := Finset.mem_biUnion.mp heU
      rw [← hbaseEq P' hP' e heP']
      exact hP'
  -- the base set: bounded, and the coset map is injective on it
  have hBlt : ∀ r ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
      (· % (n / (t + 1))), r < n / (t + 1) := by
    intro r hr
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hr
    exact Nat.mod_lt _ hmpos
  have hcosetInj : ∀ r₁ ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
        (· % (n / (t + 1))),
      ∀ r₂ ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
        (· % (n / (t + 1))),
      cosetOf n (t + 1) r₁ = cosetOf n (t + 1) r₂ → r₁ = r₂ := by
    intro r₁ h₁ r₂ h₂ heq
    have hmem : r₁ ∈ cosetOf n (t + 1) r₂ :=
      heq ▸ base_mem_cosetOf (Nat.succ_pos t)
    obtain ⟨s, _, hseq⟩ := Finset.mem_image.mp hmem
    have hr₁ : r₁ < n / (t + 1) := hBlt _ h₁
    rcases Nat.eq_zero_or_pos s with rfl | hspos
    · omega
    · have : n / (t + 1) ≤ s * (n / (t + 1)) :=
        Nat.le_mul_of_pos_left _ hspos
      omega
  -- extract the vanishing base sum at level n/(t+1)
  have hτsum : ∑ P ∈ Ps, ∑ e ∈ P, ζ ^ ((t + 1) * e) = 0 := by
    have h := hsum
    rw [hSuni, Finset.sum_biUnion hdisj] at h
    simpa using h
  rw [← Finset.sum_filter_add_sum_filter_not Ps (fun P => P.card = t + 1)]
    at hτsum
  have hbig0 : ∑ P ∈ Ps.filter (fun P => ¬ P.card = t + 1),
      ∑ e ∈ P, ζ ^ ((t + 1) * e) = 0 := by
    refine Finset.sum_eq_zero fun P hP => ?_
    obtain ⟨d, hdn, htd, hPd⟩ := hbig P hP
    refine isPacket_pow_sum_eq_zero hnpos hdn hζ hPd fun hddvd => ?_
    have := Nat.le_of_dvd (Nat.succ_pos t) hddvd
    omega
  rw [hbig0, add_zero, hPsmall_eq, Finset.sum_image hcosetInj] at hτsum
  have hinner : ∀ r ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
      (· % (n / (t + 1))),
      ∑ e ∈ cosetOf n (t + 1) r, ζ ^ ((t + 1) * e)
        = ((t + 1 : ℕ) : L) * (ζ ^ (t + 1)) ^ r :=
    fun r _ => cosetOf_pow_sum hmpos hτm hζ.pow_eq_one
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum] at hτsum
  have hξsum : ∑ r ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
      (· % (n / (t + 1))), (ζ ^ (t + 1)) ^ r = 0 := by
    rcases mul_eq_zero.mp hτsum with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero t))
    · exact h
  -- classify the bases at level n/(t+1)
  have hξ : IsPrimitiveRoot (ζ ^ (t + 1)) (n / (t + 1)) := hζ.pow hnpos hτm.symm
  obtain ⟨Qs, hQpk, hQdisj, hBuni⟩ := hLD _ hξ _ hBlt hξsum
  -- elements of merged cosets recover their base inside Q
  have hmem_merge : ∀ Q ∈ Qs, ∀ x ∈ Q.biUnion (cosetOf n (t + 1)),
      x % (n / (t + 1)) ∈ Q := by
    intro Q hQ x hx
    obtain ⟨r, hrQ, hxc⟩ := Finset.mem_biUnion.mp hx
    have hrB : r ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
        (· % (n / (t + 1))) := hBuni ▸ Finset.mem_biUnion.mpr ⟨Q, hQ, hrQ⟩
    rw [mod_of_mem_cosetOf (hBlt r hrB) hxc]
    exact hrQ
  -- merged cosets sit inside the resonant union
  have hmerge_sub : ∀ Q ∈ Qs, Q.biUnion (cosetOf n (t + 1))
      ⊆ (Ps.filter (fun P => P.card = t + 1)).biUnion id := by
    intro Q hQ x hx
    obtain ⟨r, hrQ, hxc⟩ := Finset.mem_biUnion.mp hx
    have hrB : r ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
        (· % (n / (t + 1))) := hBuni ▸ Finset.mem_biUnion.mpr ⟨Q, hQ, hrQ⟩
    have hPmem : cosetOf n (t + 1) r ∈ Ps.filter (fun P => P.card = t + 1) := by
      rw [hPsmall_eq]
      exact Finset.mem_image_of_mem _ hrB
    exact Finset.mem_biUnion.mpr ⟨_, hPmem, hxc⟩
  -- cross-disjointness: non-resonant cosets avoid every merged coset
  have hcross : ∀ P ∈ Ps.filter (fun P => ¬ P.card = t + 1), ∀ Q ∈ Qs,
      Disjoint P (Q.biUnion (cosetOf n (t + 1))) := by
    intro P hP Q hQ
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => ?_
    obtain ⟨P', hP', hxP'⟩ := Finset.mem_biUnion.mp (hmerge_sub Q hQ hx₂)
    have hne' : P ≠ P' := by
      intro hcon
      have hc₁ := (Finset.mem_filter.mp hP).2
      have hc₂ := (Finset.mem_filter.mp hP').2
      rw [hcon] at hc₁
      exact hc₁ hc₂
    have hd := hdisj (Finset.mem_coe.mpr (Finset.filter_subset _ _ hP))
      (Finset.mem_coe.mpr (Finset.filter_subset _ _ hP')) hne'
    exact Finset.disjoint_left.mp hd hx₁ hxP'
  -- assemble
  refine ⟨Ps.filter (fun P => ¬ P.card = t + 1)
      ∪ Qs.image (fun Q => Q.biUnion (cosetOf n (t + 1))), ?_, ?_, ?_⟩
  · -- every member is a `d > t+1` packet
    intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hbig P hP
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨d, hdpr, hdm, hQd⟩ := hQpk Q hQ
      have hdvd' : (t + 1) * d ∣ n :=
        hτm ▸ mul_dvd_mul_left (t + 1) hdm
      exact ⟨(t + 1) * d, hdvd',
        (Nat.lt_mul_iff_one_lt_right (Nat.succ_pos t)).mpr hdpr.one_lt,
        isPacket_merge (Nat.succ_pos t) hdpr.pos hdvd' hQd⟩
  · -- pairwise disjointness
    intro P₁ h₁ P₂ h₂ hne
    show Disjoint P₁ P₂
    rcases Finset.mem_union.mp (Finset.mem_coe.mp h₁) with hm₁ | hm₁ <;>
      rcases Finset.mem_union.mp (Finset.mem_coe.mp h₂) with hm₂ | hm₂
    · exact hdisj (Finset.mem_coe.mpr (Finset.filter_subset _ _ hm₁))
        (Finset.mem_coe.mpr (Finset.filter_subset _ _ hm₂)) hne
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hm₂
      exact hcross P₁ hm₁ Q hQ
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hm₁
      exact (hcross P₂ hm₂ Q hQ).symm
    · obtain ⟨Q₁, hQ₁, rfl⟩ := Finset.mem_image.mp hm₁
      obtain ⟨Q₂, hQ₂, rfl⟩ := Finset.mem_image.mp hm₂
      have hQne : Q₁ ≠ Q₂ := fun hcon => hne (by rw [hcon])
      refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => ?_
      have hb₁ := hmem_merge Q₁ hQ₁ x hx₁
      have hb₂ := hmem_merge Q₂ hQ₂ x hx₂
      have hd := hQdisj (Finset.mem_coe.mpr hQ₁) (Finset.mem_coe.mpr hQ₂) hQne
      exact Finset.disjoint_left.mp hd hb₁ hb₂
  · -- the union is S
    ext x
    constructor
    · intro hx
      have hx' : x ∈ Ps.biUnion id := hSuni ▸ hx
      obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx'
      by_cases hcard : P.card = t + 1
      · have hPm : P ∈ Ps.filter (fun P => P.card = t + 1) :=
          Finset.mem_filter.mpr ⟨hP, hcard⟩
        have hrB : x % (n / (t + 1))
            ∈ ((Ps.filter (fun P => P.card = t + 1)).biUnion id).image
              (· % (n / (t + 1))) :=
          Finset.mem_image.mpr ⟨x, Finset.mem_biUnion.mpr ⟨P, hPm, hxP⟩, rfl⟩
        have hrQs : x % (n / (t + 1)) ∈ Qs.biUnion id := hBuni ▸ hrB
        obtain ⟨Q, hQ, hrQ⟩ := Finset.mem_biUnion.mp hrQs
        refine Finset.mem_biUnion.mpr ⟨Q.biUnion (cosetOf n (t + 1)),
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ), ?_⟩
        refine Finset.mem_biUnion.mpr ⟨x % (n / (t + 1)), hrQ, ?_⟩
        rw [← hbaseEq P hPm x hxP]
        exact hxP
      · exact Finset.mem_biUnion.mpr ⟨P,
          Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, hcard⟩), hxP⟩
    · intro hx
      obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx
      rcases Finset.mem_union.mp hP with hP | hP
      · rw [hSuni]
        exact Finset.mem_biUnion.mpr ⟨P, Finset.filter_subset _ _ hP, hxP⟩
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
        obtain ⟨P', hP', hxP'⟩ := Finset.mem_biUnion.mp (hmerge_sub Q hQ hxP)
        rw [hSuni]
        exact Finset.mem_biUnion.mpr ⟨P', Finset.filter_subset _ _ hP', hxP'⟩

/-! ## The induction wrapper and the modulus-agnostic law -/

/-- **The forward direction**, by induction on the window length: window
vanishing forces the divisor-coset decomposition, given level decomposition at
every divisor level `≥ 2`. -/
theorem isWindowCosetUnion_of_window {L : Type*} [Field L] [CharZero L] {n : ℕ}
    (hLD : ∀ m, m ∣ n → 2 ≤ m → LevelDecomposes L m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) {S : Finset ℕ} (hS : ∀ e ∈ S, e < n) :
    ∀ t, t < n → (∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0) →
      IsWindowCosetUnion n t S := by
  intro t
  induction t with
  | zero => exact fun _ _ => isWindowCosetUnion_zero hS
  | succ t IH =>
    intro htn hwin
    have hprev := IH (by omega) fun j h1 h2 => hwin j h1 (by omega)
    by_cases hdvd : (t + 1) ∣ n
    · have hτm : (t + 1) * (n / (t + 1)) = n := Nat.mul_div_cancel' hdvd
      have hm2 : 2 ≤ n / (t + 1) := by
        by_contra hlt
        have hmpos : 0 < n / (t + 1) :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.succ_pos t)
        have h1 : n / (t + 1) = 1 := by omega
        rw [h1, mul_one] at hτm
        omega
      exact window_step hζ htn hdvd
        (hLD _ ⟨t + 1, (Nat.div_mul_cancel hdvd).symm⟩ hm2) hprev
        (hwin _ (Nat.succ_pos t) le_rfl)
    · -- no divisor equals t+1: the inherited decomposition already qualifies
      obtain ⟨Ps, hpk, hdisj, hSuni⟩ := hprev
      refine ⟨Ps, fun P hP => ?_, hdisj, hSuni⟩
      obtain ⟨d, hdn, htd, hPd⟩ := hpk P hP
      refine ⟨d, hdn, ?_, hPd⟩
      rcases Nat.lt_or_ge (t + 1) d with h | h
      · exact h
      · have hdeq : d = t + 1 := by omega
        exact absurd (hdeq ▸ hdn) hdvd

/-- **THE WINDOWED LAW** (modulus-agnostic iff): given level decomposition at
every divisor level, the window fiber at length `t` is exactly the family of
disjoint unions of canonical rotated `μ_d`-cosets with `d ∣ n`, `d > t`. -/
theorem windowed_law {L : Type*} [Field L] [CharZero L] {n : ℕ}
    (hLD : ∀ m, m ∣ n → 2 ≤ m → LevelDecomposes L m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) {S : Finset ℕ} (hS : ∀ e ∈ S, e < n)
    {t : ℕ} (htn : t < n) :
    (∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0) ↔
      IsWindowCosetUnion n t S :=
  ⟨isWindowCosetUnion_of_window hLD hζ hS t htn,
    fun h => window_vanishes_of_isWindowCosetUnion (by omega) hζ h⟩

/-! ## Discharging the level interface at two-prime-smooth moduli -/

/-- Prime-power levels decompose: O92's `debruijn_prime_power` pulled through the
ZMod bridges into canonical-packet form. -/
lemma primePow_packet_decomposition {L : Type*} [Field L] [CharZero L]
    {p c : ℕ} (hp : p.Prime) {ξ : L} (hξ : IsPrimitiveRoot ξ (p ^ (c + 1)))
    {B : Finset ℕ} (hB : ∀ e ∈ B, e < p ^ (c + 1))
    (hsum : ∑ e ∈ B, ξ ^ e = 0) :
    ∃ Qs : Finset (Finset ℕ),
      (∀ Q ∈ Qs, IsPacket (p ^ (c + 1)) p Q) ∧
      (↑Qs : Set (Finset ℕ)).PairwiseDisjoint id ∧ B = Qs.biUnion id := by
  classical
  have hm : 0 < p ^ (c + 1) := pow_pos hp.pos _
  haveI : NeZero (p ^ (c + 1)) := ⟨hm.ne'⟩
  have hsum' : ∑ x ∈ B.image ((↑) : ℕ → ZMod (p ^ (c + 1))), ξ ^ x.val = 0 := by
    rw [sum_image_cast ξ hB]
    exact hsum
  have hcl := DeBruijnPrimePower.closed_add_pow_of_vanishing hp hξ hsum'
  have hcln := closure_nat_of_closure_zmod hm hB hcl
  obtain ⟨Qs, hpk, hdisj, huni⟩ := isPacketUnion_of_closure hp.pos
    (pow_pos hp.pos c) (pow_succ' p c) hB hcln
  refine ⟨Qs, fun Q hQ => ?_, hdisj, huni⟩
  obtain ⟨r, hr, heq⟩ := hpk Q hQ
  have hdiv : p ^ (c + 1) / p = p ^ c := by
    rw [pow_succ']
    exact Nat.mul_div_cancel_left _ hp.pos
  rw [IsPacket, hdiv]
  exact ⟨r, hr, heq⟩

/-- **Every divisor level `≥ 2` of a two-prime-smooth modulus level-decomposes**:
the uniform classifier behind the windowed law, by cases on the divisor's
factorization (two-prime: O94; pure prime power: O92). -/
theorem levelDecomposes_of_dvd_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {m : ℕ} (hm : m ∣ p ^ a * q ^ b) (hm2 : 2 ≤ m) :
    LevelDecomposes L m := by
  intro ξ hξ B hB hsum
  classical
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hm
  obtain ⟨a', _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm₁
  obtain ⟨b', _, rfl⟩ := (Nat.dvd_prime_pow hq).mp hm₂
  rcases Nat.eq_zero_or_pos a' with rfl | hapos
  · rcases Nat.eq_zero_or_pos b' with rfl | hbpos
    · simp at hm2
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hbpos.ne'
      rw [pow_zero, one_mul] at hξ hB ⊢
      obtain ⟨Qs, hpk, hdisj, huni⟩ :=
        primePow_packet_decomposition hq hξ hB hsum
      exact ⟨Qs, fun Q hQ =>
        ⟨q, hq, dvd_pow_self q (Nat.succ_ne_zero c), hpk Q hQ⟩, hdisj, huni⟩
  · rcases Nat.eq_zero_or_pos b' with rfl | hbpos
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hapos.ne'
      rw [pow_zero, mul_one] at hξ hB ⊢
      obtain ⟨Qs, hpk, hdisj, huni⟩ :=
        primePow_packet_decomposition hp hξ hB hsum
      exact ⟨Qs, fun Q hQ =>
        ⟨p, hp, dvd_pow_self p (Nat.succ_ne_zero c), hpk Q hQ⟩, hdisj, huni⟩
    · obtain ⟨Qs, hpk, hdisj, huni⟩ :=
        (debruijn_two_prime hp hq hpq hapos hbpos hξ hB).mp hsum
      refine ⟨Qs, fun Q hQ => ?_, hdisj, huni⟩
      rcases hpk Q hQ with h | h
      · exact ⟨p, hp, dvd_mul_of_dvd_left (dvd_pow_self p hapos.ne') _, h⟩
      · exact ⟨q, hq, dvd_mul_of_dvd_right (dvd_pow_self q hbpos.ne') _, h⟩

/-! ## The headline -/

/-- **THE WINDOWED TWO-PRIME LAW** (O70's exhaustively-verified mixed-radix tower
law as a theorem; the t-general form): for `n = p^a·q^b`, `ζ` a primitive `n`-th
root of unity in a characteristic-zero field, `S ⊆ [0, n)`, and any window length
`t < n`, the power-sum window `1 ≤ j ≤ t` vanishes **iff** `S` is a disjoint
union of canonical rotated `μ_d`-cosets with `d ∣ n` and `d > t` — the pure
size-kill law (`μ_d` survives iff `d > t`).

The `t = 1` instance recovers de Bruijn 1953 (`debruijn_two_prime`, with packets
re-expressed as `d > 1` cosets); larger `t` is new — no literature statement
covers the dense-window fiber at composite `n`. -/
theorem windowed_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < p ^ a * q ^ b)
    {t : ℕ} (htn : t < p ^ a * q ^ b) :
    (∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0) ↔
      IsWindowCosetUnion (p ^ a * q ^ b) t S :=
  windowed_law (fun _ hm hm2 => levelDecomposes_of_dvd_two_prime hp hq hpq hm hm2)
    hζ hS htn

/-! ## Non-vacuity (fired at `ℂ`, `n = 12`, `t = 3`, with teeth)

The converse produces genuine window vanishing for the `μ_4`-coset
`{0, 3, 6, 9}` through the whole window `j = 1, 2, 3`; the forward direction
refutes window-3 vanishing for the `μ_2`-coset `{0, 6}` — a `d ≥ 4` coset cannot
fit in a 2-element set — so the iff genuinely discriminates by window length. -/

private lemma exp_twelfth_primitive' :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12)) (2 ^ 2 * 3 ^ 1) := by
  have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  norm_num at h ⊢
  exact h

/-- Converse fired: the canonical `μ_4`-coset `{0,3,6,9}` at `n = 12` kills the
whole window `j = 1, 2, 3` (`4 ∣ 12`, `4 > 3`). -/
example : ∀ j, 1 ≤ j → j ≤ 3 → ∑ e ∈ ({0, 3, 6, 9} : Finset ℕ),
    Complex.exp (2 * Real.pi * Complex.I / 12) ^ (j * e) = 0 := by
  refine (windowed_two_prime Nat.prime_two Nat.prime_three (by norm_num)
    exp_twelfth_primitive' (by decide) (by norm_num)).mpr ?_
  refine ⟨{({0, 3, 6, 9} : Finset ℕ)}, fun P hP => ?_, ?_, ?_⟩
  · rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨4, by norm_num, by norm_num, 0, by norm_num, by decide⟩
  · rw [Finset.coe_singleton]
    exact Set.pairwiseDisjoint_singleton _ _
  · rw [Finset.singleton_biUnion]
    rfl

/-- Forward direction fired (with teeth): the `μ_2`-coset `{0, 6}` does NOT kill
the window `j ≤ 3` — its decomposition would need a coset of size `> 3` inside a
2-element set. -/
example : ¬ (∀ j, 1 ≤ j → j ≤ 3 → ∑ e ∈ ({0, 6} : Finset ℕ),
    Complex.exp (2 * Real.pi * Complex.I / 12) ^ (j * e) = 0) := by
  intro hcon
  obtain ⟨Ps, hpk, _, huni⟩ := (windowed_two_prime Nat.prime_two Nat.prime_three
    (by norm_num) exp_twelfth_primitive' (by decide) (by norm_num)).mp hcon
  have h0 : (0 : ℕ) ∈ Ps.biUnion id := huni ▸ (by decide : (0 : ℕ) ∈ ({0, 6} : Finset ℕ))
  obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp h0
  have hsub : P ⊆ {0, 6} := fun x hx =>
    huni ▸ Finset.mem_biUnion.mpr ⟨P, hP, hx⟩
  have hcard : P.card ≤ 2 := by
    calc P.card ≤ ({0, 6} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by decide
  obtain ⟨d, hdn, htd, hPd⟩ := hpk P hP
  have hd0 : 0 < d := by omega
  have := hPd.card_eq (Nat.div_pos (Nat.le_of_dvd (by norm_num) hdn) hd0)
  omega

/-! ## The weight spectrum: 0/1 codewords of the window (dual-RS / BCH) code

The window fiber `{S ⊆ [0,n) : Σ_{e∈S} ζ^{je} = 0, 1 ≤ j ≤ t}` is exactly the
set of 0/1-supported codewords of the cyclic code with zeros `ζ, ζ², …, ζ^t` —
a BCH-style dual-RS constraint on the smooth domain.  The windowed law pins
their weights exactly:

* every nonzero weight is a **sum of divisors of `n` exceeding `t`**;
* the minimum nonzero weight is the **least divisor of `n` exceeding `t`** —
  achieved by any single canonical coset.

The classical BCH/designed-distance bound gives only `weight ≥ t + 1`; on smooth
domains the 0/1 minimum weight jumps to the next divisor, strictly past BCH
whenever `t + 1` is not itself a divisor (e.g. `n = 72`, `t = 9`: BCH gives
`≥ 10`, the windowed law gives exactly `12`). -/

/-- **Weight spectrum**: the cardinality of a window coset union is a sum of
divisors of `n` exceeding `t` (the multiset of its coset sizes). -/
theorem IsWindowCosetUnion.card_eq_sum {n t : ℕ} {S : Finset ℕ} (hn : 0 < n)
    (h : IsWindowCosetUnion n t S) :
    ∃ m : Multiset ℕ, (∀ d ∈ m, d ∣ n ∧ t < d) ∧ S.card = m.sum := by
  classical
  obtain ⟨Ps, hpk, hdisj, rfl⟩ := h
  refine ⟨Ps.val.map Finset.card, ?_, ?_⟩
  · intro d hd
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hd
    obtain ⟨d', hd'n, htd', hPd'⟩ := hpk P hP
    have hcd : P.card = d' :=
      hPd'.card_eq (Nat.div_pos (Nat.le_of_dvd hn hd'n) (by omega))
    rw [hcd]
    exact ⟨hd'n, htd'⟩
  · rw [Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)]
    simp only [id_eq]
    exact Finset.sum_eq_multiset_sum Ps Finset.card

/-- **The exact 0/1 minimum-weight bound**: a nonempty window coset union has at
least `d₀` elements, for `d₀` any lower bound on the divisors of `n` exceeding
`t`. -/
theorem IsWindowCosetUnion.le_card_of_nonempty {n t d₀ : ℕ} {S : Finset ℕ}
    (hn : 0 < n) (h : IsWindowCosetUnion n t S) (hne : S.Nonempty)
    (hmin : ∀ d, d ∣ n → t < d → d₀ ≤ d) : d₀ ≤ S.card := by
  obtain ⟨Ps, hpk, hdisj, rfl⟩ := h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨d, hdn, htd, hPd⟩ := hpk P hP
  have hcd : P.card = d :=
    hPd.card_eq (Nat.div_pos (Nat.le_of_dvd hn hdn) (by omega))
  calc d₀ ≤ d := hmin d hdn htd
    _ = P.card := hcd.symm
    _ ≤ (Ps.biUnion id).card :=
        Finset.card_le_card fun y hy => Finset.mem_biUnion.mpr ⟨P, hP, hy⟩

/-- **Sharpness**: every divisor `d₀ ∣ n` with `t < d₀` is achieved as the
weight of a window-`t`-vanishing set — the canonical coset over base `0`. -/
theorem window_min_weight_sharp {L : Type*} [Field L] {n t d₀ : ℕ} (hn : 0 < n)
    (hd₀ : d₀ ∣ n) (htd : t < d₀) {ζ : L} (hζ : IsPrimitiveRoot ζ n) :
    (∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ cosetOf n d₀ 0, ζ ^ (j * e) = 0)
      ∧ (cosetOf n d₀ 0).card = d₀ := by
  have hbase : 0 < n / d₀ := Nat.div_pos (Nat.le_of_dvd hn hd₀) (by omega)
  have hpk : IsPacket n d₀ (cosetOf n d₀ 0) := ⟨0, hbase, rfl⟩
  refine ⟨window_vanishes_of_isWindowCosetUnion hn hζ
    ⟨{cosetOf n d₀ 0}, ?_, ?_, ?_⟩, hpk.card_eq hbase⟩
  · intro P hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨d₀, hd₀, htd, hpk⟩
  · rw [Finset.coe_singleton]
    exact Set.pairwiseDisjoint_singleton _ _
  · rw [Finset.singleton_biUnion]
    rfl

/-- **The 0/1 BCH-window weight spectrum on smooth two-prime domains**: every
window-`t`-vanishing subset has cardinality a sum of divisors of `n = p^a·q^b`
exceeding `t`. -/
theorem window_weight_spectrum_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < p ^ a * q ^ b)
    {t : ℕ} (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0) :
    ∃ m : Multiset ℕ, (∀ d ∈ m, d ∣ p ^ a * q ^ b ∧ t < d) ∧ S.card = m.sum :=
  ((windowed_two_prime hp hq hpq hζ hS htn).mp hwin).card_eq_sum (by omega)

/-- **The exact 0/1 minimum weight on smooth two-prime domains**: a nonempty
window-`t`-vanishing subset has at least `d₀` elements whenever `d₀` lower-bounds
the divisors of `n` exceeding `t`; with `window_min_weight_sharp`, the minimum
0/1-codeword weight of the window code is EXACTLY the least divisor of `n`
exceeding `t` — strictly past the BCH designed-distance bound `t + 1` between
divisors. -/
theorem window_min_weight_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < p ^ a * q ^ b)
    {t : ℕ} (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0)
    (hne : S.Nonempty) {d₀ : ℕ}
    (hmin : ∀ d, d ∣ p ^ a * q ^ b → t < d → d₀ ≤ d) :
    d₀ ≤ S.card :=
  ((windowed_two_prime hp hq hpq hζ hS htn).mp hwin).le_card_of_nonempty
    (by omega) hne hmin

/-- The BCH-beating instance, concretely: at `n = 72 = 2³·3²` with window
`t = 9`, every nonempty window-vanishing 0/1 set has weight `≥ 12` (the least
divisor of `72` exceeding `9`), while the designed-distance bound is only `10`. -/
example {L : Type*} [Field L] [CharZero L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ 3 * 3 ^ 2))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < 2 ^ 3 * 3 ^ 2)
    (hwin : ∀ j, 1 ≤ j → j ≤ 9 → ∑ e ∈ S, ζ ^ (j * e) = 0)
    (hne : S.Nonempty) : 12 ≤ S.card := by
  refine window_min_weight_two_prime Nat.prime_two Nat.prime_three (by norm_num)
    hζ hS (by norm_num) hwin hne ?_
  intro d hdvd hgt
  norm_num at hdvd
  have hle : d ≤ 72 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases d <;> revert hdvd <;> decide

end DeBruijnWindowedLaw

#print axioms DeBruijnWindowedLaw.isPacket_pow_sum_eq_zero
#print axioms DeBruijnWindowedLaw.cosetOf_pow_sum
#print axioms DeBruijnWindowedLaw.isPacket_merge
#print axioms DeBruijnWindowedLaw.window_vanishes_of_isWindowCosetUnion
#print axioms DeBruijnWindowedLaw.isWindowCosetUnion_of_window
#print axioms DeBruijnWindowedLaw.windowed_law
#print axioms DeBruijnWindowedLaw.levelDecomposes_of_dvd_two_prime
#print axioms DeBruijnWindowedLaw.windowed_two_prime
#print axioms DeBruijnWindowedLaw.IsWindowCosetUnion.card_eq_sum
#print axioms DeBruijnWindowedLaw.IsWindowCosetUnion.le_card_of_nonempty
#print axioms DeBruijnWindowedLaw.window_min_weight_sharp
#print axioms DeBruijnWindowedLaw.window_weight_spectrum_two_prime
#print axioms DeBruijnWindowedLaw.window_min_weight_two_prime
