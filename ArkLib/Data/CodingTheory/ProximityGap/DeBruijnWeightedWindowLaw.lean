/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedTwoPrime
import ArkLib.Data.CodingTheory.ProximityGap.WeightedPrimePowerPacket

/-!
# Issue #232 — THE WEIGHTED WINDOWED LAW (O108): the full weight-distribution-side
# window classification at two-prime-smooth moduli

O106 classified the **0/1** window fiber (`DeBruijnWindowedLaw.lean`); O103
classified **ℕ-weighted** vanishing at window length `1`
(`debruijn_weighted_two_prime`).  This file proves their common generalization —
the windowed law at every multiplicity:

* `weighted_windowed_two_prime` — **the headline iff**: for `n = p^a·q^b`, `ζ`
  a primitive `n`-th root of unity in a characteristic-zero field, `w : ℕ → ℕ`,
  and `t < n`:
  `(∀ j, 1 ≤ j ≤ t → Σ_{e<n} w_e·ζ^{je} = 0)  ↔  w` is an ℕ-combination of
  `μ_d`-coset indicators with `d ∣ n`, `d > t` — concretely
  `∃ A, ∀ e < n, w e = Σ_{d ∈ n.divisors, d > t} A d (e % (n/d))`.

Probe-verified before formalization (`scripts/probes/probe_weighted_window_law.py`,
exact ℤ[x]/Φ_n, exit 0): exhaustively over the full multiplicity box `{0,1,2}^12`
(531 441 vectors, 2 024 window-vanishing points, every one decomposing at its
maximal window), the full 0/1 box at `n = 18`, 400k samples of `{0..3}^12`, and
6 000 random-combination converse trials at `n = 12, 18, 20`.

The induction mirrors O106 but is **simpler in the weighted world**: no
disjointness bookkeeping exists anywhere — the merge step is a single mod-index
identity `(e % m) % (m/d') = e % (m/d')`.  Step `t → t+1`: the inherited
combination's `d > t+1` parts kill the `j = t+1` power sum
(`packet_part_pow_sum_eq_zero`, the `u ∤ j` geometric kill); the resonant
`d = t+1` part contributes `(t+1)·Σ_r A_{t+1}(r)·(ζ^{t+1})^r`
(`packet_part_resonant_sum`), extracting a vanishing ℕ-weighted sum at level
`n/(t+1)`; the weighted level classifier (`WeightedLevelDecomposes`, discharged
by O103 at two-prime levels and the O96 prime-power packet theorem through a
ℕ↔ZMod periodicity bridge) rewrites `A_{t+1}` as a prime-packet combination one
level down; and re-indexing folds it into divisors `(t+1)·d' > t+1` of `n`.

As with O106, the induction wrapper is **modulus-agnostic** through the
`WeightedLevelDecomposes` interface.
-/

namespace DeBruijnWeightedWindowLaw

open Finset

variable {L : Type*} [Field L]

/-! ## Power-sum kill and resonance for coset combinations -/

/-- **The `u ∤ j` kill**: a `μ_u`-coset combination annihilates the `j`-th power
sum (each thread carries a full nontrivial geometric sum). -/
lemma packet_part_pow_sum_eq_zero {n u j : ℕ} (hu : 1 < u) (hun : u ∣ n)
    (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n) (huj : ¬ u ∣ j) (A : ℕ → ℕ) :
    ∑ e ∈ Finset.range n, (A (e % (n / u)) : L) * ζ ^ (j * e) = 0 := by
  have hk : 0 < n / u := Nat.div_pos (Nat.le_of_dvd hn hun) (by omega)
  have hsplit : (n / u) * u = n := Nat.div_mul_cancel hun
  simp only [pow_mul]
  rw [show Finset.range n = Finset.range ((n / u) * u) from by rw [hsplit]]
  rw [WeightedThreadSplit.weighted_sum_eq_thread_sum hk (ζ ^ j)
    (fun e => A (e % (n / u)))]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hconst : ∀ e' ∈ Finset.range u,
      (A ((r + (n / u) * e') % (n / u)) : L) * ((ζ ^ j) ^ (n / u)) ^ e'
        = (A r : L) * ((ζ ^ j) ^ (n / u)) ^ e' := by
    intro e' _
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  have hx : (ζ ^ j) ^ (n / u) = ζ ^ (j * (n / u)) := by rw [← pow_mul]
  have hx1 : ζ ^ (j * (n / u)) ≠ 1 := by
    intro h1
    rw [hζ.pow_eq_one_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    refine huj ⟨c, Nat.eq_of_mul_eq_mul_right hk ?_⟩
    calc j * (n / u) = n * c := hc
      _ = u * (n / u) * c := by rw [Nat.mul_div_cancel' hun]
      _ = u * c * (n / u) := by ring
  have hxu : (ζ ^ (j * (n / u))) ^ u = 1 := by
    rw [← pow_mul]
    refine (hζ.pow_eq_one_iff_dvd _).mpr ⟨j, ?_⟩
    calc j * (n / u) * u = j * (n / u * u) := by ring
      _ = n * j := by rw [hsplit]; ring
  have hgeom : ∑ e' ∈ Finset.range u, (ζ ^ (j * (n / u))) ^ e' = 0 := by
    rw [geom_sum_eq hx1, hxu, sub_self, zero_div]
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, hx, hgeom, mul_zero, mul_zero]

/-- **The resonant sum**: at `j = u`, a `μ_u`-coset combination contributes `u`
times its base sum against the level-`n/u` root `ζ^u`. -/
lemma packet_part_resonant_sum {n u : ℕ} (hu : 0 < u) (hun : u ∣ n)
    (hn : 0 < n) {ζ : L} (hζ : ζ ^ n = 1) (A : ℕ → ℕ) :
    ∑ e ∈ Finset.range n, (A (e % (n / u)) : L) * ζ ^ (u * e)
      = (u : L) * ∑ r ∈ Finset.range (n / u), (A r : L) * (ζ ^ u) ^ r := by
  have hk : 0 < n / u := Nat.div_pos (Nat.le_of_dvd hn hun) hu
  have hsplit : (n / u) * u = n := Nat.div_mul_cancel hun
  simp only [pow_mul]
  rw [show Finset.range n = Finset.range ((n / u) * u) from by rw [hsplit]]
  rw [WeightedThreadSplit.weighted_sum_eq_thread_sum hk (ζ ^ u)
    (fun e => A (e % (n / u)))]
  have hone : (ζ ^ u) ^ (n / u) = 1 := by
    rw [← pow_mul, Nat.mul_div_cancel' hun]
    exact hζ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hconst : ∀ e' ∈ Finset.range u,
      (A ((r + (n / u) * e') % (n / u)) : L) * ((ζ ^ u) ^ (n / u)) ^ e'
        = (A r : L) := by
    intro e' _
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr),
      hone, one_pow, mul_one]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-! ## The combination predicate and the easy direction -/

/-- `w` is an **ℕ-combination of `μ_d`-coset indicators with `d ∣ n`, `d > t`**
on `[0, n)`. -/
def IsWeightedWindowCombination (n t : ℕ) (w : ℕ → ℕ) : Prop :=
  ∃ A : ℕ → ℕ → ℕ, ∀ e < n,
    w e = ∑ d ∈ n.divisors.filter (t < ·), A d (e % (n / d))

/-- **⟸ of the weighted windowed law**: a `d > t` combination kills the whole
window `1 ≤ j ≤ t`. -/
theorem window_vanishes_of_combination [CharZero L] {n t : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) {w : ℕ → ℕ}
    (h : IsWeightedWindowCombination n t w) :
    ∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e) = 0 := by
  intro j hj1 hjt
  obtain ⟨A, hA⟩ := h
  have hswap : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e)
      = ∑ d ∈ n.divisors.filter (t < ·),
          ∑ e ∈ Finset.range n, (A d (e % (n / d)) : L) * ζ ^ (j * e) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hA e (Finset.mem_range.mp he)]
    push_cast
    rw [Finset.sum_mul]
  rw [hswap]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
  have hdn : d ∣ n := (Nat.mem_divisors.mp hmem).1
  refine packet_part_pow_sum_eq_zero (by omega) hdn hn hζ ?_ (A d)
  intro hdj
  have := Nat.le_of_dvd (by omega) hdj
  omega

/-! ## The weighted level-classification interface -/

/-- Vanishing ℕ-weighted sums at level `m` are prime-packet combinations. -/
def WeightedLevelDecomposes (L : Type*) [Field L] (m : ℕ) : Prop :=
  ∀ ξ : L, IsPrimitiveRoot ξ m → ∀ v : ℕ → ℕ,
    (∑ r ∈ Finset.range m, (v r : L) * ξ ^ r = 0) →
    ∃ C : ℕ → ℕ → ℕ, ∀ r < m,
      v r = ∑ d ∈ m.primeFactors, C d (r % (m / d))

/-! ## The induction step -/

/-- **One upgrade step**: a window-`t` combination plus the `(t+1)`-st power sum
upgrades to a window-`(t+1)` combination, given weighted level decomposition at
`n/(t+1)`. -/
private lemma window_step [CharZero L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) {t : ℕ} (htn : t + 1 < n) (hdvd : t + 1 ∣ n)
    (hWLD : WeightedLevelDecomposes L (n / (t + 1)))
    {w : ℕ → ℕ} (hprev : IsWeightedWindowCombination n t w)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ ((t + 1) * e) = 0) :
    IsWeightedWindowCombination n (t + 1) w := by
  classical
  obtain ⟨A, hA⟩ := hprev
  have hnpos : 0 < n := by omega
  have hτm : (t + 1) * (n / (t + 1)) = n := Nat.mul_div_cancel' hdvd
  have hmpos : 0 < n / (t + 1) :=
    Nat.div_pos (Nat.le_of_dvd hnpos hdvd) (Nat.succ_pos t)
  have hτmem : t + 1 ∈ n.divisors.filter (t < ·) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hnpos.ne'⟩, by omega⟩
  have hτnot : t + 1 ∉ n.divisors.filter (t + 1 < ·) := by
    intro hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (by omega)
  -- the filter at t splits as {t+1} ∪ filter at t+1
  have hfilter : n.divisors.filter (t < ·)
      = insert (t + 1) (n.divisors.filter (t + 1 < ·)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, hne⟩, htd⟩
      rcases Nat.lt_or_ge (t + 1) d with h | h
      · exact Or.inr ⟨⟨hdn, hne⟩, h⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨⟨hdn, hne⟩, htd⟩)
      · exact ⟨(Nat.mem_divisors.mp (Finset.mem_filter.mp hτmem).1), by omega⟩
      · exact ⟨⟨hdn, hne⟩, by omega⟩
  -- extract the resonant base sum at level n/(t+1)
  have hswap : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ ((t + 1) * e)
      = ∑ d ∈ n.divisors.filter (t < ·),
          ∑ e ∈ Finset.range n, (A d (e % (n / d)) : L) * ζ ^ ((t + 1) * e) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hA e (Finset.mem_range.mp he)]
    push_cast
    rw [Finset.sum_mul]
  have hkill : ∀ d ∈ n.divisors.filter (t + 1 < ·),
      ∑ e ∈ Finset.range n, (A d (e % (n / d)) : L) * ζ ^ ((t + 1) * e) = 0 := by
    intro d hd
    obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hmem).1
    refine packet_part_pow_sum_eq_zero (by omega) hdn hnpos hζ ?_ (A d)
    intro hdj
    have := Nat.le_of_dvd (Nat.succ_pos t) hdj
    omega
  have hres : (((t + 1 : ℕ)) : L)
      * ∑ r ∈ Finset.range (n / (t + 1)),
          (A (t + 1) r : L) * (ζ ^ (t + 1)) ^ r = 0 := by
    have h0 := hsum
    rw [hswap, hfilter, Finset.sum_insert hτnot,
      Finset.sum_eq_zero hkill, add_zero,
      packet_part_resonant_sum (Nat.succ_pos t) hdvd hnpos hζ.pow_eq_one
        (A (t + 1))] at h0
    exact h0
  have hbase : ∑ r ∈ Finset.range (n / (t + 1)),
      (A (t + 1) r : L) * (ζ ^ (t + 1)) ^ r = 0 := by
    rcases mul_eq_zero.mp hres with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero t))
    · exact h
  -- classify the resonant coefficients one level down
  have hξ : IsPrimitiveRoot (ζ ^ (t + 1)) (n / (t + 1)) := hζ.pow hnpos hτm.symm
  obtain ⟨C, hC⟩ := hWLD _ hξ _ hbase
  -- fold the level-(n/(t+1)) packets into divisors (t+1)·d' of n
  refine ⟨fun d r =>
    (if t + 1 < d then A d r else 0)
      + ∑ d' ∈ (n / (t + 1)).primeFactors.filter (fun d' => (t + 1) * d' = d),
          C d' r, ?_⟩
  intro e he
  have hAe := hA e he
  rw [hfilter, Finset.sum_insert hτnot] at hAe
  -- the t+1 term re-expands through C
  have hCval : A (t + 1) (e % (n / (t + 1)))
      = ∑ d' ∈ (n / (t + 1)).primeFactors,
          C d' (e % (n / ((t + 1) * d'))) := by
    rw [hC _ (Nat.mod_lt _ hmpos)]
    refine Finset.sum_congr rfl fun d' hd' => ?_
    have hd'm : d' ∣ n / (t + 1) := Nat.dvd_of_mem_primeFactors hd'
    have hmm : n / (t + 1) / d' = n / ((t + 1) * d') := Nat.div_div_eq_div_mul n _ _
    rw [← hmm, Nat.mod_mod_of_dvd e (Nat.div_dvd_of_dvd hd'm)]
  rw [hCval] at hAe
  rw [hAe]
  -- expand the new coefficient sum
  rw [Finset.sum_add_distrib]
  have hfirst : ∑ d ∈ n.divisors.filter (t + 1 < ·),
      (if t + 1 < d then A d (e % (n / d)) else 0)
        = ∑ d ∈ n.divisors.filter (t + 1 < ·), A d (e % (n / d)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [if_pos (Finset.mem_filter.mp hd).2]
  have hsecond : ∑ d ∈ n.divisors.filter (t + 1 < ·),
      ∑ d' ∈ (n / (t + 1)).primeFactors.filter (fun d' => (t + 1) * d' = d),
          C d' (e % (n / d))
        = ∑ d' ∈ (n / (t + 1)).primeFactors,
            C d' (e % (n / ((t + 1) * d'))) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun d' => (t + 1) * d')
      (fun d' hd' => ?_) (fun d' => C d' (e % (n / ((t + 1) * d'))))]
    · refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun d' hd' => ?_
      rw [(Finset.mem_filter.mp hd').2]
    · -- (t+1)·d' lands in the t+1 filter
      have hd'p := Nat.prime_of_mem_primeFactors hd'
      have hd'm : d' ∣ n / (t + 1) := Nat.dvd_of_mem_primeFactors hd'
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hnpos.ne'⟩, ?_⟩
      · calc (t + 1) * d' ∣ (t + 1) * (n / (t + 1)) := mul_dvd_mul_left _ hd'm
          _ = n := hτm
      · exact (Nat.lt_mul_iff_one_lt_right (Nat.succ_pos t)).mpr hd'p.one_lt
  rw [hfirst, hsecond]
  ring

/-! ## The induction wrapper and the modulus-agnostic law -/

/-- **The forward direction**, by induction on the window length. -/
theorem combination_of_window [CharZero L] {n : ℕ}
    (hWLD : ∀ m, m ∣ n → WeightedLevelDecomposes L m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℕ) :
    ∀ t, t < n → (∀ j, 1 ≤ j → j ≤ t →
      ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e) = 0) →
      IsWeightedWindowCombination n t w := by
  intro t
  induction t with
  | zero =>
    intro htn _
    refine ⟨fun d r => if d = 1 then w r else 0, fun e he => ?_⟩
    have h1mem : 1 ∈ n.divisors.filter (0 < ·) :=
      Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), one_pos⟩
    rw [Finset.sum_eq_single_of_mem 1 h1mem]
    · dsimp only
      rw [if_pos rfl, Nat.div_one, Nat.mod_eq_of_lt he]
    · intro d _ hne
      dsimp only
      rw [if_neg hne]
  | succ t IH =>
    intro htn hwin
    have hprev := IH (by omega) fun j h1 h2 => hwin j h1 (by omega)
    by_cases hdvd : (t + 1) ∣ n
    · exact window_step hζ htn hdvd
        (hWLD _ ⟨t + 1, (Nat.div_mul_cancel hdvd).symm⟩) hprev
        (hwin _ (Nat.succ_pos t) le_rfl)
    · -- t+1 is not a divisor: the filters coincide
      obtain ⟨A, hA⟩ := hprev
      refine ⟨A, fun e he => ?_⟩
      have hfeq : n.divisors.filter (t + 1 < ·) = n.divisors.filter (t < ·) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdn, hne⟩, htd⟩
          exact ⟨⟨hdn, hne⟩, by omega⟩
        · rintro ⟨⟨hdn, hne⟩, htd⟩
          refine ⟨⟨hdn, hne⟩, ?_⟩
          rcases Nat.lt_or_ge (t + 1) d with h | h
          · exact h
          · have hde : d = t + 1 := by omega
            exact absurd (hde ▸ hdn) hdvd
      rw [hfeq]
      exact hA e he

/-- **THE WEIGHTED WINDOWED LAW** (modulus-agnostic iff). -/
theorem weighted_windowed_law [CharZero L] {n : ℕ}
    (hWLD : ∀ m, m ∣ n → WeightedLevelDecomposes L m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℕ) {t : ℕ} (htn : t < n) :
    (∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e) = 0) ↔
      IsWeightedWindowCombination n t w :=
  ⟨combination_of_window hWLD hζ w t htn,
    fun h => window_vanishes_of_combination (by omega) hζ h⟩

/-! ## Discharging the weighted level interface at two-prime-smooth moduli -/

/-- The prime-power weighted level: O96's periodicity theorem pulled through a
ℕ↔ZMod bridge into combination form. -/
lemma weightedLevel_prime_pow [CharZero L] {p c : ℕ} (hp : p.Prime)
    {ξ : L} (hξ : IsPrimitiveRoot ξ (p ^ (c + 1))) (v : ℕ → ℕ)
    (hsum : ∑ r ∈ Finset.range (p ^ (c + 1)), (v r : L) * ξ ^ r = 0) :
    ∀ r < p ^ (c + 1), v r = v (r % p ^ c) := by
  classical
  have hn : 0 < p ^ (c + 1) := pow_pos hp.pos _
  haveI : NeZero (p ^ (c + 1)) := ⟨hn.ne'⟩
  -- bridge the sum to ZMod indexing
  have hzsum : ∑ e : ZMod (p ^ (c + 1)), ((v e.val : ℕ) : L) * ξ ^ e.val = 0 := by
    have hbij : ∑ e : ZMod (p ^ (c + 1)), ((v e.val : ℕ) : L) * ξ ^ e.val
        = ∑ r ∈ Finset.range (p ^ (c + 1)), (v r : L) * ξ ^ r := by
      refine Finset.sum_nbij' (i := fun e : ZMod (p ^ (c + 1)) => e.val)
        (j := fun r : ℕ => (r : ZMod (p ^ (c + 1)))) ?_ ?_ ?_ ?_ ?_
      · intro e _
        exact Finset.mem_range.mpr (ZMod.val_lt e)
      · intro r _
        exact Finset.mem_univ _
      · intro e _
        exact ZMod.natCast_rightInverse e
      · intro r hr
        exact ZMod.val_cast_of_lt (Finset.mem_range.mp hr)
      · intro e _
        rfl
    rw [hbij]
    exact hsum
  have hper := WeightedPrimePowerPacket.weight_replicated_of_vanishing hp hξ
    (w := fun z => v z.val) hzsum
  -- one ℕ-step of the periodicity
  have hstep : ∀ y, y + p ^ c < p ^ (c + 1) → v (y + p ^ c) = v y := by
    intro y hy
    have hcast : ((y : ZMod (p ^ (c + 1))) + ((p ^ c : ℕ) : ZMod (p ^ (c + 1))))
        = ((y + p ^ c : ℕ) : ZMod (p ^ (c + 1))) := by push_cast; ring
    have h := hper (y : ZMod (p ^ (c + 1)))
    dsimp only at h
    rw [hcast] at h
    rw [ZMod.val_cast_of_lt hy, ZMod.val_cast_of_lt (by omega : y < p ^ (c + 1))]
      at h
    exact h
  -- iterate
  have hiter : ∀ k x, x < p ^ c → x + k * p ^ c < p ^ (c + 1) →
      v (x + k * p ^ c) = v x := by
    intro k
    induction k with
    | zero => intro x _ _; simp
    | succ k IHk =>
      intro x hx hlt
      have h1 : x + (k + 1) * p ^ c = (x + k * p ^ c) + p ^ c := by ring
      have h2 : (x + k * p ^ c) + p ^ c < p ^ (c + 1) := by rw [← h1]; exact hlt
      rw [h1, hstep _ h2]
      exact IHk x hx (by omega)
  intro r hr
  have hsplitr : r % p ^ c + r / p ^ c * p ^ c = r := Nat.mod_add_div' r (p ^ c)
  calc v r = v (r % p ^ c + r / p ^ c * p ^ c) := by rw [hsplitr]
    _ = v (r % p ^ c) := hiter _ _ (Nat.mod_lt _ (pow_pos hp.pos c))
        (by rw [hsplitr]; exact hr)

/-- **Every divisor level of a two-prime-smooth modulus weighted-level-decomposes**:
O103 at two-prime levels, O96 at prime-power levels, trivially at level 1. -/
theorem weightedLevelDecomposes_of_dvd_two_prime [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {m : ℕ} (hm : m ∣ p ^ a * q ^ b) (hm0 : 0 < m) :
    WeightedLevelDecomposes L m := by
  intro ξ hξ v hsum
  classical
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hm
  obtain ⟨a', _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm₁
  obtain ⟨b', _, rfl⟩ := (Nat.dvd_prime_pow hq).mp hm₂
  rcases Nat.eq_zero_or_pos a' with rfl | hapos
  · rcases Nat.eq_zero_or_pos b' with rfl | hbpos
    · -- level 1: the single weight is zero
      refine ⟨fun _ _ => 0, fun r hr => ?_⟩
      simp only [pow_zero, one_mul] at hr hsum ⊢
      interval_cases r
      have h0 : v 0 = 0 := by
        have h := hsum
        simp at h
        exact h
      simp [h0]
    · -- level q^b'
      obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hbpos.ne'
      rw [pow_zero, one_mul] at hξ hsum ⊢
      have hper := weightedLevel_prime_pow hq hξ v hsum
      refine ⟨fun _ r => v r, fun r hr => ?_⟩
      have hpf : (q ^ (c + 1)).primeFactors = {q} := by
        rw [Nat.primeFactors_pow _ (Nat.succ_ne_zero c), Nat.Prime.primeFactors hq]
      rw [hpf, Finset.sum_singleton]
      have hdiv : q ^ (c + 1) / q = q ^ c := by
        rw [pow_succ']
        exact Nat.mul_div_cancel_left _ hq.pos
      rw [hdiv]
      exact hper r hr
  · rcases Nat.eq_zero_or_pos b' with rfl | hbpos
    · -- level p^a'
      obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hapos.ne'
      rw [pow_zero, mul_one] at hξ hsum ⊢
      have hper := weightedLevel_prime_pow hp hξ v hsum
      refine ⟨fun _ r => v r, fun r hr => ?_⟩
      have hpf : (p ^ (c + 1)).primeFactors = {p} := by
        rw [Nat.primeFactors_pow _ (Nat.succ_ne_zero c), Nat.Prime.primeFactors hp]
      rw [hpf, Finset.sum_singleton]
      have hdiv : p ^ (c + 1) / p = p ^ c := by
        rw [pow_succ']
        exact Nat.mul_div_cancel_left _ hp.pos
      rw [hdiv]
      exact hper r hr
    · -- genuine two-prime level: O103
      obtain ⟨A, B, hAB⟩ :=
        (DeBruijnWeightedTwoPrime.debruijn_weighted_two_prime hp hq hpq hapos hbpos
          hξ v).mp hsum
      have hpf : (p ^ a' * q ^ b').primeFactors = {p, q} := by
        rw [Nat.primeFactors_mul (pow_pos hp.pos a').ne' (pow_pos hq.pos b').ne',
          Nat.primeFactors_pow _ hapos.ne', Nat.primeFactors_pow _ hbpos.ne',
          Nat.Prime.primeFactors hp, Nat.Prime.primeFactors hq]
        rfl
      have hdivp : p ^ a' * q ^ b' / p = p ^ (a' - 1) * q ^ b' := by
        have h2 : p * p ^ (a' - 1) = p ^ a' := by
          rw [← pow_succ']
          congr 1
          omega
        have hform : p ^ a' * q ^ b' = p * (p ^ (a' - 1) * q ^ b') := by
          rw [← h2]; ring
        rw [hform, Nat.mul_div_cancel_left _ hp.pos]
      have hdivq : p ^ a' * q ^ b' / q = p ^ a' * q ^ (b' - 1) := by
        have h2 : q * q ^ (b' - 1) = q ^ b' := by
          rw [← pow_succ']
          congr 1
          omega
        have hform : p ^ a' * q ^ b' = q * (p ^ a' * q ^ (b' - 1)) := by
          rw [← h2]; ring
        rw [hform, Nat.mul_div_cancel_left _ hq.pos]
      refine ⟨fun d r => if d = p then A r else B r, fun r hr => ?_⟩
      rw [hpf, Finset.sum_pair hpq]
      dsimp only
      rw [if_pos rfl, if_neg (Ne.symm hpq), hdivp, hdivq]
      exact hAB r hr

/-! ## The headline -/

/-- **THE WEIGHTED WINDOWED TWO-PRIME LAW** (O108): for `n = p^a·q^b`, `ζ` a
primitive `n`-th root of unity in characteristic zero, `w : ℕ → ℕ`, `t < n`:
the power-sum window `1 ≤ j ≤ t` vanishes **iff** `w` is an ℕ-combination of
`μ_d`-coset indicators with `d ∣ n`, `d > t`.  Common generalization of O103
(`t = 1`) and O106 (0/1 weights); probe-verified exhaustively before
formalization. -/
theorem weighted_windowed_two_prime [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    {t : ℕ} (htn : t < p ^ a * q ^ b) :
    (∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ (j * e) = 0) ↔
      IsWeightedWindowCombination (p ^ a * q ^ b) t w :=
  weighted_windowed_law
    (fun _ hm => weightedLevelDecomposes_of_dvd_two_prime hp hq hpq hm
      (Nat.pos_of_dvd_of_pos hm
        (Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b))))
    hζ w htn

end DeBruijnWeightedWindowLaw

#print axioms DeBruijnWeightedWindowLaw.packet_part_pow_sum_eq_zero
#print axioms DeBruijnWeightedWindowLaw.packet_part_resonant_sum
#print axioms DeBruijnWeightedWindowLaw.window_vanishes_of_combination
#print axioms DeBruijnWeightedWindowLaw.combination_of_window
#print axioms DeBruijnWeightedWindowLaw.weighted_windowed_law
#print axioms DeBruijnWeightedWindowLaw.weightedLevel_prime_pow
#print axioms DeBruijnWeightedWindowLaw.weightedLevelDecomposes_of_dvd_two_prime
#print axioms DeBruijnWeightedWindowLaw.weighted_windowed_two_prime
