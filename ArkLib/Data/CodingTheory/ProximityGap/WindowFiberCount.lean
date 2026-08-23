/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWindowedLaw

/-!
# Issue #232 — the window fiber-count law: the block-trace bijection (O111 Lean layer)

O106 classified the window-`t` fiber as `IsWindowCosetUnion n t` (disjoint unions
of canonical rotated `μ_d`-cosets, `d ∣ n`, `d > t`).  O111 pinned the fiber-count
law `F_n(t) ≅ F_m(t)^(n/m)` at probe level with the exact block-trace bijection.
This file lands its Lean substance — pure coset combinatorics, no roots of unity:

* `traceBlock g c S = {e/g : e ∈ S, e ≡ c (mod g)}` — the block trace;
* `traceBlock_cosetOf` — **the key structural lemma**: the trace of a canonical
  `μ_d`-coset (level `n`) on a block is empty or a canonical
  `μ_{gcd(d,m)}`-coset at level `m` (`g = n/m`), proven through the linear
  congruence `g·e' ≡ r − c (mod n/d)` whose solution classes have modulus
  `(n/d)/gcd(g, n/d) = m/gcd(d,m)` — the divisor identity
  `(n/d)·gcd(d,m) = m·gcd(n/m, n/d)` collapses to `gcd_mul_left` twice;
* `isWindowCosetUnion_iff_traceBlocks` — **the headline iff** under the abstract
  interface `(H)`: `m ∣ n` and every divisor `d ∣ n` with `d > t` has
  `gcd(d, m) > t` (satisfied by `m = lcm(Dmin)` — divisibility-minimal divisors
  exceeding `t` all divide `m`): `S` is a window coset union at `n` **iff**
  every block trace is one at `m`.  This is the set-level bijection behind
  `|F_n(t)| = |F_m(t)|^(n/m)` (O70's exact law, probe-verified 25/25).
-/

namespace DeBruijnWindowedLaw

open Finset DeBruijnTwoPrimeAssembly

/-! ## The block trace and lift -/

/-- The trace of `S` on block `c` mod `g`: `{e/g : e ∈ S, e % g = c}`. -/
def traceBlock (g c : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (S.filter fun e => e % g = c).image (· / g)

/-- The lift of a level-`m` set into block `c`: `{c + g·e' : e' ∈ T}`. -/
def liftBlock (g c : ℕ) (T : Finset ℕ) : Finset ℕ :=
  T.image fun e' => c + g * e'

lemma mem_traceBlock {g c : ℕ} (hc : c < g) {S : Finset ℕ} {e' : ℕ} :
    e' ∈ traceBlock g c S ↔ c + g * e' ∈ S := by
  constructor
  · rintro he'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨heS, hec⟩ := Finset.mem_filter.mp he
    rwa [← hec, Nat.mod_add_div e g]
  · intro hmem
    refine Finset.mem_image.mpr ⟨c + g * e', Finset.mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    · rw [Nat.add_mul_div_left _ _ (by omega : 0 < g), Nat.div_eq_of_lt hc,
        zero_add]

lemma mem_liftBlock {g c : ℕ} {T : Finset ℕ} {e : ℕ} :
    e ∈ liftBlock g c T ↔ ∃ e' ∈ T, e = c + g * e' := by
  simp only [liftBlock, Finset.mem_image]
  exact ⟨fun ⟨e', h, he⟩ => ⟨e', h, he.symm⟩, fun ⟨e', h, he⟩ => ⟨e', h, he.symm⟩⟩

/-! ## Canonical cosets as residue classes -/

/-- A canonical coset is exactly a full residue class inside `[0, n)`. -/
lemma mem_cosetOf_iff_mod {n d r e : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (hr : r < n / d) :
    e ∈ cosetOf n d r ↔ e < n ∧ e % (n / d) = r := by
  have hτd : n / d * d = n := Nat.div_mul_cancel hd
  have hτ0 : 0 < n / d := by
    rcases Nat.eq_zero_or_pos (n / d) with h | h
    · rw [h, zero_mul] at hτd
      omega
    · exact h
  constructor
  · intro he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
    have hs' : s < d := Finset.mem_range.mp hs
    constructor
    · calc r + s * (n / d) < n / d + s * (n / d) := by omega
        _ = (s + 1) * (n / d) := by ring
        _ ≤ d * (n / d) := Nat.mul_le_mul_right _ (by omega)
        _ = n := by rw [mul_comm]; exact hτd
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  · rintro ⟨hen, her⟩
    refine Finset.mem_image.mpr ⟨e / (n / d), Finset.mem_range.mpr ?_, ?_⟩
    · refine Nat.div_lt_of_lt_mul ?_
      rw [hτd]
      exact hen
    · conv_rhs => rw [← Nat.mod_add_div e (n / d), her, mul_comm]

/-! ## The congruence structure of a block trace -/

/-- Trace exponents of one residue class are congruent mod `(n/d)/gcd(g, n/d)`. -/
lemma trace_congr {g τ c r x y : ℕ} (hg : 0 < g)
    (hx : (c + g * x) % τ = r) (hy : (c + g * y) % τ = r) :
    x % (τ / Nat.gcd g τ) = y % (τ / Nat.gcd g τ) := by
  have h0 : 0 < Nat.gcd g τ := Nat.gcd_pos_of_pos_left _ hg
  have hgg : Nat.gcd g τ * (g / Nat.gcd g τ) = g :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hgτ : Nat.gcd g τ * (τ / Nat.gcd g τ) = τ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hxy : c + g * x ≡ c + g * y [MOD τ] := by
    unfold Nat.ModEq
    rw [hx, hy]
  have hgxy : g * x ≡ g * y [MOD τ] := Nat.ModEq.add_left_cancel' c hxy
  have hfac : Nat.gcd g τ * ((g / Nat.gcd g τ) * x)
      ≡ Nat.gcd g τ * ((g / Nat.gcd g τ) * y)
      [MOD Nat.gcd g τ * (τ / Nat.gcd g τ)] := by
    rw [← mul_assoc, ← mul_assoc, hgg, hgτ]
    exact hgxy
  have hcanc : (g / Nat.gcd g τ) * x ≡ (g / Nat.gcd g τ) * y
      [MOD τ / Nat.gcd g τ] :=
    Nat.ModEq.mul_left_cancel' (by omega) hfac
  have h0' : 0 < Nat.gcd τ g := by rwa [Nat.gcd_comm]
  have hco := Nat.coprime_div_gcd_div_gcd h0'
  rw [Nat.gcd_comm τ g] at hco
  exact Nat.ModEq.cancel_left_of_coprime hco hcanc

/-- Conversely, congruence mod `τ/gcd(g,τ)` transports trace membership. -/
lemma trace_congr_mem {g τ c r x y : ℕ}
    (hx : (c + g * x) % τ = r)
    (hxy : x % (τ / Nat.gcd g τ) = y % (τ / Nat.gcd g τ)) :
    (c + g * y) % τ = r := by
  have hmodeq : x ≡ y [MOD τ / Nat.gcd g τ] := hxy
  have hgxy : g * x ≡ g * y [MOD g * (τ / Nat.gcd g τ)] :=
    Nat.ModEq.mul_left' g hmodeq
  have hτdvd : τ ∣ g * (τ / Nat.gcd g τ) := by
    have h1 : τ = Nat.gcd g τ * (τ / Nat.gcd g τ) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
    calc τ = Nat.gcd g τ * (τ / Nat.gcd g τ) := h1
      _ ∣ g * (τ / Nat.gcd g τ) :=
        Nat.mul_dvd_mul_right (Nat.gcd_dvd_left _ _) _
  have hgxyτ : g * x ≡ g * y [MOD τ] := Nat.ModEq.of_dvd hτdvd hgxy
  have : c + g * y ≡ c + g * x [MOD τ] := (Nat.ModEq.add_left c hgxyτ).symm
  unfold Nat.ModEq at this
  rw [this, hx]

/-! ## The divisor identity -/

/-- `(n/d)·gcd(d,m) = m·gcd(n/m, n/d)` for `d, m ∣ n`: both sides are
`gcd(n, (n/d)·m)` by `gcd_mul_left`. -/
lemma div_gcd_identity {n d m : ℕ} (hd : d ∣ n) (hm : m ∣ n) :
    n / d * Nat.gcd d m = m * Nat.gcd (n / m) (n / d) := by
  calc n / d * Nat.gcd d m
      = Nat.gcd (n / d * d) (n / d * m) := (Nat.gcd_mul_left _ _ _).symm
    _ = Nat.gcd n (n / d * m) := by rw [Nat.div_mul_cancel hd]
    _ = Nat.gcd (m * (n / m)) (m * (n / d)) := by
        rw [Nat.mul_div_cancel' hm, mul_comm (n / d) m]
    _ = m * Nat.gcd (n / m) (n / d) := Nat.gcd_mul_left _ _ _

/-- The trace modulus is the level-`m` step: `(n/d)/gcd(n/m, n/d) = m/gcd(d,m)`,
in product form `σ·gcd(d,m) = m`. -/
lemma trace_step_eq {n d m : ℕ} (hn : 0 < n) (hd : d ∣ n) (hm : m ∣ n)
    (hd0 : 0 < d) (hm0 : 0 < m) :
    n / d / Nat.gcd (n / m) (n / d) * Nat.gcd d m = m := by
  have hτ0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hd) hd0
  have hg0 : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hm) hm0
  have hh0 : 0 < Nat.gcd (n / m) (n / d) := Nat.gcd_pos_of_pos_left _ hg0
  have hhdvd : Nat.gcd (n / m) (n / d) ∣ n / d := Nat.gcd_dvd_right _ _
  have key := div_gcd_identity hd hm
  have hfac : n / d = n / d / Nat.gcd (n / m) (n / d) * Nat.gcd (n / m) (n / d) :=
    (Nat.div_mul_cancel hhdvd).symm
  have key2 : n / d / Nat.gcd (n / m) (n / d) * Nat.gcd (n / m) (n / d)
      * Nat.gcd d m = m * Nat.gcd (n / m) (n / d) := by
    rw [← hfac]
    exact key
  have key3 : n / d / Nat.gcd (n / m) (n / d) * Nat.gcd d m
      * Nat.gcd (n / m) (n / d) = m * Nat.gcd (n / m) (n / d) := by
    rw [mul_right_comm]
    exact key2
  exact Nat.eq_of_mul_eq_mul_right hh0 key3

/-! ## The key structural lemma: coset traces are cosets -/

/-- **The block trace of a canonical coset** is empty or a canonical
`μ_{gcd(d,m)}`-coset at level `m`. -/
lemma traceBlock_cosetOf {n m d r c : ℕ} (hn : 0 < n) (hm : m ∣ n) (hm0 : 0 < m)
    (hd : d ∣ n) (hd0 : 0 < d) (hr : r < n / d) (hc : c < n / m) :
    traceBlock (n / m) c (cosetOf n d r) = ∅ ∨
    ∃ ρ < m / Nat.gcd d m,
      traceBlock (n / m) c (cosetOf n d r) = cosetOf m (Nat.gcd d m) ρ := by
  set g := n / m with hgdef
  set τ := n / d with hτdef
  set σ := τ / Nat.gcd g τ with hσdef
  have hg0 : 0 < g := Nat.div_pos (Nat.le_of_dvd hn hm) hm0
  have hτ0 : 0 < τ := Nat.div_pos (Nat.le_of_dvd hn hd) hd0
  have hgm : g * m = n := Nat.div_mul_cancel hm
  have hστ : σ * Nat.gcd d m = m := trace_step_eq hn hd hm hd0 hm0
  have hG0 : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_left _ hd0
  have hσ0 : 0 < σ := by
    rcases Nat.eq_zero_or_pos σ with h | h
    · rw [h, zero_mul] at hστ
      omega
    · exact h
  have hσm : σ = m / Nat.gcd d m :=
    (Nat.div_eq_of_eq_mul_left hG0 hστ.symm).symm
  have hGm : Nat.gcd d m ∣ m := Nat.gcd_dvd_right _ _
  -- membership characterization of the trace
  have hmem : ∀ e' : ℕ, e' ∈ traceBlock g c (cosetOf n d r)
      ↔ e' < m ∧ (c + g * e') % τ = r := by
    intro e'
    rw [mem_traceBlock hc, mem_cosetOf_iff_mod hn hd hr]
    constructor
    · rintro ⟨hlt, hmod⟩
      refine ⟨?_, hmod⟩
      by_contra hge
      have : g * m ≤ g * e' := Nat.mul_le_mul_left _ (by omega)
      omega
    · rintro ⟨hlt, hmod⟩
      refine ⟨?_, hmod⟩
      calc c + g * e' < g + g * e' := by omega
        _ = g * (e' + 1) := by ring
        _ ≤ g * m := Nat.mul_le_mul_left _ (by omega)
        _ = n := hgm
  by_cases hne : (traceBlock g c (cosetOf n d r)).Nonempty
  · right
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨hx₀m, hx₀mod⟩ := (hmem x₀).mp hx₀
    have hρlt : x₀ % σ < m / Nat.gcd d m := by
      rw [← hσm]
      exact Nat.mod_lt _ hσ0
    refine ⟨x₀ % σ, hρlt, ?_⟩
    ext e'
    rw [hmem e', mem_cosetOf_iff_mod hm0 hGm hρlt]
    constructor
    · rintro ⟨he'm, he'mod⟩
      refine ⟨he'm, ?_⟩
      rw [← hσm]
      exact trace_congr hg0 he'mod hx₀mod
    · rintro ⟨he'm, he'mod⟩
      rw [← hσm] at he'mod
      exact ⟨he'm, trace_congr_mem hx₀mod he'mod.symm⟩
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hne

/-! ## The forward direction: traces of window coset unions decompose -/

/-- Traces commute with disjoint unions. -/
lemma traceBlock_biUnion {g c : ℕ} (hc : c < g) (Ps : Finset (Finset ℕ)) :
    traceBlock g c (Ps.biUnion id) = Ps.biUnion (fun P => traceBlock g c P) := by
  ext e'
  rw [mem_traceBlock hc, Finset.mem_biUnion]
  simp only [Finset.mem_biUnion, id]
  constructor
  · rintro ⟨P, hP, hmem⟩
    exact ⟨P, hP, (mem_traceBlock hc).mpr hmem⟩
  · rintro ⟨P, hP, hmem⟩
    exact ⟨P, hP, (mem_traceBlock hc).mp hmem⟩

/-- Traces of disjoint sets are disjoint. -/
lemma disjoint_traceBlock {g c : ℕ} (hc : c < g) {P Q : Finset ℕ}
    (h : Disjoint P Q) : Disjoint (traceBlock g c P) (traceBlock g c Q) := by
  rw [Finset.disjoint_left] at h ⊢
  intro e' heP heQ
  exact h ((mem_traceBlock hc).mp heP) ((mem_traceBlock hc).mp heQ)

/-- **Forward**: every block trace of a window coset union at level `n` is a
window coset union at level `m`, under the divisor-gcd interface `(H)`. -/
theorem isWindowCosetUnion_traceBlock {n m t : ℕ} (hn : 0 < n) (hm : m ∣ n)
    (hm0 : 0 < m) (hH : ∀ d, d ∣ n → t < d → t < Nat.gcd d m)
    {S : Finset ℕ} (h : IsWindowCosetUnion n t S) {c : ℕ} (hc : c < n / m) :
    IsWindowCosetUnion m t (traceBlock (n / m) c S) := by
  classical
  obtain ⟨Ps, hPs, hdisj, rfl⟩ := h
  refine ⟨(Ps.image (traceBlock (n / m) c)).filter (·.Nonempty), ?_, ?_, ?_⟩
  · -- each nonempty trace is a `μ_{gcd(d,m)}`-coset with the right bounds
    intro T hT
    obtain ⟨hTim, hTne⟩ := Finset.mem_filter.mp hT
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hTim
    obtain ⟨d, hdn, htd, hPd⟩ := hPs P hP
    obtain ⟨r, hr, hPeq⟩ := hPd
    have hPco : P = cosetOf n d r := hPeq
    have hd0 : 0 < d := by omega
    rcases traceBlock_cosetOf hn hm hm0 hdn hd0 hr hc with hemp | ⟨ρ, hρ, heq⟩
    · rw [hPco, hemp] at hTne
      exact absurd rfl hTne.ne_empty
    · exact ⟨Nat.gcd d m, Nat.gcd_dvd_right _ _, hH d hdn htd,
        isPacket_iff_cosetOf.mpr ⟨ρ, hρ, by rw [hPco]; exact heq⟩⟩
  · -- pairwise disjointness: distinct nonempty traces come from distinct
    -- (hence disjoint) parents
    intro T₁ hT₁ T₂ hT₂ hne
    obtain ⟨hT₁im, hT₁ne⟩ := Finset.mem_filter.mp hT₁
    obtain ⟨hT₂im, hT₂ne⟩ := Finset.mem_filter.mp hT₂
    obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.mp hT₁im
    obtain ⟨P₂, hP₂, rfl⟩ := Finset.mem_image.mp hT₂im
    have hP₁₂ : P₁ ≠ P₂ := fun h => hne (h ▸ rfl)
    have hdj : Disjoint P₁ P₂ :=
      hdisj (Finset.mem_coe.mpr hP₁) (Finset.mem_coe.mpr hP₂) hP₁₂
    exact disjoint_traceBlock hc hdj
  · rw [traceBlock_biUnion hc]
    ext e'
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨P, hP, hmem⟩
      exact ⟨traceBlock (n / m) c P, ⟨⟨P, hP, rfl⟩, ⟨e', hmem⟩⟩, hmem⟩
    · rintro ⟨T, ⟨⟨P, hP, rfl⟩, _⟩, hmem⟩
      exact ⟨P, hP, hmem⟩

/-! ## The backward direction: lifts of block decompositions assemble -/

/-- The lift of a canonical level-`m` coset into block `c` is a canonical
level-`n` coset with the same divisor. -/
lemma liftBlock_cosetOf {n m d' r' c : ℕ} (hm : m ∣ n) (hd' : d' ∣ m) :
    liftBlock (n / m) c (cosetOf m d' r') = cosetOf n d' (c + (n / m) * r') := by
  have hstep : n / m * (m / d') = n / d' := by
    rw [← Nat.mul_div_assoc _ hd', Nat.div_mul_cancel hm]
  ext e
  rw [mem_liftBlock]
  simp only [cosetOf, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨e', ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, by rw [← hstep]; ring⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨r' + s * (m / d'), ⟨s, hs, rfl⟩, by rw [← hstep]; ring⟩

/-- Lift bases are canonical: `c + g·r' < n/d'`. -/
lemma liftBlock_base_lt {n m d' r' c : ℕ} (hm : m ∣ n) (hd' : d' ∣ m)
    (hr' : r' < m / d') (hc : c < n / m) :
    c + (n / m) * r' < n / d' := by
  have hstep : n / m * (m / d') = n / d' := by
    rw [← Nat.mul_div_assoc _ hd', Nat.div_mul_cancel hm]
  calc c + (n / m) * r' < n / m + (n / m) * r' := by omega
    _ = (n / m) * (r' + 1) := by ring
    _ ≤ (n / m) * (m / d') := Nat.mul_le_mul_left _ (by omega)
    _ = n / d' := hstep

/-- Lifted elements sit in their block. -/
lemma liftBlock_mod {g c : ℕ} (hc : c < g) {T : Finset ℕ} {e : ℕ}
    (he : e ∈ liftBlock g c T) : e % g = c := by
  obtain ⟨e', _, rfl⟩ := mem_liftBlock.mp he
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- **Backward**: if every block trace decomposes at level `m`, then `S`
decomposes at level `n` (divisors of `m` are divisors of `n`). -/
theorem isWindowCosetUnion_of_traceBlocks {n m t : ℕ} (hn : 0 < n) (hm : m ∣ n)
    (hm0 : 0 < m) {S : Finset ℕ} (hSn : ∀ e ∈ S, e < n)
    (h : ∀ c < n / m, IsWindowCosetUnion m t (traceBlock (n / m) c S)) :
    IsWindowCosetUnion n t S := by
  classical
  set g := n / m with hgdef
  have hg0 : 0 < g := Nat.div_pos (Nat.le_of_dvd hn hm) hm0
  have hgm : g * m = n := Nat.div_mul_cancel hm
  -- choose a decomposition per block
  choose Qs hQs hQdisj hQunion using fun (c : Fin g) => h c.val c.isLt
  -- the lifted family
  set Ps : Finset (Finset ℕ) :=
    (Finset.univ : Finset (Fin g)).biUnion
      (fun c => (Qs c).image (liftBlock g c.val)) with hPsdef
  have hmemPs : ∀ P ∈ Ps, ∃ c : Fin g, ∃ Q ∈ Qs c, P = liftBlock g c.val Q := by
    intro P hP
    obtain ⟨c, _, hPim⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hPim
    exact ⟨c, Q, hQ, rfl⟩
  refine ⟨Ps, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨c, Q, hQ, rfl⟩ := hmemPs P hP
    obtain ⟨d', hd'm, htd', hQd'⟩ := hQs c Q hQ
    obtain ⟨r', hr', rfl⟩ := hQd'
    have hd'0 : 0 < d' := by omega
    refine ⟨d', hd'm.trans hm, htd', isPacket_iff_cosetOf.mpr
      ⟨c.val + g * r', liftBlock_base_lt hm hd'm hr' c.isLt, ?_⟩⟩
    exact liftBlock_cosetOf hm hd'm
  · -- pairwise disjointness of lifts
    intro P₁ hP₁ P₂ hP₂ hne
    obtain ⟨c₁, Q₁, hQ₁, rfl⟩ := hmemPs P₁ hP₁
    obtain ⟨c₂, Q₂, hQ₂, rfl⟩ := hmemPs P₂ hP₂
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    have hc₁ := liftBlock_mod c₁.isLt he₁
    have hc₂ := liftBlock_mod c₂.isLt he₂
    have hcc : c₁ = c₂ := Fin.ext (by rw [← hc₁, ← hc₂])
    subst hcc
    -- same block: lifts of distinct members of a disjoint family
    have hQQ : Q₁ ≠ Q₂ := by
      rintro rfl
      exact hne rfl
    obtain ⟨e₁', he₁', rfl⟩ := mem_liftBlock.mp he₁
    obtain ⟨e₂', he₂', heq⟩ := mem_liftBlock.mp he₂
    have hge : g * e₁' = g * e₂' := by omega
    have : e₁' = e₂' := Nat.eq_of_mul_eq_mul_left hg0 hge
    subst this
    exact Finset.disjoint_left.mp (hQdisj c₁ hQ₁ hQ₂ hQQ) he₁' he₂'
  · -- the union recomposes `S`
    ext e
    simp only [hPsdef, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image, id]
    constructor
    · rintro he
      have hen : e < n := hSn e he
      have hcblock : e % g < g := Nat.mod_lt _ hg0
      have hediv : e / g < m := by
        have : e < g * m := by rw [hgm]; exact hen
        exact Nat.div_lt_of_lt_mul this
      have hmem : e / g ∈ traceBlock g (e % g) S :=
        (mem_traceBlock hcblock).mpr (by rwa [Nat.mod_add_div e g])
      rw [hQunion ⟨e % g, hcblock⟩] at hmem
      obtain ⟨Q, hQ, hQmem⟩ := Finset.mem_biUnion.mp hmem
      refine ⟨liftBlock g (e % g) Q, ⟨⟨e % g, hcblock⟩, Q, hQ, rfl⟩, ?_⟩
      rw [mem_liftBlock]
      exact ⟨e / g, hQmem, (Nat.mod_add_div e g).symm⟩
    · rintro ⟨P, ⟨c, Q, hQ, rfl⟩, hmem⟩
      obtain ⟨e', he', rfl⟩ := mem_liftBlock.mp hmem
      have : e' ∈ traceBlock g c.val S := by
        rw [hQunion c]
        exact Finset.mem_biUnion.mpr ⟨Q, hQ, he'⟩
      exact (mem_traceBlock c.isLt).mp this

/-- **THE BLOCK-TRACE IFF (the fiber-count law's substance, O111 Lean layer)**:
under the abstract interface `(H)` — `m ∣ n` and every divisor of `n` exceeding
`t` has gcd with `m` exceeding `t` — a subset of `[0, n)` is a window coset
union at level `n` **iff** all its `n/m` block traces are window coset unions
at level `m`.  Since a set is determined by its block traces, this is the
set-level bijection `F_n(t) ≅ F_m(t)^(n/m)`. -/
theorem isWindowCosetUnion_iff_traceBlocks {n m t : ℕ} (hn : 0 < n) (hm : m ∣ n)
    (hm0 : 0 < m) (hH : ∀ d, d ∣ n → t < d → t < Nat.gcd d m)
    {S : Finset ℕ} (hSn : ∀ e ∈ S, e < n) :
    IsWindowCosetUnion n t S ↔
      ∀ c < n / m, IsWindowCosetUnion m t (traceBlock (n / m) c S) :=
  ⟨fun h _ hc => isWindowCosetUnion_traceBlock hn hm hm0 hH h hc,
    isWindowCosetUnion_of_traceBlocks hn hm hm0 hSn⟩

/-! ## The canonical instantiation: `m = lcm(Dmin)` -/

/-- The divisibility-minimal divisors of `n` exceeding `t` (O70's `Dmin`). -/
def minWindowDivisors (n t : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => t < d ∧ ∀ d' ∈ n.divisors, t < d' → d' ∣ d → d' = d

/-- Every divisor of `n` exceeding `t` is a multiple of a minimal one. -/
lemma exists_minWindowDivisor_dvd {n t : ℕ} (hn : 0 < n) :
    ∀ d, d ∣ n → t < d → ∃ d₀ ∈ minWindowDivisors n t, d₀ ∣ d := by
  intro d₁
  induction d₁ using Nat.strong_induction_on with
  | _ d ih =>
    intro hd htd
    by_cases hmin : ∀ d' ∈ n.divisors, t < d' → d' ∣ d → d' = d
    · refine ⟨d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩,
        htd, hmin⟩, dvd_rfl⟩
    · push Not at hmin
      obtain ⟨d', hd'mem, htd', hd'd, hne⟩ := hmin
      have hd'lt : d' < d :=
        lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd'd) hne
      obtain ⟨d₀, hd₀, hdvd⟩ :=
        ih d' hd'lt (Nat.dvd_of_mem_divisors hd'mem) htd'
      exact ⟨d₀, hd₀, hdvd.trans hd'd⟩

lemma lcm_minWindowDivisors_dvd {n t : ℕ} :
    (minWindowDivisors n t).lcm id ∣ n :=
  Finset.lcm_dvd fun _ hd =>
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1

lemma lcm_minWindowDivisors_pos {n t : ℕ} :
    0 < (minWindowDivisors n t).lcm id := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rw [Finset.lcm_eq_zero_iff] at h0
  obtain ⟨d, hd, hd0⟩ := h0
  have := (Finset.mem_filter.mp hd).2.1
  simp only [id] at hd0
  omega

/-- `m = lcm(Dmin)` satisfies the divisor-gcd interface `(H)`. -/
lemma gcd_lcm_minWindowDivisors_gt {n t : ℕ} (hn : 0 < n) :
    ∀ d, d ∣ n → t < d → t < Nat.gcd d ((minWindowDivisors n t).lcm id) := by
  intro d hd htd
  obtain ⟨d₀, hd₀mem, hd₀d⟩ := exists_minWindowDivisor_dvd hn d hd htd
  have ht0 : t < d₀ := (Finset.mem_filter.mp hd₀mem).2.1
  have hdvd : d₀ ∣ Nat.gcd d ((minWindowDivisors n t).lcm id) :=
    Nat.dvd_gcd hd₀d (by simpa using Finset.dvd_lcm hd₀mem)
  have hgcd0 : 0 < Nat.gcd d ((minWindowDivisors n t).lcm id) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  exact lt_of_lt_of_le ht0 (Nat.le_of_dvd hgcd0 hdvd)

/-- **The fiber-count law at the canonical modulus `m = lcm(Dmin)`** — the
O70/O111 law's exact instantiation: the window fiber at `n` is the product of
the window fibers at `lcm(Dmin)` over the `n/lcm(Dmin)` blocks. -/
theorem isWindowCosetUnion_iff_traceBlocks_lcm {n t : ℕ} (hn : 0 < n)
    {S : Finset ℕ} (hSn : ∀ e ∈ S, e < n) :
    IsWindowCosetUnion n t S ↔
      ∀ c < n / (minWindowDivisors n t).lcm id,
        IsWindowCosetUnion ((minWindowDivisors n t).lcm id) t
          (traceBlock (n / (minWindowDivisors n t).lcm id) c S) :=
  isWindowCosetUnion_iff_traceBlocks hn lcm_minWindowDivisors_dvd
    lcm_minWindowDivisors_pos (gcd_lcm_minWindowDivisors_gt hn) hSn

/-! ## The literal count: `|F_n(t)| = |F_m(t)|^(n/m)` -/

open Classical in
/-- The window fiber as a finite family: window coset unions inside `[0, n)`. -/
noncomputable def windowFiber (n t : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter fun S => IsWindowCosetUnion n t S

lemma mem_windowFiber {n t : ℕ} {S : Finset ℕ} :
    S ∈ windowFiber n t ↔ S ⊆ Finset.range n ∧ IsWindowCosetUnion n t S := by
  classical
  simp [windowFiber, Finset.mem_powerset]

/-- Tracing a lift on its own block recovers the set. -/
lemma traceBlock_liftBlock_self {g c : ℕ} (hc : c < g) (T : Finset ℕ) :
    traceBlock g c (liftBlock g c T) = T := by
  have hg0 : 0 < g := by omega
  ext e'
  rw [mem_traceBlock hc, mem_liftBlock]
  constructor
  · rintro ⟨e'', he'', heq⟩
    have : e' = e'' := by
      have hge : g * e' = g * e'' := by omega
      exact Nat.eq_of_mul_eq_mul_left hg0 hge
    rwa [this]
  · intro he'
    exact ⟨e', he', rfl⟩

/-- Tracing a lift on a different block is empty. -/
lemma traceBlock_liftBlock_ne {g c c' : ℕ} (hc : c < g) (hc' : c' < g)
    (hne : c ≠ c') (T : Finset ℕ) :
    traceBlock g c (liftBlock g c' T) = ∅ := by
  ext e'
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_traceBlock hc, mem_liftBlock]
  rintro ⟨e'', _, heq⟩
  have h1 : (c + g * e') % g = c := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have h2 : (c' + g * e'') % g = c' := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc']
  rw [heq, h2] at h1
  exact hne h1.symm

/-- A set inside `[0, n)` is the union of the lifts of its block traces. -/
lemma biUnion_liftBlock_traceBlock {n m : ℕ} (hm : m ∣ n) (hm0 : 0 < m)
    (hn : 0 < n) (S : Finset ℕ) :
    (Finset.univ : Finset (Fin (n / m))).biUnion
      (fun c => liftBlock (n / m) c.val (traceBlock (n / m) c.val S)) = S := by
  set g := n / m with hgdef
  have hg0 : 0 < g := Nat.div_pos (Nat.le_of_dvd hn hm) hm0
  ext e
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, _, hmem⟩
    obtain ⟨e', he', rfl⟩ := mem_liftBlock.mp hmem
    exact (mem_traceBlock c.isLt).mp he'
  · intro he
    have hcblock : e % g < g := Nat.mod_lt _ hg0
    refine ⟨⟨e % g, hcblock⟩, Finset.mem_univ _, ?_⟩
    rw [mem_liftBlock]
    refine ⟨e / g, (mem_traceBlock hcblock).mpr ?_, (Nat.mod_add_div e g).symm⟩
    rwa [Nat.mod_add_div e g]

/-- Block traces of a set inside `[0, n)` live inside `[0, m)`. -/
lemma traceBlock_subset_range {n m : ℕ} (hm : m ∣ n) {c : ℕ}
    (hc : c < n / m) {S : Finset ℕ} (hSn : S ⊆ Finset.range n) :
    traceBlock (n / m) c S ⊆ Finset.range m := by
  set g := n / m
  have hgm : g * m = n := Nat.div_mul_cancel hm
  intro e' he'
  have hmem := (mem_traceBlock hc).mp he'
  have hen : c + g * e' < n := Finset.mem_range.mp (hSn hmem)
  rw [Finset.mem_range]
  by_contra hge
  have : g * m ≤ g * e' := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Lifts of sets inside `[0, m)` live inside `[0, n)`. -/
lemma liftBlock_subset_range {n m : ℕ} (hm : m ∣ n) {c : ℕ}
    (hc : c < n / m) {T : Finset ℕ} (hTm : T ⊆ Finset.range m) :
    liftBlock (n / m) c T ⊆ Finset.range n := by
  set g := n / m
  have hgm : g * m = n := Nat.div_mul_cancel hm
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_liftBlock.mp he
  have he'm : e' < m := Finset.mem_range.mp (hTm he')
  rw [Finset.mem_range]
  calc c + g * e' < g + g * e' := by omega
    _ = g * (e' + 1) := by ring
    _ ≤ g * m := Nat.mul_le_mul_left _ (by omega)
    _ = n := hgm

/-- **THE FIBER-COUNT LAW, literal form**: under interface `(H)`,
`|F_n(t)| = |F_m(t)|^(n/m)` — the block-trace map is a bijection onto the
`(n/m)`-fold product of level-`m` fibers. -/
theorem card_windowFiber {n m t : ℕ} (hn : 0 < n) (hm : m ∣ n) (hm0 : 0 < m)
    (hH : ∀ d, d ∣ n → t < d → t < Nat.gcd d m) :
    (windowFiber n t).card = (windowFiber m t).card ^ (n / m) := by
  classical
  set g := n / m with hgdef
  have hg0 : 0 < g := Nat.div_pos (Nat.le_of_dvd hn hm) hm0
  have hcard : ((Fintype.piFinset fun _ : Fin g => windowFiber m t).card)
      = (windowFiber m t).card ^ g := by
    rw [Fintype.card_piFinset_const]
  rw [← hcard]
  apply Finset.card_bij
    (i := fun S _ => fun c : Fin g => traceBlock g c.val S)
  · -- maps into the product of level-m fibers
    intro S hS
    obtain ⟨hSn, hSw⟩ := mem_windowFiber.mp hS
    rw [Fintype.mem_piFinset]
    intro c
    rw [mem_windowFiber]
    exact ⟨traceBlock_subset_range hm c.isLt hSn,
      isWindowCosetUnion_traceBlock hn hm hm0 hH hSw c.isLt⟩
  · -- injective: a set is recovered from its traces
    intro S₁ hS₁ S₂ hS₂ heq
    have h1 := biUnion_liftBlock_traceBlock hm hm0 hn S₁
    have h2 := biUnion_liftBlock_traceBlock hm hm0 hn S₂
    rw [← h1, ← h2]
    congr 1
    funext c
    rw [show traceBlock g c.val S₁ = traceBlock g c.val S₂ from congrFun heq c]
  · -- surjective: assemble from any tuple of level-m fibers
    intro F hF
    rw [Fintype.mem_piFinset] at hF
    set S : Finset ℕ := (Finset.univ : Finset (Fin g)).biUnion
      (fun c => liftBlock g c.val (F c)) with hSdef
    have hSn : S ⊆ Finset.range n := by
      intro e he
      obtain ⟨c, _, hmem⟩ := Finset.mem_biUnion.mp he
      exact liftBlock_subset_range hm c.isLt
        (mem_windowFiber.mp (hF c)).1 hmem
    have htrace : ∀ c : Fin g, traceBlock g c.val S = F c := by
      intro c
      ext e'
      rw [mem_traceBlock c.isLt, hSdef, Finset.mem_biUnion]
      constructor
      · rintro ⟨c', _, hmem⟩
        obtain ⟨e'', he'', heq⟩ := mem_liftBlock.mp hmem
        have h1 : (c.val + g * e') % g = c.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]
        have h2 : (c'.val + g * e'') % g = c'.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c'.isLt]
        rw [heq, h2] at h1
        have hcc : c = c' := Fin.ext h1.symm
        subst hcc
        have hge : g * e' = g * e'' := by omega
        have he : e' = e'' := Nat.eq_of_mul_eq_mul_left hg0 hge
        rwa [he]
      · intro he'
        exact ⟨c, Finset.mem_univ _, mem_liftBlock.mpr ⟨e', he', rfl⟩⟩
    refine ⟨S, ?_, funext htrace⟩
    rw [mem_windowFiber]
    refine ⟨hSn, ?_⟩
    refine isWindowCosetUnion_of_traceBlocks hn hm hm0
      (fun e he => Finset.mem_range.mp (hSn he)) ?_
    intro c hc
    rw [htrace ⟨c, hc⟩]
    exact (mem_windowFiber.mp (hF ⟨c, hc⟩)).2

/-- The fiber-count law at the canonical modulus `lcm(Dmin)`. -/
theorem card_windowFiber_lcm {n t : ℕ} (hn : 0 < n) :
    (windowFiber n t).card
      = (windowFiber ((minWindowDivisors n t).lcm id) t).card
        ^ (n / (minWindowDivisors n t).lcm id) :=
  card_windowFiber hn lcm_minWindowDivisors_dvd lcm_minWindowDivisors_pos
    (gcd_lcm_minWindowDivisors_gt hn)

end DeBruijnWindowedLaw
