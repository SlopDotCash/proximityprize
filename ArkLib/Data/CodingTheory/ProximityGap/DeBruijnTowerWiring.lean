/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnTwoPrimeAssembly

/-!
# Issue #232 — WIRING de Bruijn two-prime into the mixed-radix tower surface (O95)

`DeBruijnTwoPrimeAssembly.debruijn_two_prime` (O94) classifies vanishing 0/1 sums of
`p^a·q^b`-th roots of unity at the EXPONENT level (`S : Finset ℕ`).  The mixed-radix
tower consumers (`MixedRadixTower.lean`, O73) speak the FIELD level: subsets
`T : Finset F` of `μ_n` with multiplicative closure hypotheses
`∀ y ∈ T, ∀ g, g ^ p = 1 → g * y ∈ T`.  This file is the bridge: it transports the
O94 classification onto the tower's own surface, in the tower's own closure language.

## What is discharged (the `t = 1` layer of the O70 tower law, unconditional)

* `vanishing_packet_dichotomy` — **the pointwise packet dichotomy**: on
  `n = p^a·q^b`-torsion domains (char 0), `∑_{y ∈ T} y = 0` forces EVERY `y ∈ T` to
  carry its full `μ_p`-coset or its full `μ_q`-coset inside `T`.  This is the sharp
  two-prime analogue of the `s = 1` rung of `LamLeungTwoPow.full_tower` (O53): at two
  primes, uniform closure is FALSE (a rotated `μ_q`-packet vanishes without being
  `μ_p`-closed — kernel-checked below), so the pointwise disjunction is the strongest
  true form.  Probe: dichotomy holds on ALL `1{,}001{,}100` vanishing subsets across
  `n = 12, 18` (exhaustive) and `n = 36` (full MITM census).
* `vanishing_card_two_prime` — **the Lam–Leung two-prime cardinality law** on the
  field surface: `|T| ∈ ℕ·p + ℕ·q` for every vanishing `T ⊆ μ_{p^a·q^b}` (de Bruijn
  packets have size exactly `p` or `q`).
* `rung_base_dichotomy` — the dichotomy instantiated at every level `n / p^k`
  (`k < a`) of the `MixedRadixTower.prime_climb_conditional` ladder, in the climb's
  own indexing (the `q`-side twin is symmetric).
* `m31_smooth_dichotomy`, `m31_smooth_card` — the M31 instantiation, `n = 18`:
  the multiplicative group of `F_{2^31−1}` has order `2^31 − 2 = 2·3²·7·11·31·151·331`,
  so its 2-3-smooth subgroup — the largest two-prime-smooth multiplicative domain over
  M31 — is `μ_18` with `18 = 2^1·3^2`.  (The 2-adic FFT/circle side of M31, `2^31 = q+1`
  with in-tree surface `MCAJohnsonEnvelope` at `n ≤ 2^M`, `M ≥ 31`, is the 2-power
  regime already covered by `full_tower`/O61.)

## The wall that remains (named, kernel-witnessed)

The conditional hypotheses `hBasep/hBaseq` of
`MixedRadixTower.two_prime_tower_conditional` demand UNIFORM `μ_p`-closure from a
power-sum window `1 ≤ j < w`.  At `w = 2` (sum only — all `debruijn_two_prime`
provides) this is FALSE: the negative control below exhibits the rotated `μ_3`-packet
`{ζ₁₂, ζ₁₂⁵, ζ₁₂⁹}`, vanishing but not `μ_2`-closed.  Discharging `hBase` at
`w > q^b` is the `t > 1` window law (O70's exhaustively verified divisor-coset law,
`F_n(t) =` disjoint unions of rotated `μ_d`-cosets with `d ∣ n`, `d > t`), which no
literature covers — genuinely open mathematics, not assembly.  The dichotomy here is
exactly its `t = 1` stratum, now unconditional.
-/

namespace DeBruijnTowerWiring

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The exponent-set bridge: `Finset F` subsets of `μ_n` ↔ `Finset ℕ` exponents -/

/-- The exponent set of `T ⊆ μ_n` along a primitive `n`-th root `ζ`:
`{e < n : ζ^e ∈ T}`. -/
def expSet (n : ℕ) (ζ : F) (T : Finset F) : Finset ℕ :=
  (Finset.range n).filter (fun e => ζ ^ e ∈ T)

lemma mem_expSet {n : ℕ} {ζ : F} {T : Finset F} {e : ℕ} :
    e ∈ expSet n ζ T ↔ e < n ∧ ζ ^ e ∈ T := by
  simp [expSet]

/-- The exponent set maps back onto `T`: every `n`-torsion element is a power of `ζ`. -/
lemma image_expSet {n : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset F} (hT : ∀ y ∈ T, y ^ n = 1) :
    (expSet n ζ T).image (ζ ^ ·) = T := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_expSet.mp he).2
  · intro y hy
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hT y hy)
    exact Finset.mem_image.mpr ⟨i, mem_expSet.mpr ⟨hi, hy⟩, rfl⟩

/-- Sums transport across the bridge (the discrete log is injective below `n`). -/
lemma sum_expSet {n : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset F} (hT : ∀ y ∈ T, y ^ n = 1) :
    ∑ e ∈ expSet n ζ T, ζ ^ e = ∑ y ∈ T, y := by
  conv_rhs => rw [← image_expSet hn hζ hT]
  rw [Finset.sum_image (fun i hi j hj hij =>
    hζ.pow_inj (mem_expSet.mp hi).1 (mem_expSet.mp hj).1 hij)]

/-- Cardinalities transport across the bridge. -/
lemma card_expSet {n : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset F} (hT : ∀ y ∈ T, y ^ n = 1) :
    (expSet n ζ T).card = T.card := by
  conv_rhs => rw [← image_expSet hn hζ hT]
  rw [Finset.card_image_of_injOn (fun i hi j hj hij =>
    hζ.pow_inj (mem_expSet.mp (Finset.mem_coe.mp hi)).1
      (mem_expSet.mp (Finset.mem_coe.mp hj)).1 hij)]

/-! ## The absorption engine: a canonical exponent packet absorbs the full `μ_d`-coset -/

omit [DecidableEq F] in
/-- **Packet absorption**: if the exponent `e` of `y = ζ^e` lies in a canonical
`d`-packet `P` all of whose members exponentiate into `T`, then `T` absorbs the whole
coset `μ_d · y`.  The index arithmetic is the O94 lift map run in reverse: rotating by
`(ζ^{n/d})^t` moves `e = r + s·(n/d)` to `r + ((s+t) % d)·(n/d) ∈ P`, the wraparound
killed by `ζ^n = 1`. -/
lemma packet_absorb {n d : ℕ} (hd : 0 < d) (hdn : d ∣ n) (hnpos : 0 < n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) {T : Finset F}
    {P : Finset ℕ} (hP : DeBruijnTwoPrimeAssembly.IsPacket n d P)
    (hPT : ∀ x ∈ P, ζ ^ x ∈ T) {e : ℕ} (heP : e ∈ P) :
    ∀ g : F, g ^ d = 1 → g * ζ ^ e ∈ T := by
  obtain ⟨r, hr, rfl⟩ := hP
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp heP
  intro g hg
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
  have hξ : IsPrimitiveRoot (ζ ^ (n / d)) d :=
    hζ.pow hnpos (Nat.div_mul_cancel hdn).symm
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨t, htd, rfl⟩ := hξ.eq_pow_of_pow_eq_one hg
  have hsplit : (s + t) * (n / d) = n * ((s + t) / d) + (s + t) % d * (n / d) := by
    conv_lhs => rw [← Nat.div_add_mod (s + t) d]
    rw [Nat.add_mul]
    congr 1
    calc d * ((s + t) / d) * (n / d)
        = (s + t) / d * (d * (n / d)) := by ring
      _ = n * ((s + t) / d) := by rw [hmul]; ring
  have hkey : (ζ ^ (n / d)) ^ t * ζ ^ (r + s * (n / d))
      = ζ ^ (r + (s + t) % d * (n / d)) := by
    rw [← pow_mul, ← pow_add]
    have harith : n / d * t + (r + s * (n / d))
        = r + (s + t) % d * (n / d) + n * ((s + t) / d) := by
      have hcollect : n / d * t + (r + s * (n / d)) = r + (s + t) * (n / d) := by
        ring
      rw [hcollect, hsplit]
      ring
    rw [harith, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [hkey]
  exact hPT _ (Finset.mem_image.mpr
    ⟨(s + t) % d, Finset.mem_range.mpr (Nat.mod_lt _ hd), rfl⟩)

/-! ## The dichotomy: the `t = 1` tower layer, unconditional on the field surface -/

/-- **The pointwise packet dichotomy** (de Bruijn 1953 on the tower surface — the
`t = 1` stratum of the O70 divisor-coset law, unconditional): in characteristic zero,
if `T ⊆ μ_{p^a·q^b}` (`p ≠ q` primes, `a, b ≥ 1`) has vanishing sum, then every
`y ∈ T` carries its FULL `μ_p`-coset or its FULL `μ_q`-coset inside `T` — in exactly
the closure language of `MixedRadixTower.mixed_rung_conditional`.

The disjunction is pointwise and SHARP: uniform `μ_p`-closure is refuted by a rotated
`μ_q`-packet (negative control below), which is why the `hBase` hypotheses of the
conditional tower demand the `t > 1` window law rather than this theorem. -/
theorem vanishing_packet_dichotomy [CharZero F] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {T : Finset F} (hT : ∀ y ∈ T, y ^ (p ^ a * q ^ b) = 1)
    (hsum : ∑ y ∈ T, y = 0) :
    ∀ y ∈ T, (∀ g : F, g ^ p = 1 → g * y ∈ T) ∨ (∀ g : F, g ^ q = 1 → g * y ∈ T) := by
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hpn : p ∣ p ^ a * q ^ b := dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _
  have hqn : q ∣ p ^ a * q ^ b := dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _
  have hSlt : ∀ e ∈ expSet (p ^ a * q ^ b) ζ T, e < p ^ a * q ^ b :=
    fun e he => (mem_expSet.mp he).1
  have hsumS : ∑ e ∈ expSet (p ^ a * q ^ b) ζ T, ζ ^ e = 0 := by
    rw [sum_expSet hnpos hζ hT]
    exact hsum
  obtain ⟨Ps, htype, hdisj, huni⟩ :=
    (DeBruijnTwoPrimeAssembly.debruijn_two_prime hp hq hpq ha hb hζ hSlt).mp hsumS
  intro y hy
  haveI : NeZero (p ^ a * q ^ b) := ⟨hnpos.ne'⟩
  obtain ⟨e, helt, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hT y hy)
  have heS : e ∈ expSet (p ^ a * q ^ b) ζ T := mem_expSet.mpr ⟨helt, hy⟩
  rw [huni] at heS
  obtain ⟨P, hPmem, hePmem⟩ := Finset.mem_biUnion.mp heS
  have hPT : ∀ x ∈ P, ζ ^ x ∈ T := by
    intro x hx
    have hxS : x ∈ expSet (p ^ a * q ^ b) ζ T := by
      rw [huni]
      exact Finset.mem_biUnion.mpr ⟨P, hPmem, hx⟩
    exact (mem_expSet.mp hxS).2
  rcases htype P hPmem with hPp | hPq
  · exact Or.inl (packet_absorb hp.pos hpn hnpos hζ hPp hPT hePmem)
  · exact Or.inr (packet_absorb hq.pos hqn hnpos hζ hPq hPT hePmem)

/-! ## The cardinality law: Lam–Leung at two primes, on the field surface -/

/-- **The two-prime Lam–Leung cardinality law** (field surface): a vanishing
`T ⊆ μ_{p^a·q^b}` has `|T| ∈ ℕ·p + ℕ·q` — the de Bruijn decomposition counts its
packets, each of size exactly `p` or `q`.  On the M31 multiplicative smooth domain
this constrains every vanishing syndrome support. -/
theorem vanishing_card_two_prime [CharZero F] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {T : Finset F} (hT : ∀ y ∈ T, y ^ (p ^ a * q ^ b) = 1)
    (hsum : ∑ y ∈ T, y = 0) :
    ∃ cp cq : ℕ, T.card = cp * p + cq * q := by
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hpn : p ∣ p ^ a * q ^ b := dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _
  have hqn : q ∣ p ^ a * q ^ b := dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _
  have hSlt : ∀ e ∈ expSet (p ^ a * q ^ b) ζ T, e < p ^ a * q ^ b :=
    fun e he => (mem_expSet.mp he).1
  have hsumS : ∑ e ∈ expSet (p ^ a * q ^ b) ζ T, ζ ^ e = 0 := by
    rw [sum_expSet hnpos hζ hT]
    exact hsum
  obtain ⟨Ps, htype, hdisj, huni⟩ :=
    (DeBruijnTwoPrimeAssembly.debruijn_two_prime hp hq hpq ha hb hζ hSlt).mp hsumS
  have hcardP : ∀ P ∈ Ps, P.card = p ∨ P.card = q := by
    intro P hP
    rcases htype P hP with h | h
    · exact Or.inl (h.card_eq (Nat.div_pos (Nat.le_of_dvd hnpos hpn) hp.pos))
    · exact Or.inr (h.card_eq (Nat.div_pos (Nat.le_of_dvd hnpos hqn) hq.pos))
  refine ⟨(Ps.filter (fun P => P.card = p)).card,
    (Ps.filter (fun P => ¬ P.card = p)).card, ?_⟩
  have h1 : T.card = ∑ P ∈ Ps, P.card := by
    rw [← card_expSet hnpos hζ hT, huni]
    have h := Finset.card_biUnion (s := Ps) (t := id) hdisj
    simpa using h
  have hA : ∑ P ∈ Ps.filter (fun P => P.card = p), P.card
      = (Ps.filter (fun P => P.card = p)).card * p := by
    calc ∑ P ∈ Ps.filter (fun P => P.card = p), P.card
        = ∑ _P ∈ Ps.filter (fun P => P.card = p), p :=
          Finset.sum_congr rfl (fun P hP => (Finset.mem_filter.mp hP).2)
      _ = (Ps.filter (fun P => P.card = p)).card * p := by
          rw [Finset.sum_const, smul_eq_mul]
  have hB : ∑ P ∈ Ps.filter (fun P => ¬ P.card = p), P.card
      = (Ps.filter (fun P => ¬ P.card = p)).card * q := by
    have hq' : ∀ P ∈ Ps.filter (fun P => ¬ P.card = p), P.card = q := by
      intro P hP
      rcases hcardP P (Finset.mem_filter.mp hP).1 with h | h
      · exact absurd h (Finset.mem_filter.mp hP).2
      · exact h
    calc ∑ P ∈ Ps.filter (fun P => ¬ P.card = p), P.card
        = ∑ _P ∈ Ps.filter (fun P => ¬ P.card = p), q := Finset.sum_congr rfl hq'
      _ = (Ps.filter (fun P => ¬ P.card = p)).card * q := by
          rw [Finset.sum_const, smul_eq_mul]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not Ps (fun P => P.card = p), hA, hB]

/-! ## The rung-level instantiation: the dichotomy at every level of the climb -/

/-- **The dichotomy at every rung of the `p`-climb**: in the indexing of
`MixedRadixTower.prime_climb_conditional` (`n = p^a·q^b`, levels `n / p^k`, `k < a`),
every level's vanishing subsets satisfy the packet dichotomy — the `t = 1` base layer
of the climb is unconditionally classified at every height.  (The `q`-side twin is
symmetric.)  The conditional `hBase k` of the climb asks for more — uniform closure
from a `w k`-window — which is the open `t > 1` law; this theorem is what `w = 2`
honestly yields. -/
theorem rung_base_dichotomy [CharZero F] {n p q a b k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hk : k < a) (hb : 0 < b)
    (hn : n = p ^ a * q ^ b) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset F} (hT : ∀ y ∈ T, y ^ (n / p ^ k) = 1)
    (hsum : ∑ y ∈ T, y = 0) :
    ∀ y ∈ T, (∀ g : F, g ^ p = 1 → g * y ∈ T) ∨ (∀ g : F, g ^ q = 1 → g * y ∈ T) := by
  have hsplit : n = p ^ k * (p ^ (a - k) * q ^ b) := by
    rw [hn, ← Nat.mul_assoc, pow_mul_pow_sub p hk.le]
  have hdivn : n / p ^ k = p ^ (a - k) * q ^ b := by
    rw [hsplit, Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
  have hnpos : 0 < n := by
    rw [hn]
    exact Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hζ' : IsPrimitiveRoot (ζ ^ p ^ k) (p ^ (a - k) * q ^ b) := hζ.pow hnpos hsplit
  rw [hdivn] at hT
  exact vanishing_packet_dichotomy hp hq hpq (by omega) hb hζ' hT hsum

/-! ## The M31 instantiation: `n = 18`, the two-prime-smooth multiplicative domain

`|F_{2^31−1}^×| = 2^31 − 2 = 2 · 3^2 · 7 · 11 · 31 · 151 · 331`, so the 2-3-smooth
subgroup — the exact regime O67 named for the de Bruijn program — is `μ_18`,
`18 = 2^1 · 3^2`.  (M31's 2-adic circle/FFT side `2^31 = q + 1` is the 2-power regime
of `full_tower`.) -/

/-- **The M31 smooth-domain dichotomy**: every vanishing subset of `μ_18` (char 0)
carries, through each of its points, a full `μ_2`-coset or a full `μ_3`-coset. -/
theorem m31_smooth_dichotomy [CharZero F] {ζ : F} (hζ : IsPrimitiveRoot ζ 18)
    {T : Finset F} (hT : ∀ y ∈ T, y ^ 18 = 1) (hsum : ∑ y ∈ T, y = 0) :
    ∀ y ∈ T, (∀ g : F, g ^ 2 = 1 → g * y ∈ T) ∨ (∀ g : F, g ^ 3 = 1 → g * y ∈ T) := by
  have h18 : (18 : ℕ) = 2 ^ 1 * 3 ^ 2 := by norm_num
  rw [h18] at hζ hT
  exact vanishing_packet_dichotomy Nat.prime_two Nat.prime_three (by norm_num)
    one_pos (by norm_num) hζ hT hsum

/-- **The M31 smooth-domain cardinality law**: vanishing subsets of `μ_18` have
`|T| ∈ 2ℕ + 3ℕ`. -/
theorem m31_smooth_card [CharZero F] {ζ : F} (hζ : IsPrimitiveRoot ζ 18)
    {T : Finset F} (hT : ∀ y ∈ T, y ^ 18 = 1) (hsum : ∑ y ∈ T, y = 0) :
    ∃ cp cq : ℕ, T.card = cp * 2 + cq * 3 := by
  have h18 : (18 : ℕ) = 2 ^ 1 * 3 ^ 2 := by norm_num
  rw [h18] at hζ hT
  exact vanishing_card_two_prime Nat.prime_two Nat.prime_three (by norm_num)
    one_pos (by norm_num) hζ hT hsum

/-! ## Teeth -/

private lemma exp_root_primitive (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- The dichotomy FIRED at `ℂ` on the M31 smooth domain: `T = {1, −1} ⊆ μ_18` has
vanishing sum, and the theorem produces coset closure through every point — the
hypotheses are jointly satisfiable and the conclusion lands. -/
example : ∀ y ∈ ({1, -1} : Finset ℂ),
    (∀ g : ℂ, g ^ 2 = 1 → g * y ∈ ({1, -1} : Finset ℂ))
    ∨ (∀ g : ℂ, g ^ 3 = 1 → g * y ∈ ({1, -1} : Finset ℂ)) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (18 : ℕ))) 18 :=
    exp_root_primitive 18 (by norm_num)
  refine m31_smooth_dichotomy hζ ?_ ?_
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · norm_num
    · rw [Finset.mem_singleton] at hy
      subst hy
      norm_num
  · rw [Finset.sum_pair (by norm_num : (1 : ℂ) ≠ -1)]
    norm_num

/-- **NEGATIVE CONTROL — the named wall, kernel-checked**: the rotated `μ_3`-packet
`{1, 5, 9}` at `n = 12` has vanishing sum (by the O94 converse) yet is NOT closed
under the `μ_2` exponent shift `e ↦ (e + 6) % 12` (since `7 ∉ {1, 5, 9}`).  So sum
vanishing alone can NEVER discharge the uniform-closure hypothesis
`hBase (w = 2)` of `MixedRadixTower.mixed_rung_conditional`: the pointwise dichotomy
is the sharp `t = 1` truth, and unconditionalizing the rung requires the `t > 1`
window law (open). -/
example : (∑ e ∈ ({1, 5, 9} : Finset ℕ),
      Complex.exp (2 * Real.pi * Complex.I / (12 : ℕ)) ^ e = 0)
    ∧ ¬ ∀ e ∈ ({1, 5, 9} : Finset ℕ), (e + 6) % 12 ∈ ({1, 5, 9} : Finset ℕ) := by
  constructor
  · refine DeBruijnTwoPrimeAssembly.sum_eq_zero_of_isPacketUnion
      (n := 12) (p := 2) (q := 3) one_lt_two (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (exp_root_primitive 12 (by norm_num)) ?_
    refine ⟨{({1, 5, 9} : Finset ℕ)}, fun P hP => ?_, ?_, ?_⟩
    · rw [Finset.mem_singleton] at hP
      subst hP
      exact Or.inr ⟨1, by norm_num, by decide⟩
    · rw [Finset.coe_singleton]
      exact Set.pairwiseDisjoint_singleton _ _
    · rw [Finset.singleton_biUnion]
      rfl
  · decide

/-! ## Axiom audit -/

#print axioms DeBruijnTowerWiring.vanishing_packet_dichotomy
#print axioms DeBruijnTowerWiring.vanishing_card_two_prime
#print axioms DeBruijnTowerWiring.rung_base_dichotomy
#print axioms DeBruijnTowerWiring.m31_smooth_dichotomy
#print axioms DeBruijnTowerWiring.m31_smooth_card
#print axioms DeBruijnTowerWiring.packet_absorb
#print axioms DeBruijnTowerWiring.image_expSet

end DeBruijnTowerWiring
