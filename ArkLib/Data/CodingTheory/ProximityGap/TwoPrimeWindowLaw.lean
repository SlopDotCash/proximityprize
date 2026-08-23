/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnTowerWiring
import ArkLib.Data.CodingTheory.ProximityGap.MixedRadixTower

/-!
# Issue #232 — THE TWO-PRIME WINDOW LAW: the mixed-radix tower goes UNCONDITIONAL (O97)

O95 (`DeBruijnTowerWiring`) ended with: "what separates `two_prime_tower_conditional`
from unconditional is ONE named statement, the `t > 1` window law … genuinely new
mathematics".  This file proves that statement at every two-prime modulus
`n = p^a·q^b`, by induction on the `q`-exponent over the landed O94 classification —
no weighted/multiplicity de Bruijn theory is needed.

## The rung (the new theorem, `window_mu_p_closed`)

For `T ⊆ μ_{p^a·q^b}` (char 0, `p ≠ q` primes, `a ≥ 1`, `b ≥ 0`):

    `∑_{y∈T} y^(q^c) = 0` for ALL `c ≤ b`   ⟹   `T` is `μ_p`-closed.

A SPARSE window — only the `b+1` exponents `1, q, q², …, q^b` — suffices.  Mechanism:
* `c = 0` vanishing ⟹ the O94 packet decomposition of the exponent set;
* at exponents `q^(c+1)` every `μ_p`-packet dies (`q^(c+1)` coprime to `p`, full
  twisted geometric sum — `packet_sum_pow_coprime`) while every `μ_q`-packet
  collapses to `q·ρ^(q^c)` for its SPECTRUM point `ρ = ζ^(q·base)`
  (`qpacket_sum_pow`);
* canonical bases are `< n/q`, so `P ↦ ρ_P` is collision-free and the spectrum is an
  honest `Finset` one `q`-level down, inheriting the window;
* induction on `b`; the floor `b = 0` is Lam–Leung at prime powers
  (`MixedRadixTower.vanishing_sum_mu_p_closed`, O66);
* closure lifts back: `g^q ∈ μ_p` moves spectrum points, and the moved packet
  absorbs `g·y` via `DeBruijnTowerWiring.packet_absorb`.

With the cheap converse (`pow_sum_eq_zero_of_mu_p_closed`: a `μ_p`-closed set kills
every power sum at `p`-coprime exponents), the sparse window EXACTLY characterizes
`μ_p`-closure (`window_iff_mu_p_closed`).

## The capstone (`two_prime_tower_window`)

The rung discharges EVERY `hBasep`/`hBaseq` hypothesis of
`MixedRadixTower.two_prime_tower_conditional` at exact level `n = p^a·q^b`
(`base_discharge`), so the tower goes unconditional: an interval window

    `1 ≤ j < max (p^(a-1)·(q^b+1)) (q^(b-1)·(p^a+1))`

forces closure under the FULL `μ_{p^a·q^b}` — hence `S ∈ {∅, μ_n}` at exact level
(`two_prime_window_empty_or_full`).  Partial windows give the intermediate
`μ_{p^t}`-closures (`two_prime_partial_climb`).  Instances: the M31 smooth domain
`μ_18` (window `j < 10`, sharp per the probe: the rotated `μ_9`-coset survives
`j < 9`), and `n = 2^a·3` (window `j < 2^(a+1)`) — O95's named items (ii) and (iii).

Falsified first: `scripts/probes/probe_two_prime_window_law.py` (exact integer
arithmetic mod `Φ_n`; exit 0): the rung EXHAUSTIVELY over all `2^n` masks at
`n = 12, 18, 20, 24` and the full MITM census at `n = 36` (`a = b = 2`; 1,000,000
vanishing masks, 262,144 rung candidates, 0 violators), both orientations; sharpness
(dropping the top exponent `q^b` admits the rotated `μ_{q^b}`-coset violator, so the
sparse window is minimal in length); the capstone window forces empty/full at every
test point (interval slack ≤ 4, within one of sharp at `n = 18`).

## Honest scope

* Exact two-prime levels only: `n = p^a·q^b`, no third prime or cofactor.  The
  cofactor/multi-prime generalization is genuinely open (Lam–Leung ℕ-span territory).
* The capstone's interval window is what the climb's plumbing consumes; the probe
  records the sharp interval thresholds (slack 0–4 at the test points).  The rung's
  SPARSE window is exactly minimal in length (probe R3/R3').
-/

namespace TwoPrimeWindowLaw

open Finset DeBruijnTwoPrimeAssembly DeBruijnTowerWiring

variable {F : Type*} [Field F]

/-! ## Packet power sums at twisted roots -/

/-- **Packet death at coprime exponents**: a canonical `d`-packet sums to zero
against `ζ^j` whenever `j` is coprime to `d` — the twisted geometric sum is still
full.  (At `d = p` this kills every `μ_p`-packet at every exponent `q^c`.) -/
lemma packet_sum_pow_coprime {n d j : ℕ} (hd : 1 < d) (hdn : d ∣ n) (hn : 0 < n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (hcop : Nat.Coprime j d)
    {P : Finset ℕ} (hP : IsPacket n d P) :
    ∑ e ∈ P, (ζ ^ j) ^ e = 0 := by
  obtain ⟨r, _, rfl⟩ := hP
  have hstep : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) (by omega)
  have hinj : ∀ t₁ ∈ Finset.range d, ∀ t₂ ∈ Finset.range d,
      r + t₁ * (n / d) = r + t₂ * (n / d) → t₁ = t₂ := by
    intro t₁ _ t₂ _ h
    exact Nat.eq_of_mul_eq_mul_right hstep (by omega)
  rw [Finset.sum_image hinj]
  have hξ : IsPrimitiveRoot (ζ ^ (n / d)) d := hζ.pow hn (Nat.div_mul_cancel hdn).symm
  have hξj : IsPrimitiveRoot ((ζ ^ (n / d)) ^ j) d := hξ.pow_of_coprime j hcop
  have hterm : ∀ t ∈ Finset.range d,
      (ζ ^ j) ^ (r + t * (n / d)) = (ζ ^ j) ^ r * ((ζ ^ (n / d)) ^ j) ^ t := by
    intro t _
    simp only [← pow_mul, ← pow_add]
    congr 1
    ring
  calc ∑ t ∈ Finset.range d, (ζ ^ j) ^ (r + t * (n / d))
      = (ζ ^ j) ^ r * ∑ t ∈ Finset.range d, ((ζ ^ (n / d)) ^ j) ^ t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hterm
    _ = 0 := by rw [hξj.geom_sum_eq_zero hd, mul_zero]

/-- **`μ_q`-packet collapse at `q`-power exponents**: against `ζ^(q^(c+1))` a
canonical `q`-packet contributes `q` copies of `ζ^(q^(c+1)·base)` — the wraparound
`ζ^(q^(c+1)·t·(n/q)) = (ζ^n)^(q^c·t) = 1` makes every tooth equal. -/
lemma qpacket_sum_pow {n q r : ℕ} (hq : 0 < q) (hqn : q ∣ n) (hn : 0 < n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (c : ℕ) :
    ∑ e ∈ (Finset.range q).image (fun t => r + t * (n / q)), (ζ ^ q ^ (c + 1)) ^ e
      = q • ζ ^ (q ^ (c + 1) * r) := by
  have hstep : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn) hq
  have hinj : ∀ t₁ ∈ Finset.range q, ∀ t₂ ∈ Finset.range q,
      r + t₁ * (n / q) = r + t₂ * (n / q) → t₁ = t₂ := by
    intro t₁ _ t₂ _ h
    exact Nat.eq_of_mul_eq_mul_right hstep (by omega)
  rw [Finset.sum_image hinj]
  have hterm : ∀ t ∈ Finset.range q,
      (ζ ^ q ^ (c + 1)) ^ (r + t * (n / q)) = ζ ^ (q ^ (c + 1) * r) := by
    intro t _
    have hmul : q * (n / q) = n := Nat.mul_div_cancel' hqn
    have hsplit : q ^ (c + 1) * (r + t * (n / q))
        = q ^ (c + 1) * r + n * (q ^ c * t) := by
      calc q ^ (c + 1) * (r + t * (n / q))
          = q ^ (c + 1) * r + q ^ c * (q * (n / q)) * t := by ring
        _ = q ^ (c + 1) * r + n * (q ^ c * t) := by rw [hmul]; ring
    rw [← pow_mul, hsplit, pow_add, pow_mul ζ n (q ^ c * t), hζ.pow_eq_one,
      one_pow, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]

/-! ## The bridge: power sums transport across the exponent set -/

/-- Power sums transport across the `expSet` bridge at every exponent. -/
lemma sum_pow_expSet [DecidableEq F] {n : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) {T : Finset F} (hT : ∀ y ∈ T, y ^ n = 1) (j : ℕ) :
    ∑ e ∈ expSet n ζ T, (ζ ^ j) ^ e = ∑ y ∈ T, y ^ j := by
  conv_rhs => rw [← image_expSet hn hζ hT]
  rw [Finset.sum_image (fun i hi i' hi' hii =>
    hζ.pow_inj (mem_expSet.mp hi).1 (mem_expSet.mp hi').1 hii)]
  exact Finset.sum_congr rfl fun e _ => by rw [← pow_mul, mul_comm, pow_mul]

/-! ## THE RUNG: the sparse `q`-power window forces `μ_p`-closure -/

/-- **THE TWO-PRIME WINDOW RUNG** (the windowed law named open by O95, proved): in
characteristic zero, a subset `T ⊆ μ_{p^a·q^b}` (`p ≠ q` primes, `a ≥ 1`) whose
power sums vanish at the sparse window `{q^c : c ≤ b}` is closed under
multiplication by every `p`-th root of unity.

Induction on `b`: the `c = 0` sum plus O94 (`debruijn_two_prime`) decompose the
exponent set into prime packets; exponent `q^(c+1)` kills the `μ_p`-packets and
sends each `μ_q`-packet to `q·ρ^(q^c)` for its spectrum point `ρ = ζ^(q·base)`;
canonical bases make the spectrum collision-free, so it is a vanishing subset of
`μ_{p^a·q^(b-1)}` inheriting the window one level down; `b = 0` is Lam–Leung at
prime powers (O66).  Closure lifts back through `packet_absorb` since `g^q ∈ μ_p`
moves spectrum points. -/
theorem window_mu_p_closed [DecidableEq F] [CharZero F] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∀ b a : ℕ, 0 < a → ∀ ζ : F, IsPrimitiveRoot ζ (p ^ a * q ^ b) →
      ∀ T : Finset F, (∀ y ∈ T, y ^ (p ^ a * q ^ b) = 1) →
      (∀ c, c ≤ b → ∑ y ∈ T, y ^ q ^ c = 0) →
      ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T := by
  intro b
  induction b with
  | zero =>
    intro a ha ζ hζ T hT hwin
    rw [pow_zero, mul_one] at hζ hT
    have hsum : ∑ y ∈ T, y = 0 := by
      have h := hwin 0 le_rfl
      simpa using h
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    exact MixedRadixTower.vanishing_sum_mu_p_closed hp hζ hT hsum
  | succ b ih =>
    intro a ha ζ hζ T hT hwin
    classical
    have hnpos : 0 < p ^ a * q ^ (b + 1) :=
      Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos (b + 1))
    have hpn : p ∣ p ^ a * q ^ (b + 1) :=
      dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _
    have hqn : q ∣ p ^ a * q ^ (b + 1) :=
      dvd_mul_of_dvd_right (dvd_pow_self q (Nat.succ_ne_zero b)) _
    have hqF : ((q : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr hq.pos.ne'
    -- the O94 decomposition from the `c = 0` sum
    have hSlt : ∀ e ∈ expSet (p ^ a * q ^ (b + 1)) ζ T, e < p ^ a * q ^ (b + 1) :=
      fun e he => (mem_expSet.mp he).1
    have hsum0 : ∑ e ∈ expSet (p ^ a * q ^ (b + 1)) ζ T, ζ ^ e = 0 := by
      rw [sum_expSet hnpos hζ hT]
      have h := hwin 0 (Nat.zero_le _)
      simpa using h
    obtain ⟨Ps, htype, hdisj, huni⟩ :=
      (debruijn_two_prime hp hq hpq ha (Nat.succ_pos b) hζ hSlt).mp hsum0
    -- the `μ_q`-packet part and the spectrum value
    have hQs : ∀ P ∈ Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P),
        IsPacket (p ^ a * q ^ (b + 1)) q P := fun P hP =>
      (htype P (Finset.mem_filter.mp hP).1).resolve_left (Finset.mem_filter.mp hP).2
    have hsv : ∀ r : ℕ,
        (q : F)⁻¹ * ∑ e ∈ (Finset.range q).image
            (fun t => r + t * ((p ^ a * q ^ (b + 1)) / q)), (ζ ^ q) ^ e
          = ζ ^ (q * r) := by
      intro r
      have h0 := qpacket_sum_pow (F := F) (r := r) hq.pos hqn hnpos hζ 0
      simp only [zero_add, pow_one] at h0
      rw [h0, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hqF, one_mul]
    -- the twisted sums collapse packet-by-packet
    have hQsum : ∀ P ∈ Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P),
        ∀ c : ℕ, ∑ e ∈ P, (ζ ^ q ^ (c + 1)) ^ e
          = q • (((q : F)⁻¹ * ∑ e ∈ P, (ζ ^ q) ^ e) ^ q ^ c) := by
      intro P hP c
      obtain ⟨r, hr, rfl⟩ := hQs P hP
      rw [qpacket_sum_pow hq.pos hqn hnpos hζ c, hsv r, ← pow_mul]
      have hexp : q ^ (c + 1) * r = q * r * q ^ c := by ring
      rw [hexp]
    -- spectrum injectivity (canonical bases pin the discrete log)
    have hqrlt : ∀ {r : ℕ}, r < (p ^ a * q ^ (b + 1)) / q →
        q * r < p ^ a * q ^ (b + 1) := by
      intro r hr
      have h1 : q * r < q * ((p ^ a * q ^ (b + 1)) / q) :=
        mul_lt_mul_of_pos_left hr hq.pos
      rwa [Nat.mul_div_cancel' hqn] at h1
    have hinjQ : ∀ P ∈ Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P),
        ∀ P' ∈ Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P),
        (q : F)⁻¹ * ∑ e ∈ P, (ζ ^ q) ^ e = (q : F)⁻¹ * ∑ e ∈ P', (ζ ^ q) ^ e →
        P = P' := by
      intro P hP P' hP' heq
      obtain ⟨r, hr, rfl⟩ := hQs P hP
      obtain ⟨r', hr', rfl⟩ := hQs P' hP'
      rw [hsv r, hsv r'] at heq
      have hrr : q * r = q * r' := hζ.pow_inj (hqrlt hr) (hqrlt hr') heq
      have hrr' : r = r' := Nat.eq_of_mul_eq_mul_left hq.pos hrr
      rw [hrr']
    -- the spectrum window, one level down
    have hRwin : ∀ c, c ≤ b →
        ∑ z ∈ (Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P)).image
          (fun P => (q : F)⁻¹ * ∑ e ∈ P, (ζ ^ q) ^ e), z ^ q ^ c = 0 := by
      intro c hc
      have hbridge : ∑ e ∈ expSet (p ^ a * q ^ (b + 1)) ζ T,
          (ζ ^ q ^ (c + 1)) ^ e = 0 := by
        rw [sum_pow_expSet hnpos hζ hT]
        exact hwin (c + 1) (by omega)
      rw [huni, Finset.sum_biUnion hdisj] at hbridge
      simp only [id_eq] at hbridge
      have hsubset : Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P) ⊆ Ps :=
        Finset.filter_subset _ _
      have hvanish : ∀ P ∈ Ps,
          P ∉ Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P) →
          ∑ e ∈ P, (ζ ^ q ^ (c + 1)) ^ e = 0 := by
        intro P hP hPnot
        have hPp : IsPacket (p ^ a * q ^ (b + 1)) p P := by
          by_contra hcon
          exact hPnot (Finset.mem_filter.mpr ⟨hP, hcon⟩)
        exact packet_sum_pow_coprime hp.one_lt hpn hnpos hζ
          (Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))) hPp
      rw [← Finset.sum_subset hsubset hvanish] at hbridge
      rw [Finset.sum_congr rfl (fun P hP => hQsum P hP c), ← Finset.smul_sum]
        at hbridge
      rw [nsmul_eq_mul, mul_eq_zero] at hbridge
      rw [Finset.sum_image hinjQ]
      exact hbridge.resolve_left hqF
    -- the spectrum is torsion one level down
    have hRtor : ∀ z ∈ (Ps.filter
        (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P)).image
        (fun P => (q : F)⁻¹ * ∑ e ∈ P, (ζ ^ q) ^ e), z ^ (p ^ a * q ^ b) = 1 := by
      intro z hz
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨r, hr, rfl⟩ := hQs P hP
      rw [hsv r, ← pow_mul]
      have hexp : q * r * (p ^ a * q ^ b) = (p ^ a * q ^ (b + 1)) * r := by ring
      rw [hexp, pow_mul, hζ.pow_eq_one, one_pow]
    have hζq : IsPrimitiveRoot (ζ ^ q) (p ^ a * q ^ b) :=
      hζ.pow hnpos (by ring)
    -- the induction hypothesis: the spectrum is `μ_p`-closed
    have hRcl := ih a ha (ζ ^ q) hζq _ hRtor hRwin
    -- closure assembly
    intro y hy g hg
    haveI : NeZero (p ^ a * q ^ (b + 1)) := ⟨hnpos.ne'⟩
    obtain ⟨e, helt, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hT y hy)
    have heS : e ∈ expSet (p ^ a * q ^ (b + 1)) ζ T := mem_expSet.mpr ⟨helt, hy⟩
    rw [huni] at heS
    obtain ⟨P, hPmem, heP⟩ := Finset.mem_biUnion.mp heS
    have hPT : ∀ x ∈ P, ζ ^ x ∈ T := by
      intro x hx
      have hxS : x ∈ expSet (p ^ a * q ^ (b + 1)) ζ T := by
        rw [huni]
        exact Finset.mem_biUnion.mpr ⟨P, hPmem, hx⟩
      exact (mem_expSet.mp hxS).2
    by_cases hPp : IsPacket (p ^ a * q ^ (b + 1)) p P
    · exact packet_absorb hp.pos hpn hnpos hζ hPp hPT heP g hg
    · have hPQs : P ∈ Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P) :=
        Finset.mem_filter.mpr ⟨hPmem, hPp⟩
      obtain ⟨r, hr, hPeq⟩ := hQs P hPQs
      subst hPeq
      -- move the spectrum point by `g^q ∈ μ_p`
      have hgq : (g ^ q) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]
      have hspecP : (q : F)⁻¹ * ∑ e' ∈ (Finset.range q).image
          (fun t => r + t * ((p ^ a * q ^ (b + 1)) / q)), (ζ ^ q) ^ e' ∈
          (Ps.filter (fun P => ¬ IsPacket (p ^ a * q ^ (b + 1)) p P)).image
            (fun P => (q : F)⁻¹ * ∑ e ∈ P, (ζ ^ q) ^ e) :=
        Finset.mem_image.mpr ⟨_, hPQs, rfl⟩
      have hmoved := hRcl _ hspecP (g ^ q) hgq
      obtain ⟨P', hP'Qs, hP'val⟩ := Finset.mem_image.mp hmoved
      obtain ⟨r', hr', hP'eq⟩ := hQs P' hP'Qs
      subst hP'eq
      rw [hsv r', hsv r] at hP'val
      -- hP'val : ζ ^ (q * r') = g ^ q * ζ ^ (q * r)
      have hP'T : ∀ x ∈ (Finset.range q).image
          (fun t => r' + t * ((p ^ a * q ^ (b + 1)) / q)), ζ ^ x ∈ T := by
        intro x hx
        have hxS : x ∈ expSet (p ^ a * q ^ (b + 1)) ζ T := by
          rw [huni]
          exact Finset.mem_biUnion.mpr ⟨_, (Finset.mem_filter.mp hP'Qs).1, hx⟩
        exact (mem_expSet.mp hxS).2
      have hζne : (ζ : F) ≠ 0 := by
        intro h0
        have h1 := hζ.pow_eq_one
        rw [h0, zero_pow hnpos.ne'] at h1
        exact zero_ne_one h1
      obtain ⟨t, htlt, hte⟩ := Finset.mem_image.mp heP
      have hqe : (ζ ^ e) ^ q = ζ ^ (q * r) := by
        rw [← hte, ← pow_mul]
        have hmul : q * ((p ^ a * q ^ (b + 1)) / q) = p ^ a * q ^ (b + 1) :=
          Nat.mul_div_cancel' hqn
        have harith : (r + t * ((p ^ a * q ^ (b + 1)) / q)) * q
            = q * r + (p ^ a * q ^ (b + 1)) * t := by
          calc (r + t * ((p ^ a * q ^ (b + 1)) / q)) * q
              = q * r + (q * ((p ^ a * q ^ (b + 1)) / q)) * t := by ring
            _ = q * r + (p ^ a * q ^ (b + 1)) * t := by rw [hmul]
        rw [harith, pow_add, pow_mul ζ (p ^ a * q ^ (b + 1)) t, hζ.pow_eq_one,
          one_pow, mul_one]
      have hr'ne : (ζ : F) ^ r' ≠ 0 := pow_ne_zero _ hζne
      have hhq : (g * ζ ^ e * (ζ ^ r')⁻¹) ^ q = 1 := by
        have h1 : ((ζ : F) ^ r') ^ q = ζ ^ (q * r') := by
          rw [← pow_mul, Nat.mul_comm]
        rw [mul_pow, mul_pow, inv_pow, hqe, h1, hP'val]
        refine mul_inv_cancel₀ ?_
        rw [← hP'val]
        exact pow_ne_zero _ hζne
      have hr'mem : r' ∈ (Finset.range q).image
          (fun t => r' + t * ((p ^ a * q ^ (b + 1)) / q)) :=
        Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hq.pos, by simp⟩
      have habs := packet_absorb hq.pos hqn hnpos hζ ⟨r', hr', rfl⟩ hP'T hr'mem
        (g * ζ ^ e * (ζ ^ r')⁻¹) hhq
      rwa [inv_mul_cancel_right₀ hr'ne] at habs

/-! ## The converse: `μ_p`-closure kills every `p`-coprime power sum -/

/-- **The converse half**: a `μ_p`-closed subset of `μ_n` (`0 ∉ T`, `p ∣ n`) has
vanishing power sums at EVERY exponent not divisible by `p` — each fiber of
`x ↦ x^p` is a full coset (`MixedRadixTower.pow_fiber_coset`) and the twisted
geometric sum dies.  Together with the rung this makes the sparse window an exact
characterization. -/
theorem pow_sum_eq_zero_of_mu_p_closed [DecidableEq F] {p n j : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset F} (h0 : (0 : F) ∉ T)
    (hcl : ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T) (hj : ¬ p ∣ j) :
    ∑ y ∈ T, y ^ j = 0 := by
  classical
  have hξ : IsPrimitiveRoot (ζ ^ (n / p)) p := hζ.pow hn (Nat.div_mul_cancel hpn).symm
  have hmaps : ∀ x ∈ T, x ^ p ∈ T.image (· ^ p) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => x ^ j)]
  refine Finset.sum_eq_zero fun z hz => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hz
  rw [MixedRadixTower.pow_fiber_coset hξ hp.pos h0 hcl hx₀]
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  have hinj : ∀ i ∈ Finset.range p, ∀ i' ∈ Finset.range p,
      (ζ ^ (n / p)) ^ i * x₀ = (ζ ^ (n / p)) ^ i' * x₀ → i = i' := by
    intro i hi i' hi' h
    exact hξ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hi')
      (mul_right_cancel₀ hx₀0 h)
  rw [Finset.sum_image hinj]
  have hcop : Nat.Coprime j p := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hj)
  have hξj : IsPrimitiveRoot ((ζ ^ (n / p)) ^ j) p := hξ.pow_of_coprime j hcop
  have hterm : ∀ i ∈ Finset.range p,
      ((ζ ^ (n / p)) ^ i * x₀) ^ j = ((ζ ^ (n / p)) ^ j) ^ i * x₀ ^ j := by
    intro i _
    rw [mul_pow, ← pow_mul, mul_comm i j, pow_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hξj.geom_sum_eq_zero hp.one_lt,
    zero_mul]

/-- **The sparse window EXACTLY characterizes `μ_p`-closure** on two-prime torsion
domains: the `b+1` power sums at `1, q, …, q^b` vanish iff `T` is `μ_p`-closed. -/
theorem window_iff_mu_p_closed [DecidableEq F] [CharZero F] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {T : Finset F} (h0 : (0 : F) ∉ T) (hT : ∀ y ∈ T, y ^ (p ^ a * q ^ b) = 1) :
    (∀ c, c ≤ b → ∑ y ∈ T, y ^ q ^ c = 0) ↔
      ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T := by
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hpn : p ∣ p ^ a * q ^ b := dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _
  constructor
  · exact fun hwin => window_mu_p_closed hp hq hpq b a ha ζ hζ T hT hwin
  · intro hcl c _
    refine pow_sum_eq_zero_of_mu_p_closed hp hpn hnpos hζ h0 hcl ?_
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-! ## The base-case discharge and the unconditional tower -/

/-- **The `hBase` discharge**: the rung, packaged in the exact hypothesis shape of
`MixedRadixTower.prime_climb_conditional` at every level `(p^a·q^b)/p^k` (`k < a`),
window `q^b + 1`. -/
lemma base_discharge [DecidableEq F] [CharZero F] {p q a b k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hk : k < a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) :
    ∀ T : Finset F, (∀ y ∈ T, y ^ ((p ^ a * q ^ b) / p ^ k) = 1) →
      (∀ j, 1 ≤ j → j < q ^ b + 1 → ∑ y ∈ T, y ^ j = 0) →
      ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T := by
  intro T hTtor hTwin
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hksplit : p ^ a * q ^ b = p ^ k * (p ^ (a - k) * q ^ b) := by
    rw [← Nat.mul_assoc, pow_mul_pow_sub p hk.le]
  have hdiv : (p ^ a * q ^ b) / p ^ k = p ^ (a - k) * q ^ b := by
    rw [hksplit, Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
  rw [hdiv] at hTtor
  have hξ : IsPrimitiveRoot (ζ ^ p ^ k) (p ^ (a - k) * q ^ b) := hζ.pow hnpos hksplit
  exact window_mu_p_closed hp hq hpq b (a - k) (by omega) _ hξ T hTtor
    (fun c hc => hTwin (q ^ c) (Nat.one_le_pow _ _ hq.pos)
      (Nat.lt_succ_of_le (Nat.pow_le_pow_right hq.pos hc)))

/-- **THE PARTIAL CLIMB, UNCONDITIONAL**: on `μ_{p^a·q^b}` an interval window
`1 ≤ j < p^(t-1)·(q^b+1)` forces closure under `μ_{p^t}` (`t ≤ a`) — the
rung-resolved form of the O70 divisor-coset law along the `p`-direction. -/
theorem two_prime_partial_climb [DecidableEq F] [CharZero F] {p q a b t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ht : t ≤ a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset F} (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ (p ^ a * q ^ b) = 1)
    (hwin : ∀ j, 1 ≤ j → j < p ^ (t - 1) * (q ^ b + 1) → ∑ x ∈ S, x ^ j = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ p ^ t = 1 → h * x ∈ S := by
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  refine MixedRadixTower.prime_climb_conditional hp.pos hnpos hζ h0 hS
    (fun _ => q ^ b + 1) t (dvd_mul_of_dvd_left (pow_dvd_pow p ht) _) ?_ ?_
  · intro k hk j hj1 hj2
    refine hwin j hj1 (lt_of_lt_of_le hj2 ?_)
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))
  · intro k hk T _ hTtor hTwin
    exact base_discharge hp hq hpq (by omega) hζ T hTtor hTwin

/-- **THE UNCONDITIONAL TWO-PRIME TOWER** (O95's separation closed): on the exact
two-prime level `n = p^a·q^b`, an interval window

  `1 ≤ j < max (p^(a-1)·(q^b+1)) (q^(b-1)·(p^a+1))`

of vanishing power sums forces closure under the FULL `μ_{p^a·q^b}` — every
classical base case of `MixedRadixTower.two_prime_tower_conditional` is discharged
by the rung.  The first unconditional mixed-radix tower instance. -/
theorem two_prime_tower_window [DecidableEq F] [CharZero F] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset F} (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ (p ^ a * q ^ b) = 1)
    (hwin : ∀ j, 1 ≤ j →
      j < max (p ^ (a - 1) * (q ^ b + 1)) (q ^ (b - 1) * (p ^ a + 1)) →
      ∑ x ∈ S, x ^ j = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ (p ^ a * q ^ b) = 1 → h * x ∈ S := by
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  refine MixedRadixTower.two_prime_tower_conditional hp.pos hq.pos
    ((Nat.coprime_primes hp hq).mpr hpq) hnpos dvd_rfl hζ h0 hS
    (fun _ => q ^ b + 1) (fun _ => p ^ a + 1) ?_ ?_ ?_ ?_
  · -- the `p`-climb windows sit inside the master window
    intro k hk j hj1 hj2
    refine hwin j hj1 (lt_of_lt_of_le (lt_of_lt_of_le hj2 ?_) (le_max_left _ _))
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))
  · -- the `p`-side base cases: the rung
    intro k hk T _ hTtor hTwin
    exact base_discharge hp hq hpq hk hζ T hTtor hTwin
  · -- the `q`-climb windows sit inside the master window
    intro k hk j hj1 hj2
    refine hwin j hj1 (lt_of_lt_of_le (lt_of_lt_of_le hj2 ?_) (le_max_right _ _))
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq.pos (by omega))
  · -- the `q`-side base cases: the rung with the primes swapped
    intro k hk T _ hTtor hTwin
    have hζ' : IsPrimitiveRoot ζ (q ^ b * p ^ a) := by
      rwa [Nat.mul_comm] at hζ
    have hnum : (q ^ b * p ^ a) / q ^ k = (p ^ a * q ^ b) / q ^ k := by
      rw [Nat.mul_comm]
    have hTtor' : ∀ y ∈ T, y ^ ((q ^ b * p ^ a) / q ^ k) = 1 := by
      rw [hnum]
      exact hTtor
    exact base_discharge hq hp (Ne.symm hpq) hk hζ' T hTtor' hTwin

/-- **The empty-or-full endpoint**: at exact level `n = p^a·q^b` the master window
collapses every subset to `∅` or ALL of `μ_n` — the `d = n` stratum of the O70
divisor-coset law. -/
theorem two_prime_window_empty_or_full [DecidableEq F] [CharZero F] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset F} (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ (p ^ a * q ^ b) = 1)
    (hwin : ∀ j, 1 ≤ j →
      j < max (p ^ (a - 1) * (q ^ b + 1)) (q ^ (b - 1) * (p ^ a + 1)) →
      ∑ x ∈ S, x ^ j = 0) :
    S = ∅ ∨ ∀ z : F, z ^ (p ^ a * q ^ b) = 1 → z ∈ S := by
  rcases Finset.eq_empty_or_nonempty S with h | ⟨x, hx⟩
  · exact Or.inl h
  · refine Or.inr fun z hz => ?_
    have hx0 : x ≠ 0 := fun h' => h0 (h' ▸ hx)
    have hcl := two_prime_tower_window hp hq hpq ha hb hζ h0 hS hwin x hx
      (z * x⁻¹) ?_
    · rwa [inv_mul_cancel_right₀ hx0] at hcl
    · rw [mul_pow, hz, one_mul, inv_pow, hS x hx, inv_one]

/-! ## Instances: the M31 smooth domain and `n = 2^a·3` -/

/-- **The M31 smooth-domain window law**: on `μ_18` (the 2-3-smooth multiplicative
domain of `F_{2^31−1}`, `18 = 2·3²`) a vanishing window `1 ≤ j < 10` forces closure
under the full `μ_18` — sharp per the probe (the rotated `μ_9`-coset survives
`1 ≤ j < 9`). -/
theorem m31_smooth_window_law [DecidableEq F] [CharZero F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 18) {S : Finset F} (h0 : (0 : F) ∉ S)
    (hS : ∀ x ∈ S, x ^ 18 = 1)
    (hwin : ∀ j, 1 ≤ j → j < 10 → ∑ x ∈ S, x ^ j = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ 18 = 1 → h * x ∈ S := by
  have h18 : (18 : ℕ) = 2 ^ 1 * 3 ^ 2 := by norm_num
  rw [h18] at hζ hS ⊢
  refine two_prime_tower_window Nat.prime_two Nat.prime_three (by norm_num)
    one_pos (by norm_num) hζ h0 hS ?_
  intro j hj1 hj2
  refine hwin j hj1 ?_
  norm_num at hj2
  omega

/-- **The `n = 2^a·3` window law** (O95's item (iii)): on `μ_{2^a·3}` a vanishing
window `1 ≤ j < 2^(a+1)` forces closure under the full `μ_{2^a·3}`. -/
theorem two_pow_three_window_law [DecidableEq F] [CharZero F] {a : ℕ} (ha : 0 < a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ a * 3)) {S : Finset F}
    (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ (2 ^ a * 3) = 1)
    (hwin : ∀ j, 1 ≤ j → j < 2 ^ (a + 1) → ∑ x ∈ S, x ^ j = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ (2 ^ a * 3) = 1 → h * x ∈ S := by
  have h3 : (2 : ℕ) ^ a * 3 = 2 ^ a * 3 ^ 1 := by norm_num
  rw [h3] at hζ hS ⊢
  refine two_prime_tower_window Nat.prime_two Nat.prime_three (by norm_num) ha
    one_pos hζ h0 hS ?_
  intro j hj1 hj2
  refine hwin j hj1 ?_
  have h1 : 2 ^ (a - 1) * (3 ^ 1 + 1) = 2 ^ (a + 1) := by
    have h4 : (3 : ℕ) ^ 1 + 1 = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add]
    congr 1
    omega
  have h2 : 3 ^ (1 - 1) * (2 ^ a + 1) ≤ 2 ^ (a + 1) := by
    have h5 : (1 : ℕ) ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have h6 : (2 : ℕ) ^ (a + 1) = 2 ^ a + 2 ^ a := by rw [pow_succ]; ring
    simp only [Nat.sub_self, pow_zero, one_mul]
    omega
  exact lt_of_lt_of_le hj2 (max_le (le_of_eq h1) h2)

/-! ## Teeth (fired at `ℂ`) -/

private lemma exp_root_primitive (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- The rung FIRED at `ℂ`: `T = {1, −1} ⊆ μ_12` kills the sparse window `{1, 3}`
(`1 + (−1) = 0` and `1³ + (−1)³ = 0`), so the rung concludes `μ_2`-closure — the
hypotheses are jointly satisfiable on a nonempty set and the conclusion lands. -/
example : ∀ y ∈ ({1, -1} : Finset ℂ), ∀ g : ℂ, g ^ 2 = 1 →
    g * y ∈ ({1, -1} : Finset ℂ) := by
  have hζ12 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (12 : ℕ)))
      (2 ^ 2 * 3 ^ 1) := by
    have h := exp_root_primitive 12 (by norm_num)
    norm_num at h ⊢
    exact h
  refine window_mu_p_closed Nat.prime_two Nat.prime_three (by norm_num) 1 2
    (by norm_num) _ hζ12 {1, -1} ?_ ?_
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · norm_num
    · rw [Finset.mem_singleton] at hz
      subst hz
      norm_num
  · intro c hc
    interval_cases c
    · rw [Finset.sum_pair (by norm_num : (1 : ℂ) ≠ -1)]
      norm_num
    · rw [Finset.sum_pair (by norm_num : (1 : ℂ) ≠ -1)]
      norm_num

end TwoPrimeWindowLaw

#print axioms TwoPrimeWindowLaw.window_mu_p_closed
#print axioms TwoPrimeWindowLaw.pow_sum_eq_zero_of_mu_p_closed
#print axioms TwoPrimeWindowLaw.window_iff_mu_p_closed
#print axioms TwoPrimeWindowLaw.base_discharge
#print axioms TwoPrimeWindowLaw.two_prime_partial_climb
#print axioms TwoPrimeWindowLaw.two_prime_tower_window
#print axioms TwoPrimeWindowLaw.two_prime_window_empty_or_full
#print axioms TwoPrimeWindowLaw.m31_smooth_window_law
#print axioms TwoPrimeWindowLaw.two_pow_three_window_law
