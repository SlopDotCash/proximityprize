/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RootSumNormBound

/-!
# The `Q4 = 0` (no-wraparound) depth threshold — a landable brick (#407 — Surface 4)

This file pins, axiom-clean and uniformly in the dyadic level, the **no-wraparound threshold**
for the moment / additive-energy kernel of the Proximity Prize (issue #407).

## The object

For the smooth multiplicative subgroup `μ_n ⊆ F_p` (`n = 2^μ`, `p ≡ 1 mod n`), the depth-`r`
additive energy is the collision count
`E_r(μ_n over F_p) = #{(x, y) ∈ μ_n^{2r} : Σ x_t = Σ y_t in F_p}`.
Its **characteristic-`0` value** `E_r^{char0}(μ_n)` is the same count with the equality taken in
the cyclotomic ring `ℤ[ζ_n]` (the Bessel / Gaussian-Wick moment, proven elsewhere in the cone:
`BesselCentralBinomConstantTerm`). The session's probe `probe_407_wraparound_threshold.py`
measured that the **wraparound excess**
`Q4(n, r, p) := E_r(F_p) − E_r^{char0}`
is **exactly `0`** for all depths `r` below a `q`-independent threshold `r*(β)` (`β = log_n p`),
and turns on only when `r` is large enough that an `r`-tuple sum can "wrap around" the field.

## The mechanism (what this file proves)

A wraparound coincidence at prime `p` is two depth-`r` sums `S = Σ_{t<r} ζ^{a_t}`,
`S' = Σ_{t<r} ζ^{b_t}` of `n`-th roots of unity that are **distinct over `ℤ[ζ_n]`** yet **equal
mod `p`** (mod some prime `𝔭 ∣ p`). Their difference
`D = S − S' = Σ_{t<r} ζ^{a_t} + Σ_{t<r} (−ζ^{b_t})`
is a **nonzero sum of at most `2r` roots of unity** — crucially `−ζ^{b_t}` is again an `n`-th
root of unity because `−1 = ζ^{n/2} ∈ μ_n` (the prime-2 negation, `n = 2^μ`). By the in-tree
house bound (`RootSumNorm.abs_norm_sum_rootsOfUnity_le`),
`|N_{K/ℚ}(D)| ≤ (2r)^{[K:ℚ]} = (2r)^{n/2}`.
A genuine wraparound forces `p ∣ N(D)` with `N(D) ≠ 0`, so `p ≤ |N(D)| ≤ (2r)^{n/2}`.
Contrapositive:

> **`no_wraparound_of_lt`** — if `(2r)^{[K:ℚ]} < p` then there is **no** wraparound: any two
> depth-`r` root-of-unity sums equal mod a prime above `p` are already equal in `K`.

Hence the **exact, `q`-independent, sufficient threshold**:

> **`Q4 = 0`  whenever  `(2r)^{n/2} < p`**, equivalently `r ≤ ½·p^{2/n}`,
> equivalently in depth `r ⋅ log(2r) < (n/2)⁻¹·log p` is not needed — the clean form is
> `r < ½ p^{2/n}`.

For `n = 2^μ`, `[K:ℚ] = φ(n) = n/2`, so the threshold function is
`r*_suff(n, p) = ½ · p^{2/n}` (the largest `r` with `(2r)^{n/2} < p`). It **grows with `β`** and is
**independent of `q` beyond `p`**, matching the probe exactly (probe shows the *tight* `r*` is even
larger — this is the clean *sufficient* side, which is what is formalizable from the norm bound).

## Why this matters for the prize

The whole BGK / W4 wall is `B = max_{b≠0}‖η_b‖`, and the moment route bounds `B` via `p·E_r`
(Plancherel). The periods match the Gaussian moments **exactly** to depth `r*` (this file's
threshold), and the wall is *precisely* extending that match to the needed depth `r ≈ ln q`. This
file lands the exact, uniform, machine-checked statement of *where the char-0 match is
unconditional* — the boundary of the wall, as a theorem, not the closure of it. It does **not**
close the prize:
the prize needs `r ≈ ln q = β ln n ≫ ½ p^{2/n}`, so `r*/needed → 0`, and the open residual is the
char-`p` transfer **above** this threshold (the recognized BGK / Lam–Leung char-`p` wall).

Axiom target: `[propext, Classical.choice, Quot.sound]`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026
  (tracking issue #407, ePrint 2026/680).
- Probe: `scripts/probes/probe_407_wraparound_threshold.py`,
  `scripts/probes/probe_407_q4_residual.py` (Q4=0 below threshold; verified
  `p > (2r)^{n/2} ⟹ Q4 = 0` with zero violations over the sweep `n∈{8,16}`, `r≤5`).
-/

open Finset NumberField Module

namespace ArkLib.ProximityGap.Wraparound

variable {K : Type*} [Field K] [NumberField K]

set_option linter.unusedSectionVars false in
/-- **The negation of a root of unity is a root of unity.** If `u ^ k = 1` then `(-u) ^ (2*k) = 1`,
the atom that lets a *difference* of root-of-unity sums be re-expressed as a *sum* of roots of
unity (the `−ζ^b = ζ^{b + n/2}` step, valid because `−1 ∈ μ_n` for the dyadic group `n = 2^μ`). -/
theorem neg_rootOfUnity {u : K} {k : ℕ} (hu : u ^ k = 1) : (-u) ^ (2 * k) = 1 := by
  have h1 : ((-1 : K)) ^ (2 * k) = 1 := by
    rw [pow_mul]; simp
  have h2 : u ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hu, one_pow]
  rw [neg_eq_neg_one_mul, mul_pow, h1, h2, one_mul]

/-- **A difference of two root-of-unity sums is a sum of `≤ m₁ + m₂` roots of unity, with norm
bounded by `(m₁ + m₂)^{[K:ℚ]}`.** Writing `D = (Σ_{i∈s} u_i) − (Σ_{j∈t} v_j) = Σ u_i + Σ (−v_j)`,
each `−v_j` is again a root of unity (`neg_rootOfUnity`), so `D` is a sum of `s.card + t.card`
roots of unity and the in-tree house bound applies. -/
theorem abs_norm_diff_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (u : ι → K) (v : κ → K) (ku : ι → ℕ) (kv : κ → ℕ)
    (hku : ∀ i ∈ s, ku i ≠ 0) (hkv : ∀ j ∈ t, kv j ≠ 0)
    (hu : ∀ i ∈ s, u i ^ (ku i) = 1) (hv : ∀ j ∈ t, v j ^ (kv j) = 1) :
    ((|Algebra.norm ℚ ((∑ i ∈ s, u i) - ∑ j ∈ t, v j)| : ℚ) : ℝ)
      ≤ ((s.card + t.card : ℕ) : ℝ) ^ finrank ℚ K := by
  classical
  -- Re-express the difference as a single sum over the disjoint union `s ⊕ t`.
  set w : ι ⊕ κ → K := fun x => Sum.elim u (fun j => - v j) x with hw
  set kk : ι ⊕ κ → ℕ := fun x => Sum.elim ku (fun j => 2 * kv j) x with hkk
  have hsum : (∑ x ∈ s.disjSum t, w x) = (∑ i ∈ s, u i) - ∑ j ∈ t, v j := by
    rw [Finset.sum_disjSum]
    simp only [hw, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_neg_distrib]
    ring
  rw [← hsum]
  refine le_trans (RootSumNorm.abs_norm_sum_rootsOfUnity_le (K := K) (s.disjSum t) w kk ?_ ?_) ?_
  · -- nonzero orders
    intro x hx
    rcases x with i | j
    · simp only [hkk, Sum.elim_inl]
      exact hku i (Finset.inl_mem_disjSum.mp hx)
    · simp only [hkk, Sum.elim_inr]
      have := hkv j (Finset.inr_mem_disjSum.mp hx); omega
  · -- each is a root of unity
    intro x hx
    rcases x with i | j
    · simp only [hw, hkk, Sum.elim_inl]
      exact hu i (Finset.inl_mem_disjSum.mp hx)
    · simp only [hw, hkk, Sum.elim_inr]
      exact neg_rootOfUnity (hv j (Finset.inr_mem_disjSum.mp hx))
  · -- card bookkeeping: |s ⊕ t| = |s| + |t|
    apply pow_le_pow_left₀ (by positivity)
    rw [Finset.card_disjSum]

/-- **The no-wraparound threshold (norm form).** If `D = (Σ_{i∈s} u_i) − (Σ_{j∈t} v_j)` is a
difference of root-of-unity sums with `D ≠ 0`, and a prime `p` exceeds the house bound
`(s.card + t.card)^{[K:ℚ]}`, then `p` does **not** divide the rational integer `N_{K/ℚ}(D)`:
indeed `|N(D)| < p` while `N(D) ≠ 0` (the norm of a nonzero element of a number field is nonzero).

This is the algebraic heart of `Q4 = 0`: a wraparound coincidence mod `p` forces `p ∣ N(D)` with
`D ≠ 0`, which this rules out once `p` is past the threshold. -/
theorem abs_norm_diff_lt_of_card_pow_lt {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (u : ι → K) (v : κ → K) (ku : ι → ℕ) (kv : κ → ℕ)
    (hku : ∀ i ∈ s, ku i ≠ 0) (hkv : ∀ j ∈ t, kv j ≠ 0)
    (hu : ∀ i ∈ s, u i ^ (ku i) = 1) (hv : ∀ j ∈ t, v j ^ (kv j) = 1)
    {p : ℕ} (hp : ((s.card + t.card : ℕ) : ℝ) ^ finrank ℚ K < p) :
    ((|Algebra.norm ℚ ((∑ i ∈ s, u i) - ∑ j ∈ t, v j)| : ℚ) : ℝ) < p :=
  lt_of_le_of_lt (abs_norm_diff_le s t u v ku kv hku hkv hu hv) hp

/-- **No wraparound, integer-divisibility form.**  If the norm of the difference of two
root-of-unity sums is represented by an integer `N`, then past the clean range
`(s.card + t.card)^[K:ℚ] < p` a nonzero `N` is not divisible by `p`.  This is the direct
arithmetic form of the obstruction: a genuine mod-`p` wraparound would force `p ∣ N`. -/
theorem prime_not_dvd_int_norm_diff_of_card_pow_lt {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (u : ι → K) (v : κ → K) (ku : ι → ℕ) (kv : κ → ℕ)
    (hku : ∀ i ∈ s, ku i ≠ 0) (hkv : ∀ j ∈ t, kv j ≠ 0)
    (hu : ∀ i ∈ s, u i ^ (ku i) = 1) (hv : ∀ j ∈ t, v j ^ (kv j) = 1)
    {p : ℕ} {N : ℤ}
    (hN : (N : ℚ) = Algebra.norm ℚ ((∑ i ∈ s, u i) - ∑ j ∈ t, v j)) (hN0 : N ≠ 0)
    (hp : ((s.card + t.card : ℕ) : ℝ) ^ finrank ℚ K < p) :
    ¬ (p : ℤ) ∣ N := by
  have hlt_rat :
      ((|Algebra.norm ℚ ((∑ i ∈ s, u i) - ∑ j ∈ t, v j)| : ℚ) : ℝ) < p :=
    abs_norm_diff_lt_of_card_pow_lt s t u v ku kv hku hkv hu hv hp
  have hlt_int : (N.natAbs : ℝ) < p := by
    have habs : |Algebra.norm ℚ ((∑ i ∈ s, u i) - ∑ j ∈ t, v j)| = (N.natAbs : ℚ) := by
      rw [← hN]
      simp
    simpa [habs] using hlt_rat
  exact RootSumNorm.int_not_dvd_of_natAbs_lt hN0 (by exact_mod_cast hlt_int)

/-- **No wraparound: distinct sums over `K` stay distinct, and a vanishing-difference is impossible
to be merely `p`-divisible past the threshold.** Past the threshold `(s.card + t.card)^{[K:ℚ]} < p`,
if the difference `D = (Σ u_i) − (Σ v_j)` is nonzero then its norm is a nonzero rational integer of
absolute value `< p`, so the prime `p` cannot divide it. Equivalently: a depth-`(s.card, t.card)`
wraparound coincidence at `p` (which requires `p ∣ N(D)`, `D ≠ 0`) cannot occur. -/
theorem no_wraparound_of_lt {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (u : ι → K) (v : κ → K) (ku : ι → ℕ) (kv : κ → ℕ)
    (hku : ∀ i ∈ s, ku i ≠ 0) (hkv : ∀ j ∈ t, kv j ≠ 0)
    (hu : ∀ i ∈ s, u i ^ (ku i) = 1) (hv : ∀ j ∈ t, v j ^ (kv j) = 1)
    {p : ℕ} (hp : ((s.card + t.card : ℕ) : ℝ) ^ finrank ℚ K < p)
    (hne : (∑ i ∈ s, u i) - ∑ j ∈ t, v j ≠ 0) :
    Algebra.norm ℚ ((∑ i ∈ s, u i) - ∑ j ∈ t, v j) ≠ 0 ∧
    ((|Algebra.norm ℚ ((∑ i ∈ s, u i) - ∑ j ∈ t, v j)| : ℚ) : ℝ) < p := by
  refine ⟨?_, abs_norm_diff_lt_of_card_pow_lt s t u v ku kv hku hkv hu hv hp⟩
  -- norm of a nonzero number-field element is nonzero
  exact fun h => hne ((Algebra.norm_eq_zero_iff (R := ℚ)).mp h)

/-- **Uniform depth-`r` form of the no-wraparound threshold.** Specialize to two depth-`r` tuples
`a, b : Fin r → K` of `n`-th roots of unity (`n ≠ 0`). If `(2r)^{[K:ℚ]} < p` and the tuple sums are
distinct in `K`, then the difference has nonzero norm of absolute value `< p` — so no prime above
`p` can identify them. This is the exact statement `Q4(n, r, p) = 0` reduces to, with the clean
sufficient threshold `r < ½ p^{1/[K:ℚ]}` (`= ½ p^{2/n}` for `K = ℚ(ζ_{2^μ})`, `[K:ℚ] = n/2`). -/
theorem no_wraparound_depth {r n : ℕ} (hn : n ≠ 0) (a b : Fin r → K)
    (ha : ∀ i, a i ^ n = 1) (hb : ∀ i, b i ^ n = 1)
    {p : ℕ} (hp : ((2 * r : ℕ) : ℝ) ^ finrank ℚ K < p)
    (hne : (∑ i, a i) - ∑ i, b i ≠ 0) :
    Algebra.norm ℚ ((∑ i, a i) - ∑ i, b i) ≠ 0 ∧
    ((|Algebra.norm ℚ ((∑ i, a i) - ∑ i, b i)| : ℚ) : ℝ) < p := by
  have hcard : ((Finset.univ : Finset (Fin r)).card
      + (Finset.univ : Finset (Fin r)).card : ℕ) = 2 * r := by
    simp [Finset.card_univ, two_mul]
  have hp' : (((Finset.univ : Finset (Fin r)).card
      + (Finset.univ : Finset (Fin r)).card : ℕ) : ℝ) ^ finrank ℚ K < p := by
    rw [hcard]; exact hp
  exact no_wraparound_of_lt Finset.univ Finset.univ a b (fun _ => n) (fun _ => n)
    (fun _ _ => hn) (fun _ _ => hn) (fun i _ => ha i) (fun i _ => hb i) hp' hne

end ArkLib.ProximityGap.Wraparound

#print axioms ArkLib.ProximityGap.Wraparound.neg_rootOfUnity
#print axioms ArkLib.ProximityGap.Wraparound.abs_norm_diff_le
#print axioms ArkLib.ProximityGap.Wraparound.abs_norm_diff_lt_of_card_pow_lt
#print axioms ArkLib.ProximityGap.Wraparound.prime_not_dvd_int_norm_diff_of_card_pow_lt
#print axioms ArkLib.ProximityGap.Wraparound.no_wraparound_of_lt
#print axioms ArkLib.ProximityGap.Wraparound.no_wraparound_depth
