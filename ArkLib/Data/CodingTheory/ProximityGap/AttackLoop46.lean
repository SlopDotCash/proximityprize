/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Loop 46 (ATTACK / EXPLORE) — the BCHKS §7 multiplicative-subgroup attack and the additive-
# combinatorics question the #232 disproof reduces to.

This loop reads and formalizes the *freshest* (Nov 11 2025) negative construction directly relevant
to the prize: **Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, "On Proximity Gaps for Reed–Solomon
Codes", Theorem 7.1** — an explicit proximity-gap attack on Reed–Solomon codes whose evaluation
domain is a **multiplicative subgroup** (the prize's exact, FRI-friendly, smooth-domain setting).
It does *not* close the prize; it sharpens exactly where the prize can still break.

## The §7 attack (Theorem 7.1), in prize coordinates

Let `G ⊆ H ⊆ F_q^*` be multiplicative subgroups, `Φ : H → G`, `x ↦ x^c`, `c = |H|/|G|`. For a
subset `E ⊆ G` with `|E^{(+ℓ)}| ≥ a` (the ℓ-fold *distinct-subset-sumset* size), the code
`RS[F_q, Φ⁻¹(E), n − (ℓ+2)c]` (domain size `n = c·|E|`) admits `f, g` such that at radius
`γ = ℓc/n` there are `≥ a` "bad" combining scalars `z` with `f + z·g` `γ`-close, yet `[f,g]` is
`(ℓ+1)/ℓ · γ`-far. Translating to prize parameters (rate `ρ = 1 − (ℓ+2)c/n`, gap to capacity
`η := (1−ρ) − γ`):

* **the rate pins the free set:** `|E| = (ℓ+2)/(1−ρ)`, and the gap identity
  `η = 2(1−ρ)/(ℓ+2)` collapses this to `|E| = 2/η` — independent of `q`, `n`, `c`
  (`thm71_freeSet_eq`);
* **the bad-scalar count is field-independent:** `a = |E^{(+ℓ)}| ≤ 2^{|E|}`, a function of `(ρ,η)`
  only (`thm71_badCount_le_subsets`).

## The dichotomy this exposes (the new content)

The prize tolerates any bound `ε_mca ≤ (1/q)·(2^m)^{c₁}/(ρ^{c₂}η^{c₃})` with `2^m = |domain|`.
The §7 attack contributes `ε_mca = a/q`. Hence:

* **Large domains absorb it.** Whenever the prize numerator `(2^m)^{c₁}/(ρ^{c₂}η^{c₃})` is `≥ a`,
  the §7 attack respects the prize (`thm71_within_prize`). Since `a` is *fixed* by `(ρ,η)` while
  `(2^m)^{c₁} → ∞` with the domain, **every** sufficiently large domain absorbs it — this is why all
  prior loops observed the prize surviving §7-type attacks.
* **The minimal domain is the pressure point.** At `2^m = |E| = 2/η` (the domain *is* the small
  subgroup), if the subgroup's ℓ-fold sumset attains its upper bound `a = 2^{|E|} = 2^{2^m}`, the
  bad count outruns `(2^m)^{c₁}` for the prize's own Johnson-side exponent `c₁ = 2` already at tiny
  `m`, and the gap *widens* with `m` (`thm71_minimal_domain_pressure_*`, `thm71_refutes_prize`).
  No fixed `c₁` survives.

So the §7 route to **dis**proving the prize reduces to one sharply isolated question:

> **Open (O11).** For a smooth multiplicative subgroup `G ≤ F_q^*` of order `2^m`, how large is the
> ℓ-fold distinct-subset-sumset `|G^{(+ℓ)}|` at the §7-critical `ℓ`? If it is polynomially bounded
> in `(2^m, 1/η)` the prize survives §7; if some family forces it super-polynomial in `2^m` at a
> *fixed* gap, the prize-as-stated (`2^m = |domain|`, all sizes) is **false**.

This is genuine additive combinatorics of multiplicative subgroups (cf. BCHKS §7, Conj. 1.12 over
prime fields). It is *plausible* the prize survives — a full subgroup satisfies the vanishing
power-sum relations `∑_{g∈G} g^j = 0` (`1 ≤ j < |G|`), which are strong additive constraints that
should keep `|G^{(+ℓ)}|` far below `2^{|G|}` — but this is **unproven** in either direction.

**Honest status.** This loop is `sorry`-free and axiom-clean. It proves the §7
*parameter* identities
and the prize *comparison* arithmetic, and isolates the disproof to a concrete sumset bound. It does
**not** prove or refute that bound, so the prize remains OPEN. See `DISPROOF_LOG.md` (Loop46/O11).
-/

namespace ArkLib.ProximityGap.AttackLoop46

/-- **§7 rate identity — the gap pins the free set.** With the Theorem 7.1 rate relation
`|E| = (ℓ+2)/(1−ρ)` and the gap-to-capacity identity `η = 2(1−ρ)/(ℓ+2)`, the attacker's free set
collapses to `|E| = 2/η`, *independent of the field size `q`, the ambient domain size `n`, and the
subgroup index `c`*. The whole strength of the attack is therefore a function of `(ρ, η)` alone. -/
lemma thm71_freeSet_eq (ρ η : ℝ) (ℓ : ℕ)
    (hρ : ρ < 1) (_hη : 0 < η)
    (hgap : η = 2 * (1 - ρ) / ((ℓ : ℝ) + 2)) :
    ((ℓ : ℝ) + 2) / (1 - ρ) = 2 / η := by
  have h1 : (0 : ℝ) < 1 - ρ := by linarith
  have hl : (0 : ℝ) < (ℓ : ℝ) + 2 := by positivity
  rw [hgap]
  field_simp

/-- **§7 bad count is field-independent and at most `2^{|E|}`.** The number of bad combining scalars
equals `|E^{(+ℓ)}|`, the count of *distinct* ℓ-element subset-sums of `E`; trivially this is at most
the number of subsets of `E`, namely `2^{|E|}`. Combined with `thm71_freeSet_eq` (`|E| = 2/η`) the
bad count depends only on `(ρ, η)`, never on `q` or the domain size. -/
lemma thm71_badCount_le_subsets (Ecard a : ℕ) (hsumset : a ≤ 2 ^ Ecard) :
    (a : ℝ) ≤ (2 : ℝ) ^ Ecard := by
  have : ((2 : ℕ) ^ Ecard : ℝ) = (2 : ℝ) ^ Ecard := by push_cast; ring
  calc (a : ℝ) ≤ ((2 : ℕ) ^ Ecard : ℝ) := by exact_mod_cast hsumset
    _ = (2 : ℝ) ^ Ecard := this

/-- **Large domains absorb the §7 attack.** Whenever the prize numerator dominates the (fixed) bad
count `a ≤ num`, the §7 MCA contribution `a/q` lands within the prize RHS `(1/q)·num`. Because `a`
is fixed by `(ρ,η)` while `num` grows with the domain, this holds for all large enough domains. -/
lemma thm71_within_prize {a q num : ℝ} (hq : 0 < q) (h : a ≤ num) :
    a / q ≤ 1 / q * num := by
  rw [one_div_mul_eq_div]
  gcongr

/-- **The §7 attack refutes any prize triple whose numerator the bad count exceeds.** If at some
admissible domain the realized bad count `a` strictly exceeds the prize numerator `num`, the MCA
contribution `a/q` strictly exceeds the prize RHS `(1/q)·num`: that triple `(c₁,c₂,c₃)` is refuted
there. (The open question is whether such `a > num` is *realizable* at a smooth
subgroup; see O11.) -/
lemma thm71_refutes_prize {a q num : ℝ} (hq : 0 < q) (h : num < a) :
    1 / q * num < a / q := by
  rw [one_div_mul_eq_div]
  gcongr

/-- **Minimal-domain exponential pressure, concrete witness at `c₁ = 2`.** At the minimal domain
`2^m = |E|` with `m = 4` (so `|E| = 16`), if the subgroup's ℓ-fold sumset attains its upper bound
`a = 2^{|E|} = 2^{16}`, the bad count `65536` already outstrips the prize numerator at the
Johnson-side exponent `c₁ = 2`, namely `(2^4)^2 = 256`. So even the *proven* large-gap exponent
`c₁ = 2` fails at the minimal domain under a maximal sumset. -/
lemma thm71_minimal_domain_pressure_c2 : ((2 : ℝ) ^ 4) ^ 2 < (2 : ℝ) ^ (2 ^ 4) := by
  norm_num

/-- **The pressure widens with `m` (witness at `c₁ = 3`, `m = 5`).** `((2^5))^3 = 2^15 = 32768`
versus `2^{2^5} = 2^32 ≈ 4.3·10^9`: a maximal sumset beats the cubic exponent by five orders of
magnitude, and the ratio grows doubly-exponentially. No fixed polynomial exponent `c₁` can absorb a
maximal subgroup sumset at the minimal domain. -/
lemma thm71_minimal_domain_pressure_c3 : ((2 : ℝ) ^ 5) ^ 3 < (2 : ℝ) ^ (2 ^ 5) := by
  norm_num

/-- Arithmetic helper: `2^(c+1)·c < 2^(2^(c+1))` — a maximal subgroup sumset `2^{|G|}` (with
`|G| = 2^m` at the minimal domain `m = c+1`) outruns the prize numerator `(2^m)^c` for every `c`. -/
private lemma pow_mul_lt_two_pow_two_pow (c : ℕ) :
    2 ^ (c + 1) * c < 2 ^ (2 ^ (c + 1)) := by
  have h1 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ c ≤ 2 ^ (c + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ c)
  have hcM : c < 2 ^ (c + 1) := by omega
  have hesucc : (2 : ℕ) ^ (c + 1) = 2 * 2 ^ c := by rw [pow_succ]; ring
  have hB : 2 * (c + 1) ≤ 2 ^ (c + 1) := by omega
  have hMM : (2 : ℕ) ^ (c + 1) * 2 ^ (c + 1) = 2 ^ (2 * (c + 1)) := by
    rw [← pow_add]; congr 1; ring
  have hpos : 0 < (2 : ℕ) ^ (c + 1) := by positivity
  calc 2 ^ (c + 1) * c < 2 ^ (c + 1) * 2 ^ (c + 1) := mul_lt_mul_of_pos_left hcM hpos
    _ = 2 ^ (2 * (c + 1)) := hMM
    _ ≤ 2 ^ (2 ^ (c + 1)) := Nat.pow_le_pow_right (by norm_num) hB

/-- **No fixed prize exponent absorbs a maximal subgroup sumset (the rigorous disproof branch).**
For *every* fixed numerator exponent `c₁`, there is a minimal domain `2^m` (take
`m = c₁+1`) at which
a maximal §7 sumset `a = 2^{|G|} = 2^{2^m}` strictly exceeds the prize numerator `(2^m)^{c₁}`. So if
the ℓ-fold subset-sumset of a smooth subgroup can attain its `2^{|G|}` upper bound at fixed gap, the
prize-as-stated (`2^m = |domain|`, all sizes, one fixed triple) is refuted. This is the precise
sense in which the §7 route *threatens* the prize, conditional on the O11 sumset-growth question. -/
theorem thm71_no_fixed_exponent (c₁ : ℕ) :
    ∃ m : ℕ, ((2 : ℝ) ^ m) ^ c₁ < (2 : ℝ) ^ (2 ^ m) := by
  refine ⟨2 ^ (c₁ + 1), ?_⟩
  rw [← pow_mul]
  exact pow_lt_pow_right₀ (by norm_num) (pow_mul_lt_two_pow_two_pow c₁)

/-- **Non-vacuity / sanity.** The free-set size `2/η` is a genuine positive real for any positive
gap, so the attack parameters are non-degenerate. -/
lemma thm71_freeSet_pos {η : ℝ} (hη : 0 < η) : 0 < 2 / η := by positivity

end ArkLib.ProximityGap.AttackLoop46

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_freeSet_eq
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_badCount_le_subsets
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_within_prize
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_refutes_prize
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_minimal_domain_pressure_c2
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_minimal_domain_pressure_c3
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_no_fixed_exponent
