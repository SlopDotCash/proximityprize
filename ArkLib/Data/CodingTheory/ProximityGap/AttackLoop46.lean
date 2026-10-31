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
* **the bad-scalar count is field-independent:** `a = |E^{(+ℓ)}| ≤ choose(|E|, ℓ) ≤ 2^{|E|}`, a
  function of `(ρ,η)` only (`thm71_badCount_le_subsets` records the cruder `2^{|E|}` form).
  For nonempty `E` the inequality `choose(|E|, ℓ) < 2^{|E|}` is **strict**, so the ℓ-element
  subset-sum image can **never** have size `2^{|E|}` (`thm71_subsetSum_card_lt_two_pow`,
  `thm71_maximal_sumset_unattainable`).

## The dichotomy this exposes (corrected)

The prize tolerates any bound `ε_mca ≤ (1/q)·(2^m)^{c₁}/(ρ^{c₂}η^{c₃})` with `2^m = |domain|`.
The §7 attack contributes `ε_mca = a/q`. Hence:

* **Large domains absorb it.** Whenever the prize numerator `(2^m)^{c₁}/(ρ^{c₂}η^{c₃})` is `≥ a`,
  the §7 attack respects the prize (`thm71_within_prize`). Since `a` is *fixed* by `(ρ,η)` while
  `(2^m)^{c₁} → ∞` with the domain, **every** sufficiently large domain absorbs it — this is why all
  prior loops observed the prize surviving §7-type attacks.
* **The minimal domain is not an unbounded family at fixed gap.** An earlier version of this file
  based a "pressure" branch on the subgroup's ℓ-fold sumset attaining `a = 2^{|E|}`. That premise
  is **impossible** (see above), and moreover `|E| = 2/η`: holding the gap `η` fixed fixes `|E|`,
  so at the minimal domain `2^m = |E|` there is no family with `2^m → ∞` at all. To study a growing
  minimal domain one must let `η = 2/|E| → 0`, and then the full prize numerator
  `(2^m)^{c₁}·ρ^{−c₂}·η^{−c₃} = n^{c₁}·ρ^{−c₂}·(n/2)^{c₃}` (with `n = 2^m = |E|`) must be compared,
  not `n^{c₁}` alone. The arithmetic lemmas `thm71_minimal_domain_pressure_*` and
  `thm71_no_fixed_exponent` below are true exponent comparisons but realize **no** bad-scalar
  count; they do not threaten the prize.

So the §7 route to **dis**proving the prize reduces to a *feasible lower-bound* question:

> **Open (O11, corrected).** At the minimal domain `n = |G| = |E| = 2^m`, `η = 2/n`, fixed rate
> `ρ`, and the §7-critical `ℓ = n(1−ρ) − 2`, is there a family of smooth multiplicative subgroups
> `G ≤ F_q^*` with `|G^{(+ℓ)}| > n^{c₁}·ρ^{−c₂}·(n/2)^{c₃}` for every fixed triple `(c₁,c₂,c₃)`
> (i.e. super-polynomial growth in `n`, within the feasible ceiling `|G^{(+ℓ)}| ≤ choose(n, ℓ)`,
> and also `≤ q`)? If `|G^{(+ℓ)}|` is polynomially bounded in `(n, 1/η)` the prize survives §7.

This is genuine additive combinatorics of multiplicative subgroups (cf. BCHKS §7, Conj. 1.12 over
prime fields). It is *plausible* the prize survives — a full subgroup satisfies the vanishing
power-sum relations `∑_{g∈G} g^j = 0` (`1 ≤ j < |G|`), which are strong additive constraints that
should keep `|G^{(+ℓ)}|` far below `choose(|G|, ℓ)` — but this is **unproven** in either direction.

**Honest status.** This loop is `sorry`-free and axiom-clean. All declared results are elementary
§7 *parameter* identities, prize *comparison* arithmetic, and the trivial subset-count ceiling; none
is a construction or a subset-sum lower bound. It does **not** prove or refute the O11 bound, so the
prize remains OPEN. See `Research/ProximityPrize/DISPROOF_LOG.md` (Loop46/O11).
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
the number of subsets of `E`, namely `2^{|E|}` (in fact at most `choose(|E|, ℓ)`, which is strictly
smaller for nonempty `E`: `thm71_subsetSum_card_lt_two_pow`). Combined with `thm71_freeSet_eq`
(`|E| = 2/η`) the bad count depends only on `(ρ, η)`, never on `q` or the domain size. This lemma
is only the cast of the supplied hypothesis `a ≤ 2^{|E|}` to `ℝ`. -/
lemma thm71_badCount_le_subsets (Ecard a : ℕ) (hsumset : a ≤ 2 ^ Ecard) :
    (a : ℝ) ≤ (2 : ℝ) ^ Ecard := by
  have : ((2 : ℕ) ^ Ecard : ℝ) = (2 : ℝ) ^ Ecard := by push_cast; ring
  calc (a : ℝ) ≤ ((2 : ℕ) ^ Ecard : ℝ) := by exact_mod_cast hsumset
    _ = (2 : ℝ) ^ Ecard := this

/-- **The ℓ-element subset-sum image is strictly smaller than `2^{|E|}`.** For a nonempty finite
set `E` in an additive commutative monoid, the set of sums of `ℓ`-element subsets of `E` has at
most `choose(|E|, ℓ)` elements, and `choose(|E|, ℓ) < 2^{|E|}` since `|E| > 0`. -/
theorem thm71_subsetSum_card_lt_two_pow {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (E : Finset G) (hE : E.Nonempty) (ℓ : ℕ) :
    ((E.powersetCard ℓ).image (fun S => ∑ x ∈ S, x)).card < 2 ^ E.card :=
  lt_of_le_of_lt (Finset.card_image_le.trans (Finset.card_powersetCard ℓ E).le)
    (Nat.choose_lt_two_pow _ _ hE.card_pos)

/-- **The "maximal sumset" premise is unattainable.** No nonempty `E` has an ℓ-fold
distinct-subset-sumset of size `2^{|E|}`; so any argument assuming `a = 2^{|E|}` for the §7 bad
count assumes something false. -/
theorem thm71_maximal_sumset_unattainable {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (E : Finset G) (hE : E.Nonempty) (ℓ : ℕ) :
    ((E.powersetCard ℓ).image (fun S => ∑ x ∈ S, x)).card ≠ 2 ^ E.card :=
  (thm71_subsetSum_card_lt_two_pow E hE ℓ).ne

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

/-- **Arithmetic comparison only: `(2^4)^2 < 2^{2^4}`.** Historically motivated as a
"minimal-domain pressure" witness under a maximal sumset `a = 2^{|E|}` at `|E| = 16`; that premise
is unattainable (`thm71_maximal_sumset_unattainable`), and the comparison omits the `ρ^{−c₂}η^{−c₃}`
numerator factors. This lemma is a numerical inequality and realizes no bad-scalar count. -/
lemma thm71_minimal_domain_pressure_c2 : ((2 : ℝ) ^ 4) ^ 2 < (2 : ℝ) ^ (2 ^ 4) := by
  norm_num

/-- **Arithmetic comparison only: `(2^5)^3 < 2^{2^5}`.** As for
`thm71_minimal_domain_pressure_c2`: the "maximal sumset" interpretation is unattainable and the
full prize numerator is not compared; this is a numerical inequality, not an attack. -/
lemma thm71_minimal_domain_pressure_c3 : ((2 : ℝ) ^ 5) ^ 3 < (2 : ℝ) ^ (2 ^ 5) := by
  norm_num

/-- Arithmetic helper: `2^(c+1)·c < 2^(2^(c+1))`. -/
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

/-- **Exponent growth comparison (arithmetic only).** For every fixed `c₁` there is an `m` (the
proof takes `m = 2^(c₁+1)`) with `(2^m)^{c₁} < 2^{2^m}`. This is a true statement about powers of
two and nothing more. It does **not** realize a bad-scalar count: the earlier reading "a maximal
§7 sumset `a = 2^{|G|}` beats the prize numerator" rests on an unattainable premise
(`thm71_maximal_sumset_unattainable`), fixes the gap although `|E| = 2/η` then fixes the minimal
domain, and omits the `ρ^{−c₂}η^{−c₃}` numerator factors. A genuine §7 disproof branch would need
the corrected O11 lower bound described in the module docstring. -/
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
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_subsetSum_card_lt_two_pow
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_maximal_sumset_unattainable
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_within_prize
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_refutes_prize
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_minimal_domain_pressure_c2
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_minimal_domain_pressure_c3
#print axioms ArkLib.ProximityGap.AttackLoop46.thm71_no_fixed_exponent
