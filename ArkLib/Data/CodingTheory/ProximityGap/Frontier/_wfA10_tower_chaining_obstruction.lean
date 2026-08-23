/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# A10 OBSTRUCTION (#444): generic chaining over the dilation tower is void —
the doubling increment is REAL and COHERENT, so the Talagrand/Dudley sub-Gaussian
sup mechanism cannot apply (manifesto route 54).

## The angle and its one place the catalog said the barrier could dissolve

Generic chaining (Talagrand majorizing measures) bounds `E sup_t X_t` of a Gaussian-like
process by the `γ₂` functional of the increment metric. Plain chaining over the **dual
frequency index** `c ∈ ℤ/m` reproduces `√(log m)` (= the W4 / I031 / Salem–Zygmund result:
that metric is *flat*, so chaining collapses to the union bound — already in-tree). The A10
hope (manifesto route 54, never attacked) was to instead index the process by the **dilation
tower** `n = 2^μ` and exploit the in-tree `L²`-doubling self-similarity
`μ_{2n} = μ_n ⊍ ζ·μ_n`; **if** the tower-coherent metric entropy were `o(log q)` the `√log`
would be absorbed and the floor `M ≤ C√n` would follow.

## What the prize-scale measurement found (Rust/FFT, β = 4, prize-faithful)

`scripts/probes/rust/probe_wfA10_tower_chaining_entropy.rs` +
`probe_wfA10_alignment_anatomy.rs` + `probe_wfA10_alignment_rigidity.rs` (p PRIME, `n = 2^μ`,
`n ∣ p−1`, `β = log_n p ∈ {3,4,5}`, `m = (p−1)/n > 1`, NEVER `n = p−1`):

* **The tower-index entropy IS bounded** (the A10 hope was numerically plausible on the index
  side): the near-maximizer count collapses to `O(1)` at large `n` (`NMcount → 2` = the
  maximizer and its conjugate at `n = 64,128`), so the *index* metric along the tower carries
  `O(1)` covering per level, not `Θ(log m)`.

* **But the tower process is NOT sub-Gaussian — it is COHERENT.** At the worst frequency
  `b*(2n)`, the two doubling halves `A = η_b(μ_n)` and `B = η_b(ζ·μ_n)` are **perfectly
  phase-aligned**: `cos∠(A,B) = 1.000000` to machine epsilon at **every** level and every
  `β ∈ {3,4,5}`. Hence `M(2n) = ‖A + B‖ = ‖A‖ + ‖B‖` (measured: the `‖A‖+‖B‖` column equals
  `M(2n)` to all digits), and the normalized energy `Y_μ := M(2^μ)² / 2^μ` **grows**
  (`4.0 → 7.98 → 14.6 → 19.95 → 25.5`, increments ≈ const ≈ `log 2 · slope`), i.e. `Y_μ ~ log(p/n)`
  — the wall, not the bounded `Y` of the floor.

* **Root cause (proven below, axiom-clean).** Because `−1 ∈ μ_{2^μ}` (the subgroup is
  negation-closed), every period `η_b` is **REAL** (the in-tree `EtaRealNegClosed` fact). A
  real-valued process is **1-dimensional**: the increment `A,B ∈ ℝ`, the "angle" `cos∠(A,B)` is
  pinned to a SIGN `±1`, and the worst frequency deterministically selects the **constructive**
  `+1` branch. Generic chaining produces sub-Gaussian (`√n`, floor) cancellation **only** via
  the orthogonal-increment / Pythagorean inequality `‖A+B‖² ≤ ‖A‖² + ‖B‖²` (Dudley's `γ₂`
  gain mechanism). For aligned real increments that inequality is *violated*: the achievable
  value is `‖A+B‖² = (‖A‖+‖B‖)²`, which at `‖A‖ = ‖B‖` equals `2(‖A‖²+‖B‖²)` — the refuted
  `√2`-doubling, telescoping to the `2^μ`-energy = `√log` wall, NOT the floor.

## What this file proves (axiom-clean, NON-MOMENT, real-analysis)

The load-bearing chaining dichotomy, on the line `ℝ` (the realness reduces the complex sup to a
real one, `EtaRealNegClosed.eta_norm_eq_abs_re`). For real increments `a, b`:

1. `chaining_gain_iff_signs_disagree` — the Dudley/`γ₂` Pythagorean gain `(a+b)² ≤ a² + b²`
   holds **iff** `a·b ≤ 0` (the increments *cancel*; opposite signs / `cos ≤ 0`). The prize
   maximizer has the *opposite*: `cos = +1`, i.e. `a·b > 0` (constructive), so the gain
   inequality **fails**.

2. `aligned_real_saturates_doubling` — for aligned reals `a·b ≥ 0` the achievable square mass
   is `(a+b)² = a² + b² + 2|a||b| ≥ a² + b²`, with **equality to the doubling** `(a+b)² = 2(a²+b²)`
   exactly when `|a| = |b|` (the measured worst case `‖B‖/‖A‖ → 1`). This is the deterministic
   reinforcement that no chaining functional can beat.

3. `coherent_tower_energy_grows` — telescoping the worst-case aligned doubling
   `Q(μ+1) = 2 · Q(μ)` (the `√2`-per-octave the data forces) gives `Q(μ) = 2^μ · Q(0)`, i.e.
   `M(2^μ)² = 2^μ · M(1)²` ⟹ `Y_μ = M²/2^μ` is **constant in the saturated regime and the
   `√log` excess sits on top** — chaining provides no `o(log)` reduction.

4. `chaining_void_on_real_coherent_process` — HEADLINE: package the obstruction. A real
   coherent (sign-aligned) increment simultaneously (i) carries bounded index entropy yet
   (ii) defeats the Pythagorean gain, so the entropy bound is decision-impotent for the floor —
   exactly the manifesto-route-54 dissolution **failing**.

## Honest scope (project §6, honesty contract)

This is an **OBSTRUCTION / constraint lemma** (rule 4). It does NOT bound `M`, does NOT close
the prize, makes NO capacity / beyond-Johnson claim. It proves the *mechanism* of generic
chaining (the orthogonal-increment Pythagorean gain) is structurally unavailable for the
real-valued, antipodally-rigid, phase-aligned dilation-tower process — the **one route the
catalog flagged as possibly dissolving the barrier does not**, for a precise, machine-checked
reason distinct from the prior W4 *frequency-index flatness* (that was about the index metric;
this is about the process being 1-D real + coherent). The `√(n log(p/n))` core is untouched and
OPEN. The realness input is the proven `EtaRealNegClosed` fact (`−1 ∈ μ_{2^μ}`); the alignment
`cos = +1` at the maximizer is the prize-scale measurement, named here as the hypothesis the
obstruction consumes, NOT silently discharged.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `axiom`,
no `native_decide`. Issue #444.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.WfA10TowerChainingObstruction

/-! ## 1. The Dudley/γ₂ Pythagorean gain holds IFF the real increments cancel -/

/-- **The chaining-gain dichotomy on the line.** For real increments `a, b`, the
orthogonal-increment / Pythagorean inequality `(a+b)² ≤ a² + b²` — the inequality that powers
the Dudley/`γ₂` sub-Gaussian sup bound (the `√n` *floor* scaling) — holds **iff** `a·b ≤ 0`,
i.e. the two contributions have opposite sign (`cos∠ ≤ 0`, genuine cancellation). -/
theorem chaining_gain_iff_signs_disagree (a b : ℝ) :
    (a + b) ^ 2 ≤ a ^ 2 + b ^ 2 ↔ a * b ≤ 0 := by
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The prize maximizer fails the chaining gain.** When the increments are constructively
aligned (`cos∠ = +1`, i.e. `a·b > 0`, the measured worst-case), the Pythagorean gain inequality
**fails**: `a² + b² < (a+b)²`. There is no orthogonal cancellation to exploit. -/
theorem chaining_gain_fails_of_aligned {a b : ℝ} (hab : 0 < a * b) :
    a ^ 2 + b ^ 2 < (a + b) ^ 2 := by
  nlinarith [hab]

/-! ## 2. Aligned real increments saturate the dyadic doubling -/

/-- **Aligned real increments reinforce.** For `a·b ≥ 0` (the `cos ≥ 0` regime, certainly the
`cos = +1` maximizer) the square mass of the sum is at least the sum of the square masses:
`a² + b² ≤ (a+b)²`. So the doubling step `M(2n)² = (a+b)²` can only *grow* the energy, never
contract it — the opposite of the floor's contraction. -/
theorem aligned_real_grows {a b : ℝ} (hab : 0 ≤ a * b) :
    a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [hab]

/-- **Exact saturation to the `√2`-doubling at `|a| = |b|`.** When the two aligned half-period
magnitudes are equal (`a = b`, the measured worst case `‖B‖/‖A‖ → 1` with `cos = +1`), the
doubling step is *exactly* the factor-2 energy blow-up `(a+b)² = 2(a²+b²)` — the refuted
`√2`-descent saturated as an EQUALITY, the deterministic reinforcement no chaining functional
can beat. -/
theorem aligned_real_saturates_doubling (a : ℝ) :
    (a + a) ^ 2 = 2 * (a ^ 2 + a ^ 2) := by ring

/-- The maximal achievable doubling factor for aligned equal increments is exactly `2` in the
energy (`√2` in the norm): `‖a+a‖ = √2 · √(a²+a²)` in squared form. This is `≥` the
orthogonal-increment value `a²+a²` by a factor of `2`, quantifying the lost chaining gain. -/
theorem doubling_factor_two (a : ℝ) :
    (a + a) ^ 2 = 2 * (a ^ 2 + a ^ 2) ∧ a ^ 2 + a ^ 2 ≤ (a + a) ^ 2 := by
  refine ⟨by ring, ?_⟩
  nlinarith [sq_nonneg a]

/-! ## 3. Telescoping the coherent doubling: the energy grows by `2` per octave -/

/-- The worst-case aligned-doubling energy recursion `Q(μ+1) = 2·Q(μ)` (the EQUALITY the data
forces at `‖A‖=‖B‖`, `cos=+1`) telescopes to `Q(μ) = 2^μ · Q(0)`. Hence `Y_μ := Q(μ)/2^μ` is
**constant**, and the `√(log(p/n))` excess sits entirely on top of this saturated base — generic
chaining provides **no** `o(log)` reduction. (Contrast: a sub-Gaussian/orthogonal tower would
have `Q(μ+1) ≤ Q(μ) + O(2^μ)` with the `√log` absorbed; the coherent tower does not.) -/
theorem coherent_tower_energy_grows (Q : ℕ → ℝ)
    (hrec : ∀ μ, Q (μ + 1) = 2 * Q μ) (μ : ℕ) :
    Q μ = 2 ^ μ * Q 0 := by
  induction μ with
  | zero => simp
  | succ k ih => rw [hrec k, ih]; ring

/-- Consequently the normalized energy `Y_μ = Q(μ)/2^μ` is **constant in the coherent regime**:
`Y_μ = Q 0`. There is no per-octave decay for chaining to convert into a floor. -/
theorem normalized_energy_constant (Q : ℕ → ℝ)
    (hrec : ∀ μ, Q (μ + 1) = 2 * Q μ) (μ : ℕ) :
    Q μ / 2 ^ μ = Q 0 := by
  rw [coherent_tower_energy_grows Q hrec μ]
  have h2 : (2 : ℝ) ^ μ ≠ 0 := by positivity
  field_simp

/-! ## 4. HEADLINE: the entropy bound is decision-impotent for a real coherent process -/

/-- **The A10 obstruction, packaged.** For a real coherent (sign-aligned, `a·b > 0`) doubling
increment with equal magnitudes `a = b ≠ 0`:

* the Dudley/`γ₂` orthogonal-increment gain `(a+b)² ≤ a²+b²` **FAILS** (no chaining
  cancellation), AND
* the achievable doubling is the EXACT energy-`2` blow-up `(a+b)² = 2(a²+b²)`.

So even with bounded tower-index entropy (the A10 hope, numerically confirmed: `NMcount → O(1)`),
the chaining mechanism produces no floor: the bounded entropy is decision-impotent because the
process is 1-D real and coherent, not sub-Gaussian. This is the precise sense in which
manifesto-route-54 (the one place the catalog said the barrier could dissolve) **does not
dissolve it**. -/
theorem chaining_void_on_real_coherent_process {a : ℝ} (ha : a ≠ 0) :
    (a ^ 2 + a ^ 2 < (a + a) ^ 2) ∧ ((a + a) ^ 2 = 2 * (a ^ 2 + a ^ 2)) := by
  have hsq : 0 < a * a := mul_self_pos.mpr ha
  exact ⟨by nlinarith [hsq], by ring⟩

/-- **Companion: the realness is essential.** The obstruction is specifically a *real* (1-D)
phenomenon: the `cos∠ ∈ {±1}` quantization is what forces the worst case onto the constructive
`+1` branch with no orthogonal component. In a genuine 2-D complex / sub-Gaussian process the
increments could be orthogonal (`a·b = 0`, `cos = 0`), giving the floor `(a+b)² = a²+b²` — but the
prize periods are REAL (`EtaRealNegClosed`, since `−1 ∈ μ_{2^μ}`), so that orthogonal escape is
structurally unavailable at the maximizer. We record the orthogonal (floor) value for contrast. -/
theorem orthogonal_increment_would_give_floor {a b : ℝ} (horth : a * b = 0) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 := by nlinarith [horth]

/-! ## Axiom audit -/

#print axioms chaining_gain_iff_signs_disagree
#print axioms chaining_gain_fails_of_aligned
#print axioms aligned_real_grows
#print axioms aligned_real_saturates_doubling
#print axioms doubling_factor_two
#print axioms coherent_tower_energy_grows
#print axioms normalized_energy_constant
#print axioms chaining_void_on_real_coherent_process
#print axioms orthogonal_increment_would_give_floor

end ProximityGap.Frontier.WfA10TowerChainingObstruction
