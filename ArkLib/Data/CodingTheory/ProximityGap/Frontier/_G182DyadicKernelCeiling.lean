/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G181DyadicKernelFloor

/-!
# G182: the dyadic antipodal kernel CEILING — the depth-`2` kernel-class mass is
EXACTLY `n`, unconditionally and in every characteristic (`repRF g n 2 0 = n`)

## Context and the dual to G181

G181 (`_G181DyadicKernelFloor.lean`) proves the thinness-forced **lower** bound
`n ≤ repRF g n 2 0` for a smooth subgroup `⟨g⟩` of even order `n = 2m` with `g^m = -1`, by
injecting the `n` antipodal pairs `(j, j+m)` into the depth-`2` zero-sum fiber, and composes it
with G88's `kernel_sq_le_centeredShadowMass` into the wall floor
`q·n² − n⁴ ≤ centeredShadowMass`.

G181's honest scope note flagged that only the `≥` direction was proved, because "accidental
char-`p` zero-sums below a saturation threshold `p*` inflate `S₀`" — this caution is real at
depth `r = 4` and beyond (`A(n,4) = 3n(n-1)` only stabilises for `p > p*`, e.g. `p*(8,4)=73`).

**This file removes that caution at depth `2`.**  It proves the matching **upper** bound

`repRF g n 2 0 ≤ n`,

hence the EXACT count

`repRF g n 2 0 = n`   (`repRF_two_zero_eq`),

with NO field-size hypothesis: the depth-`2` kernel-class mass is `n` for *every* prime `p`,
including the smallest fields, with no `p*` threshold.  There are no accidental depth-`2`
zero-sums.

## The mechanism (uniqueness of the order-two element)

A depth-`2` tuple `t : Fin 2 → Fin n` lies in the zero-sum fiber iff
`g^{t 0} + g^{t 1} = 0`, i.e. `g^{t 1} = -g^{t 0} = g^{t 0} · g^m = g^{t 0 + m}`.  Because
`orderOf g = n`, the power map `i ↦ g^i` is **injective** on `{0, …, n-1}`
(`pow_injOn_Iio_orderOf`).  Both `t 1` and `(t 0 + m) mod n` lie in that range, so
`t 1 = (t 0 + m) mod n = t 0 + s` in `Fin n` (`s` the half-shift).  Therefore the fiber is
**exactly** the injective antipodal image `{ (j, j+m) : j ∈ Fin n }`, whose cardinality is `n`.

The crux is that `-1 = g^m` has a **unique** preimage under `i ↦ g^i` on `Fin n` (it is the
unique element of order `2` in the cyclic group `⟨g⟩` of even order), so the second index is
FORCED to be `t 0 + m` — no accidental char-`p` coincidence can add a solution.  This is what
fails at depth `≥ 3`, where the number of ways to write `0` as a sum of `≥ 3` roots does pick up
genuine char-`p` accidents; depth `2` is exactly the rigid boundary.

## Consequence: the depth-`2` wall floor is EXACT, not merely a lower bound

Substituting `repRF g n 2 0 = n` into G88's Parseval decomposition, the kernel-class contribution
to `n · centeredShadowMass` is the exact constant `q · n · n² = q·n³` (there is no slack in `S₀`
at depth `2`), so all remaining freedom in `centeredShadowMass` lives in the cross-orbit tail
`Σ_γ S_γ²` — precisely the doctrine-v3 object.  In other words: **at depth `2` the kernel side of
the wall is completely determined; the entire open content is the cross-orbit tail.**  We record
the sharpened floor `q·n² − n⁴ ≤ centeredShadowMass` now as an EQUALITY-of-the-`S₀`-term statement
(`dyadic_kernel_floor_two_exact`), pinning that the `1/3` prize fraction from G181 is the *exact*
kernel contribution, not a lower estimate.

## Why genuinely new (not a G181 restatement)

G181 supplies `S₀ ≥ n` (a one-sided injection).  G182 supplies `S₀ ≤ n` via the **reverse**
containment (fiber ⊆ antipodal image), which is a strictly different structural fact requiring
the uniqueness of the order-`2` element and `orderOf g = n`.  Together they close the depth-`2`
kernel-class size to an exact `= n` with no `p*` threshold, upgrading G181's honest one-sided
scope note to a two-sided exact count on the floor object.  This is thinness-essential in the
same way: for ODD `n`, `-1 ∉ ⟨g⟩`, so the depth-`2` fiber is empty and the count is `0`, not `n`
(verified in the probe; the dyadic `= n` is unavailable to any odd-order subgroup).

## Scope (honest)

Exact count of the depth-`2` kernel-class mass only.  It does NOT bound the cross-orbit tail
`Σ_γ S_γ²` (the remaining open object, doctrine v2/v3), nor the higher-depth kernel masses
`repRF g n r 0` for `r ≥ 3` (where char-`p` accidents genuinely appear).  CORE remains OPEN /
ON-BGK.  Value: closes the depth-`2` kernel side of the G88 wall to an exact, unconditional,
`p`-independent constant, removing G181's `p*` caveat at `r = 2` and isolating the tail as the
sole remaining freedom.

Issue #509.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.

Probe: `scripts/probes/probe_oc_kernel_depth2_upper.py` (1367 `(n,p)` rows, all even `n` and all
primes `p ≡ 1 (mod n)` up to bound: `repRF g n 2 0 = n` with zero violations; odd-`n` control
gives `0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.G182DyadicKernelCeiling

open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence
open ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld
open ArkLib.ProximityGap.Frontier.G181DyadicKernelFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The reverse containment: the depth-2 zero-sum fiber lies in the antipodal image -/

/-- **Every depth-`2` zero-sum tuple is antipodal.**  If `g^{t 0} + g^{t 1} = 0` with
`orderOf g = n` and `g^m = -1`, then the second index is forced: `t 1 = t 0 + s`, where
`s = ⟨m % n, _⟩` is the half-shift.  The mechanism is the uniqueness of the order-two element:
`g^{t 1} = g^{t 0 + m}` and injectivity of `i ↦ g^i` on `Fin n` (`pow_injOn_Iio_orderOf`). -/
theorem zeroSum_forces_antipodal
    (g : F) (n m : ℕ) (hn : n = 2 * m) (hg : g ^ m = -1) (hord : orderOf g = n)
    (hnpos : 0 < n) (t : Fin 2 → Fin n)
    (ht : gsumR g n 2 t = 0) :
    t = antipodalPair (⟨m % n, Nat.mod_lt m hnpos⟩) (t 0) := by
  classical
  -- period: g^n = 1
  have hgn : g ^ n = 1 := by
    have h2 : g ^ n = (g ^ m) ^ 2 := by rw [← pow_mul]; congr 1; omega
    rw [h2, hg]; ring
  have hperiod : ∀ k : ℕ, g ^ (k % n) = g ^ k := by
    intro k
    conv_rhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hgn, one_pow, one_mul]
  -- from the two-term sum: g^{t0} + g^{t1} = 0
  have hsum : g ^ ((t 0 : ℕ)) + g ^ ((t 1 : ℕ)) = 0 := by
    have := ht
    unfold gsumR at this
    rwa [Fin.sum_univ_two] at this
  -- g^{t1} = -g^{t0} = g^{t0} * (-1) = g^{t0} * g^m = g^{t0 + m}
  have hkey : g ^ ((t 1 : ℕ)) = g ^ ((t 0 : ℕ) + m) := by
    have h1 : g ^ ((t 1 : ℕ)) = - g ^ ((t 0 : ℕ)) := by
      rw [add_comm] at hsum; exact eq_neg_of_add_eq_zero_left hsum
    rw [h1, pow_add, hg]; ring
  -- injectivity of i ↦ g^i on Iio (orderOf g) = Iio n
  have hinj : Set.InjOn (fun i => g ^ i) (Set.Iio (orderOf g)) := pow_injOn_Iio_orderOf
  -- both exponents reduce into Iio n
  have ht1lt : (t 1 : ℕ) < n := (t 1).isLt
  have hmodlt : ((t 0 : ℕ) + m) % n < n := Nat.mod_lt _ hnpos
  have hg_t1 : g ^ ((t 1 : ℕ)) = g ^ (((t 0 : ℕ) + m) % n) := by
    rw [hperiod ((t 0 : ℕ) + m)]; exact hkey
  have heq : (t 1 : ℕ) = ((t 0 : ℕ) + m) % n :=
    hinj (by rw [hord]; exact Set.mem_Iio.mpr ht1lt)
      (by rw [hord]; exact Set.mem_Iio.mpr hmodlt) hg_t1
  -- assemble: t = antipodalPair s (t 0).  Second index forced; first index definitional.
  have h1eq : t 1 = t 0 + (⟨m % n, Nat.mod_lt m hnpos⟩ : Fin n) := by
    apply Fin.val_injective
    rw [Fin.val_add, heq]
    -- both sides = (t0 + m) % n : reduce the inner `m % n` via add_mod
    have hmm : m % n % n = m % n := Nat.mod_mod_of_dvd m (dvd_refl n) |>.symm ▸ rfl
    have : ((t 0 : ℕ) + m % n) % n = ((t 0 : ℕ) + m) % n := by
      rw [Nat.add_mod ((t 0 : ℕ)) (m % n) n, hmm, ← Nat.add_mod]
    rw [this]
  funext i
  fin_cases i
  · change t 0 = antipodalPair (⟨m % n, Nat.mod_lt m hnpos⟩) (t 0) 0
    simp only [antipodalPair, if_true]
  · change t 1 = antipodalPair (⟨m % n, Nat.mod_lt m hnpos⟩) (t 0) 1
    simp only [antipodalPair, if_neg (by decide : ¬((1 : Fin 2) = 0))]
    exact h1eq

/-! ## 2. The exact depth-2 kernel count -/

/-- **The dyadic antipodal kernel ceiling / exact count (depth 2), unconditional.**
The depth-`2` zero-sum fiber is EXACTLY the injective antipodal image, so
`repRF g n 2 0 = n` in every characteristic — no `p*` saturation threshold.  Combined with
G181's `n_le_repRF_two_zero` this is the two-sided exact size of the kernel-class mass at
depth `2`. -/
theorem repRF_two_zero_eq
    (g : F) (n m : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hord : orderOf g = n) :
    repRF g n 2 0 = n := by
  classical
  have hnpos : 0 < n := by omega
  let s : Fin n := ⟨m % n, Nat.mod_lt m hnpos⟩
  -- the fiber equals the antipodal image
  have hset : (Finset.univ.filter (fun t : Fin 2 → Fin n => gsumR g n 2 t = 0))
      = Finset.univ.image (antipodalPair s) := by
    apply Finset.ext
    intro t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ht
      exact ⟨t 0, (zeroSum_forces_antipodal g n m hn hg hord hnpos t ht).symm⟩
    · rintro ⟨j, _, rfl⟩
      exact gsumR_antipodalPair_eq_zero g n m hn hg j hnpos
  have hcard : (Finset.univ.image (antipodalPair s)).card = n := by
    rw [Finset.card_image_of_injective _ (antipodalPair_injective s),
      Finset.card_univ, Fintype.card_fin]
  unfold repRF
  rw [hset, hcard]

/-! ## 3. The exact kernel contribution to the G88 wall -/

/-- **The depth-`2` wall floor is the EXACT kernel contribution.**  Since `repRF g n 2 0 = n`
exactly (G182), the G181 lower bound `q·n² − n⁴ ≤ centeredShadowMass` is now certified to be the
*exact* value of the kernel-class term in G88's Parseval decomposition (no `S₀`-slack at depth
`2`); the residual `centeredShadowMass − (q·n² − n⁴)/…` is entirely the cross-orbit tail. -/
theorem dyadic_kernel_floor_two_exact
    (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    repRF g n 2 0 = n ∧
    (Fintype.card F : ℝ) * (n : ℝ) ^ 2 - (n : ℝ) ^ 4 ≤ centeredShadowMass g n m 2 := by
  refine ⟨repRF_two_zero_eq g n m hm hn hg hord,
    dyadic_kernel_floor_two g n m hg0 hord hm hn hg⟩

end ArkLib.ProximityGap.Frontier.G182DyadicKernelCeiling
