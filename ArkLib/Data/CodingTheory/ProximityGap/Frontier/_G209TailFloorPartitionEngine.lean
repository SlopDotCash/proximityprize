/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G209: pure-ℕ extremal engine behind the depth-2 cross-orbit tail floor (#466, #509)

On the deep dyadic wall (G88's cross-orbit Parseval identity, #505) the depth-2
kernel-class ℓ²-profile is `(S₀, (S_γ)_γ)`.  Opus-core landed the exact ceiling
`S₀ = n` (`repRF g n 2 0 = n`, G182) and established, on the CORE object, that every
occupied cross-orbit class carries mass `S_γ = n · k_γ` with `k_γ ≥ 1` integer,
`Σ_γ k_γ = n - 1` (a partition of `n - 1`), and that the number of occupied classes is
capped by the `d ↦ n - d` involution at `t ≤ m = n / 2`.

Opus-core's probe flagged that the naive floor `n²(n - 1)` (the all-ones partition,
`t = n - 1`) is NOT realized, leaving the exact extremal constant open.  This file isolates
and proves the pure-ℕ optimization fact that pins it, with NO CORE-object dependency:

For a partition `ks` of `n - 1` into `t ≤ n / 2` positive parts (`n` even, `2 ≤ n`),

`Σ_i k_i² ≥ 2 n - 3`,   hence   `Σ_γ S_γ² = n² · Σ_i k_i² ≥ n² (2 n - 3)`.

The mechanism is a clean, tight, kernel-checked engine:

* pointwise `3 k ≤ k² + 2` for every `k : ℕ`  (equivalently `(k-1)(k-2) ≥ 0`), so
* summing over `t ≤ m = n/2` parts, `3 (n - 1) = 3 Σk ≤ Σk² + 2 t ≤ Σk² + 2 m = Σk² + n`,
  giving `2 n - 3 ≤ Σk²`.

Tightness: the flat partition `[2, …, 2, 1]` (`m - 1` twos and one `1`) saturates BOTH the
pointwise inequality — every part lies in `{1, 2}`, exactly the equality set of
`(k-1)(k-2) = 0` — AND the class-count cap `t = m`.  So the floor genuinely needs the cap:
without it (`t ≤ n - 1`) the pointwise bound only yields `n - 1`, the non-realized naive
floor.  This is the axiom-clean lower half of the depth-2 tail.  Large-prime probes show the floor
is typical, but G210 records large exceptional primes and proves that equality is instead a
checkable per-prime collision-free condition; no eventual-prime threshold is claimed.

Thinness-essential: the whole object exists only for the 2-power smooth subgroup — an
odd-order subgroup has `-1 ∉ ⟨g⟩`, empty depth-2 fiber, and no cross-orbit partition of
`n - 1` at all.  This is a structural floor on the CORE object, not a prize closure: it
pins the *magnitude* of the depth-2 kernel-plus-tail Parseval mass and leaves the signed
simultaneous two-depth (`r = 5 ∧ r = 6`) cyclotomic-class covariance — the literal BGK
weighted-collision object — entirely open.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G209

open Multiset

/-- The pointwise engine, ℕ-safe form of `(k - 1) (k - 2) ≥ 0`:
`3 k ≤ k² + 2` for every natural number `k`.  Equality holds exactly at `k = 1` and
`k = 2`, the only parts appearing in the extremal flat partition. -/
theorem three_mul_le_sq_add_two (k : ℕ) : 3 * k ≤ k ^ 2 + 2 := by
  rcases k with _ | _ | k
  · simp
  · simp
  · -- k ≥ 2 : (k+2)^2 + 2 - 3(k+2) = k^2 + k ≥ 0
    ring_nf
    nlinarith [Nat.zero_le k]

/-- Equality case of the pointwise engine at the extremal parts `{1, 2}`. -/
theorem three_mul_eq_sq_add_two_of_le_two {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 2) :
    3 * k = k ^ 2 + 2 := by
  interval_cases k <;> rfl

/-- Summed engine: for any multiset `ks` of naturals,
`3 · (Σ ks) ≤ (Σ ks²) + 2 · card ks`.  (No positivity or cap needed yet.) -/
theorem three_mul_sum_le_sumSq_add_two_mul_card (ks : Multiset ℕ) :
    3 * ks.sum ≤ (ks.map (· ^ 2)).sum + 2 * ks.card := by
  induction ks using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      have ha : 3 * a ≤ a ^ 2 + 2 := three_mul_le_sq_add_two a
      simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.card_cons]
      -- goal: 3 * (a + s.sum) ≤ (a ^ 2 + (s.map (·^2)).sum) + 2 * (s.card + 1)
      omega

/-- **Thinness-forced depth-2 cross-orbit tail floor (pure-ℕ half).**

For a partition `ks` of `n - 1` into positive parts with at most `m = n / 2` parts,
where `n` is even and `2 ≤ n`, the sum of squares is at least `2 n - 3`; stated ℕ-safely,

`2 * n ≤ (Σ ks²) + 3`.

Both hypotheses are essential: dropping the cap `card ks ≤ n / 2` collapses the floor to
`n - 1` (the non-realized naive floor); dropping positivity breaks the partition count. -/
theorem tail_sumSq_floor
    (n : ℕ) (_hn : 2 ≤ n) (heven : Even n)
    (ks : Multiset ℕ)
    (_hpos : ∀ k ∈ ks, 1 ≤ k)
    (hsum : ks.sum = n - 1)
    (hcard : ks.card ≤ n / 2) :
    2 * n ≤ (ks.map (· ^ 2)).sum + 3 := by
  obtain ⟨m, rfl⟩ := heven
  -- n = m + m = 2 m, m ≥ 1, n/2 = m
  have hm1 : 1 ≤ m := by omega
  have hdiv : (m + m) / 2 = m := by omega
  rw [hdiv] at hcard
  -- summed engine at ks : 3·(Σ ks) ≤ (Σ ks²) + 2·card ks
  have hengine := three_mul_sum_le_sumSq_add_two_mul_card ks
  rw [hsum] at hengine
  -- 3·(2m - 1) ≤ (Σ ks²) + 2·card ks ≤ (Σ ks²) + 2 m
  have hcard2 : 2 * ks.card ≤ 2 * m := by omega
  have hkey : 3 * (m + m - 1) ≤ (ks.map (· ^ 2)).sum + 2 * m :=
    le_trans hengine (Nat.add_le_add_left hcard2 _)
  -- 3·(2m-1) = 6m - 3 ≥ 4m - 3 = 2n - 3 ; and 2n = 4m
  omega

/-- **Depth-2 cross-orbit tail floor consumer (`n²`-scaled, ℕ-safe).**

Substituting the CORE-object mass identity `S_γ = n · k_γ` (opus-core, G88/G182 surface,
`S_γ² = n² · k_γ²`, so `Σ_γ S_γ² = n² · Σ_i k_i²`), the pure-ℕ floor lifts to the realized
depth-2 cross-orbit tail floor

`n² (2 n - 3) ≤ Σ_γ S_γ²`,   stated ℕ-safely as   `n² · (2 n) ≤ (Σ_γ S_γ²) + 3 · n²`,

where `Σ_γ S_γ² = n² · (Σ ks²)`.  G210 proves the exact equality case and corrects the
empirical large-prime observation to a per-prime flatness certificate. -/
theorem tail_floor_scaled
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (ks : Multiset ℕ)
    (hpos : ∀ k ∈ ks, 1 ≤ k)
    (hsum : ks.sum = n - 1)
    (hcard : ks.card ≤ n / 2) :
    n ^ 2 * (2 * n) ≤ n ^ 2 * (ks.map (· ^ 2)).sum + 3 * n ^ 2 := by
  have h := tail_sumSq_floor n hn heven ks hpos hsum hcard
  calc n ^ 2 * (2 * n)
      ≤ n ^ 2 * ((ks.map (· ^ 2)).sum + 3) := by
        exact Nat.mul_le_mul_left _ h
    _ = n ^ 2 * (ks.map (· ^ 2)).sum + 3 * n ^ 2 := by ring

/-- Concrete tight witness as a multiset (the flat partition `[2, …, 2, 1]`), packaged so a
consumer can read the attained floor.  For `n = 2 m`, the multiset `w m` has `m` parts,
sums to `n - 1 = 2 m - 1`, each part is `≥ 1`, and its sum of squares is `2 n - 3 = 4 m - 3`. -/
def w (m : ℕ) : Multiset ℕ := Multiset.replicate (m - 1) 2 + {1}

theorem w_card (m : ℕ) (hm : 1 ≤ m) : (w m).card = m := by
  simp [w, Multiset.card_add, Multiset.card_replicate]
  omega

theorem w_pos (m : ℕ) : ∀ k ∈ w m, 1 ≤ k := by
  intro k hk
  simp only [w, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton] at hk
  rcases hk with ⟨_, rfl⟩ | rfl <;> omega

theorem w_sum (m : ℕ) (hm : 1 ≤ m) : (w m).sum = 2 * m - 1 := by
  simp only [w, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton,
    smul_eq_mul]
  omega

theorem w_sumSq (m : ℕ) (hm : 1 ≤ m) :
    ((w m).map (· ^ 2)).sum = 4 * m - 3 := by
  simp only [w, Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
    Multiset.sum_replicate, Multiset.map_singleton, Multiset.sum_singleton,
    smul_eq_mul]
  norm_num
  omega

/-- The witness attains the floor: `2 n - 3` for `n = 2 m`, i.e. `4 m - 3`.  Combined with
`tail_sumSq_floor`, the extremal constant `2 n - 3` is exact. -/
theorem tail_floor_attained (m : ℕ) (hm : 1 ≤ m) :
    ((w m).map (· ^ 2)).sum = 4 * m - 3 ∧ (w m).sum = 2 * m - 1 ∧ (w m).card = m :=
  ⟨w_sumSq m hm, w_sum m hm, w_card m hm⟩

end ArkLib.ProximityGap.Frontier.G209
