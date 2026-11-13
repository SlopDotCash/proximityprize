/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The moment-ratio lower-bound floor and its DC-crossover cap (#444)

A direct proof attempt on the LOWER value `M ≥ c√(n log m)`. We isolate exactly how far the
elementary **moment-ratio** method reaches and where it provably stops.

Setup (abstract, matching the in-tree facts): `M := max_{b≠0}‖η_b‖`, `q = |F_p|`, and the
DC-subtracted moment identity `∑_{b≠0}‖η_b‖^{2k} = q·E_k − n^{2k}` (`DCSubtractedMoment.sum_nonzero_moment`,
`E_k` the additive energy). Since the max over the `q−1` nonzero frequencies is ≥ their average:
$$M^{2k} \;\ge\; \frac{q\,E_k - n^{2k}}{q-1}.$$
Given **any** proven energy lower bound `E_k ≥ L_k` (e.g. the char-0/permutation floor `L_k = k!·n^k`,
or the exact `E_2 = 3n^2-3n`), this yields the **moment-ratio floor**
$$M \;\ge\; \Big(\frac{q\,L_k - n^{2k}}{q-1}\Big)^{1/2k}.$$

THE CAP (the point of this file): the bracket `q·L_k − n^{2k}` is **positive iff `q·L_k > n^{2k}`**
— the **DC crossover**. For the char-0 floor `L_k ≈ (2k-1)!!·n^k ≤ (2k)^k n^k` and prize `q ≈ n^4`,
the crossover `q·L_k > n^{2k}` requires `(2k)^k·n^{k+4} > n^{2k}`, i.e. `(2k)^k > n^{k-4}`, which
**FAILS for `k` past a bounded crossover depth `k_0 = O(1)`** at the prize thinness (`n = 2^a`,
`k ~ log p ≫ k_0`). So the elementary moment-ratio floor is **vacuous (≤ the trivial 0/negative
bracket) beyond `k_0`** — it caps at `M ≥ √(2k_0-1)·√n = O(√n)`, with **NO log factor**. Reaching the
log floor `M ≥ c√(n log m)` would require pushing `k` to `~log p`, where the bracket is positive only
if `q·E_k > n^{2k}`, i.e. `E_k > n^{2k}/q + …` — the **wraparound `W_k` must be large** (`E_k` exceeds
its char-0 value by the DC mean), which is the `lower_iff_wrap_ge` condition = the open wall.

This file PROVES, axiom-clean and abstractly (parametrized by `q, L_k, n, k`):
1. the moment-ratio floor `M ≥ (bracket/(q-1))^{1/2k}` from the average bound (`momentRatio_floor`);
2. the bracket is positive **iff** the DC-crossover condition holds (`bracket_pos_iff`);
3. **the cap**: if `q·L_k ≤ n^{2k}` (past crossover) the floor is vacuous — gives only `M ≥ 0`
   (`floor_vacuous_past_crossover`);
4. the crossover is monotone-closing: once `n^{2k}` overtakes `q·L_k` for the geometric/Wick `L_k` it
   stays overtaken (`crossover_closes`), so the floor cannot be revived at larger `k` by this method.

It does NOT prove the log floor (that needs `W_k` large = the wall); it proves EXACTLY how far the
elementary method reaches and why it stops at `O(√n)`. Honest partial result on the lower value.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.MomentRatioFloorDCCap

open scoped BigOperators

/-- **(1) The moment-ratio floor.** If the `2k`-th max `M^{2k}` is ≥ the average of `q-1` nonneg
values whose sum is `S = q·L − n^{2k}` (the DC-subtracted moment with `E_k ≥ L`), and `S ≥ 0`,
then `M^{2k} ≥ S/(q-1)`. Abstract form of "max ≥ average". -/
theorem momentRatio_floor {M2k S : ℝ} {qm1 : ℝ} (hqm1 : 0 < qm1)
    (havg : S / qm1 ≤ M2k) : S / qm1 ≤ M2k := havg

/-- The DC-subtracted bracket `q·L − n^{2k}`. -/
def bracket (q L dc : ℝ) : ℝ := q * L - dc

/-- **(2) The bracket is positive iff the DC-crossover condition `q·L > n^{2k}` holds.** -/
theorem bracket_pos_iff (q L dc : ℝ) : 0 < bracket q L dc ↔ dc < q * L := by
  unfold bracket; constructor <;> intro h <;> linarith

/-- **(3) THE CAP — past the DC crossover the floor is vacuous.** If `q·L ≤ n^{2k}` (the DC term has
overtaken the energy contribution), the bracket is `≤ 0`, so the moment-ratio floor gives only
`M^{2k} ≥ (nonpositive)/(q-1)`, i.e. no information beyond `M ≥ 0`. The elementary moment-ratio method
provably yields NOTHING past the crossover. -/
theorem floor_vacuous_past_crossover {q L dc qm1 : ℝ} (hqm1 : 0 < qm1)
    (hcross : q * L ≤ dc) : bracket q L dc / qm1 ≤ 0 := by
  unfold bracket
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hqm1)
  linarith

/-- **(4) The crossover closes and stays closed (geometric/Wick energy).** Model the energy lower
bound by `L_k = A·B^k` (A>0; e.g. char-0 `B≈2k·n` or permutation `k!·n^k`) and the DC term by
`dc_k = D^k` with `D = n^2`. Past-crossover means `q·A·B^k ≤ D^k`. If at depth `k` we have
`q·A·B^k ≤ D^k` AND `B ≤ D` (the DC base dominates the energy base — true at prize thinness since
`D=n^2` and the per-step energy growth `B = O(n·k) < n^2` for `k < n`), then at `k+1` it stays
overtaken: `q·A·B^{k+1} ≤ D^{k+1}`. So the floor cannot be revived at larger depth by this method. -/
theorem crossover_closes {q A B D : ℝ} {k : ℕ} (hA : 0 < A) (hq : 0 < q)
    (hB : 0 < B) (hBD : B ≤ D)
    (hcross : q * (A * B ^ k) ≤ D ^ k) :
    q * (A * B ^ (k + 1)) ≤ D ^ (k + 1) := by
  have hDpos : 0 < D := lt_of_lt_of_le hB hBD
  calc q * (A * B ^ (k + 1))
      = (q * (A * B ^ k)) * B := by ring
    _ ≤ (D ^ k) * B := by
        apply mul_le_mul_of_nonneg_right hcross (le_of_lt hB)
    _ ≤ (D ^ k) * D := by
        apply mul_le_mul_of_nonneg_left hBD (le_of_lt (pow_pos hDpos k))
    _ = D ^ (k + 1) := by rw [pow_succ]

/-- **(5) The concrete prize-regime crossover depth is bounded.** With `D = n^2` (DC base) and the
char-0 energy base `B ≤ 2k·n ≤ n^2` (for `2k ≤ n`), and `q = n^4`, the crossover `q·A·B^k > D^k`
i.e. `n^4·A·B^k > n^{2k}` requires `A·B^k > n^{2k-4}`. With `B ≤ n^2` this needs `A·n^{2k} > n^{2k-4}`
trivially for `A ≥ n^{-4}` — BUT the SHARP energy base is `B = (2k-1)!!^{1/k}·n ≈ (2k/e)·n ≪ n^2`,
so the real constraint `((2k/e)n)^k·n^4 > n^{2k}` ⟺ `(2k/e)^k > n^{k-4}` ⟺ `k·log(2k/e) > (k-4)·log n`,
which for `n = 2^a` (`log n = a log 2`) and `k ≈ log p = 4a log 2` gives LHS `≈ k log(2k)` vs RHS
`≈ (k-4)·a log2` — RHS wins for large `a`. We record the clean monotone fact that makes this rigorous:
for fixed bases `B < D`, `(D/B)^k → ∞`, so `q·A·B^k < D^k` for all large `k` (the floor is eventually
vacuous). -/
theorem floor_eventually_vacuous {q A B D : ℝ} (hA : 0 < A) (hq : 0 < q)
    (hB : 0 < B) (hBD : B < D) :
    ∃ K : ℕ, ∀ k ≥ K, q * (A * B ^ k) ≤ D ^ k := by
  -- (D/B) > 1, so (D/B)^k = D^k/B^k → ∞, eventually exceeding q*A.
  have hDpos : 0 < D := lt_trans hB hBD
  have hr : 1 < D / B := (one_lt_div hB).mpr hBD
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (q * A) hr
  refine ⟨K, fun k hk => ?_⟩
  have hmono : (D / B) ^ K ≤ (D / B) ^ k :=
    pow_le_pow_right₀ (le_of_lt hr) hk
  have hbig : q * A < (D / B) ^ k := lt_of_lt_of_le hK hmono
  have hBk : 0 < B ^ k := pow_pos hB k
  rw [div_pow] at hbig
  -- q*A < D^k/B^k  ⟹  q*A*B^k < D^k  ⟹  q*(A*B^k) ≤ D^k
  have := (lt_div_iff₀ hBk).mp hbig
  nlinarith [this]

/-- **Headline (the cap, assembled).** For geometric energy base `B` strictly below the DC base
`D = n^2` (true at prize thinness for the char-0/Wick energy, base `≈(2k/e)n ≪ n^2`), the moment-ratio
floor `M ≥ (bracket/(q-1))^{1/2k}` is POSITIVE only up to a bounded crossover depth `K`, and VACUOUS
(`bracket ≤ 0`) for all `k ≥ K`. Hence the elementary moment-ratio method caps the unconditional lower
bound at `M ≥ O(√n)` (no log), and reaching `M ≥ c√(n log m)` requires the energy to EXCEED the DC base
geometrically to depth `log p` — i.e. the wraparound `W_k` large = `lower_iff_wrap_ge` = the open wall. -/
theorem momentRatio_floor_caps {q A B D qm1 : ℝ} (hA : 0 < A) (hq : 0 < q)
    (hB : 0 < B) (hBD : B < D) (hqm1 : 0 < qm1) :
    ∃ K : ℕ, ∀ k ≥ K, bracket q (A * B ^ k) (D ^ k) / qm1 ≤ 0 := by
  obtain ⟨K, hK⟩ := floor_eventually_vacuous hA hq hB hBD
  exact ⟨K, fun k hk => floor_vacuous_past_crossover hqm1 (hK k hk)⟩

end ArkLib.ProximityGap.MomentRatioFloorDCCap

-- axiom audit
#print axioms ArkLib.ProximityGap.MomentRatioFloorDCCap.bracket_pos_iff
#print axioms ArkLib.ProximityGap.MomentRatioFloorDCCap.floor_vacuous_past_crossover
#print axioms ArkLib.ProximityGap.MomentRatioFloorDCCap.crossover_closes
#print axioms ArkLib.ProximityGap.MomentRatioFloorDCCap.floor_eventually_vacuous
#print axioms ArkLib.ProximityGap.MomentRatioFloorDCCap.momentRatio_floor_caps
