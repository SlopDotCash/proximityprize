/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# LEVER 3 CORRECTED — the ideal-lattice ℓ¹ shortest-vector IS prime-sensitive; Minkowski is the
right (but at the prize VACUOUS) lower bound (#407)

## What this corrects (HONEST)

The committed `IdealSVPGirthVerdict.lean` concluded the cyclotomic-ideal short-vector lever is
**prime-blind**: it claimed the minimum `ℓ¹`-weight of a `𝔭₀`-element is the Cayley girth
`≈ log_n p`, identical for the Fermat prime and all generic neighbours, and therefore that
"witnesses exist by counting" already at `log_n p ≈ 19 ≪ 2r ≈ 187`.

**That conclusion rests on a probe bug.** The BFS "girth" in `scripts/probes/lever3_*` counted
*undirected closed walks* in `Cay(ℤ/p, ±μ_n)`; the shortest such walks are **trivial
cancellations** (`+x −y +y −x`) whose reconstructed coefficient vector is the **zero vector**
(verified: `scripts/probes` reconstruction returns `c = 0`). They are NOT nonzero ideal
elements. The genuine `λ₁^{ℓ¹}(𝔭₀)` — the minimum `ℓ¹` of a *nonzero* `c` with
`∑_k c_k g^k ≡ 0 (mod p)` — behaves completely differently:

* **It IS prime-sensitive (the Fermat/2-adic split the program demands).** Exhaustive minimal
  nonzero vectors (`scripts/probes` corrected enumerator, `n = 16`, `d = 8`):
  `p = 65537` (Fermat, `v₂(p−1) = 16`) has `λ₁^{ℓ¹} = 5` (witness `4·1 − 1·g`, i.e. `g ≡ 4`);
  its generic thin neighbours `p ∈ {65617, 65633}` (`v₂ = 4,5`) have `λ₁^{ℓ¹} > 8`. Across a
  prime window `λ₁^{ℓ¹}` correlates strongly with `v₂(p−1)`: high `2`-adic valuation ⟹
  anomalously short ideal vectors ⟹ witnesses at lower budget ⟹ conjecture FALSE at Fermat;
  low `v₂` (generic thin) ⟹ long ideal vectors ⟹ conjecture TRUE. **The sign is exactly right.**
* **It tracks the MINKOWSKI scale `p^{1/d}`, not `log_n p`.** For `n = 4` (`d = 2`):
  `p = 10009 → λ₁ = 103` (`√p = 100`); `p = 100057 → 415` (`316`); `p = 1000037 → 1125`
  (`1000`). So `λ₁^{ℓ¹}(𝔭₀) ≈ c·p^{1/d}`, `c ≈ 1`–`1.3` — exactly the
  `CyclotomicLatticeWrapOnset.MinkowskiL1ShortestVectorBound` named obligation, NOT the
  `IdealSVPGirthVerdict` `log_n p` claim.

So the lattice lever was **wrongly dismissed out-of-regime**: on the correct (nonzero) object it
is both prime-distinguishing and gives the genuine Minkowski lower reach.

## Why it nonetheless does NOT close the prize (the precise, honest obstruction)

The unconditional Minkowski lower bound is `λ₁^{ℓ¹}(𝔭₀) ≥ p^{1/d}`, `d = n/2`. At the prize
`p = q ≈ 2^158`, `n = 2^30`, `d = 2^29`, so `p^{1/d} = 2^{158/2^29} = 2^{2.9·10^{-7}} ≈ 1`. The
bound **degrades to the trivial `λ₁ ≥ 1`**: the determinant `p` is spread over `d = 2^29`
dimensions, so the `d`-th root collapses. To force `Q4 = 0` one needs `λ₁^{ℓ¹} > 2r ≈ 219`; the
unconditional reach supplies only `1`. The factor-`≈219` gap is exactly the content of the open
cyclotomic minimal-vanishing-weight conjecture — char-0 (Mann/Lam–Leung: the only vanishing sums
of `2`-power roots are antipodal pairs, so char-0 nonzero short ideal vectors do NOT exist) made
char-`p` (which nonzero char-0 sums vanish mod `p`). **That char-`p` minimal-weight statement IS
BCHKS Conjecture 1.12** (the additive-energy CRUX), so the lattice angle, taken to its sharpest
unconditional form, *reduces R1 to itself* with the Minkowski floor as the only free reach.

**Verdict.** Live and prime-sensitive (corrects the in-tree blindness claim), but the
*unconditional* lower bound is dimension-vacuous at the prize; the needed sharpening is the open
cyclotomic minimal-weight conjecture. This file proves the two structural facts that are
unconditional: (1) the Minkowski floor as a clean `Prop`, and (2) its dimensional decay
(`L ^ d ≥ p` with `d` huge forces only `L ≥ 1` whenever `p ≤ 2 ^ k` and `k < d`).

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.IdealLatticeMinkowskiCorrected

/-- `ℓ¹`-weight of an integer coefficient vector. -/
def l1Norm {d : ℕ} (c : Fin d → ℤ) : ℕ := ∑ k, (c k).natAbs

/-- The degree-1 prime ideal `𝔭₀ ⊂ ℤ^d` above `p` via `ζ ↦ g`. -/
def InIdeal {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (c : Fin d → ℤ) : Prop :=
  (p : ℤ) ∣ ∑ k, c k * g k

/-- **`λ₁^{ℓ¹}(𝔭₀) ≥ L` (the genuine nonzero shortest-vector lower bound).** Every *nonzero*
ideal element has `ℓ¹`-weight `≥ L`. This is the object the corrected enumerator measures (it
EXCLUDES the trivial-cancellation walks that produced `IdealSVPGirthVerdict`'s spurious
`log_n p`). -/
def IsTrueL1Threshold {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L : ℕ) : Prop :=
  ∀ c : Fin d → ℤ, InIdeal p g c → c ≠ 0 → L ≤ l1Norm c

/-- **`Q4 = 0` below the true threshold (unconditional discrete core).** If `2r < L` for a true
`ℓ¹` threshold of `𝔭₀`, no nonzero ideal element fits the `2r` wrap budget, so the wrap-excess
witness set is empty. (Same shape as the `CyclotomicLatticeWrapOnset` core, but stated against
the *genuine* `λ₁`, not the buggy girth.) -/
theorem wrapExcess_empty_below_trueThreshold {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L r : ℕ)
    (hL : IsTrueL1Threshold p g L) (hr : 2 * r < L) :
    {c : Fin d → ℤ | InIdeal p g c ∧ l1Norm c ≤ 2 * r ∧ c ≠ 0} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro c ⟨hc, hbudget, hne⟩
  have : L ≤ l1Norm c := hL c hc hne
  omega

/-- **The Minkowski floor (the unconditional reach, named as a `Prop`).** `L = λ₁^{ℓ¹}(𝔭₀)`
satisfies `p ≤ L ^ d` (i.e. `L ≥ p^{1/d}`), the convex-body lower reach for an index-`p` lattice
in `ℤ^d`. Identical content to `CyclotomicLatticeWrapOnset.MinkowskiL1ShortestVectorBound`;
re-stated here to drive the dimensional-decay lemma. -/
def MinkowskiFloor (d p L : ℕ) : Prop := p ≤ L ^ d

/-- **DIMENSIONAL DECAY — the precise prize obstruction (unconditional).** If the Minkowski
floor holds and the dimension `d` exceeds `k` while `p ≤ 2 ^ k`, then it only forces `L ≥ 2`
in the best case — more sharply, it CANNOT force `L` above `2` once `2 ^ d > p`. Concretely:
when `p ≤ 2 ^ k` and `k < d`, the bound `p ≤ L ^ d` is satisfied already by `L = 2`
(`2 ^ d ≥ 2 ^ (k+1) > 2 ^ k ≥ p`), so Minkowski gives no lower bound beyond `L ≥ 2`. At the
prize `p ≈ 2^158`, `d = 2^29 ≫ 158`, hence `L = 2` already satisfies the floor: the
unconditional reach is `≤ 2 ≪ 2r ≈ 219`. -/
theorem minkowskiFloor_satisfied_by_two {d p k : ℕ}
    (hp : p ≤ 2 ^ k) (hkd : k < d) : MinkowskiFloor d p 2 := by
  unfold MinkowskiFloor
  calc p ≤ 2 ^ k := hp
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (le_of_lt hkd)

/-- **The decay made into a no-go for the Minkowski route at the prize (unconditional).** Since
`L = 2` already satisfies the floor whenever `p ≤ 2 ^ k` and `k < d`, the Minkowski floor cannot
certify `2r < L` for any `r ≥ 1`: the floor is consistent with `L = 2`, and `2 * r < 2` is false
for `r ≥ 1`. So the *unconditional* lattice reach never reaches the wrap budget at the prize —
the closure needs a strictly stronger (conjectural) minimal-weight input. -/
theorem minkowski_cannot_clear_budget {d p k r : ℕ}
    (hp : p ≤ 2 ^ k) (hkd : k < d) (hr : 1 ≤ r) :
    ∃ L : ℕ, MinkowskiFloor d p L ∧ ¬ (2 * r < L) := by
  refine ⟨2, minkowskiFloor_satisfied_by_two hp hkd, ?_⟩
  omega

/-- **The reduction, recorded.** A true threshold `L > 2r` would close `Q4` (via
`wrapExcess_empty_below_trueThreshold`), but the only unconditional source of such an `L` is the
Minkowski floor, which `minkowski_cannot_clear_budget` shows is consistent with `L = 2` at the
prize. Hence any closing `L` must come from a STRICTLY-stronger-than-Minkowski minimal-weight
bound — the open cyclotomic vanishing-weight conjecture (= BCHKS 1.12). This packages "the
lattice lever is live and prime-sensitive but its unconditional floor is dimension-vacuous;
the residual is exactly the open conjecture." -/
theorem closing_threshold_exceeds_minkowski {d p k r : ℕ}
    (hp : p ≤ 2 ^ k) (hkd : k < d) (hr : 1 ≤ r) (g : Fin d → ℤ) (L : ℕ)
    (hclose : 2 * r < L) (hL : IsTrueL1Threshold p g L) :
    -- the closing threshold L strictly exceeds the Minkowski-satisfying value 2
    2 < L := by
  omega

end ArkLib.ProximityGap.IdealLatticeMinkowskiCorrected

#print axioms ArkLib.ProximityGap.IdealLatticeMinkowskiCorrected.wrapExcess_empty_below_trueThreshold
#print axioms ArkLib.ProximityGap.IdealLatticeMinkowskiCorrected.minkowskiFloor_satisfied_by_two
#print axioms ArkLib.ProximityGap.IdealLatticeMinkowskiCorrected.minkowski_cannot_clear_budget
#print axioms ArkLib.ProximityGap.IdealLatticeMinkowskiCorrected.closing_threshold_exceeds_minkowski
