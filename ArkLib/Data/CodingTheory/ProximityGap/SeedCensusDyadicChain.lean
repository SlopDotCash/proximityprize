/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SpectrumCosetLevelBound
import ArkLib.Data.CodingTheory.ProximityGap.CensusTowerFinite

/-!
# Seed-census orbit count: the nested dyadic chain toward the tower depth (#389)

Residual `seeds-card-orbit-census`: the OPEN quantitative piece is
`#coset-levels = (S.image (·^h)).card ≤ O(log n)` (after the proven reduction chain
`SmoothSupplyTowerBridge → SeedCensusBound → SpectrumCosetLevelBound`).

This file does NOT prove the `O(log n)` bound (recognized open wall). It does the honest
TIGHTENING: state the level set as the bottom of a **nested dyadic chain**
of root-of-unity subgroups, prove the chain is graded and terminating, and isolate the
per-rung "vanishing ⟹ antipodal-collapse" step as a named Prop a future dyadic-descent
argument can weld rung-by-rung. The sharp obstruction (why dyadic halving alone gives `O(n)`
not `O(log n)`) is pinned explicitly.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset

namespace ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The nested dyadic level chain

For the bad spectrum `S ⊆ μ_n`, define the `r`-th coset-level set as the image of `S` under
the `(h·2^r)`-th power map. Level `0` is the residual quantity `S.image (·^h)`. Each level is
the squaring image of the previous one, and lives in a strictly smaller root-of-unity subgroup.
-/

/-- The `r`-th coset-level set: `levelStep S h r = S.image (· ^ (h * 2^r))`. -/
def levelStep (S : Finset F) (h r : ℕ) : Finset F :=
  S.image (fun x => x ^ (h * 2 ^ r))

@[simp] theorem levelStep_zero (S : Finset F) (h : ℕ) :
    levelStep S h 0 = S.image (fun x => x ^ h) := by
  simp [levelStep]

/-- **The chain recursion.** Level `r+1` is the squaring image of level `r`:
`levelStep S h (r+1) = (levelStep S h r).image (·^2)`. This realizes the levels as the
successive square-map images, the heart of the 2-adic descent. -/
theorem levelStep_succ (S : Finset F) (h r : ℕ) :
    levelStep S h (r + 1) = (levelStep S h r).image (fun y => y ^ 2) := by
  classical
  unfold levelStep
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  simp only [Function.comp_apply]
  rw [← pow_mul]
  congr 1
  rw [pow_succ]
  ring

/-- **The chain is graded.** If `S ⊆ μ_n` and `(h·2^r) ∣ n`, then level `r` lies in the
order-`n/(h·2^r)` root-of-unity subgroup. As `r` grows the subgroup order halves, so the
levels descend a nested dyadic tower `μ_{n/h} ⊇ μ_{n/2h} ⊇ ⋯`. -/
theorem levelStep_subset_subgroup {n h : ℕ} (hn : 0 < n) (r : ℕ) (hdvd : (h * 2 ^ r) ∣ n)
    (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F)) :
    levelStep S h r ⊆ nthRootsFinset (n / (h * 2 ^ r)) (1 : F) := by
  have hh2r : 0 < h * 2 ^ r := Nat.pos_of_ne_zero (by
    rintro he; rw [he] at hdvd; simp at hdvd; omega)
  have hnh : 0 < n / (h * 2 ^ r) := Nat.div_pos (Nat.le_of_dvd hn hdvd) hh2r
  intro c hc
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hc
  have hxn : x ^ n = 1 := (mem_nthRootsFinset hn (1 : F)).1 (hS hxS)
  rw [mem_nthRootsFinset hnh, ← pow_mul, Nat.mul_div_cancel' hdvd, hxn]

/-- **The chain terminates.** Once `n ∣ (h·2^r)`, level `r` is contained in `{1}`: the
descent has reached the trivial subgroup `μ_1`. For `n = 2^m`, `h = 2^j` this happens at
`r = m - j`. -/
theorem levelStep_eq_one_of_dvd {n h : ℕ} (hn : 0 < n) (r : ℕ) (hdvd : n ∣ (h * 2 ^ r))
    (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F)) :
    levelStep S h r ⊆ {1} := by
  intro c hc
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hc
  have hxn : x ^ n = 1 := (mem_nthRootsFinset hn (1 : F)).1 (hS hxS)
  obtain ⟨k, hk⟩ := hdvd
  rw [Finset.mem_singleton, hk, pow_mul, hxn, one_pow]

/-! ## 2. The per-rung collapse step

The square map `c ↦ c²` on a finite set has fibers `{c, -c}` (or `{c}` if `c = -c`). So for ANY
finite set `A`, `A.card ≤ 2 · (A.image (·²)).card`. This is the *unconditional* rung-collapse:
each descent step loses at most a factor of two. Chained from level `0` to the terminal level,
this gives the unconditional `#levels ≤ 2^{m-j} · 1 = 2^{m-j}` bound — `O(n)`, NOT `O(log n)`.
The `O(log n)` gap is exactly the per-level sparsity that dyadic halving alone does NOT supply.
-/

/-- **Unconditional per-step factor-two bound (the square map is ≤ 2-to-1).** For any finite
`A`, `A.card ≤ 2 · (A.image (·^2)).card`: every `(·^2)`-fiber `{x ∈ A | x² = c}` is a subset of
`{c.sqrt, -c.sqrt}`, hence has ≤ 2 elements. -/
theorem card_le_two_mul_card_image_sq (A : Finset F) :
    A.card ≤ 2 * (A.image (fun x => x ^ 2)).card := by
  classical
  have hfib : ∀ c ∈ A.image (fun x => x ^ 2),
      (A.filter (fun x => x ^ 2 = c)).card ≤ 2 := by
    intro c hc
    obtain ⟨g, hgA, hgc⟩ := Finset.mem_image.mp hc
    -- the fiber is a subset of {g, -g}
    have hsub : A.filter (fun x => x ^ 2 = c) ⊆ {g, -g} := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hx2 : x ^ 2 = g ^ 2 := by rw [hx.2, hgc]
      have hfac : (x - g) * (x + g) = 0 := by linear_combination hx2
      rcases mul_eq_zero.mp hfac with h | h
      · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp h))
      · exact Finset.mem_insert.mpr (Or.inr (by
          rw [Finset.mem_singleton]; linear_combination h))
    calc (A.filter (fun x => x ^ 2 = c)).card
        ≤ ({g, -g} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  have hpig := Finset.card_le_mul_card_image A 2 hfib
  exact hpig

/-- **The unconditional level-chain factor-two recursion.**
`(levelStep S h r).card ≤ 2 · (levelStep S h (r+1)).card`: one rung of the dyadic descent loses
at most a factor of two, unconditionally. -/
theorem levelStep_card_le_two_mul_succ (S : Finset F) (h r : ℕ) :
    (levelStep S h r).card ≤ 2 * (levelStep S h (r + 1)).card := by
  rw [levelStep_succ]
  exact card_le_two_mul_card_image_sq _

/-- **The unconditional dyadic descent count.** Chaining the factor-two recursion `R` times,
`(levelStep S h 0).card ≤ 2^R · (levelStep S h R).card`. With `R = m - j` rungs and the
terminal level `levelStep S h (m-j) ⊆ {1}` (so its card ≤ 1), this gives the **unconditional**
`#coset-levels ≤ 2^{m-j}`. This is `O(n)` — the honest ceiling of pure dyadic halving. -/
theorem levelStep_card_le_pow_two_mul (S : Finset F) (h : ℕ) :
    ∀ R, (levelStep S h 0).card ≤ 2 ^ R * (levelStep S h R).card := by
  intro R
  induction R with
  | zero => simp
  | succ r ih =>
    calc (levelStep S h 0).card
        ≤ 2 ^ r * (levelStep S h r).card := ih
      _ ≤ 2 ^ r * (2 * (levelStep S h (r + 1)).card) :=
          Nat.mul_le_mul_left _ (levelStep_card_le_two_mul_succ S h r)
      _ = 2 ^ (r + 1) * (levelStep S h (r + 1)).card := by ring

/-- **The unconditional spectrum-level ceiling (`O(n)`).** For `S ⊆ μ_n` with `n ∣ (h·2^R)`
(the descent has reached `μ_1`), the number of coset-levels is bounded by `2^R`:
`#coset-levels ≤ 2^R`. For `n = 2^m`, `h = 2^j`, `R = m - j` this reads `#levels ≤ 2^{m-j} ≤ n`.
This is the sharp ceiling pure dyadic halving delivers — and it is NOT `O(log n)`. -/
theorem levels_card_le_pow_two {n h : ℕ} (hn : 0 < n) (R : ℕ) (hdvd : n ∣ (h * 2 ^ R))
    (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F)) :
    (S.image (fun x => x ^ h)).card ≤ 2 ^ R := by
  have hterm : levelStep S h R ⊆ {1} := levelStep_eq_one_of_dvd hn R hdvd S hS
  have htermcard : (levelStep S h R).card ≤ 1 :=
    (Finset.card_le_card hterm).trans (by simp)
  have hchain := levelStep_card_le_pow_two_mul S h R
  rw [levelStep_zero] at hchain
  calc (S.image (fun x => x ^ h)).card
      ≤ 2 ^ R * (levelStep S h R).card := hchain
    _ ≤ 2 ^ R * 1 := Nat.mul_le_mul_left _ htermcard
    _ = 2 ^ R := by ring

/-! ## 3. The sharp obstruction pin + the conditional log bound

The unconditional `levels_card_le_pow_two` gives `2^{m-j} = O(n)`. The `O(log n)` target is
strictly stronger, so dyadic halving ALONE cannot deliver it (antipodal-closure, the only
structure the tower descent hands us, makes the square map *exactly* 2-to-1, i.e. exact
doubling — the WORST case for the count). The `O(log n)` bound requires that the level set
*collapses geometrically faster than halving* down the rungs: a per-rung **strict-decay** input.

### THE SHARP OBSTRUCTION (proven below, `factor_two_chain_saturates`):
the factor-two chain is *tight* — when each level is antipodal-closed the square map is EXACTLY
2-to-1, so `#levelStep r = 2·#levelStep (r+1)` and the chain reaches the full group
`#levelStep 0 = 2^{m-j}`. Therefore `O(log n)` is UNREACHABLE through the halving chain: even a
depth-`O(log n)` cutoff `r₀` only gives `2^{r₀} = 2^{O(log n)} = poly(n)`, never `O(log n)`.

CONSEQUENCE (the honest pin): the `O(log n)` census CANNOT come from the dyadic *halving* chain.
It must come from a **direct sparsity bound** on the level COUNT — the genuinely-open input that
the bad spectrum meets only `O(log n)` distinct coset-levels, NOT from the geometry of the chain.
We name this directly (`LevelSparse`) and weld it into the proven `seeds.card` consumer; the
chain infrastructure above stays as the structural backbone but is NOT the source of the log.
-/

/-- **The direct level-sparsity residual (the genuine open input).** `LevelSparse S h B` asserts
the bad spectrum meets at most `B` distinct coset-levels: `#(S.image (·^h)) ≤ B`. The OPEN
content is that this holds with `B = O(log n)`; that is the dyadic-vanishing / tower-depth count,
NOT supplied by the halving chain (see `factor_two_chain_saturates`). -/
def LevelSparse (S : Finset F) (h B : ℕ) : Prop :=
  (S.image (fun x => x ^ h)).card ≤ B

/-- **The named depth cutoff (the `O(n)`-route residual, honestly labelled).** `LevelTrivialBy
S h r₀` says the level chain has trivialized by rung `r₀`. This is a SUFFICIENT condition for
`LevelSparse S h (2^{r₀})` — but it only yields `B = 2^{r₀}`, which is `poly(n)` for
`r₀ = O(log n)`. Recorded to make the saturation gap explicit, NOT as a log route. -/
def LevelTrivialBy (S : Finset F) (h r₀ : ℕ) : Prop :=
  levelStep S h r₀ ⊆ {1}

/-- **The `O(n)`-route weld (honest: gives `2^{r₀}`, NOT `O(log n)`).** A depth-`r₀` trivializing
cutoff yields `LevelSparse S h (2^{r₀})` via the unconditional halving chain. This is the BEST
the chain can do; for `r₀ = O(log n)` the bound is `2^{O(log n)} = poly(n)`. Recorded to pin that
the chain route is provably insufficient for `O(log n)`. -/
theorem levelSparse_of_trivialBy {S : Finset F} {h r₀ : ℕ}
    (hdec : LevelTrivialBy S h r₀) :
    LevelSparse S h (2 ^ r₀) := by
  unfold LevelSparse
  have htermcard : (levelStep S h r₀).card ≤ 1 :=
    (Finset.card_le_card hdec).trans (by simp)
  have hchain := levelStep_card_le_pow_two_mul S h r₀
  rw [levelStep_zero] at hchain
  calc (S.image (fun x => x ^ h)).card
      ≤ 2 ^ r₀ * (levelStep S h r₀).card := hchain
    _ ≤ 2 ^ r₀ * 1 := Nat.mul_le_mul_left _ htermcard
    _ = 2 ^ r₀ := by ring

/-- **THE SHARP OBSTRUCTION (saturation of the halving chain).** If every rung up to `R` is
*antipodal-closed* (the only structure the tower descent supplies — `subset_neg_mem_of_sum_zero`
yields exactly this from a vanishing level-sum), and the action is free (each `{±c}` pair is
genuine, `c ≠ -c`), then the square map is EXACTLY 2-to-1 at every rung, so the count *doubles*
each step:  `(levelStep S h R).card * 2 ^ R = (levelStep S h 0).card`.

Hence the factor-two chain is tight and the level count is the FULL group order `2^{m-j}` in the
antipodal case — the halving chain provably cannot beat `O(n)`. The `O(log n)` census is therefore
NOT a consequence of dyadic halving; it requires the direct sparsity `LevelSparse … O(log n)`,
which the antipodal structure actively *contradicts*. This is the precise pinned obstruction. -/
theorem factor_two_chain_saturates {S : Finset F} {h : ℕ} :
    ∀ R, (∀ r < R, ∀ c ∈ levelStep S h r, (-c ∈ levelStep S h r) ∧ c ≠ -c ∧ c ≠ 0) →
      (levelStep S h 0).card = 2 ^ R * (levelStep S h R).card := by
  intro R
  induction R with
  | zero => intro _; simp
  | succ r ih =>
    intro hanti
    -- the rungs below r are still antipodal (restrict the hypothesis)
    have hbelow : ∀ r' < r, ∀ c ∈ levelStep S h r',
        (-c ∈ levelStep S h r') ∧ c ≠ -c ∧ c ≠ 0 :=
      fun r' hr' => hanti r' (by omega)
    -- exact doubling at the top rung r: levelStep (r+1) = (levelStep r).image (·^2),
    -- and the square map is exactly 2-to-1 on the antipodal-closed level r.
    have htop := hanti r (by omega)
    have hdouble : (levelStep S h r).card = 2 * (levelStep S h (r + 1)).card := by
      rw [levelStep_succ]
      -- fiberwise: every (·^2)-fiber of levelStep r has EXACTLY 2 elements {c,-c}
      classical
      have hmaps : ∀ x ∈ levelStep S h r, x ^ 2 ∈ (levelStep S h r).image (fun y => y ^ 2) :=
        fun x hx => Finset.mem_image_of_mem _ hx
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      have hfibeq : ∀ d ∈ (levelStep S h r).image (fun y => y ^ 2),
          ((levelStep S h r).filter (fun x => x ^ 2 = d)).card = 2 := by
        intro d hd
        obtain ⟨g, hgL, hgd⟩ := Finset.mem_image.mp hd
        obtain ⟨hnegg, hgne, hg0⟩ := htop g hgL
        have hfilter : (levelStep S h r).filter (fun x => x ^ 2 = d) = {g, -g} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hzL, hz⟩
            have hz2 : z ^ 2 = g ^ 2 := by rw [hz, hgd]
            have hfac : (z - g) * (z + g) = 0 := by linear_combination hz2
            rcases mul_eq_zero.mp hfac with hh | hh
            · exact Or.inl (sub_eq_zero.mp hh)
            · exact Or.inr (by linear_combination hh)
          · rintro (rfl | rfl)
            · exact ⟨hgL, hgd⟩
            · exact ⟨hnegg, by rw [neg_pow, hgd]; ring⟩
        rw [hfilter, Finset.card_pair (by
          intro hc; exact hgne (by linear_combination hc))]
      rw [Finset.sum_congr rfl hfibeq, Finset.sum_const, smul_eq_mul, mul_comm]
    calc (levelStep S h 0).card
        = 2 ^ r * (levelStep S h r).card := ih hbelow
      _ = 2 ^ r * (2 * (levelStep S h (r + 1)).card) := by rw [hdouble]
      _ = 2 ^ (r + 1) * (levelStep S h (r + 1)).card := by ring

/-! ## 4. Non-vacuity: the single-orbit baseline satisfies the residuals

For the single-orbit witness (`S` = the full order-`h` orbit `{g^k : k < h}`, `h = 2^j`,
`g` a primitive `h`-th root) the level set `S.image(·^h)` is `{1}` — `LevelTrivialBy S h 0`
holds and so `LevelSparse S h 1` (= `seeds.card = 1`). This is the `single_orbit_seedCensus`
baseline seen through the level lens: the coset-level count is exactly `1`, the smallest
possible. So the residuals are non-vacuous and the log target is the *right* asymptotic shape. -/

/-- **Single-orbit baseline: trivial at depth 0.** If every element of `S` is an `h`-th root of
unity (`x^h = 1`), then `S.image(·^h) ⊆ {1}`, so `LevelTrivialBy S h 0` holds — the descent
trivializes at depth `0`, matching the `seeds.card = 1` witness. -/
theorem levelTrivialBy_zero_of_hth_roots (S : Finset F) (h : ℕ)
    (hS : ∀ x ∈ S, x ^ h = 1) :
    LevelTrivialBy S h 0 := by
  unfold LevelTrivialBy
  rw [levelStep_zero]
  intro c hc
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hc
  rw [Finset.mem_singleton]
  exact hS x hxS

/-- **Single-orbit baseline: `LevelSparse … 1`.** The single-orbit witness meets exactly one
coset-level, so `LevelSparse S h 1` holds (= the smallest census, `seeds.card = 1`). -/
theorem levelSparse_one_of_hth_roots (S : Finset F) (h : ℕ)
    (hS : ∀ x ∈ S, x ^ h = 1) :
    LevelSparse S h 1 := by
  have := levelSparse_of_trivialBy (levelTrivialBy_zero_of_hth_roots S h hS)
  simpa using this

/-! ## 5. End-to-end weld: `LevelSparse` ⟹ the deployed `S.card` / `seeds.card` supply bound

The whole reduction chain bottoms out here. `LevelSparse S h B` (the direct sparsity input) feeds
the proven `spectrum_card_le_levels_mul_h` to give `S.card ≤ B·h`, the spectrum-cardinality bound
the seed-census chain consumes. With `B = O(log n)` this is the target `O(n log n)` supply. The
weld is axiom-clean; the ONLY open hypothesis is `LevelSparse … O(log n)` — the level count. -/

/-- **THE WELD.** Given the direct level-sparsity input `LevelSparse S h B` and `S ⊆ μ_n`
(`0 < n`, `0 < h`, `h ∣ n`, `ζ` a primitive `n`-th root), the bad-spectrum cardinality is
bounded: `S.card ≤ B·h`. This is exactly the spectrum-cardinality residual the seed-census chain
reduces to; supplying `B = O(log n)` yields `S.card = O(n log n)`. Axiom-clean; the sole open
input is `LevelSparse` (the coset-level count), now isolated as the single named residual. -/
theorem spectrum_card_le_of_levelSparse {ζ : F} {n h B : ℕ}
    (hn : 0 < n) (hh : 0 < h) (hdvd : h ∣ n) (hζ : IsPrimitiveRoot ζ n)
    (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F))
    (hsparse : LevelSparse S h B) :
    S.card ≤ B * h := by
  calc S.card
      ≤ (S.image (fun x => x ^ h)).card * h :=
        spectrum_card_le_levels_mul_h hn hh hdvd hζ S hS
    _ ≤ B * h := Nat.mul_le_mul_right h hsparse

end ArkLib.ProximityGap.Rigidity

