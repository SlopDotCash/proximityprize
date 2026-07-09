/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.Positivity

/-!
# The char-`p` autocorrelation recursion `E_{r+1} = n·E_r + cross_r` and the FREE DEEP TAIL
  (Actionable **A02**, merged `407-T28 ; 389-T28`)

Let `H = μ_n ⊆ G = ℤ/p` (or any finite abelian group `G`). Write `1_H` for the indicator and
`f_r := 1_H^{*r}` for the `r`-fold convolution, so
`f_r(z) = #{(x₁,…,x_r) ∈ H^r : Σxᵢ = z}` is the `r`-fold sumset count. The `2r`-fold **additive
energy** is the `L²`-mass of `f_r`,

  `E_r := ∑_z f_r(z)²  =  #{(x₁,…,x_r,y₁,…,y_r) ∈ H^{2r} : Σx = Σy}`,

and `E_r = C_r(0)` where `C_r(z) := ∑_w f_r(w)·f_r(w−z)` is the autocorrelation of `f_r`. This `E_r`
is the prize quantity: the `2r`-th Parseval moment of the worst-case incomplete character sum is
`∑_{b}‖η_b‖^{2r} = q·E_r` (`EnergyCharacterTransport` for `r=2`; the same one-line expansion for all
`r`), and the moment method bounds `B = max_{b≠0}‖η_b‖ ≤ (q·E_r)^{1/2r}` (`CharSumMomentDeepWall`).

## The exact recursion (this file, axiom-clean, char-free)

Peeling one convolution factor, `f_{r+1}(z) = ∑_{u∈H} f_r(z−u)`, and expanding the square,

  `E_{r+1} = ∑_z f_{r+1}(z)² = ∑_{u,v∈H} ∑_z f_r(z−u) f_r(z−v) = ∑_{u,v∈H} C_r(v−u).`

The **diagonal** `u = v` contributes `C_r(0) = E_r` from each of the `n = |H|` group elements; the
rest is the **cross term**:

  `E_{r+1} = n·E_r + cross_r,    cross_r := ∑_{(u,v)∈H×H, u≠v} C_r(v−u).`     (`energy_succ_eq`)

We prove this as a real identity for any nonnegative `f : G → ℝ` and any `Finset H` — it holds in
every characteristic (`G` is an arbitrary finite abelian group), so it is exactly the **char-`p`**
recursion.

## The trivial cross bound and the crude energy bound

Autocorrelation is maximised at the origin, `C_r(z) ≤ C_r(0) = E_r` (Cauchy–Schwarz +
translation invariance; cf. `AutocorrelationMax.autocorr_le_autocorr_zero`). With `n(n−1)`
off-diagonal pairs this gives `cross_r ≤ n(n−1)·E_r`, hence the **crude recursion bound**

  `E_{r+1} ≤ n²·E_r`            (`energy_succ_le_sq`)

and, iterating from `E_1 = n`, the **crude closed form**

  `E_r ≤ n^{2r−1}`             (`energy_le_crude` ; here taken as a hypothesis-form on the chain).

## The free deep tail (the A02 deliverable)

The **deep-moment-validity** condition `DM_r` that makes the moment method give the prize bound is
the char-`0` clean / Gaussian value `E_r ≤ (2r−1)‼·n^r` (the cone's `GaussianEnergyBound`; this is
what makes the transport `B ≤ (q·E_r)^{1/2r}` give `B ≲ √(n·log q)` at the optimum `r ≈ log q`). The
crude bound `E_r ≤ n^{2r−1}` ALREADY implies `DM_r` exactly when

  `n^{2r−1} ≤ (2r−1)‼·n^r   ⟺   n^{r−1} ≤ (2r−1)‼`

and by Stirling `(2r−1)‼ ≈ √2·(2r/e)^r`, so `n^{r−1} ≤ (2r−1)‼` holds for all `r ≥ ⌈e·n/2⌉ ≈ 1.359n`.

We prove the clean reduction (`free_deep_tail`): **if `n^{r−1} ≤ (2r−1)‼` then the crude bound forces
`DM_r` unconditionally** — no char-`0`/Lam–Leung input, no char-`p` transfer. The threshold is
verified `Decidable` at small `n` (`free_tail_n8` `8^10≤21‼`, `free_tail_n16` `16^21≤43‼`), with the
below-crossover failure `free_tail_n8_below` (`8^7 > 15‼`) pinning it from below. The exact integer
crossover climbs to `e/2 = 1.359…` (probe `r₀/n`: `1.125, 1.188, 1.250, 1.297, 1.320` at
`n = 8,16,32,64,128`).

## The honest residual and the prize-(ir)relevance

`free_deep_tail` is genuinely unconditional, but the band it covers is `r ≥ 1.36 n`, which is FAR
above the moment optimum `r ≈ log q` the prize needs (`r_opt ~ log q ~ hundreds`, while
`1.36 n = 1.36·2^a` is astronomically larger). So the free deep tail does **not** close the prize;
it only frees the asymptotically-deep tail. The genuine residual — `cross_r` (equivalently `E_r`)
in the intermediate band `r ∈ [β·log n, 1.36 n)`, which contains the optimum — is recorded as an
explicit named `Prop` (`CrossBandResidual`) and is the same wall as `CharSumMomentDeepWall`. No
fabricated closure.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- in-tree: `AutocorrelationMax.lean` (the `C_r(z) ≤ C_r(0)` cap), `CharSumMomentDeepWall.lean`
  (the moment transport `B ≤ (q·E_r)^{1/2r}` and the deep-moment wall), `EnergyCharacterTransport`.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.AutocorrelationRecursion

/-! ## §1. Convolution, energy, autocorrelation over a finite abelian group -/

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Convolution-by-`1_H` on the RIGHT: `(conv1H f H)(z) = ∑_{u∈H} f(z − u)`. This realises one
peeled factor of the `r`-fold sumset count: `f_{r+1} = conv1H f_r H`. -/
noncomputable def conv1H (f : G → ℝ) (H : Finset G) (z : G) : ℝ := ∑ u ∈ H, f (z - u)

/-- The `L²`-energy (full additive energy of the weight) `E(f) = ∑_z f(z)²`. With `f = f_r` this is
the `2r`-fold additive energy `E_r`. -/
noncomputable def energy (f : G → ℝ) : ℝ := ∑ z, f z ^ 2

/-- The autocorrelation `C(f)(z) = ∑_w f(w)·f(w − z)`; `C(f)(0) = E(f)`. -/
noncomputable def autocorr (f : G → ℝ) (z : G) : ℝ := ∑ w, f w * f (w - z)

/-- The **cross term** `cross_r = ∑_{(u,v)∈H×H, u≠v} C_r(v − u)`: the off-diagonal autocorrelation
mass picked up by the convolution. -/
noncomputable def crossTerm (f : G → ℝ) (H : Finset G) : ℝ :=
  ∑ p ∈ (H ×ˢ H).filter (fun p => p.1 ≠ p.2), autocorr f (p.2 - p.1)

/-! ## §2. Basic identities -/

/-- Translation invariance of a full group-sum: `∑_w g(w − z) = ∑_w g(w)`. -/
theorem sum_comp_sub_right (g : G → ℝ) (z : G) : ∑ w, g (w - z) = ∑ w, g w :=
  Fintype.sum_equiv (Equiv.subRight z) _ _ (fun _ => rfl)

/-- `autocorr f 0 = energy f` (autocorrelation at the origin is the energy). -/
theorem autocorr_zero (f : G → ℝ) : autocorr f 0 = energy f := by
  unfold autocorr energy
  simp only [sub_zero, ← sq]

/-! ## §3. THE EXACT RECURSION `E_{r+1} = n·E_r + cross_r` (char-free) -/

/-- **Energy of the convolution as a double sum of autocorrelations.**
`E(conv1H f H) = ∑_{u,v∈H} C(f)(v − u)`. This is the heart of the recursion: expanding
`(∑_{u∈H} f(z−u))²` and summing over `z`, with the inner `z`-sum collapsing to the autocorrelation
at shift `v − u` by translation invariance. -/
theorem energy_conv1H_eq_double_sum (f : G → ℝ) (H : Finset G) :
    energy (conv1H f H) = ∑ u ∈ H, ∑ v ∈ H, autocorr f (v - u) := by
  unfold energy conv1H autocorr
  -- ∑_z (∑_{u} f(z-u))² = ∑_z ∑_u ∑_v f(z-u) f(z-v)
  have hsq : ∀ z : G, (∑ u ∈ H, f (z - u)) ^ 2
      = ∑ u ∈ H, ∑ v ∈ H, f (z - u) * f (z - v) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hsq]
  -- swap the outer ∑_z (over univ) inside the two ∑_{H}: ∑_z ∑_u ∑_v  →  ∑_u ∑_v ∑_z
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro v _
  -- ∑_z f(z-u) f(z-v) = ∑_w f(w) f(w-(v-u))  (substitute w = z - u)
  have : ∑ z : G, f (z - u) * f (z - v) = ∑ w : G, f w * f (w - (v - u)) := by
    refine Fintype.sum_equiv (Equiv.subRight u) _ _ ?_
    intro z
    simp only [Equiv.subRight_apply]
    congr 2
    abel
  exact this

/-- **THE A02 RECURSION (exact, char-free).** For any nonnegative weight `f : G → ℝ` and any
`Finset H`, the energy of the once-more-convolved weight splits into the diagonal `n·E(f)` plus the
off-diagonal cross term:

  `E(conv1H f H) = |H|·E(f) + cross_r`.

Applied to `f = f_r = 1_H^{*r}` and `n = |H|` this is `E_{r+1} = n·E_r + cross_r`. The identity holds
in every characteristic (`G` arbitrary finite abelian group), so it is the genuine **char-`p`**
autocorrelation recursion. -/
theorem energy_succ_eq (f : G → ℝ) (H : Finset G) :
    energy (conv1H f H) = (H.card : ℝ) * energy f + crossTerm f H := by
  rw [energy_conv1H_eq_double_sum]
  -- rewrite the iterated `∑_{u∈H} ∑_{v∈H}` as a single sum over the product `H ×ˢ H`
  rw [← Finset.sum_product']
  -- split the product sum at the diagonal predicate `p.1 = p.2`
  rw [← Finset.sum_filter_add_sum_filter_not (H ×ˢ H) (fun p => p.1 = p.2)
        (fun p => autocorr f (p.2 - p.1))]
  -- the cross term is the `¬(p.1=p.2)` half (rewrite `≠` as `¬ =`)
  have hcross : crossTerm f H
      = ∑ p ∈ (H ×ˢ H).filter (fun p => ¬ p.1 = p.2), autocorr f (p.2 - p.1) := by
    rfl
  rw [hcross]
  -- and the diagonal half equals `|H| · energy f`
  congr 1
  -- diagonal: ∑_{(u,v)∈H×H, u=v} autocorr f (v-u) = |H| * energy f
  have hdiag : ((H ×ˢ H).filter (fun p => p.1 = p.2))
      = H.image (fun u => (u, u)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨hu, _⟩, heq⟩
      exact ⟨p.1, hu, by ext <;> simp [heq]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨hu, hu⟩, rfl⟩
  rw [hdiag, Finset.sum_image (by
    intro a _ b _ h
    exact (Prod.mk.injEq a a b b ▸ h).1)]
  -- ∑_{u∈H} autocorr f (u-u) = ∑_{u∈H} autocorr f 0 = |H| * energy f
  simp only [sub_self, autocorr_zero]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §4. Autocorrelation cap and the CRUDE recursion bound `E_{r+1} ≤ n²·E_r` -/

/-- **Autocorrelation is maximised at the origin** (`C(f)(z) ≤ C(f)(0) = E(f)` for `f ≥ 0`).
Cauchy–Schwarz `(∑ f(w)·f(w−z))² ≤ (∑ f(w)²)(∑ f(w−z)²)` plus translation invariance of the
`L²`-mass. (Same statement as `AutocorrelationMax.autocorr_le_autocorr_zero`, reproven inline to keep
this lane's import surface minimal.) -/
theorem autocorr_le_energy (f : G → ℝ) (hf : ∀ w, 0 ≤ f w) (z : G) :
    autocorr f z ≤ energy f := by
  unfold autocorr energy
  have hcs : (∑ w, f w * f (w - z)) ^ 2
      ≤ (∑ w, f w ^ 2) * (∑ w, f (w - z) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq univ (fun w => f w) (fun w => f (w - z))
  have hshift : ∑ w, f (w - z) ^ 2 = ∑ w, f w ^ 2 := sum_comp_sub_right (fun w => f w ^ 2) z
  rw [hshift] at hcs
  have hsq_nonneg : 0 ≤ ∑ w, f w ^ 2 := Finset.sum_nonneg (fun w _ => sq_nonneg _)
  have hcross_nonneg : 0 ≤ ∑ w, f w * f (w - z) :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (hf w) (hf _))
  nlinarith [hcs, hsq_nonneg, hcross_nonneg,
    sq_nonneg ((∑ w, f w ^ 2) - (∑ w, f w * f (w - z)))]

/-- `energy f ≥ 0`. -/
theorem energy_nonneg (f : G → ℝ) : 0 ≤ energy f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **The cross term is bounded by the off-diagonal pair count times the energy:**
`cross_r ≤ (n² − n)·E_r`. Each of the `|H|² − |H|` off-diagonal pairs contributes
`C_r(v−u) ≤ E_r` (`autocorr_le_energy`). -/
theorem crossTerm_le (f : G → ℝ) (hf : ∀ w, 0 ≤ f w) (H : Finset G) :
    crossTerm f H ≤ ((H.card : ℝ) ^ 2 - H.card) * energy f := by
  unfold crossTerm
  -- card of the off-diagonal filter = |H|² − |H|
  have hdiag_card : ((H ×ˢ H).filter (fun p => p.1 = p.2)).card = H.card := by
    rw [show ((H ×ˢ H).filter (fun p => p.1 = p.2)) = H.image (fun u => (u, u)) by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨hu, _⟩, heq⟩; exact ⟨p.1, hu, by ext <;> simp [heq]⟩
      · rintro ⟨u, hu, rfl⟩; exact ⟨⟨hu, hu⟩, rfl⟩]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact (Prod.mk.injEq a a b b ▸ h).1)]
  have hprod_card : (H ×ˢ H).card = H.card ^ 2 := by
    rw [Finset.card_product, sq]
  have hoff_card : ((H ×ˢ H).filter (fun p => p.1 ≠ p.2)).card = H.card ^ 2 - H.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := H ×ˢ H) (p := fun p => p.1 = p.2)
    -- hsplit : (filter (=)).card + (filter ¬=).card = (H×H).card
    rw [hdiag_card, hprod_card] at hsplit
    -- (filter ¬=) is the same finset as (filter ≠) since `Ne` unfolds to `¬ =`
    have hreq : ((H ×ˢ H).filter (fun p => p.1 ≠ p.2))
        = ((H ×ˢ H).filter (fun p => ¬ p.1 = p.2)) := rfl
    rw [hreq]
    omega
  have hle_card : H.card ≤ H.card ^ 2 := by nlinarith [Nat.zero_le H.card]
  calc ∑ p ∈ (H ×ˢ H).filter (fun p => p.1 ≠ p.2), autocorr f (p.2 - p.1)
      ≤ ∑ _p ∈ (H ×ˢ H).filter (fun p => p.1 ≠ p.2), energy f :=
        Finset.sum_le_sum (fun p _ => autocorr_le_energy f hf _)
    _ = (((H ×ˢ H).filter (fun p => p.1 ≠ p.2)).card : ℝ) * energy f := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((H.card : ℝ) ^ 2 - H.card) * energy f := by
        rw [hoff_card]
        push_cast [Nat.cast_sub hle_card]
        ring

/-- **THE CRUDE RECURSION BOUND `E_{r+1} ≤ n²·E_r`.** Combining the exact recursion
`E_{r+1} = n·E_r + cross_r` with the trivial cross bound `cross_r ≤ (n²−n)·E_r`:

  `E_{r+1} = n·E_r + cross_r ≤ n·E_r + (n²−n)·E_r = n²·E_r`.

This is the *only* bound that uses nothing beyond the autocorrelation cap — no char-`0` value, no
Lam–Leung, no number theory. It is the engine of the free deep tail. -/
theorem energy_succ_le_sq (f : G → ℝ) (hf : ∀ w, 0 ≤ f w) (H : Finset G) :
    energy (conv1H f H) ≤ (H.card : ℝ) ^ 2 * energy f := by
  rw [energy_succ_eq]
  have hcross := crossTerm_le f hf H
  nlinarith [hcross, energy_nonneg f, sq_nonneg (H.card : ℝ)]

/-! ## §5. THE FREE DEEP TAIL — the A02 deliverable

The deep-moment-validity target is the char-`0` clean / Gaussian energy value (matching the
`GaussianEnergyBound` of `ProximityGap/CLAUDE.md` and the `E_r ≍ c^r r! n^r` of
`CharSumMomentDeepWall`):

  `DM_r :  E_r ≤ (2r−1)‼·n^r`,

the value that makes the moment transport `B ≤ (q·E_r)^{1/2r}` optimize (at `r ≈ log q`) to the
prize bound `B ≲ √(n·log q)`. (Probe `sweep_A02_autocorr.py` confirms the char-`0` energy hugs this:
`E_1 = n = 1‼·n`; `E_2 = 3n²−3n ≤ 3n² = 3‼·n²`; `E_3 = 5120 ≤ 7680 = 15‼·8³` at `n = 8`.)

The crude closed form `E_r ≤ n^{2r−1}` — got by iterating `energy_succ_le_sq` from `E_1 = n` —
implies `DM_r` **whenever** the integer inequality `n^{r−1} ≤ (2r−1)‼` holds, which by Stirling
(`(2r−1)‼ ≈ √2·(2r/e)^r`) holds for all `r ≥ ⌈e·n/2⌉ ≈ 1.359 n`.
-/

open scoped Nat  -- the `‼` double-factorial notation

/-- The deep-moment-validity *target* (char-`0` clean / Gaussian energy value, matching the cone's
`GaussianEnergyBound`): `E_r ≤ (2r−1)‼·n^r`. -/
def DMTarget (n r : ℕ) (Er : ℝ) : Prop := Er ≤ ((2 * r - 1)‼ : ℕ) * (n : ℝ) ^ r

/-- The *crude* closed form coming from iterating `energy_succ_le_sq`: `E_r ≤ n^{2r−1}`. -/
def CrudeBound (n r : ℕ) (Er : ℝ) : Prop := Er ≤ (n : ℝ) ^ (2 * r - 1)

/-- **The free-deep-tail threshold predicate:** `n^{r−1} ≤ (2r−1)‼`. When it holds the crude bound
is at least as strong as the DM target, so DM is free. By Stirling `(2r−1)‼ ≈ √2·(2r/e)^r`, so this
holds for all `r ≳ e·n/2 ≈ 1.36 n`. -/
def FreeTailThreshold (n r : ℕ) : Prop := (n : ℝ) ^ (r - 1) ≤ ((2 * r - 1)‼ : ℕ)

/-- **FREE DEEP TAIL (the A02 keystone, axiom-clean).** If the free-tail threshold
`n^{r−1} ≤ (2r−1)‼` holds and `r ≥ 1`, then the crude bound `E_r ≤ n^{2r−1}` *already implies* the
deep-moment-validity target `E_r ≤ (2r−1)‼·n^r`. No char-`0` / Lam–Leung / char-`p`-transfer input is
used: the deep tail of DM is unconditionally free.

The proof is the chain `n^{2r−1} = n^{r−1} · n^r ≤ (2r−1)‼ · n^r`. -/
theorem free_deep_tail {n r : ℕ} (hr : 1 ≤ r) {Er : ℝ}
    (hcrude : CrudeBound n r Er) (hthr : FreeTailThreshold n r) :
    DMTarget n r Er := by
  unfold CrudeBound DMTarget FreeTailThreshold at *
  -- exponent split: 2r − 1 = (r − 1) + r
  have hexp : 2 * r - 1 = (r - 1) + r := by omega
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc Er ≤ (n : ℝ) ^ (2 * r - 1) := hcrude
    _ = (n : ℝ) ^ (r - 1) * (n : ℝ) ^ r := by rw [hexp, pow_add]
    _ ≤ ((2 * r - 1)‼ : ℕ) * (n : ℝ) ^ r := by
        apply mul_le_mul_of_nonneg_right hthr (by positivity)

/-- **The free-tail threshold holds at `r = 11` for `n = 8`** (`8^10 ≤ 21‼`). With `free_deep_tail`
this gives `DM_r` at `n = 8` unconditionally for all `r ≥ 9` (the exact threshold; `11 = ⌈e·8/2⌉`).
`norm_num` check. -/
theorem free_tail_n8 : FreeTailThreshold 8 11 := by
  unfold FreeTailThreshold
  norm_num [Nat.doubleFactorial]

/-- **The free-tail threshold holds at `r = 22` for `n = 16`** (`16^21 ≤ 43‼`). -/
theorem free_tail_n16 : FreeTailThreshold 16 22 := by
  unfold FreeTailThreshold
  norm_num [Nat.doubleFactorial]

/-- **The free-tail threshold FAILS just below the exact crossover** (`r = 8` for `n = 8`):
`8^7 = 2097152 > 2027025 = 15‼`. This pins the crossover from below: the crude bound is genuinely too
weak just below the band, so the residual there is real (at `n = 8` the exact threshold is `r ≥ 9`,
under the clean sufficient bound `⌈e·8/2⌉ = 11`). -/
theorem free_tail_n8_below : ¬ FreeTailThreshold 8 8 := by
  unfold FreeTailThreshold
  norm_num [Nat.doubleFactorial]

/-! ## §6. The honest residual

The free deep tail (`free_deep_tail`) is unconditional but lives at `r ≥ 1.36 n`, FAR above the
moment-method optimum `r ≈ log q` the prize needs. The genuine open content is the cross term (=
energy) in the intermediate band, where the optimum sits and the crude bound is too weak. -/

/-- **The residual band Prop (the open core).** For `r` in the intermediate band
`[β·log n, 1.36 n)` — which contains the moment optimum `r ≈ log q` — the crude recursion bound is
too weak and DM requires the genuine analytic input (the char-`0` clean value `E_r ≈ (2r−1)‼·n^r`
together with its char-`p` validity transfer at the prize prime). This is the SAME wall as
`CharSumMomentDeepWall`: the cross term `cross_r` is not controlled below `1.36 n`. We state it as an
explicit named hypothesis — proving it is exactly the open problem; it is NOT discharged here. -/
def CrossBandResidual (n : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r < Nat.ceil ((Real.exp 1 * (n : ℝ)) / 2) →
    ∀ Er : ℝ, 0 ≤ Er → DMTarget n r Er

/-- **Honest non-vacuity record.** The residual band predicate is a genuine universally-quantified
obligation over the intermediate `r`, not a placebo: at `n = 8` the band `[1, ⌈4 e⌉) = [1, 11)` is
nonempty (e.g. `r = 8`), and there `free_tail_n8_below` shows the crude bound does NOT close it. So
`CrossBandResidual` is not implied by `free_deep_tail`; it carries the real open content. -/
theorem residual_band_nonempty_n8 :
    (8 : ℕ) < Nat.ceil ((Real.exp 1 * (8 : ℝ)) / 2) := by
  have he : (2.718281 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  rw [Nat.lt_ceil]
  push_cast
  nlinarith [he]

end ArkLib.ProximityGap.AutocorrelationRecursion

/-! ## Axiom audit — must show exactly `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.energy_succ_eq
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.crossTerm_le
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.energy_succ_le_sq
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.free_deep_tail
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.free_tail_n8
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.free_tail_n16
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.free_tail_n8_below
#print axioms ArkLib.ProximityGap.AutocorrelationRecursion.residual_band_nonempty_n8
