/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvRem_BesselMfold
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvUC_BesselIdentityFormalized

/-!
# The symbolic-`m` Bessel `m`-fold factorization on the ACTUAL energy (#444, avenue F1, TRACK 1)

This brick finishes the char-0 Wick chain by **iterating** the two-direction decoupling bijection
(`_AvRem`'s `zeroSumCount_union_eq_binom_convolution`) over the `m = n/2` antipodal DIRECTIONS of
`μ_{2m}`, for **symbolic `m`**, by induction.

## What `_AvRem` / `_AvUC` already supply (consumed here, not re-derived)

* `_AvRem.zeroSumCount_union_eq_binom_convolution` — for two `AdditivelyDecoupled` directions
  `G, H`, the union zero-sum count is the binomial-weighted convolution of the two per-direction
  counts (a genuine `Finset.card` bijection).
* `_AvUC.zeroSum_negPair_eq_centralBinom` — the per-direction (`m = 1`) count
  `Z_r({1,−1}) = C(2r,r) = centralBinom r` (the `I₀(2x)` base, central binomial).

## What is FORMALIZED here (axiom-clean, no `sorry`, no `native_decide`)

The crux requested by the task: **iterate the convolution over the `m` directions**, reducing the
whole `m`-fold identity to the single clean "mutual decoupling" hypothesis.

1. **`natConv`** — the natural-number convolution-power of a per-direction count function `f`
   (the integer shadow of `_AvW0.cpow`): `natConv f 0 N = [N = 0]`,
   `natConv f (d+1) N = Σ_{a≤N} C(N,a)·f a·natConv f d (N−a)`.

2. **`zeroSumCount_iUnion_eq_natConv`** — **THE INDUCTIVE THEOREM.** Given a family of `d`
   directions `D : Fin d → Finset F`, each with the SAME per-direction count `f` (i.e.
   `zeroSumCount (D j) N = f N`), and the **mutual-decoupling** hypothesis that each new direction
   is `AdditivelyDecoupled` from the union of the earlier ones, the union zero-sum count is the
   `d`-fold convolution `natConv f d N`. This is the `m`-fold Bessel factorization on the genuine
   `Finset.card` energy.

3. **`bessel_mfold_two`** — the `m = 2` rung, fully discharged from the single decoupling instance
   `AdditivelyDecoupled G H` (no symbolic induction needed): the union of two negation-closed
   directions has zero-sum count the binomial convolution of the per-direction counts. With the
   central-binomial base this is the second `I₀(2x)^m` coefficient on the real energy.

4. **`bessel_mfold_step`** — the inductive STEP in isolation: given the `d`-fold identity and that
   direction `d` decouples from the running union, the `(d+1)`-fold identity follows. This is the
   one structural fact the symbolic `m` induction turns on.

5. **`natConv_negDirCount_one`** — the `m = 1` ANCHOR of the bridge to the `_AvW0` EGF model:
   the per-direction central-binomial count gives `natConv negDirCount 1 (2r) = AvW0.Edef r 1
   = C(2r,r)` (via `_AvUC.bessel_identity_mu2`). The general even-length closed form
   `natConv negDirCount d (2r) = AvW0.Edef r d` for symbolic `d` (whose existence would yield
   `Z_r(μ_{2m}) = AvW0.Edef r m`) is NOT landed here — only this `d = 1` case is. It structurally
   matches `_AvW0.cpow`'s recursion but the symbolic-`d` numeric bridge remains a residual
   (see Honest scope below), alongside the single `MutuallyDecoupled` input.

## Honest scope (#444)

This LANDS the symbolic-`m` induction (`zeroSumCount_iUnion_eq_natConv`) and the `m = 2` base
fully, reducing the entire char-0 `m`-fold Bessel identity to ONE clean named input:
`MutuallyDecoupled` — that each antipodal direction of `μ_{2m}` is `AdditivelyDecoupled` from the
union of the others. That input is exactly the content of the proven Lam–Leung two-power theorem
(a vanishing sum of `2^μ`-th roots is a union of antipodal pairs ⇒ no cross-direction cancellation),
already lifted in `_AvX_LamLeungTwoPowerAntipodalBalan` / `_AvUC.antipodal_balance_forces_split`;
mechanically threading the *per-direction-filter is well-defined on a union* bookkeeping into the
`AdditivelyDecoupled.separates` shape for an arbitrary running union is the remaining engineering,
named here as `MutuallyDecoupled` rather than re-proved inline. It is a char-0 brick: the prize is
char-`p`, where wraparound excess `W_r` breaks the EGF identity off a finite bad-prime set.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.AvRem

namespace ArkLib.ProximityGap.Frontier.AvF1

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The natural-number convolution power (integer shadow of `_AvW0.cpow`). -/

/-- The `d`-fold convolution-power of a per-direction count function `f : ℕ → ℕ`:
`natConv f 0 N = [N = 0]`, `natConv f (d+1) N = Σ_{a≤N} C(N,a)·f a·natConv f d (N−a)`.
This is the integer realization of the EGF convolution `_AvW0.cpow`: at the central-binomial
per-direction count it computes `(2r)!·[x^{2r}] I₀(2x)^d`. -/
def natConv (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0,     N => if N = 0 then 1 else 0
  | d + 1, N => ∑ a ∈ Finset.range (N + 1), N.choose a * (natConv f d a * f (N - a))

@[simp] lemma natConv_zero (f : ℕ → ℕ) (N : ℕ) :
    natConv f 0 N = if N = 0 then 1 else 0 := rfl

lemma natConv_succ (f : ℕ → ℕ) (d N : ℕ) :
    natConv f (d + 1) N
      = ∑ a ∈ Finset.range (N + 1), N.choose a * (natConv f d a * f (N - a)) := rfl

/-! ## The mutual-decoupling hypothesis and the inductive `m`-fold factorization.

We model the `m` antipodal directions of `μ_{2m}` as a family `D : Fin d → Finset F`. The single
input is that each direction is additively decoupled from the union of the *earlier* ones — the
Lam–Leung separation extended to a running union. We carry the union of the first `k` directions as
`unionUpto D k`. -/

/-- The union of the first `k` directions `D 0, …, D (k−1)`. -/
def unionUpto {d : ℕ} (D : Fin d → Finset F) : ℕ → Finset F
  | 0     => ∅
  | k + 1 => (unionUpto D k) ∪ (if h : k < d then D ⟨k, h⟩ else ∅)

/-- The **mutual-decoupling input** (the single named Lam–Leung hypothesis): every direction
`D k` is `AdditivelyDecoupled` from the union of the strictly-earlier directions. For the antipodal
directions of `μ_{2m}` this is exactly the content of the proven Lam–Leung two-power theorem (a
vanishing sum of `2^μ`-th roots splits as a union of antipodal pairs, with no cancellation across
distinct directions). -/
def MutuallyDecoupled {d : ℕ} (D : Fin d → Finset F) : Prop :=
  ∀ k : ℕ, (h : k < d) → AdditivelyDecoupled (unionUpto D k) (D ⟨k, h⟩)

/-- `zeroSumCount ∅ N = [N = 0]`: the empty direction contributes the trivial unit. -/
lemma zeroSumCount_empty (N : ℕ) :
    zeroSumCount (∅ : Finset F) N = if N = 0 then 1 else 0 := by
  classical
  unfold zeroSumCount
  cases N with
  | zero =>
      -- the unique empty tuple sums to 0
      have : ((Fintype.piFinset (fun _ : Fin 0 => (∅ : Finset F))).filter
          (fun c => ∑ i, c i = 0)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨fun i => i.elim0, ?_⟩
        ext c
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
        constructor
        · rintro _; funext i; exact i.elim0
        · rintro rfl
          exact ⟨fun i => i.elim0, by simp⟩
      rw [this]; simp
  | succ k =>
      -- no tuple of positive length lands in ∅
      have : ((Fintype.piFinset (fun _ : Fin (k + 1) => (∅ : Finset F))).filter
          (fun c => ∑ i, c i = 0)).card = 0 := by
        rw [Finset.card_eq_zero]
        ext c
        constructor
        · intro hc
          rw [Finset.mem_filter, Fintype.mem_piFinset] at hc
          exact absurd (hc.1 0) (by simp)
        · intro hc; exact absurd hc (Finset.notMem_empty c)
      rw [this]; simp

/-- **THE INDUCTIVE STEP, in isolation.** If the union of the first `d` directions already realizes
the `d`-fold convolution `natConv f d`, the per-direction count is uniformly `f`, and the new
direction `D d` is `AdditivelyDecoupled` from that union, then the union of the first `d+1`
directions realizes `natConv f (d+1)`. The single fact this turns on is the proven two-direction
bijection `_AvRem.zeroSumCount_union_eq_binom_convolution`. -/
theorem bessel_mfold_step {d : ℕ} (D : Fin (d + 1) → Finset F) (f : ℕ → ℕ)
    (hf : ∀ (k : ℕ) (h : k < d + 1) (N : ℕ), zeroSumCount (D ⟨k, h⟩) N = f N)
    (hIH : ∀ N, zeroSumCount (unionUpto D d) N = natConv f d N)
    (hdec : AdditivelyDecoupled (unionUpto D d) (D ⟨d, Nat.lt_succ_self d⟩))
    (N : ℕ) :
    zeroSumCount (unionUpto D (d + 1)) N = natConv f (d + 1) N := by
  classical
  -- unionUpto D (d+1) = unionUpto D d ∪ D d
  have hun : unionUpto D (d + 1) = (unionUpto D d) ∪ D ⟨d, Nat.lt_succ_self d⟩ := by
    show (unionUpto D d) ∪ (if h : d < d + 1 then D ⟨d, h⟩ else ∅)
      = (unionUpto D d) ∪ D ⟨d, Nat.lt_succ_self d⟩
    rw [dif_pos (Nat.lt_succ_self d)]
  rw [hun, zeroSumCount_union_eq_binom_convolution _ _ hdec N, natConv_succ]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hIH a, hf d (Nat.lt_succ_self d) (N - a)]

/-- **THE SYMBOLIC-`m` `m`-fold FACTORIZATION on the actual energy.** Given a family of `d`
directions all with per-direction count `f`, mutually decoupled (the single Lam–Leung input), the
zero-sum count of the union of all `d` directions is the `d`-fold convolution `natConv f d`. This is
the iterated convolution over the `m` antipodal directions of `μ_{2m}`, by induction on `d`. -/
theorem zeroSumCount_iUnion_eq_natConv : ∀ (d : ℕ) (D : Fin d → Finset F) (f : ℕ → ℕ)
    (_ : ∀ (k : ℕ) (h : k < d) (N : ℕ), zeroSumCount (D ⟨k, h⟩) N = f N)
    (_ : MutuallyDecoupled D) (N : ℕ),
    zeroSumCount (unionUpto D d) N = natConv f d N := by
  classical
  intro d
  induction d with
  | zero =>
      intro D f _ _ N
      -- unionUpto D 0 = ∅, natConv f 0 N = [N=0]
      simp only [unionUpto]
      rw [zeroSumCount_empty, natConv_zero]
  | succ d ih =>
      intro D f hf hdec N
      -- restrict the family to the first d directions and apply the step
      set D' : Fin d → Finset F := fun k => D ⟨k.1, Nat.lt_succ_of_lt k.2⟩ with hD'
      -- the truncated union agrees with the full one on `≤ d` (same recursion below `d`)
      have hunion_eq : ∀ k ≤ d, unionUpto D' k = unionUpto D k := by
        intro k hk
        induction k with
        | zero => simp [unionUpto]
        | succ j ihj =>
            have hjd : j < d := hk
            have hjd1 : j < d + 1 := Nat.lt_succ_of_lt hjd
            simp only [unionUpto, dif_pos hjd, dif_pos hjd1, hD']
            rw [ihj (Nat.le_of_lt hjd)]
      have hf' : ∀ (k : ℕ) (h : k < d) (M : ℕ), zeroSumCount (D' ⟨k, h⟩) M = f M := by
        intro k h M; exact hf k (Nat.lt_succ_of_lt h) M
      have hdec' : MutuallyDecoupled D' := by
        intro k hk
        have hku : unionUpto D' k = unionUpto D k := hunion_eq k (Nat.le_of_lt hk)
        have := hdec k (Nat.lt_succ_of_lt hk)
        rw [hku]
        -- D' ⟨k,hk⟩ = D ⟨k, lt_succ_of_lt hk⟩
        simpa [hD'] using this
      have hIH : ∀ M, zeroSumCount (unionUpto D d) M = natConv f d M := by
        intro M
        rw [← hunion_eq d (le_refl d)]
        exact ih D' f hf' hdec' M
      -- apply the step lemma to the full family `D`
      have hdecTop : AdditivelyDecoupled (unionUpto D d) (D ⟨d, Nat.lt_succ_self d⟩) :=
        hdec d (Nat.lt_succ_self d)
      exact bessel_mfold_step D f hf hIH hdecTop N

/-! ## The `m = 2` rung, fully discharged (no symbolic induction). -/

/-- **The `m = 2` Bessel rung on the real energy.** For two directions `G, H` that are a single
`AdditivelyDecoupled` instance, the union zero-sum count is the binomial convolution of the per-
direction counts — the second coefficient of `I₀(2x)^m` on the genuine `Finset.card` energy. -/
theorem bessel_mfold_two (G H : Finset F) (hdec : AdditivelyDecoupled G H) (N : ℕ) :
    zeroSumCount (G ∪ H) N
      = ∑ a ∈ Finset.range (N + 1),
          N.choose a * (zeroSumCount G a * zeroSumCount H (N - a)) :=
  zeroSumCount_union_eq_binom_convolution G H hdec N

/-! ## Bridge to the `_AvW0` EGF model: integer convolution = `(2r)!·cpow I0c`.

The per-direction count for an antipodal direction is `f (2a) = centralBinom a` (and `0` on odd
length). We show the integer convolution `natConv` of this `f` reproduces `_AvW0.Edef` at even
length, so the symbolic-`m` factorization above lands exactly the Bessel identity
`Z_r(μ_{2m}) = AvW0.Edef r m`. We carry the bridge as a clean `m = 1` anchor (the base of the
ladder) plus the structural restatement; the full even-length closed form is `_AvW0`'s
`cpow`-recursion content. -/

/-- The antipodal per-direction count function: central binomial on even lengths, `0` on odd. -/
def negDirCount (N : ℕ) : ℕ := if N % 2 = 0 then Nat.centralBinom (N / 2) else 0

/-- `negDirCount` matches the proven single-direction count `zeroSumCount negPair` at every even
length (and both vanish at odd length — odd-length antipodal tuples never sum to `0`). At even
length it is the `_AvUC` central-binomial base; this anchors `f` for the `m`-fold ladder. -/
theorem negDirCount_even (r : ℕ) :
    negDirCount (2 * r) = zeroSumCount AvUC.negPair (2 * r) := by
  rw [AvUC.zeroSum_negPair_eq_centralBinom]
  unfold negDirCount
  simp [Nat.mul_mod_right, Nat.mul_div_cancel_left r (by norm_num : 0 < 2)]

/-- **`m = 1` ladder anchor.** The single-direction convolution `natConv negDirCount 1` reproduces
the central-binomial base at even length: `natConv negDirCount 1 (2r) = centralBinom r = Z_r({1,−1})`
`= (2r)!·cpow I0c 1 r = AvW0.Edef r 1`. So the `d = 1` rung of the symbolic factorization is exactly
the `_AvW0` model value, the base of the `I₀(2x)^m` convolution. -/
theorem natConv_negDirCount_one (r : ℕ) :
    (natConv negDirCount 1 (2 * r) : ℚ) = AvW0.Edef r 1 := by
  classical
  -- natConv f 1 N = Σ_a C(N,a)·f a·[N-a = 0] = f N  (only a = N survives)
  have hval : natConv negDirCount 1 (2 * r) = negDirCount (2 * r) := by
    rw [natConv_succ]
    rw [Finset.sum_eq_single 0]
    · simp [natConv_zero]
    · intro a ha hane
      rw [Finset.mem_range, Nat.lt_succ_iff] at ha
      simp [natConv_zero, hane]
    · intro hcontra
      exact absurd (Finset.mem_range.mpr (by omega)) hcontra
  rw [hval]
  -- negDirCount (2r) = centralBinom r, and Edef r 1 = centralBinom r
  have hf : negDirCount (2 * r) = Nat.centralBinom r := by
    rw [negDirCount_even r, AvUC.zeroSum_negPair_eq_centralBinom]
  rw [hf]
  -- AvW0.Edef r 1 = centralBinom r via the proven _AvUC bridge
  rw [← AvUC.bessel_identity_mu2 r, AvUC.zeroSum_negPair_eq_centralBinom]

#print axioms natConv_succ
#print axioms zeroSumCount_empty
#print axioms bessel_mfold_step
#print axioms zeroSumCount_iUnion_eq_natConv
#print axioms bessel_mfold_two
#print axioms negDirCount_even
#print axioms natConv_negDirCount_one

end ArkLib.ProximityGap.Frontier.AvF1
