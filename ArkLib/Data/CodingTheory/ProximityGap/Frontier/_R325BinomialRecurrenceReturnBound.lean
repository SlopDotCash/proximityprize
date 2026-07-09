/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R314KernelRelationMassDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R315KernelRelationResultantWeld

/-!
# ROUND 325 (#466, Fable session 2026-07-09): THE BINOMIAL RETURN-PROBABILITY BOUND —
  short vectors in a banded recurrence lattice, unconditionally

R321/R322 left ONE named hard step for the `PrimitiveSaturationDichotomy`: a uniform
return-probability (short-vector count) bound for the principal recurrence lattice
`L_f = f·ℤ[x]/(x^m+1)`, using the short/banded structure of `f` (the census shows the top
recurrence orbit is short — the `c=3` violator is `3 + x^5` — and carries 71.7–100% of
collision mass in all 92 in-window `n=32` cells).

This brick proves the bound for the **binomial class** `f = a + b·x^s`, `|b| < |a|` —
with a two-line max-coordinate argument that completely bypasses the cyclic-orbit
unrolling and any Fourier duality (hence does NOT collapse to the Paley spectrum):

If every coordinate of the (nega)cyclic product `g·f` is `≤ H` in absolute value, let
`M = max_i |g_i|`, attained at `i₀`.  The product coordinate at `i₀` is
`a·g_{i₀} ± b·g_{i₀-s}`, so `|a|·M ≤ H + |b|·M`, i.e. `M·(|a|-|b|) ≤ H`.

* **`banded_max_bound`** — the abstract inequality, for ANY single-off-diagonal banded
  map (arbitrary index permutation `σ`, arbitrary signs/values `|c i| ≤ b`):
  `∀ i, |g i| ≤ H` at scale `(|a| - b)`.
* **`banded_preimage_card_le`** — the resulting short-vector count: the number of `g`
  whose banded image lies in the height-`H` box is at most `(2·(H/(|a|-b)) + 1)^m`
  (integer division; matches the trivial-count baseline `(2H+1)^m / |Res|^{...}` up to
  the `K^m`-type loss the dichotomy allows, since `|Res(x^m+1, a+bx^s)| ≥ (|a|-|b|)^m`).

The wraparound sign of the negacyclic ring is absorbed into `c` (only `|c i| ≤ b` is
used), so this applies verbatim to `ℤ[x]/(x^m+1)` multiplication by `a + b·x^s` for any
shift `s` and any sign pattern.  Consumed by the R321 dichotomy at the binomial rung; the
general short-support case (support `> 2`) remains open (named in R321).

Issue #466, round r325.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R325BinomialRecurrenceReturnBound

/-- **The max-coordinate bound.**  If every coordinate of the banded image
`i ↦ a·g i + c i·g (σ i)` is bounded by `H`, and `|c i| ≤ b < |a|` for all `i`, then
every coordinate of `g` is bounded by `H` at scale `|a| - b`. -/
theorem banded_max_bound {m : ℕ} (hm : 0 < m)
    (a : ℤ) (b H : ℤ) (c : Fin m → ℤ) (σ : Fin m → Fin m)
    (hc : ∀ i, |c i| ≤ b) (hab : b < |a|)
    (g : Fin m → ℤ)
    (hbound : ∀ i, |a * g i + c i * g (σ i)| ≤ H) :
    ∀ i, |g i| * (|a| - b) ≤ H := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- the maximal coordinate
  obtain ⟨i₀, -, hi₀max⟩ := Finset.exists_max_image Finset.univ (fun i => |g i|)
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  set M : ℤ := |g i₀| with hM
  have hMmax : ∀ i, |g i| ≤ M := fun i => hi₀max i (Finset.mem_univ i)
  have hM0 : 0 ≤ M := abs_nonneg _
  -- |a|·M ≤ H + b·M at the maximal coordinate
  have hkey : |a| * M ≤ H + b * M := by
    have h1 : |a * g i₀| ≤ |a * g i₀ + c i₀ * g (σ i₀)| + |c i₀ * g (σ i₀)| := by
      calc |a * g i₀| = |(a * g i₀ + c i₀ * g (σ i₀)) + (-(c i₀ * g (σ i₀)))| := by
            ring_nf
        _ ≤ |a * g i₀ + c i₀ * g (σ i₀)| + |(-(c i₀ * g (σ i₀)))| := abs_add_le _ _
        _ = |a * g i₀ + c i₀ * g (σ i₀)| + |c i₀ * g (σ i₀)| := by rw [abs_neg]
    have h2 : |c i₀ * g (σ i₀)| ≤ b * M := by
      rw [abs_mul]
      have hcb := hc i₀
      have hgM := hMmax (σ i₀)
      have hb0 : (0 : ℤ) ≤ b := le_trans (abs_nonneg _) hcb
      exact mul_le_mul hcb hgM (abs_nonneg _) hb0
    calc |a| * M = |a * g i₀| := by rw [abs_mul, hM]
      _ ≤ |a * g i₀ + c i₀ * g (σ i₀)| + |c i₀ * g (σ i₀)| := h1
      _ ≤ H + b * M := add_le_add (hbound i₀) h2
  -- rearrange
  intro i
  have hiM : |g i| * (|a| - b) ≤ M * (|a| - b) := by
    have h := hMmax i
    have hpos : (0 : ℤ) ≤ |a| - b := by omega
    exact mul_le_mul_of_nonneg_right h hpos
  refine le_trans hiM ?_
  nlinarith [hkey]

/-- **Short-vector count for the banded image.**  The set of `g : Fin m → ℤ` whose
banded image lies in the height-`H` box (`H ≥ 0`) injects into the product of intervals
`[-K, K]^m` with `K = H / (|a| - b)` (integer division), so it has at most
`(2·(H/(|a|-b)) + 1)^m` elements. -/
theorem banded_preimage_card_le {m : ℕ} (hm : 0 < m)
    (a : ℤ) (b H : ℤ) (hH : 0 ≤ H) (c : Fin m → ℤ) (σ : Fin m → Fin m)
    (hc : ∀ i, |c i| ≤ b) (hab : b < |a|)
    (S : Finset (Fin m → ℤ))
    (hS : ∀ g ∈ S, ∀ i, |a * g i + c i * g (σ i)| ≤ H) :
    S.card ≤ (2 * (H / (|a| - b)).toNat + 1) ^ m := by
  classical
  set K : ℤ := H / (|a| - b) with hK
  have hd : (0 : ℤ) < |a| - b := by omega
  -- every g ∈ S has all coordinates in [-K, K]
  have hmem : ∀ g ∈ S, ∀ i, g i ∈ Finset.Icc (-K) K := by
    intro g hg i
    have hb := banded_max_bound hm a b H c σ hc hab g (hS g hg) i
    have habs : |g i| ≤ K := by
      rw [hK]
      rw [Int.le_ediv_iff_mul_le hd]
      exact hb
    rw [Finset.mem_Icc]
    constructor
    · linarith [neg_abs_le (g i)]
    · linarith [le_abs_self (g i)]
  -- inject into the pi-type over intervals
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin m => Finset.Icc (-K) K) := by
    intro g hg
    rw [Fintype.mem_piFinset]
    exact hmem g hg
  calc S.card ≤ (Fintype.piFinset (fun _ : Fin m => Finset.Icc (-K) K)).card :=
        Finset.card_le_card hsub
    _ = ∏ _i : Fin m, (Finset.Icc (-K) K).card := Fintype.card_piFinset _
    _ = (2 * K.toNat + 1) ^ m := by
        have hK0 : 0 ≤ K := Int.ediv_nonneg hH hd.le
        have hcard : (Finset.Icc (-K) K).card = 2 * K.toNat + 1 := by
          rw [Int.card_Icc]
          omega
        rw [Finset.prod_const, hcard, Finset.card_univ, Fintype.card_fin]

/-- **Diagonally-dominant generalization.**  The same max-coordinate argument for ANY
residual dominated in `ℓ¹` by the sup-norm of `g`: if `|v i| ≤ H` for all `i` and the
residual `v i - a·g i` is bounded by `b·M` whenever `M` bounds all coordinates of `g`,
then every coordinate of `g` is bounded by `H` at scale `|a| - b`.  Instantiating the
residual with `Σ_j c_j·g_{i-s_j}`, `Σ_j |c_j| ≤ b`, covers every short recurrence `f`
whose dominant coefficient exceeds the `ℓ¹` mass of the rest — so the only case of the
R321 return-probability step not covered by this file is non-diagonally-dominant `f`. -/
theorem dominant_max_bound {m : ℕ} (hm : 0 < m)
    (a : ℤ) (b H : ℤ) (hb : 0 ≤ b) (hab : b < |a|)
    (g v : Fin m → ℤ)
    (hv : ∀ i, |v i| ≤ H)
    (hband : ∀ i, ∀ M : ℤ, (∀ j, |g j| ≤ M) → |v i - a * g i| ≤ b * M) :
    ∀ i, |g i| * (|a| - b) ≤ H := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨i₀, -, hi₀max⟩ := Finset.exists_max_image Finset.univ (fun i => |g i|)
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  set M : ℤ := |g i₀| with hM
  have hMmax : ∀ i, |g i| ≤ M := fun i => hi₀max i (Finset.mem_univ i)
  have hkey : |a| * M ≤ H + b * M := by
    have h1 : |a * g i₀| ≤ |v i₀| + |v i₀ - a * g i₀| := by
      calc |a * g i₀| = |v i₀ + (-(v i₀ - a * g i₀))| := by ring_nf
        _ ≤ |v i₀| + |(-(v i₀ - a * g i₀))| := abs_add_le _ _
        _ = |v i₀| + |v i₀ - a * g i₀| := by rw [abs_neg]
    calc |a| * M = |a * g i₀| := by rw [abs_mul, hM]
      _ ≤ |v i₀| + |v i₀ - a * g i₀| := h1
      _ ≤ H + b * M := add_le_add (hv i₀) (hband i₀ M hMmax)
  intro i
  have hiM : |g i| * (|a| - b) ≤ M * (|a| - b) :=
    mul_le_mul_of_nonneg_right (hMmax i) (by omega)
  refine le_trans hiM ?_
  nlinarith [hkey]

/-! ## Concrete negacyclic wiring (the R321 census shape, e.g. `3 + x^5` at `m=16`) -/

/-- Coefficient `i` of the negacyclic product `g·(a + b·x^s) mod (x^m+1)`:
`a·g_i + ε_i·b·g_{(i-s) mod m}` with `ε_i = -1` exactly when the `x^s`-shift wraps
(`i < s`), since `x^m = -1`. -/
def negacyclicBinomialMul {m : ℕ} (a b : ℤ) (s : Fin m) (g : Fin m → ℤ) :
    Fin m → ℤ :=
  fun i => a * g i + (if (i : ℕ) < (s : ℕ) then -b else b) * g (i - s)

/-- **Concrete max-coordinate bound** for negacyclic binomial multiplication. -/
theorem negacyclicBinomialMul_max_bound {m : ℕ} (hm : 0 < m)
    (a b : ℤ) (s : Fin m) (H : ℤ) (hab : |b| < |a|)
    (g : Fin m → ℤ)
    (hbound : ∀ i, |negacyclicBinomialMul a b s g i| ≤ H) :
    ∀ i, |g i| * (|a| - |b|) ≤ H := by
  refine banded_max_bound hm a |b| H
    (fun i => if (i : ℕ) < (s : ℕ) then -b else b) (fun i => i - s) ?_ hab g ?_
  · intro i
    by_cases h : (i : ℕ) < (s : ℕ) <;> simp [h]
  · intro i
    exact hbound i

/-- **Concrete short-vector count** for negacyclic binomial multiplication. -/
theorem negacyclicBinomialMul_preimage_card_le {m : ℕ} (hm : 0 < m)
    (a b : ℤ) (s : Fin m) (H : ℤ) (hH : 0 ≤ H) (hab : |b| < |a|)
    (S : Finset (Fin m → ℤ))
    (hS : ∀ g ∈ S, ∀ i, |negacyclicBinomialMul a b s g i| ≤ H) :
    S.card ≤ (2 * (H / (|a| - |b|)).toNat + 1) ^ m := by
  refine banded_preimage_card_le hm a |b| H hH
    (fun i => if (i : ℕ) < (s : ℕ) then -b else b) (fun i => i - s) ?_ hab S ?_
  · intro i
    by_cases h : (i : ℕ) < (s : ℕ) <;> simp [h]
  · intro g hg i
    exact hS g hg i

/-! ## R327 weld: the fixed-prime short-relation cap, conditional only on saturation

R315 named the "genuinely hard fixed-prime counting statement": bound the number of
bounded-height kernel relations at ONE specified prime.  Given the R321 dyadic
saturation (`2^t·K ⊆ L_f`, census-verified with `t ≤ 3` in all 92 in-window `n=32`
cells) for a binomial `f`, the cap follows with NO further arithmetic input.  Injectivity
of the correspondence is free: `banded_max_bound` at `H = 0` forces the kernel of the
negacyclic multiplication to vanish. -/

/-- Multiplication by a dominant binomial is injective (max-bound at `H = 0`). -/
theorem negacyclicBinomialMul_injective {m : ℕ} (hm : 0 < m)
    (a b : ℤ) (s : Fin m) (hab : |b| < |a|) :
    Function.Injective (negacyclicBinomialMul a b s (m := m)) := by
  intro g₁ g₂ hg
  have hdiff : ∀ i, negacyclicBinomialMul a b s (g₁ - g₂) i = 0 := by
    intro i
    have h1 := congrFun hg i
    simp only [negacyclicBinomialMul, Pi.sub_apply]
    ring_nf
    simp only [negacyclicBinomialMul] at h1
    linarith [h1]
  have hz := negacyclicBinomialMul_max_bound hm a b s 0 hab (g₁ - g₂)
    (fun i => by rw [hdiff i]; simp)
  funext i
  have := hz i
  have habs : |(g₁ - g₂) i| = 0 := by
    nlinarith [abs_nonneg ((g₁ - g₂) i), this]
  have : (g₁ - g₂) i = 0 := abs_eq_zero.mp habs
  simpa [sub_eq_zero] using this

/-- **The fixed-prime short-relation cap (conditional only on dyadic saturation).**
If every relation `d` in a set `K` of height-`≤ H` vectors has `2^t·d` in the recurrence
lattice of a dominant binomial (`∃ g, g·(a+b·x^s) = 2^t·d` negacyclically), then
`#K ≤ (2·(2^t·H/(|a|-|b|)).toNat + 1)^m`. -/
theorem saturated_kernel_card_le {m : ℕ} (hm : 0 < m)
    (a b : ℤ) (s : Fin m) (H : ℤ) (hH : 0 ≤ H) (t : ℕ) (hab : |b| < |a|)
    (K : Finset (Fin m → ℤ))
    (hbox : ∀ d ∈ K, ∀ i, |d i| ≤ H)
    (hsat : ∀ d ∈ K, ∃ g : Fin m → ℤ,
      negacyclicBinomialMul a b s g = fun i => 2 ^ t * d i) :
    K.card ≤ (2 * ((2 ^ t * H) / (|a| - |b|)).toNat + 1) ^ m := by
  classical
  -- the (unique) preimage of 2^t·d
  choose gd hgd using hsat
  -- the image finset of the preimages
  set G : Finset (Fin m → ℤ) := K.attach.image (fun d => gd d.1 d.2) with hG
  have hginj : ∀ (d₁ : {x // x ∈ K}) (d₂ : {x // x ∈ K}),
      gd d₁.1 d₁.2 = gd d₂.1 d₂.2 → d₁ = d₂ := by
    intro d₁ d₂ heq
    have h1 := hgd d₁.1 d₁.2
    have h2 := hgd d₂.1 d₂.2
    rw [heq, h2] at h1
    have hcoord : ∀ i, (2 : ℤ) ^ t * d₁.1 i = 2 ^ t * d₂.1 i := fun i => (congrFun h1 i).symm
    have : d₁.1 = d₂.1 := by
      funext i
      have := hcoord i
      have h2t : (2 : ℤ) ^ t ≠ 0 := by positivity
      exact mul_left_cancel₀ h2t this
    exact Subtype.ext this
  have hcard : K.card = G.card := by
    rw [hG, Finset.card_image_of_injective _ (fun d₁ d₂ => hginj d₁ d₂),
      Finset.card_attach]
  rw [hcard]
  refine negacyclicBinomialMul_preimage_card_le hm a b s (2 ^ t * H)
    (by positivity) hab G ?_
  intro g hg i
  rw [hG] at hg
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hg
  rw [hgd d.1 d.2]
  rw [abs_mul, abs_pow]
  calc |(2 : ℤ)| ^ t * |d.1 i| ≤ |(2 : ℤ)| ^ t * H := by
        have := hbox d.1 d.2 i
        gcongr
    _ = 2 ^ t * H := by norm_num

/-! ## R328 weld: collision mass under binomial saturation

Wiring `saturated_kernel_card_le` into R314's exact decomposition
`shadowCollisionMass = Σ relationMass` via `shadowCollisionMass_le_relation_count_mul`:
under the R321 saturation hypothesis at `(g, p)`, the entire char-zero collision surplus
is capped by (short-vector count) × (per-relation mass bound), with the count now an
explicit closed form. -/

open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity

/-- **Collision-mass cap under binomial saturation.**  If every realized shadow-kernel
relation at `(g, n, m, r)` is dyadically saturated by the recurrence lattice of a dominant
binomial (`2^t·d ∈ L_{a+b·x^s}`), and each relation carries mass at most `M`, then the
whole collision surplus is at most `(2·(2^{t+1}·r/(|a|-|b|)).toNat + 1)^m · M`. -/
theorem shadowCollisionMass_le_of_binomial_saturation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (hm : 0 < m)
    (a b : ℤ) (s : Fin m) (t : ℕ) (hab : |b| < |a|) (M : ℕ)
    (hsat : ∀ d ∈ shadowKernelRelations g n m r, ∃ gv : Fin m → ℤ,
      negacyclicBinomialMul a b s gv = fun i => 2 ^ t * d i)
    (hmass : ∀ d ∈ shadowKernelRelations g n m r,
      shadowRelationMass g n m r d ≤ M) :
    shadowCollisionMass g n m r
      ≤ (2 * ((2 ^ t * (2 * r : ℤ)) / (|a| - |b|)).toNat + 1) ^ m * M := by
  classical
  refine shadowCollisionMass_le_relation_count_mul g n m r
    ((2 * ((2 ^ t * (2 * r : ℤ)) / (|a| - |b|)).toNat + 1) ^ m) M ?_ hmass
  refine saturated_kernel_card_le hm a b s (2 * r : ℤ) (by positivity) t hab
    (shadowKernelRelations g n m r) ?_ hsat
  intro d hd i
  have h := shadowKernelRelation_abs_le_two_mul_r g n m r hd i
  exact_mod_cast h

/-! ## R331 dictionary: negacyclic vector product = ring multiplication in `ℤ[x]/(x^m+1)`

The missing translation between the vector-level `negacyclicBinomialMul` and actual ring
multiplication by `a + b·x^s` in `AdjoinRoot (x^m+1)`, at the level of `mk ∘ relationPoly`.
With this, "`2^t·d` lies in the recurrence lattice `L_{a+b·x^s}`" (the R321/R329 saturation
conclusion) converts into the exact `hsat` hypothesis consumed by
`saturated_kernel_card_le` / `shadowCollisionMass_le_of_binomial_saturation`. -/

section Dictionary

open Polynomial AdjoinRoot
open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant
open ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld

/-- `mk (relationPoly v) = Σ v_i · ρ^i` where `ρ = root (x^m+1)`. -/
theorem mk_relationPoly_eq_sum {m : ℕ} (v : Fin m → ℤ) :
    AdjoinRoot.mk (fpoly m) (relationPoly v)
      = ∑ i : Fin m, (v i : AdjoinRoot (fpoly m))
          * (AdjoinRoot.root (fpoly m)) ^ (i : ℕ) := by
  rw [← AdjoinRoot.aeval_eq, relationPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, aeval_C, map_pow, aeval_X]
  simp [algebraMap_int_eq]

/-- The root of `x^m+1` is a half-root: `ρ^m = -1`. -/
theorem root_fpoly_pow {m : ℕ} :
    (AdjoinRoot.root (fpoly m)) ^ m = -1 := by
  have h := AdjoinRoot.mk_self (f := fpoly m)
  rw [fpoly, map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **The dictionary.**  Negacyclic binomial vector multiplication is ring multiplication
by `a + b·x^s` in `ℤ[x]/(x^m+1)`:
`mk (P_{v·(a+bx^s)}) = mk (P_v) · (a + b·ρ^s)`. -/
theorem mk_relationPoly_negacyclicBinomialMul {m : ℕ} (hm : 0 < m)
    (a b : ℤ) (s : Fin m) (v : Fin m → ℤ) :
    AdjoinRoot.mk (fpoly m) (relationPoly (negacyclicBinomialMul a b s v))
      = AdjoinRoot.mk (fpoly m) (relationPoly v)
        * ((a : AdjoinRoot (fpoly m))
            + (b : AdjoinRoot (fpoly m)) * (AdjoinRoot.root (fpoly m)) ^ (s : ℕ)) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  set ρ : AdjoinRoot (fpoly m) := AdjoinRoot.root (fpoly m) with hρdef
  have hρ : ρ ^ m = -1 := root_fpoly_pow
  rw [mk_relationPoly_eq_sum, mk_relationPoly_eq_sum, Finset.sum_mul]
  have hterm : ∀ i : Fin m,
      (v i : AdjoinRoot (fpoly m)) * ρ ^ (i : ℕ)
          * ((a : AdjoinRoot (fpoly m)) + (b : AdjoinRoot (fpoly m)) * ρ ^ (s : ℕ))
        = ((a * v i : ℤ) : AdjoinRoot (fpoly m)) * ρ ^ (i : ℕ)
          + ((b * v i : ℤ) : AdjoinRoot (fpoly m)) * ρ ^ ((i : ℕ) + (s : ℕ)) := by
    intro i
    rw [pow_add]
    simp only [Int.cast_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  have hshift : (∑ i : Fin m, ((b * v i : ℤ) : AdjoinRoot (fpoly m)) * ρ ^ ((i : ℕ) + (s : ℕ)))
      = ∑ j : Fin m,
          (((if (j : ℕ) < (s : ℕ) then -b else b) * v (j - s) : ℤ) : AdjoinRoot (fpoly m))
            * ρ ^ (j : ℕ) := by
    rw [← Equiv.sum_comp (Equiv.addRight s)
      (fun j => (((if (j : ℕ) < (s : ℕ) then -b else b) * v (j - s) : ℤ) : AdjoinRoot (fpoly m))
        * ρ ^ (j : ℕ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.coe_addRight]
    have hesub : i + s - s = i := by
      simp
    rw [hesub]
    have hs : (s : ℕ) < m := s.isLt
    have hi : (i : ℕ) < m := i.isLt
    have h1 : ((i + s : Fin m) : ℕ) = ((i : ℕ) + (s : ℕ)) % m := Fin.val_add i s
    by_cases hwrap : (i : ℕ) + (s : ℕ) < m
    · have hval : ((i + s : Fin m) : ℕ) = (i : ℕ) + (s : ℕ) := by
        rw [Nat.mod_eq_of_lt hwrap] at h1
        exact h1
      simp only [hval]
      rw [if_neg (by omega)]
    · push_neg at hwrap
      have hval : ((i + s : Fin m) : ℕ) = (i : ℕ) + (s : ℕ) - m := by
        rw [Nat.mod_eq_sub_mod hwrap, Nat.mod_eq_of_lt (by omega)] at h1
        exact h1
      simp only [hval]
      rw [if_pos (by omega)]
      have hpow : ρ ^ ((i : ℕ) + (s : ℕ)) = -ρ ^ ((i : ℕ) + (s : ℕ) - m) := by
        have hsum : (i : ℕ) + (s : ℕ) = ((i : ℕ) + (s : ℕ) - m) + m := by omega
        calc ρ ^ ((i : ℕ) + (s : ℕ))
            = ρ ^ (((i : ℕ) + (s : ℕ) - m) + m) := by rw [← hsum]
          _ = ρ ^ ((i : ℕ) + (s : ℕ) - m) * ρ ^ m := pow_add ρ _ m
          _ = -ρ ^ ((i : ℕ) + (s : ℕ) - m) := by rw [hρ]; ring
      rw [hpow]
      push_cast
      ring
  rw [hshift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [negacyclicBinomialMul]
  push_cast
  ring

end Dictionary

#print axioms banded_max_bound
#print axioms banded_preimage_card_le
#print axioms dominant_max_bound
#print axioms negacyclicBinomialMul_max_bound
#print axioms negacyclicBinomialMul_preimage_card_le
#print axioms negacyclicBinomialMul_injective
#print axioms saturated_kernel_card_le
#print axioms shadowCollisionMass_le_of_binomial_saturation
#print axioms mk_relationPoly_eq_sum
#print axioms root_fpoly_pow
#print axioms mk_relationPoly_negacyclicBinomialMul

end ArkLib.ProximityGap.Frontier.R325BinomialRecurrenceReturnBound
