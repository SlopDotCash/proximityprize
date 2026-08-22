/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-L4)
-/
import Mathlib

/-!
# Lane L4 (#444): the Gowers-norm inverse-theorem / nilsequence / quadratic-Fourier route

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** Lane L4 asks whether the
inverse theorem for the Gowers `U^k` norms (Green–Tao–Ziegler, *An inverse theorem for the Gowers
`U^{s+1}[N]`-norm*, Ann. of Math. 176 (2012) 1231–1372, arXiv:1009.3998; finite-field case
Tao–Ziegler / Bergelson–Tao–Ziegler, see Tao 254B Notes 5) — which detects correlation with
**degree-`(k−1)` polynomial phases / `(k−1)`-step nilsequences** beyond the linear Fourier
spectrum — gives a genuinely *non-second-order, non-linear* handle on the prize sup-norm

  `M(n) = max_{b ∈ 𝔽_p^*} |η_b|`,  `η_b = Σ_{x∈μ_n} e_p(b x)`,  `μ_n = order-n = 2^μ subgroup`,

at the prize regime `n = 2^30`, `p = n^β`, `β = 4`, `p ≡ 1 (mod n)`.

## The precise literature, and what each fact actually says (lane research, cited)

* **U² = the linear Fourier spectrum itself.** For `f : ℤ/p → ℂ`,
  `‖f‖_{U²}^4 = Σ_ξ |f̂(ξ)|⁴` (Tao 254B Notes 5; Green, *Additive Combinatorics* ch. 5). For
  `f = 1_{μ_n}`, `f̂(b) = η_b / p`, so `‖1_{μ_n}‖_{U²}^4 = (1/p³)·Σ_b |η_b|⁴ = E₂(μ_n)/p³` is
  **exactly the additive energy**. The U² *inverse theorem* returns the linear phase `e_p(bx)` —
  i.e. it hands back the `η_b` themselves. So `U²` carries **no information beyond** the `η_b` /
  the second moment. (Recorded in-tree, `DISPROOF_LOG.md`: "U² Gowers = E₂ = Johnson".) This is
  fence **F1/F7** (energy/cumulant = conjugate to the wall; entropy Rényi-2 = additive energy).

* **Higher `U^k` give WEAKER upper bounds on `M`, never sharper.** Gowers norms are monotone,
  `‖f‖_{U²} ≤ ‖f‖_{U³} ≤ ‖f‖_{U⁴} ≤ …` (Tao 254B Notes 3, Exercise 19; Green op. cit.). The
  single largest Fourier coefficient satisfies `‖f̂‖_∞ ≤ ‖f‖_{U²}` (since `‖f̂‖_∞^4 ≤ Σ|f̂|^4`),
  and `M(n) = p·‖f̂‖_∞`. So `M(n) ≤ p·‖f‖_{U²} ≤ p·‖f‖_{U^k}` for every `k ≥ 2`: each higher
  norm is a **larger** quantity, hence a **looser** ceiling on `M`. There is no mechanism by which
  a `U^k` (`k>2`) bound improves the `U²` (energy) bound on a single coefficient. This is fence
  **F0** (conservation law: 2nd-order input caps at Johnson; the `√log` excess is a tail invisible
  to fixed moments) restated for the Gowers ladder.

* **The inverse theorem is an EXISTENCE / lower-bound tool, not an upper bound.** "Large `U^{k}`
  ⟹ ∃ degree-`(k−1)` polynomial-phase correlation." It *detects* structure; it cannot *cap* `M`.
  To use it to bound `M` one needs the converse direction, which for the *linear* sup is just
  Parseval = energy = Johnson `√n`.

## The decisive structural mechanism: the quadratic obstruction FOLDS to the same wall (this file)

The one place a `U^k` route could have been non-reducing is if `1_{μ_n}` correlated with a genuine
**quadratic** phase `e_p(c·x²)` *more* than with any linear phase — a real `U³` obstruction beyond
`U²`. The exact-integer probe `scripts/probes/probe_wfH_L4_gowers{,_fold}.py` (β=4 where feasible,
4 ≤ n ≤ 64) shows this correlation `Q(n) = max_{c≠0} |Σ_{x∈μ_n} e_p(c x²)|` **does** exceed the
linear `M(n)` and the gap grows (`Q/M = 1.06, 1.36, 1.43, 1.62` at `n = 8,16,32,64`). So the
quadratic obstruction is genuinely non-trivial — the terse "it's just the wall" needs a *mechanism*.

The mechanism is the **squaring fold**, which this file formalizes abstractly and exactly:

> On a `2`-power multiplicative subgroup `μ_n`, the map `x ↦ x²` is a **2-to-1 group
> homomorphism onto the index-2 subgroup `μ_{n/2}`** (itself a `2`-power subgroup). Hence a pure
> quadratic phase sums as
>
>   `Σ_{x∈μ_n} e_p(c·x²) = 2·Σ_{y∈μ_{n/2}} e_p(c·y) = 2·η^{(μ_{n/2})}_c`,
>
> i.e. it **IS twice a *linear* Gauss period over the half-size 2-power subgroup `μ_{n/2}`** — the
> very same object `M`, one level down the dilation tower.

The probe confirms the exact identity `Q(n) = 2·M(μ_{n/2})` to machine precision (`|Q − 2M_{half}|
= 0`) for `n = 8,16,32,64`. So the `U³` "non-linear" obstruction is **the same BGK/Paley wall at
`μ_{n/2}`**; `U⁴`,`U⁵`,… iterate the fold to `μ_{n/4}`,`μ_{n/8}`,…, never leaving the family. The
inverse theorem, fed `1_{μ_n}`, returns a Gauss period over a smaller 2-power subgroup: an
**object-change synonym**, fence **F11**, layered on the energy reduction **F0/F1/F7**.

**Verdict: REDUCES-TO-FENCE (F1/F7 energy + F0 conservation + F11 fold-synonym). VACUOUS as an
upper bound (inverse theorem is lower-bound-only; monotonicity makes higher `U^k` looser).**

## Formal content of this file (all axiom-clean, no `sorry`)

`quadratic_phase_folds_to_half` — the exact algebraic fold over an arbitrary finite abelian group:
if `sq : G → H` is a group hom that is exactly `2`-to-1 onto its image `K = range sq`, then for any
phase `χ : H → ℂ`, `Σ_{x∈G} χ(sq x) = 2·Σ_{y∈K} χ y`. This is the engine: the quadratic sum over
`μ_n` is `2×` a linear sum over `μ_{n/2} = range(·²)`, so it cannot be a *new* object — it is `M`
at half size.

`gowers_higher_norm_no_improvement` — the monotone-ladder no-go in abstract form: from
`‖f̂‖_∞ ≤ U₂` and `U₂ ≤ U₃` one gets `‖f̂‖_∞ ≤ U₃`, never the reverse; the higher norm is a looser
ceiling. (A faithful encoding of "U² ≤ U³ ⟹ U³ cannot sharpen the U²/energy bound on the sup".)

Issue #444 (lane L4, Gowers-norm inverse theorem / nilsequences / quadratic Fourier).
-/

namespace ProximityGap.Frontier.GowersQuadraticFold

open Finset

/-!
### The squaring fold (the engine)

We work over an arbitrary `Fintype` `G` mapped by an arbitrary `sq : G → H` (the "squaring" map),
with the only structural hypothesis being that `sq` is **exactly 2-to-1 onto its image** — which is
the exact behaviour of `x ↦ x²` on a `2`-power multiplicative subgroup `μ_n` of `𝔽_p^*` (kernel
`{±1}`, image the index-2 subgroup `μ_{n/2}`). The conclusion is the load-bearing identity: any
phase pulled back through `sq` sums to twice its sum over the image. This is what reduces the
quadratic (`U³`) correlation to a *linear* Gauss period at half size.
-/

variable {G : Type*} [Fintype G]
variable {H : Type*} [DecidableEq H]

/--
**The squaring fold (combinatorial engine of L4).**

Let `sq : G → H` be exactly `2`-to-1 onto its image, i.e. every value `h` in the image
`K = sq '' univ` has exactly two preimages (`hfib`). Then for any complex "phase" `χ : H → ℂ`,
the pulled-back sum over `G` is **twice** the sum over the image:

  `Σ_{x : G} χ (sq x) = 2 · Σ_{y ∈ K} χ y`.

Applied to `G = μ_n`, `sq = (·²)`, `K = μ_{n/2}`, `χ = e_p(c · ·)`: the pure quadratic phase sum
`Σ_{x∈μ_n} e_p(c x²)` equals `2·η^{(μ_{n/2})}_c`, a *linear* Gauss period over the half-size
`2`-power subgroup. The "non-linear" obstruction the `U³` inverse theorem would surface is therefore
the same `M`-object one level down the tower — never a new quantity (fence **F11**, the fold
synonym). -/
theorem quadratic_phase_folds_to_half
    (sq : G → H) (K : Finset H)
    (himg : ∀ x : G, sq x ∈ K)
    (hfib : ∀ h ∈ K, (Finset.univ.filter (fun x : G => sq x = h)).card = 2)
    (χ : H → ℂ) :
    ∑ x : G, χ (sq x) = 2 * ∑ y ∈ K, χ y := by
  classical
  -- Group the sum over `G` by the value of `sq`, supported on `K`.
  have hpart : ∑ x : G, χ (sq x)
      = ∑ y ∈ K, ∑ x ∈ Finset.univ.filter (fun x : G => sq x = y), χ (sq x) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := sq) (t := K) (fun x _ => himg x)]
  rw [hpart]
  -- On each fiber over `y ∈ K`, `χ (sq x) = χ y` and there are exactly two terms.
  have hfib_sum : ∀ y ∈ K,
      (∑ x ∈ Finset.univ.filter (fun x : G => sq x = y), χ (sq x)) = 2 * χ y := by
    intro y hy
    have hconst : ∀ x ∈ Finset.univ.filter (fun x : G => sq x = y), χ (sq x) = χ y := by
      intro x hx
      have : sq x = y := (Finset.mem_filter.mp hx).2
      rw [this]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hfib y hy]
    simp [two_mul]
  rw [Finset.sum_congr rfl hfib_sum, Finset.mul_sum]

/--
**Magnitude corollary: the quadratic correlation is `2×` a linear sup at half size.**

Taking absolute values in `quadratic_phase_folds_to_half`, the worst-case quadratic-phase sum is
bounded by `2` times the worst-case *linear* sum over the image subgroup. This is the exact-probe
content `Q(n) = 2·M(μ_{n/2})` in inequality form: the `U³` obstruction never exceeds twice the
linear sup-norm one level down — so it is the **same wall**, smaller `n`, not a new handle. -/
theorem quadratic_correlation_le_two_mul_half_sup
    (sq : G → H) (K : Finset H)
    (himg : ∀ x : G, sq x ∈ K)
    (hfib : ∀ h ∈ K, (Finset.univ.filter (fun x : G => sq x = h)).card = 2)
    (χ : H → ℂ) (Mhalf : ℝ)
    (hMhalf : ‖∑ y ∈ K, χ y‖ ≤ Mhalf) :
    ‖∑ x : G, χ (sq x)‖ ≤ 2 * Mhalf := by
  rw [quadratic_phase_folds_to_half sq K himg hfib χ]
  calc ‖(2 : ℂ) * ∑ y ∈ K, χ y‖
      = 2 * ‖∑ y ∈ K, χ y‖ := by
        rw [norm_mul]; norm_num
    _ ≤ 2 * Mhalf := by
        apply mul_le_mul_of_nonneg_left hMhalf (by norm_num)

/-!
### The monotone-ladder no-go (higher `U^k` is a looser ceiling)

The Gowers norms satisfy `U² ≤ U³ ≤ U⁴ ≤ …` and the largest Fourier coefficient is `≤ U²`. We
isolate the purely order-theoretic consequence: a `U³` (or higher) bound can only *follow from* the
`U²` bound, never *improve* it on a single coefficient. Higher-order Fourier analysis adds an upper
*ceiling that is never below the energy ceiling*; on the sup-norm it is therefore strictly weaker.
-/

/--
**Higher Gowers norms cannot sharpen the energy/`U²` bound on a single Fourier coefficient.**

Given the (literature) facts `Sup ≤ U₂` (largest coefficient `≤` U² norm) and `U₂ ≤ U₃` (Gowers
monotonicity), one concludes `Sup ≤ U₃` — the `U³` ceiling is *implied by*, hence no tighter than,
the `U²` (= additive-energy) ceiling. The reverse (`U₃ < U₂`) is impossible by monotonicity, so no
higher-order norm yields a sub-energy bound on `M = p·Sup`. This is the abstract skeleton of "the
inverse-theorem ladder reduces to F0/F1: every accessible upper bound bottoms out at the energy =
Johnson scale." -/
theorem gowers_higher_norm_no_improvement
    (Sup U₂ U₃ : ℝ) (hSup : Sup ≤ U₂) (hmono : U₂ ≤ U₃) :
    Sup ≤ U₃ ∧ ¬ (U₃ < U₂) := by
  exact ⟨le_trans hSup hmono, not_lt.mpr hmono⟩

#print axioms quadratic_phase_folds_to_half
#print axioms quadratic_correlation_le_two_mul_half_sup
#print axioms gowers_higher_norm_no_improvement

end ProximityGap.Frontier.GowersQuadraticFold
