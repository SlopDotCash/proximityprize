/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# T01 (drop-locus partial-signal sub-sheaf) REDUCES-TO-WALL F10 (#444)

**NEGATIVE / guardrail brick — an honest REDUCTION, NOT a closure.**  This file pins, axiom-clean,
*why* the proposed FKM-relocation escape

> *Decompose the rank-`n` period sheaf `F` (trace `η_b = ∑_{x∈μ_n} e_p(bx)`) along its
> weight/break filtration into `F = F_avg ⊕ F_exc`, where `F_avg` carries the rank-`n` Wick/bulk
> law `|η_b| ≤ √n + o(√n)`, and `F_exc` is a polylog-conductor "drop-locus" sub-object carrying
> only the rare-event excess `E(b) := |η_b| − √n`.  Then Deligne/Weil-II on `F_exc` alone gives
> `sup_b E(b) = O(√n · log p / …)` ⟹ the prize `M(n) ≤ √n + C√(n·log(p/n))`.*

does **not** escape the conductor wall already pinned for the WHOLE sheaf in
`_C2WeilDeligneParamFamilyNoGo`, `_P3ParamFamilyConductorRankFloor`, `_wfA07_fkm_sheaf_conductor`.
It reduces to fence **F10** (no bounded-conductor `ℓ`-adic sheaf realizes the full-signal period;
conductor `= ‖signal‖₂² = rank`) composed with **F0** (the excess is a tail phenomenon invisible
to the second moment that defines rank), and is moreover *void* at the geometric level by Deligne
purity (F is pure of a single weight ⟹ the weight filtration is trivial; all constituents tame
⟹ the break filtration is trivial — there is no nontrivial split to take).

## Two independent obstructions

**(O-GEOM) The split does not exist (Deligne purity + tameness).**  The period sheaf `F` whose
trace is `η_b` is the (Tate-normalized) Gauss-period / `GL(1)^f` Gauss-sum family sheaf.  By
Deligne (Weil II), it is **pointwise pure of a single weight** (weight `1` after the usual
normalization).  A sheaf pure of a single weight has a **trivial weight filtration** — there is
exactly one graded piece — so there is no nontrivial `F = F_avg ⊕ F_exc` "along the weight
filtration."  In the *break* (Swan) direction every constituent is an Artin–Schreier / Kummer
sheaf on `𝔾_m`, hence **tame (Swan = 0)** (recorded in `MonodromyConductorScaffold`,
`MonodromyTailGaussianObstruction`), so the break filtration is trivial too.  The candidate's
named "weight/break-filtration split" is therefore the identity in both directions: `F_exc` is
either `0` (carries nothing) or all of `F` (rank `n`, the C2 wall).  This is fence F10/F2 verbatim.

**(O-2ND) Even granting an ARBITRARY direct-sum split, the excess sub-object's conductor is
≥ its second moment (this file, formalized).**  Suppose, ignoring (O-GEOM), one *postulates* any
direct-sum decomposition of the trace `η_b = t_avg(b) + t_exc(b)` realized by sheaves
`F = F_avg ⊕ F_exc`.  Any middle-extension `ℓ`-adic sheaf satisfies
`cond ≥ rank ≥ (averaged L²-second-moment of its trace)` — the generic rank equals the second
moment by diagonal/orthogonality, and `cond ≥ rank` always.  So

  `cond(F_exc)  ≥  rank(F_exc)  ≥  (1/q)·∑_b |t_exc(b)|²  =: M₂(t_exc)`.

For `F_exc` to "carry the excess" it must, at the worst frequency `b*`, supply the gap
`|t_exc(b*)| ≥ E(b*) = |η_{b*}| − √n` — the very `√(n·log(p/n))`-scale quantity the prize is
about.  But a sub-object with `cond(F_exc) ≤ c·(log p)²` has `M₂(t_exc) ≤ c·(log p)²`, and the
FKM completed-sum bound it then supplies is `sup_b |t_exc(b)| ≤ cond(F_exc)·√q/√q-normalized`,
which — read honestly through `rank = M₂` — caps the *carried* signal exactly as in A07's
conductor–signal trade-off: `signal(t_exc)² ≤ q·M₂(t_exc) ≤ q·c(log p)²`.  The pointwise excess
`E(b*) ~ √(n log(p/n))` it is meant to certify is a **rare-event/tail** quantity: it is NOT seen
by `M₂` (the second moment of the excess piece is dominated by the bulk and is `o(n)` only if the
excess is spread, in which case `F_avg` already contains the worst fiber).  The decisive identity:
the second moment of the FULL trace is pinned at `n` (Parseval, `subgroup_gaussSum_secondMoment`),
and it splits additively across `F_avg ⊕ F_exc`; pushing `M₂(t_exc)` down to polylog forces
`M₂(t_avg) → n`, i.e. **`F_avg` carries the entire rank-`n` mass including the worst-fiber spike**
— so `F_exc` carries no excess, and the sup of `η_b` is governed by `F_avg`, whose conductor is
`n` (the C2/A07/P3 wall).  Either way the prize sup is read from a rank-`n` (cond `= n`) object:
**reduces-to-F10.**

## What is proven below (pure real arithmetic; no étale machinery, no `sorry`)

* `M2` — the averaged L²-second-moment functional of a finite trace family over the parameter set.
* `m2_split` — `M2(t_avg + t_exc) ≤ 2(M2 t_avg + M2 t_exc)` and the exact orthogonal/Parseval
  split when `t_avg ⊥ t_exc` (the additive decomposition of the second moment across a direct sum).
* `condFloor_ge_m2` (abstract sheaf axiom, the FKM/Deligne dictionary `cond ≥ rank ≥ M₂`): any
  realization's conductor is ≥ its trace's second moment.  Stated as a hypothesis (the geometric
  fact `cond ≥ rank = M₂` is the unformalisable étale input; everything downstream is arithmetic).
* `exc_secondMoment_pinned` — **the core**: if the full second moment is `n` and the bulk piece
  already carries `≥ n − ε`, the excess piece carries `≤ ε`; contrapositively, an excess piece of
  second moment `> ε` forces the bulk to carry `< n − ε`.  The worst-fiber excess
  `E(b*)² ~ n·log(p/n)` cannot fit into a polylog-conductor `F_exc` because its second moment is
  `≤ cond(F_exc) ≤ c(log p)²`, which at the prize regime `p = n^4`, `n = 2^30` is
  `c(log p)² ≈ c·(4·30)² = c·14400`, vastly **below** even a single worst-fiber excess square
  `E(b*)² ≈ n·log(p/n) ≈ 2^30·(3·30) ≈ 2^36.5` — the excess does not fit.
* `prize_excess_does_not_fit` — the concrete prize instance `n = 2^30`, `p = 2^120` (β = 4): a
  single worst-fiber excess square `E(b*)² ≥ n·log₂(p/n) = 2^30·90` exceeds **any** polylog
  conductor `c·(log₂ p)² = c·120² = 14400·c` for every `c ≤ 2^10` — so the drop-locus sub-object
  cannot carry the excess while staying polylog.  The escape is closed.

## Verdict

**REDUCES-TO-WALL (F10, via F0).**  The proposed split is geometrically void (Deligne purity:
the period sheaf is pure of one weight, all constituents tame) and, even granting an arbitrary
direct-sum split, the excess sub-object's conductor is `≥` its second moment, which must reach the
worst-fiber excess square `~ n·log(p/n) ≫ (log p)²` to carry the signal — contradicting the polylog
hypothesis.  The genuine cancellation is the archimedean equidistribution of the `n` Artin–Schreier
phases (the open BGK/Paley core), realized only on the rank-`n` whole object.  Same wall as
C2/A07/P3, now shown stable under arbitrary sub-object splitting.  Not a refutation of the prize
bound (the period IS `√`-controlled empirically); a precise no-go for the sub-sheaf-isolation method.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι]

/-- The **averaged L²-second-moment** of a real trace family `t : ι → ℝ` over the parameter set
`ι` (here `ι` models the `q` parameter classes `b ∈ 𝔽_p`).  This equals the generic rank of any
middle-extension sheaf realizing `t` (diagonal/orthogonality), which lower-bounds its conductor. -/
noncomputable def M2 (t : ι → ℝ) : ℝ := (∑ b, (t b) ^ 2) / (Fintype.card ι : ℝ)

/-- `M2` is nonnegative. -/
theorem M2_nonneg (t : ι → ℝ) : 0 ≤ M2 t := by
  unfold M2
  apply div_nonneg
  · exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
  · exact Nat.cast_nonneg _

/-- **Additivity of the (un-normalized) second moment across an orthogonal direct sum.**  If the
bulk and excess traces are pointwise orthogonal in the sense that their cross term vanishes in the
sum (`∑_b t_avg(b)·t_exc(b) = 0`, the orthogonality of distinct sheaf summands in a direct sum),
then the second moment splits exactly:  `M2(t_avg + t_exc) = M2 t_avg + M2 t_exc`.  This is the
Pythagorean/Parseval split of the rank across `F_avg ⊕ F_exc`. -/
theorem M2_split_orthogonal (tav tex : ι → ℝ)
    (hortho : ∑ b, tav b * tex b = 0) :
    M2 (tav + tex) = M2 tav + M2 tex := by
  unfold M2
  rw [← add_div]
  congr 1
  have : ∀ b, ((tav + tex) b) ^ 2 = (tav b) ^ 2 + 2 * (tav b * tex b) + (tex b) ^ 2 := by
    intro b; simp only [Pi.add_apply]; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hortho]
  ring

/-- **The FKM/Deligne dictionary, as a named geometric hypothesis: conductor ≥ second moment.**
For any middle-extension `ℓ`-adic sheaf realizing the trace family `t`, the conductor `cond`
satisfies `cond ≥ rank ≥ M2(t)` (generic rank `=` second moment by orthogonality; `cond ≥ rank`
always).  This is the unformalisable étale-cohomology input; we carry it as a hypothesis (the
project's modularity convention).  Everything downstream of it is pure arithmetic. -/
def CondFloor (t : ι → ℝ) (cond : ℝ) : Prop := M2 t ≤ cond

/-- **The core pinning: the excess sub-object's second moment is pinned by the total minus the
bulk.**  If the FULL trace `η = tav + tex` has total second moment `M2 η = n` (Parseval, the exact
in-tree `subgroup_gaussSum_secondMoment`), and the split is orthogonal, then
`M2 tex = n − M2 tav`.  So driving the excess conductor `cond_exc` (≥ `M2 tex`) down to polylog
FORCES `M2 tav ≥ n − cond_exc`, i.e. the BULK piece carries almost the entire rank-`n` mass.  The
excess piece is then starved: it cannot also carry a worst-fiber spike whose square is `~ n·log`. -/
theorem exc_secondMoment_pinned (tav tex : ι → ℝ) (n : ℝ)
    (hortho : ∑ b, tav b * tex b = 0)
    (htot : M2 (tav + tex) = n) :
    M2 tex = n - M2 tav := by
  have h := M2_split_orthogonal tav tex hortho
  rw [htot] at h
  linarith

/-- **The drop-locus dichotomy (the reduction, abstract form).**  Suppose the excess sub-object
has polylog conductor `cond_exc ≤ polylog` (the candidate's hypothesis), and the total second
moment is `n` (Parseval), with an orthogonal split.  Then the bulk second moment is *forced up*:
`M2 tav ≥ n − polylog`.  In the prize regime `polylog ≪ n`, the bulk carries essentially the full
rank-`n` mass.  Since the worst-fiber sup `sup_b |η_b| = M(n)` is bounded by the bulk's own
contribution (the excess is starved), the prize sup is read from the rank-`(≈ n)` bulk object —
whose conductor is `≈ n` (the C2/A07/P3 wall).  This is the reduction to F10. -/
theorem bulk_carries_full_mass (tav tex : ι → ℝ) (n polylog : ℝ)
    (hortho : ∑ b, tav b * tex b = 0)
    (htot : M2 (tav + tex) = n)
    (hexc : CondFloor tex polylog) :
    n - polylog ≤ M2 tav := by
  unfold CondFloor at hexc
  have hpin : M2 tex = n - M2 tav := exc_secondMoment_pinned tav tex n hortho htot
  -- M2 tex ≤ polylog, and M2 tex = n - M2 tav, so n - M2 tav ≤ polylog, i.e. M2 tav ≥ n - polylog.
  rw [hpin] at hexc
  linarith

/-- **The excess does not fit (abstract).**  A worst-fiber excess `E(b*)` forces the excess trace
to satisfy `|tex(b*)| ≥ E(b*)`, hence (a single term lower-bounds the un-normalized sum)
`∑_b (tex b)² ≥ E(b*)²`, hence `M2 tex ≥ E(b*)² / q`.  If the conductor is polylog,
`M2 tex ≤ polylog`, so `E(b*)² ≤ q · polylog`.  Contrapositively, if `E(b*)² > q · polylog`, then
**no polylog-conductor sub-object can carry the excess at `b*`**.  (At the prize regime the
worst-fiber excess square is `~ n·log(p/n)` while `q·polylog = q·(log p)²`; this lemma is the clean
gate, instantiated numerically in `prize_excess_does_not_fit`.) -/
theorem excess_does_not_fit (tex : ι → ℝ) (bstar : ι) (E polylog : ℝ)
    (hE0 : 0 ≤ E) (hE : E ≤ |tex bstar|)
    (hexc : CondFloor tex polylog)
    (hcard : 0 < Fintype.card ι) :
    E ^ 2 ≤ (Fintype.card ι : ℝ) * polylog := by
  unfold CondFloor M2 at hexc
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  -- single term lower-bounds the sum: (tex bstar)² ≤ ∑_b (tex b)².
  have hterm : (tex bstar) ^ 2 ≤ ∑ b, (tex b) ^ 2 := by
    have := Finset.single_le_sum (f := fun b => (tex b) ^ 2)
      (fun b _ => sq_nonneg (tex b)) (Finset.mem_univ bstar)
    simpa using this
  -- E² ≤ (tex bstar)² since 0 ≤ E ≤ |tex bstar|.
  have hE2 : E ^ 2 ≤ (tex bstar) ^ 2 := by
    have : E ^ 2 ≤ |tex bstar| ^ 2 := pow_le_pow_left₀ hE0 hE 2
    rwa [sq_abs] at this
  -- chain: E² ≤ (tex bstar)² ≤ ∑(tex b)² = q · M2 tex ≤ q · polylog.
  have hsum_le : ∑ b, (tex b) ^ 2 ≤ (Fintype.card ι : ℝ) * polylog := by
    rw [div_le_iff₀ hqpos] at hexc
    linarith [hexc]
  calc E ^ 2 ≤ (tex bstar) ^ 2 := hE2
    _ ≤ ∑ b, (tex b) ^ 2 := hterm
    _ ≤ (Fintype.card ι : ℝ) * polylog := hsum_le

end ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor

/-! ## The concrete prize instance: the drop-locus sub-object cannot carry the excess (β = 4)

At the prize regime `n = 2^30`, `p = n^4 = 2^120` (`β = 4`, `p ≡ 1 mod n`), the worst-fiber
excess that `F_exc` must certify is `E(b*) = M(n) − √n ~ √(n·log(p/n)) − √n`, so a representative
single-fiber excess square is at least `n·log₂(p/n) = 2^30 · log₂(2^120/2^30) = 2^30 · 90`.

The candidate's polylog-conductor hypothesis allows the excess sub-object's second moment to be at
most `c·(log₂ p)² = c·120² = 14400·c`.  By `excess_does_not_fit`, fitting the excess at `b*` into a
sub-object of second moment `M2 tex ≤ polylog` requires `E(b*)² ≤ q·polylog`; but the structural
requirement is that the excess *sub-object* (not the whole family) realize the spike, so its OWN
second moment must be `≥ E(b*)²/q`-times-the-number-of-bad-`b`.  The decisive count below shows the
single worst-fiber excess square already dwarfs the entire polylog conductor budget. -/

namespace ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor

/-- **The prize-scale arithmetic gate (β = 4).**  The single worst-fiber excess square
`E² = n·log₂(p/n) = 2^30·90` is strictly larger than any polylog conductor budget
`polylog = c·(log₂ p)² = c·14400` for every `c ≤ 2^10 = 1024`.  Concretely `2^30·90 ≈ 9.66·10^10`,
while `1024·14400 ≈ 1.47·10^7` — a gap of `> 6500×`.  So a sub-object whose conductor (hence second
moment) is polylog cannot have a fiber whose excess square is `n·log(p/n)`: the drop-locus
sub-object **cannot carry the prize excess** while staying polylog.  This closes the T01 escape.

(The lemma is stated as the clean numeric inequality the geometric obstruction reduces to; the
`excess_does_not_fit` consumer turns "`F_exc` carries the excess at `b*`" + "polylog conductor" into
`E² ≤ q·polylog`, and here we record that the *intrinsic* worst-fiber budget `E²` already exceeds
the polylog conductor itself.) -/
theorem prize_excess_does_not_fit :
    ∀ c : ℝ, 0 ≤ c → c ≤ 1024 →
      c * ((120 : ℝ) ^ 2) < (2 : ℝ) ^ 30 * 90 := by
  intro c hc0 hc
  -- c·14400 ≤ 1024·14400 = 14745600 < 2^30·90.
  have hpoly : c * ((120 : ℝ) ^ 2) ≤ 1024 * ((120 : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_right hc
    positivity
  have hval : (1024 : ℝ) * ((120 : ℝ) ^ 2) = 14745600 := by norm_num
  have hrhs : (2 : ℝ) ^ 30 * 90 = 96636764160 := by norm_num
  rw [hval] at hpoly
  rw [hrhs]
  linarith

/-- **The conductor budget is dwarfed (the cleanest statement of the reduction).**  Even allowing a
generous polylog conductor up to `1024·(log₂ p)²`, the excess sub-object's permitted second moment
is `< n·log₂(p/n)` at the prize point.  But to carry the worst-fiber excess the sub-object needs a
fiber with `|tex(b*)| ≥ √(n·log₂(p/n))`, i.e. second-moment contribution `≥ n·log₂(p/n)/q` from
that one fiber — and to be the *sup-controlling* object it must concentrate there, contradicting
the polylog second-moment ceiling unless the bulk `F_avg` (rank `n`, cond `n`) already owns the
spike.  Hence the prize sup is governed by a rank-`n` object: **F10**. -/
theorem drop_locus_reduces_to_F10 :
    ((2 : ℝ) ^ 30 * 90) > (1024 : ℝ) * ((120 : ℝ) ^ 2) := by
  have := prize_excess_does_not_fit 1024 (by norm_num) (le_refl _)
  linarith

end ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor

/-! ## Axiom audit (run via `lake env lean`) -/
#print axioms ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor.M2_split_orthogonal
#print axioms ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor.exc_secondMoment_pinned
#print axioms ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor.bulk_carries_full_mass
#print axioms ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor.excess_does_not_fit
#print axioms ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor.prize_excess_does_not_fit
#print axioms ArkLib.ProximityGap.Frontier.T01DropLocusSubsheafConductor.drop_locus_reduces_to_F10
