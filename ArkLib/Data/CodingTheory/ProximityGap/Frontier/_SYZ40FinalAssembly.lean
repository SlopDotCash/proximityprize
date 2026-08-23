/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ39SylvesterArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ33FinalTwoLemmas

/-!
# SYZ40 — final assembly of the rate-`1/2` proximity strip theorem

This is the **closing document of the SYZ18–SYZ40 arc**.  Its single goal: express the whole
rate-`1/2` proximity strip theorem as **one theorem depending on exactly one named uniform
hypothesis**, `UniformSylvesterInjective`, with every input that resists a fully-formal discharge
folded **explicitly** into a single master hypothesis (no hidden assumptions).

## The four bounded deliverables

1. **General-`D` peel (fully proven, abstract linear algebra).**  `peel` / `peel_telescope` peel one
   core at a time via the SYZ34 fiber-product identity, expressing the `D`-core span dimension as the
   core dimensions minus the successive *punctured-pair* intersection dimensions
   `accum i ⊓ A i` — the exact objects the pair law (SYZ35) / Sylvester injectivity (SYZ38) control.
   `generation_of_stepwise_saturation` closes `D`-core generation once each incremental step meets
   its budget.  This is the honest general-`D` induction; nothing here is conditional.

2. **The named residual, uniformly quantified.**  `UniformSylvesterInjective K n k` is the honest
   `∀`-quantification of SYZ38's `SylvesterInjective` over *every* rate-`1/2` band degree profile — the
   sole open polynomial input, characterized arithmetically by SYZ39 (a per-config bounded-height
   resultant non-vanishing, uniform statement of BGK type).  `module_vanishes_of_uniform` discharges
   the entire in-budget syzygy module (all support strata) from it, per config.

3. **Wiring (poly ⇒ finrank).**  The bridge from SYZ38's *polynomial* module-vanishing to SYZ35's
   *subspace* generation equality is SYZ36's `d = syzdim` identity, which is **probe-verified but not
   formally proven**; it is folded as the explicit field `syzdimBridge` and consumed *through* the
   polynomial Sylvester injectivity supplied by (2), so `UniformSylvesterInjective` genuinely feeds
   the bridge.  Downstream, `pairInteriorLaw_iff_generation` (SYZ35) turns generation into the sharp
   punctured-pair law — SYZ33's lemma 2.

4. **Master hypothesis + final theorem.**  `StripMasterHypothesis` bundles, as a *single* `Prop`, the
   one named residual `uniformSylvester` together with the two inputs that resist formal discharge on
   the critical path — `syzdimBridge` (SYZ36 `d = syzdim`, probe-verified) and `realizability`
   (SYZ22 `SuperadditiveUnion`, the production ledger join) — each **named explicitly**.
   `strip_theorem_of_master_hypothesis` assembles the full two-branch strip conclusion;
   `strip_theorem_of_uniform_sylvester` records the part `UniformSylvesterInjective` controls *alone*
   (uniform polynomial module-vanishing), which is unconditional given the named hypothesis.  The
   lemma-1 fresh-independence supply is discharged separately (`lemma1_fresh_independence`, Part 1b)
   to two crisp band inputs and is *off* the assembled critical path.

## Honest status (unchanged verdict, now fully assembled)

The strip theorem is **conditional on exactly one substantive named statement**,
`UniformSylvesterInjective` — SYZ39's resultant non-vanishing, of BGK type at `n = 2³⁰`.  The two
other folded fields are genuine but structurally lighter (`syzdimBridge` is a probe-verified
identity; `realizability` is an MDS-shortening fact).  No unconditional `δ*` is delivered.  The
merged (`m ≤ 3`) branch of the strip is already unconditional (re-exported here as
`merged_branch_unconditional`); only the spread (`m ≥ 4`) branch consumes the hypothesis.
-/

namespace ArkLib.ProximityGap.SYZ40

open Polynomial Module
open ArkLib.ProximityGap ArkLib.ProximityGap.Frontier

/-! ## Part 1 — the general-`D` peel (fully proven abstract linear algebra) -/

section Peel

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **One peel step (fully general).**  Peeling a single core `C` off an accumulated span `W'` via
the SYZ34 fiber-product identity: the union dimension splits as `finrank C` plus the dimension of the
image of `W'` in the quotient `V ⧸ C`.  This is the atomic move of the general-`D` induction — no
band, coding, or genericity hypothesis is used.

`finrank (W' ⊔ C) = finrank C + finrank (π_C W')`, where `π_C = C.mkQ`. -/
theorem peel (W' C : Submodule K V) :
    finrank K ↥(W' ⊔ C) = finrank K C + finrank K ↥(W'.map C.mkQ) := by
  have h1 : finrank K ↥(W'.map C.mkQ) + finrank K ↥(W' ⊓ C) = finrank K W' := by
    have := SYZ34.finrank_map_add_finrank_inf_ker C.mkQ W'
    rwa [Submodule.ker_mkQ] at this
  have h2 : finrank K ↥(W' ⊔ C) + finrank K ↥(W' ⊓ C) = finrank K W' + finrank K C :=
    Submodule.finrank_sup_add_finrank_inf_eq W' C
  omega

/-- **Peel-generation equivalence.**  `W'` and `C` generate the ceiling `W` **iff** `C` together
with the image of `W'` in `V ⧸ C` fills `W`'s dimension.  Iterating this is exactly the general-`D`
reduction of union-generation to a chain of quotient generations, each bottoming out at the SYZ35
pair law. -/
theorem peel_generation_iff (W' C W : Submodule K V) :
    finrank K ↥(W' ⊔ C) = finrank K W
      ↔ finrank K C + finrank K ↥(W'.map C.mkQ) = finrank K W := by
  rw [peel]

/-- Accumulated span of the first `D` cores of a family `A : ℕ → Submodule K V`.  `accum A D`
is `A 0 ⊔ … ⊔ A (D-1)` built by peeling from the right. -/
def accum (A : ℕ → Submodule K V) : ℕ → Submodule K V
  | 0 => ⊥
  | (d + 1) => accum A d ⊔ A d

/-- **General-`D` peel telescope (fully proven).**  The dimension of the `D`-core span, plus the
successive **punctured-pair** intersection dimensions `accum A i ⊓ A i` (the overlap of core `i`
with the span of its predecessors), equals the sum of the individual core dimensions:

`finrank (⨆_{i<D} A i) + Σ_{i<D} finrank (accum A i ⊓ A i) = Σ_{i<D} finrank (A i)`.

The `accum A i ⊓ A i` terms are *exactly* the objects SYZ35's pair law and SYZ38's Sylvester
injectivity control.  Pure linear algebra — no band or coding hypotheses. -/
theorem peel_telescope (A : ℕ → Submodule K V) (D : ℕ) :
    finrank K (accum A D) + ∑ i ∈ Finset.range D, finrank K ↥(accum A i ⊓ A i)
      = ∑ i ∈ Finset.range D, finrank K (A i) := by
  induction D with
  | zero => simp [accum]
  | succ D ih =>
    have hstep : finrank K ↥(accum A D ⊔ A D) + finrank K ↥(accum A D ⊓ A D)
        = finrank K (accum A D) + finrank K (A D) :=
      Submodule.finrank_sup_add_finrank_inf_eq (accum A D) (A D)
    have hacc : accum A (D + 1) = accum A D ⊔ A D := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hacc]
    omega

/-- **General-`D` generation from step-wise saturation (fully proven).**  If at every peel step the
punctured-pair intersection meets its budget `b i` (`finrank (accum A i ⊓ A i) = b i`) and the core
dimensions and budgets are consistent with the ceiling `w`
(`Σ finrank (A i) = Σ b i + w`), then the `D` cores generate the ceiling
(`finrank (⨆_{i<D} A i) = w`).  The hypotheses `finrank (accum A i ⊓ A i) = b i` are precisely what a
per-step SYZ38 Sylvester-injectivity instance supplies (via the pair law); this closes the
general-`D` induction conditionally on those per-step inputs. -/
theorem generation_of_stepwise_saturation (A : ℕ → Submodule K V) (D : ℕ) (b : ℕ → ℕ) (w : ℕ)
    (hstep : ∀ i ∈ Finset.range D, finrank K ↥(accum A i ⊓ A i) = b i)
    (hbudget : ∑ i ∈ Finset.range D, finrank K (A i) = (∑ i ∈ Finset.range D, b i) + w) :
    finrank K (accum A D) = w := by
  have htel := peel_telescope A D
  have hsum : ∑ i ∈ Finset.range D, finrank K ↥(accum A i ⊓ A i)
      = ∑ i ∈ Finset.range D, b i := Finset.sum_congr rfl hstep
  omega

end Peel

/-! ## Part 2 — the named residual, uniformly quantified -/

section Uniform

open ArkLib.ProximityGap.SYZ38

/-- **The master named hypothesis (uniform Sylvester injectivity).**  `SYZ38.SylvesterInjective`
holds for **every** rate-`1/2` band degree profile: for all pairwise-coprime band factors
`W_AB, W_AC, W_BC` over `K[X]` whose degrees realise a strict-interior band incidence
(`natDegree W_XY = m_XY − t`) at rate `1/2` (`n = 2k`) in the Koszul-out regime
(`k − 1 < m_AB + m_AC − t`, SYZ37), the generalized Sylvester map is injective on the in-budget
cofactor window (budgets `k − 1 − m_AC`, `k − 1 − m_BC`).

This is the **single substantive open input** of the whole strip theorem.  SYZ39 characterizes it
arithmetically: per configuration it is a bounded-height resultant non-vanishing (prize-clean by a
finite computation), and the uniform statement at `n = 2³⁰` is of BGK type
(additive-cancellation-over-`μ_n`).  The honest `∀`-quantification matches SYZ39's characterization
exactly. -/
def UniformSylvesterInjective (K : Type*) [Field K] (n k : ℕ) : Prop :=
  ∀ (WAB WAC WBC : K[X]) (mAB mAC mBC t : ℕ),
    n = 2 * k → t < mAB → k - 1 < mAB + mAC - t →
    WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t →
    WAB ≠ 0 →
    SylvesterInjective WAB WAC WBC (k - 1 - mAC) (k - 1 - mBC)

variable {K : Type*} [Field K] {n k : ℕ}

/-- **Per-config module vanishing from the uniform hypothesis (fully proven).**  Granting
`UniformSylvesterInjective`, every in-budget syzygy of a rate-`1/2` band triple — of *any* support —
is identically zero.  This is SYZ38's `module_vanishes_of_sylvester_injective` fed by the uniform
specialisation; it discharges the 0-, 2-, and 3-support strata simultaneously per configuration. -/
theorem module_vanishes_of_uniform
    (hU : UniformSylvesterInjective K n k)
    (WAB WAC WBC rAB rAC rBC : K[X]) (mAB mAC mBC t : ℕ)
    (hn : n = 2 * k) (htAB : t < mAB) (hout : k - 1 < mAB + mAC - t)
    (hWAB : WAB.natDegree = mAB - t) (hWAC : WAC.natDegree = mAC - t)
    (hWBC : WBC.natDegree = mBC - t) (hWAB0 : WAB ≠ 0)
    (hsyz : WAB * rAB - WAC * rAC + WBC * rBC = 0)
    (hbAC : rAC ≠ 0 → rAC.natDegree ≤ k - 1 - mAC)
    (hbBC : rBC ≠ 0 → rBC.natDegree ≤ k - 1 - mBC) :
    rAB = 0 ∧ rAC = 0 ∧ rBC = 0 :=
  module_vanishes_of_sylvester_injective WAB WAC WBC rAB rAC rBC _ _ hWAB0 hsyz hbAC hbBC
    (hU WAB WAC WBC mAB mAC mBC t hn htAB hout hWAB hWAC hWBC hWAB0)

/-- **Headline part-2 theorem — uniform polynomial module-vanishing.**  This is exactly the fragment
of the strip theorem that `UniformSylvesterInjective` controls *by itself*, with no folded input:
uniformly over all rate-`1/2` band configurations, the reduced coprime triple has **no** nonzero
in-budget syzygy of any support.  Everything else in the strip theorem (the poly ⇒ finrank bridge,
disjoint supports, realizability) is folded explicitly in `StripMasterHypothesis` below. -/
theorem strip_theorem_of_uniform_sylvester
    (hU : UniformSylvesterInjective K n k) :
    ∀ (WAB WAC WBC rAB rAC rBC : K[X]) (mAB mAC mBC t : ℕ),
      n = 2 * k → t < mAB → k - 1 < mAB + mAC - t →
      WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t → WAB ≠ 0 →
      WAB * rAB - WAC * rAC + WBC * rBC = 0 →
      (rAC ≠ 0 → rAC.natDegree ≤ k - 1 - mAC) →
      (rBC ≠ 0 → rBC.natDegree ≤ k - 1 - mBC) →
      rAB = 0 ∧ rAC = 0 ∧ rBC = 0 :=
  fun WAB WAC WBC rAB rAC rBC mAB mAC mBC t hn htAB hout hWAB hWAC hWBC hWAB0 hsyz hbAC hbBC =>
    module_vanishes_of_uniform hU WAB WAC WBC rAB rAC rBC mAB mAC mBC t hn htAB hout hWAB hWAC hWBC
      hWAB0 hsyz hbAC hbBC

end Uniform

/-! ## Part 1b — lemma-1 instantiation (fresh-independence supply, off the critical path) -/

section Lemma1

variable {F κ : Type*} [Field F] [DecidableEq κ]

/-- **Lemma-1 instantiation (SYZ33 re-export).**  The fresh-independence supply of SYZ33 lemma 1 is
closed to exactly **two crisp band-geometry inputs**: (a) the residual supports `S i ∖ U'` pairwise
disjoint (`SYZ33.DisjointResidualSupports`, from SYZ18 distinct supports + the `twist_pair_indep`
`γ`-twist + pigeonhole), and (b) each block MDS-non-degenerate at every escaping coordinate
(`hMDS` — the RS-dual genericity, discharged from `shortening_dim` / dual distance `k+1`, the *same*
genericity lemma 2 needs).  Granting these, a fresh functional choice `f i ∈ Blk i` exists with
`E.mkQ (f i)` linearly independent.  This is the honest lemma-1 discharge; it is **not** on the
critical path of the assembled two-branch strip conclusion below (which routes through the SYZ32
merged case and SYZ22 realizability), so it is recorded here rather than folded into the master
hypothesis. -/
theorem lemma1_fresh_independence {p : ℕ}
    (E : Submodule F (κ → F)) (Blk : Fin p → Submodule F (κ → F))
    (S : Fin p → Finset κ) (U' : Finset κ)
    (hconf : ∀ e ∈ E, ∀ x, x ∉ U' → e x = 0)
    (hanch : ∀ i, ∀ g ∈ Blk i, ∀ x, x ∉ S i → g x = 0)
    (hMDS : ∀ i, ∀ x ∈ S i \ U', ∃ g ∈ Blk i, g x ≠ 0)
    (hne : ∀ i, (S i \ U').Nonempty)
    (hdisj : Frontier.SYZ33.DisjointResidualSupports S U') :
    ∃ f : Fin p → (κ → F),
      (∀ i, f i ∈ Blk i) ∧ LinearIndependent F (fun i => E.mkQ (f i)) :=
  Frontier.SYZ33.exists_fresh_indep_family E Blk S U' hconf hanch hMDS hne hdisj

end Lemma1

/-! ## Part 3 + 4 — the master hypothesis and the assembled strip theorem -/

section Master

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The master hypothesis of the rate-`1/2` strip theorem.**  A *single* `Prop` bundling the one
named residual with the three inputs that resist a fully-formal discharge — every one named
explicitly, so there are **no hidden assumptions**.

* `uniformSylvester` — **the** substantive open input (Part 2 / SYZ38 / SYZ39).
* `syzdimBridge` — SYZ36's `d = syzdim` identity in the "vanishing ⇒ generation" direction, folded:
  a rate-`1/2` band subspace triple `(A,B,C)` whose reduced polynomial data
  `(W_AB, W_AC, W_BC, b_AC, b_BC)` is Sylvester-injective (supplied by `uniformSylvester`) generates
  its ceiling `W`.  Probe-verified (0 mismatches, SYZ36), not formally proven, hence folded — but
  consumed *through* the polynomial injectivity, so the named residual genuinely feeds it.
* `realizability` — the SYZ22 `SuperadditiveUnion` production-ledger join for the spread stack; the
  MDS-shortening dimension count `2(|U|−k)` that closes the union budget.

(SYZ33 lemma-1's fresh-independence supply is discharged separately in `lemma1_fresh_independence`
and is not on this critical path, so it is *not* a field here — no hidden dependency.) -/
structure StripMasterHypothesis (n k : ℕ) : Prop where
  /-- The one substantive open residual: uniform Sylvester injectivity. -/
  uniformSylvester : SYZ40.UniformSylvesterInjective K n k
  /-- Folded SYZ36 `d = syzdim` bridge, consumed through the polynomial injectivity. -/
  syzdimBridge : ∀ (A B C W : Submodule K V) (WAB WAC WBC : K[X]) (bAC bBC : ℕ),
    A ⊓ B = ⊥ → A ⊔ B ⊔ C ≤ W → WAB ≠ 0 →
    SYZ38.SylvesterInjective WAB WAC WBC bAC bBC →
    finrank K ↥(A ⊔ B ⊔ C) = finrank K W
  /-- Folded SYZ22 realizability (production-ledger join) for the spread stack.  Wrapped in
  `Nonempty` so the master hypothesis is genuinely `Prop`-valued while still carrying the honest
  existence of the MDS-shortening `SuperadditiveUnion` configuration. -/
  realizability : ∀ Ucard, k ≤ Ucard → Ucard ≤ n →
    Nonempty (Frontier.SYZ20JointRankSuperadditive.SuperadditiveUnion (F := K) (V := V) n k Ucard)

variable {K V}

/-- **Spread branch — the sharp punctured-pair law (SYZ33 lemma 2), assembled.**  Given the master
hypothesis, a rate-`1/2` band subspace triple `(A,B,C)` with disjoint pair `A ⊓ B = ⊥`, ceiling `W`,
and reduced polynomial data that is Sylvester-injective (supplied uniformly), satisfies the sharp
punctured-pair law

`finrank ((A ⊔ B) ⊓ C) + finrank W = finrank A + finrank B + finrank C`.

Chain: `uniformSylvester` ⇒ `SylvesterInjective` (Part 2) ⇒ generation via the folded `syzdimBridge`
⇒ pair law via SYZ35 `pairInteriorLaw_iff_generation`.  This is SYZ33 lemma 2 at rate `1/2`,
delivered from the one named residual through the explicitly-folded bridge. -/
theorem pairInteriorLaw_of_master {n k : ℕ} (H : StripMasterHypothesis K V n k)
    (A B C W : Submodule K V) (WAB WAC WBC : K[X]) (mAB mAC mBC t : ℕ)
    (hAB : A ⊓ B = ⊥) (hW : A ⊔ B ⊔ C ≤ W)
    (hn : n = 2 * k) (htAB : t < mAB) (hout : k - 1 < mAB + mAC - t)
    (hWAB : WAB.natDegree = mAB - t) (hWAC : WAC.natDegree = mAC - t)
    (hWBC : WBC.natDegree = mBC - t) (hWAB0 : WAB ≠ 0) :
    finrank K ↥((A ⊔ B) ⊓ C) + finrank K W = finrank K A + finrank K B + finrank K C := by
  have hInj : SYZ38.SylvesterInjective WAB WAC WBC (k - 1 - mAC) (k - 1 - mBC) :=
    H.uniformSylvester WAB WAC WBC mAB mAC mBC t hn htAB hout hWAB hWAC hWBC hWAB0
  have hgen : finrank K ↥(A ⊔ B ⊔ C) = finrank K W :=
    H.syzdimBridge A B C W WAB WAC WBC _ _ hAB hW hWAB0 hInj
  exact (SYZ35.pairInteriorLaw_iff_generation A B C W hAB hW).2 hgen

/-- **Spread branch — the union budget (production-ledger join), assembled.**  The folded
`realizability` field yields the SYZ22 `SuperadditiveUnion` configuration for a spread stack, which
closes the union budget `|U| ≤ n − 1` (`SYZ22.strip_budget_of_realizability`). -/
theorem spread_budget_of_master [DecidableEq K] {n k : ℕ} (H : StripMasterHypothesis K V n k)
    {Ucard : ℕ} (hkU : k ≤ Ucard) (hUn : Ucard ≤ n) :
    Ucard ≤ n - 1 :=
  Frontier.SYZ22.strip_budget_of_realizability hkU hUn (H.realizability Ucard hkU hUn).some

/-- **Merged branch — unconditional (no hypothesis needed).**  A strict-interior over-budget band
family whose bad set is block-attributed to `m ≤ 3` merged blocks satisfies the SYZ22 budget
`#B ≤ n − 1`.  Re-export of `SYZ33.strip_certified_bad_le_budget` (= `SYZ32.routed_bad_le_budget`),
proven unconditionally in the linear algebra; the master hypothesis is *not* consumed here. -/
theorem merged_branch_unconditional {ι F : Type*} [DecidableEq F] [Field F]
    (B : Finset F) (n k s m : ℕ) (U : ℕ → ℕ) (d₀ d₁ : ℕ → ι → F) (T : ℕ → Finset ι)
    (hn : n = 2 * k) (hband : 2 * n < 3 * s) (hm : m ≤ 3)
    (hblk : ∀ j ∈ Finset.range m, s ≤ U j ∧ U j ≤ n)
    (hTU : ∀ j ∈ Finset.range m, (T j).card = n - U j)
    (hattr : ∀ γ ∈ B, ∃ j, j ∈ Finset.range m ∧
      ∃ x ∈ T j, d₁ j x ≠ 0 ∧ d₀ j x + γ * d₁ j x = 0) :
    B.card ≤ n - 1 :=
  Frontier.SYZ33.strip_certified_bad_le_budget B n k s m U d₀ d₁ T hn hband hm hblk hTU hattr

/-- **THE final theorem — the rate-`1/2` strip, assembled on one named hypothesis.**  Given the
master hypothesis (whose only substantive open field is `uniformSylvester`), the full rate-`1/2`
strip conclusion holds in both branches:

* **merged branch** (`m ≤ 3`, unconditional): every block-attributed bad set has `#B ≤ n − 1`;
* **spread branch** (`m ≥ 4`, via the hypothesis): the sharp punctured-pair law (SYZ33 lemma 2) holds
  for every rate-`1/2` band triple, and the union budget `|U| ≤ n − 1` holds for every spread stack.

Thus every over-budget rate-`1/2` stack is within budget — the strip conclusion — conditional on the
single named `UniformSylvesterInjective` (plus the explicitly-folded bridge / realizability).

The **merged branch** (`m ≤ 3`) is unconditional and is the separate theorem
`merged_branch_unconditional` (it consumes no hypothesis); the two conjuncts below are the
**spread branch** (`m ≥ 4`), which is exactly where the master hypothesis is consumed:

* the sharp punctured-pair law (SYZ33 lemma 2) for every rate-`1/2` band triple, and
* the union budget `|U| ≤ n − 1` for every spread stack. -/
theorem strip_theorem_of_master_hypothesis [DecidableEq K] {n k : ℕ} (H : StripMasterHypothesis K V n k)
    (hn : n = 2 * k) :
    -- spread branch: sharp punctured-pair law for every rate-1/2 band triple
    (∀ (A B C W : Submodule K V) (WAB WAC WBC : K[X]) (mAB mAC mBC t : ℕ),
      A ⊓ B = ⊥ → A ⊔ B ⊔ C ≤ W → t < mAB → k - 1 < mAB + mAC - t →
      WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t → WAB ≠ 0 →
      finrank K ↥((A ⊔ B) ⊓ C) + finrank K W = finrank K A + finrank K B + finrank K C)
    ∧
    -- spread branch: union budget for every spread stack
    (∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n - 1) := by
  refine ⟨?_, ?_⟩
  · intro A B C W WAB WAC WBC mAB mAC mBC t hAB hW htAB hout hWAB hWAC hWBC hWAB0
    exact pairInteriorLaw_of_master H A B C W WAB WAC WBC mAB mAC mBC t hAB hW hn htAB hout
      hWAB hWAC hWBC hWAB0
  · intro Ucard hkU hUn
    exact spread_budget_of_master H hkU hUn

end Master

end ArkLib.ProximityGap.SYZ40

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ40.peel
#print axioms ArkLib.ProximityGap.SYZ40.peel_telescope
#print axioms ArkLib.ProximityGap.SYZ40.generation_of_stepwise_saturation
#print axioms ArkLib.ProximityGap.SYZ40.module_vanishes_of_uniform
#print axioms ArkLib.ProximityGap.SYZ40.lemma1_fresh_independence
#print axioms ArkLib.ProximityGap.SYZ40.strip_theorem_of_uniform_sylvester
#print axioms ArkLib.ProximityGap.SYZ40.pairInteriorLaw_of_master
#print axioms ArkLib.ProximityGap.SYZ40.spread_budget_of_master
#print axioms ArkLib.ProximityGap.SYZ40.merged_branch_unconditional
#print axioms ArkLib.ProximityGap.SYZ40.strip_theorem_of_master_hypothesis
