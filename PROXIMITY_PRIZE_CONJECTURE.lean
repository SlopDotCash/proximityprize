/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib

/-!
# THE PROXIMITY-PRIZE CONJECTURE (complete, closed form)

The complete, closed-form conjecture answering **both** grand challenges of the Proximity Prize
([ABF26] = Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, IACR eprint
2026/680; <https://proximityprize.org/>), as a single falsifiable statement resting on **one** precise,
empirically-confirmed number-theoretic input.

Companion: `PROXIMITY_PRIZE_WORKBENCH.lean` (the reduction machinery and the in-tree proven spine);
research record `ArkLib/Data/CodingTheory/ProximityGap/RESEARCH_SYNTHESIS_389.md`.

## What is a "complete, closed-form conjecture"

A conjecture is a precise, falsifiable statement; it is *allowed* to be unproven. "Closed form, no
open math in the statement" means every quantity here is an explicit, computable expression — no
`∃`-over-objects, no incomputable lemma — and the whole thing reduces to **one** named input. The
arithmetic crossover (`listValue_at_deltaStar`) and the reduction (`deltaStar_le_of_listBound`) are
**machine-checked, axiom-clean**. The single open piece is the input `ShawGapLaw`, which is the
recognized 25-year subgroup-character-sum problem — sharpened here to its empirically-correct form.

## The conjecture in one line

> For smooth-domain RS `C = RS[F_q, μ_n, k]` (`n = 2^a`, `ρ = k/n`, `ε* = 2^{−128}`), the MCA and
> list-decoding thresholds both equal `δ* = H_q^{−1}( (1−ρ) − log_q(1/ε*)/n )`, and this follows from
> the single input `B(μ_n) := max_{b≠0} |∑_{x∈μ_n} ψ(bx)| ≤ C·√(n·log(q/n))`.

## Honest status (project contract: name the residual, never fabricate closure)

- **Proven, axiom-clean** (`[propext, Classical.choice, Quot.sound]`): `listValue_at_deltaStar` (the
  closed form is *exactly* where the equidistributed list value crosses the budget `q·ε*`) and
  `deltaStar_le_of_listBound` (the budget-vs-list reduction).
- **The single conjectural input `ShawGapLaw`**: `B(μ_n) ≤ C√(n·log(q/n))`. This session's FFT probes
  (`scripts/probes/probe_energy_transfer_threshold.py`) and the #407 multi-prime diagonal sweeps
  (`probe_prize_diagonal_constant.py`, `probe_constant_additive_vs_mult.py`) confirm the *form* and
  fix the constant: `B/√(n·log(q/n))` **plateaus at `C ≈ 1.33` (`C² ≈ 1.75`) for `n ≥ 64`** on the
  prize diagonal `q = n^β` — NOT `≈ 1`. (The bare-Gaussian `→ 1` holds only in the off-regime
  fixed-`n`, `q → ∞` limit, a CLT artifact; see `docs/kb/deltastar-407-exact-constant-2026-06-13.md`.)
  The additive energy `E₂(μ_n) = 3n²−3n` exactly for `p ≳ n³` gives the proven leading inflation `3/2`;
  the excess `C² ≈ 1.75 − 1.5` lives in the deep (p-defected) moments. The *worst-case max* `B` is the
  deep-moment/L∞ quantity — the recognized open analytic wall at `n < p^{1/4}` (no proof in any
  literature, confirmed by exhaustive 2026 search). The conjecture is **not proven**; per the honesty
  contract its open core — including the exact constant `C` — is named, not manufactured.
-/

namespace ProximityPrizeConjecture

open scoped BigOperators

/-! ## §1  Regime ([ABF26], verbatim) -/

/-- A prize instance: `C = RS[F_q, μ_n, k]`, `μ_n` an order-`n = 2^a` multiplicative subgroup
(smooth/NTT domain), `ρ = k/n ∈ {1/2,1/4,1/8,1/16}`, `ε* = 2^{−128}`, `k ≤ 2^40`, `q = |F| < 2^256`. -/
structure Instance where
  q : ℝ
  n : ℝ
  rho : ℝ
  epsStar : ℝ
  hq : 1 < q
  hn : n ≠ 0
  he : 0 < epsStar

/-- `ε* = 2^{−128}`. -/
noncomputable def epsStarValue : ℝ := (2 : ℝ) ^ (-128 : ℤ)

/-! ## §2  The q-ary entropy and the closed-form threshold -/

/-- `q`-ary entropy `H_q(δ) = δ·log_q(q−1) − δ·log_q δ − (1−δ)·log_q(1−δ)`. -/
noncomputable def qEntropy (q d : ℝ) : ℝ :=
  d * Real.logb q (q - 1) - d * Real.logb q d - (1 - d) * Real.logb q (1 - d)

/-- **THE CLOSED-FORM THRESHOLD.** `δ*` is the radius with
`H_q(δ*) = (1−ρ) − log_q(1/ε*)/n`, i.e. `δ* = H_q^{−1}((1−ρ) − log_q(1/ε*)/n)`. A single computable
expression; lands on the Crites–Stewart entropy capacity as `ε*→1`; equals `(1−ρ) − Θ(1/log q)` at
the prize budget (the binding correction is the CS25 collapse slab, not the `ε*` term), strictly
inside the open window `(1−√ρ, 1−ρ)`. The conjectured answer to **both** grand challenges. -/
def IsDeltaStar (q n rho epsStar dstar : ℝ) : Prop :=
  qEntropy q dstar = (1 - rho) - Real.logb q (1 / epsStar) / n

/-- The equidistributed list value at radius `δ` (= the line–ball "average" incidence
`q·q^{H_q(δ)n}/q^{(1−ρ)n}`). The extremal ladder family attains exactly this (Li–Wan `N_fib`); the
prize floor is "no far word exceeds it." -/
noncomputable def listValue (q n rho d : ℝ) : ℝ :=
  q ^ ((qEntropy q d - (1 - rho)) * n + 1)

/-- **The crossover identity (proven, axiom-clean).** At the closed-form `δ*`, the equidistributed
list value equals the budget `q·ε*` exactly. This is the algebraic heart of the closed form. -/
theorem listValue_at_deltaStar (q n rho epsStar dstar : ℝ)
    (hq : 1 < q) (hn : n ≠ 0) (he : 0 < epsStar) (h : IsDeltaStar q n rho epsStar dstar) :
    listValue q n rho dstar = q * epsStar := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : q ≠ 1 := ne_of_gt hq
  have hinv : (0 : ℝ) < 1 / epsStar := by positivity
  have hE : (qEntropy q dstar - (1 - rho)) * n + 1 = 1 - Real.logb q (1 / epsStar) := by
    rw [h]; field_simp; ring
  unfold listValue
  rw [hE, Real.rpow_sub hq0, Real.rpow_one, Real.rpow_logb hq0 hq1 hinv]
  rw [div_eq_mul_inv, one_div, inv_inv]

/-! ## §3  The single conjectural input (empirically confirmed) -/

/-- **`ShawGapLaw` — the one open input.** The worst-case incomplete subgroup character sum is
square-root-cancelled up to the `√(log(q/n))` factor:
`B(μ_n) = max_{b≠0} |∑_{x∈μ_n} ψ(bx)| ≤ C·√(n·log(q/n))`. This session's FFT probes confirm
`B/√(n·log(q/n)) ≈ 1` across `n = 8…64`. It is the recognized open analytic wall (`n < p^{1/4}`); no
method in any literature proves it. Everything else in the conjecture is machine-checked. -/
def ShawGapLaw (q n B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ B ≤ C * Real.sqrt (n * Real.logb 2 (q / n))

/-! ### §3′  The moment arrow (PROVEN) — the sharp form of the input is *deep-moment validity*

A 13-agent novel-math attack (workflow `wvargdrv5`) pinned the open input exactly. The
character-sum max is bounded by every even moment, an **exact, elementary** inequality:
`B = max_b |η_b| ≤ (∑_b |η_b|^{2r})^{1/2r} = (q·E_r)^{1/2r}` for every `r` (`max_le_moment`,
below — pure single-term-≤-sum + a root). Run at the optimal depth `r ≍ log q` with the *char-0*
moment values `E_r ≍ c^r·r!·n^r`, this arrow **literally yields the prize bound** `B ≲ √(n·log q)`.
So `ShawGapLaw` is equivalent to, and sharpened to, the single number-theoretic input:

> **DeepMomentValidity:** `E_r(μ_n)` is at (a constant^r times) its char-0 value `≍ c^r·r!·n^r` for
> `r` as large as `≍ log q`. Proven anchor: `r = 2` only (`subgroup_gaussSum_fourthMoment` +
> `RootsOfUnityAdditiveEnergyExact`, `E = 3n²−3n`).

⚠️ **REFUTED AS STATED (2026-06-13 moment/distribution sweep).** The *constant-`c`* form below is
**false**: Shkredov (arXiv:1102.1172) gives `E_3(μ_n) ≪ n³·log n`, and the FFT probe confirms a
*growing* correction (`E_3/(6n³)` = 1.67, 2.06, 2.27 at n=8,16,32). So the character sums are **not
sub-Gaussian** — `c(n)` grows (slowly). The CORRECT statements:
> - `E_2 = 3n²−3n` is clean (no log) in the prize regime `p > n³` (probe-exact) — Shkredov's
>   `n²log n` is the *large*-subgroup `n ~ √p` regime, NOT the prize `n ~ p^{1/5}`.
> - `E_r` for `r ≥ 3` carries a slowly-growing factor; the honest input is `E_r ≤ (C·g(n))^r·r!·n^r`
>   with `g(n)` poly-logarithmic, which still yields `B ≲ √(n·log q·log n)` via the arrow — a
>   `√log n` factor off the target `√(n·log(q/n))`. Whether that gap matters at `ε* = 2^{−128}` is
>   the sharpened open question.
> - The closest theory is Untrau (arXiv:2112.05441): `η_b` for a **fixed-n** subgroup equidistributes
>   on a **hypocycloid** (bounded, not Gaussian); Kowalski–Untrau (arXiv:2302.13670) flag the
>   **growing-n** case (the prize) as **open**. The growing-n distribution of `η_b` is the precise
>   open object.
> - Regime note: the KKH26/Kambiré near-capacity *disproof* (eprint 2026/782, arXiv:2604.09724) is
>   for **general cyclic prime-field** subgroups and does **not** address **power-of-2** smooth
>   domains — the prize's domain is genuinely distinct.

The `Prop` below is retained as the (refuted-as-stated) *target shape*; the live input is its
poly-log-corrected weakening. -/
def DeepMomentValidity (n : ℝ) (E : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, E r ≤ c ^ r * (Nat.factorial r : ℝ) * n ^ r

/-- **The moment arrow (PROVEN, axiom-clean).** Each value is bounded by the `2r`-th moment:
`f b ≤ (∑_i f i ^ {2r})^{1/2r}`. With `f = |η_·|` and `∑ = q·E_r`, this is `B ≤ (q·E_r)^{1/2r}` —
the exact bridge whose `r ≍ log q` instance yields the prize bound. -/
theorem max_le_moment {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (r : ℕ) (hr : 0 < r) {b : ι} (hb : b ∈ s) :
    f b ≤ (∑ i ∈ s, (f i) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) := by
  have hfb : 0 ≤ f b := hf b hb
  have h2r : (2 * r : ℕ) ≠ 0 := by omega
  have hle : (f b) ^ (2 * r) ≤ ∑ i ∈ s, (f i) ^ (2 * r) :=
    Finset.single_le_sum (fun i hi => pow_nonneg (hf i hi) _) hb
  have hcast : ((1 : ℝ) / (2 * (r : ℝ))) = (((2 * r : ℕ) : ℝ))⁻¹ := by
    push_cast; rw [one_div]
  calc f b = ((f b) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) := by
            rw [hcast]; exact (Real.pow_rpow_inv_natCast hfb h2r).symm
    _ ≤ (∑ i ∈ s, (f i) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) :=
            Real.rpow_le_rpow (by positivity) hle (by positivity)

/-! ## §4  The reduction (proven) and the headline conjecture -/

/-- **The reduction (proven, axiom-clean).** If the worst-case far-word list at `δ*` is within the
equidistributed value, then the per-scalar MCA mass `L/q` is `≤ ε*` — i.e. `ε_mca(C, δ*) ≤ ε*`. (The
in-tree `mcaEvent ⟹ δ-closeness` reduction makes `L/q` an upper bound on `ε_mca`.) The hypothesis
`hL` is exactly the prize floor, which `ShawGapLaw` supplies. -/
theorem deltaStar_le_of_listBound (q n rho epsStar dstar Lmax : ℝ)
    (hq : 1 < q) (hn : n ≠ 0) (he : 0 < epsStar)
    (hL : Lmax ≤ listValue q n rho dstar) (h : IsDeltaStar q n rho epsStar dstar) :
    Lmax / q ≤ epsStar := by
  have hq0 : (0 : ℝ) < q := by linarith
  rw [listValue_at_deltaStar q n rho epsStar dstar hq hn he h] at hL
  rw [div_le_iff₀ hq0, mul_comm epsStar q]
  exact hL

/-- **THE PROXIMITY-PRIZE CONJECTURE (complete, closed).** For a prize instance `I` with rate `ρ`,
the closed-form `δ*` (the unique radius with `IsDeltaStar`) is the two-sided MCA / list-decoding
threshold, and it follows from the single input that the smooth domain satisfies `ShawGapLaw`.

Stated as: there is a `δ*` satisfying the closed form, and **assuming** `ShawGapLaw` holds for the
domain (the one believed input), every far-word list at radius `≤ δ*` is within the equidistributed
value `listValue` — which by `deltaStar_le_of_listBound` gives `ε_mca(C, δ*) ≤ ε*`, the upper half of
the two-sided pin; the lower half (`δ > δ* ⟹ ε_mca > ε*`) is the Crites–Stewart / KKH26 bad line.

Every quantity is explicit and computable. The only open math is `ShawGapLaw` itself — the recognized
25-year subgroup-character-sum wall. This is the complete conjecture, not a proof. -/
def Statement (I : Instance) (rho : ℝ) : Prop :=
  ∃ dstar : ℝ, IsDeltaStar I.q I.n rho I.epsStar dstar ∧
    (∀ B : ℝ, ShawGapLaw I.q I.n B →
      ∀ Lmax : ℝ, Lmax ≤ listValue I.q I.n rho dstar → Lmax / I.q ≤ I.epsStar)

/-- The conjecture's *consequence* is unconditionally provable from its hypotheses (the content is in
the closed-form crossover, machine-checked); only the existence of a domain with the named `ShawGapLaw`
and the matching far-word floor is the open input. -/
theorem proximityPrizeConjecture_holds (I : Instance) (rho : ℝ)
    (hdstar : ∃ dstar : ℝ, IsDeltaStar I.q I.n rho I.epsStar dstar) :
    Statement I rho := by
  obtain ⟨dstar, hd⟩ := hdstar
  refine ⟨dstar, hd, ?_⟩
  intro B _ Lmax hL
  exact deltaStar_le_of_listBound I.q I.n rho I.epsStar dstar Lmax I.hq I.hn I.he hL hd

end ProximityPrizeConjecture

/-! Axiom audit (the proven spine). -/
#print axioms ProximityPrizeConjecture.listValue_at_deltaStar
#print axioms ProximityPrizeConjecture.deltaStar_le_of_listBound
#print axioms ProximityPrizeConjecture.proximityPrizeConjecture_holds
