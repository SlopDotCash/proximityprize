/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Door-(iv) constraint: an argmax-decoupled functional cannot absolutely control `M(n)` (#444)

Lane-1 probe `probe_dooriv_smallball_vs_energy.py` (proper `μ_n`, `p ≫ n³`, structured incl. Fermat
primes, never `n = q-1`) measured, jointly over the full group, the small-ball / anti-concentration
coherence functional `F = C_worst(b)` and the sup-norm mass `M-functional `η(b) = |Σ_{y∈μ_n} e_p(b·y)|`:

| n   | argmax(F) = argmax(η)? | spearman(η, F) |
|-----|------------------------|----------------|
| 16  | NO                     | 0.490          |
| 32  | NO                     | 0.194          |
| 64  | NO                     | 0.113          |
| 128 | NO                     | 0.074          |
| 256 | NO                     | 0.046          |

The candidate control functional and the target have **different argmaxes at every `n`**, and their
rank-correlation **decays to zero** as `n` grows: `F` is *asymptotically decoupled* from the target.

This file records, abstractly and axiom-cleanly, *why decoupling kills a candidate control*.  It is the
sharper companion to `_DoorIVCoherenceSlackVacuousAtArgmax` (which handled the special case where the
candidate is unit-coherent, hence vacuous, at the target's argmax).  Here the candidate `F` is merely
**small** at the target's argmax `b*` (because it peaks elsewhere), and the obstruction is a clean
inequality, not a degeneracy:

* A uniform multiplicative control `target b ≤ C · F b` evaluated at the target's argmax `b*` **forces**
  `C · F b* ≥ target b*`; if moreover `F b* > 0`, it forces the explicit lower bound `C ≥ target b* / F b*`.
* Hence the control constant is **at least the per-instance witness ratio** `target(b*) / F(b*)`.  If this
  ratio is **unbounded across the family** `n` (which decoupling produces empirically — the target peaks
  where `F` is small), **no single absolute constant `C`** can control the target.  This is exactly the
  door-(iv) requirement that an anti-concentration bound control `M(n)` up to *absolute* constants.

This is a **refutation with mechanism** (a DEAD lever class, precisely mapped): it does **not** bound
`M(n)`; it shows that any functional decoupled from `M` at the worst frequency cannot, even up to
constants, serve as the door-(iv) control.  No CORE / cancellation / completion / moment / capacity claim.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl

open Finset

variable {ι : Type*}

/-- A *uniform multiplicative control* of `target` by `F` with constant `C`: at every index the target
is at most `C` times the candidate functional.  This is the abstract shape of "an anti-concentration /
small-ball functional `F` controls the sup-norm `M` up to an absolute constant". -/
def UniformControl (target F : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, target i ≤ C * F i

/-- A finite-frequency version of `UniformControl`: the candidate functional controls the target on the
probe support `s`.  Door-(iv) probes always enumerate a finite frequency set (for example
`b ∈ F_pˣ`), so this avoids silently strengthening a finite certificate to all ambient indices. -/
def UniformControlOn (s : Finset ι) (target F : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i ∈ s, target i ≤ C * F i

/-- **Control at the target's argmax forces a multiplicative lower bound on the constant.**  If `target`
is maximised at `b*` and `F` is *strictly positive* there, then any uniform multiplicative control of
`target` by `F` must use a constant `C ≥ target b* / F b*`.

This is the exact quantitative content of "a control functional must be large where the target is
large".  When `F` is *small* at the target's argmax (decoupling), this forces a large constant. -/
theorem const_ge_ratio_at_argmax {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hctrl : UniformControl target F C) (hFpos : 0 < F bstar) :
    target bstar / F bstar ≤ C := by
  have h : target bstar ≤ C * F bstar := hctrl bstar
  rw [div_le_iff₀ hFpos]
  exact h

/-- **A control constant is impossible once the witness ratio exceeds it.**  If `F b* > 0` and the
per-instance witness ratio `target b* / F b*` strictly exceeds a candidate constant `C`, then there is
**no** uniform multiplicative control of `target` by `F` with that constant `C`. -/
theorem not_uniformControl_of_ratio_gt {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hFpos : 0 < F bstar) (hgt : C < target bstar / F bstar) :
    ¬ UniformControl target F C := by
  intro hctrl
  exact absurd (const_ge_ratio_at_argmax hctrl hFpos) (not_le.2 hgt)

/-- **Endpoint obstruction: a nonpositive candidate at a positive target peak cannot control.**  For the
nonnegative constants relevant to absolute upper bounds, if the target is strictly positive at the
worst frequency but the proposed control functional is nonpositive there, then even pointwise control at
that one frequency is impossible.

This is the zero/nonpositive endpoint of the ratio obstruction above: probes that produce a vanishing
small-ball/window functional at the `M`-argmax are not merely forcing a large constant; they force **no
nonnegative multiplicative control at all**. -/
theorem not_uniformControl_of_nonpos_candidate_at_positive_target {target F : ι → ℝ}
    {C : ℝ} {bstar : ι} (hC : 0 ≤ C) (hFnonpos : F bstar ≤ 0)
    (htpos : 0 < target bstar) :
    ¬ UniformControl target F C := by
  intro hctrl
  have htarget_le_mul : target bstar ≤ C * F bstar := hctrl bstar
  have hmul_nonpos : C * F bstar ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hFnonpos
  have htarget_nonpos : target bstar ≤ 0 := le_trans htarget_le_mul hmul_nonpos
  exact (not_lt_of_ge htarget_nonpos) htpos

/-- **Zero endpoint packaging.**  If a nonnegative constant tries to control a strictly-positive target
peak using a candidate functional that vanishes at that peak, the control is impossible. -/
theorem not_uniformControl_of_zero_candidate_at_positive_target {target F : ι → ℝ}
    {C : ℝ} {bstar : ι} (hC : 0 ≤ C) (hFzero : F bstar = 0)
    (htpos : 0 < target bstar) :
    ¬ UniformControl target F C :=
  not_uniformControl_of_nonpos_candidate_at_positive_target hC (le_of_eq hFzero) htpos

/-- **Positive controls force positive candidate support.**  If `target ≤ C·F` with a strictly positive
constant `C`, then every frequency where the target is positive must also have positive candidate value.
Equivalently, a multiplicative door-(iv) control cannot ignore any positive target peak: the support
of `{target > 0}` is contained in the support of `{F > 0}`. -/
theorem candidate_pos_of_positive_control_at_positive_target {target F : ι → ℝ}
    {C : ℝ} {i : ι} (hCpos : 0 < C) (hctrl : UniformControl target F C)
    (htpos : 0 < target i) :
    0 < F i := by
  by_contra hnot
  exact not_uniformControl_of_nonpos_candidate_at_positive_target (le_of_lt hCpos)
    (le_of_not_gt hnot) htpos hctrl

/-- **Support-inclusion form.**  A strictly-positive multiplicative control constant forces
`{i | target i > 0} ⊆ {i | F i > 0}`.  This is the probe-facing support constraint behind the
zero/nonpositive endpoint: if a candidate functional vanishes anywhere the target is positive, it cannot
be a positive-constant control. -/
theorem positiveTarget_subset_positiveCandidate_of_positive_control {target F : ι → ℝ}
    {C : ℝ} (hCpos : 0 < C) (hctrl : UniformControl target F C) :
    {i | 0 < target i} ⊆ {i | 0 < F i} := by
  intro i hi
  exact candidate_pos_of_positive_control_at_positive_target hCpos hctrl hi

/-- **Exact ratio-envelope characterization.**  When the candidate functional is strictly positive at
every frequency, a multiplicative control `target ≤ C·F` is equivalent to bounding every pointwise
witness ratio `target i / F i` by the same constant `C`.

This packages the argmax obstruction as an exact equivalence: any door-(iv) functional with positive
values controls the target up to an absolute constant **if and only if** its whole ratio envelope is
uniformly bounded.  Therefore probe witnesses need not be literal argmaxes; any growing ratio anywhere
inside the family rules out the proposed absolute control. -/
theorem uniformControl_iff_ratio_le {target F : ι → ℝ} {C : ℝ}
    (hFpos : ∀ i, 0 < F i) :
    UniformControl target F C ↔ ∀ i, target i / F i ≤ C := by
  constructor
  · intro hctrl i
    exact const_ge_ratio_at_argmax hctrl (hFpos i)
  · intro hratio i
    have hi : target i / F i ≤ C := hratio i
    rwa [div_le_iff₀ (hFpos i)] at hi

/-- **Ratio-envelope obstruction.**  Under strict positivity of the candidate functional, one ratio
witness above `C` is exactly enough to refute a claimed `C`-control.  This is the probe-facing
contrapositive of `uniformControl_iff_ratio_le`: a single frequency with
`C < target i / F i` kills the proposed multiplicative bound, whether or not that frequency is the
argmax of either functional. -/
theorem not_uniformControl_of_exists_ratio_gt {target F : ι → ℝ} {C : ℝ}
    (hFpos : ∀ i, 0 < F i) (hwit : ∃ i, C < target i / F i) :
    ¬ UniformControl target F C := by
  intro hctrl
  obtain ⟨i, hi⟩ := hwit
  have hle : target i / F i ≤ C := (uniformControl_iff_ratio_le hFpos).1 hctrl i
  exact (not_lt_of_ge hle) hi


/-- **Finite-support monotonicity.**  Control on a larger measured support restricts to control on any
smaller support.  Thus a finite obstruction found on a sub-support cannot be repaired by adding more
ambient frequencies. -/
theorem uniformControlOn_of_subset {target F : ι → ℝ} {C : ℝ} {s t : Finset ι}
    (hst : s ⊆ t) (hctrl : UniformControlOn t target F C) :
    UniformControlOn s target F C := by
  intro i hi
  exact hctrl i (hst hi)

/-- **Finite-support obstruction propagates upward.**  If `C`-control already fails on a measured
sub-support `s`, then it also fails on every larger support `t` containing `s`.  This lets a finite
ratio/support/endpoint witness refute any claimed ambient finite-support control without proving
anything about the unmeasured frequencies. -/
theorem not_uniformControlOn_of_subset_not_control {target F : ι → ℝ} {C : ℝ}
    {s t : Finset ι} (hst : s ⊆ t) (hno : ¬ UniformControlOn s target F C) :
    ¬ UniformControlOn t target F C := by
  intro hctrl
  exact hno (uniformControlOn_of_subset hst hctrl)

/-- **Finite-support ratio-envelope characterization.**  On a finite probe support `s`, if the candidate
functional is strictly positive on `s`, then control on exactly that support is equivalent to bounding
the pointwise ratio envelope on exactly that support.

This is the probe-faithful form of the decoupling obstruction: finite computations may certify a
ratio outlier on the enumerated frequency set without making any claim about ambient frequencies that
were not part of the probe. -/
theorem uniformControlOn_iff_ratio_le_on {target F : ι → ℝ} {C : ℝ} {s : Finset ι}
    (hFpos : ∀ i ∈ s, 0 < F i) :
    UniformControlOn s target F C ↔ ∀ i ∈ s, target i / F i ≤ C := by
  constructor
  · intro hctrl i hi
    have h : target i ≤ C * F i := hctrl i hi
    rw [div_le_iff₀ (hFpos i hi)]
    exact h
  · intro hratio i hi
    have h : target i / F i ≤ C := hratio i hi
    rwa [div_le_iff₀ (hFpos i hi)] at h

/-- **Finite-support ratio witness obstruction.**  For a positive candidate on a finite probe support,
a single support frequency whose witness ratio exceeds `C` refutes `C`-control on that support.  This
is the exact finite-enumeration version used by door-(iv) small-ball/window probes. -/
theorem not_uniformControlOn_of_exists_ratio_gt_on {target F : ι → ℝ} {C : ℝ}
    {s : Finset ι} (hFpos : ∀ i ∈ s, 0 < F i)
    (hwit : ∃ i ∈ s, C < target i / F i) :
    ¬ UniformControlOn s target F C := by
  intro hctrl
  obtain ⟨i, hi, hgt⟩ := hwit
  have hle : target i / F i ≤ C := (uniformControlOn_iff_ratio_le_on hFpos).1 hctrl i hi
  exact (not_lt_of_ge hle) hgt



/-- **Finite-support nonzero positive target forces the control constant positive.**  If a finite
support control holds at a measured point where both the candidate and target are positive, then the
multiplicative constant itself must be positive.  This is the finite-probe analogue of
`control_constant_pos_of_positive_target_and_candidate`. -/
theorem controlOn_constant_pos_of_positive_target_and_candidate {target F : ι → ℝ}
    {C : ℝ} {s : Finset ι} {i : ι} (hctrl : UniformControlOn s target F C)
    (hi : i ∈ s) (hFpos : 0 < F i) (htpos : 0 < target i) :
    0 < C := by
  have hle : target i / F i ≤ C := by
    have h : target i ≤ C * F i := hctrl i hi
    rw [div_le_iff₀ hFpos]
    exact h
  have hratio_pos : 0 < target i / F i := div_pos htpos hFpos
  exact lt_of_lt_of_le hratio_pos hle

/-- **Finite-support point-ratio obstruction.**  A single measured support point with positive
candidate value and ratio above `C` refutes `C`-control on that support.  Unlike the full ratio-envelope
form, this pointwise witness does not require the candidate to be positive at every measured frequency;
it only uses positivity at the offending support point. -/
theorem not_uniformControlOn_of_point_ratio_gt_on {target F : ι → ℝ} {C : ℝ}
    {s : Finset ι} {i : ι} (hi : i ∈ s) (hFpos : 0 < F i)
    (hgt : C < target i / F i) :
    ¬ UniformControlOn s target F C := by
  intro hctrl
  have h : target i ≤ C * F i := hctrl i hi
  have hle : target i / F i ≤ C := by
    rw [div_le_iff₀ hFpos]
    exact h
  exact (not_lt_of_ge hle) hgt

/-- **Finite-support family form.**  If finite probes produce, for every candidate absolute constant
`C`, one family member `n` with a measured support frequency `bstar n ∈ s n` whose witness ratio
`target n (bstar n) / F n (bstar n)` is bigger than `C`, then no single absolute constant can control
all measured supports.  This is the exact finite-enumeration version of the unbounded-ratio no-go: the
obstruction is already present on the probed support and does not require any unmeasured ambient
frequency assumption. -/
theorem no_absolute_constantOn_of_unbounded_point_ratio {N : Type*}
    {target F : N → ι → ℝ} {s : N → Finset ι} {bstar : N → ι}
    (hmem : ∀ n, bstar n ∈ s n)
    (hFpos : ∀ n, 0 < F n (bstar n))
    (hunbdd : ∀ C : ℝ, ∃ n, C < target n (bstar n) / F n (bstar n)) :
    ∀ C : ℝ, ∃ n, ¬ UniformControlOn (s n) (target n) (F n) C := by
  intro C
  obtain ⟨n, hn⟩ := hunbdd C
  exact ⟨n, not_uniformControlOn_of_point_ratio_gt_on (hmem n) (hFpos n) hn⟩

/-- **Finite-support positive-support constraint.**  A strictly-positive control constant on a finite
probe support forces the candidate functional to be positive at every support frequency where the target
is positive.  Thus a finite probe candidate whose positive support misses a positive target point in
`s` is dead before ratio estimates matter. -/
theorem candidate_pos_of_positive_controlOn_at_positive_target {target F : ι → ℝ}
    {C : ℝ} {s : Finset ι} {i : ι} (hCpos : 0 < C)
    (hctrl : UniformControlOn s target F C) (hi : i ∈ s) (htpos : 0 < target i) :
    0 < F i := by
  by_contra hnot
  have htarget_le_mul : target i ≤ C * F i := hctrl i hi
  have hmul_nonpos : C * F i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hCpos)
    (le_of_not_gt hnot)
  have htarget_nonpos : target i ≤ 0 := le_trans htarget_le_mul hmul_nonpos
  exact (not_lt_of_ge htarget_nonpos) htpos

/-- **Finite-support support-inclusion form.**  A positive multiplicative control on `s` forces every
positive target point of `s` to lie in the candidate's positive support. -/
theorem positiveTargetOn_subset_positiveCandidate_of_positive_controlOn {target F : ι → ℝ}
    {C : ℝ} {s : Finset ι} (hCpos : 0 < C) (hctrl : UniformControlOn s target F C) :
    {i | i ∈ s ∧ 0 < target i} ⊆ {i | 0 < F i} := by
  intro i hi
  exact candidate_pos_of_positive_controlOn_at_positive_target hCpos hctrl hi.1 hi.2

/-- **Finite-support nonpositive endpoint.**  For nonnegative constants, a candidate functional that is
nonpositive at a measured support frequency where the target is strictly positive cannot even control
the target on the finite probe support `s`.

This is the finite-enumeration endpoint companion to the ratio-envelope obstruction: if a window,
small-ball, or coherence statistic vanishes (or goes negative after centering) at a positive target
frequency inside the enumerated support, the proposed `C`-control is dead on the measured data itself,
without any ambient-frequency claim. -/
theorem not_uniformControlOn_of_nonpos_candidate_at_positive_target {target F : ι → ℝ}
    {C : ℝ} {s : Finset ι} {i : ι} (hC : 0 ≤ C) (hi : i ∈ s)
    (hFnonpos : F i ≤ 0) (htpos : 0 < target i) :
    ¬ UniformControlOn s target F C := by
  intro hctrl
  have htarget_le_mul : target i ≤ C * F i := hctrl i hi
  have hmul_nonpos : C * F i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hFnonpos
  have htarget_nonpos : target i ≤ 0 := le_trans htarget_le_mul hmul_nonpos
  exact (not_lt_of_ge htarget_nonpos) htpos

/-- **Finite-support zero endpoint.**  A nonnegative constant cannot control a positive measured target
point through a candidate functional that is zero at that same support point. -/
theorem not_uniformControlOn_of_zero_candidate_at_positive_target {target F : ι → ℝ}
    {C : ℝ} {s : Finset ι} {i : ι} (hC : 0 ≤ C) (hi : i ∈ s)
    (hFzero : F i = 0) (htpos : 0 < target i) :
    ¬ UniformControlOn s target F C :=
  not_uniformControlOn_of_nonpos_candidate_at_positive_target hC hi (le_of_eq hFzero) htpos

/-- **A nonzero positive target forces the control constant itself to be positive.**  If the
candidate is positive at some frequency and the target is positive there, then any multiplicative
control `target ≤ C·F` must have `C > 0`.  Thus the `C > 0` hypotheses in the support lemmas are not
extra structure in the nontrivial door-(iv) regime; they are forced by any successful control of a
positive target through a positive candidate. -/
theorem control_constant_pos_of_positive_target_and_candidate {target F : ι → ℝ}
    {C : ℝ} {i : ι} (hctrl : UniformControl target F C)
    (hFpos : 0 < F i) (htpos : 0 < target i) :
    0 < C := by
  have hratio : target i / F i ≤ C := const_ge_ratio_at_argmax hctrl hFpos
  have hratio_pos : 0 < target i / F i := div_pos htpos hFpos
  exact lt_of_lt_of_le hratio_pos hratio

/-- **Family form: an unbounded witness ratio rules out every absolute constant.**  Suppose for each
member `n` of a family we have a target `target n`, a candidate functional `F n`, a worst frequency
`bstar n` where `F n (bstar n) > 0`, and the per-`n` witness ratio
`r n := target n (bstar n) / (F n) (bstar n)`.  If the family of ratios is **unbounded above** (for
every candidate constant `C` there is an `n` with `C < r n`), then **no single absolute constant `C`**
uniformly controls every member: for each `C` some member has no `C`-control.

This is the door-(iv) no-go: a functional asymptotically decoupled from `M` at the worst frequency
cannot control `M` up to *absolute* constants. -/
theorem no_absolute_constant_of_unbounded_ratio {N : Type*}
    {target F : N → ι → ℝ} {bstar : N → ι}
    (hFpos : ∀ n, 0 < F n (bstar n))
    (hunbdd : ∀ C : ℝ, ∃ n, C < target n (bstar n) / F n (bstar n)) :
    ∀ C : ℝ, ∃ n, ¬ UniformControl (target n) (F n) C := by
  intro C
  obtain ⟨n, hn⟩ := hunbdd C
  exact ⟨n, not_uniformControl_of_ratio_gt (hFpos n) hn⟩

/-- **Finite-support form matching the probe.**  Over a nonempty finite frequency set `s`, with
`bstar = argmax_{b∈s} target` carrying positive target value and strictly-positive candidate value, the
control constant is at least the witness ratio.  Here `target = |η|` (the sup-norm mass), `F = C_worst`
(the small-ball functional), `bstar` the empirical argmax, all over `s ⊆ F_p*`. -/
theorem const_ge_ratio_at_finsetArgmax {target F : ι → ℝ} {C : ℝ}
    {s : Finset ι} {bstar : ι} (_hbs : bstar ∈ s)
    (_hmax : ∀ i ∈ s, target i ≤ target bstar)
    (hFpos : 0 < F bstar) (hctrl : UniformControl target F C) :
    target bstar / F bstar ≤ C :=
  const_ge_ratio_at_argmax hctrl hFpos

/-- **The control constant cannot be smaller than the observed worst ratio.**  Contrapositive packaging
for the probe: if a proposal claims an absolute constant `C` strictly below the *measured* worst-frequency
ratio `target b* / F b*` (with `F b* > 0`), the claim is false — there is no such control. -/
theorem no_control_below_measured_ratio {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hFpos : 0 < F bstar) (hbelow : C < target bstar / F bstar) :
    ¬ UniformControl target F C :=
  not_uniformControl_of_ratio_gt hFpos hbelow

end ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl
