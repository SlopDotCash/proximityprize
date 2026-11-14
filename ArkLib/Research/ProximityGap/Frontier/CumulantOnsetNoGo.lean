/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The CUMULANT ONSET NO-GO for the δ* deep-moment wall (Issue #407, route [cumulant])

## The route and the question

The prize floor is `B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b·x)`. The moment method bounds `B`
via the raw `2r`-th moment `M_{2r} = Σ_{b≠0}‖η_b‖^{2r} = p·E_r − n^{2r}` (`E_r` the char-`p` additive
energy of `μ_n`). The **deep-moment / Betti wall** (`CharSumMomentDeepWall.lean`): `E_r` is at its
clean char-0 value `(2r−1)‼·n^r` only for `r ≤ r₀ ≈ ⌈log_n p⌉`; past `r₀` the **mod-`q` defect**
`E_r^{F_q} − E_r^{ℂ}` (short `±1` relations of `2^μ`-th roots vanishing mod `𝔮`) overtakes and the
raw moment blows up. In the prize regime (index `m = (p−1)/n ≈ 2^128` held constant as the FFT
domain `n → ∞`, so `log_n p → 1⁺`) this caps the reliable depth at `r₀ = 2`.

The route asks: do the **connected (classical) cumulants** `κ_r` of the random variable
`X = |η_b|²` (`b` uniform over `F_p^×`) — being *signed* partition-Möbius combinations of the raw
moments `μ_r = E[X^r]` — exhibit cancellation that the raw moment `μ_r` misses, so that a
cumulant-based transport reaches **deeper** than `r₀`?

## The answer (this file): NO — the cumulant inherits the defect AT its onset order, exactly.

The classical cumulants satisfy the recurrence
  `κ_r = μ_r − Σ_{k=1}^{r−1} C(r−1, k−1)·κ_k·μ_{r−k}`,  i.e.  with `j = k`,  `s = r − 1`,
  `κ_{s+1} = μ_{s+1} − Σ_{k ∈ range s} C(s, k)·κ_{k+1}·μ_{s−k}`.
The correction `Σ_{k ∈ range s} C(s,k)·κ_{k+1}·μ_{s−k}` depends **only on strictly-lower moments**
`μ_1, …, μ_s` (and their cumulants, which in turn depend only on lower moments). At the *onset* order
`r₀` — the FIRST order at which the `F_q` moment deviates from its char-0 value — every lower moment
`μ_1, …, μ_{r₀−1}` is still defect-free (equal to its char-0 value). Hence the entire correction
polynomial is identical in the two worlds, and

  **`κ_{r₀}^{F_q} − κ_{r₀}^{ℂ} = μ_{r₀}^{F_q} − μ_{r₀}^{ℂ}` — the cumulant defect EQUALS the raw
  moment defect at the onset order, with NO cancellation.**

This is `cumulant_defect_eq_moment_defect_at_onset` below, proven axiom-clean over `ℚ`. We phrase the
recurrence as a *hypothesis* `IsCumulantSeq` (rather than a `termination_by` definition) so the result
covers ANY cumulant flavor whose moment→cumulant map has this "leading `μ_r` + correction in strictly
lower moments" shape (classical, free, Boolean, monotone — all do; the only difference is the weights
on the lower-moment products, which the proof never inspects).

Numerically (`scripts/probes/_wf407_cumulant_{connected,onset,prize_regime,flavor_independent}.py`,
EXACT integer/rational arithmetic): the ratio `|κ_{r₀}^{def}| / |μ_{r₀}^{def}|` is **`1.000000` at
EVERY onset order**, for classical, free, AND Boolean cumulants, across `n ∈ {4,8,16}` and all swept
`p` (onset `r₀ = ⌈log_n p⌉`). In the held-index prize regime `r₀ → 2` (probe `_prize_regime`).

## Honest scope

This is a **NO-GO for the cumulant route**, not a closure of the prize. It rigorously explains *why*
cumulants cannot beat `r = 2`: the leading (disconnected/Gaussian) mass that cumulants cancel is
*already* defect-free in the lower moments; the cumulant's signed combination only touches lower
moments, which carry no defect at the onset, so it cannot subtract the onset defect — it reproduces
it. The open core (bounding the onset defect itself = the mod-`q` short-relation count / the
off-diagonal √-cancellation of the `CDD` conjecture) is untouched and remains the wall.

## References
- `CharSumMomentDeepWall.lean` (the `r₀ ≈ 2 log_n p` Betti wall this route tried to cross)
- `docs/kb/deltastar-cumulant-not-moment-2026-06-13.md`, `...-CDD-cumulant-diagonal-dominance-...`
- memory `arklib-407-habegger-archimedean-defect-split` (the `κ_r = kA + kD` split)
- [ABF26] ePrint 2026/680 (the Proximity Prize). Issue #407.
-/

namespace ArkLib.ProximityGap.CumulantOnsetNoGo

open Finset

/-- A real-valued **weight scheme** `w s k` for a moment→cumulant recurrence: at order `s + 1` the
cumulant is `κ_{s+1} = μ_{s+1} − Σ_{k ∈ range s} w s k · κ_{k+1} · μ_{s-k}`. For classical cumulants
`w s k = C(s, k)`; for free/Boolean/monotone cumulants the weights differ but the *shape* (leading
`μ_{s+1}` plus a correction built from strictly-lower-index cumulants `κ_{k+1}` (`k < s`, so
`k+1 ≤ s`) and moments `μ_{s-k}` (`s-k ≤ s`)) is identical. The onset proof inspects only the shape,
never the weights, so it applies to every flavor. -/
abbrev Weight := ℕ → ℕ → ℚ

/-- `IsCumulantSeq w μ κ` says `κ` is the cumulant sequence of the moment sequence `μ` under the
weight scheme `w`: `κ 0 = 0` and `κ (s+1) = μ (s+1) − Σ_{k ∈ range s} w s k · κ (k+1) · μ (s-k)`.
This is the abstract recurrence; both the classical and free cumulant sequences satisfy it (with
their respective `w`). -/
def IsCumulantSeq (w : Weight) (μ κ : ℕ → ℚ) : Prop :=
  κ 0 = 0 ∧
    ∀ s : ℕ, κ (s + 1) =
      μ (s + 1) - ∑ k ∈ Finset.range s, w s k * κ (k + 1) * μ (s - k)

/-- **Two moment sequences agreeing on all indices `< r₀` have identical cumulants on indices `< r₀`**
(for the SAME weight scheme `w`). Proof by strong induction: `κ j` for `j < r₀` is built, via the
recurrence, entirely from `μ`-values and `κ`-values of strictly smaller index. -/
theorem cumulant_eq_of_moments_eq_below {w : Weight} {μ ν κμ κν : ℕ → ℚ}
    (hμ : IsCumulantSeq w μ κμ) (hν : IsCumulantSeq w ν κν) (r₀ : ℕ)
    (hmom : ∀ j, j < r₀ → μ j = ν j) :
    ∀ j, j < r₀ → κμ j = κν j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    match j with
    | 0 => rw [hμ.1, hν.1]
    | (s + 1) =>
      rw [hμ.2 s, hν.2 s]
      have hμs1 : μ (s + 1) = ν (s + 1) := hmom (s + 1) hj
      rw [hμs1]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hk1 : k + 1 < r₀ := by omega
      have hsk : s - k < r₀ := by omega
      rw [ih (k + 1) (by omega) hk1, hmom (s - k) hsk]

/-- **THE CUMULANT ONSET NO-GO (main theorem).** Let `μ` (the `F_q` moments of `X = |η_b|²`) and
`ν` (the char-0 / Gaussian-baseline moments) agree on every order strictly below the **defect onset**
`r₀` (the first order at which they differ), and let `κμ, κν` be their cumulant sequences under a
common weight scheme `w`. Then the cumulant *defect* at `r₀` equals the raw moment *defect* at `r₀`,
exactly:

  `κμ r₀ − κν r₀ = μ r₀ − ν r₀`.

At the onset order the connected cumulant reproduces the mod-`q` moment defect with NO cancellation;
the cumulant route gains **zero** moment depth past the Betti wall. (Matches the machine-checked
ratio `1.000000` in `_wf407_cumulant_onset.py`, for classical, free, and Boolean weights alike.) -/
theorem cumulant_defect_eq_moment_defect_at_onset {w : Weight} {μ ν κμ κν : ℕ → ℚ}
    (hμ : IsCumulantSeq w μ κμ) (hν : IsCumulantSeq w ν κν) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (hbelow : ∀ j, j < r₀ → μ j = ν j) :
    κμ r₀ - κν r₀ = μ r₀ - ν r₀ := by
  obtain ⟨s, rfl⟩ : ∃ s, r₀ = s + 1 := ⟨r₀ - 1, by omega⟩
  rw [hμ.2 s, hν.2 s]
  -- the two correction sums are EQUAL (they depend only on moments/cumulants of index ≤ s < s+1)
  have hcorr :
      (∑ k ∈ Finset.range s, w s k * κμ (k + 1) * μ (s - k))
        = ∑ k ∈ Finset.range s, w s k * κν (k + 1) * ν (s - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hk1 : k + 1 < s + 1 := by omega
    have hsk : s - k < s + 1 := by omega
    have hcum : κμ (k + 1) = κν (k + 1) :=
      cumulant_eq_of_moments_eq_below hμ hν (s + 1) hbelow (k + 1) hk1
    have hmom : μ (s - k) = ν (s - k) := hbelow (s - k) hsk
    rw [hcum, hmom]
  rw [hcorr]
  ring

/-- **Corollary (the route verdict in one line).** Under the onset hypothesis, if the raw moment has
a genuine defect at the onset (`μ r₀ ≠ ν r₀`), then so does the cumulant, and by the *same* amount.
There is no choice of lower moments for which the cumulant defect is smaller than the moment defect:
it is forced equal. Hence a cumulant transport `B ≤ (q·κ_r)^{1/2r}`-type argument inherits the wall at
the identical depth `r₀`. -/
theorem cumulant_no_escape_at_onset {w : Weight} {μ ν κμ κν : ℕ → ℚ}
    (hμ : IsCumulantSeq w μ κμ) (hν : IsCumulantSeq w ν κν) (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (hbelow : ∀ j, j < r₀ → μ j = ν j) (hdefect : μ r₀ ≠ ν r₀) :
    κμ r₀ ≠ κν r₀ ∧ κμ r₀ - κν r₀ = μ r₀ - ν r₀ := by
  have h := cumulant_defect_eq_moment_defect_at_onset hμ hν r₀ hr₀ hbelow
  refine ⟨?_, h⟩
  intro hcontra
  rw [hcontra, sub_self] at h
  exact hdefect (sub_eq_zero.mp h.symm)

/-- **Classical cumulants are an instance** (sanity check that `IsCumulantSeq` is inhabited with the
real moment→cumulant map): the weight scheme `w s k = C(s, k)` gives the classical cumulants. The
explicit classical sequence is `κ` defined by the same recurrence; here we just record that any `κ`
built from `μ` by that recurrence satisfies `IsCumulantSeq (fun s k => C(s,k)) μ κ` definitionally. -/
theorem isCumulantSeq_classical (μ κ : ℕ → ℚ)
    (h0 : κ 0 = 0)
    (hrec : ∀ s, κ (s + 1) =
      μ (s + 1) - ∑ k ∈ Finset.range s, (Nat.choose s k : ℚ) * κ (k + 1) * μ (s - k)) :
    IsCumulantSeq (fun s k => (Nat.choose s k : ℚ)) μ κ :=
  ⟨h0, hrec⟩

end ArkLib.ProximityGap.CumulantOnsetNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CumulantOnsetNoGo.cumulant_eq_of_moments_eq_below
#print axioms ArkLib.ProximityGap.CumulantOnsetNoGo.cumulant_defect_eq_moment_defect_at_onset
#print axioms ArkLib.ProximityGap.CumulantOnsetNoGo.cumulant_no_escape_at_onset
#print axioms ArkLib.ProximityGap.CumulantOnsetNoGo.isCumulantSeq_classical
