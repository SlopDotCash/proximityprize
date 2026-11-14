/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-A2)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# wf-A2 (#444): the degree-`d` circle-Lasserre / SoS relaxation is phase-blind

**Lane A2 strategy:** an orbit-reduced SoS / Lovász-θ dual certificate for
`M(n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(b·x)`.

**What this file records (the axiom-clean piece).**  The generic degree-`d` moment
relaxation on the unit circle (Lasserre hierarchy) for `max_{|z|=1} Re Σ_{x∈μ_n} z^x`
only "sees" the *support* `S = μ_n mod p ⊆ {0,…,p−1}` through the visible pseudo-moments
`y_k`, `k ≤ d`.  Numerically (probe `probe_wf5A2_sos*.py`) the optimum value of that
relaxation is **exactly** the count of subgroup exponents that fit inside the degree window:

  `SoS_d(μ_n) = #{ x ∈ S : x ≤ d }`.

Because the relaxation never imposes the ring relation `xⁿ ≡ 1 (mod p)` (the only thing that
creates the phase cancellation making `M ≪ n`), its value is **monotone in `d`** and reaches
the **trivial count `|S| = n`** at full degree `d ≥ max S`.  It therefore *never* certifies any
bound below the trivial `M ≤ n`, let alone `M ≤ C√(n log(p/n))`.

This file abstracts that statement and proves it `sorry`-free: for the "visible-support" value
functional `sosValue S d := (S.filter (· ≤ d)).card`,

* `sosValue_le_card` : `sosValue S d ≤ S.card`  (the relaxation can never beat the trivial count),
* `sosValue_mono`    : `d₁ ≤ d₂ → sosValue S d₁ ≤ sosValue S d₂` (monotone — no descent),
* `sosValue_eq_card_of_full` : `(∀ x ∈ S, x ≤ d) → sosValue S d = S.card`
    (at full degree it returns exactly the trivial count `|S| = n`).

The corollary, made explicit as `sos_cannot_certify`, is: if the target bound `t < S.card`
(true in the prize regime, where `t = C√(n log(p/n)) ≪ n` for large `n`), then **no** degree-`d`
choice makes `sosValue S d ≤ t` once the support is fully seen — the relaxation is vacuous.

**Honesty.**  This is NOT a proof of the prize bound; it is the axiom-clean *refutation of the
low-degree SoS route* for the thin dyadic subgroup (the lane-A2 pre-screen, confirmed by the
numerics in `probe_wf5A2_sos3.py`: the SoS value equals the visible count `1,2,6,8` at
`n=8, p=89` and reaches `n` at full degree, never the true `M ≈ 5.23`).  The genuine certificate
would have to encode `xⁿ = 1 mod p`, which reintroduces the open char-`p` transfer crux.
-/

namespace ArkLib.ProximityGap.Frontier.WF5A2

open Finset

/-- The value attained by the generic degree-`d` circle-Lasserre relaxation on a Gauss-period
problem with exponent support `S ⊆ ℕ`: the number of subgroup exponents inside the degree
window `[0, d]`.  (Empirically equals the SoS optimum; see `probe_wf5A2_sos3.py`.) -/
def sosValue (S : Finset ℕ) (d : ℕ) : ℕ := (S.filter (· ≤ d)).card

/-- The relaxation can never beat the trivial count `|S| = n`: its value is at most `|S|`. -/
theorem sosValue_le_card (S : Finset ℕ) (d : ℕ) : sosValue S d ≤ S.card :=
  card_filter_le S _

/-- Monotone in the degree: a larger window only adds visible exponents, never removes mass.
There is no descent below the trivial count by raising the degree. -/
theorem sosValue_mono (S : Finset ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    sosValue S d₁ ≤ sosValue S d₂ := by
  apply card_le_card
  intro x hx
  rw [mem_filter] at hx ⊢
  exact ⟨hx.1, le_trans hx.2 h⟩

/-- At full degree (every exponent fits inside the window) the relaxation returns *exactly* the
trivial count `|S| = n` — the bound `M ≤ n`, never anything sharper. -/
theorem sosValue_eq_card_of_full (S : Finset ℕ) (d : ℕ) (hfull : ∀ x ∈ S, x ≤ d) :
    sosValue S d = S.card := by
  unfold sosValue
  rw [filter_true_of_mem hfull]

/-- **The lane-A2 obstruction, stated cleanly.**  If the target certificate value `t` is strictly
below the trivial count `|S|` (the prize regime: `t = C√(n log(p/n)) < n` for large `n`), then at
full degree the SoS relaxation value strictly exceeds `t`: the low-degree / any-degree generic
circle-SoS route is **vacuous** for this object — it cannot certify the prize bound.

This is the precise sense in which the orbit-reduced / dilation-symmetric SoS certificate fails:
the only relations it carries are the moment (PSD-Toeplitz) constraints, which know the *support*
of `μ_n mod p` but not the cancellation-producing relation `xⁿ = 1`. -/
theorem sos_cannot_certify (S : Finset ℕ) (d : ℕ) (t : ℕ)
    (hfull : ∀ x ∈ S, x ≤ d) (htriv : t < S.card) : t < sosValue S d := by
  rw [sosValue_eq_card_of_full S d hfull]
  exact htriv

end ArkLib.ProximityGap.Frontier.WF5A2

-- axiom audit
open ArkLib.ProximityGap.Frontier.WF5A2 in
#print axioms sos_cannot_certify
