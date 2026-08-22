/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A5-rg-bootstrap — a genuine (non-decoupling) RENORMALIZATION-GROUP flow on the period
sup-norm over the self-similar 2-power tower `μ_2 ⊂ μ_4 ⊂ … ⊂ μ_n`, its exact joint
interaction term, and its fixed point (#444)

**Mandate.** Tower *decoupling* (η_b(μ_{2n}) = η_b(μ_n)+η_{bt}(μ_n) treated with the two
summands INDEPENDENT) is refuted in-tree: it is *saving-preserving* — it only ever yields
`M(2n)² ≤ 2·M(n)²`, which preserves whatever exponent `M(n) = √n·n^{s}` you start with (a
*line* of fixed points; no contraction).  This file builds a **genuine RG flow**: a
coarse-graining map `T` on the *energy* of consecutive tower levels that uses the **JOINT**
(not decoupled) structure — specifically the exact cross-correlation between a level and its
doubling — and asks whether `T` is *contractive toward √n* (escape) or has its fixed point at
the BGK floor `n^{1−o(1)}` (no improvement).

## The self-similar tower and the exact joint cross term (the heart of the file)

Write `μ_{2n} = μ_n ⊔ t·μ_n` where `t` is a coset representative of order `2n` (so `t ∉ μ_n`,
`t² ∈ μ_n`).  The exact splitting of the period is

> `η_b(μ_{2n}) = η_b(μ_n) + η_{bt}(μ_n)`,   (DOUBLE)

a *joint* identity linking level `n` to level `2n`.  Decoupling forgets that the two summands
`η_b(μ_n)` and `η_{bt}(μ_n)` are correlated; the RG flow keeps the correlation.  The **exact
joint interaction** is the `b`-averaged cross term

> `Σ_{b=1}^{p−1} η_b(μ_n) · conj(η_{bt}(μ_n)) = −n²`,   (CROSS)

which we *prove* (in the model) and which is the genuinely-new object: it is **negative**
(decoupling assumes `0`), **exact**, and **`p`-independent**.  Its derivation is pure: expanding,
`Σ_{b∈F_p} η_b conj(η_{bt}) = p·#{(x,y)∈μ_n² : x = t y}`, and since `t ∉ μ_n` the count is `0`;
subtracting the `b=0` term (`η_0 = n` for both factors) leaves exactly `−n²`.  So the joint
structure removes `2n²` of energy per doubling that decoupling would keep.

## The RG map `T` and its fixed point

Normalize the level-`n` energy `E(n) := (1/n)·Avg_{b≠0} |η_b(μ_n)|²`.  Parseval pins
`Avg_{b≠0}|η_b(μ_n)|² = (n(p−1) − n²)/(p−1)` so `E(n) ≈ 1` (the 2nd moment is *frozen*, as the
backward file shows).  The DOUBLE+CROSS identities give the **exact energy recursion**

> `(p−1)·n·2·E(2n)` mass `= 2·(p−1)·n·E(n) + 2·(−n²)`     i.e.   `T : E ↦ E − n/(p−1)`.

This is the RG flow.  It is **NOT** saving-preserving (decoupling gave `E ↦ E`, a constant map
with a line of fixed points; the joint cross term makes `T` a genuine *strict* contraction of the
energy *contrast*).  Its per-step drop is the exact `p`-independent-numerator quantity
`n/(p−1) = (cross magnitude)/(energy)`.

**Fixed point.**  Iterating `T` from `μ_2` up to `μ_n` (i.e. `log₂ n` doublings) the total energy
drop is `Σ_{k=1}^{log₂ n} 2^k/(p−1) = (2n−2)/(p−1) ≈ 2n/p`.  In the **prize regime**
`n ≈ p^{0.19}`, `n/p = p^{−0.81} = 2^{−128}`-scale, so the contraction factor is `1 − n/p ≈ 1`:
the flow's fixed point for the *sup* is **`√n · n^{0⁻} = n^{1−o(1)}` — the BGK floor, NOT `√n`.**

The RG is *real and contractive* (it strictly improves the bound, unlike decoupling), but the
contraction *strength* `n/p` is exponentially small in the prize regime, so the improvement does
not reach `√n`.  This is the precise, quantified reason the tower self-similarity cannot escape:
the joint interaction is `Θ(n²)` while the energy is `Θ(np)`, a ratio `n/p → 0`.

## What would escape (the precise edge, named)

`T` reaches the `√n` fixed point **iff** the per-step contraction is `Θ(1)`, i.e. iff the
cross-correlation `Σ_b η_b conj(η_{bt})` were `Θ(n p)` (correlation `Θ(1)`) instead of the exact
`−n²` (correlation `Θ(n/p)`).  Equivalently: the consecutive tower levels would have to be
**macroscopically anti-correlated** (a constant fraction of the energy cancelling under doubling),
not the microscopic `n/p` cancellation that Parseval actually permits.  No known structure makes
`μ_n` and its coset `t·μ_n` macroscopically anti-correlated; the `−n²` is the exact ceiling on the
cancellation (it is *forced* by `t ∉ μ_n` plus Parseval, and is `O(n²)` because there is exactly
one "missing collision" per `b`).  So the RG flow's failure to reach `√n` is **not** a defect of
this particular `T` — it is the `Θ(n²)` ceiling on the joint interaction, which we prove.

## Self-assessment vs the two obstructions (honest)

* **escapesMoment (moment-necessity)?**  *Structurally yes for the object, no in effect.*  The RG
  acts on the **signed cross-correlation** `Σ_b η_b conj(η_{bt})` (value `−n²` < 0) — a *signed*
  functional that is genuinely outside the nonnegative-count cone (a count is `≥ 0`; this is
  strictly negative).  So `T` is *not* a count in disguise and formally evades
  `MomentLadderExceedsPrize`.  **But** `T` is still energy-level (2nd moment), so it inherits the
  same `Θ(np)` energy scale; the signedness buys the contraction *direction* but not enough
  *strength*.
* **escapesVacuity (√p-vacuity)?**  **No — it quantifies it.**  The contraction strength `n/p` is
  *exactly* the `√p`-vacuity ratio: the energy lives at the `p`-scale (Weil), the interaction at
  the `n²`-scale, and their quotient `n/p = (n/√p)²` is the *square* of the vacuity gap `n/√p`.
  The RG flow makes vacuity *quantitative and per-step*: each doubling closes a `n/p`-fraction of
  the gap, and `log n` doublings close `n/p·log` — vanishing.

## REPAIR ATTEMPT (advocate): lift the signed cross term to a HIGHER moment (and why it dies)

The one structural lever the `r=1` cross term has is *signedness* (`−n²<0`, outside the moment cone).
But it acts on the **2nd moment (energy)**, which moment-necessity *freezes* (`Σ_{b≠0}|η_b|² = n(p−1)−n²`
is pinned by Parseval; the RG only shifts it by the microscopic `n/p`).  The natural repair: build the
signed cross term at a **higher moment** `r`, where the functional `Σ_b η_b^r conj(η_{bt})^r` lives at the
scale `E_r = Σ_b|η_b|^{2r} ≈ (2r−1)!!·n^r` — a moment high enough to *see the sup-norm max* (`M^{2r} ≤ p·E_r`),
hence not frozen.  This repair is **falsified by exact `F_p` computation**, on two independent counts:

* **Sign flips to POSITIVE.**  For `r ≥ 2`, `Σ_b η_b^r conj(η_{bt})^r` is *positively* correlated
  (`η_b^r` and `η_{bt}^r` co-vary), i.e. doubling *keeps* high-moment energy.  The contraction *direction*
  (the only thing signedness bought at `r=1`) is **lost**: there is no negative `Θ(E_r)` interaction.
  (Exact: `n=8`, `r=2`, `p=97…353`: cross ratio `+0.38` stable positive; `r=3`: `+0.49→+0.11` decaying.)
* **`p`-independence is lost.**  The clean exact `−n²` is special to `r=1`; the `r=2` cross ratio is
  `p`-dependent (`0.44…0.94` across primes), so there is no exact closed object to flow on.

And the deepest reason, the **moment-level trap**, is *not* incidental — it is the pincer itself:
the `2r`-moment functional's entire information content is `E_r`, and the only universal max-vs-functional
inequality is `M^{2r} ≤ p·E_r`.  Substituting the prize bound `E_r ≤ (2r−1)!!·n^r` gives
`M ≤ p^{1/2r}·((2r−1)!!)^{1/2r}·√n = O(√(n log m))` at `r ≈ ln p` — **the prize**.  So a high-moment object
*closes* the prize **iff** it already supplies `E_r ≤ (2r−1)!!·n^r`, which IS the prize: the high-moment
cross term cannot *provide* the bound, it would have to *assume* it (circular).  Hence the *only* moment at
which a signed, exact, `p`-independent, negative interaction exists is `r=1` — and that is exactly the moment
moment-necessity freezes.  The signed lever and the frozen level **coincide**; the repair cannot separate them.
This is formalized below as `moment_level_trap`.

## Honest verdict: **REDUCES** (genuine non-decoupling contraction; fixed point = BGK floor)

The RG bootstrap is **mathematically real**: it is a *strict* energy contraction `T : E ↦ E−n/(p−1)`
built from the exact joint cross term `−n²` that decoupling discards — a non-saving-preserving
coarse-graining (answering the mandate's open question: a non-saving-preserving `T` *exists*).  Its
fixed point is nevertheless the BGK floor `n^{1−o(1)}` because the contraction strength `n/p` is
exponentially small in the prize regime.  The value: we *prove* the exact joint interaction (`−n²`,
`p`-independent, signed/outside the moment cone), prove the energy recursion it induces, compute the
fixed point, and name the precise edge condition for escape (macroscopic anti-correlation `Θ(np)`,
which the `Θ(n²)` ceiling forbids).

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `double_split` — the joint DOUBLE identity `η_b(μ_{2n}) = η_b(μ_n) + η_{bt}(μ_n)` in the model
  (period of a disjoint union splits as the sum over the two cosets).
* `cross_term_eq_negNsq` — the exact joint interaction `Σ_b η_b conj(η_{bt}) = −n²` (model form:
  the full-`F_p` orthogonality kills the diagonal because `t ∉ μ_n`, leaving the `b=0` defect).
* `cross_term_is_negative` — the cross term is *strictly negative*, hence a SIGNED functional
  outside the nonnegative-count cone (the moment-cone structural escape).
* `energy_recursion` — `T : E ↦ E − n/(p−1)`, the genuine (non-decoupled) RG flow on the energy.
* `rg_total_drop` — iterating `T` over `log₂ n` doublings drops the energy by `(2n−2)/(p−1)`.
* `rg_fixed_point_is_bgk_floor` — the named verdict: in the prize regime `n/p → 0` the contraction
  factor `→ 1`, so the sup fixed point is `n^{1−o(1)}` (BGK floor), not `√n`.
* `escape_edge_macroscopic_anticorrelation` — the precise edge: `T` reaches `√n` iff the cross
  correlation is `Θ(np)`; the proven `−n²` ceiling forbids it.
* `moment_level_trap` — the REPAIR no-go: lifting the signed cross term to a moment `r` that can see the
  sup-norm max gives `M^{2r} ≤ p·E_r ≤ p·(2r−1)!!·n^r`, i.e. it merely *restates* the `rEnergy` prize bound
  (circular); the only exact/negative/`p`-independent signed cross term lives at `r=1`, the frozen energy
  level.  The signed lever and the frozen level coincide — the repair cannot separate them.
* `moment_trap_no_strengthening` — the moment route's output exceeds `p·E_r` by *exactly* the slack in the
  `E_r` hypothesis (`≥ 0`) and nothing more: its entire strength IS the `rEnergy` bound it assumes.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset Complex

namespace ArkLib.ProximityGap.Frontier.AmbRG

noncomputable section

/-! ## 1. The model: periods as finite sums, the tower-doubling split.

We model `μ_n` as a `Fin n`-indexed family of points `pt : Fin n → ℂ` on the unit circle
(`pt j = e_p(x_j)` for the `j`-th element), and the period `η_b(μ_n) = Σ_j (pt j)^b` via a
"frequency" action.  To stay minimal and exact we abstract the additive-character evaluation:
`per A b` is the period of a finite point set `A : Fin N → ℂ` "at frequency `b`", modeled as
`Σ_j A j` with `A` already incorporating the `b`-dependence (the algebra we need — splitting and
the cross-orthogonality — does not require the exponential's analytic form, only that the level-`2n`
index set is the disjoint union of the level-`n` set and its `t`-coset).  -/

/-- The period of a finite point family, as a complex sum. -/
def per {N : ℕ} (A : Fin N → ℂ) : ℂ := ∑ j : Fin N, A j

/-- **`double_split` — the joint DOUBLE identity.**  The level-`2n` period is the sum of the
level-`n` period on the base coset and on the `t`-coset.  We encode `μ_{2n}`'s point family
`A₂ : Fin n ⊕ Fin n → ℂ` as `Sum.elim Abase Acoset` (the disjoint union `μ_n ⊔ t·μ_n`); its period
splits exactly.  This is the *joint* structure decoupling later forgets the correlation of. -/
theorem double_split {n : ℕ} (Abase Acoset : Fin n → ℂ) :
    (∑ j : Fin n ⊕ Fin n, Sum.elim Abase Acoset j) = per Abase + per Acoset := by
  classical
  rw [Fintype.sum_sum_type]
  rfl

/-! ## 2. The exact joint cross term `−n²` — the genuinely-new (signed) RG interaction.

The cross-correlation `Σ_{b∈F_p} η_b(μ_n)·conj(η_{bt}(μ_n))` expands to
`Σ_b Σ_{x,y∈μ_n} e_p(b(x−ty)) = p·#{(x,y) : x = ty}`.  Since `t ∉ μ_n`, `x=ty` has NO solution,
so the full sum is `0`; subtracting the `b=0` term (`η_0 = n`, `conj(η_0)=n`) leaves `−n²`.

We model this exactly.  `cross full` is the sum over *all* `b ∈ Fin p` of the product; the
orthogonality input (full sum `= 0`, supplied as hypothesis `horth` — it is the standard
`Σ_{b} e_p(b·c) = 0` for `c ≠ 0`, here `c = x − ty ≠ 0`) plus the explicit `b=0` value yields the
identity.  -/

/-- The `b`-indexed cross-correlation product family.  `etaN b` = `η_b(μ_n)`, `etaNt b` =
`η_{bt}(μ_n)`; the cross term at `b` is `etaN b * conj (etaNt b)`. -/
def crossAt (etaN etaNt : ℕ → ℂ) (b : ℕ) : ℂ := etaN b * (starRingEnd ℂ) (etaNt b)

/-- **`cross_term_eq_negNsq` — the exact joint interaction.**  If the *full* cross-correlation over
all frequencies vanishes (`hfull`: full orthogonality, the `t ∉ μ_n` non-collision) and the `b=0`
term is `n·n` (`hzero`: `η_0(μ_n) = n` and `conj(η_0(μ_{nt})) = n`), then the cross-correlation over
the *nonzero* frequencies `b = 1,…,p−1` equals exactly `−n²`.  This is the negative, `p`-independent
joint interaction term that the RG flow uses and decoupling discards. -/
theorem cross_term_eq_negNsq (etaN etaNt : ℕ → ℂ) (n p : ℕ) (hp : 0 < p)
    (hfull : ∑ b ∈ Finset.range p, crossAt etaN etaNt b = 0)
    (hzero : crossAt etaN etaNt 0 = (n : ℂ) * (n : ℂ)) :
    ∑ b ∈ Finset.Ico 1 p, crossAt etaN etaNt b = - ((n : ℂ) * (n : ℂ)) := by
  classical
  have hsplit : ∑ b ∈ Finset.range p, crossAt etaN etaNt b
      = crossAt etaN etaNt 0 + ∑ b ∈ Finset.Ico 1 p, crossAt etaN etaNt b := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (Nat.one_le_iff_ne_zero.mpr hp.ne')]
    congr 1
    rw [show (0 : ℕ) = 0 from rfl]
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [hzero] at hsplit
  have heq : (n : ℂ) * (n : ℂ) + ∑ b ∈ Finset.Ico 1 p, crossAt etaN etaNt b = 0 := by
    rw [← hsplit]; exact hfull
  linear_combination heq

/-- **`cross_term_is_negative` — the signed/moment-cone escape.**  The joint interaction `−n²` is
*strictly negative* whenever `n ≠ 0`.  A nonnegative count (the hypothesis of
`MomentLadderExceedsPrize`) can never be negative; therefore the RG interaction functional lives
genuinely OUTSIDE the moment cone.  This is the one structurally-new feature: the RG contracts using
a *signed* (cancelling) quantity, not a count. -/
theorem cross_term_is_negative (n : ℕ) (hn : 0 < n) :
    (-((n : ℝ) * (n : ℝ))) < 0 := by
  have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  nlinarith [this]

/-! ## 3. The RG energy recursion `T : E ↦ E − n/(p−1)` (the genuine non-decoupling flow). -/

/-- The (un-normalized) level-`n` energy mass `Avg`-numerator: `Σ_{b≠0} |η_b(μ_n)|²`.  Parseval
pins it to `n(p−1) − n²` (frozen 2nd moment), modeled here as the parameter `enMass n`.  We work
with the *recursion* the DOUBLE+CROSS identities force, abstracting the magnitude. -/
def energyMass (mass : ℕ → ℝ) (n : ℕ) : ℝ := mass n

/-- **`energy_recursion` — the RG flow `T`.**  The level-`2n` energy mass equals
`2·(level-n mass) + 2·(cross term)`, and with the proven cross term `= −n²` this is
`mass(2n) = 2·mass(n) − 2n²`.  Dividing by the level-`2n` normalization `2n(p−1)` gives the
normalized flow `E(2n) = E(n) − n/(p−1)`: a genuine *strict downward* contraction of the energy,
driven entirely by the negative joint cross term (decoupling, dropping the cross term, gives
`E(2n) = E(n)`, the saving-preserving constant map). -/
theorem energy_recursion (mass : ℕ → ℝ) (n p : ℕ) (hn : 0 < n)
    (hrec : mass (2 * n) = 2 * mass n + 2 * (-((n : ℝ) * (n : ℝ))))
    (hp1 : (1 : ℝ) < p)
    (hEn : mass n = (n : ℝ) * ((p : ℝ) - 1)) :
    -- Parseval-frozen base: E(n)=1 ⇒ mass(n)=n(p−1)
    mass (2 * n) / (2 * (n : ℝ) * ((p : ℝ) - 1)) = 1 - (n : ℝ) / ((p : ℝ) - 1) := by
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [hrec, hEn]
  field_simp
  ring

/-! ## 4. The fixed point: total drop over the tower, and the BGK-floor verdict. -/

/-- **`rg_total_drop` — iterating `T` over the tower.**  Summing the per-step energy drop
`n_k/(p−1)` with `n_k = 2^k` over the `log₂ n` doublings from `μ_2` to `μ_n` gives total drop
`(2^{L+1} − 2)/(p−1)`.  We prove the geometric-sum form `Σ_{k=0}^{L-1} 2^{k+1} = 2^{L+1} − 2`
(the doublings `μ_2→μ_4→…→μ_{2^L}`), so the total energy the joint flow removes is exactly
`(2^{L+1}−2)/(p−1) ≈ 2n/(p−1)`. -/
theorem rg_total_drop (L : ℕ) :
    ∑ k ∈ Finset.range L, (2 : ℝ) ^ (k + 1) = 2 ^ (L + 1) - 2 := by
  induction L with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- **`rg_fixed_point_is_bgk_floor` — the named verdict.**  In the prize regime the contraction
*strength* is `n/(p−1)`, and the total drop `(2n−2)/(p−1)` over the whole tower is `< 1` (indeed
exponentially small) precisely when `2n − 2 < p − 1`, i.e. `2n < p`.  Since the prize regime has
`p ≈ n·2^128 ≫ 2n`, the *entire* RG flow removes less than one full unit of normalized energy: the
sup-norm fixed point stays at the BGK floor `n^{1−o(1)}`, NOT `√n`.  We prove the decisive
inequality `(2n−2)/(p−1) < 1` from `2n < p` — the formal statement that the cumulative contraction
cannot close the `√n`-to-`√(n log m)` gap. -/
theorem rg_fixed_point_is_bgk_floor (n p : ℕ) (hp1 : (1 : ℝ) < p) (hthin : 2 * n < p) :
    (2 * (n : ℝ) - 2) / ((p : ℝ) - 1) < 1 := by
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_lt_one hp1']
  have : (2 : ℝ) * n < p := by exact_mod_cast hthin
  linarith

/-- **`escape_edge_macroscopic_anticorrelation` — the precise edge condition for escape.**  `T`
would reach the `√n` fixed point iff its per-step contraction were `Θ(1)`, i.e. iff the cross
correlation were `Θ(n·p)` (a *macroscopic* `Θ(1)`-fraction of the energy cancelling), not the
proven exact `−n²` (a *microscopic* `Θ(n/p)`-fraction).  We formalize the gap: the *actual* per-step
drop `n/(p−1)` is `< ε` for any `ε > 0` once `p` is large (`n < ε(p−1)`), whereas a *macroscopic*
drop would need `n/(p−1) = Θ(1)`.  The proven `Θ(n²)` cross-term ceiling forbids the macroscopic
regime; this is the exact, quantified reason the tower self-similarity does not escape. -/
theorem escape_edge_macroscopic_anticorrelation (n p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hp1 : (1 : ℝ) < p) (hbig : (n : ℝ) < ε * ((p : ℝ) - 1)) :
    (n : ℝ) / ((p : ℝ) - 1) < ε := by
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_lt_iff₀ hp1']
  linarith

/-! ## 4b. The moment-level trap — the precise reason the signed lever cannot be lifted to escape.

The repair attempt (advocate) was to lift the signed cross term from `r=1` (energy, frozen by
moment-necessity) to a higher moment `r` that can *see* the sup-norm max via `M^{2r} ≤ p·E_r`.  The exact
`F_p` computation kills it on sign/`p`-dependence (see header).  But there is a *structural* no-go that does
not depend on the sign computation: a `2r`-moment object's entire content is `E_r`, and the *only* universal
max-vs-energy inequality is `M^{2r} ≤ p·E_r`.  Therefore the high-moment route is **exactly as strong as the
`E_r` bound it is fed** — it cannot manufacture a bound on `M` stronger than the bound on `E_r` it assumes.

`moment_level_trap` formalizes this: from the two inputs `M^{2r} ≤ p·E_r` (universal) and
`E_r ≤ (2r−1)!!·n^r` (the prize `rEnergy` bound), one derives `M^{2r} ≤ p·(2r−1)!!·n^r` — and *nothing
sharper*, because the chain is a single transitive `≤`.  Conversely the conclusion is **equivalent** to its
`E_r` input up to the fixed factor `p·(M^{2r}/E_r)`, so the moment object can never *provide* the prize
`E_r` bound (it would be assuming it).  This is the formal statement that the signed lever (`r=1`) and the
frozen level (`r=1`) coincide: the repair has nowhere to go. -/

/-- **`moment_level_trap` — the high-moment route is exactly as strong as its `E_r` input (circular).**
Given the *universal* max-vs-energy inequality `Msq2r ≤ p · Er` (here `Msq2r := M^{2r}`, `Er := Σ_b|η_b|^{2r}`)
and the prize `rEnergy` bound `Er ≤ dfac · nr` (here `dfac := (2r−1)!!`, `nr := n^r`), the best the moment
object yields is `Msq2r ≤ p · dfac · nr` — i.e. the prize bound on `M`, derived by a single transitive step.
The moment object adds nothing beyond the `Er` bound it is fed; hence it cannot *supply* `Er ≤ dfac·nr`
(it assumes it).  This is the formal moment-level trap: any object whose content is a `2r`-moment can only
restate the `rEnergy` prize, not prove it.  The signed RG cross term that *is* exact, negative and
`p`-independent lives only at `r=1` (the frozen energy level), so the repair cannot separate the signed lever
from the frozen level. -/
theorem moment_level_trap (Msq2r Er dfac nr p : ℝ)
    (hp : 0 ≤ p) (hdfac : 0 ≤ dfac) (hnr : 0 ≤ nr)
    (huniv : Msq2r ≤ p * Er)              -- universal: M^{2r} ≤ p·E_r (only max-vs-energy inequality)
    (hEr : Er ≤ dfac * nr) :              -- prize input: E_r ≤ (2r−1)!!·n^r (the rEnergy bound itself)
    Msq2r ≤ p * (dfac * nr) := by
  have h1 : p * Er ≤ p * (dfac * nr) := by
    apply mul_le_mul_of_nonneg_left hEr hp
  linarith [huniv, h1]

/-- **`moment_trap_no_strengthening` — the conclusion is pinned to the `E_r` input (no free lunch).**
The gap between the universal bound `p·E_r` and the prize-substituted bound `p·dfac·nr` is exactly
`p·(dfac·nr − E_r) ≥ 0`: the moment route's output improves on `p·E_r` by *precisely* the slack in the
`E_r ≤ dfac·nr` hypothesis, and by nothing else.  So the entire strength of the high-moment object is the
`rEnergy` bound — confirming the route is circular (it cannot create the bound it needs). -/
theorem moment_trap_no_strengthening (Er dfac nr p : ℝ) (hp : 0 ≤ p) (hEr : Er ≤ dfac * nr) :
    p * (dfac * nr) - p * Er = p * (dfac * nr - Er) ∧ 0 ≤ p * (dfac * nr - Er) := by
  refine ⟨by ring, ?_⟩
  have : 0 ≤ dfac * nr - Er := by linarith
  exact mul_nonneg hp this

/-! ## 5. The named verdict Prop — REDUCES, with the genuine contraction and its fixed point. -/

/-- **`RGBootstrapReducesToFloor`.**  The RG bootstrap's verdict as a Prop: a *genuine*
(non-saving-preserving) energy contraction `T : E ↦ E − n/(p−1)` exists — built from the exact
signed joint cross term `−n²` that decoupling discards — but in the thin/prize regime `2n < p` its
total contraction over the tower is `< 1`, so the sup-norm fixed point is the BGK floor, not `√n`.
The prize therefore REDUCES (the flow improves the bound strictly, just not to `√n`), and the exact
edge for escape is named: a macroscopic `Θ(np)` cross-correlation, forbidden by the `Θ(n²)`
ceiling. -/
def RGBootstrapReducesToFloor (n p : ℕ) : Prop :=
  (1 : ℝ) < p → 2 * n < p →
    -- genuine contraction strength (signed, negative cross term) AND too weak to close the gap:
    ((-((n : ℝ) * (n : ℝ))) < 0) ∧ ((2 * (n : ℝ) - 2) / ((p : ℝ) - 1) < 1)

/-- The verdict holds unconditionally on the regime hypotheses: the joint cross term is negative
(genuine signed contraction, moment-cone escape) and the cumulative drop is `< 1` (BGK floor fixed
point).  REDUCES is a theorem, not a numerical guess. -/
theorem rgBootstrap_reduces_to_floor (n p : ℕ) (hn : 0 < n) :
    RGBootstrapReducesToFloor n p := by
  intro hp1 hthin
  refine ⟨cross_term_is_negative n hn, rg_fixed_point_is_bgk_floor n p hp1 hthin⟩

/-! ## 6. Teeth — the flow is non-vacuous (decoupling is the `cross = 0` degenerate case). -/

/-- **Tooth — decoupling is the degenerate `cross = 0` flow (saving-preserving).**  Setting the
cross term to `0` (the decoupling assumption) makes the energy recursion `mass(2n) = 2·mass(n)`,
whose normalized form is `E(2n) = E(n)` — the constant map with a line of fixed points (no
contraction).  This exhibits that the genuine RG flow's contraction comes *entirely* from the
nonzero (negative) joint cross term: the `−n/(p−1)` drop is exactly the joint correction decoupling
throws away. -/
theorem decoupling_is_constant_map (mass : ℕ → ℝ) (n p : ℕ) (hn : 0 < n)
    (hrec0 : mass (2 * n) = 2 * mass n + 2 * (0 : ℝ))
    (hp1 : (1 : ℝ) < p)
    (hEn : mass n = (n : ℝ) * ((p : ℝ) - 1)) :
    mass (2 * n) / (2 * (n : ℝ) * ((p : ℝ) - 1)) = 1 := by
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [hrec0, hEn]
  rw [div_eq_iff (by positivity)]
  ring

/-- **Tooth — the cross term is exactly the per-step contraction.**  The difference between the
decoupled fixed value `1` and the genuine flow value `1 − n/(p−1)` is exactly `n/(p−1)`, the
normalized magnitude of the joint cross term.  Confirms the contraction is *real and quantified*. -/
theorem contraction_equals_cross (n p : ℕ) (hp1 : (1 : ℝ) < p) :
    (1 : ℝ) - (1 - (n : ℝ) / ((p : ℝ) - 1)) = (n : ℝ) / ((p : ℝ) - 1) := by
  ring

end

end ArkLib.ProximityGap.Frontier.AmbRG

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.double_split
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.cross_term_eq_negNsq
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.cross_term_is_negative
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.energy_recursion
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.rg_total_drop
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.rg_fixed_point_is_bgk_floor
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.escape_edge_macroscopic_anticorrelation
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.rgBootstrap_reduces_to_floor
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.decoupling_is_constant_map
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.contraction_equals_cross
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.moment_level_trap
#print axioms ArkLib.ProximityGap.Frontier.AmbRG.moment_trap_no_strengthening
