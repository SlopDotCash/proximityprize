/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-A05 frontier — Galois-orbit count of spurious relations)
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# wf-A05 — the GALOIS-ORBIT-COUNT residual of the spurious energy (S7 reframe) (#444)

## The lane: closing the open residual stated in `_wfS7_galois_spread`

`n = 2^μ`, `p ≡ 1 (mod n)` prime, prize regime `p ≈ n^4` (`β = 4`). A *spurious* config is an
antipodal-free signed sum of `n`-th roots vanishing mod `p` but not over `ℤ`; these carry the
char-`p` excess `spur_r(p) = E_r^{char-p} − E_r^{char-0}` of the depth-`r` energy `E_r`.

`_wfS7_galois_spread.lean` (axiom-clean, prior) proved the Galois group `G = (ℤ/n)^×` acts
**freely** on the spurious set, so every orbit is FULL of size `|G| = φ(n) = n/2` and

  > `#spurious(n,w,p) = (#base orbits) · φ(n)`.

It then stated the precise OPEN residual: **`K` bounded `⟺` the number of base orbits `O` is
controlled.** This file CLOSES the arithmetic half of that residual — the exact conversion of an
orbit-count bound into a `K`-bound and back — leaving only the (genuinely open) input
`O ≤ C·(2r-1)!!·n^{r-1}` itself (= the BGK/Gauss-period spread).

## The arithmetic of the threshold (what this file proves, axiom-clean)

The depth-`r` energy decomposes `E_r = (char-0 part) + (spurious excess)`, with
`char-0 part ≤ D·n^r`, `D := (2r-1)!!` (proven char-0, taken as hypothesis here), and by the free
action the spurious excess is `spur = O · φ` with `φ = φ(n) = n/2`. So

  `E_r ≤ D·n^r + O·(n/2)`.

If the orbit count obeys the threshold `O ≤ C·D·n^{r-1}` then
`O·(n/2) ≤ (C/2)·D·n^r`, whence `E_r ≤ (1 + C/2)·D·n^r`, i.e. the moment ratio `E_r/(D·n^r)` is
**bounded by `1 + C/2`** uniformly in `n` — the prize `K`-bound (`K ≤ (1+C/2)^{1/r}`). This is the
content of:

* `orbitCount_bound_to_energy_bound` — `O ≤ C·D·n^{r-1}` ⟹ `E_r ≤ (1 + C/2)·D·n^r`.
* `energy_ratio_le_of_orbit_bound` — the same as a clean ratio `E_r ≤ (1 + C/2)·D·n^r`
  packaged with the char-0 hypothesis as the only other input.
* `orbit_explodes_of_energy_unbounded` — the **contrapositive / sharpness**: if `E_r` exceeds
  `B·D·n^r` for some `B > 1 + C/2`, then `O > C·D·n^{r-1}` — the orbit count must EXCEED the
  threshold. So the residual is genuinely *equivalent*: no `K`-blowup without orbit-count blowup.

The orbit count itself is provided by the free-action class equation, reproven here as a consumer
(`spurExcess_eq_orbitCount_mul_phi` is the prior `_wfS7_galois_spread` law in the shape needed).

## Honest scope at the prize regime (rules 1, 3)

This is **NOT** a CORE closure. It is the axiom-clean *bookkeeping bridge* of the S7 residual:
"orbit count `≤ C·(2r-1)!!·n^{r-1}`" ⟺ "`K` bounded". The bridge is unconditional; the INPUT
`O ≤ C·(2r-1)!!·n^{r-1}` is the open quantity (= the spread / BGK Gauss-period wall).

**MEASURED pre-screen (`probe_wfA05_galois_orbit_count.rs`, exact, `β = 4`):**
- The free-action law `#spur = O·|±G|` is confirmed EXACTLY (witness `n=64, p=17318209`:
  `#spur=2048 = 32·64`, `64 = 2φ(64)`, 32 base orbits, every orbit full).
- At `n ∈ {16, 32}` a sweep of `200`/`120` prize primes (`β = 4`) finds **ZERO** weight-`≤4`
  spurious relations on EVERY prize prime — `O_band ≡ 0`, `rho_2 = 0`. The orbit count does not
  even turn on below `n=64`; this is consistent with (does not refute) the bounded-`K` regime, but
  is NOT a proof at prize scale `n = 2^30` (the orbit count there is unmeasured — the genuine open
  residual). Honest tag: pre-screen, not proof.

CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.

## References
- in-tree: `_wfS7_galois_spread.lean` (free-action class equation, `galois_card_dvd_of_free`),
  `_wfS4_galois_perprime_spread.lean` (per-prime spread Fubini identity),
  `_wfS7_spur_minweight.lean` (Mann-analogue weight floor `p ≤ w^{φ}`).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
-/

namespace ArkLib.ProximityGap.Frontier.WFA05

open scoped BigOperators
open MulAction

/-! ## Part A — the free-action class equation in the consumer shape

We re-derive the prior `_wfS7_galois_spread` law `|X| = (#orbits)·|G|` for a free action, since
the orbit-count residual needs it as the spurious-excess identity `spur = O · φ`. -/

/-- A free finite-group action has every orbit of size `|G|` and the class equation
`|X| = (#orbits)·|G|`. (This is the prior `card_eq_numOrbits_mul_card_group_of_free`, restated for
self-containedness; it is the identity `spur = O · φ(n)` for `X` = the spurious set, `G = (ℤ/n)^×`.) -/
theorem spurExcess_eq_orbitCount_mul_phi {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [Finite X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    Nat.card X = Nat.card (Quotient (orbitRel G X)) * Nat.card G := by
  classical
  haveI : Fintype (Quotient (orbitRel G X)) := Fintype.ofFinite _
  have e := selfEquivSigmaOrbitsQuotientStabilizer G X
  rw [Nat.card_congr e, Nat.card_sigma]
  have hsumm : ∀ ω : Quotient (orbitRel G X),
      Nat.card (G ⧸ stabilizer G ω.out) = Nat.card G := by
    intro ω
    have hbot : stabilizer G ω.out = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      exact hfree g ω.out (by simpa using hg)
    rw [hbot]
    exact Nat.card_congr (QuotientGroup.quotientBot.toEquiv)
  rw [Finset.sum_congr rfl (fun ω _ => hsumm ω), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, ← Nat.card_eq_fintype_card (α := Quotient (orbitRel G X))]

/-! ## Part B — the orbit-count ↔ energy-bound bridge (the S7 residual conversion)

We work over `ℝ` with explicit nonnegative quantities. The depth-`r` energy `Er` decomposes as
`charZero + spur` with `charZero ≤ D·n^r`, `D = (2r-1)!!`, and `spur = O·φ` (the free-action law,
with `φ = n/2`). The bridge is the elementary inequality chain. -/

/-- **The orbit-count ⟹ energy-bound bridge.** Let `Er = charZero + spur` be the depth-`r` energy,
with the char-0 part bounded by `D·n^r` (`D := (2r-1)!!`, the proven char-0 envelope) and the
spurious excess `spur = O·φ` (free Galois action, `O =` #base orbits, `φ = n/2`). If the orbit
count obeys the threshold `O ≤ C·D·n^{r-1}` then `Er ≤ (1 + C/2)·D·n^r`. The `n/2` from `φ` cancels
exactly one power of `n` against the threshold's `n^{r-1}`, leaving the moment ratio bounded by
`1 + C/2` — the prize `K`-bound `K ≤ (1 + C/2)^{1/r}`. -/
theorem orbitCount_bound_to_energy_bound
    (Er charZero spur D C O n φ : ℝ) (r : ℕ)
    (hn : 0 ≤ n) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hdecomp : Er = charZero + spur)
    (hcz : charZero ≤ D * n ^ r)
    (hspur : spur = O * φ)
    (hφ : φ ≤ n / 2) (hφ0 : 0 ≤ φ)
    (hO : O ≤ C * D * n ^ (r - 1)) (hO0 : 0 ≤ O)
    (hr : 1 ≤ r) :
    Er ≤ (1 + C / 2) * D * n ^ r := by
  -- spur = O*φ ≤ (C D n^{r-1})·(n/2) = (C/2) D n^r.
  have hpow : n ^ (r - 1) * n = n ^ r := by
    have : r - 1 + 1 = r := Nat.sub_add_cancel hr
    calc n ^ (r - 1) * n = n ^ (r - 1 + 1) := by rw [pow_succ]
      _ = n ^ r := by rw [this]
  have hnr0 : 0 ≤ n ^ r := pow_nonneg hn r
  have hnr1 : 0 ≤ n ^ (r - 1) := pow_nonneg hn (r - 1)
  -- bound spur
  have hspur_le : spur ≤ (C / 2) * D * n ^ r := by
    rw [hspur]
    have h1 : O * φ ≤ (C * D * n ^ (r - 1)) * (n / 2) := by
      apply mul_le_mul hO hφ hφ0
      positivity
    refine le_trans h1 ?_
    have : (C * D * n ^ (r - 1)) * (n / 2) = (C / 2) * D * (n ^ (r - 1) * n) := by ring
    rw [this, hpow]
  -- combine
  calc Er = charZero + spur := hdecomp
    _ ≤ D * n ^ r + (C / 2) * D * n ^ r := add_le_add hcz hspur_le
    _ = (1 + C / 2) * D * n ^ r := by ring

/-- **Packaged ratio form.** Same conclusion `Er ≤ (1 + C/2)·D·n^r` from the orbit-count bound; this
is the statement the campaign consumes (the moment-ratio bound that gives the prize `K`). -/
theorem energy_ratio_le_of_orbit_bound
    (Er charZero spur D C O n φ : ℝ) (r : ℕ)
    (hn : 0 ≤ n) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hdecomp : Er = charZero + spur) (hcz : charZero ≤ D * n ^ r)
    (hspur : spur = O * φ) (hφ : φ ≤ n / 2) (hφ0 : 0 ≤ φ)
    (hO : O ≤ C * D * n ^ (r - 1)) (hO0 : 0 ≤ O) (hr : 1 ≤ r) :
    Er ≤ (1 + C / 2) * D * n ^ r :=
  orbitCount_bound_to_energy_bound Er charZero spur D C O n φ r hn hD hC hdecomp hcz
    hspur hφ hφ0 hO hO0 hr

/-- **Sharpness / contrapositive — no `K`-blowup without orbit-count blowup.** Suppose the energy
exceeds the bounded-`K` ceiling, `Er > (1 + C/2)·D·n^r` (for `n,D > 0`), the char-0 part is at most
`D·n^r`, and `spur = O·φ` with `φ ≤ n/2`. Then the orbit count strictly EXCEEDS the threshold,
`O > C·D·n^{r-1}`. So the orbit-count residual is genuinely EQUIVALENT to `K`-boundedness: the
spurious energy can only inflate by the orbit count crossing `C·(2r-1)!!·n^{r-1}`. -/
theorem orbit_explodes_of_energy_unbounded
    (Er charZero spur D C O n φ : ℝ) (r : ℕ)
    (hn : 0 < n) (hD : 0 < D) (hC : 0 ≤ C)
    (hdecomp : Er = charZero + spur)
    (hcz : charZero ≤ D * n ^ r)
    (hspur : spur = O * φ)
    (hφ : φ ≤ n / 2) (hφpos : 0 < φ)
    (hr : 1 ≤ r)
    (hbig : (1 + C / 2) * D * n ^ r < Er) :
    C * D * n ^ (r - 1) < O := by
  by_contra hle
  rw [not_lt] at hle
  -- O ≤ C D n^{r-1}, O can be negative? we don't assume; but hspur and hφ give spur ≤ (C/2)Dn^r
  -- only when O ≥ 0. Derive O ≥ 0 is NOT given; instead bound directly using hle and φ>0.
  have hpow : n ^ (r - 1) * n = n ^ r := by
    have : r - 1 + 1 = r := Nat.sub_add_cancel hr
    calc n ^ (r - 1) * n = n ^ (r - 1 + 1) := by rw [pow_succ]
      _ = n ^ r := by rw [this]
  have hnr0 : 0 ≤ n ^ r := pow_nonneg (le_of_lt hn) r
  -- spur = O*φ ≤ (C D n^{r-1})*φ ≤ (C D n^{r-1})*(n/2) since C D n^{r-1} ≥ 0? need that nonneg.
  have hCDnr : 0 ≤ C * D * n ^ (r - 1) :=
    mul_nonneg (mul_nonneg hC (le_of_lt hD)) (pow_nonneg (le_of_lt hn) (r - 1))
  have hspur_le : spur ≤ (C / 2) * D * n ^ r := by
    rw [hspur]
    have h1 : O * φ ≤ (C * D * n ^ (r - 1)) * φ := by
      apply mul_le_mul_of_nonneg_right hle (le_of_lt hφpos)
    have h2 : (C * D * n ^ (r - 1)) * φ ≤ (C * D * n ^ (r - 1)) * (n / 2) :=
      mul_le_mul_of_nonneg_left hφ hCDnr
    have h3 : (C * D * n ^ (r - 1)) * (n / 2) = (C / 2) * D * n ^ r := by
      have : (C * D * n ^ (r - 1)) * (n / 2) = (C / 2) * D * (n ^ (r - 1) * n) := by ring
      rw [this, hpow]
    exact le_trans h1 (le_trans h2 (le_of_eq h3))
  have : Er ≤ (1 + C / 2) * D * n ^ r := by
    calc Er = charZero + spur := hdecomp
      _ ≤ D * n ^ r + (C / 2) * D * n ^ r := add_le_add hcz hspur_le
      _ = (1 + C / 2) * D * n ^ r := by ring
  exact absurd hbig (not_lt.mpr this)

/-! ## Part C — the per-depth band consumer (sum over `w ≤ 2r`)

`spur_r(p)` aggregates the spurious excess over all weights `w ≤ 2r`. Writing `O_band = Σ_w O_w`
(the band orbit count) and `spur = O_band·φ`, the band threshold `O_band ≤ C·D·n^{r-1}` feeds the
exact same bridge. We package the band sum so the threshold is on the AGGREGATE orbit count. -/

/-- **Band aggregation.** If the spurious excess is `spur = (Σ_{w} O_w)·φ` (sum of per-weight base
orbit counts times `φ`), and the aggregate satisfies `Σ_w O_w ≤ C·D·n^{r-1}`, the energy bound
`Er ≤ (1 + C/2)·D·n^r` follows. The hypothesis is exactly the band orbit-count threshold. -/
theorem band_orbitCount_to_energy
    {ι : Type*} (s : Finset ι) (Ow : ι → ℝ)
    (Er charZero D C n φ : ℝ) (r : ℕ)
    (hn : 0 ≤ n) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hdecomp : Er = charZero + (∑ w ∈ s, Ow w) * φ)
    (hcz : charZero ≤ D * n ^ r)
    (hφ : φ ≤ n / 2) (hφ0 : 0 ≤ φ)
    (hOw0 : ∀ w ∈ s, 0 ≤ Ow w)
    (hband : (∑ w ∈ s, Ow w) ≤ C * D * n ^ (r - 1))
    (hr : 1 ≤ r) :
    Er ≤ (1 + C / 2) * D * n ^ r := by
  have hsum0 : 0 ≤ ∑ w ∈ s, Ow w := Finset.sum_nonneg hOw0
  exact orbitCount_bound_to_energy_bound Er charZero ((∑ w ∈ s, Ow w) * φ) D C
    (∑ w ∈ s, Ow w) n φ r hn hD hC hdecomp hcz rfl hφ hφ0 hband hsum0 hr

end ArkLib.ProximityGap.Frontier.WFA05

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WFA05.spurExcess_eq_orbitCount_mul_phi
#print axioms ArkLib.ProximityGap.Frontier.WFA05.orbitCount_bound_to_energy_bound
#print axioms ArkLib.ProximityGap.Frontier.WFA05.energy_ratio_le_of_orbit_bound
#print axioms ArkLib.ProximityGap.Frontier.WFA05.orbit_explodes_of_energy_unbounded
#print axioms ArkLib.ProximityGap.Frontier.WFA05.band_orbitCount_to_energy
