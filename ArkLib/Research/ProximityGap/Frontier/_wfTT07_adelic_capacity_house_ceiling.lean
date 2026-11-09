/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-T07 frontier — adelic capacity / Fekete-Szegő House ceiling)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# wf-T07 — Capacity / transfinite-diameter ceiling on the conjugate set of the period (#444)

## The candidate (architect ID G2-2, cluster: adelic / heights / Fekete–Szegő)

Let `n = 2^μ`, `p ≈ n^4`.  Let `Ψ_b(T) = ∏_{σ∈Gal} (T − σ(θ_b)) ∈ ℤ[T]` be the period polynomial
of the Gauss period `θ_b = Σ_{x∈μ_n} ζ_p^{bx}`. These periods lie in the unique degree-`m`
subfield `K ⊂ ℚ(ζ_p)`, `m = (p−1)/n`, so `d = m`. (An earlier version placed `θ_b` in `ℚ(ζ_n)`
with `d = n/2`; that is wrong for periods of `μ_n ⊂ 𝔽_p^*` — audit CW-B19-02.)  Let `E_b ⊂ ℂ` be the
archimedean conjugate set and `cap(E_b)` its transfinite diameter (= logarithmic capacity).

> **CANDIDATE (the asserted SHARP UPPER ceiling).**  Via Fekete–Szegő WITH a non-archimedean
> splitting condition (Rumely), if the conjugate set together with its `p`-adic and `2`-adic local
> conjugate sets has total *adelic* capacity `< 1`, then the QUANTITATIVE Fekete bound gives
> `House(θ_b) ≤ cap(E_b)·exp(O(1)) + (non-arch corrections)`, and concretely
> `M(n)² ≤ n·(1 + log cap_adelic(θ_b))` with the prize `M(n) ≤ C√(n log(p/n))` claimed EQUIVALENT
> to `log cap_adelic(θ_b) ≤ C²·log(p/n) − 1`, a place-coupled adelic-capacity ceiling.

The architect's non-reduction rationale: capacity is a discriminant/Vandermonde (geometric-spread)
quantity, claimed structurally distinct from the additive-energy moment ladder `E_r` (F1), and the
`2`-adic & `p`-adic local capacities are claimed to be the coupling that escapes F3.

## THE VERDICT (revised after audit CW-B19-02): Obstruction 1 (direction) stands as a remark;
## the earlier Obstruction 2 (prize-scale VACUITY, `log cap → 0`) is RETRACTED.

Only the direction remark below survives. The Lean content of this file is elementary exponent /
inequality algebra; it does not establish any statement about actual Gauss-period discriminants.

### Obstruction 1 — Fekete gives a LOWER bound on House, not an upper (sign reversal = F1/T06).

The transfinite diameter of the conjugate set is, by Fekete's own definition, the limit of the
geometric mean of the pairwise distances:
`cap(E_b) = lim_d ( ∏_{i<j} |σ_i(θ) − σ_j(θ)| )^{2/(d(d−1))}`.
The product under the root is `√|disc(Ψ_b)|`.  For an algebraic *integer* `disc(Ψ_b) ∈ ℤ` is a
NONZERO integer, so `|disc(Ψ_b)| ≥ 1`, and Fekete's lower bound on the max-modulus reads
`House(θ_b) ≥ |disc(Ψ_b)|^{1/(d(d−1))} ≥ 1`.
This is the SAME direction T06 found by the product formula: the discriminant / capacity bounds the
House from BELOW.  Fekete therefore does not *supply* an upper ceiling `House ≤ cap·exp(O(1))`; this
does not show such a ceiling is false (a lower bound cannot refute an upper bound), only that the
candidate's central inequality is not delivered by Fekete (`capacity_gives_lower_bound`).

### (Retracted) Obstruction 2 — "the discriminant is `≈ p^{m−1}`, so `log cap = (log p)/m → 0`".

By the conductor–discriminant formula the period field `K` (degree `m=(p−1)/n` over ℚ) is tamely
ramified only at `p`, so `disc(Ψ_b) = p^{m−1}·f²` with `f ∈ ℤ` the index `[𝒪_K:ℤ[θ]]`. The earlier
argument treated `f` as negligible. **It is not** (audit CW-B19-02, exact Gauss-period
discriminants): `log|disc|/(m(m−1))` vs `(log p)/m` is `0.854` vs `0.381` at `p=97, n=8`
(`log f² ≈ 62`), `1.448` vs `0.196` at `p=1153, n=32` (`log f² ≈ 1578`), and `1.109` vs `0.0186` at
`p=7681, n=16, m=480` (`log f² ≈ 250610`). The capacity datum stays of order `(1/2)·log n`, not
`→ 0`. So the claims "`disc ≈ p^{m−1}`", "`log cap = (log p)/m → 0`", "the Fekete lower bound is
vacuous at the prize", and "the candidate's ceiling collapses to the Parseval floor" are all
unsupported and are withdrawn. Whether the candidate ceiling has content is left open here.

### The reduction map to the fences.

- **F1 (moment/energy is conjugate to the wall).**  `disc(Ψ_b) = ∏_{i<j}(η_i−η_j)²` is a symmetric
  function of the periods, hence a polynomial in the power sums `p_k = Σ η_i^k = E_{k/2}`-type
  moments.  Its leading content is exactly the second moment `p₂ = Σ η_i² = p − n` (the `G3`
  identity, `_wf9G3_periodpoly_coeff_nogo.lean`). (The earlier claim that this forces
  `disc ≈ p^{m−1}` is false: the index `f` is large; see the retraction above.)  So the capacity
  IS a function of the additive-energy moment ladder — not a new lever.  The geometric-mean (Fekete)
  reading only changes it into a LOWER bound, which F1's S2-equidistribution (`A01`,
  `(κ/c)·E_r ≥ M^{2r}`) already shows is conjugate to, never milder than, the wall.
- **F3 (non-archimedean is archimedean-blind) + F11 (BGK divisibility).**  The architect's "coupling
  to the `p`-adic and `2`-adic local capacities" reduces to the ramification data: the only
  non-archimedean content of `disc(Ψ_b)` is `v_p(disc) = m−1` (tame ramification at `p`) and
  `v_2(disc) ⊆ f²` (the index, prime-to-`p`).  These are precisely the conductor–discriminant /
  Stickelberger valuation classes that `_ValuationClassBarrier`/`_wfS4` prove carry "ZERO
  archimedean spread information"; `p^{m−1} ∥ disc` is the BGK bad-prime norm divisibility (F11).
  The adelic coupling adds no archimedean handle — it re-packages the `p`-blind ramification.

## Honest scope

Verdict (revised, audit CW-B19-02): **direction remark only; no vacuity verdict.**  Novel as a
*framing* (the literature Fekete–Szegő/Rumely program is about existence/finiteness of conjugate sets
when `cap ≷ 1`, never a sup-norm CEILING; absent from the cone). Fekete supplies only a LOWER bound on
House, so it does not deliver the candidate's ceiling; the earlier vacuity argument (`f ≈ 1`,
`log cap → 0`) is false and withdrawn. This file proves, axiom-clean, only elementary algebra:
(1) `capacity_gives_lower_bound` (a linear-inequality rearrangement under a hypothesised Fekete
bound); (2) the exponent identity `(p^{m−1})^{1/(m(m−1))} = p^{1/m}` and `log(p^{1/m}) → 0` as
`m → ∞` for fixed `p` — which says nothing about the true capacity, since `|disc| ≠ p^{m−1}`;
(3) `ceiling_below_band`, conditional on `logCap ≤ 1`, a premise that the exact discriminants do NOT
support (`logCap ≈ (1/2) log n`).

## References
- Fekete (1923) / Fekete–Szegő (1955); Rumely, *Capacity Theory on Algebraic Curves* (LNM 1378).
- arXiv 2412.13593 (On a Fekete–Szegő Theorem), eudml 207410 (splitting conditions) — all
  EXISTENCE/finiteness criteria via `cap ≷ 1`, NOT a quantitative House ceiling.
- in-tree: `_wf9G3_periodpoly_coeff_nogo.lean` (`p₂ = p − n`, disc≈p^{m−1}),
  `_wfTT06_coupled_productformula_house.lean` (the product-formula sign reversal, T06),
  `_ValuationClassBarrier.lean`/`_wfS4_stickelberger_perweight_threshold.lean` (F3),
  `scripts/probes/_probe_444_periodpoly_disc_cft.py` (14 cases, all `YES`),
  `docs/kb/deltastar-444-frontier-synthesis-NOLARP-2026-06-16.md` (the disc-house-blind row).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.AdelicCapacityHouseCeiling

open scoped Real

/-! ## 1. The Fekete capacity ↔ discriminant geometric-mean identity (LOWER, not upper).

For the conjugate set `E = {σ_i(θ)}` of `d` points, the transfinite diameter is the limit of the
geometric mean of the pairwise distances; its `d(d−1)`-th power is the absolute discriminant
`|disc(Ψ)| = ∏_{i<j} |σ_i − σ_j|²`.  We model the place data abstractly to expose the direction:
write `logCap := (1/(d(d−1)))·log|disc|` for the log-capacity and `logHouse` for the max
log-modulus.  Fekete's bound (the max dominates the geometric mean of moduli, and the pairwise
distances are bounded by twice the max modulus) gives `logCap ≤ logHouse + log 2`, i.e. capacity is
a LOWER bound on House. -/

/-- **Capacity is a LOWER bound on the House (Fekete direction).**  With `D := log|disc|` the log
discriminant over `d` conjugates and `logCap := D/(d(d−1))` the log-capacity, Fekete's elementary
bound `|σ_i − σ_j| ≤ 2·House` over the `d(d−1)/2` unordered pairs gives
`D = Σ_{i≠j} log|σ_i−σ_j| ≤ d(d−1)·(logHouse + log 2)`, hence `logCap ≤ logHouse + log 2`.  Capacity
bounds the House from BELOW — the OPPOSITE of the candidate's "House ≤ cap·exp(O(1))" ceiling. -/
theorem capacity_gives_lower_bound
    {D dd logHouse logCap : ℝ} (hdd : 0 < dd)
    (hFekete : D ≤ dd * (logHouse + Real.log 2))
    (hCap : logCap = D / dd) :
    logCap ≤ logHouse + Real.log 2 := by
  rw [hCap, div_le_iff₀ hdd]
  linarith

/-! ## 2. Exponent algebra for the `p^{m−1}` factor of the discriminant (vacuity reading RETRACTED).

By the conductor–discriminant formula `|disc(Ψ)| = p^{m−1}·f²` with `m = (p−1)/n`, the period field
is ramified only at `p`.  Fekete's lower bound on the House is then
`House ≥ |disc|^{1/(d(d−1))} ≥ (p^{m−1})^{1/(m(m−1))} = p^{1/m}` (taking `f ≥ 1`, `d = m`).
(This would make the bound `→ 1` only if `f ≈ 1`, which is false; see below.)  We prove the collapse
`(p^{m−1})^{1/(m(m−1))} = p^{1/m}` and that `log(p^{1/m}) = (log p)/m → 0`.

**Retracted interpretation (audit CW-B19-02).** The step `|disc| ≈ p^{m−1}` ignores the index `f`,
which is huge (`log f² ≈ 62, 1578, 250610` in the exact cases quoted in the module docstring), so
these exponent identities do not show that the Fekete bound or the capacity datum vanishes. -/

/-- **Exponent identity: `(p^{m−1})^{1/(m(m−1))} = p^{1/m}`** (pure `rpow` algebra; it concerns only
the `p^{m−1}` factor, not the full discriminant `p^{m−1}·f²`).
`((p^{m−1}))^{1/(m(m−1))} = p^{(m−1)/(m(m−1))} = p^{1/m}` for `p ≥ 0`, `m ≥ 2`.  Here all powers are
real `rpow`.  The exponent collapse is `(m−1)·(m(m−1))⁻¹ = m⁻¹`. -/
theorem disc_root_eq_pInvM (p : ℝ) (hp : 0 ≤ p) (m : ℝ) (hm : 2 ≤ m) :
    (p ^ (m - 1)) ^ ((m * (m - 1))⁻¹) = p ^ (m⁻¹) := by
  rw [← Real.rpow_mul hp]
  congr 1
  -- (m − 1) * (m * (m − 1))⁻¹ = m⁻¹
  have hm1 : m - 1 ≠ 0 := by intro h; nlinarith
  have hmne : m ≠ 0 := by intro h; nlinarith
  rw [mul_comm m (m - 1), mul_inv, ← mul_assoc, mul_inv_cancel₀ hm1, one_mul]

/-- **Exponent algebra: `log(p^{1/m}) = (log p)/m → 0` for fixed `p > 1`.**  For any target
`ε > 0` there is an `m` past which `(log p)/m < ε`. This is only the `p^{m−1}` part of the
discriminant; since the index `f` in `disc = p^{m−1}·f²` is large, it does NOT show that the true
capacity datum vanishes (the earlier "Fekete bound is vacuous at the prize" reading is retracted,
audit CW-B19-02). -/
theorem capacity_logcontent_vanishes (p : ℝ) (hp : 1 < p) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → Real.log (p ^ (m⁻¹)) < ε := by
  -- log(p^{1/m}) = (log p)/m.  Choose M = (log p)/ε + 1 > 0; for m ≥ M, (log p)/m ≤ (log p)/M < ε.
  have hlogp : 0 < Real.log p := Real.log_pos hp
  refine ⟨Real.log p / ε + 1, ?_⟩
  intro m hM
  have hMpos : (0 : ℝ) < Real.log p / ε + 1 := by positivity
  have hmpos : 0 < m := lt_of_lt_of_le hMpos hM
  rw [Real.log_rpow (by linarith : (0:ℝ) < p)]
  -- goal: Real.log p * m⁻¹ < ε.  Multiply out: log p * m⁻¹ < ε  ⟺  log p < ε * m  (m>0).
  have hεm : ε * (Real.log p / ε + 1) ≤ ε * m :=
    mul_le_mul_of_nonneg_left hM (le_of_lt hε)
  have hexp : ε * (Real.log p / ε + 1) = Real.log p + ε := by
    field_simp
  have hlt : Real.log p < ε * m := by nlinarith [hεm, hexp, hlogp]
  -- log p * m⁻¹ < ε * (m * m⁻¹) = ε, since log p < ε*m and m⁻¹ > 0, and m*m⁻¹ = 1.
  have hminv : (0 : ℝ) < m⁻¹ := inv_pos.mpr hmpos
  have hcancel : m * m⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hmpos)
  nlinarith [mul_lt_mul_of_pos_right hlt hminv, hcancel]

/-- The `p`-adic valuation of the discriminant: `disc = p^{m−1}·f²` with `p ∤ f`, so
`v_p(disc) = m − 1`, fixed by `(p,m)` alone. (The archimedean size of `disc` is dominated by the
index `f`, which this does not capture.) -/
def discValuationAtP (m : ℝ) : ℝ := m - 1

/-- **Conditional arithmetic: a capacity term `≤ 1` keeps `n·(1+logCap)` below the band.**  If
`logCap ≤ 1` then `n·(1+logCap) ≤ 2n < n·log m` once `log m > 2`. The premise `logCap ≤ 1` is
**not established** for the Gauss-period capacity: the exact discriminants give
`logCap ≈ (1/2) log n` (audit CW-B19-02), so this lemma does not show that the candidate's ceiling
collapses to the Parseval floor. -/
theorem ceiling_below_band (n m logCap : ℝ) (hn : 0 < n) (hcap : logCap ≤ 1)
    (hlogm : 2 < Real.log m) :
    n * (1 + logCap) < n * Real.log m := by
  have h2 : (1 : ℝ) + logCap ≤ 2 := by linarith
  have : n * (1 + logCap) ≤ n * 2 := by
    apply mul_le_mul_of_nonneg_left h2 (le_of_lt hn)
  calc n * (1 + logCap) ≤ n * 2 := this
    _ < n * Real.log m := by
        apply mul_lt_mul_of_pos_left _ hn
        linarith

end ProximityGap.Frontier.AdelicCapacityHouseCeiling

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx) -/
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.capacity_gives_lower_bound
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.disc_root_eq_pInvM
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.capacity_logcontent_vanishes
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.ceiling_below_band
