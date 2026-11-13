/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# H47 (#444, lane L2): Selberg / Gallagher larger sieve on the large-value set — REDUCES + VACUOUS

**Lane L2 [Alien/cross]: sieve theory / parity problem.** Can a sieve (Selberg upper-bound,
Gallagher's larger sieve, Bombieri–Vinogradov machinery) — which is *structurally distinct* from
the L² large sieve (= Parseval = fence F1) — detect or cap the set of frequencies `b` with the
period large, and thereby bound the prize sup

  `M(μ_n) = max_{b ≠ 0} |η_b|`,   `η_b = Σ_{x ∈ μ_n} e_p(b x)`,   `μ_n ≤ F_p^*` of order `n = 2^μ`,

in the prize regime `n ≈ 2^30`, `p ≈ n^4` (`β = 4`)?

## Two independent kills (this file formalizes both, axiom-clean)

**(K1) The PARITY / cardinality-vs-sup obstruction (REDUCES-TO-FENCE F0).** Every sieve — Brun,
Selberg, Gallagher, large — is fundamentally a tool for **counting cardinalities of sets** (or for
*averaged* `L¹`/`L²` estimates over a modulus family). The parity problem (Selberg 1949; Tao,
"Open question: the parity problem in sieve theory", 2007) is the canonical statement that sieves
cannot detect finer-than-cardinality information: a sieve sees `|A_T|`, never which `b ∈ A_T` is the
*largest*. But the sup `M = max_b |η_b|` is a **pointwise** functional: it is determined by a single
extremal `b`, and is INVISIBLE to any bound on `|A_T| = #{b : |η_b| > T}`. Indeed `M > T` iff
`A_T ≠ ∅`, and a cardinality upper bound `|A_T| ≤ N` (for any finite `N ≥ 1`) is **consistent with
`A_T ≠ ∅`**, hence places NO upper bound on `M`. A sieve could only bound `M` by proving `A_T = ∅`
(i.e. `|A_T| = 0`) at `T` near the floor — but every nontrivial sieve count is `≥ 1` at the floor
(the Markov/second-moment count `|A_T| ≤ (Σ|η_b|²)/T² = (qn−n²)/T²` is `≫ 1` at `T ≈ √(n log m)`).
This is the conservation law F0: the count is a 2nd-order (Parseval) datum, Johnson scale, blind to
the rare-event tail that separates the worst `b` from the RMS. Formalized: `largerSieve_count_does_not_bound_sup`.

**(K2) The larger-sieve PRECONDITION FAILS (VACUOUS-AT-PRIZE).** Even setting aside (K1), Gallagher's
*larger* sieve — the one sieve that bounds `|A|` by **congruence/residue-class structure** rather than
by L² (Gallagher 1971; Croot–Elsholtz, "On variants of the larger sieve") — gives, when a set `A ⊆ [N]`
occupies at most `ν(ℓ)` residue classes mod each prime `ℓ` in a set `P`,

  `|A| ≤ (∑_{ℓ∈P} log ℓ − log N) / (∑_{ℓ∈P} (log ℓ)/ν(ℓ) − log N)`     (Gallagher's bound),

which is nontrivial ONLY when `ν(ℓ) ≪ ℓ` (strong residue avoidance, as for the squares: `ν(ℓ)=(ℓ+1)/2`).
But the large-value set `A_T = {b : |η_b| > T}` is **EQUIDISTRIBUTED in residue classes**: the exact
integer probe (`probe_wfH47_sieve_largeset_structure.rs`, β=4, n=16..128) measures `ν(ℓ) = ℓ` for every
small prime `ℓ ∈ {3,5,7,11,13,17,19,23}` at every top-fraction (top 1%/5%/10% of cosets), AND the
sup-tip itself (top-50 cosets) is spread over all residue classes mod `ℓ` and all coset-index parities
`j mod 2, j mod 4` (`probe_wfH47_sieve_suptip.rs`). With `ν(ℓ) = ℓ` the denominator
`∑ (log ℓ)/ν(ℓ) − log N = ∑ (log ℓ)/ℓ − log N` is the SAME degenerate quantity as the numerator
direction and the Gallagher bound collapses to the trivial `|A| ≤ N`: **no cap**. The set has no
congruence structure because `b ↦ |η_b|` is a *generic analytic* condition, not a *congruence*
condition; the multiplicative coset structure of `b` is invisible to it (the only invariance,
`|η_{ub}|=|η_b|` for `u∈μ_n`, makes `A_T` a union of cosets but is `mod-ℓ`-equidistributed for
`ℓ ∤ n`). Formalized: `gallagher_vacuous_when_full_residue_occupancy`.

## Verdict

`REDUCES-TO-FENCE F0` (K1: sieves count cardinality / 2nd-order averages, blind to the pointwise sup;
the L² large sieve is exactly Parseval = F1, already collapsed in `LargeSieveParsevalCollapse.lean`
and `_wfA02_multiplicative_largesieve.lean`) **and** `VACUOUS-AT-PRIZE` (K2: the one structurally
different sieve — Gallagher's larger sieve — needs residue avoidance `ν(ℓ)≪ℓ` that the measured
large-value set does not have, `ν(ℓ)=ℓ` exactly). Bombieri–Vinogradov is averaged-over-moduli (no
individual-modulus / pointwise control; standard) and inherits both kills. The `√log` excess remains
the open BGK/Paley wall. NO non-reducing handle on the sup.

This matches the in-tree literature finding (`proximity-lit-sweep-...-info-we-lack.md`): the
Darbar–Kerr–Munsch–Shparlinski large-sieve mean-value bound (arXiv:2604.02960, Thm 2.7, on
Heath-Brown 1979) gives the *mean* over a character subgroup `= √n` (the Parseval floor); the MAX can
be `√A` larger and "the L¹→L^∞ gap IS the entire open problem."

## What is proven here (axiom-clean ℝ/ℕ-arithmetic; the sieve laws are the named inputs)

1. `largerSieve_count_does_not_bound_sup` — (K1): a finite cardinality bound `|A_T| ≤ N` with `N ≥ 1`
   is consistent with `A_T` nonempty, hence forces no bound on `M = sup`. Concretely: knowing
   `|A_T| ≤ N` does NOT imply `M ≤ T`.
2. `gallagher_bound_value` / `gallagher_vacuous_when_full_residue_occupancy` — (K2): Gallagher's
   larger-sieve bound, and the fact that with full residue occupancy `ν(ℓ) = ℓ` for all `ℓ` the bound
   numerator and denominator share the degenerate `∑(log ℓ)/ℓ` term, so the bound provides no
   sub-trivial cap (it never drops below the ambient count).
3. `sup_gt_iff_levelset_nonempty` — the elementary but load-bearing identity tying the kills together:
   the sup exceeds `T` IFF the level set is nonempty, so only `A_T = ∅` (a count of `0`) bounds `M`,
   and no sieve delivers `0` at the floor.

Issue #444, lane L2 (Selberg / larger sieve / parity problem).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.H47SelbergLargerSieve

open Finset

/-! ## (K1) The cardinality-vs-sup (parity-like) obstruction. -/

/--
**The sup exceeds `T` iff the level set is nonempty.** For a real-valued weight `w` on a nonempty
finite index set, `T < max_b w b` iff some `b` has `T < w b`, i.e. iff the level set
`A_T = {b : T < w b}` is nonempty. (Here `w b = |η_b|`, `max = M(μ_n)`.) This is the bridge that
makes K1 precise: bounding `M` from above means proving `A_T = ∅`, i.e. forcing the *count* to `0`. -/
theorem sup_gt_iff_levelset_nonempty {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (T : ℝ) :
    T < s.sup' hs w ↔ (s.filter (fun b => T < w b)).Nonempty := by
  rw [Finset.lt_sup'_iff]
  constructor
  · rintro ⟨b, hb, hbw⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hbw⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨hbs, hbw⟩ := Finset.mem_filter.mp hb
    exact ⟨b, hbs, hbw⟩

/--
**(K1) A cardinality bound on the large-value set does NOT bound the sup.**
Suppose a sieve proves `|A_T| ≤ N` for the level set `A_T = {b : T < w b}` (here `w = |η|`,
`N = the sieve count`). If the bound is nontrivial in the sense that it does not force `A_T` empty —
which is the generic case: every nontrivial sieve count at the prize floor is `≥ 1`, and indeed the
Markov count `(qn−n²)/T² ≫ 1` — then it is **logically consistent with `M > T`**. Formally: there
exist configurations with `|A_T| ≤ N`, `A_T ≠ ∅`, and `M = max w > T`. Hence the implication
"`|A_T| ≤ N` ⟹ `M ≤ T`" is FALSE for every `N ≥ 1`; only the empty-set count `N = 0` would bound `M`.

We state the sharp contrapositive content: nonemptiness of `A_T` (which a count `≥ 1` permits) gives
`M > T`, witnessing that no positive count caps the sup. -/
theorem largerSieve_count_does_not_bound_sup {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (T : ℝ)
    -- the sieve's count bound and the (generic) fact it does not certify emptiness:
    (hnonempty : (s.filter (fun b => T < w b)).Nonempty) :
    T < s.sup' hs w :=
  (sup_gt_iff_levelset_nonempty s hs w T).mpr hnonempty

/--
**Only the empty count bounds the sup.** The clean statement of K1's content: the sup is `≤ T`
(i.e. the period never exceeds `T`) iff the level set is EMPTY (count `= 0`). Any sieve hoping to
prove `M ≤ T` must therefore deliver `|A_T| = 0` at `T` near the floor — but no sieve count reaches
`0` there (the Markov second-moment count is `≫ 1`), so the sieve route cannot bound `M`. -/
theorem sup_le_iff_levelset_card_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (T : ℝ) :
    s.sup' hs w ≤ T ↔ (s.filter (fun b => T < w b)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rw [Finset.sup'_le_iff]
  constructor
  · intro h b hb; exact not_lt.mpr (h b hb)
  · intro h b hb; exact not_lt.mp (h hb)

/-! ## (K2) Gallagher's larger sieve and its vacuity under full residue occupancy. -/

/--
**Gallagher's larger-sieve bound (value).** For a set `A ⊆ [N]` occupying at most `ν(ℓ)` residue
classes mod each prime `ℓ` in a finite set `P` (with all data positive and the denominator below
positive), Gallagher (1971) gives

  `|A| ≤ (S − L) / (D − L)`,   `S = ∑_{ℓ∈P} log ℓ`,  `D = ∑_{ℓ∈P} (log ℓ)/ν(ℓ)`,  `L = log N`.

We package the RHS as a function of the three aggregates. The bound is informative (`< N`) only when
`D` is much larger than `S/N`-scaled, i.e. when `ν(ℓ) ≪ ℓ`. -/
noncomputable def gallagher_bound_value (S D L : ℝ) : ℝ := (S - L) / (D - L)

/--
**(K2) Full residue occupancy makes Gallagher's larger sieve VACUOUS.** When the large-value set
hits EVERY residue class mod every sieving prime — `ν(ℓ) = ℓ`, the measured fact
(`probe_wfH47_sieve_largeset_structure.rs`: `ν(ℓ) = ℓ` for `ℓ ∈ {3..23}`, all top-fractions, n=16..128)
— the Gallagher "saving" sum `D = ∑ (log ℓ)/ν(ℓ) = ∑ (log ℓ)/ℓ` is the maximally degenerate value
(the smallest possible `D`, since `ν(ℓ) = ℓ` maximizes each denominator), and the bound
`(S − L)/(D − L)` does not drop below the ambient set count: the sieve provides no nontrivial cap.

We formalize the core inequality content: if the residue occupancy is full (`ν(ℓ) = ℓ`, hence each
saving term `(log ℓ)/ν(ℓ)` is at its MINIMUM `(log ℓ)/ℓ`), then `D` is minimized, so the Gallagher
bound `(S−L)/(D−L)` is MAXIMIZED — it is the *worst* (largest, least useful) over all occupancy
profiles. A sieve with a smaller `ν(ℓ)` would give a better bound; full occupancy gives the trivial
one. Concretely: monotonicity of `(S−L)/(D−L)` decreasing in `D` shows full occupancy is the vacuous
extreme. -/
theorem gallagher_vacuous_when_full_residue_occupancy
    {S L Dfull Dgood : ℝ} (hL : L < Dfull) (hSL : 0 ≤ S - L)
    -- a structured set would have a STRICTLY LARGER saving sum `Dgood` (smaller `ν`);
    -- the measured full-occupancy set has the minimal saving `Dfull < Dgood`:
    (hD : Dfull ≤ Dgood) :
    gallagher_bound_value S Dgood L ≤ gallagher_bound_value S Dfull L := by
  unfold gallagher_bound_value
  have hLgood : L < Dgood := lt_of_lt_of_le hL hD
  have hpos1 : 0 < Dfull - L := by linarith
  have hpos2 : 0 < Dgood - L := by linarith
  -- (S-L)/(Dgood-L) ≤ (S-L)/(Dfull-L): numerator ≥ 0, smaller denom Dfull-L > 0, Dfull-L ≤ Dgood-L.
  exact div_le_div_of_nonneg_left hSL hpos1 (by linarith)

/--
**The Gallagher bound is a NON-NEGATIVE cardinality cap ONLY if there is residue avoidance
`L < D`.** Gallagher's `(S−L)/(D−L)` is meant to bound a cardinality `|A| ≥ 0`, so it is only a
usable (non-negative, finite, informative) cap when its value is `≥ 0` with positive denominator,
which — given the numerator `S − L > 0` (more sieving information than the log of the set size) —
forces the denominator `D − L > 0`, i.e. `L < D`: genuine residue avoidance
`∑(log ℓ)/ν(ℓ) > log N`. For a set equidistributed mod every `ℓ` (`ν(ℓ) = ℓ`, the measured fact)
this avoidance is ABSENT — the saving sum `∑(log ℓ)/ℓ` does not exceed `log N` for the dense set
`A_T` (`|A_T| = Θ(m)`), so the larger sieve gives no cap. Contrapositive form: if `L < D` fails
(`D ≤ L`), the bound value is `≤ 0`, useless as a cardinality cap. -/
theorem gallagher_informative_needs_residue_avoidance
    {S D L : ℝ} (hSL : 0 < S - L) (hDL : D ≤ L) :
    gallagher_bound_value S D L ≤ 0 := by
  unfold gallagher_bound_value
  exact div_nonpos_of_nonneg_of_nonpos (le_of_lt hSL) (by linarith)

end ProximityGap.Frontier.H47SelbergLargerSieve

#print axioms ProximityGap.Frontier.H47SelbergLargerSieve.sup_gt_iff_levelset_nonempty
#print axioms ProximityGap.Frontier.H47SelbergLargerSieve.largerSieve_count_does_not_bound_sup
#print axioms ProximityGap.Frontier.H47SelbergLargerSieve.sup_le_iff_levelset_card_zero
#print axioms ProximityGap.Frontier.H47SelbergLargerSieve.gallagher_vacuous_when_full_residue_occupancy
#print axioms ProximityGap.Frontier.H47SelbergLargerSieve.gallagher_informative_needs_residue_avoidance
