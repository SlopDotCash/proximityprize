# The Tower–Fiber Formal Corpus (#232, O35–O117)

The connected machine-checked theory built around the Proximity Prize's open core,
spanning `ArkLib/Data/CodingTheory/ProximityGap/`. Every theorem below is axiom-clean
(`[propext, Classical.choice, Quot.sound]`, 0 sorry). The narrative ledger is
`Research/ProximityPrize/DISPROOF_LOG.md` entries O35–O117 (numbering shared with other swarm lanes from ~O85);
this page is the stable map.

## The files

| File | Contents |
|---|---|
| `DescentKernelLemma.lean` | Lemma K (`kernel_rigidity`), sharp `pattern_rigidity` (`2\|B\|+\|O₁\| ≥ 2κ`), `agreement_count`, `exists_glue_decomposition` — the descent program's single-level bookkeeping. |
| `C2CoreEliminationBound.lean` | 2026/858 Thm 38 machine-checked (`c2_core_bound`) with the minimal nondegeneracy proviso, plus the refutation of its literal `min` packaging (`thm38_min_bound_fails`, kernel-checked `ZMod 11` witness). |
| `NormalRankSharpThreshold.lean` | 2026/858 Thm 26 + Rem 27 (sharp rank threshold, both sides); deficient-triples-are-sunflowers; the cyclic/PTE deficiency mechanism; `equal_window_image`. |
| `TopDirectionLineCount.lean` | The decoupling theorem (`top_line_compat_iff`), Conjecture-41 count lower bound and kernel-checked violation witness (`conj41_violation_witness`), the point-fiber theorem (`point_compat_iff_esymm_zero`, `zero_fiber_filter_eq`), the coset construction (`coset_fiber_lower_bound`), generic tower rung (`mul_root_closure`). |
| `DeBruijnTwoPrime.lean` | The two-prime (de Bruijn) theory, built O71–O117: coprime cyclotomic linear disjointness (`minpoly_qadjoin_eq_cyclotomic`), the unconditional double-slice (`two_prime_deBruijn_double_slice`), the packet cover (`two_prime_packet_cover`), **the full de Bruijn decomposition as an iff** (`two_prime_packet_decomposition` / `packetUnion_sum_zero`), small-sector closure, the spectral transfers (`packetUnion_spectral_transfer`, iterated + p-side + endpoint), the upward rung (`coset_lift`), the full export (orbit+dichotomy+transfer), the first-peel export (decomposition choice), **the general-t windowed law both directions** (`windowed_coset_cover_q/p`), and **the divisor-form law below p** (`windowed_coset_cover_below_p`). |
| `MixedRadixTower.lean` | The conditional two-prime tower: radix-d descent toolkit, rungs, the prime climb, the coprime weld (`coprime_mu_closure_combine`), `two_prime_tower_conditional`, degenerate base discharges. |
| `EffectiveTransfer.lean` | The O49 effective char-0 ⟺ F_p transfer: embedding bounds, `|ℤ-norm| ≤ B^finrank`, reduction nonvanishing, `esymm_eq_zero_iff_cyclotomicField`. |
| `ClassChartBounds.lean` | The scaling-orbit card equality, fiber cardinality as a weighted-projective orbit invariant, the conditional Aliev–Smyth decomposition, kernel-checked F₁₃ orbit instances. |
| `LamLeungTwoPow.lean` | Lam–Leung at p=2 (`vanishing_sum_antipodal`), the full tower theorem (`full_tower`) and converse (`closed_pow_sum_vanish`), the count (`tower_count`), the Newton bridge (`esymm_window_iff_psum_window`), general-word fold identities (`syndrome_fold`, `syndrome_fold_odd`), branch-mass conservation (`branch_mass_inequality`), window-weight tradeoff (`window_forces_weight`), and the capstones (`unit_syndrome_list_budget`, `two_sided_unit_syndrome_budget`). |

## The two-prime arc in one paragraph (O71–O117)

A vanishing subset of `μ_{p^{a+1}q^{b+1}}` (char 0) IS a disjoint union of full prime
packets (de Bruijn 1953, both directions machine-checked). One spectrum per
decomposition carries the orbit property, a membership dichotomy, and the complete
syndrome transfer at all exponents `p ∤ e`; iterating descends any q-power window to a
structured endpoint, and the upward rung (`coset_lift`) multiplies recovered coset
orders back up. The general-`t` windowed law follows in both prime directions —
window `{q^c ≤ t}` forces every element to be `μ_{q^c·p}`- or `μ_{q^{m+1}}`-covered —
and below `p` (one prime above the window) this is the full divisor form of the
exhaustively-verified law: `∃ d | n, d > t`, full `μ_d`-coset in `S`. The all-`t`
completion needs the bigraded two-spectrum analysis (the transfer's `p ∤ e` puncture
couples the `R`/`T` spectra in one underdetermined equation per exponent — joint
coverage must be carried through the induction); its decomposition-choice stall case is
already resolved by `first_peel_export`.

## The theory in one paragraph

On 2-power-torsion domains in characteristic zero (and over `F_p` above an explicit
cyclotomic-norm threshold — DISPROOF_LOG O49), the multi-symmetric fiber
`{S : e₁ = ⋯ = e_t = 0}` is **exactly** the unions of `μ_d`-cosets (`d` = smallest
2-power `> t`): `full_tower` + `closed_pow_sum_vanish` give the iff, `tower_count` gives
the `2^{O(1/η)}` budget, the Newton bridge identifies the esymm and power-sum forms, and
`zero_fiber_filter_eq` makes the fiber *equal* to a syndrome-side list at the unit
syndrome — composed in `unit_syndrome_list_budget` and pinned two-sidedly in
`two_sided_unit_syndrome_budget`. For general received words, the fold identities,
branch-mass conservation, and the window-weight tradeoff isolate the open remainder to
one object: the **branch-count distribution** down the squaring tower — equivalent to
S-two Conjecture 1 (ePrint 2026/532 App. A) on these domains.

## Conventions and gotchas (recurring learnings)

- Verify single files with `lake env lean <file>`; only `lake build <module>` when a
  cross-file import needs a fresh `.olean` (twice total in this corpus).
- `Finset.filter` instances: keep statements `open Classical in` consistently;
  instance mismatches surface as α-equivalent-but-rejected `calc`/`rw` steps — fix via
  `le_trans (le_of_eq _)` + `Finset.filter_congr`, or `convert` + `congr 1` + `ext`.
- `linarith` fails over general fields (not ordered): use `linear_combination`.
- Beta-redexes from `set`/lambda filters block `rw`: `simp only []` first.
- Newton identities were avoidable everywhere except the esymm⇔psum bridge itself
  (power-sum windows transfer through fold/fiber structure directly).
- Literature lives in `~/Desktop/math/` (Lam–Leung, Conway–Jones, Mann, Zannier,
  Aliev–Smyth, KPS/DKS Nullstellensätze, BCIKS/BCHKS/GG25/S-two/Chai–Fan/Kambiré).
