# δ*/#466 — SYZ37: the rate-1/2 assembly, and reconciling SYZ36's "saturated" claim (2026-07-11)

## TL;DR

SYZ36 reduced union-generation of a band triple to the vanishing of the **in-budget syzygy module**
of the reduced pairwise-coprime univariate triple `(W_AB, W_AC, W_BC)`, closed the *saturated*
sub-band (`k ≤ m_XY`) via `saturated_cofactor_zero`, and flagged the rest as "open beyond the
saturated sub-band … holds at rate ≤ 1/2 with maximal overlaps". SYZ37 **audits that claim at rate
exactly 1/2** and finds:

- **Reconciliation verdict: NO rate-1/2 interior-band triple is saturated.** At `k = n/2`, interior
  width `2n/3 < s < 3n/4`, every pairwise overlap obeys `m_XY ≤ k−1 < k`. The saturated route
  (needs `k ≤ m`) covers **zero** rate-1/2 band triples. SYZ36's saturated case is the WRONG
  mechanism at rate 1/2; the docstring phrasing "rate ≤ 1/2 with maximal overlaps" is misleading —
  the rate-1/2 interior band has **minimal-ish**, never maximal, overlaps.
- **Generation nonetheless holds for all of them** — via **degree**, not saturation: the Koszul (and
  every 2-support) certificate is *out of budget*, and the full in-budget syzygy module is `0`.
- **The residual is domain-independent and degree-forced** (new finding): 14 908 uniformly-random
  pairwise-coprime triples with rate-1/2 band degree profiles ⇒ **0** with a nonzero in-budget
  syzygy. The `μ_n` (roots-of-unity) domain does **not** unbalance the μ-basis — so there are no
  unbalanced instances to lift-test; none exist.

## The probe (`scripts/probes/probe_syz37_rate_half_assembly.py`)

Rate-1/2 configs `k = n//2`, `n ∈ {10,…,20}`, `p ∈ {31,101,65537}`, generic + roots-of-unity
domains, ~300 interior-band triples each:

```
p=* n=* k=n/2 dom=gen/roots: sat=0 nonsat=ALL | genFAILS=0 koszul_inbudget=0 inbudget_syz>0=0 | unbalanced_mubasis=0
```

Uniform: `sat=0` (none saturated), `genFAILS=0`, `inbudget_syz>0 = 0`, `unbalanced μ-basis = 0`.

Boundary (`k = n//2 + 1`, rate > 1/2): `genFAILS` reappears and equals `inbudget_syz>0` exactly
(e.g. n=10 k=6: 262 = 262; n=16 k=9: 166 = 166) — confirming SYZ36's law `d = syzdim`. Notably
`koszul_inbudget = 0` even just above 1/2: the first failing syzygies are **non-Koszul 3-support**.

Random-coprime stress test (in-line, manual GF(p) gcd): 14 908 random pairwise-coprime triples with
rate-1/2 band degree profiles → **0** in-budget syzygies. Vanishing depends only on the degree
profile + coprimality.

μ₁ balance law: minimal nonzero syzygy product-degree `D*` exceeds the uniform budget `k−1−t` by
`≥ 1` for every rate-1/2 band triple (margin 1 for n≤16, 2 for n=18). At rate 1/2 the μ-basis
minimal generator sits just *above* the budget window; it slips below only at rate > 1/2.

## The degree mechanism (why saturation is beside the point)

- **Uniform product bound.** Each in-budget product `W_XY · r_XY` has `deg ≤ (m_XY−t) + (k−1−m_XY)
  = k−1−t`, *independent of the pair* — the whole module lands in one degree-`(k−t)` window.
- **Koszul out of budget.** Inclusion–exclusion: `m_AB+m_AC+m_BC − t = 3s − |U| ≥ 3s − n`. With
  `|U| ≤ n = 2k`, `m_BC ≤ k−1`, interior `3s ≥ 2n+1`: `m_AB+m_AC − t ≥ k+2 > k−1`. The Koszul
  budget `m_AB+m_AC−t ≤ k−1` fails at rate 1/2 for every pair.
- **2-support vanishing.** A syzygy with a zero component forces (coprimality) `W_AC ∣ r_AB`, so
  `deg r_AB ≥ m_AC − t`; with the budget `deg r_AB ≤ k−1−m_AB` this needs the Koszul budget — which
  fails — so `r_AB = 0`. The whole 2-support stratum is empty.
- **3-support residual.** All three `r_XY ≠ 0`: not a divisibility fact — the μ-basis degree balance
  of a coprime univariate triple. Probe-forced by the degree profile alone (domain-independent).

## Lean landed: `Frontier/_SYZ37RateHalfAssembly.lean` (7 thms, axiom-clean)

`propext`/`Classical.choice`/`Quot.sound` only; no `sorry`, no `native_decide`.

- `not_saturated_rate_half` — `m ≤ k−1 ⇒ ¬ k ≤ m` (saturated route vacuous at rate 1/2).
- `inbudget_product_natDegree_le` — uniform product bound `deg (W·r) ≤ k−1−t`.
- `koszul_out_of_budget_rate_half` (ℤ) — `k−1 < m_AB+m_AC−t` from inclusion–exclusion + `n=2k` +
  interior width. The forced-failure certificate never fires at rate 1/2.
- `coprime_natDegree_le` — `W_AB·r_AB = W_AC·r_AC`, coprime, `r_AB≠0` ⇒ `deg W_AC ≤ deg r_AB`.
- `two_support_syzygy_vanishes` — 2-support stratum is empty at rate 1/2.
- `pairInteriorLaw_of_generation` / `rate_half_gate_closed_of_module_vanishes` — SYZ35 wiring:
  generation (`InBudgetSyzygyModuleVanishes`) ⇒ the sharp punctured-pair law = SYZ33 lemma 2 at
  rate 1/2.

## Honest final state of the strip theorem

SYZ36's "saturated" phrasing is **corrected**: at rate 1/2 generation is *not* by saturation
(vacuous) but by the out-of-budget/degree mechanism. The entire rate-1/2 residual is localized to a
**single classical, field- and domain-independent** statement — the μ-basis degree balance of
coprime univariate triples with band degree profile — proven here for the 0- and 2-support strata,
reduced to the 3-support stratum (probe-exact, degree-forced, 0 counterexamples) for the general
case. This is strictly stronger and cleaner than SYZ36's "open beyond the saturated sub-band".

The strip still does NOT deliver an unconditional δ* statement (SYZ33 caveats (i)–(iv) unchanged):
this closes lemma 2's rate-1/2 sub-band down to the 3-support μ-basis residual; the SYZ22
realizability / ledger bridge remain open.
