# Pulling all 8 open threads — verdict (wf_fbb6da8a-b8c, 2026-06-16)

8-thread parallel investigation of every open/dropped thread around the proof-obligation map, each
adversarially verified (3 lenses) + judged. **Verdict: no escape from the BGK wall. 6/8 collapse to the
open core M(n); 1 (T4) is a genuine non-BGK object but inert; 1 (T7) dies on a DIFFERENT, independent wall.**
Two findings correct earlier docs.

> **Correction (2026-10-28 audit, T48).**
> - **Count.** The table below has six collapses (T1, T2, T3, T5, T6, T8) plus two distinct cases
>   (T4, T7). The original header said "7/8 collapse" *and* listed both other cases, which adds up to
>   nine; the header and bottom line now say 6/8.
> - **Three different objects.** T2's "`#bad = E_k = p⁻¹Σ_b|S(b)|^{2k} = M(n)` exactly" is withdrawn.
>   The moment identity equates the energy `E_k` with an averaged power of the periods. It does not
>   identify that number with the spectral maximum `M(n)` or with an MCA bad-scalar count. Already
>   for `μ₂ = {1, −1} ⊆ F₅` at `k = 1`: `E_1 = 2`, every nonzero period has modulus `< 2`
>   (`≈ 0.618, 1.618`), and the constant code on `{1, −1}` with the pencil `(0,1) + γ·(0,2)` has exactly
>   one bad scalar (`γ = 2`) at radius `0`.
> - **Norm envelopes.** In correction 1 below, the failure of a norm-size certificate for larger `n`
>   does not prove that a chosen sponsor prime is bad (cross T85).
>
> The finite correction evidence (the T1 and T2 computations) is kept.

## Per-thread (all grounded by computation)
| thread | verdict | why |
|---|---|---|
| **T1 saturation / corrected monotonicity** | collapses-to-BGK (but rescues the reduction at the edge) | saturation excess `Θ(q)` lands at **offset 1 (near capacity), NOT the window edge** — at the window edge `#bad_q=#bad_0` (verified: excess prime 8161 vs faithful 4129/12289 give identical incidence at offset≥2). So the monotonicity HOLDS at the window edge; residual = char-0 offset asymptotic = open core. |
| **T2 census (ExplainableCoreSupply/CensusDomination)** | collapses-to-BGK; UNREPAIRABLE | `#SETS` (what CensusDomination bounds) over-counts `#bad` by 5–9× and **exceeds the budget at n=16** (deployed Prop is FALSE at prize budget). `#bad = E_k = p⁻¹Σ_b|S(b)|^{2k} = M(n)` exactly (verified to machine precision). No middle object. |
| **T3 cofactor / WB-pencil / PGL₂** | collapses-to-BGK | cofactor "doubling" confined to `agree=k+1` deep over-list regime (outside the window) — the generic dense-line saturation, not a window-edge effect; reduces to M(n). |
| **T4 smooth-vs-random M3** | partial-handle, **SURVIVES adversarial 3/3 — but INERT** | a genuinely different Weil-clean spectral-gap object, char-0-clean — BUT its δ*-signal is `q^{−Ω(1)} ≈ 2^{−607}` at `q≈2^128`, ~480 bits below the `ε*=2^-128` resolution any tail argument needs. Bought cleanliness by routing AROUND the char-p incomplete sum. No prize signal. |
| **T5 bypass-BGK (inverse-LO, slice-rank, fold, syndrome, derand)** | collapses-to-BGK | inverse-LO is a CONVERSE (hypothesis = desired conclusion, vacuous: roots of unity already a gap); all reduce to the small-ball/concentration = M(n). |
| **T6 thin-subgroup NT (Corvaja-Zannier, OSV, Shkredov, Myerson-Lehmer)** | collapses-to-BGK | TORSION MISMATCH (computed): CZ/subspace solution-count (the only q-uniform mechanism) doesn't apply to the relevant solutions; q-uniform bounds don't beat `n^{1−o(1)}`. |
| **T7 push floor past Johnson (char-indep autocorrelation)** | refuted-dead — on a DIFFERENT wall | dies on **coset-saturation** (`autocorrelation ≥ n/2−1`), = Kelley-3.2 curve-decodability — an INDEPENDENT open problem, NOT the BGK core. A genuine second front. Char-free bound reaches only half-Johnson. |
| **T8 Mahler-measure resultant / Poisson ceiling** | collapses-to-BGK | gives bad-prime SIZE (`≤2^{O(n log n)}`) not COUNT; the prize prime can itself be a bad prime; reduces to M(n). |

## Two corrections to earlier docs
1. **Doc 13's "P1 monotonicity is FATAL" is too strong — T1 shows P1 HOLDS at the window edge.** The
   saturation excess that refutes the *global* monotonicity is confined to offset 1 (near capacity).
   AT THE WINDOW EDGE, `#bad_q ≤ #bad_0` holds, so the doc-11/12 char-0 reduction is VALID there. The
   route is not dead — but its residual (the char-0 window-edge offset asymptotic `offset₀(n)`) is the
   open Paley/BGK core, with the precise new norm-size reason saturation can't reach the edge for `n ≲ 48`
   (saturation norms `(n/2)log(k+1)` first exceed `2^128` at `n≈64`). So: reduction valid, closure not.
2. **The census equivalence (issue's "asserted but never proven") is provably FALSE in the load-bearing
   direction**, not merely unproven — `#SETS > budget` at n=16. Settles that dropped thread negatively.

## The genuinely interesting residue (ranked)
1. **T7's second front** — the char-independent autocorrelation route dies on coset-saturation, an
   *independent* wall (curve-decodability of explicit RS), not BGK. Most interesting long-shot: bound the
   ragged-excess autocorrelation `M(S\core)` after coset-core removal; if separable from the core (the step
   that saturates at `n/2−1`), the floor moves past Johnson WITHOUT touching M(n). Different open problem.
2. **T1's exact residual** — the single scalar `offset₀(n)`; push the char-0 CRT incidence to `n=64–128`.
3. **T4** — real but inert; do not pursue (no prize signal).

## Honest bottom line
No escape. 6/8 threads = the same open core `M(n) ≤ C√(n log(p/n))` (thin-2-power Gauss-period / Paley)
in new vocabulary; T4 is char-0-clean but inert; T7 is a genuinely independent second wall. The recurring
law (exactly the honesty contract): **any prize-scale bound silently invokes √n-cancellation (= open core);
any genuinely char-0-clean angle loses all prize signal.** char-0 telescopes to Wick, char-p at r≈log q
does not, and nothing here crosses that gap. The prize core stands open — now with every adjacent thread
mapped to its precise terminus. Source: wf_fbb6da8a-b8c (12 agents). Related: docs 11,12,13.
