# #466 L4(A): Tsang/Selberg level-splitting is VACUOUS — the wraparound term has nothing to split (2026-07-01)

**Verdict: KILL, sharper than pre-registered.** DISPROOF tag `466-r4-tsang-levels-vacuous`.
Probe `scripts/probes/probe_466_tsang_levels.py` → `_out_466_tsang_levels.txt` (deterministic,
no RNG; independently re-run 2026-07-02, byte-identical numerics).

## Question

Does Selberg-style prime-power level-splitting of the char-p energy
`E_r = Σ_{b≠0}|η_b|^{2r}` capture wraparound structure past the diagonal? D3
(`Frontier/_D3TsangHighMomentRangeGate.lean`) is range-gated to `2r ≤ β` (constant depth);
the pre-registered kill-risk was that its hypothesis is exactly the already-closed diagonal
regime.

## Method (exact integer decomposition)

For each solution of `x₁+…+x_r ≡ y₁+…+y_r (mod p)` in `μ_n`, the **level** is
`k = (Σ_Z x − Σ_Z y)/p` (level 0 = holds over Z; |k| ≥ 1 = genuine wraparound). With
`N_k` = solution count at level k and `ĝ_k` = the smooth (equidistribution-null) window mass,
the exact identity `E_r = Σ_k e_k`, `e_k = p·N_k − Σ_{d∈W_k} g(d)` holds by construction
(asserted as exact integers; float cross-check vs direct η sums ≤ 6.3e-16 rel). Cells:
n = 8 (p = 4129, 4153), n = 16 (p = 65617, 65633), r = 2..6, plus 65537 = 2¹⁶+1 as the
FLAGGED generalized-Fermat contrast point.

## Findings

1. **For generic primes the wraparound term is IDENTICALLY ZERO** for all r ≤ 6 at n = 8 and
   r ≤ 4 at n = 16: `N_k = 0` for every k ≠ 0. `T_r` is p-independent there — new
   p-independent values `T₄(16) = 4,649,680`, `T₅(8) = 7,939,008`, `T₆(8) = 357,713,664`.
2. **Level 0 carries 100.1–104.2% of `E_r` in EVERY cell** (share +1.0006 … +1.0416): the
   entire excess over Wick is the Z-lift/archimedean object. Re-confirms "the wall is
   archimedean" from a new direction.
3. **At onset (n = 16, r = 5,6) the k ≠ 0 levels are SUB-smooth**: ρ_k = N_k/ĝ_k mostly
   0.002–0.22 < 1, with a small NEGATIVE excess (all-wraparound share −0.02 … −0.04 of E_r)
   — lift sums *repel* exact p-multiples; local z-scores of g at d = kp are ≈ −0.2 (the
   solution point is not special inside its own window).
4. **The resonant 65537 onsets earliest** (r = 4, level-3 concentration, ρ₃ = 1.12 → 1.83 →
   2.30 at r = 4,5,6) but its wraparound stays ≤ 1% of E_r (e₃/E_r = 0.0001/0.0021/0.0086).
   Consistent with the generalized-Fermat resonant-family flag; still nowhere near
   level-local dominance.

## Verdict

Past the closed diagonal (`2r ≤ β`) there is literally **nothing for a p-adic/divisor
level-splitting to localize**: the wraparound levels carry only (slightly less than) their
smooth/DC share, so any level-local bound reduces to smooth counting = the aggregate `W_r`.
The only structured level is 0 = the Z/diagonal regime D3 already owns. Do NOT re-attempt
level-splitting variants (window reshaping, signed levels, level-weighted moments): the
decomposition is exact and the non-zero levels are sub-smooth, not hiding structure.

Composes with: `_D3TsangHighMomentRangeGate.lean` (range gate), the archimedean-wall
dichotomy (#444), `466-r4-i031-tail-cosmetic` (the other L4 half).
