# G86H + G87V — the G83 fence instantiation: Hadamard bound and coverage divisibility PROVEN (2026-07-10)

Round: direct Fable 5, issue #466 / #505, lane = transversality seam (doctrine-v2 surviving
source #1). Files: `Frontier/_G86HadamardSupportSix.lean`, `Frontier/_G87CoverageDivisibility.lean`.

## What G83 left open

`_G83DeterminantCoverageFence.lean` proved the arithmetic handoff
(`p^s ∣ D`, `D > 0`, `D² ≤ 6^d` ⟹ `s·log p ≤ (d/2)·log 6`) but took all three certificate
fields as assumptions, recording three open instantiation pieces:

1. the Euclidean **Hadamard square bound** `D² ≤ 6^d` for support-six rows;
2. **coverage ⟹ divisibility** `p^s ∣ D` from common prime-ideal membership;
3. construction of a **full-rank census matrix** (nonzero determinant).

## G86 — Hadamard's determinant inequality (new to the tree AND absent from Mathlib)

Mathlib (at this checkout's pin) has no Hadamard determinant inequality. G86 proves it from
`InnerProductSpace.gramSchmidtOrthonormalBasis_det` + Cauchy–Schwarz + the ±1 determinant of
an orthonormal change of basis:

- `abs_basisFun_det_le_prod_norm` : `|det f| ≤ ∏ ‖f i‖` (family form, `EuclideanSpace ℝ`);
- `abs_det_le_prod_sqrt_row_sq_sum` : `|M.det| ≤ ∏ᵢ √(Σⱼ M i j²)` (matrix rows, ℝ);
- `sq_det_le_pow_of_row_sq_sum_le` : integer form — row squared norms ≤ B ⟹ `det² ≤ B^d`;
- `row_sq_sum_le_of_support_le` : a `{−1,0,1}` row with ≤ c nonzeros has squared norm ≤ c;
- `supportSixDeterminantCertificate_of_rows` : the weld — support-six rows + `det ≠ 0` +
  `p^s ∣ det` yield G83's `SupportSixDeterminantCertificate` (Hadamard field now a theorem);
- `no_census_matrix_above_half_height` : above the half-height threshold, coverage
  divisibility forces `det = 0`.

Piece (1) CLOSED. The family/matrix forms are Mathlib-upstreaming candidates.

## G87 — coverage ⟹ divisibility, with NO Smith normal form

Concretely, common coverage of the census at `s` distinct degree-one primes of `ℤ[ζ_n]` above
`p` means: every census row `w` satisfies `Σⱼ wⱼ t_k^j ≡ 0 (mod p)` at `s` roots `t_k` of
`Φ_n` mod `p`, pairwise distinct mod `p`. The elementary mechanism:

pad the roots to `d` nodes distinct mod `p`, set `A = (vandermonde t)ᵀ`; then `M·A` has the
covered columns divisible by `p`; **multilinearity of det in columns** gives
`p^s ∣ det(M)·det(A)`; `det A = ∏(t_j − t_i)` is a unit mod `p`; primality cancels it.

- `pow_card_dvd_det_of_cols_dvd` : columns in `S` divisible by `p` ⟹ `p^{|S|} ∣ det`
  (generic multilinearity brick, upstreaming candidate);
- `pow_dvd_det_of_annihilator` : the cancellation step;
- `pow_dvd_det_of_vanishing_at_roots` : **HEADLINE** — vanishing mod `p` at `|S|`
  pairwise-distinct nodes ⟹ `p^{|S|} ∣ det M`;
- `censusFence_of_vanishing_rows` : **end-to-end fence** (G87∘G86∘G83) — a full-rank
  support-six census matrix whose rows vanish at `s` distinct roots satisfies
  `s·log p ≤ (d/2)·log 6`, directly from raw matrix data.

Piece (2) CLOSED.

## What this changes in the G82 race

The fence bound is now UNCONDITIONAL for matrix families: any full-rank `d×d` support-six
family has common coverage `s ≤ (d/2)·log 6/log p`. At the prize cell (`d ≤ φ(n) = n/2`) this
is exactly the G82 threshold `s* = (n/4)·log 6/log p` — i.e. the CRT contradiction can never
be *strictly* fired by a full-rank support-six family; the forcing direction of the G82 race
is capped at marginality by theorem, matching the addendum probe (coverage ≡ 1 at all
accessible cells, factor `n/log n` below threshold).

**Remaining open content of the fence lane** = exactly piece (3), which is census-side and
data-dependent: either exhibit census structure forcing common coverage beyond the cap under
a coincidence hypothesis (now provably impossible for support-six full-rank families — a
non-CRT or non-support-six mechanism would be needed), or prove coverage stays `o(n/log n)`
(strengthening the fence below `s*`). Piece (b) of r369 anti-coincidence therefore still
needs a non-CRT mechanism.

## Honest scope

Axiom-clean (target `[propext, Classical.choice, Quot.sound]`; audit blocks in both files).
No bound on `M(μ_n)`; no census data is constructed; CORE remains OPEN / ON-BGK.

## Bonus: floor-bad(64) probe continuation (from the FS1 crash recovery)

The interrupted `_out_466_floorbad64_decide.txt` run (Windows multiprocessing WinError-5
crash) had COMPLETED two more primes before dying: **p=257 and p=449 are NOT floor-bad(64)**
(complete MITM scans, 10,424,700 pairs each, same certificate shape as p=193). p=577 was cut
off mid-scan. Floor-bad(64) so far contains NONE of the first primes ≡ 1 mod 64 tested
(193, 257, 449) — consistent with FS1's refutation of the uniform floor-successor conjecture.
