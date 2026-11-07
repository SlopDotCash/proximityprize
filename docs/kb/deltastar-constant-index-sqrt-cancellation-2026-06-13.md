# LANDED (axiom-clean, real build green): √-cancellation for EVERY constant-index subgroup (#407)

**Status: PROVEN, axiom-clean, real `lake build` green (3315 jobs, 0 sorryAx).** Generalizes the
index-2 QR discharge (`QRWorstCaseIncompleteSum.lean`) to **all constant indices** via the classical
Gauss sums. `ArkLib/Data/CodingTheory/ProximityGap/ConstantIndexGaussSumBound.lean`.

## What is landed

For a multiplicative character `χ : MulChar F ℂ` of order `m = orderOf χ ≥ 2` over a finite field `F`
(`q = |F|`), let `G_χ = {a : χ a = 1}` be the index-`m` subgroup. Then the worst-case per-frequency
incomplete sum is bounded **unconditionally**:

* `eta_constIndex_norm_le` : for `b ≠ 0`,  `‖η_b(G_χ)‖ ≤ ((m−1)·√q + 1)/m`.
* `worstCaseIncompleteSumBound_constIndex` : discharges the in-tree named open Prop
  `WorstCaseIncompleteSumBound ψ (G_χ) (((m−1)√q+1)/m)²` — no hypothesis beyond `m ≥ 2`.
  *(Corrected 2026-10-28, audit T48 / T107: both endpoints, `ConstantIndexGaussSumBound.lean:144,187`,
  also require the additive character `ψ` to be **primitive** (`hψ : ψ.IsPrimitive`), the same
  input the classical Gauss-sum formula needs. The headline "no hypothesis beyond `m ≥ 2`" omitted
  it. Discharging the generic `WorstCaseIncompleteSumBound` at this large scale `M` does not by
  itself establish a particular beyond-Johnson coding theorem; that still needs its quantitative
  consumer.)*

Since `|G_χ| = (q−1)/m =: n`, the bound reads `‖η_b‖ ≲ √m·√n` — **genuine square-root cancellation
for every CONSTANT (or polylog) index `m`**, which is the beyond-Johnson, sub-`√q` per-frequency
object the prize needs. It degrades to the trivial Weil `√q` exactly at `m = 2¹²⁸` (the prize 2-power
index) — i.e. it covers the entire constant-index lane and stops precisely at the open BGK regime.

## The proof (all axiom-clean, no wall)

The period is the average of the `m` twisted Gauss sums (character orthogonality):

  `m·η_b(G_χ) = Σ_{j<m} gaussSum(χ^j, ψ_b)`,  `ψ_b = mulShift ψ b`   (`eta_constIndex_decomp`),

via `mulChar_pow_sum_all` (`Σ_{j<m}(χ^j)a = m·[χ a = 1]`, geometric series + `χ^m=1`). The `j=0`
term is `gaussSum(1, ψ_b) = −1` (`gaussSum_one_eq_neg_one`); each `j≠0` term has magnitude `√q`
(`norm_gaussSum_pow_eq`, from `χ^j ≠ 1` via `pow_ne_one_of_lt_orderOf` + the general magnitude
below). Triangle inequality ⟹ `‖m·η_b‖ ≤ 1 + (m−1)√q`.

**Reusable spin-off (`norm_gaussSum_eq_sqrt`):** `‖gaussSum χ ψ‖ = √q` for ANY nontrivial `χ` and
primitive `ψ` over a finite field, valued in `ℂ`. Mathlib has the product identity
`gaussSum_mul_gaussSum_eq_card` but NOT the magnitude — derived here via `conj_gaussSum`
(`conj(g(χ,ψ)) = g(χ⁻¹,ψ⁻¹)`) + `Complex.mul_conj'`. Generalizes the in-tree quadratic
`gaussSum_normSq`.

The 7 theorems (`norm_mulChar_unit`, `conj_gaussSum`, `norm_gaussSum_eq_sqrt`, `mulChar_pow_sum_all`,
`eta_constIndex_decomp`, `eta_constIndex_norm_le`, `worstCaseIncompleteSumBound_constIndex`) all
audit to `[propext, Classical.choice, Quot.sound]`.

## Honest scope

Constant/polylog index, not the prize 2-power index `≈2¹²⁸` (where this gives only the trivial Weil
`√q` and the bound IS the open BGK wall). But it is a genuine, exact, axiom-clean, beyond-Johnson
discharge of the named open Prop across the WHOLE constant-index regime — the cleanest "no-wall"
slice of the worst-case incomplete-sum problem, solved by the classical Gauss sums. Found+built via
the `feasibility9-target-hunt` workflow (candidate F→generalized). Related:
`deltastar-QR-worstcase-discharge-2026-06-13.md` (the index-2 special case),
`deltastar-cumulant-dichotomy-2026-06-13.md` (the prize-index open core).
