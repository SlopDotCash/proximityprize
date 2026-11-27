# Quarter-Rate Complementary-Pencil Local-Contact Closure (`e = 536,870,914`)

This note documents the Lean-checked algebraic closure of the sole remaining Rate-`1/4`
prime-field `d = 1` list-decoding sliver (`d_{A_f} = 4`, `d_{B_f} ≤ 2`, `ω_f ∈ [5.00, 5.06]`)
at `e = 536,870,914` (`J + 1`), combining `ComplementaryListPencil.lean` and
`DrdosDiscriminantBarrier.local_contact_vanishing_equations`.

- **Lean module:** `ArkLib/Research/ProximityGap/Frontier/QuarterComplementaryContactClosure.lean`
- **Verification probe:** `scripts/probes/probe_quarter_complementary_contact_closure.py`
- **Status:** 100% kernel-checked (zero `sorry`, zero custom axioms;
  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`).

---

## 1. Core Characteristic-Free Mechanism

Suppose `y : I → K` agrees off an exceptional set `E ⊆ I` (`G = I \ E`) with a coprime rational
function `B(X) / A(X)` (`IsCoprime A B`, `A ≠ 0`, `deg A ≤ d`, `deg B ≤ 2d`), and let
`f = A_f(X, Y₀) Y₁ + B_f(X, Y₀) ∈ K[X][Y₀][Y₁]` be a candidate irreducible factor with
`deg_{Y₀}(A_f) ≤ d_A`, `deg_{Y₀}(B_f) ≤ d_B ≤ d_A`, weighted `(1, d)`-degrees `W_A, W_B`,
and local `(T, E)`-contact order `LinearLocalContactGE (dom i) (y i) A_f B_f (k i)` at each
`i ∈ G`.

Define the homogenized rational pullback
$$\operatorname{ratPullback}\; A\; B\; d_P\; P \;=\; \sum_{q=0}^{d_P} P_q(X)\, B(X)^q\, A(X)^{d_P - q} \;\in\; K[X].$$

1. **Bezout Bivariate Divisibility (`linear_dvd_of_ratPullback_eq_zero`)**:
   Over ANY commutative ring `R`, `IsCoprime A B` gives the explicit 1-line unit
   `(C u + C v * X) * C A + (-C v) * (C A * X - C B) = 1` in `BiPoly R = R[X][Y₀]`, so
   `ratPullback A B d_P P = 0` (`P.natDegree ≤ d_P`) immediately forces
   `(C A * X - C B) ∣ P` without Gauss's lemma or UFD assumptions.
2. **Step 1 — Pullback Order on `R_B` (`pow_dvd_ratPullback_of_biMultGE`)**:
   Using the exact shift identity `ratPullback_comp_shift`, `biMultGE x₀ y₀ B_f (k_i - 1)`
   (from `local_contact_vanishing_equations`) implies `(X - C x_i)^{k_i - 1} ∣ R_B` at every
   `i ∈ G`. Whenever `W_B + d_B d < ∑_{i ∈ G} (k_i - 1)`, `R_B = 0`, forcing
   `B_f = (C A * X - C B) * C_f`.
3. **Step 2 — Universal All-`k` Contact Boost on `R_A` (`pow_dvd_ratPullback_A_of_contact`)**:
   Strictly strengthening the `k = 3` boost: at ANY site `i ∈ G` where the rational Wronskian
   `W = B' A - A' B` satisfies `W(x_i) ≠ 0`, `B_f = (C A * X - C B) * C_f` forces
   `biMultGE x_i y_i C_f (k_i - 2)`, `c_{k_i - 2, 0} = 0`, and an exact telescoping cancellation
   in `[T^{k_i - 1}] R_A` (`Finset.sum_range_sub`), yielding
   **`(X - C x_i)^{k_i} ∣ R_A` for EVERY `k_i ≥ 0`** (while sites with `W(x_i) = 0` still
   satisfy `(X - C x_i)^{k_i - 1} ∣ R_A`).
4. **Step 3 — Dichotomy & Irreducibility Contradiction (`common_linear_factor_of_complementary_contact`,
   `not_irreducible_of_common_linear_factor`, `complementary_pencil_dichotomy`)**:
   - If `W = B' A - A' B = 0` (under `char K = 0 ∨ 2d < char K`), `const_of_coprime_wronskian_eq_zero`
     forces `y` constant on `G`, capping any degree-`≤ d` codeword list at `≤ 1`
     (`constant_good_set_list_le_one`).
   - Otherwise `W` has at most `3d - 1` zeros on `G` (`card_wronskian_zeros_le`). Whenever
     `W_A + d_A d + (3d - 1) < ∑_{i ∈ G} k_i`, we get `R_A = 0` and `(C A * X - C B) ∣ A_f`,
     so `(C A * X - C B)` divides BOTH `A_f` and `B_f`, contradicting irreducibility of
     `f = C A_f * X + C B_f` in `K[X][Y₀][Y₁]`.

---

## 2. Production Rate-`1/4` (`n = 2³⁰`, `e = 536,870,914`) Sliver Elimination

Because Step 2 boosts **every** `k_i ≥ 1` (not only `k_i = 3`), **neither an LP nor
`Res(A_f, B_f)` nor `Disc(A_f)` is required** for Step 1 or Step 3.

At `n = 2³⁰ = 1,073,741,824`, `d = 2²⁸ - 1 = 268,435,455`, `t = 2d = 536,870,910`,
`d_A = 4`, `d_B ≤ 2`, `|E| ≤ 3,080`, `k_i ≤ 20,000` on `E` (covering every
`m_q ∈ {160, 256, 512, 1024, ...}`), and ANY `5d ≤ W_B`, `W_A + d ≤ W_B + 1` (covering
all `ω_f ∈ [5.00, ∞)`, including the entire `[5.00, 5.06]` sliver) under a `0.04` finite-`m`
drop below `k_thr(ω_f) = 1 + (ω_f - 1)/2` (`25 ∑ k_i ≥ 50 W_B + 46 d`):

| Quantity | Degree Bound | Vanishing Order Lower Bound | Guaranteed Slack (`k_cap = 20,000`) | Guaranteed Slack (`m_q = 160`) |
| :--- | :---: | :---: | :---: | :---: |
| `R_B` (Step 1) | `W_B + 2d` | `∑_{i ∈ G} (k_i - 1)` | **`+163,885,779` roots** | **`+224,992,979` roots** |
| `R_A` (Step 3) | `W_A + 4d` | `∑_{i ∈ G} k_i - (3d - 1)` | **`+163,885,783` roots** | **`+224,992,983` roots** |

Lean theorems:
- `production_quarter_sliver_closed` — holds over ANY field `K` of characteristic `0` or
  `> 536,870,910` (including `𝔽_{P₁}`, `𝔽_{P₂}`, `AlgebraicClosure 𝔽_{P₁}`, and
  `AlgebraicClosure 𝔽_{P₂}`) and ANY length-`2³⁰` injective domain.
- `first_prime_quarter_sliver_closed` & `second_prime_quarter_sliver_closed` — direct
  instantiations for `PrizeShapePrimeP30.P` and `PrizeShapePrimeP30Second.P`.
- `complementary_pair_identities` & `complementary_derivative_pell_identity` — algebraic link
  to `ComplementaryListPencil.common_product` and the formal Derivative-Pell identity
  `(A (S + A U) - 2 B) U' = D D'`.

### Honesty Boundary
- All theorems listed above are **100% Lean-checked** with zero `sorry` and zero custom axioms.
- The extraction of `(A, B, E)` (`|E| ≤ 3,080`) from a hypothetical over-budget quarter-rate
  list (`ComplementaryListPencil` + `SupportDeficitMatrix`) and the outer prime-HD quotient-contact
  interpolation producing `f` and `k_i` remain in their respective modules (`complementary-list-pencil.md`,
  `DrdosDiscriminantBarrier.lean`, and the prime-HD Farkas track); this module supplies the complete
  kernel-checked elimination theorem closing the Rate-`1/4` sliver once `(A, B, E, f, k)` are given.
