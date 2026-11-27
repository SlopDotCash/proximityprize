# Smooth Coset-Folding List Descent, Saturated Three-Split Pencils, and Multi-Step Inclusion Bounds

## Overview

In [`CarbonListSmoothFoldedRigidity.lean`](../../../ArkLib/Research/ProximityGap/Frontier/CarbonListSmoothFoldedRigidity.lean)
(companion arithmetic verifier:
[`probe_carbon_list_smooth_folded_rigidity.py`](../../../scripts/probes/probe_carbon_list_smooth_folded_rigidity.py)),
we develop three structural and quantitative tools for all-center Reed–Solomon list decoding beyond
the finite-length Johnson radius:

1. **Exact $m$-way power-fiber coset folding and defect-sensitive list descent** on smooth and
   regularly fibered evaluation domains (`sum_foldSlice_comp`, `eval_eq_on_fiber_iff_folded`,
   `folded_family_card_le_base_lambda`, `smooth_folded_low_error_lambda_le`).
2. **Algebraic common-$(k - 1)$-core star bounds and saturated-triangle / $4$-clique three-split
   locator pencil reductions** (`common_core_star_bound`, `saturated_triangle_three_split_pencil`,
   `saturated_four_clique_forces_three_split_pencil`), separating actual Reed–Solomon lists from
   purely combinatorial constant-weight $(n, t, k - 1)$ set systems
   ([`QuarterSupportPackingBarrier.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSupportPackingBarrier.lean)).
3. **Multi-step mixed inclusion–omission bounds at $J + 2$ and $J + 3$** (`rate_eighth_johnson_plus_two`,
   `rate_eighth_johnson_plus_three`, `rate_sixteenth_johnson_plus_two`,
   `rate_sixteenth_johnson_plus_three`, and the all-$k$, all-$s$ algebraic slack law
   `rate_sixteenth_inclusion_family_gap`), improving pure omission
   ([`MultipleOmissionJohnson.lean`](../../../ArkLib/Research/ProximityGap/Frontier/MultipleOmissionJohnson.lean))
   by **$2.65\times$ to $15.57\times$** across all fields, injective domains, and interleaving widths.

## 1. Exact $m$-Way Coset Folding and Fiber-Error Excess Accounting

For any $m \ge 1$ and any polynomial $P \in F[X]$ of degree $< m k$, the $m$ folded slices
$$P_r(Z) = \sum_{q = 0}^{k - 1} [X^{q m + r}] P(X) \cdot Z^q \qquad (0 \le r < m)$$
have $\deg P_r < k$ and satisfy $P(X) = \sum_{r = 0}^{m - 1} X^r P_r(X^m)$ (`sum_foldSlice_comp`).
On any $m$-element fiber $F_z \subseteq I$ where $D(i)^m = z$, applying
`Lagrange.eq_interpolate_iff` to $Q_z(X) = \sum_{r = 0}^{m - 1} P_r(z) X^r$ shows that full-fiber
agreement is equivalent to folded column agreement (`eval_eq_on_fiber_iff_folded`):
$$\bigl(\forall i \in F_z,\; P(D(i)) = y(i)\bigr) \;\Longleftrightarrow\;
  \forall r \in \operatorname{Fin} m,\; P_r(z) = \bigl(\operatorname{Lagrange.interpolate}(F_z, D, y)\bigr)_r.$$

Defining the fiber multi-error excess
$$\operatorname{fiberErrorExcess}(\pi, c, y) := \sum_{v \in J}
  \bigl(\lvert\{i \in I \mid \pi(i) = v \wedge c(i) \ne y(i)\}\rvert - 1\bigr)$$
(in truncated natural subtraction) yields the exact identity (`hammingDist_add_fiberExcess_eq`)
$$\Delta_H(\widetilde{c}, \widetilde{y}) + \operatorname{fiberErrorExcess}(\pi, c, y) = \Delta_H(c, y).$$
Consequently, any finite family of `width`-interleaved codewords on $D$ with
$\Delta_H(c, y) \le e_{\mathrm{fib}} + \operatorname{fiberErrorExcess}(\pi, c, y)$ injects into the
radius-$(e_{\mathrm{fib}} / |J|)$ ball of the $(m \cdot \text{width})$-interleaved RS code of
degree $< k$ on the base domain $E$ (`folded_family_card_le_base_lambda`), and on every smooth
domain of size $m \cdot h$ (`smooth_folded_low_error_lambda_le`),
$$\Lambda\bigl(\operatorname{RS}(D, m k)^{\bowtie \text{width}},\, \tfrac{e}{m h}\bigr) \;\le\;
  \Lambda\bigl(\operatorname{RS}(D^{(m)}, k)^{\bowtie (m \cdot \text{width})},\, \tfrac{e}{h}\bigr).$$

## 2. Common-Core Star Cap and Saturated Three-Split Locator Pencils

- **Common $(k - 1)$-core star bound (`common_core_star_bound`)**: If $r$ distinct
  `width`-interleaved codewords of degree $< k$ agree with $y$ on sets $S_a$ ($|S_a| \ge t$)
  containing a common $(k - 1)$-subset $W$, then $S_a \setminus W$ are pairwise disjoint in
  $I \setminus W$, so $r(t - (k - 1)) \le |I| - (k - 1)$. At $n = 2^{30}$ (`J + 1`), this caps
  common-$(k - 1)$ stars at $r \le 2$ (rate $1/2$) and $r \le 3$ (rates $1/4$ and $1/8$).
- **Saturated-triangle three-split pencil (`saturated_triangle_three_split_pencil`)**: Three
  distinct scalar codewords $P_0, P_1, P_2$ of degree $< k$ with $|S_a \cap S_b| = k - 1$ and
  triple core $W = S_0 \cap S_1 \cap S_2$ of size $w < k - 1$ produce three pairwise disjoint sets
  $A, B, C_{\mathrm{set}} \subseteq I \setminus W$ of size $m = k - 1 - w \ge \max(1,\, 3t - 2(k - 1) - |I|)$
  ($m \ge 130{,}266{,}726$ at rate $1/2$ `J + 1`) and $\mu \in F \setminus \{0, 1\}$ with
  $$\operatorname{nodal}(C_{\mathrm{set}}, D) = \mu \cdot \operatorname{nodal}(A, D) + (1 - \mu) \cdot \operatorname{nodal}(B, D).$$
- **Saturated $4$-clique consequence (`saturated_four_clique_forces_three_split_pencil`)**: Whenever
  $|I| - (k - 1) < 4(t - (k - 1))$ (rates $1/2, 1/4, 1/8$ at $n = 2^{30}$ `J + 1`), no four
  codewords can share a $(k - 1)$-core, so every saturated $K_4$ (such as the one forced at
  rate $1/8$ `J + 1` above $B_1 = 2^{30}$ in
  [`SaturatedListCliques.lean`](../../../ArkLib/Research/ProximityGap/Frontier/SaturatedListCliques.lean))
  unconditionally forces a positive-degree three-split monic locator pencil on $D$.

## 3. Multi-Step Mixed Inclusion–Omission Bounds ($n = 2^{30}$)

At rate $1/16$ ($n = 16 k, d = k - 1$) and $t = 4k - 2 - s$ (`Johnson + s` errors), pure $s$-site
inclusion ($r = 0$) obeys the exact identity (`rate_sixteenth_inclusion_family_gap`):
$$(4k - 2 - 2s)^2 = (16k - s)(k - 1 - s) + \bigl(s k + (3s + 4)(s + 1)\bigr) > (16k - s)(k - 1 - s).$$

| Production step ($n = 2^{30}$) | Errors $e$ | Pure omission (`s = 0`) | Mixed `(s, r)` | Certified all-width bound $B$ | Gain |
| :--- | :---: | ---: | :---: | ---: | :---: |
| Rate $1/8$, `J + 2` | $694{,}116{,}764$ | $22{,}763{,}326{,}668$ ($21.20\,n$) | $(2, 0)$ | **$8{,}589{,}934{,}703$** ($8.00\,n$) | $2.65\times$ |
| Rate $1/8$, `J + 3` | $694{,}116{,}765$ | $201{,}608{,}069{,}100$ ($187.76\,n$) | $(3, 2)$ | **$58{,}139{,}264{,}338$** ($54.15\,n$) | $3.47\times$ |
| Rate $1/16$, `J + 2` | $805{,}306{,}372$ | $142{,}842{,}804{,}084$ ($133.03\,n$) | $(2, 0)$ | **$17{,}179{,}869{,}712$** ($16.00\,n$) | $8.31\times$ |
| Rate $1/16$, `J + 3` | $805{,}306{,}373$ | $1{,}070{,}112{,}682{,}879$ ($996.62\,n$) | $(3, 0)$ | **$68{,}719{,}480{,}960$** ($64.00\,n$) | $15.57\times$ |

*Context vs. degree-3 Hahn LP (`J + 2`)*: Note that at `J + 2`,
[`CubicHahnJohnson.lean`](../../../ArkLib/Research/ProximityGap/Frontier/CubicHahnJohnson.lean)
on `main` already certifies tighter degree-$3$ Hahn polynomial LP list bounds (`5,744,500,761` =
$5.35\,n$ at rate $1/8$ and `7,874,106,789` = $7.33\,n$ at rate $1/16$). The table above isolates
the pure combinatorial `(s, r)` inclusion–omission gains over `MultipleOmissionJohnson` and supplies
new explicit `J + 3` bounds (`58.14B` at rate $1/8$ and `68.72B` at rate $1/16$).
