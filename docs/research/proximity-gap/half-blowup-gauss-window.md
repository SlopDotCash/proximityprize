# Nef-Safe Blown-Up Gauss-Graph Excess Intersection and Half-Rate Safety Through 313,215,000 Errors

This note advances the second-prime half-rate MCA safety lower bound from `312,800,000`
(`half-sparse-gauss-window.md`) to **`313,215,000` errors** (first failure $\ge 313{,}215{,}001$,
a gain of `+415,000` errors) using only two ordinary mixed-Hasse surfaces on any injective domain
of length $n = 2^{30}$ over any field of characteristic $> 2^{100}$ (in particular, $p_2 = 2^{30}(2^{129} + 13) + 1$).

Two new ingredients account for the gain:

1. **Nef-safe blown-up Gauss-graph excess intersection.** Blowing up the $n$ received lines $C_x$
   on the toric resolution $\tilde{X}_0 = \operatorname{Bl}_\Sigma \mathbf{P}_{\mathbf{P}^1_X}(\mathcal{O} \oplus \mathcal{O} \oplus \mathcal{O}(-d))$
   recovers the singular excess along any $t$-site agreement set $T$ of an irreducible common nonlinear
   factor $F$, lowering the pole-degree height bound from the sparse polytope volume bound
   $(6b + 2)W - 3b^2 d$ to
   $$
   \operatorname{blowupH}(b, W, t, d)
   = (6b + 2)W - 3b^2 d - \left\lfloor \frac{3(W - t)_+^2}{t} \right\rfloor - 2(W - t)_+,
   $$
   while preserving nefness via the exact threshold $\sum_{x \in T} \lambda_x \le W$ and cancelling
   the $+i_x \lambda_x^2$ blow-up self-intersection term completely against the discarded polytope
   volume term $-3b^2 W + 2db^3$.
2. **Dual-constraint $(\alpha, \beta)$ Veronese allocation.** Projective plane-curve reflexivity
   for a degree-$s$ Veronese determinant requires $m > s(s - 1)$ on the *total companion plane degree*
   $m = \deg_{Y, Z}(F)$, not on the ordinate degree $b = \deg_Y(F)$. Pricing each nonlinear factor
   linearly as $\operatorname{pop}_i \le \alpha(j) m_i + \beta(j) b_i$ simultaneously exploits both
   degree budgets $\sum m_i \le s_2 - j$ and $\sum b_i \le v_1 - j$, unlocking degree-$s = 24$
   Veronese determinants at $j = 0$ for every ordinate degree $b \ge 2$ without paying a single
   worst-case small-$m$ price across the entire companion degree budget.

## Verification Scope

- **Lean-checked (`ArkLib/Research/ProximityGap/Frontier/HalfBlowupGaussWindow.lean`)**:
  zero `sorry`, zero custom axioms (`#print axioms` $\subseteq$ `{propext, Classical.choice, Quot.sound}`):
  - `factor_order_sum_ge`: primary weight excess $\sum_{x \in T} i_x \ge W + 1$ for any common factor $F$ carrying a section outside the primary cofactor $G_1$.
  - `volume_excess_cancel`: exact rational cancellation of the blow-up self-intersection sum $\sum i_x \lambda_x^2$ against $-3b^2 W + 2db^3$ whenever $\sum \lambda_x \le W$ and $bd \le W$.
  - `nef_weight_cauchy_schwarz`: existence of nef-admissible weights $\lambda_x \in \mathbb{Q}_{\ge 0}$ on $T$ proving both $W + 1 \le bt$ and $(W - t)^2 \le t \sum \lambda_x^2$ when $t \le W$.
  - `blowupH_ge_rat` and `blowupH_mono`: integer floor validity and monotonicity of $\operatorname{blowupH}(b, W, t, d)$ over $W \in [bd, \min(W_{\max}, bt - 1)]$.
  - `coprime_companion_fallback`: Case-1 fallback bound $|G| \le (s' + v') m$ via `DoubleInterpolationCommonFactor.exists_common` when every remaining section on $F$ lies on a coprime companion cofactor $Q'$.
  - `ranks` and `surfaces`: exact rank surpluses (`152,825,916` and `13,495,881,357`) and existence of both mixed-Hasse surfaces `(88, 124, 188604)` and `(174, 246, 14431)` at $e = 313{,}215{,}000$ on any injective length-$2^{30}$ domain.
  - `parameters`, `dual_prices`, and `allocation`: exact verification of all denominators, tame-characteristic guards, Veronese gaps, Case-1 fallback floors, dual-constraint $(\alpha, \beta)$ prices for all $j \in \{0, \dots, 124\}$ and $2 \le b \le 124 - j$, and the total bad-scalar cap **`2,145,744,452 < 2^31`** (slack **`1,739,196`**).
- **Written mathematical steps (this document, building on `half-sparse-gauss-window.md`,
  `gauss-polar-section-heights.md`, `tangent-polar-windows.md`, and `quarter-transverse-tangents.md`)**:
  - Intersection theory on the smooth toric blow-up $\hat{X} = \operatorname{Bl}_{\cup C_x}\operatorname{Bl}_\Sigma \mathbf{P}_{\mathbf{P}^1_X}(\mathcal{O}\oplus\mathcal{O}\oplus\mathcal{O}(-d))$, nefness of $M = \mathcal{L} - \sum_x \lambda_x E_x$, Cartier effectiveness of homogenized partials at $Z = \infty$, and the Gauss-graph height inequality $L \cdot A \le \tilde{F} \cdot M^2$.
  - Projective plane-curve duality, triangle/Veronese/transverse tangent windows, and factor extraction from the two Lean-constructed surfaces.
- **Independent Python verification (`scripts/probes/probe_half_blowup_gauss_window.py`)**:
  reproduces the exact integer surpluses, resultant and linear caps, and all `52,172` $(j, b, m)$ pricing checks (max `2,145,744,452` at $j = 4$, slack `1,739,196`).

---

## 1. Nef-Safe Blown-Up Gauss-Graph Excess Intersection Theorem

Let $F(X, Z, Y)$ be an irreducible common nonlinear factor of the primary and companion surfaces
with actual degrees $b = \deg_Y(F) \ge 2$, $m = \deg_{Y, Z}(F) \ge b$, and strict $(1, d)$-weighted
degree cap $W = \operatorname{wdeg}_{1, d}(F) \ge bd$, so every monomial $X^u Z^v Y^y$ in $F$
satisfies
$$
0 \le y \le b, \qquad 0 \le u \le W - dy, \qquad 0 \le v \le m - y.
$$
As in `half-sparse-gauss-window.md` (Section 2), let
$X_0 = \mathbf{P}_{\mathbf{P}^1_X}(\mathcal{O} \oplus \mathcal{O} \oplus \mathcal{O}(-d)) := \operatorname{Proj}_{\mathbf{P}^1_X}\operatorname{Sym}(\mathcal{O} \oplus \mathcal{O} \oplus \mathcal{O}(-d))$
(equivalently $\mathbf{P}_{\mathrm{sub}}(\mathcal{O} \oplus \mathcal{O} \oplus \mathcal{O}(d))$
under the subspace convention), with homogeneous fiber coordinates $[T : Z : Y]$, where
$T, Z \in H^0(X_0, H)$ and $Y \in H^0(X_0, H + dF)$ ($F$ denotes the fiber class over $\mathbf{P}^1_X$).
Since $\{T = Z = Y = 0\} = \emptyset$, we have $H^2(H + dF) = 0$, hence $H^3 = -d$, $H^2 F = 1$,
and $H F^2 = F^3 = 0$. Blow up the smooth section $\Sigma = \{T = Z = 0\} \subset X_0$ (which has
$H \cdot \Sigma = -d$) to obtain the smooth projective toric threefold
$\pi_\infty : \tilde{X}_0 = \operatorname{Bl}_\Sigma X_0 \to X_0$ with exceptional divisor
$E_\infty$ (satisfying $H \cdot E_\infty^2 = d$ and $E_\infty^3 = 2d$). As computed in
`half-sparse-gauss-window.md`,
$$
\mathcal{L} := m H + W F - (m - b) E_\infty
= (m - b)(H - E_\infty) + b(H + dF) + (W - bd) F
$$
is nef on $\tilde{X}_0$, has global sections matching the exact monomial polytope
$P = \{(u, v, y) : 0 \le y \le b,\; 0 \le u \le W - dy,\; 0 \le v \le m - y\}$, and satisfies
$$
\mathcal{L}^3 = 6\operatorname{Vol}(P) = 6 b W m - 3 b^2 (d m + W) + 2 d b^3.
$$

### 1.1 Blowing Up the Received Lines

Fix an affine chart on $\mathbf{P}^1_X$ containing the $n$ evaluation points $x \in H_{\mathrm{dom}}$
(after applying the inversion $T_{\mathrm{inv}} = (X - r)^{-1}$, $\tilde{Y} = T_{\mathrm{inv}}^d Y$
centered at any $r \notin H_{\mathrm{dom}}$, the polytope $P$ and every vanishing order along the
received lines are unchanged, while the fiber over $\infty$ is kept free of evaluation points).
In each fiber $F_x \cong \mathbf{P}^2_{[T:Z:Y]}$ over $x \in H_{\mathrm{dom}}$, the received line
$$
C_x := \{X = x,\; Y = u_0(x) T + u_1(x) Z\} \subset F_x \subset X_0
$$
is a smooth projective line **disjoint from $\Sigma = \{T = Z = 0\}$** (since $T = Z = 0$ on $C_x$
forces $Y = 0$). Hence the $n$ smooth curves $C_x$ are pairwise disjoint in $\tilde{X}_0$ and
disjoint from $E_\infty$.

Let $\pi : \hat{X} = \operatorname{Bl}_{\bigcup_x C_x} \tilde{X}_0 \to \tilde{X}_0$ be the blow-up
along the disjoint union of the $C_x$, with exceptional divisors
$E_x \cong \operatorname{Proj}\operatorname{Sym}(N_{C_x / \tilde{X}_0}^\vee)$.
Since $C_x$ is a line in a smooth fiber $F_x$ of $X_0 \to \mathbf{P}^1_X$, its normal bundle in
$\tilde{X}_0$ is
$$
N_{C_x / \tilde{X}_0} \cong N_{C_x / F_x} \oplus (N_{F_x / \tilde{X}_0})|_{C_x} \cong \mathcal{O}_{\mathbf{P}^1}(1) \oplus \mathcal{O}_{\mathbf{P}^1},
\qquad
N_{C_x / \tilde{X}_0}^\vee \cong \mathcal{O}_{\mathbf{P}^1}(-1) \oplus \mathcal{O}_{\mathbf{P}^1}.
$$
Thus $E_x \cong \mathbf{F}_1$ (the Hirzebruch surface with negative section $s_0$ of self-intersection
$s_0^2 = -1$ and fiber class $f$ with $f^2 = 0$, $s_0 \cdot f = 1$). Because
$h^0(E_x, \mathcal{O}_{E_x}(1)) = h^0(\mathbf{P}^1, \mathcal{O}(-1) \oplus \mathcal{O}) = 1$, we
have $\mathcal{O}_{E_x}(1) = s_0$ (matching the strict-transform restriction $\tilde{F}_x|_{E_x} = s_0$).
The standard blow-up intersection numbers for a smooth curve $C_x \subset \tilde{X}_0$ are:
- $E_x \cdot E_{x'} = 0$ and $E_x \cdot E_\infty = 0$ for all $x \ne x'$;
- $\mathcal{L} \cdot E_x = (\mathcal{L} \cdot C_x) f = m f$ on $E_x$, because $C_x$ is a line in $F_x$
  disjoint from $E_\infty$, so $H \cdot C_x = 1$, $F \cdot C_x = 0$, $E_\infty \cdot C_x = 0$, giving
  $\mathcal{L} \cdot C_x = m$;
- $E_x|_{E_x} = \mathcal{O}_{E_x}(-1) = -s_0$, so
  $$
  E_x^3 = (-s_0)^2 = -1, \qquad
  \mathcal{L} \cdot E_x^2 = (m f) \cdot (-s_0) = -m, \qquad
  \mathcal{L}^2 \cdot E_x = 0.
  $$

### 1.2 Exact Vanishing Orders of $F$ and Its Partials Along $C_x$ (Including $Z = \infty$)

For each site $x \in H_{\mathrm{dom}}$, let $i_x = \operatorname{ord}_{C_x}(F) \in \mathbb{N}$ be the
multiplicity of the divisor $\{F = 0\}$ along $C_x$. Because $F$ is irreducible of $Y$-degree
$b \ge 2$, we have $X - x \nmid F$, so the fiber restriction $F(x, Z, Y)$ is not identically zero;
hence $i_x \le \operatorname{ord}_{C_x}(F|_{F_x}) \le \deg_Y F(x, Z, Y) \le b$.

Crucially, **all three homogenized partial derivatives defining the Gauss map lie in the common
linear system $|\mathcal{L} - \sum_x (i_x - 1)_+ E_x|$ everywhere on $\hat{X}$, including at the
point at infinity $[0 : 1 : u_1(x)] \in C_x$**:
- Homogenize $F$ in $(X_0, X_1)$ (with $X = X_1/X_0$) and $(T, Z, Y)$ to a global section
  $\bar{F} \in H^0(\tilde{X}_0, \mathcal{L})$. The three sections
  $$
  S_X := X_0 \partial_{X_1} \bar{F}, \qquad
  S_Y := X_0^d T \partial_Y \bar{F}, \qquad
  S_Z := T \partial_Z \bar{F}
  $$
  all lie in the common bundle $H^0(\tilde{X}_0, \mathcal{L})$ and represent the Gauss map
  $[S_X : S_Y : S_Z] = [F_X : F_Y : F_Z]$ on the affine chart $\{X_0 = 1,\; T = 1\}$.
- Locally around any finite point of $C_x$ ($X_0 = 1, T = 1$), write $s = X - x$, $z = Z/T$, and
  $w = Y/T - u_0(x) - u_1(x) z$. Every monomial in $F$ expands in $(s, w)$ with $z$-polynomial
  coefficients, and $F \in (s, w)^{i_x}$. Differentiating gives
  $S_X = \partial_s F$, $S_Y = \partial_w F$, and $S_Z = \partial_z F - u_1(x) \partial_w F$,
  all of which belong to $(s, w)^{(i_x - 1)_+}$.
- Around the point at infinity $[T : Z : Y] = [0 : 1 : u_1(x)] \in C_x$ (on $\{X_0 = 1\}$), set
  $t' = T/Z$ and $\tilde{w} = Y/Z - u_0(x) t' - u_1(x)$. Because $C_x$ is disjoint from $\Sigma$,
  $(s, t', \tilde{w})$ are regular local coordinates on $\tilde{X}_0$ with ideal
  $I_{C_x} = (s, \tilde{w})$, and $\bar{F} = Z^m \tilde{F}(s, t', \tilde{w})$ with
  $\tilde{F} \in (s, \tilde{w})^{i_x}$. Direct differentiation (noting that the $u_0(x) t'$ term
  cancels in $\partial_Z \bar{F}$ via $-\frac{Y}{Z^2} + u_0(x)\frac{T}{Z^2} = -\frac{1}{Z}(\tilde{w} + u_1(x))$)
  yields
  $$
  S_X = Z^m \partial_s \tilde{F}, \qquad
  S_Y = Z^m t' \partial_{\tilde{w}} \tilde{F}, \qquad
  S_Z = Z^m t'\bigl(m \tilde{F} - t' \partial_{t'} \tilde{F} - (\tilde{w} + u_1(x))\partial_{\tilde{w}}\tilde{F}\bigr),
  $$
  every one of which belongs to $Z^m (s, \tilde{w})^{(i_x - 1)_+}$. Pulling back to $\hat{X}$, all
  three sections $S_X, S_Y, S_Z$ lie in $H^0(\hat{X}, \mathcal{L} - \sum_x (i_x - 1)_+ E_x)$.

### 1.3 Exact Nefness Criterion on $\hat{X}$

**Lemma (Nef-Safe Blow-Up Divisor).** *Let $\lambda_x \in \mathbb{Q}_{\ge 0}$ ($x \in H_{\mathrm{dom}}$)
satisfy*
$$
0 \le \lambda_x \le \min\bigl((i_x - 1)_+,\, b\bigr) \quad \forall x,
\qquad\text{and}\qquad
\sum_{x \in H_{\mathrm{dom}}} \lambda_x \le W.
$$
*Then the $\mathbb{Q}$-divisor $M := \mathcal{L} - \sum_x \lambda_x E_x$ is **nef** on $\hat{X}$.*

*Proof.* Let $C \subset \hat{X}$ be any irreducible projective curve. We check $M \cdot C \ge 0$ in
all four exhaustive cases for the position of $C$:

1. **$C \subset E_x$ for some $x$.** Since $E_x \cap E_{x'} = \emptyset$ for $x' \ne x$ and
   $E_x|_{E_x} = -s_0$,
   $$
   M|_{E_x} = \mathcal{L}|_{E_x} - \lambda_x E_x|_{E_x}
   = \lambda_x s_0 + m f
   \quad\text{on } E_x \cong \mathbf{F}_1.
   $$
   On $\mathbf{F}_1$, the nef cone is $\{a s_0 + c f : a \ge 0,\; c \ge a\}$. Here $a = \lambda_x \ge 0$
   and $c = m \ge b \ge \lambda_x$ (using $b \le m$), so $M|_{E_x}$ is nef and $M \cdot C \ge 0$.
2. **$C \subset E_\infty$.** Since $E_\infty$ is disjoint from every $E_x$, we have $E_x \cdot C = 0$
   for all $x$, so $M \cdot C = \mathcal{L} \cdot C \ge 0$ because $\mathcal{L}$ is nef on $\tilde{X}_0$.
3. **$C \subset \tilde{F}_x$ (the strict transform of a fiber $F_x \cong \mathbf{P}^2$ over $x$) with
   $C \not\subset E_x, E_\infty$.** Let $C' = \pi(C) \subset F_x$ be the image plane curve of degree
   $k = H \cdot C' \ge 1$ passing through the point $\Sigma \cap F_x = [0 : 0 : 1]$ with multiplicity
   $\mu_\infty = E_\infty \cdot C \le k$ (in fact, since $C' \not\subset C_x$ or if $C' = C_x$):
   - If $C' \ne C_x$, then $C'$ meets the line $C_x$ in at most $k$ points (counted with multiplicity),
     so $E_x \cdot C \le C' \cdot_{F_x} C_x = k$ and $E_{x'} \cdot C = 0$ ($x' \ne x$). Meanwhile,
     since $\mathcal{L} = (m - b)(H - E_\infty) + b(H + dF) + (W - bd)F$ and $H - E_\infty$ is nef
     (it pulls back from $\mathbf{P}^1_{[T:Z]}$), we have $\mathcal{L} \cdot C \ge b(H \cdot C') = b k$.
     Hence $M \cdot C \ge (b - \lambda_x) k \ge 0$ because $\lambda_x \le b$.
   - Notice $C'$ cannot equal $C_x$ because $\tilde{F}_x \cong \operatorname{Bl}_{C_x \cap F_x} F_x = F_x$
     (blowing up the Cartier divisor $C_x \subset F_x$ is an isomorphism on $F_x$), so the inverse
     image of $C_x$ inside $\tilde{F}_x$ is the single curve $\tilde{F}_x \cap E_x \subset E_x$,
     already covered by Case 1.
4. **$C$ dominates $\mathbf{P}^1_X$, with projection degree $k := F \cdot C \ge 1$.**
   Because $H - E_\infty$ is base-point-free on $\tilde{X}_0$ (pulling back from $\mathbf{P}^1_{[T:Z]}$),
   $(H - E_\infty) \cdot C \ge 0$. Since $C \not\subset E_\infty$, its image $\pi(C)$ is not contained
   in $\Sigma = \{T = Z = 0\}$, so a general section $a T + b Z \in H^0(X_0, H)$ meets $\pi(C)$ properly
   and $H \cdot C \ge 0$. Writing $\mathcal{L} = (m - b)(H - E_\infty) + b H + W F$ gives
   $$
   \mathcal{L} \cdot C = (m - b)(H - E_\infty) \cdot C + b(H \cdot C) + W(F \cdot C) \ge W k.
   $$
   Meanwhile, for each $x$, the strict transform $\tilde{F}_x = \pi^* F_x - E_x$ is an effective
   divisor not containing $C$ (as $C$ dominates $\mathbf{P}^1_X$), so $\tilde{F}_x \cdot C \ge 0$,
   i.e., $E_x \cdot C \le F_x \cdot C = k$. Summing over $x$ yields
   $$
   M \cdot C = \mathcal{L} \cdot C - \sum_x \lambda_x (E_x \cdot C)
   \ge W k - \Bigl(\sum_x \lambda_x\Bigr) k
   = \Bigl(W - \sum_x \lambda_x\Bigr) k \ge 0. \qquad\square
   $$

> **Why $\sum_x \lambda_x \le W$ cannot be omitted (non-nef counterexample).**
> Taking $\lambda_x = i_x - 1$ simultaneously on *all* $n$ sites without capping $\sum_x \lambda_x \le W$
> is **false**: for $F(X, Z, Y)$ homogeneous of degree $r = b = m = 5$ in $(Z, Y)$ with $d = 1$,
> $W = 100$, and $n = 39$ sites (where $u_0 = u_1 = 0$), the interpolation space has $591 > 585$
> monomials over constraints, yet the unguarded formula gives $6\operatorname{Vol}(P) - n\cdot\text{excess}
> = 7375 - 7800 = -425 < 0 \le L \cdot A$. The failure is exact: the curve $C = \{Z = Y = 0\} \subset \tilde{X}_0$
> has $F \cdot C = 1$, $\mathcal{L} \cdot C = W = 100$, $E_x \cdot C = 1$, so $M \cdot C = 100 - 4 \cdot 39 = -56 < 0$.
> Enforcing $\sum_x \lambda_x \le W$ restores $M \cdot C \ge 0$ on every curve (giving $+2375 > 0$ on
> the same example) and has been cross-checked against exact $\mathbb{F}_{10^9 + 7}$ resultant counts.

### 1.4 Gauss-Graph Intersection Bound and Volume-Excess Cancellation

Let $\tilde{F} \in |\mathcal{L} - \sum_x i_x E_x|$ be the strict transform of $\{F = 0\}$ on $\hat{X}$,
and let $\nu : \hat{S} \to \tilde{F}$ be the normalization of the Gauss graph of $F$ (blowing up the
base locus of the rational Gauss map $\gamma : \tilde{F} \dashrightarrow \mathbf{P}^2$). Write $L$ for
the movable pullback of $\mathcal{O}_{\mathbf{P}^2}(1)$ via $\gamma$ and $A$ for the pullback of the
polar linear system generated by the homogenized partials. Because every generating section of both
$L$ and $A$ comes from $H^0(\hat{X}, \mathcal{L} - \sum_x (i_x - 1)_+ E_x) \subset H^0(\hat{X}, M)$
(since $\lambda_x \le (i_x - 1)_+$), both $M|_{\hat{S}} - L$ and $M|_{\hat{S}} - A$ are effective
Cartier $\mathbb{Q}$-divisors on $\hat{S}$. Since $A$ and $M|_{\hat{S}}$ are nef on $\hat{S}$,
$$
L \cdot A \le M|_{\hat{S}} \cdot A \le (M|_{\hat{S}})^2 = \tilde{F} \cdot M^2.
$$
Expanding $\tilde{F} \cdot M^2 = (\mathcal{L} - \sum_x i_x E_x)(\mathcal{L} - \sum_x \lambda_x E_x)^2$
using $\mathcal{L}^2 E_x = 0$, $\mathcal{L} E_x^2 = -m$, $E_x^3 = -1$, and $E_x E_{x'} = 0$ ($x \ne x'$) yields:
$$
\tilde{F} \cdot M^2
= \mathcal{L}^3 - \sum_x \Bigl((2 i_x \lambda_x + \lambda_x^2) m - i_x \lambda_x^2\Bigr)
= 6 b W m - 3 b^2 (d m + W) + 2 d b^3 - \sum_x \Bigl((2 i_x \lambda_x + \lambda_x^2) m - i_x \lambda_x^2\Bigr).
$$
Now apply the Lean-checked algebraic cancellation (`HalfBlowupGaussWindow.volume_excess_cancel`):
for every $x$, $0 < \lambda_x \implies \lambda_x + 1 \le i_x \le b$, so
$2 i_x \lambda_x + \lambda_x^2 \ge 3 \lambda_x^2 + 2 \lambda_x$ and $i_x \lambda_x^2 \le b^2 \lambda_x$.
Under $\sum_x \lambda_x \le W$ and $bd \le W$,
$$
\sum_x i_x \lambda_x^2 \le b^2 \sum_x \lambda_x \le b^2 W \le 3 b^2 W - 2 d b^3,
$$
so the entire $+i_x \lambda_x^2$ blow-up self-intersection term is absorbed by the previously discarded
$-3b^2 W + 2db^3$ polytope volume term! Combining with the remaining polar-to-Gauss height term
$L \cdot H_Y \le 2 W m$ (from `half-sparse-gauss-window.md`, Eq. (3)) yields the per-unit-$m$ height
bound
$$
\frac{H_{\mathrm{pole}}(F)}{m} \le 6 b W - 3 b^2 d + 2 W - 3 \sum_x \lambda_x^2 - 2 \sum_x \lambda_x.
$$

### 1.5 Two-Case Factor Assignment and Monotonicity of `blowupH`

Assign witnessing sections $(z, q_z)$ in order to the five non-nonlinear label classes first:
(1) rich polynomial affine heads (the $j$ heads with $> s_1$ sections), (2) scalar-only primary factors,
(3) noncommon sections (bounded by the single resultant $s_1 v_2 + v_1 s_2$), (4) small polynomial
affine heads (at most $(v_1 - j) s_1$), and (5) common nonaffine linear factors (at most $(s_2 - j) \cdot 21$
at half-rate, via `4n ≤ 20(t - d)`). After dividing out the $j$ rich heads with their full multiplicities $m_a \ge 1$ from $Q_2$
(and at least once from $P_1$), let $F$ be an irreducible common nonlinear factor ($2 \le b \le m$)
with $Q_2 = \bigl(\prod_{a=1}^j (Y - h_a)^{m_a}\bigr) F^{k_2} G_2$ ($k_2 \ge 1$, $F \nmid G_2$)
carrying a nonempty set of remaining sections. Notice that $F$ also divides
$P_1 / \prod_{a=1}^j (Y - h_a)$, so its $(1, d)$-weighted degree satisfies $W \le 88 t - 1 - j d$.
Splitting on the companion cofactor $G_2$ (which satisfies $\deg_Y G_2 \le v_2 - j$ and
$\deg_{Y, Z} G_2 \le s_2 - j$) yields two exhaustive cases:

- **Case 1 (every remaining section on $F$ also lies on $G_2$):**
  Since $F$ and $G_2$ are coprime of degrees $(b, m)$ and $(\le v_2 - j, \le s_2 - j)$ with $b \le m$,
  `HalfBlowupGaussWindow.coprime_companion_fallback` bounds the number of remaining sections on $F$
  by $((s_2 - j) + (v_2 - j)) m$, which `dual_prices` verifies is $\le \alpha(j) m$ for every $j$.
- **Case 2 (some remaining section $(z, q_z)$ on $F$ does not lie on $G_2$):**
  Pick any $t$-element subset $T \subseteq S_z$ of the agreement set of $(z, q_z)$. Set
  $G_2' := \bigl(\prod_{a=1}^j (Y - h_a)^{m_a}\bigr) G_2$, so $Q_2 = F^{k_2} G_2'$ with
  $k_2 W + W_{G_2'} < r_2 t$. Because $(z, q_z)$ was not assigned to any rich head and does not lie
  on $G_2$, we have $G_2'(X, z, q_z(X)) \not\equiv 0$ of degree $\le W_{G_2'}$, so its vanishing
  orders $j'_{2, x}$ along $C_x$ satisfy $\sum_{x \in T} j'_{2, x} \le W_{G_2'}$ while
  $k_2 i_x + j'_{2, x} \ge r_2$ at every $x \in T$.
  By `HalfBlowupGaussWindow.factor_order_sum_ge` applied to $Q_2 = F^{k_2} G_2'$ ($r = r_2 = 174$),
  $$
  \sum_{x \in T} i_x \ge W + 1.
  $$
  Applying `HalfBlowupGaussWindow.nef_weight_cauchy_schwarz` then proves $W \le b t - 1$ and constructs
  nef-admissible rational weights $\lambda_x = \min(1, W/U)(i_x - 1)_+$ on $T$ (with $U = \sum_{x \in T}(i_x - 1)_+$)
  satisfying $\sum_{x \in T} \lambda_x \in [(W - t)_+, W]$ and $\sum_{x \in T} \lambda_x^2 \ge (W - t)_+^2 / t$.
  Finally, `HalfBlowupGaussWindow.blowupH_ge_rat` and `HalfBlowupGaussWindow.blowupH_mono`
  (using $b d \le W \le \min(88 t - 1 - j d,\, b t - 1)$) yield
  $$
  \frac{H_{\mathrm{pole}}(F)}{m} \le \operatorname{blowupH}\!\bigl(b,\, \min(88 t - 1 - j d,\, b t - 1),\, t,\, d\bigr)
  =: \operatorname{maxBlowupH}(j, b).
  $$

---

## 2. Dual-Constraint $(\alpha, \beta)$ Veronese Allocation at `e = 313,215,000`

### 2.1 Production Parameters

At $n = 2^{30} = 1{,}073{,}741{,}824$, $d = 2^{29} - 1 = 536{,}870{,}911$, $e = 313{,}215{,}000$,
$t = n - e = 760{,}526{,}824$, $\mathrm{miss} = 4096$, $\mathrm{core} = t - \mathrm{miss} = 760{,}522{,}728$:

| Surface | Order $r$ | Ordinate deg $b$ | Total deg $s$ | Columns | Constraints | Rank Surplus |
|---|---:|---:|---:|---:|---:|---:|
| Primary $P_1$ | `88` | `124` | `188,604` | `647,068,595,487,212,672` | `647,068,595,334,386,756` | **`152,825,916`** |
| Companion $Q_2$ | `174` | `246` | `14,431` | `192,299,839,077,679,552` | `192,299,839,064,183,671` | **`13,495,881,357`** |

Non-nonlinear fixed overhead (`otherLabels(j)`):
- Scalar-only primary factors: $\le 188{,}604$.
- Single resultant (noncommon sections): $\le 188{,}604 \cdot 246 + 124 \cdot 14{,}431 = 48{,}186{,}028$.
- Small polynomial affine heads: $\le (124 - j) \cdot 188{,}604$.
- Common nonaffine linear factors: $\le (14{,}431 - j) \cdot 21$ (since $4n \le 20(t - d)$).
- Rich polynomial affine heads: `headMass(j)` using $\max(\mathrm{discreteUnion}(j), \lceil j \cdot \mathrm{core}^2 / (\mathrm{core} + (j - 1)d) \rceil)$
  with $a \in \{\lfloor 7j/10 \rfloor, \lfloor (7j+9)/10 \rfloor\}$.

### 2.2 Veronese Regimes and Dual Pricing

For $j = 0$, we apply three Veronese determinant ladders $(s, a, h, C_a, E_s)$ from `tangent-polar-windows.md`:

| Veronese $(s, a)$ | $h = \binom{s+2}{2}$ | $C_a = \binom{a+2}{3}$ | $E_s = \frac{s(s+1)(s+2)}{3}$ | Reflexivity guard $m > s(s-1)$ |
|---|---:|---:|---:|---:|
| `(6, 5)` | `28` | `35` | `112` | `m > 30` |
| `(12, 10)` | `91` | `220` | `728` | `m > 132` |
| `(24, 20)` | `325` | `1,540` | `5,200` | `m > 552` |

At $j = 0$, set $\alpha(0) = 131{,}427$ and $\beta(0) = 27{,}182$. For every $2 \le b \le 124$:
- If $m > 552$: $\operatorname{price24}(b) \le \alpha(0)$, so $m \cdot \operatorname{price24}(b) \le m \alpha(0) + b \beta(0)$.
- If $132 < m \le 552$: $m(\operatorname{price12}(b) - \alpha(0))_+ \le 552(\operatorname{price12}(b) - \alpha(0))_+ \le b \beta(0)$.
- If $30 < m \le 132$: $m(\operatorname{price6}(b) - \alpha(0))_+ \le 132(\operatorname{price6}(b) - \alpha(0))_+ \le b \beta(0)$.
- If $b \le m \le 30$: $m(\operatorname{basePrice}(0, b) - \alpha(0))_+ \le 30(\operatorname{basePrice}(0, b) - \alpha(0))_+ \le b \beta(0)$.

For $j \ge 1$, $\beta(j) = 0$ and the triangle ($j \in \{1, 2\}$) plus transverse ($j \ge 3$) tangent
windows already satisfy $\operatorname{basePrice}(j, b) \le \alpha(j) = \lfloor (\mathrm{bound} - \mathrm{otherLabels}(j)) / (14{,}431 - j) \rfloor$
uniformly across all $2 \le b \le 124 - j$.

Summing over all common nonlinear factors $(b_i, m_i)$ with $\sum m_i \le 14{,}431 - j$ and
$\sum b_i \le 124 - j$ proves (`HalfBlowupGaussWindow.allocation`):
$$
\text{total bad scalars} \le \mathbf{2{,}145{,}744{,}452} < 2^{31} = 2{,}147{,}483{,}648
$$
with maximum attained at $j = 4$ and **`1,739,196`** bad scalars to spare.

### 2.3 Selected $j$-Profile

| $j$ | Regime | `otherLabels(j)` | $\alpha(j)$ | $\beta(j)$ | Total Cap | Slack below $2^{31}$ |
|---:|---|---:|---:|---:|---:|---:|
| `0` | Blow-up + Veronese `(6,12,24)` dual $(\alpha,\beta)$ | `72,064,499` | `131,427` | `27,182` | `1,972,058,084` | `175,425,564` |
| `1` | Blow-up + 1-head triangle | `385,090,896` | `122,013` | `0` | `2,145,738,486` | `1,745,162` |
| `2` | Blow-up + 2-head triangle | `698,117,293` | `100,327` | `0` | `2,145,735,676` | `1,747,972` |
| `3` | Blow-up + transverse | `991,341,286` | `80,011` | `0` | `2,145,740,004` | `1,743,644` |
| `4` | Blow-up + transverse (**peak**) | `1,069,144,104` | `74,623` | `0` | **`2,145,744,452`** | **`1,739,196`** |
| `5` | Blow-up + transverse | `1,073,081,383` | `74,356` | `0` | `2,145,741,919` | `1,741,729` |
