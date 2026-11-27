# General homothetic-cover obstructions and 3+1 pencil-degree barrier at eighth rate

This note and its Lean companion [`EighthRationalCoverObstructions.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthRationalCoverObstructions.lean) push Target A (`671,088,640` errors) and Target B (`679,477,248` ceiling) beyond group-action symmetries to **completely arbitrary (non-Galois, non-dihedral, non-monomial) homothetic covers** and prove the exact `3 + 1` pencil-degree barrier below `679,477,248`.

## 1. Universal homothetic fiber theorem (`homothetic_fiber_universal`)

Earlier (`EighthDyadicHeadDirections.lean`), `two_stars` proved $2 M + 3 W \le 16$ for a pair of homothetic regular sites ($|S| = 2$). We generalize this to **any nonempty finite fiber $S$ of arbitrary size $|S| \ge 1$**: for any 4-point multiset $(P, w)$ ($\sum_{i \in P} w(i) = 4$, $w(i) \ge 1$) with symmetric direction map $\operatorname{dir}$, and any nonempty finite family $S$ of regular centers $u : S \to P$ with $w(u(x)) \le 2$,
$$
2 \left|\bigcup_{x \in S} \operatorname{star}(P, \operatorname{dir}, u(x))\right| + 3 \sum_{x \in S} w(u(x)) \;\le\; 6\,|S| + 4.
$$
The proof handles every multiset partition of $4$:
- $|P| = 2$ ($w = (2,2)$): at most $1$ direction total ($M \le 1$, $W = 2|S| \implies 2M + 3W \le 6|S| + 2$).
- $|P| = 3$ ($w = (2,1,1)$): at most $3$ directions total ($M \le 3$); if every $x \in S$ picks the unique weight-$2$ center, all share one star of size $\le 2$ ($2(2) + 3(2|S|) = 6|S| + 4$), otherwise $W \le 2|S| - 1$ ($2(3) + 3(2|S| - 1) = 6|S| + 3$).
- $|P| = 4$ ($w = (1,1,1,1)$): $W = |S|$ and $M \le 6$ (`card_biUnion_star_le_choose_two`), giving $2M + 3W \le 12 + 3|S| \le 6|S| + 4$ for $|S| \ge 3$ and $9, 16$ for $|S| = 1, 2$.

## 2. Arbitrary homothetic-cover image and partial-involution floors (`0 ≤ s ≤ 4`)

Suppose the four heads' projective directions of *any* near-saturated ($0 \le s \le 4$) overrun at $e = 671{,}088{,}640$ factor through *any* map $h : H \to T$ (no Galois, monomial, or dihedral assumption), with at most $12$ exceptional sites $H_{\mathrm{exc}}$ covering $Z(h_{\mathrm{loc}}) \cup X_0 \cup X_3 \cup X_4$. Summing `homothetic_fiber_universal` over all regular fibers $y \in h(H_{\mathrm{reg}})$ and using $M_x + W_x \le 4 \implies 2 M_x + 3 W_x \le 12$ on $H_{\mathrm{exc}}$ yields (`homothetic_cover_mass_bound`, `homothetic_cover_image_floors`, `partial_involution_cap`, Lean-checked):

| Residual regime at `671,088,640` | Min regular image `\|h(H_reg)\|` | Min isolated singleton fibers | Max disjoint homothetic pairs `P` |
|---|---:|---:|---:|
| Baseline (`other ≤ 20,607,410`) | **`660,784,912`** (`> 0.615 n`) | **`247,828,000`** (`> 0.230 n`) | **`412,956,912`** (`< 0.385 n`) |
| Sparse-Gauss (`other ≤ 397,364`, [`EighthSuccessorTightWindow.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthSuccessorTightWindow.lean)) | **`670,889,935`** (`> 0.6248 n`) | **`268,038,046`** (`> 0.2496 n`) | **`402,851,889`** (`< 0.3752 n`) |
| Blowup-Gauss + fixed-row dual $(\alpha, \beta)$ (`other ≤ 188,424`, probed) | **`670,994,405`** (`> 0.6249 n`) | **`268,246,986`** (`> 0.2498 n`) | **`402,747,419`** (`< 0.3751 n`) |

In particular, **every** $q$-to-$1$ ($q \ge 2$) homothetic factorization on $H$ — and **every** partial involution (such as an arbitrary Möbius involution $\sigma(X) = (aX + b)/(cX - a)$ preserving $\ge 75.1\%$ of $H$) — is unconditionally impossible across all five open profiles $(1,1,1,1)$ through $(1,1,1,5)$.

## 3. Exact `3 + 1` pencil-degree barrier below `679,477,248`

For any `3 collinear + 1 transverse` four-head construction with primitive direction degree $h \ge 1$, common triple locator degree $j_{\mathrm{loc}}$, and reduced 3-split pencil degree $r_{\mathrm{pair}}$ ($j_{\mathrm{loc}} + r_{\mathrm{pair}} \le d - h$),
$$
C_0 + C_1 + C_2 + C_3 \le n + 3d - h + r_{\mathrm{pair}}.
$$
To beat `679,477,248` errors ($e \le 679{,}477{,}247$) with balanced deficit-$(1,1,1,1)$ cores ($C_i \ge 394{,}264{,}576$), `three_plus_one_pencil_barrier` (Lean-checked) forces
$$
r_{\mathrm{pair}} \ge \frac{3}{4}k + 4 = 100{,}663{,}300.
$$
Thus [`EighthTransverseAttack.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthTransverseAttack.lean) saturates the $\mu_{16}$ cubic 3-split pencil ($r_{\mathrm{pair}} = 3k/4 = 100{,}663{,}296$) down to the very last site; lowering the `3 + 1` upper bound below `679,477,248` strictly requires a higher-density 3-split polynomial pencil on $\mu_{2^{30}}$.

## Verification ledger

- **Lean-checked (axiom-clean, zero `sorry`)**: [`ArkLib/Research/ProximityGap/Frontier/EighthRationalCoverObstructions.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthRationalCoverObstructions.lean) — all 6 public theorems (`card_biUnion_star_le_choose_two`, `homothetic_fiber_universal`, `homothetic_cover_mass_bound`, `homothetic_cover_image_floors`, `partial_involution_cap`, `three_plus_one_pencil_barrier`) verified with `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Reproducible probe**: [`scripts/probes/probe_eighth_rational_cover_obstructions.py`](../../../scripts/probes/probe_eighth_rational_cover_obstructions.py) exhaustively checks `homothetic_fiber_universal` across all multiset partitions of $4$ and fiber sizes $1 \le |S| \le 7$, reproduces all three residual-regime image/singleton/pair floors, and checks the `3 + 1` barrier.
