# Individual Pairwise Direction-Map Image Floors for Eighth-Rate Four-Head Profiles

At the eighth-rate second-prime successor $e = 671{,}088{,}640$ ($n = 2^{30}$, $k = 2^{27}$,
$d = 2^{27} - 1$, $t = 3k$, $B_2 = 2^{31}$), any overrun is a noncollinear four-head quartet with
sorted deficits $(1, 1, 1, q)$ ($1 \le q \le 5$). While `eighth-rational-cover-obstructions.md`
rules out any *joint* map $h : H \to T$ factoring all four heads' directions simultaneously, this
note proves **individual** image-size lower bounds on each pairwise direction map
$z_{ij} : H \to Z$ ($0 \le i < j \le 3$) directly from fresh-label disjointness ($G_i \cap G_j = \emptyset$)
and core overlaps ($|C_i \cap C_j| \le d$, and the triple-overlap triangle bound
$|C_0 \cap C_1| + |C_0 \cap C_2| + |C_1 \cap C_2| = y_2 + 3 y_3 \le 2d + 2(q - 1)$ since
$y_2 + 2 y_3 \le 2d$ and $y_3 \le x_3 + 2 x_4 + 2 x_0 \le 2(q - 1)$),
requiring no symmetry, dihedral, or monomial assumptions.

## Summary of Individual Image Floors (`res4 ≤ 189,082`)

| Profile | $\min_{i<j\le 2} |z_{ij}(H)|$ | $\max_{i<j\le 2} |z_{ij}(H)|$ | $\min_{i\le 2} |z_{i3}(H)|$ | Excluded individual factorizations |
|---|---:|---:|---:|---|
| **`(1,1,1,5)`** | **`536,681,827`** (`0.4998 n`) | **`626,223,335`** (`0.5832 n`) | **`321,933,459`** (`0.2998 n`) | **All 6** exclude $4$-to-$1$ (`X^4`); **all 3** of $z_{01},z_{02},z_{12}$ exclude $3$-to-$1$; **$\ge 1$** excludes $2$-to-$1$ (`X^2`) |
| **`(1,1,1,4)`** | **`503,127,395`** (`0.4686 n`) | **`603,853,715`** (`0.5624 n`) | — | All 3 of $z_{01},z_{02},z_{12}$ exclude $3$-to-$1$; **$\ge 1$** excludes $2$-to-$1$ (`X^2`) |
| **`(1,1,1,3)`** | **`447,203,342`** (`0.4165 n`) | **`566,571,014`** (`0.5277 n`) | — | All 3 of $z_{01},z_{02},z_{12}$ exclude $3$-to-$1$; **$\ge 1$** excludes $2$-to-$1$ (`X^2`) |
| **`(1,1,1,2)`** | **`335,355,235`** (`0.3123 n`) | **`492,005,611`** (`0.4582 n`) | — | All 3 of $z_{01},z_{02},z_{12}$ exclude $4$-to-$1$; **$\ge 1$** excludes $3$-to-$1$ |
| **`(1,1,1,1)`** | **`268,340,914`** (`0.2499 n`, each $z_a$) | **`357,819,399`** (`0.3332 n`, $\max z_a$) | $\sum_{a=1}^3 |z_a(H)| \ge \mathbf{1{,}073{,}458{,}195}$ (`0.9997 n`) | **$\ge 1$** of $z_1, z_2, z_3$ excludes $4$-to-$1$ (`X^4`) |

## Proof Mechanism

1. **Multi-slot subset image lemma (`multi_slot_subset_image_ge`)**: For any head core $C \subseteq H$
   of deficit $q \ge 1$ whose assigned labels $G$ each occupy $\ge q$ fresh sites in $H \setminus C$
   under $L$, and any subset $A \subseteq H \setminus C$ on which $L = z$, every label in
   $G \setminus z(A)$ has all $\ge q$ of its fresh sites inside $(H \setminus C) \setminus A$, so
   $$
   |A| + q\,|G| \le |H \setminus C| + q\,|G \cap z(A)|.
   $$
2. **Pairwise disjointness (`pair_direction_image_ge`, `unit_pair_direction_image_ge`)**: On
   $C_j \setminus C_i \subseteq H \setminus C_i$ we have $L_i = z_{ij}$, and on
   $C_i \setminus C_j \subseteq H \setminus C_j$ we have $L_j = z_{ij}$. Because $G_i \cap G_j = \emptyset$,
   the two sets $G_i \cap z_{ij}(C_j \setminus C_i)$ and $G_j \cap z_{ij}(C_i \setminus C_j)$ are
   disjoint subsets of $z_{ij}(H)$, yielding
   $$
   q_j |C_j \setminus C_i| + q_i |C_i \setminus C_j| + q_i q_j (|G_i| + |G_j|)
   \le q_j |H \setminus C_i| + q_i |H \setminus C_j| + q_i q_j |z_{ij}(H)|.
   $$
3. **Opposite-pair involution (`opposite_pair_involution_image_ge`)**: In saturated `(1, 1, 1, 1)`,
   the constant nonsingular involution $J$ pairs $z_{23} = J \circ z_{01}$, so all four disjoint sets
   $G_0, G_1, G_2, G_3$ contribute to $z_{01}(H) \cup J(z_{01}(H))$ of cardinality $\le 2 |z_{01}(H)|$.
4. **Factorization exclusion (`image_card_mul_le_of_factor`)**: If $z = f \circ h$ on $H$ with
   $r |h(H)| \le |H|$, then $r |z(H)| \le |H|$, ruling out any $r$-to-$1$ factorization (in particular
   any power map $M(X^e)$ with $r \mid e$ on $\mu_{2^{30}}$) whenever $|z(H)| > n/r$.

## Verification Scope

- **Lean-checked (`ArkLib/Research/ProximityGap/Frontier/EighthDirectionImageFloors.lean`)**:
  Mathlib-only, zero `sorry`, zero custom axioms (`#print axioms` $\subseteq$ `{propext, Classical.choice, Quot.sound}`).
  Proves `multi_slot_subset_image_ge`, `pair_direction_image_ge`, `unit_pair_direction_image_ge`,
  `opposite_pair_involution_image_ge`, `image_card_mul_le_of_factor`, `profile_q2_to_q5_image_floors`,
  and `profile_q1_saturated_image_floors`.
- **Independent Python probe (`scripts/probes/probe_eighth_direction_image_floors.py`)**:
  independently recomputes every integer floor and tests random finite models against the Finset
  inequalities.
