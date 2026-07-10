#!/usr/bin/env python3
"""_FSMD_Bonferroni probe: restricted-universe Bonferroni / triple-collinearity cascade at P1.

P1 rate-quarter predecessor parameters:
  N = 2^30, K = 2^28, T = 592794966.

Angle: after removing j saturated pencil cores (each of size z <= T-2, pairwise core
overlaps <= K-1 by line rigidity), an off-all-pencils scalar gamma keeps fresh agreement
mass >= T - j*(K-1) inside a universe of size <= N - j*z + C(j,2)*(K-1).
Three such scalars are forced collinear (slope-polynomial equality, deg < K) when their
triple intersection is >= K; Bonferroni gives triple >= 3*mass - 2*universe.

This probe computes EXACTLY:
  1. j = 1 threshold: minimal z for which the triple fires, vs the admissible cap z <= T-2
     and the feasibility cap z <= N - (T-K+1) (off-line scalars must fit off the core).
  2. Full cascade table j = 1..8 at maximal saturation z = T-2 for every removed pencil.
  3. Pairwise (Plotkin/Corradi) restricted-universe forcing: whether counting can force a
     K-overlap PAIR among fresh sets (limit j -> infinity of max forced pairwise overlap
     is m^2/U; equivalently Corradi is vacuous iff m^2 <= (K-1)*U).
All integers, no floats in the verdict path. Deterministic.
"""

N = 2**30            # 1073741824
K = 2**28            # 268435456
T = 592794966
m1 = T - (K - 1)     # fresh mass after one core steals <= K-1

def ceil_div(a, b):
    return -(-a // b)

print("=" * 78)
print("P1 constants")
print("=" * 78)
print(f"N = {N}, K = {K}, T = {T}")
print(f"pairwise agreement floor 2T-N = {2*T-N}  (< K: {2*T-N < K})")
print(f"L=3 per-line core floor (3T-N)/2 = {(3*T-N)//2} rem {(3*T-N)%2}")
print(f"saturation core z_sat = T-2 = {T-2}; max line pop L = N-T+1 = {N-T+1}")
print(f"Plotkin pairwise ceiling ceil(T^2/N) = {ceil_div(T*T, N)}")
print(f"fresh mass (one core removed) m = T-K+1 = {m1}")

print()
print("=" * 78)
print("1. j = 1 restricted-universe TRIPLE threshold (exact)")
print("=" * 78)
# triple >= 3m - 2(N - z); fires iff 3m - 2(N-z) >= K  iff  2z >= K + 2N - 3m
need2z = K + 2*N - 3*m1
zmin_triple = ceil_div(need2z, 2)
print(f"fires iff 2z >= K + 2N - 3(T-K+1) = {need2z}  =>  z >= {zmin_triple}")
print(f"(matches legacy form 3T + 2z > 2N + 4(K-1), i.e. z > {(2*N + 4*(K-1) - 3*T)//2})")
z_adm = T - 2
print(f"admissible pencil cap (extraction needs z+2 <= T): z <= {z_adm}")
print(f"CORE SHORTFALL: zmin - (T-2) = {zmin_triple - z_adm}")
mass_at_sat = 3*m1 - 2*(N - z_adm)
print(f"triple mass at z = T-2: 3m - 2(N-T+2) = {mass_at_sat}; need >= K = {K}")
print(f"MASS SHORTFALL: K - mass = {K - mass_at_sat}")
z_feas = N - m1  # off-line scalar needs T-(K-1) fresh coords outside the core
print(f"feasibility cap for off-line scalars: z <= N - m = {z_feas}")
print(f"non-vacuous window [zmin, z_feas] = [{zmin_triple}, {z_feas}], "
      f"width {z_feas - zmin_triple} (nonempty: {z_feas >= zmin_triple})")
print(f"but per-line packing delivers z >= (LT-N)/(L-1) <= T-1 = {T-1} < {zmin_triple}: "
      "window unreachable from population counts, and inadmissible for the 4-pencil cover.")
assert zmin_triple > z_adm

print()
print("=" * 78)
print("2. Cascade table: j saturated cores removed (z = T-2 each, best case)")
print("=" * 78)
# universe upper bound U(j) = N - j*(T-2) + C(j,2)*(K-1)   (cores pairwise overlap <= K-1)
# fresh mass  m(j) = T - j*(K-1)
# triple(j) = 3*m(j) - 2*U(j); fires iff >= K
print(f"{'j':>2} {'mass m(j)':>12} {'universe U(j)':>14} {'triple 3m-2U':>14} "
      f"{'fires(>=K)?':>12} {'shortfall':>12}")
best = None
for j in range(1, 9):
    mj = T - j*(K-1)
    Uj = N - j*(T-2) + (j*(j-1)//2)*(K-1)
    tj = 3*mj - 2*Uj
    fires = tj >= K
    short = K - tj
    if best is None or tj > best[1]:
        best = (j, tj)
    print(f"{j:>2} {mj:>12} {Uj:>14} {tj:>14} {str(fires):>12} {short:>12}")
    if mj <= 0 or Uj <= 0:
        print(f"   (j = {j}: mass/universe exhausted; cascade dead beyond here)")
        break
print(f"best j = {best[0]} with triple mass {best[1]} < K = {K} "
      f"(margin {K - best[1]}). Cascade NEVER fires.")
assert best[1] < K

# monotonicity certificate: g(j) = 3T - 2N + j*a - j(j-1)(K-1)/1 with a = 2(T-2)-3(K-1);
# doubled: G(j) = 6T - 4N + 2*j*a - j*(j-1)*(K-1); G decreasing for j >= 1
a = 2*(T-2) - 3*(K-1)
print(f"discrete-derivative certificate: a = 2(T-2)-3(K-1) = {a}; "
      f"2a - 2j(K-1) < 0 for j >= 1 iff a < K-1... a >= K-1: {a >= K-1}")
# G(j+1)-G(j) = 2a - 2j(K-1); negative for all j >= ceil(a/(K-1))
jstar = ceil_div(a, K - 1)
print(f"G increases up to j = {jstar} then decreases; check all j in 1..{jstar+1} explicitly:")
for j in range(1, jstar + 2):
    mj = T - j*(K-1)
    Uj = N - j*(T-2) + (j*(j-1)//2)*(K-1)
    print(f"   j={j}: triple = {3*mj - 2*Uj} < K: {3*mj-2*Uj < K}")

print()
print("=" * 78)
print("3. Pairwise restricted-universe forcing (Plotkin/Corradi), z = T-2")
print("=" * 78)
U = N - (T - 2)
print(f"fresh sets of size m = {m1} in universe U = N-(T-2) = {U}")
# Convexity: max forced pairwise overlap among j sets >= m*(j*m - U)/(U*(j-1)) -> m^2/U
lim_num, lim_den = m1*m1, U
print(f"j->inf forced-overlap limit m^2/U: m^2 = {lim_num}, U*K = {U*K}")
print(f"m^2 >= K*U (pair forcing possible in the limit)? {lim_num >= K*U}; "
      f"deficit K*U - m^2 = {K*U - lim_num}")
# Corradi: if all pairwise overlaps <= K-1 then j*(m^2 - U*(K-1)) <= U*(m-(K-1));
# vacuous (no bound on j) iff m^2 <= U*(K-1)
print(f"Corradi vacuous iff m^2 <= (K-1)*U: m^2 = {lim_num}, (K-1)*U = {(K-1)*U}, "
      f"vacuous: {lim_num <= (K-1)*U}; slack = {(K-1)*U - lim_num}")
# minimal z where pairwise limit would fire: K*(N-z) <= m^2  =>  z >= N - m^2/K
zmin_pair = N - (m1*m1)//K
print(f"pairwise limit fires iff z >= N - floor(m^2/K) = {zmin_pair} "
      f"(> T-2 by {zmin_pair - (T-2)})")
# six-set analogue in restricted universe: max pair among 6 >= m(6m-U)/(5U)
six_num = m1*(6*m1 - U)
six_den = 5*U
print(f"six-set forced pair (j=6): m(6m-U)/(5U) = {six_num//six_den} < K: "
      f"{six_num < K*six_den}")
assert lim_num < K*U and lim_num <= (K-1)*U

print()
print("=" * 78)
print("VERDICT: restricted-universe Bonferroni (triple AND pairwise-counting) is")
print("arithmetically DEAD at P1 for admissible cores z <= T-2, at every cascade")
print("depth j >= 1. Best case (j=1, z=T-2): triple mass 11184813 vs K = 268435456.")
print("Non-vacuous triple window z in [721420286, 749382313] exists but is both")
print("inadmissible (z+2 <= T required) and unreachable (packing caps z <= T-1... and")
print("agreement geometry caps deliverable cores at T-1 < 721420286).")
print("=" * 78)
