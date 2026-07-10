#!/usr/bin/env python3
"""_FSMC_Sunflower probe: sunflower / spread structure of the forced core system
at the P1 rate-quarter lattice predecessor.

Exact integer analysis of:
  1. Plotkin bound ON CORES (weight w, pairwise overlap <= K-1): activation
     threshold, cap table, and the six-line impossibility at near-saturated w.
  2. Matching spread: >= 2^29-2 disjoint forced pairs; pigeonhole over secant
     lines; <=4 lines forces a saturated (z >= T-1) line; no-saturation forces
     >= 5 distinct lines.
  3. Turan pair-mass: thick (K-core) ordered pair mass forced by six-set
     forcing at |G| = N+1; per-line contribution caps; minimum line counts.
  4. Averaging / sunflower statistics: exact triple & quadruple mean overlaps
     vs K; matched-core mean pairwise overlap vs K; where the adversary
     survives.
  5. Vacuity re-checks (high-core collapse, Plotkin ceiling).

Deterministic; run: python3 probe_fsmc_sunflower_forced_core_spread.py
"""

from fractions import Fraction
import math

N = 2**30
K = 2**28
T = 592794966

def ceil_div(a, b):
    return -((-a) // b)

print("=" * 72)
print("SECTION 0: constants and prompt-claimed derived numbers")
print("=" * 72)
print(f"N = {N}, K = {K}, T = {T}")
print(f"2T - N            = {2*T - N}   (pairwise agreement overlap floor; < K: {2*T-N < K})")
print(f"(3T - N)/2 ceil   = {ceil_div(3*T - N, 2)}")
print(f"L_max = N - T + 1 = {N - T + 1}")
print(f"L forcing z>=T-2  : L >= {ceil_div(N - T + 2, 2)}  (claimed 240473431: "
      f"{ceil_div(N-T+2,2) == 240473430} -> careful, see below)")
# z >= ceil((L*T-N)/(L-1)); find min L with that >= T-2 and >= T-1
def zmin(L):
    return ceil_div(L*T - N, L - 1)
lo, hi = 2, N
for target, name in [(T-2, "T-2"), (T-1, "T-1"), (T, "T")]:
    lo2, hi2 = 2, 2*N
    while lo2 < hi2:
        mid = (lo2 + hi2)//2
        if zmin(mid) >= target:
            hi2 = mid
        else:
            lo2 = mid + 1
    print(f"min L with forced z >= {name}: {lo2}   (zmin({lo2}) = {zmin(lo2)}, zmin({lo2-1}) = {zmin(lo2-1)})")
print(f"Plotkin ceiling ceil(T^2/N) = {ceil_div(T*T, N)}  (claimed 327272222: {ceil_div(T*T,N)==327272222})")
print(f"High-core collapse needs z > (2N+4(K-1)-3T)/2 = {Fraction(2*N+4*(K-1)-3*T,2)} "
      f"> T-2 = {T-2}: vacuous at P1: {Fraction(2*N+4*(K-1)-3*T,2) > T-2}")

print()
print("=" * 72)
print("SECTION 1: Plotkin bound ON CORES (overlap cap s = K-1)")
print("=" * 72)
s = K - 1
# constantWeight_plotkin: m*(w^2 - N*s) <= N*(w - s); active iff w^2 > N*s
wact = math.isqrt(N*s) + 1
while wact*wact <= N*s:
    wact += 1
print(f"activation: w^2 > N(K-1) = {N*s}  <=> w >= {wact}  (2K-1 = {2*K-1}, 2K = {2*K})")
print(f"check: (2K-1)^2 - N(K-1) = {(2*K-1)**2 - N*s}")
def plotkin_cap(w):
    d = w*w - N*s
    if d <= 0:
        return None
    return (N*(w - s)) // d
for w in [2*K-1, 2*K, 550000000, 560000000, 570000000, 580000000, 590000000,
          T-2, T-1, T, 2*T-N + K, N]:
    print(f"  w = {w:>10}: cap m <= {plotkin_cap(w)}")
# exact minimal w where cap <= 5 (i.e. 6 lines impossible): 6*(w^2-Ns) > N*(w-s)
lo2, hi2 = wact, N
def six_impossible(w):
    return 6*(w*w - N*s) > N*(w - s)
while lo2 < hi2:
    mid = (lo2 + hi2)//2
    if six_impossible(mid):
        hi2 = mid
    else:
        lo2 = mid + 1
w6 = lo2
print(f"six cores of weight w pairwise-overlapping <= K-1 impossible iff w >= {w6}")
print(f"  T-2 = {T-2} >= {w6}: {T-2 >= w6}   T-1 >= {w6}: {T-1 >= w6}")
print(f"  margin at w=T-2: 6*((T-2)^2-N(K-1)) - N(T-2-(K-1)) = "
      f"{6*((T-2)**2 - N*s) - N*(T-2-s)}")
print(f"  margin at w=T-1: {6*((T-1)**2 - N*s) - N*(T-1-s)}")
# also check 5 lines feasible by Plotkin at T-1 (bound not violated)
print(f"  5-line Plotkin slack at w=T-1: 5*((T-1)^2-N(K-1)) = {5*((T-1)**2 - N*s)} "
      f"<= N(T-K) = {N*(T-K)}: {5*((T-1)**2-N*s) <= N*(T-K)}")
# minimal w where even 5 / 4 impossible
for m in [5, 4, 2]:
    lo3, hi3 = wact, 2*N
    while lo3 < hi3:
        mid = (lo3+hi3)//2
        if m*(mid*mid - N*s) > N*(mid - s):
            hi3 = mid
        else:
            lo3 = mid + 1
    print(f"  {m} cores impossible iff w >= {lo3}  (> T? {lo3 > T}; > N? {lo3 > N})")

print()
print("=" * 72)
print("SECTION 2: matching spread (M0 = 2^29 - 2 disjoint forced pairs)")
print("=" * 72)
M0 = 2**29 - 2
print(f"M0 = {M0}")
print(f"pigeonhole over <= 4 lines: max fiber >= ceil(M0/4) = {ceil_div(M0,4)} = 2^27? "
      f"{ceil_div(M0,4) == 2**27}")
p4 = ceil_div(M0, 4)
L4 = 2*p4
print(f"forced L >= 2*{p4} = {L4} = 2^28? {L4 == 2**28}")
print(f"packing with z <= T-2 (w = T-z >= 2): L*w + z <= N with z = T-w:")
print(f"  w*(L-1) <= N-T = {N-T}; at L = 2^28: w <= {(N-T)//(2**28-1)} "
      f"(exact {Fraction(N-T, 2**28-1)}) -> w <= 1 CONTRADICTION => z >= T-1")
print(f"  check omega form: 2*(2^28 - 1) = {2*(2**28-1)} > N-T = {N-T}: {2*(2**28-1) > N-T}")
# 5-line case: max fiber >= ceil(M0/5)
p5 = ceil_div(M0, 5)
L5 = 2*p5
print(f"with 5 lines: fiber >= {p5}, L >= {L5}, forced z >= {zmin(L5)} "
      f"(T-2 = {T-2}, T-1 = {T-1}) -> saturated? {zmin(L5) >= T-1}")
p6 = ceil_div(M0, 6)
print(f"with 6 lines: fiber >= {p6}, L >= {2*p6}, forced z >= {zmin(2*p6)} vs T-2={T-2}")
# how many lines needed so that forced z can stay <= T-2:
# fiber p forces L >= 2p forces z >= zmin(2p); need zmin(2p) <= T-2
lo4, hi4 = 1, M0
def max_pairs_nonsat():
    # max p with zmin(2p) <= T-2  <=> 2p <= max L with zmin(L) <= T-2
    lo5, hi5 = 2, 2*N
    while lo5 < hi5:
        mid = (lo5+hi5)//2
        if zmin(mid) >= T-1:
            hi5 = mid
        else:
            lo5 = mid+1
    Lns = lo5 - 1  # max L with forced z <= T-2
    return Lns, Lns//2
Lns, pns = max_pairs_nonsat()
print(f"max L with forced z <= T-2: {Lns}; max pairs on such a line: {pns}")
print(f"min #lines if all forced-z nonsaturated: ceil(M0/{pns}) = {ceil_div(M0, pns)}")
# but the actual z (not just forced-z) may exceed forced; nonsaturated ACTUAL z <= T-2
# caps L via packing: L <= (N-z)/(T-z) maximized at z=T-2:
Lhalf = (N - (T-2)) // 2
print(f"ACTUAL nonsaturated line cap: L <= (N-z)/(T-z) <= (N-T+2)/2 = {Lhalf}")
print(f"pairs per actual-nonsaturated line <= {Lhalf//2}")
print(f"min #distinct lines if NO saturated (z>=T-1) line exists: "
      f"ceil(M0/{Lhalf//2}) = {ceil_div(M0, Lhalf//2)}")
# saturated line capacity
Lsat = N - (T-1)
print(f"saturated line (z >= T-1) cap: L <= N-z <= {Lsat}; pairs <= {Lsat//2}")
for nsat in range(0, 6):
    rem = M0 - nsat*(Lsat//2)
    if rem <= 0:
        print(f"  {nsat} saturated lines alone can carry M0: True")
        break
    print(f"  {nsat} saturated lines: leftover pairs {rem}, "
          f"extra nonsat lines >= {ceil_div(rem, Lhalf//2)}")

print()
print("=" * 72)
print("SECTION 3: Turan pair-mass at |G| = N+1 (all pairs, not just matched)")
print("=" * 72)
G = N + 1
total_ordered = G*(G-1)
# six-set forcing => complement (thin-overlap) graph K6-free => Turan
# e(H-bar) <= (1 - 1/5) * G^2 / 2 ; ordered thin <= 4G^2/5
thin_max_ordered = Fraction(4*G*G, 5)
thick_min_ordered = total_ordered - thin_max_ordered
print(f"ordered pairs total   = {total_ordered}")
print(f"ordered thin (Turan)  <= {thin_max_ordered} ~ {float(thin_max_ordered):.4e}")
print(f"ordered thick (>=K)   >= {thick_min_ordered} ~ {float(thick_min_ordered):.4e}")
contrib_ns = Lhalf*(Lhalf-1)
print(f"nonsaturated line max ordered-pair contribution = Lhalf(Lhalf-1) = {contrib_ns}")
mmin = ceil_div(int(math.ceil(thick_min_ordered)), contrib_ns)
print(f"min #thick lines if all nonsaturated: ceil(thick_min/contrib) = {mmin}")
print(f"4-line feasibility margin: 4*contrib - thick_min = "
      f"{4*contrib_ns - thick_min_ordered} ~ {float(4*contrib_ns - thick_min_ordered):.3e} "
      f"({'FEASIBLE at count level' if 4*contrib_ns >= thick_min_ordered else 'INFEASIBLE -> >=5'})")
contrib_sat = Lsat*(Lsat-1)
print(f"saturated line max contribution = {contrib_sat} ~ {float(contrib_sat):.4e} "
      f">= thick_min? {contrib_sat >= thick_min_ordered}")
# scalars covered by 4 nonsaturated pencils (pairwise share <= 1 scalar)
print(f"4 nonsaturated pencils cover <= 4*Lhalf = {4*Lhalf} scalars < N+1 = {G}: "
      f"{4*Lhalf < G}  (deficit {G - 4*Lhalf})")
print(" => the 'four-pencil small-core cover' can NEVER literally cover an")
print("    over-budget family; the residual is the pin itself (consistent with")
print("    the machine-checked equivalence).")

print()
print("=" * 72)
print("SECTION 4: averaging / sunflower statistics")
print("=" * 72)
# triple mean overlap lower bound (convexity, |A_g| >= T, |G| = N+1):
# sum_i C(d_i,3) >= N*C(dbar,3), dbar = G*T/N; mean over ordered triples
dbar = Fraction(G*T, N)
mean_triple = Fraction(N) * (dbar*(dbar-1)*(dbar-2)) / (Fraction(G*(G-1)*(G-2)))
print(f"mean triple overlap (convexity floor) = {float(mean_triple):.1f} "
      f"~ T^3/N^2 = {Fraction(T**3, N**2)} ~ {float(Fraction(T**3,N**2)):.1f}")
print(f"K = {K}; triple mean < K: {mean_triple < K}  "
      f"(deficit ~ {K - float(mean_triple):.4e})")
print(f"exact numeric pin: T^3 = {T**3} < K*N^2 = {K*N**2}: {T**3 < K*N**2}")
print(f"  ratio T^3/(K N^2) = {float(Fraction(T**3, K*N**2)):.6f}")
mean_quad = Fraction(T**4, N**3)
print(f"quadruple mean ~ T^4/N^3 = {float(mean_quad):.1f} < K: {mean_quad < K}")
# what overlap threshold CAN triple averaging force? mean_triple itself:
print(f"triple averaging forces only common-coverage ~ {int(mean_triple)} "
      f"= {float(Fraction(int(mean_triple),K)):.3f} K")
# matched cores: M0 cores of size >= K; mean pairwise core overlap floor:
# sum_i C(d_i,2) >= N C(M0*K/N, 2); mean over ordered core pairs
dbar2 = Fraction(M0*K, N)
mean_core_pair = Fraction(N)*(dbar2*(dbar2-1))/Fraction(M0*(M0-1))
print(f"matched-core mean pairwise overlap floor = {float(mean_core_pair):.1f} "
      f"~ K^2/N = K/4 = {K//4}; K needed for consolidation: {K}")
print(f"  => averaging on matched cores reaches only ~K/4; consolidation (>=K)")
print(f"     NOT forced by second moment. adversary head-room factor ~4.")
# can the geometry cap even allow high triple overlaps off-line?
print("off-line cap: |A_theta ∩ core| <= K-1 for theta off the line; so any")
print("triple common overlap >= K forces collinearity -- i.e. exactly the")
print("configuration counting cannot force (Plotkin ceiling 327272222 < T-2).")
# consistency of the 'many small thick lines' adversary with second moments:
# G scalars, all cores exactly K, pairwise core overlaps <= K-1, thin pairs
# on Turan 5-partition. Check fractional second-moment feasibility:
# sum_i C(d_i,2) over coordinates for agreement sets:
dbarA = Fraction(G*T, N)
lhs = N * (dbarA*(dbarA-1)) / 2
pairs = Fraction(G*(G-1), 2)
mean_pair = lhs/pairs
print(f"agreement-set mean pairwise overlap floor = {float(mean_pair):.1f} "
      f"(2T-N = {2*T-N}, K = {K})")
print(f"  floor sits between 2T-N and K: {2*T-N <= mean_pair < K}")

print()
print("=" * 72)
print("SECTION 5: verdict-shaping summary")
print("=" * 72)
print(f"* NEW cap (landable): at most 5 distinct deg<K lines with core >= {w6}")
print(f"  (in particular >= T-2 and >= T-1). First Plotkin-active core bound;")
print(f"  works because T-1 > 2K-1 = {2*K-1}.")
print(f"* NEW dichotomy (landable): matching on <= 4 distinct secant lines")
print(f"  forces a fiber >= 2^27, hence L >= 2^28, hence z >= T-1 (saturated).")
print(f"  Contrapositive: all matched secant cores <= T-2 => >= 5 distinct lines.")
print(f"* Combined with actual-size cap: no saturation => >= {ceil_div(M0, Lhalf//2)} distinct")
print(f"  thick lines carry the matching (>= {ceil_div(M0, Lhalf//2)} > 4).")
print(f"* Pure set-system CANNOT finish: triple mean {float(mean_triple)/K:.3f}K < K,")
print(f"  matched-core pair mean {float(mean_core_pair)/K:.3f}K < K, number of")
print(f"  K-cores with (K-1)-overlaps is UNBOUNDED (Plotkin inactive at w=K),")
print(f"  and 4-line pair-mass margin is positive ({float(4*contrib_ns - thick_min_ordered):.2e}).")
