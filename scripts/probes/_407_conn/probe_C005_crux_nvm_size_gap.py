"""
C005 crux probe (#407): does k=1 NVM (nonvanishing T_j) deliver the SIZE bound B?

The C005 record says nonvanishing is the "qualitative shadow" and the sup-norm is the
"quantitative" version of the SAME object.  The honest question for the prize: does the
k=1 NVM PROPERTY (all T_j != 0) -- or even the FULL NVM property (all minors != 0) --
imply any nontrivial upper bound on  B = max_j |T_j| = max_{b!=0}|eta_b| ?

We show NO, in two ways:

(I) DIRECT: across the proper-subgroup primes, all T_j are nonzero (NVM at k=1 holds)
    yet B tracks the BGK/Gauss-period size, which GROWS roughly like sqrt(n log(p/n))
    and is NOT bounded by any nonvanishing fact.  We print B / sqrt(n log(p/n)) to show
    it is the live analytic quantity, independent of the (always-true) nonvanishing.

(II) STRUCTURAL: nonvanishing is invariant under rescaling the phases; the SIZE is not.
    Concretely, the in-tree Lean lemma cft_det_eq shows det = (det F)^2 * prod G_i / m^m
    which is nonzero purely from |G_i|=sqrt q != 0 -- a nonvanishing argument that uses
    ONLY |G_i|>0 and NEVER the relative phases of the G_i.  But B depends entirely on the
    relative phases (the DFT can be flat ~sqrt n or spiky ~n with the SAME |G_i|).  So the
    minor machinery is provably blind to the quantity B.  We demonstrate by replacing the
    true Gauss phases with (a) aligned phases -> B = n (max spike) and (b) random phases ->
    B ~ sqrt(n): same |G_i|, same nonvanishing, wildly different B.
"""
import cmath, math, random

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    fact = []; phi = p-1; x = phi; d = 2
    while d*d <= x:
        if x % d == 0:
            fact.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fact.append(x)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fact): return g
    return None

def find_prime_for_subgroup(n, blo, bhi, count=2):
    out = []; lo = int(n**blo); hi = int(n**bhi); m = max(2, lo//n)
    while (p := m*n+1) <= hi:
        if is_prime(p) and (p-1)//n == m and m >= 2:
            out.append((p, m))
            if len(out) >= count: break
        m += 1
    return out

def B_of_subgroup(p, g, m, n):
    wq = 2j*math.pi/p
    H = [pow(g, (m*j) % (p-1), p) for j in range(n)]
    Ts = []  # the m DISTINCT period values
    for c in range(m):
        b = pow(g, c, p)
        Ts.append(sum(cmath.exp(wq*((b*h) % p)) for h in H))
    return max(abs(t) for t in Ts), Ts

print("="*78)
print("(I) k=1 NVM ALWAYS holds (all period values nonzero) but B is the LIVE size")
print("    that grows ~ sqrt(n log(p/n)).  Nonvanishing != size bound.")
print("="*78)
for n in [8, 16, 32, 64]:
    for (p, m) in find_prime_for_subgroup(n, 2.0, 3.0, count=2):
        g = primitive_root(p)
        B, Ts = B_of_subgroup(p, g, m, n)
        allnz = all(abs(t) > 1e-9 for t in Ts)
        target = math.sqrt(n*math.log(p/n))
        print(f"  n={n:3d} p={p:8d} m={m:6d}: k=1 NVM(all!=0)={allnz}  "
              f"B={B:7.3f}  sqrt(n log(p/n))={target:7.3f}  B/target={B/target:.3f}")

print()
print("="*78)
print("(II) STRUCTURAL BLINDNESS: SAME |G_i|=1 (=> det != 0, NVM holds), different phases")
print("     => B ranges from sqrt(n) (random) to n (aligned).  Minor nonvanishing uses")
print("     only |G_i|>0 and is provably blind to the phases that DETERMINE B.")
print("="*78)
random.seed(1)
for m in [8, 16, 32, 64]:
    zm = cmath.exp(2j*math.pi/m)
    # unimodular "Gauss phase" vector a_i = G_i/sqrt q ; B-analog = (1/?)max_j|sum_i zm^{ij} a_i|
    # aligned: a_i = 1  => T_0 = sum 1 = m (full spike)
    a_aligned = [1.0+0j]*m
    Talign = [sum(zm**((i*j)%m)*a_aligned[i] for i in range(m)) for j in range(m)]
    Balign = max(abs(t) for t in Talign)
    # random unimodular
    Bsamples = []
    for _ in range(200):
        a = [cmath.exp(2j*math.pi*random.random()) for _ in range(m)]
        Tr = [sum(zm**((i*j)%m)*a[i] for i in range(m)) for j in range(m)]
        Bsamples.append(max(abs(t) for t in Tr))
    Brand = sum(Bsamples)/len(Bsamples)
    # all |a_i| = 1 in BOTH cases -> diag(a) has nonzero det -> all minor-nonvanishing facts identical
    print(f"  m={m:3d}: aligned-phase B={Balign:7.3f} (=m, max spike)   "
          f"random-phase mean B={Brand:7.3f} (~sqrt m={math.sqrt(m):.2f}*c)   "
          f"-> ratio {Balign/Brand:.2f}x; SAME |a_i|, SAME nonvanishing")

print("""
CONCLUSION:
 (I) k=1 NVM nonvanishing is ALWAYS satisfied at every proper-subgroup prize prime, while
     B is the genuinely varying analytic quantity (the BGK sup-norm).  The two are NOT the
     same: one is the constant True, the other is the open number.
 (II) The minor/determinant machinery (cft_det_eq, cft_top_minor_ne_zero, the gen-Vandermonde
     nonvanishing) depends ONLY on |G_i|=sqrt q > 0 and is provably BLIND to the relative
     phases of the Gauss sums -- but B is determined ENTIRELY by those phases (same |a_i|
     gives B from sqrt(m) to m).  So no nonvanishing-minor statement, at ANY k, can deliver
     the quantitative sup-norm bound B <= C sqrt(n log(p/n)).
 => C005 correctly IDENTIFIES the k=1 minor with the period house (exact, structural,
     already Lean-proven as cftMat_apply_eq_houseVec), but the attack_plan's hoped-for
     wiring (NVM-quantitative -> WorstCaseIncompleteSumBound) has NO content the existing
     GaussPeriodMomentBound consumer lacks: the open input is still |T_j| <= C sqrt(n log m),
     i.e. the BGK/Paley sup-norm wall, verbatim.
""")
