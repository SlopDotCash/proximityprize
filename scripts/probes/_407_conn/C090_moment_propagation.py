"""
C090 probe: "Negative-energy-defect = bounded-support TRUNCATION = supply LOWER bound."

THE CLAIM (C090.json attack_plan, verbatim intent):
  Does the PROVEN r=2 fact -- E_2(mu_n) = 3n^2-3n  (=> normalized mu_2=1, mu_4=3-3/n)
  TOGETHER WITH the support cap |X| <= sqrt(n) -- ALGEBRAICALLY FORCE the Gaussian baseline
        mu_{2r}  <=  (2r-1)!! * n^r   (i.e. normalized  m_{2r} <= (2r-1)!! )
  for ALL r, via a Hausdorff-moment / completely-monotone interpolation on the compactly
  supported measure?  If YES, the open core (r ~ ln q) collapses to the proven r=2.

  Concretely the connection conjectures: "compact support sqrt(n) + mu_4 <= 3  ==>  mu_{2r} <= (2r-1)!! n^r".

DECISIVE TEST:
  Given a symmetric mean-0 prob measure X on [-S,S] (S = sqrt(n) in normalized units, so the
  RAW spectrum eta_b in [-n,n]) with m = (p-1)/n atoms, normalized mu_2 = 1, mu_4 = 3-3/n,
  compute the MAXIMAL feasible normalized 2r-th moment  m_{2r}^max  (a finite linear program /
  Markov-Krein upper extremal).  Compare to the Gaussian baseline (2r-1)!!.
    * If m_{2r}^max <= (2r-1)!! for all r  -> claim could hold (propagation works).
    * If m_{2r}^max EXCEEDS (2r-1)!! at some r -> claim REFUTED: support+mu2+mu4 do NOT force
      the baseline; the high moments are FREE above Gaussian.

  We compute m_{2r}^max in closed form: maximize 2r-th moment subject to support [-S,S],
  mu_2=1, mu_4<=K.  The extremal measure of such an interval moment problem is supported on
  the boundary +-S plus interior points; for MAXIMIZING the highest moment under an UPPER
  cap on a fixed support, the maximizer pushes mass to the endpoints +-S.  The clean exact
  upper bound (drop the mu_4 constraint, keep only mu_2 and support): mass w at +-S with
  2 w S^2 <= 1 i.e. w <= 1/(2S^2), the rest at 0; then m_{2r} = 2 w S^{2r} <= S^{2r-2} = S^{2(r-1)}.
  i.e.  m_{2r}^max(only mu2+support) = S^{2(r-1)} = n^{r-1}.   This is the Markov upper.

  Also we add the mu_4 constraint via a small exact LP on a grid for a real upper extremal.

KEY DISTINCTION C090 adds vs C075:
  C075 maximized the support ATOM location; C090 asks about the MOMENTS themselves and whether
  r=2 propagates.  We test moment-by-moment propagation AND we contrast the FALSE support cap
  sqrt(n) against the TRUE Gauss-period L-infinity scale ~ sqrt(n*log m) (the actual eta_b max).
"""
import math
from fractions import Fraction as Fr

def doublefact(k):  # (2r-1)!! for k=2r-1
    r = (k+1)//2
    out = 1
    for j in range(1, r+1):
        out *= (2*j-1)
    return out

def markov_upper_moment_2r(r, S, mu2=1.0):
    """Closed-form Markov upper for normalized m_{2r} given support [-S,S] and 2nd moment mu2,
    NO mu_4 constraint: put mass w at +-S (rest at 0), 2 w S^2 = mu2 => w = mu2/(2 S^2),
    m_{2r} = 2 w S^{2r} = mu2 * S^{2(r-1)}."""
    return mu2 * S**(2*(r-1))

def lp_upper_moment_2r(r, S, K, mu2=1.0, ngrid=400):
    """Exact-ish LP: maximize m_{2r} = sum p_i x_i^{2r} over symmetric prob measure on a grid
    of [0,S] (paired +-), s.t. sum p_i = 1 (full mass over half, doubled), mu_2 = mu2, mu_4 <= K.
    Symmetric => only even moments; represent half-measure q_i on grid points g_i in [0,S],
    total mass 1 (q sums to 1, each point contributes symmetric pair so even moments = sum q_i g_i^{2k}).
    Maximize sum q_i g_i^{2r}. LP with 2 eq (mass, mu2) + 1 ineq (mu4). The optimum is at a vertex:
    support on <=3 points. We just enumerate triples (0, a, b) cheaply for an upper extremal."""
    grid = [S*i/ngrid for i in range(ngrid+1)]
    best = 0.0
    # extremal of a problem with 3 linear constraints (mass, mu2, mu4<=) maximizing one moment:
    # supported on at most 3 points. Enumerate triples including endpoint S and 0.
    cand = sorted(set([0.0, S] + grid))
    # To keep it fast: the maximizer for the highest moment pushes mass to S; pair S with one interior
    # point and 0 to satisfy mu2, mu4. Enumerate pairs (0 or interior a) with S.
    for a in cand:
        for b in cand:
            if b <= a:
                continue
            # masses pa at a, pb at b, p0 at 0 ; pa+pb+p0=1 ; pa a^2 + pb b^2 = mu2
            # solve for pa,pb,p0 with p0 free? 2 eqns, 3 unknowns -> 1-param; pick to maximize moment.
            # Simpler: 2-atom support {a,b}: pa+pb=1, pa a^2+pb b^2=mu2.
            denom = (b*b - a*a)
            if abs(denom) < 1e-12:
                continue
            pa = (b*b - mu2)/denom
            pb = (mu2 - a*a)/denom
            if pa < -1e-12 or pb < -1e-12:
                continue
            mu4 = pa*a**4 + pb*b**4
            if mu4 > K + 1e-9:
                continue
            mom = pa*a**(2*r) + pb*b**(2*r)
            if mom > best:
                best = mom
    return best

def main():
    print("="*108)
    print(" C090: does proven r=2 (mu2=1, mu4=3-3/n) + support cap FORCE mu_{2r} <= (2r-1)!! n^r for all r?")
    print("="*108)
    print(" Normalized: X = eta_b/sqrt(n), support S=sqrt(n), baseline (Gaussian/Bessel) = (2r-1)!!")
    print(" RAW moment baseline = (2r-1)!! * n^r ; we work normalized so baseline = (2r-1)!!.")
    print()
    for n, beta in [(8,4),(16,4),(32,5),(64,5),(2**20,5),(2**30,5)]:
        m = max(2, int(round(n**(beta-1))))
        S = math.sqrt(n)
        K = 3 - 3/n
        target_atom = math.sqrt(2*math.log(m))   # the true B/sqrt(n) law
        print(f" n={n}  beta={beta}  m=2^{math.log2(m):.1f}  S=sqrt(n)={S:.3f}  mu4(cap)={K:.4f}  true B/sqrt(n)~{target_atom:.3f}")
        print(f"   {'r':>3}{'baseline (2r-1)!!':>20}{'Markov-upper m2r (mu2+supp)':>30}{'  exceeds baseline?':>20}")
        for r in [2,3,4,5,8,13]:
            base = float(doublefact(2*r-1))
            mu_upper = markov_upper_moment_2r(r, S)   # = n^{r-1}
            ratio = mu_upper / base
            flag = "YES (free above)" if mu_upper > base else "no"
            print(f"   {r:>3}{base:>20.3e}{mu_upper:>30.3e}{('  '+flag):>20}")
        print()
    print("="*108)
    print(" CRUX: the SUPPORT CAP is NOT sqrt(n). The TRUE eta_b L-infinity scale is ~ sqrt(n*log m).")
    print("="*108)
    print(" The proven |eta_b|<=n cap gives S=sqrt(n) normalized, but the ACTUAL extreme eta_b sits at")
    print(" sqrt(n*log m) (the very quantity B we want to bound) -- so 'support cap sqrt(n)' is the")
    print(" trivial Cantelli ceiling, far above the true max, and assuming support sqrt(n) is circular:")
    print(" it would already imply B<=sqrt(n), DISPROVING the open core for free, which is false.")
    print()
    print(" Small-r LP cross-check (mu4<=3-3/n constraint included), max m_{2r}:")
    for n in [16, 64]:
        S = math.sqrt(n); K = 3 - 3/n
        print(f"   n={n}, S={S:.3f}, K={K:.4f}:")
        for r in [2,3,4]:
            base = float(doublefact(2*r-1))
            lp = lp_upper_moment_2r(r, S, K, ngrid=200)
            print(f"     r={r}: baseline={base:.3e}  LP-max-m2r={lp:.3e}  ratio={lp/base:.3e}  {'EXCEEDS baseline' if lp>base else 'within'}")

if __name__ == "__main__":
    main()
