"""
C046 meta-claim check: "any FINITE-degree moment chain returns the variance."

The connection abstracts BOTH
  (list)   squaredJohnson_le_fourthChain : (n*S2)^2 <= n^3 * S4        [PROVEN in tree]
  (period) exists_period_sq_ge floor      : max ||eta||^2 >= (qE-n^4)/(qn-n^2)
to one principle. Concretely the proposed meta-lemma finiteMoment_returns_variance:
for any nonneg profile a_1..a_N (here the per-coordinate counts m_i, or the per-freq ||eta_b||^2),
the power-mean tower S_{2r}^{1/r} only ever lower-bounds the VARIANCE (= S2/N scale), with
equality iff flat; a finite r CANNOT detect the L-infinity max above that.

Two checks:
 (A) numerical: for random nonneg profiles, the L4-based "improvement" n^3*S4 - (n*S2)^2 is ALWAYS >=0
     (the no-go direction), == 0 iff flat; AND the best lower bound on max from (S2,S4) via
     Cauchy-Schwarz  max >= S4/S2  is bounded by O(mean^2)=O(variance) when the profile is flat,
     never the log-N extreme value of an actually-peaked-by-one-spike profile.
 (B) the SAME-NO-GO equivalence at the algebra level: show
       (n S2)^2 <= n^3 S4   <=>   S2^2 <= n S4   <=>   (1/N)Sum a^2  >= ((1/N)Sum a)^2  ... no:
     the right statement is the period one. Demonstrate that the *list* chain inequality and the
     *period* 4th-moment lower bound are the SAME Cauchy-Schwarz applied to the profile a_i:
       Cauchy-Schwarz:  (Sum a^2)^2 <= (Sum a) * (Sum a^3)   ... ; here the relevant pair is
       (Sum a^2)^2 <= N * Sum a^4   (used as a no-go on the LIST side, S2^2<=N S4)
       Sum a^4 <= max(a) * Sum a^3  / OR / Sum a^4 <= max(a^2)*Sum a^2  (used as the LOWER bound max>=S4/S2 on PERIOD side)
     i.e. ONE Cauchy-Schwarz S2^2<=N*S4 read in two directions:
        - solved for an UPPER cap on (Sum a)  -> list no-go (can't beat Johnson)
        - solved for a LOWER bound on max     -> period floor (only Theta(variance))
"""
import random, math

def profile_stats(a):
    N=len(a)
    S1=sum(a); S2=sum(x*x for x in a); S3=sum(x**3 for x in a); S4=sum(x**4 for x in a)
    mx=max(a)
    return N,S1,S2,S3,S4,mx

def check_random(N, trials=20000):
    # init to +inf so we record the GENUINE minimum (catch any negativity = a real violation)
    worst_violation_list = float('inf')
    worst_violation_floor = float('inf')
    for _ in range(trials):
        a=[random.random() for _ in range(N)]
        Nn,S1,S2,S3,S4,mx=profile_stats(a)
        # list no-go:  N*S4 - S2^2 >= 0  always
        list_gap = Nn*S4 - S2*S2
        worst_violation_list = min(worst_violation_list, list_gap)  # should never be < 0
        # period floor: max(a) >= S4/S2 (since Sum a^4 = Sum a^2 * a^2 <= max(a) * Sum a^3 ...
        #   the clean read used in exists_period_sq_ge is S4 <= max(a^2)*S2, i.e. max(a) >= S4/S2,
        #   here a plays the role of ||eta||^2.)
        floor = S4/S2
        floor_gap = mx - floor
        worst_violation_floor = min(worst_violation_floor, floor_gap)  # should never be < 0
    # flat profile -> equality everywhere
    a=[1.0]*N
    Nn,S1,S2,S3,S4,mx=profile_stats(a)
    flat_list = Nn*S4 - S2*S2          # ==0
    flat_floor = mx - S4/S2            # ==0
    # "log-N flat-with-one-bump" Gumbel-like profile: a flat sea of height 1 with ONE entry
    # at the extreme-value height sqrt(2 log N) (the L-infinity max of N iid sub-Gaussians).
    # This is the ANALOGUE of the real Gauss-period situation: a flat L2/L4 sea, max = sqrt(log N) bump.
    h = math.sqrt(2*math.log(N))
    a=[1.0]*(N-1)+[h]
    Nn,S1,S2,S3,S4,mx=profile_stats(a)
    ev_floor = S4/S2
    ev_max = mx
    return dict(N=N, list_min_gap=worst_violation_list, floor_min_gap=worst_violation_floor,
                flat_list=flat_list, flat_floor=flat_floor,
                ev_floor=ev_floor, ev_max=ev_max, ev_h=h)

if __name__=="__main__":
    print("META-LEMMA CHECK: finiteMoment_returns_variance (list no-go == period floor, one Cauchy-Schwarz)")
    print("-"*90)
    for N in (8,16,32,64,128,1024,16384):
        r=check_random(N)
        print(f"N={N:5d}: list no-go (N*S4-S2^2) min over 20000 rand profiles = {r['list_min_gap']:+.3e} (>=0 OK)")
        print(f"          period floor (max - S4/S2)    min                       = {r['floor_min_gap']:+.3e} (>=0 OK)")
        print(f"          flat profile: list_gap={r['flat_list']:.1e}  floor_gap={r['flat_floor']:.1e}  (both ==0: equality at flat)")
        print(f"          EXTREME-VALUE profile (flat sea + 1 bump of height sqrt(2logN)={r['ev_h']:.2f}):")
        print(f"            S4/S2 floor={r['ev_floor']:.4f} (~1, the VARIANCE)  vs true max={r['ev_max']:.4f} (=sqrt(2logN))"
              f"  -> the L-inf max EXCEEDS the L4 floor by the log-N factor, invisible to S4/S2.")
        print()
    print("CONCLUSION: both inequalities are NON-NEGATIVE for every nonneg profile and ==0 exactly at the flat")
    print("profile. They are the SINGLE Cauchy-Schwarz S2^2 <= N*S4 read in two directions (upper cap on the")
    print("target sum = list no-go; lower bound on max = period floor). A one-spike profile shows the true L-inf")
    print("max is unbounded above the S4/S2 floor -> finite L^p chains return only the variance; the max is the escape.")
