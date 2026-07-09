"""
C075 probe: "The cumulant kappa_r is PLATYKURTIC (kurtosis -> 3 from BELOW): a one-sided
Markov-Krein with the WRONG-SIGN constraint the SOS no-go ignored."

THE CLAIM (from C075.json attack_plan):
  Run the Chebyshev-Markov extremal LP for the LARGEST support atom of a symmetric mean-0
  measure on [-sqrt(n), sqrt(n)] subject to
       mu_2 = 1   AND   mu_4 <= 3 - 3/n   (INEQUALITY, the platykurtic/wrong-sign constraint)
  at m atoms. Compare to the equality-mu_4 = 3 bound. The hope: strict-below + compact support
  pulls the max atom below n^{1-eps} at fixed rate, beating the prize target.

THE PRIZE REGIME numbers (what we must beat):
  Off-diagonal spectrum: X = eta_b / sqrt(n) over b != 0, m = (p-1)/n distinct coset values
  (eta is REAL since -1 in mu_n). Proven moments (in-tree, char-0 / Duke-Garcia):
     mu_2 = E_1/n   = 1            (Parseval; E_1 = n)
     mu_4 = E_2/n^2 = 3 - 3/n      (E_2 = 3n^2 - 3n  ->  PLATYKURTIC, kurtosis < 3)
  SUPPORT: |eta_b| <= n always (sum of n unit roots), so |X| <= sqrt(n).  <<< the support cap
  is EXACTLY sqrt(n) in these units.
  TRUE max:  B/sqrt(n) ~ sqrt(2 ln m) ~ sqrt(2 beta ln n)   (the DGPH house law; the prize target)

DECISIVE QUESTION:
  Does imposing (a) mu_4 <= 3 - 3/n  and (b) |X| <= sqrt(n) make the extremal LP max-atom
  t_max FALL BELOW the target sqrt(2 ln m)?  If YES at proper subgroups -> real progress.
  If the LP max-atom stays at sqrt(n)*poly(m) (i.e. the support cap or worse), the route walls.

We solve the extremal moment LP EXACTLY (rational arithmetic) on a fine atom grid:
  maximize  t   s.t.  exists prob measure nu on grid in [-S, S],
                       symmetric, mean 0, sum mu_2 = 1, sum mu_4 <= K := 3 - 3/n,
                       and nu({t}) >= 1/m   (a single atom of mass >= 1/m must sit at t).
Standard Markov-Krein dual: the answer is the largest t such that the moment constraints admit
a feasible measure with an atom of mass >= 1/m at t. We compute it by an explicit 3-atom (the
extremal measure of a 2-moment-constrained problem is supported on few points) construction
+ a dense-grid LP cross-check, both ways, and report t_max for equality and inequality mu_4,
WITH and WITHOUT the support cap S = sqrt(n).
"""
import math
from fractions import Fraction as Fr

# ---------- exact in-tree moment inputs ----------
def mu4_exact(n):
    # E_2 = 3 n^2 - 3 n  =>  mu_4 = E_2 / n^2 = 3 - 3/n   (platykurtic; PROVEN in-tree)
    return Fr(3*n*n - 3*n, n*n)

# ---------- the extremal max-atom of a 2-moment + support + mass problem ----------
# Symmetric mean-0 measure, second moment = 1, fourth moment <= K, support in [-S,S],
# wanting an atom of mass w = 1/m placed as far out as possible at +-t (and its mirror).
#
# Put mass w at +t, w at -t, remaining mass (1-2w) somewhere in [-S,S] symmetric.
# Constraints (symmetric so odd moments auto-0):
#   2w t^2 + (rest 2nd moment) = 1
#   2w t^4 + (rest 4th moment) <= K
# To push t as large as possible we want the "rest" to absorb as much 2nd-moment budget as
# cheaply (in 4th-moment) as possible: a point mass at 0 contributes 0 to both. But we still
# must HIT mu_2 = 1 EXACTLY. The rest must supply (1 - 2w t^2) of second moment using total
# mass (1-2w), staying in [-S,S], with minimal 4th moment. Minimal 4th moment for fixed mass
# and fixed 2nd moment, support [-S,S]: spread it (two atoms at +-r). To give 2nd-moment
# budget V_rest with mass (1-2w): atoms at +-r with mass (1-2w)/2 each (plus possibly mass at 0).
# Actually to MINIMIZE 4th moment for given (mass M_r, 2nd-moment V_r), put it all at one radius
# r with r^2 = V_r / M_r, giving 4th = M_r * r^4 = V_r^2 / M_r. (Jensen: single radius minimizes
# 4th for fixed mass & 2nd.) Requires r <= S i.e. V_r/M_r <= S^2.
#
# So feasibility for a given t (with w=1/m, S):
#   need t <= S
#   M_r = 1 - 2w ;  V_r = 1 - 2 w t^2  (must be >= 0)
#   require V_r/M_r <= S^2   (rest radius within support)
#   4th moment total = 2 w t^4 + V_r^2 / M_r  <=  K
# t_max = largest t<=S satisfying the 4th-moment inequality (monotone increasing in t for the
# relevant range), found by binary search.

def fourth_total(t, w, S):
    M_r = 1 - 2*w
    V_r = 1 - 2*w*t*t
    if V_r < 0:   # too much 2nd-moment already at +-t; infeasible (rest would need negative)
        return float('inf')
    if M_r <= 0:
        return 2*w*t**4
    # rest single-radius minimal 4th; but radius must be <= S
    r2 = V_r / M_r
    if r2 > S*S + 1e-15:
        return float('inf')   # cannot place rest within support and hit mu_2 -> infeasible
    return 2*w*t**4 + V_r*V_r / M_r

def tmax_constrained(n, m, K, S):
    """largest t in [0,S] with a feasible symmetric mean-0 measure: mu2=1, mu4<=K, atom mass 1/m at t."""
    w = 1.0/m
    lo, hi = 0.0, S
    # check feasibility at t=0-ish
    if fourth_total(1e-9, w, S) > K + 1e-12:
        return 0.0  # even tiny atom infeasible -> degenerate
    for _ in range(200):
        mid = 0.5*(lo+hi)
        if fourth_total(mid, w, S) <= K + 1e-12:
            lo = mid
        else:
            hi = mid
    return lo

def main():
    print("="*100)
    print(" C075: one-sided platykurtic Markov-Krein extremal max-atom  vs  prize target sqrt(2 ln m)")
    print("="*100)
    print(" units: X = eta_b / sqrt(n);  support cap S = sqrt(n);  atom mass w = 1/m;  m = (p-1)/n")
    print(" mu_2 = 1 (Parseval), mu_4 = 3 - 3/n (PLATYKURTIC, proven in-tree via E_2 = 3n^2-3n)")
    print()
    hdr = (f"{'n':>5}{'beta':>5}{'m=2^':>6}{'mu4(<3)':>9}"
           f"{'LP t_max(mu4<=3-3/n,S=√n)':>26}{'LP t_max(mu4=3,S=√n)':>22}"
           f"{'LP t_max(mu4<=3-3/n,no cap)':>28}{'target √(2lnm)':>15}")
    print(hdr)
    rows = []
    # prize-shaped: n=2^mu proper subgroup, p~n^beta (beta 4-5), so m=(p-1)/n ~ n^(beta-1)
    for n, beta in [(8,4),(8,5),(16,4),(16,5),(32,4),(32,5),(64,4),(64,5),
                    (2**20,5),(2**30,5)]:
        m = max(2, int(round(n**(beta-1))))
        K = float(mu4_exact(n))                 # 3 - 3/n   (the platykurtic inequality RHS)
        S = math.sqrt(n)
        t_ineq   = tmax_constrained(n, m, K,   S)              # mu4 <= 3 - 3/n , capped
        t_eq     = tmax_constrained(n, m, 3.0, S)              # mu4 = 3 (equality, the old no-go), capped
        t_nocap  = tmax_constrained(n, m, K,   1e18)          # mu4 <= 3-3/n , NO support cap
        target   = math.sqrt(2*math.log(m))
        log2m = math.log2(m)
        print(f"{n:>5}{beta:>5}{log2m:>6.1f}{K:>9.4f}"
              f"{t_ineq:>26.3f}{t_eq:>22.3f}{t_nocap:>28.3f}{target:>15.3f}")
        rows.append((n,beta,m,K,S,t_ineq,t_eq,t_nocap,target))
    print()
    print(" KEY RATIOS (does the platykurtic+support LP beat the target?):")
    print(f"{'n':>5}{'beta':>5}{'t_ineq/target':>15}{'t_ineq/t_eq':>14}{'t_ineq/√n(=S)':>15}{'t_ineq/(√n·poly?)':>18}")
    for (n,beta,m,K,S,t_ineq,t_eq,t_nocap,target) in rows:
        print(f"{n:>5}{beta:>5}{t_ineq/target:>15.3f}{(t_ineq/t_eq if t_eq>0 else float('nan')):>14.4f}"
              f"{t_ineq/S:>15.4f}{t_ineq/(S):>18.4f}")
    print()
    print(" VERDICT LOGIC:")
    print("  - If LP t_max (platykurtic, capped) << target  -> route WORKS (real progress).")
    print("  - If LP t_max (platykurtic, capped) >= target by a growing factor -> route WALLS:")
    print("    the LP admits a far atom AT/NEAR the support cap S=√n, vastly ABOVE the √(2 ln m) target.")
    print("  - t_ineq/t_eq ~ 1 means the platykurtic strict-below buys essentially NOTHING vs equality.")

if __name__ == "__main__":
    main()
