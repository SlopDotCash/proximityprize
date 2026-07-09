"""
C007 probe: does the budget-vs-supply crossover C(2N,r) < r*2^r*C(N,r) flip
EXACTLY at the prize wall / beyond-Johnson window?

Prize regime: dyadic mu_n, n = 2^mu PROPER subgroup of F_q*, q ~ n^beta (beta~4-5).
m = 1 (so n = 2^mu = 2N, N = 2^{mu-1}).

The Lean pin (kkh26_deltaStar_pin_lowdegree) pins  delta* = 1 - r/2^mu = 1 - r/n
UNCONDITIONALLY whenever the budget-below-supply holds.

Key questions:
 (Q1) Where exactly is the PIN->WALL crossover r*(n)?  (claim: r*~0.27-0.34 n)
 (Q2) What delta* values does the crossover band correspond to?  delta* = 1 - r/n.
 (Q3) Does that band sit INSIDE the beyond-Johnson window (1-sqrt(rho), 1-rho]?
      Here the *code rate* rho is set by the code degree k = (r-2)m = r-2,
      so rho = (k+1)/n = (r-1)/n.  Johnson radius = 1 - sqrt(rho).
 (Q4) Is the wall REALLY at the crossover, or does the analytic (BGK) wall bite
      strictly EARLIER (smaller r) than the binomial crossover?
"""
from math import comb, sqrt, isqrt

def crossover_r(n):
    """Smallest r where budget >= supply (PIN fails -> WALL), m=1.
    budget = C(n,r)/r  (since (r-2)*1+2=r, (r-2)*1+1=r-1, C(r,r-1)=r)
    supply = 2^r * C(n/2, r)
    PIN holds while budget < supply.
    """
    N = n // 2
    flips = None
    for r in range(2, n // 2 + 1):
        budget = comb(n, r) // r          # integer floor as in Lean (Nat division)
        supply = (2 ** r) * comb(N, r)
        pin = budget < supply
        if not pin and flips is None:
            flips = r
    return flips

def detail(n):
    N = n // 2
    rows = []
    last_pin = None
    rstar = None
    for r in range(2, n // 2 + 1):
        budget_floor = comb(n, r) // r
        supply = (2 ** r) * comb(N, r)
        pin = budget_floor < supply
        if last_pin is True and pin is False and rstar is None:
            rstar = r
        last_pin = pin
        rows.append((r, budget_floor, supply, pin))
    return rstar, rows

print("=" * 90)
print("Q1/Q2: crossover r* and corresponding delta* = 1 - r/n   (prize regime m=1)")
print("=" * 90)
print(f"{'n=2^mu':>8} {'sqrt(n)':>8} {'r*(PIN->WALL)':>14} {'r*/n':>7} {'delta*@r*':>10} "
      f"{'r<=sqrt(n)?proven':>18}")
for mu in range(3, 13):
    n = 2 ** mu
    rstar, _ = detail(n)
    if rstar is None:
        print(f"{n:>8} {sqrt(n):>8.2f}  no crossover up to n/2")
        continue
    dstar = 1 - rstar / n
    print(f"{n:>8} {sqrt(n):>8.2f} {rstar:>14} {rstar/n:>7.3f} {dstar:>10.4f} "
          f"{'r*>sqrt(n)='+str(rstar>isqrt(n)):>18}")

print()
print("=" * 90)
print("Q3: is the crossover band INSIDE the beyond-Johnson window?")
print("  code degree k=(r-2)*1=r-2, rate rho=(k+1)/n=(r-1)/n")
print("  Johnson radius  = 1 - sqrt(rho);  capacity radius = 1 - rho")
print("  pin gives delta* = 1 - r/n.  Beyond-Johnson <=> delta* > 1-sqrt(rho) <=> r/n < sqrt(rho)")
print("=" * 90)
print(f"{'n':>6} {'r*':>5} {'rho@r*':>9} {'1-sqrt rho':>11} {'1-rho':>8} "
      f"{'delta*@r*':>10} {'beyond-John?':>13} {'in-window?':>11}")
for mu in range(4, 13):
    n = 2 ** mu
    rstar, _ = detail(n)
    if rstar is None:
        continue
    r = rstar
    rho = (r - 1) / n
    johnson = 1 - sqrt(rho)
    cap = 1 - rho
    dstar = 1 - r / n
    beyond = dstar > johnson
    inwin = johnson < dstar <= cap
    print(f"{n:>6} {r:>5} {rho:>9.4f} {johnson:>11.4f} {cap:>8.4f} "
          f"{dstar:>10.4f} {str(beyond):>13} {str(inwin):>11}")

print()
print("=" * 90)
print("Q3b: WHERE does delta*=1-r/n enter the beyond-Johnson window, vs r*?")
print("  For each n, find r_johnson = smallest r with delta*(r) <= johnson(r) (i.e leaves window)")
print("  and r_enter = smallest r with delta* > johnson (enters beyond-Johnson).")
print("=" * 90)
print(f"{'n':>6} {'r_enter(>John)':>14} {'r_leave(<=John)':>15} {'r*(crossover)':>14} "
      f"{'window=[r_enter,r_leave)':>24}")
for mu in range(4, 13):
    n = 2 ** mu
    rstar, _ = detail(n)
    r_enter = None
    r_leave = None
    for r in range(2, n // 2 + 1):
        rho = (r - 1) / n
        johnson = 1 - sqrt(rho)
        dstar = 1 - r / n
        beyond = dstar > johnson
        if beyond and r_enter is None:
            r_enter = r
        if (not beyond) and r_enter is not None and r_leave is None:
            r_leave = r
    print(f"{n:>6} {str(r_enter):>14} {str(r_leave):>15} {str(rstar):>14} "
          f"  [{r_enter},{r_leave})")
