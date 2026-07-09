# probe_wfCF_closedform.py  (#444)
#
# GOAL: assess the closed-form conjecture  delta*(rho,n) = (1-rho) - c(rho)/log2(n)
# for the prize regime (smooth RS, n=2^mu, rho in {1/2,1/4,1/8,1/16}, eps*=2^-128, q~n*2^128).
#
# The GOVERNING LAW (proven in-tree): delta* is the cushion where the worst-case window list
# L*(delta) = 2^{c(rho)/eta} crosses the budget eps*|F| ~ n, eta=(1-rho)-delta.
# Setting 2^{c(rho)/eta}=n=2^mu gives eta* = c(rho)/mu = c(rho)/log2 n.
#
# THE CONSTANT c(rho) -- four routes returned three competing closed forms:
#   Route 1/2 (KKH26 explicit / list-crossover):  c1(rho) = H2(rho)
#   Route 3   (dyadic-entropy / sym-tower):        c3(rho) = rho + (1/2) H2(2 rho)   (needs 2rho<=1)
#   Route 4   (EVT/house):                          rho-independent, NOT of this class (excluded)
#
# We ALSO derive the constant DIRECTLY from the in-tree KKH26 entropy count
# (KKH26EntropyForm.lean): count ~ 2^{r + (n/2) H2(2r/n)} with the antipodal structure,
# at radius delta = 1 - r/n (so r = n*(1-delta) = n*(rho+eta)). Solving the crossover
# count = budget gives the EXACT in-tree constant c_KKH(rho); we check which closed form it equals.
#
# All logs base 2. H2 = binary entropy in bits.

from math import log2, log, comb

def H2(x):
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -x*log2(x) - (1-x)*log2(1-x)

# ---- the three candidate closed constants ----
def c_route1(rho):                       # KKH26 explicit ceiling / list-crossover
    return H2(rho)

def c_route3(rho):                       # dyadic-entropy / symmetric-tower base count
    if 2*rho >= 1.0:
        return rho + 0.5*H2(2*rho)       # H2(1)=0 at rho=1/2 -> c3(1/2)=1/2
    return rho + 0.5*H2(2*rho)

# ---- the EXACT in-tree KKH26 count constant, derived from the entropy form ----
# In KKH26WitnessSpread/EntropyForm: the smooth subgroup has size n=2^mu. The bad line at
# radius delta=1-r/n has bad-scalar count >= 2^r * C(n/2, r)  (n/2 = 2^{mu-1}, antipodal).
# Bit-exponent E(r) = r + log2 C(n/2, r) ~ r + (n/2) H2( r/(n/2) ) = r + (n/2) H2(2r/n).
# With r = n*(1-delta), and we want the radius delta where E(r) = budget exponent = log2 n = mu.
#
# Write delta = (1-rho) - eta, so 1-delta = rho + eta, r = n(rho+eta). Then
#   E = n(rho+eta) + (n/2) H2( 2(rho+eta) ).
# This is LINEAR-in-n leading order, NOT log n -- the KKH26 line's RAW count is exponential
# in n at any fixed eta>0. The "list L*=2^{c/eta}" governing law is the WINDOW list (the
# worst-case list as a function of the CUSHION eta), a different object: as eta->0 the per-eta
# list exponent is c(rho)/eta. The bridge (CLAUDE.md governing law) is:
#   log2 L*(delta) = c(rho)/eta   with   c(rho) := lim_{eta->0+} eta * log2 L*(rho,eta).
#
# We extract c(rho) from the KKH26 count by the SMALL-CUSHION expansion of its PER-SYMBOL
# rate. The KKH26 radius family is parametrized by r (integer). The natural "rate per cushion"
# the law uses is the exponent of the list at the SMALLEST nontrivial spread, which the
# in-tree entropy lemma packages as countRate(m,r) with m=n/2. The crossover eta*(n) solving
#   2^{c(rho)/eta} = n      <=>      c(rho)/eta = log2 n = mu      <=>     eta* = c(rho)/mu.
# So c(rho) is read off as the coefficient. We TEST all three candidate c's against:
#   (A) the KKH26 entropy rate near the capacity edge (r/(n/2) small <-> rho small);
#   (B) the window-interior landing requirement.

def kkh26_rate_constant(rho, n):
    """Empirical c from the in-tree KKH26 count: choose r at the capacity-adjacent radius
    and read off eta*log2(count) as the cushion-normalised exponent. We pick the r that makes
    the count cross the budget n, then report eta*=(r/n - rho) and c_emp = eta* * log2 n."""
    mu = round(log2(n))
    half = n // 2
    if half < 1:
        return None
    # find smallest r >= 2 with 2^r * C(half, r) >= n   (count crosses budget eps*|F| ~ n)
    best = None
    for r in range(2, half+1):
        try:
            cnt = (2**r) * comb(half, r)
        except (OverflowError, ValueError):
            cnt = float('inf')
        if cnt >= n:
            # crossover radius delta = 1 - r/n, cushion eta = (1-rho) - delta = r/n - rho
            eta = r/n - rho
            if eta > 0:
                best = (r, eta, eta*mu)
            break
    return best

print("="*78)
print("#444  CLOSED-FORM delta* = (1-rho) - c(rho)/log2(n)  -- constant assessment")
print("="*78)

rates = [(0.5,"1/2"), (0.25,"1/4"), (0.125,"1/8"), (0.0625,"1/16")]

print("\n[1] The three candidate closed constants c(rho):\n")
print(f"  {'rho':>6} | {'c1=H2(rho)':>12} | {'c3=rho+H2(2rho)/2':>18} | {'c1==c3?':>8}")
for rho,rl in rates:
    c1=c_route1(rho); c3=c_route3(rho)
    print(f"  {rl:>6} | {c1:12.6f} | {c3:18.6f} | {abs(c1-c3)<1e-9!s:>8}")

print("\n  NOTE rho=1/2: c1=H2(1/2)=1.0 ; c3=1/2+H2(1)/2=1/2+0=0.5  -> they DISAGREE.")
print("  NOTE rho=1/4: c1=H2(1/4)=0.8113; c3=1/4+H2(1/2)/2=0.25+0.5=0.75 -> DISAGREE.")
print("  => Routes 1/2 and Route 3 are DIFFERENT closed forms. Need the in-tree arbiter.")

print("\n[2] The EXACT in-tree KKH26 count constant (read off the entropy-form crossover):\n")
print(f"  {'rho':>6} | {'c1=H2(rho)':>10} | {'c3':>8} | KKH26 crossover c_emp at n=2^mu")
for rho,rl in rates:
    c1=c_route1(rho); c3=c_route3(rho)
    row=[]
    for mu in (10,14,18,22):
        n=1<<mu
        res=kkh26_rate_constant(rho,n)
        row.append("n/a" if res is None else f"{res[2]:.3f}")
    print(f"  {rl:>6} | {c1:10.4f} | {c3:8.4f} | mu=10,14,18,22: {row}")

print("\n  (c_emp = eta*log2 n at the budget-crossover r; this is the count's cushion constant.)")

print("\n" + "="*78)
print("[3] WINDOW-INTERIOR TEST: does delta* land in (1-sqrt rho, 1-rho) at prize n?")
print("="*78)

def window_test(c_func, label):
    print(f"\n--- using c(rho) = {label} ---")
    print(f"  {'rho':>6} | {'lower=1-sqrt rho':>16} | {'upper=1-rho':>11} | "
          f"{'delta* @ n=2^30':>15} | {'strictly interior?':>18}")
    allok=True
    for rho,rl in rates:
        lower=1-rho**0.5
        upper=1-rho
        mu=30
        c=c_func(rho)
        d=upper - c/mu
        interior = lower < d < upper
        allok = allok and interior
        print(f"  {rl:>6} | {lower:16.5f} | {upper:11.5f} | {d:15.5f} | {interior!s:>18}")
    print(f"  ALL FOUR strictly interior at n=2^30: {allok}")
    return allok

ok1=window_test(c_route1, "H2(rho)  [Route 1/2]")
ok3=window_test(c_route3, "rho + H2(2rho)/2  [Route 3]")

print("\n" + "="*78)
print("[4] FULL CURVE n=2^10 .. 2^30, both c's, all four rates")
print("="*78)
for rho,rl in rates:
    lower=1-rho**0.5; upper=1-rho
    print(f"\nrho={rl}: Johnson(lower)={lower:.5f}  capacity(upper)={upper:.5f}  "
          f"window-width={upper-lower:.5f}")
    print(f"  {'mu':>4} | {'delta*(c1=H2)':>14} | {'in?':>4} | {'delta*(c3)':>12} | {'in?':>4}")
    for mu in (10,12,14,16,18,20,22,24,26,28,30):
        d1=upper - c_route1(rho)/mu
        d3=upper - c_route3(rho)/mu
        in1 = lower < d1 < upper
        in3 = lower < d3 < upper
        print(f"  {mu:>4} | {d1:14.5f} | {str(in1):>4} | {d3:12.5f} | {str(in3):>4}")

print("\n" + "="*78)
print("[5] WHERE does the window OPEN (smallest n with delta* > Johnson) for each c?")
print("="*78)
for rho,rl in rates:
    lower=1-rho**0.5; upper=1-rho
    def first_open(cf):
        for mu in range(2, 200):
            if upper - cf(rho)/mu > lower:
                return mu
        return None
    m1=first_open(c_route1); m3=first_open(c_route3)
    print(f"  rho={rl:>4}: window opens at  c1=H2 -> mu>={m1} (n=2^{m1})   "
          f"c3 -> mu>={m3} (n=2^{m3})")
