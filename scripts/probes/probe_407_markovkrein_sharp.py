#!/usr/bin/env python3
"""
#407 NOVEL ROUTE: SHARP moment-problem (Markov-Krein/Chebyshev) bound on the MAX eigenvalue,
using the PROVEN low even-moments E_1=n (Parseval), E_2=3n^2-3n (Duke-Garcia, in-tree), and the
known count of m off-diagonal eigenvalues. This is DIFFERENT from the naive (p E_r)^{1/2r} moment
bound: it asks for the largest x in the SUPPORT of ANY measure consistent with the given moments and
the given number of atoms -- the Markov-Krein extremal problem.

Setup. The off-diagonal spectrum {eta_b : b not in mu_n} consists of m = (p-1)/n real values
(since -1 in mu_n => eta real). Their empirical measure nu (m atoms) has moments:
   m_1 = (1/m) sum eta_b = (1/m)(-1) ~ 0   [trace of A minus n = -n, over m... actually sum_{all b!=0} eta_b = -n]
   m_2 = (1/m) sum eta_b^2 = (1/m)(n(p-1) - n^2) = n(p-1-n)/m = n(nm - n)/m = n^2(m-1)/m ~ n^2 ... 
WAIT: recompute. sum_{b in F_p} eta_b^2 = p * (#{(x,y) in mu_n^2 : x=y}) = p*n. Minus the eta_0=n term: n^2.
So sum_{b!=0} eta_b^2 = pn - n^2. Over m=(p-1)/n cosets each repeated n times... 

CAREFUL: eta_b depends only on coset; each coset has n elements b. The DISTINCT eigenvalues are the m
coset-values, but as eigenvalues of A they have MULTIPLICITY n each (n b's per coset). 
sum over ALL b in F_p^* of eta_b^2 = pn - n^2 (computed above). Each coset value v_j appears n times:
   n * sum_{j=1}^{m} v_j^2 = pn - n^2  => sum_j v_j^2 = p - n = nm + 1 - n ~ nm.
   => second moment of coset-measure: (1/m) sum v_j^2 = (nm+1-n)/m ~ n.   GOOD: RMS = sqrt(n). 
Fourth moment: sum_{b!=0} eta_b^4 = p*E_2 - n^4 where E_2=#{x1+x2=y1+y2 in mu_n}=3n^2-2n (Duke-Garcia, 
  the +-includes... use 3n^2-2n per the tangent note; check). Each coset n times:
   n sum_j v_j^4 = p*E2 - n^4 => sum_j v_j^4 = (p E2 - n^4)/n. (1/m)sum v_j^4 = (p E2 - n^4)/(nm) ~ E2 = 3n^2.
   => normalized 4th moment mu4 := (1/m)sum (v/sqrt(n))^4 -> 3  (Gaussian kurtosis!).

THE EXTREMAL PROBLEM. Given a probability measure nu on R with m atoms, mean 0, variance s^2=n, 
4th moment mu4*s^4 = 3n^2 (kurtosis 3), what is the MAX possible support point?
   Chebyshev-Cantelli / one-sided: P(X >= t) <= s^2/(s^2+t^2) (Cantelli, uses only variance).
   With m atoms each mass 1/m: the max atom t_max satisfies 1/m <= P(X>=t_max) <= variance bound.
   Using variance only: 1/m <= n/(n+t^2) => t^2 <= n(m-1) => t <= sqrt(nm) = sqrt(p). [trivial bracket]
   Using 4th moment (kurtosis K): sharper one-sided. The Markov bound with 2 moments:
       P(X>=t) <= inf over poly q>=0 on support, q>=1[t,inf) of E[q(X)]. For even moments up to 4:
       best quadratic majorant gives P(X>=t) <= (K-1)/((t^2/s^2-1)^2 + K -1)  ... 
   We compute the SHARP 2-moment (var+kurtosis) Markov-Krein upper bound on t_max from 1/m <= P, and
   compare to sqrt(n log m). DOES adding the proven kurtosis=3 beat the trivial sqrt(p)? By how much?

   We also test the EXACT extremal: with the FULL known even-moment SEQUENCE mu_{2r}=(2r-1)!! (Gaussian,
   valid up to r<r*~3 then defects), the Chebyshev-Markov extremal max given moments up to order 2R and
   m atoms. This is the BEST POSSIBLE bound any moment method (even sharp, even using exact low moments)
   can give -- if THIS is still >> sqrt(n log m), then NO moment-based route (however sharp) can work.
"""
import math
from fractions import Fraction

def cheb_markov_max(moments_normalized, m):
    """
    Given normalized even moments mu_2, mu_4, ..., mu_{2R} (mu_2=1 after scaling by s=sqrt(var)),
    of a mean-0 symmetric measure with m atoms, return the SHARP upper bound on max|atom|/s.
    Uses the Markov (Chebyshev-Markov) extremal: max t s.t. there's a measure with these moments and
    an atom at t of mass >= 1/m. Equivalent sharp bound: t_max/s <= largest root achievable.
    Simple sharp 2-moment version (mu_2=1, mu_4=K): one-sided Markov for symmetric meas:
       P(|X|>=t) <= (K-1)/((t^2-1)^2/... )  -- use the Selberg/Markov 4th-moment tail:
       For symmetric X with EX^2=1, EX^4=K: P(|X|>=t) <= (K-1)/(t^4 - 2t^2 + K)  for t^2>1 (valid Markov).
    Set = 2/m (two-sided, both +-t atoms) and solve for t.
    """
    K = moments_normalized.get(4, 3.0)
    # solve (K-1)/(t^4 - 2 t^2 + K) = 2/m  => t^4 - 2t^2 + K = (K-1)m/2
    # t^4 - 2 t^2 + (K - (K-1)m/2) = 0 ; let u=t^2: u^2 -2u + (K-(K-1)m/2)=0
    C = K - (K-1)*m/2.0
    disc = 4 - 4*C
    u = (2 + math.sqrt(disc))/2 if disc>=0 else None
    t4 = math.sqrt(u) if u and u>0 else float('nan')
    # 2-moment Cantelli (variance only): P(|X|>=t)<=1/t^2 => 2/m=1/t^2 => t=sqrt(m/2)
    t2 = math.sqrt(m/2.0)
    return t2, t4, K

def high_moment_markov(R, m):
    """sharp-ish: with Gaussian even moments mu_{2r}=(2r-1)!! up to order 2R, the best Markov tail uses
    the optimal degree-2R nonneg polynomial. APPROX by the moment-method optimum but at the SHARP atom
    level: t_max/s <= min_r ( m * (2r-1)!! )^{1/2r}  -- this is exactly the (count * moment)^{1/2r} which
    for our scaling is the naive bound. Report it for comparison (the 'best moment method can do' with
    char-0 moments only, count m)."""
    best=None
    def ldf(r):  # ln((2r-1)!!)
        return math.lgamma(2*r+1) - r*math.log(2) - math.lgamma(r+1)
    for r in range(1,R+1):
        val = (math.log(m) + ldf(r))/(2*r)   # ln( (m (2r-1)!!)^{1/2r} ) in units of s
        if best is None or val<best[1]: best=(r,val)
    return best[0], math.exp(best[1])

def main():
    print("="*96)
    print(" #407 SHARP MOMENT-PROBLEM (Markov-Krein) bound on max|eta|/sqrt(n)  vs  target sqrt(log m)")
    print("="*96)
    print(f"\n{'log2(m)':>8}{'m':>14}{'Cantelli(var)':>14}{'Markov(var+K=3)':>16}"
          f"{'GaussMomOpt(r*)':>16}{'target sqrt(2lnm)':>18}")
    for log2m in (10,15,20,25,30,32):
        m = 2**log2m
        t2,t4,K = cheb_markov_max({4:3.0}, m)
        ropt, tmom = high_moment_markov(2*log2m+10, m)
        target = math.sqrt(2*math.log(m))   # extreme value of m gaussians: sqrt(2 ln m) sigma
        print(f"{log2m:>8}{m:>14}{t2:>14.2f}{t4:>16.2f}{tmom:>16.2f}{target:>18.2f}  (r*={ropt})")
    print("\nInterpretation: all columns are max|eta|/sqrt(n). target = sqrt(2 ln m) is the TRUE extreme")
    print("value of m near-Gaussian samples (the prize law, since B/sqrt(n)~sqrt(2 ln m)~sqrt(2(b-1)ln n)).")
    print("Cantelli(var): trivial sqrt(m/2)=sqrt(p)/sqrt(2n)-ish. Markov(var+K): does kurtosis=3 help?")
    print("GaussMomOpt: best the (m * char0-moment)^{1/2r} method gives -- this IS ~ target IF char0 moments")
    print("valid to r~ln m. The whole point: char0 moments only valid to r*~3 (p-defect), so GaussMomOpt")
    print("is NOT achievable; what's achievable is r<=3 only.")
    print()
    # what r<=3 (only proven char0 region) actually gives:
    print(" REALITY: moment method restricted to PROVEN-valid depth r<=r* (=3, p-defect onset):")
    print(f"{'log2(m)':>8}{'r=2 bound':>12}{'r=3 bound':>12}{'target':>10}")
    def ldf(r): return math.lgamma(2*r+1)-r*math.log(2)-math.lgamma(r+1)
    for log2m in (20,30,40,50,60):
        m=2**log2m
        b2=math.exp((math.log(m)+ldf(2))/4)
        b3=math.exp((math.log(m)+ldf(3))/6)
        target=math.sqrt(2*math.log(m))
        print(f"{log2m:>8}{b2:>12.2f}{b3:>12.2f}{target:>10.2f}")

if __name__=="__main__":
    main()
